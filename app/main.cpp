#include <cstdlib>
#include <cstdio>
#include <utility>
#include <sys/wait.h>
#include <cstring>
#include <iostream>
#include <fstream>
#include <string>
#include <optional>
#include <functional>
#include <pthread.h>
#include <execinfo.h>
#include <csignal>
#include <sys/time.h>
#include <unistd.h>
#include <fcntl.h>
#include "xolver/Proof.h"
#include <iterator>
#include <vector>
#include <cerrno>
#include <limits>
#include "xolver/Script.h"
#include "base/RuntimeConfig.h"

// XOLVER_SELFPROF: poor-man's CPU profiler. ITIMER_PROF fires SIGPROF on the
// thread consuming CPU (the large-stack solve worker), so the backtrace lands
// in the actual hot loop. backtrace_symbols_fd writes to the real fd 2,
// bypassing the std::cerr NullStreambuf, so samples survive non-verbose mode.
// Async-signal-safe (backtrace/backtrace_symbols_fd/write). Resolve frames with
// addr2line on the printed module+offset.
static void xolverSelfprofHandler(int) {
    void* bt[64];
    int n = backtrace(bt, 64);
    static const char hdr[] = "==SELFPROF-SAMPLE==\n";
    ssize_t w = write(2, hdr, sizeof(hdr) - 1); (void)w;
    backtrace_symbols_fd(bt, n, 2);
}
static void xolverMaybeInstallSelfprof() {
    if (!xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_SELFPROF")) return;
    struct sigaction sa{};
    sa.sa_handler = xolverSelfprofHandler;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = SA_RESTART;
    sigaction(SIGPROF, &sa, nullptr);
    struct itimerval tv{};
    tv.it_interval.tv_usec = 400000;  // 400ms repeating
    tv.it_value.tv_usec = 400000;
    setitimer(ITIMER_PROF, &tv, nullptr);
}

static void printUsage(const char* prog) {
    std::cout << "Usage: " << prog << " <command> [options]\n"
              << "\nCommands:\n"
              << "  solve <file.smt2>      Solve SMT-LIB input\n"
              << "  bench <dir>            Run benchmark suite\n"
              << "  trace <file.json>      View / replay trace\n"
              << "  model-check <file>     Solve and positively validate the extracted model\n"
              << "  proof-check <proof>    Check proof certificate\n"
              << "  version                Print version\n"
              << "\nOptions:\n"
              << "  --logic <logic>        Set logic (e.g., QF_NRA)\n"
              << "  --produce-models       Enable model production\n"
              << "  --produce-proof [base] On unsat, emit a checkable refutation: <base>.cnf + <base>.drat (needs -DXOLVER_ENABLE_PROOFS=ON)\n"
              << "  --trace-out <file>     Write execution trace\n"
              << "  --seed <n>             Random seed for reproducibility\n"
              << "  --timeout <seconds>    Per-solve wall-clock budget (0 = none)\n"
              << "  --dump-stats <file>    Dump per-case stats JSON (requires XOLVER_ENABLE_CASESTATS)\n"
              << "  --produce-pa-certificate <file> Export native QE obligations for independent Isabelle replay\n"
              << "  --certify <file>       On sat, write a re-checkable certificate (independently re-validated model)\n"
              << "  --unsat-core           On unsat, print the core assertions (subset that proves unsat)\n"
              << "  --parse-only           Parse the file and exit (print parse-ok); no solve\n"
              << "  --features             Print the instance feature vector (JSON) and exit; no solve\n"
              << "  -v, --verbose          Verbose output\n";
}

#include <xolver/Solver.h>

// Discards everything written to it. Installed as std::cerr's buffer in the
// default (non-verbose) mode so the solver's internal diagnostics never reach
// the terminal/logs. This matters at benchmark scale: a single hard NRA case
// can emit tens of thousands of [CDCAC-FULL]/etc. lines, which (a) balloon any
// harness that captures stderr and (b) add enough write I/O to push otherwise-
// solvable cases over the timeout. The SMT-COMP contract only reads stdout
// (sat/unsat/unknown), so discarding stderr is safe; `--verbose` keeps it.
namespace {
struct NullStreambuf : std::streambuf {
    int overflow(int c) override { return c; }  // pretend success, write nothing
    std::streamsize xsputn(const char*, std::streamsize n) override { return n; }
};

// Defense-in-depth net for deep-input stack overflow. The frontend preprocess
// passes and the SOMTParser rewriter are iterative, but other recursive
// walkers remain downstream (e.g. PolynomialConverter::collectRec, the
// atomizer, theory term builders). Running parse+solve on a thread with a
// large stack lets those survive deeply-nested benchmarks rather than
// SIGSEGV. Single worker; the caller blocks on join, so stdout/stderr writes
// are not concurrent. Falls back to inline execution if the thread cannot be
// created. Stack reservation is virtual (lazily committed), not RSS.
struct LargeStackCtx { std::function<int()> fn; int ret; };
extern "C" inline void* largeStackTrampoline(void* p) {
    auto* c = static_cast<LargeStackCtx*>(p);
    c->ret = c->fn();
    return nullptr;
}
inline int runWithLargeStack(std::function<int()> fn) {
    constexpr size_t kStackBytes = 512UL * 1024 * 1024;  // 512 MB
    pthread_attr_t attr;
    if (pthread_attr_init(&attr) != 0) return fn();
    LargeStackCtx ctx{std::move(fn), EXIT_FAILURE};
    pthread_t tid;
    if (pthread_attr_setstacksize(&attr, kStackBytes) == 0 &&
        pthread_create(&tid, &attr, largeStackTrampoline, &ctx) == 0) {
        pthread_join(tid, nullptr);
        pthread_attr_destroy(&attr);
        return ctx.ret;
    }
    pthread_attr_destroy(&attr);
    return ctx.fn();  // fallback: run on the current thread
}
}  // namespace

// --certify: persist a portable, independently re-checkable SAT certificate.
// Certification requires a positive result from the independent evaluator;
// an indeterminate diagnostic is not evidence. This is an in-process check,
// not an externally or formally checked proof of the implementation.
// Running the strict check (caller side: validateModel) and
// writing the validated model as a self-contained SMT-LIB artifact. A third
// party reloads the original formula, binds these define-funs, and evaluates the
// assertions to confirm `sat` without trusting Xolver. Returns true iff written.
static bool writeSatCertificate(const xolver::Solver& solver,
                                const std::string& sourcePath,
                                const std::string& outPath) {
    std::ofstream out(outPath);
    if (!out) {
        std::cerr << "(certify-error cannot-open " << outPath << ")\n";
        return false;
    }
    out << "; Xolver SAT certificate\n"
        << "; format: xolver-sat-cert/1\n"
        << "; source: " << sourcePath << "\n"
        << "; generated-by: Xolver " << XOLVER_VERSION_MAJOR << "."
        << XOLVER_VERSION_MINOR << "." << XOLVER_VERSION_PATCH << "\n"
        << "; verdict: sat\n"
        << "; certification: positive in-process evaluation by an independent evaluator\n"
        << ";   (exact GMP/MPFR/libpoly). Not an external or formal proof check.\n"
        << "; replay: assert the original formula, bind the model below, evaluate to true.\n"
        << ";\n"
        << "; --- model (SMT-LIB get-model response) ---\n";
    solver.dumpModel(out);
    out.flush();
    return static_cast<bool>(out);
}


static int cmdSolve(int argc, char* argv[], bool defaultMode = false) {
    int fileIdx = defaultMode ? 1 : 2;
    if (argc < fileIdx + 1) {
        std::cerr << "Error: solve requires an input file.\n";
        return EXIT_FAILURE;
    }

    xolver::Solver solver;

    // Parse options after the file path
    std::optional<std::string> logicOpt;
    std::optional<std::string> certifyPath;
    std::optional<std::string> proofBase;
    std::optional<std::string> paCertificate;
    bool checkModel = false;
    bool verbose = false;
    bool parseOnly = false;
    bool produceModels = false;
    bool featuresOnly = false;
    try {
    for (int i = fileIdx + 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (arg == "--parse-only") {
            parseOnly = true;
        } else if (arg == "--features") {
            featuresOnly = true;
        } else if (arg == "--logic" && i + 1 < argc) {
            logicOpt = argv[++i];
        } else if (arg == "--seed" && i + 1 < argc) {
            solver.setOption("seed", xolver::OptionValue(static_cast<int64_t>(std::stoll(argv[++i]))));
        } else if (arg == "--timeout" && i + 1 < argc) {
            // Expose the per-solve wall-clock budget as a CLI flag. beginSolve()
            // reads XOLVER_WALLCLOCK_MS at solve time (api/Solver.cpp), so setting
            // it here before solve() takes effect. <=0 means no limit (the default).
            long long secs = std::stoll(argv[++i]);
            if (secs > std::numeric_limits<long long>::max() / 1000)
                throw std::invalid_argument("timeout is too large");
            solver.setRuntimeParameter("XOLVER_WALLCLOCK_MS",
                                       std::to_string(secs > 0 ? secs * 1000 : 0));
        } else if (arg == "--dump-stats" && i + 1 < argc) {
            solver.setDumpStatsPath(argv[++i]);
        } else if (arg == "--produce-pa-certificate" && i + 1 < argc) {
            paCertificate = argv[++i];
            solver.setOption("produce-pa-certificate", xolver::OptionValue(true));
        } else if (arg == "--certify" && i + 1 < argc) {
            certifyPath = argv[++i];
        } else if (arg == "--unsat-core") {
            // Enable unsat-core production. (The parser does not yet map the
            // SMT-LIB :produce-unsat-cores option, so expose it as a flag.) On
            // unsat, the core assertions are printed on stdout after the verdict.
            solver.setOption("produce-unsat-cores", xolver::OptionValue(true));
        } else if (arg == "--produce-models") {
            // Force the SMT-LIB get-model response after `sat`, even if the input
            // did not set :produce-models / issue (get-model). The model is built
            // internally on every sat (see Solver.cpp), so dumpModel is meaningful.
            produceModels = true;
        } else if (arg == "--produce-proofs" || arg == "--produce-proof") {
            // Enable UNSAT proof production. Optional explicit base path follows;
            // otherwise derive it from the input file. The backend writes the
            // DIMACS it feeds the SAT engine to <base>.cnf and the propositional
            // refutation to <base>.drat, so an independent checker (drat-trim)
            // can verify <base>.cnf |- false. Requires a build configured with
            // -DXOLVER_ENABLE_PROOFS=ON; otherwise this is a degraded no-op
            // (unsat is still emitted, just without a certificate).
            std::string base;
            if (i + 1 < argc && argv[i + 1][0] != '-') base = argv[++i];
            else base = std::string(argv[fileIdx]) + ".proof";
            proofBase = base;
            solver.setOption("produce-proofs", xolver::OptionValue(std::string_view(base)));
        } else if (arg == "-v" || arg == "--verbose") {
            verbose = true;
        } else if (arg == "--check-model") {
            checkModel = true;
        } else {
            std::cerr << "Warning: unknown option " << arg << "\n";
        }
    }
    } catch (const std::exception& error) {
        std::cerr << "Invalid solve option: " << error.what() << '\n';
        return EXIT_FAILURE;
    }

    // Silence the solver's internal stderr diagnostics by default. Kept live
    // for --verbose (debugging) and --check-model (whose MODEL_MISMATCH report
    // goes to stderr). The buffer must outlive every write, so it is static.
    static NullStreambuf nullCerr;
    if (!verbose && !checkModel && !certifyPath && !paCertificate) {
        std::cerr.rdbuf(&nullCerr);
    }

    // Parse + solve + emit on a large-stack worker thread so deeply-nested
    // inputs survive any remaining recursive walker (see runWithLargeStack).
    auto exportPA = [&]() -> bool {
        if (!paCertificate) return true;
        const auto certificate = solver.getProof().presburger();
        if (certificate.empty()) {
            std::cerr << "no completed PA decision: certificate unavailable\n";
            return false;
        }
        // Exclusive creation prevents a stale result or another writer's file
        // from being mistaken for evidence produced by this invocation.
        int fd = open(paCertificate->c_str(), O_WRONLY | O_CREAT | O_EXCL, 0600);
        if (fd < 0) {
            std::cerr << "cannot create new PA certificate: " << std::strerror(errno) << "\n";
            return false;
        }
        size_t offset = 0;
        while (offset < certificate.size()) {
            ssize_t count = write(fd, certificate.data() + offset, certificate.size() - offset);
            if (count < 0 && errno == EINTR) continue;
            if (count <= 0) { close(fd); std::cerr << "PA certificate write failed\n"; return false; }
            offset += static_cast<size_t>(count);
        }
        if (close(fd) != 0) { std::cerr << "PA certificate close failed\n"; return false; }
        std::cerr << "PA obligations exported (generated-unchecked)\n";
        return true;
    };
    auto body = [&]() -> int {
      try {
        if (paCertificate && (parseOnly || featuresOnly))
            throw std::invalid_argument("PA certificate export requires solving");
        std::ifstream scriptInput(argv[fileIdx]);
        if (!scriptInput) return EXIT_FAILURE;
        const std::string source{std::istreambuf_iterator<char>(scriptInput), {}};
        const auto snapshots = xolver::smtQuerySnapshots(source);
        if (snapshots.size() > 1 && !parseOnly && !featuresOnly) {
            if (certifyPath || proofBase || paCertificate) {
                std::cerr << "certificate/proof export requires a single query per invocation\n";
                return EXIT_FAILURE;
            }
            for (const auto& snapshot : snapshots) {
                struct TemporaryQuery {
                    char path[32] = "/tmp/xolver-query-XXXXXX";
                    int fd = mkstemp(path);
                    ~TemporaryQuery() { if (fd >= 0) { close(fd); unlink(path); } }
                } temp;
                if (temp.fd < 0) return EXIT_FAILURE;
                size_t offset = 0;
                while (offset < snapshot.size()) {
                    const ssize_t written = write(temp.fd, snapshot.data() + offset,
                                                  snapshot.size() - offset);
                    if (written < 0 && errno == EINTR) continue;
                    if (written <= 0) return EXIT_FAILURE;
                    offset += static_cast<size_t>(written);
                }
                std::vector<char*> args(argv, argv + argc);
                args[fileIdx] = temp.path;
                args.push_back(nullptr);
                const int rc = cmdSolve(argc, args.data());
                if (rc != EXIT_SUCCESS) return rc;
            }
            return EXIT_SUCCESS;
        }
        if (!solver.parseFile(argv[fileIdx])) {
            std::cerr << "Error: failed to parse " << argv[fileIdx] << "\n";
            return EXIT_FAILURE;
        }

        // --parse-only: report parse success and exit BEFORE solving. Lets the
        // harness separate parse-phase failures (the case times out / OOMs under
        // --parse-only) from solve-phase failures (parses fast here, fails only
        // under a normal solve). Emits `parse-ok` on stdout; no solver run.
        if (parseOnly) {
            std::cout << "parse-ok\n";
            std::cout.flush();
            return EXIT_SUCCESS;
        }

        // --features: emit the per-instance feature vector (JSON) and exit
        // WITHOUT solving — fast (parse + detect only). For mining a benchmark
        // tree into a training corpus (learned strategy selection / autotuning).
        if (featuresOnly) {
            solver.dumpFeatures(std::cout);
            std::cout.flush();
            return EXIT_SUCCESS;
        }

        // Command-line --logic overrides file-declared logic
        if (logicOpt) {
            solver.setLogic(*logicOpt);
        }

        // #12: interactive command responses. When the script has echo or
        // get-info commands (which the batch path below cannot answer), walk the
        // parsed commands in SOURCE ORDER and print each response, so an
        // (echo ...) before (check-sat) prints before the verdict. Non-interactive
        // scripts (the SMT-COMP path) take NEITHER branch of this guard and fall
        // through to the byte-identical batch path below. get-value /
        // get-assignment are recognized but not yet answered (deferred #12.c).
        {
            auto scriptCmds = solver.scriptResponseCommands();
            using K = xolver::Solver::ScriptResponseCommand::Kind;
            bool interactive = false;
            size_t queryCount = 0;
            for (const auto& c : scriptCmds)
                if (c.kind == K::Echo || c.kind == K::GetInfo ||
                    c.kind == K::GetValue) interactive = true;
                else if (c.kind == K::CheckSat) ++queryCount;
            interactive = interactive || queryCount > 1;
            if (interactive) {
                xolver::Result r = xolver::Result::Unknown;
                bool solved = false, modelDumped = false;
                for (const auto& c : scriptCmds) {
                    switch (c.kind) {
                        case K::Echo:
                            std::cout << c.text << "\n";
                            break;
                        case K::CheckSat:
                            r = solver.checkSat();
                            solved = true;
                            std::cout << toString(r) << "\n";
                            if (r == xolver::Result::Sat &&
                                (solver.modelRequested() || produceModels)) {
                                solver.dumpModel(std::cout);
                                modelDumped = true;
                            }
                            if (r == xolver::Result::Unsat && solver.unsatCoreRequested())
                                solver.dumpUnsatCore(std::cout);
                            break;
                        case K::GetInfo: {
                            const std::string& kw = c.text;
                            if (kw == ":name")
                                std::cout << "(:name \"Xolver\")\n";
                            else if (kw == ":version")
                                std::cout << "(:version \"" << XOLVER_VERSION_MAJOR << "."
                                          << XOLVER_VERSION_MINOR << "."
                                          << XOLVER_VERSION_PATCH << "\")\n";
                            else if (kw == ":authors")
                                std::cout << "(:authors \"Xolver authors\")\n";
                            else if (kw == ":error-behavior")
                                std::cout << "(:error-behavior immediate-exit)\n";
                            else if (kw == ":reason-unknown")
                                std::cout << "(:reason-unknown "
                                          << (solved && r == xolver::Result::Unknown
                                                  ? "incomplete" : "unknown")
                                          << ")\n";
                            else
                                std::cout << "unsupported\n";
                            break;
                        }
                        case K::GetModel:
                            if (solved && r == xolver::Result::Sat && !modelDumped) {
                                solver.dumpModel(std::cout);
                                modelDumped = true;
                            }
                            break;
                        case K::GetValue: {
                            std::string resp = solver.getValueResponse(c.scriptIndex);
                            if (!resp.empty())
                                std::cout << resp << "\n";
                            // empty -> unsupported term or no model; emit nothing
                            break;
                        }
                        case K::GetAssignment:
                            break;  // deferred
                    }
                }
                std::cout.flush();
                return exportPA() ? EXIT_SUCCESS : EXIT_FAILURE;
            }
        }

        // SMT-COMP output contract: stdout carries ONLY the SMT-LIB result
        // tokens (sat / unsat / unknown). Diagnostics go to stderr so the
        // competition harness (which greps stdout) is not confused.
        xolver::Result r = solver.checkSat();
        std::cout << toString(r) << "\n";
        if (!exportPA()) return EXIT_FAILURE;
        // Model-Validation track: if the input requested a model and we found
        // one, emit the SMT-LIB get-model response on stdout right after `sat`.
        if (r == xolver::Result::Sat && (solver.modelRequested() || produceModels)) {
            solver.dumpModel(std::cout);
        }
        // Unsat-core track: if the input requested cores (:produce-unsat-cores)
        // and we proved unsat, emit the core assertions on stdout after `unsat`.
        if (r == xolver::Result::Unsat && solver.unsatCoreRequested()) {
            solver.dumpUnsatCore(std::cout);
        }
        // --produce-proof: report the emitted refutation on stderr (stdout carries
        // only the verdict, per the SMT-COMP contract). Honest about degraded mode:
        // claim a proof ONLY if the backend actually wrote one — an unsat decided
        // outside the SAT core (pure theory refutation, or a no-proof theory)
        // produces no propositional certificate, and we never fake one.
        if (proofBase && r == xolver::Result::Unsat) {
#ifdef XOLVER_ENABLE_PROOFS
            // The backend writes <base>.cnf whenever the SAT core produced the
            // refutation; its presence is the "proof produced" signal. The CNF's
            // leading `c xolver-proof:` comment records how many theory lemmas (if
            // any) are ASSUMED as axioms — read it to know whether this is a
            // complete proof or a Boolean skeleton (lemmas justified in Phase C).
            std::ifstream pf(*proofBase + ".cnf");
            if (pf.good())
                std::cerr << "(proof " << *proofBase << ".drat + " << *proofBase
                          << ".cnf — verify: drat-trim " << *proofBase << ".cnf "
                          << *proofBase << ".drat)\n";
            else
                std::cerr << "(no propositional proof produced — unsat decided "
                             "outside the SAT core; degraded no-proof mode)\n";
#else
            std::cerr << "(proof requested but this binary was built without proof "
                         "support; rebuild with -DXOLVER_ENABLE_PROOFS=ON)\n";
#endif
        }
        std::cout.flush();
        // Diagnostic: independent model self-check against original assertions.
        if (checkModel && r == xolver::Result::Sat && !solver.modelMatchesOriginal()) {
            std::cerr << "MODEL_MISMATCH\n";
        }
        // Only positive validation can authorize a SAT certificate. A missing
        // interpretation or unsupported term must fail certification.
        if (certifyPath) {
            if (r == xolver::Result::Sat) {
                if (solver.validateModel() == xolver::Solver::ModelValidation::Satisfied) {
                    if (writeSatCertificate(solver, argv[fileIdx], *certifyPath))
                        std::cerr << "(certified-sat " << *certifyPath << ")\n";
                    else
                        return EXIT_FAILURE;
                } else {
                    std::cerr << "CERTIFICATION_FAILED (model violated or not fully "
                                 "evaluable; no certificate written)\n";
                    return EXIT_FAILURE;
                }
            } else {
                std::cerr << "(certify: no SAT model to certify — verdict "
                          << toString(r) << ")\n";
            }
        }
        if (r == xolver::Result::Unknown) {
            auto reason = solver.lastUnknownReason();
            if (!reason.empty()) {
                std::cerr << "(unknown-reason " << reason << ")\n";
            }
        }
        return EXIT_SUCCESS;
      } catch (const std::exception& ex) {
        // Graceful degradation: emit a valid SMT-LIB token instead of crashing.
        std::cout << "unknown\n";
        std::cout.flush();
        std::cerr << "(error " << ex.what() << ")\n";
        return EXIT_FAILURE;
      }
    };
    return runWithLargeStack(body);
}

static int cmdBench(int argc, char* argv[]) {
    std::string scriptDir = "tools/run_benchmark.py";
    std::string cmd = "python3 " + scriptDir;

    // Pass all args after 'bench' to the Python script
    for (int i = 2; i < argc; ++i) {
        cmd += " ";
        cmd += argv[i];
    }

    int ret = std::system(cmd.c_str());
    return (ret == 0) ? EXIT_SUCCESS : EXIT_FAILURE;
}

static int cmdTrace(int argc, char* argv[]) {
    std::cout << "[Xolver trace] (stub)\n";
    return EXIT_SUCCESS;
}

static int cmdModelCheck(int argc, char* argv[]) {
    int fileIdx = 2;
    std::optional<std::string> logicOpt;
    for (int i = fileIdx; i < argc; ++i) {
        if (std::strcmp(argv[i], "--logic") == 0 && i + 1 < argc) {
            logicOpt = argv[i + 1];
            ++i;
        }
    }
    if (argc < fileIdx + 1) {
        std::cerr << "Error: model-check requires an input file.\n";
        return EXIT_FAILURE;
    }

    xolver::Solver solver;
    if (logicOpt) solver.setLogic(*logicOpt);
    if (!solver.parseFile(argv[fileIdx])) {
        std::cerr << "Error: failed to parse " << argv[fileIdx] << "\n";
        return EXIT_FAILURE;
    }

    xolver::Result r = solver.checkSat();
    if (r == xolver::Result::Sat) {
        if (solver.validateModel() != xolver::Solver::ModelValidation::Satisfied) {
            std::cout << "unknown\n";
            std::cerr << "model-check: model violated or not fully evaluable\n";
            return EXIT_FAILURE;
        }
        std::cout << "sat\n";
        auto model = solver.getModel();
        for (const auto& [varId, value] : model.values()) {
            std::cout << "  v" << varId << " = " << value << "\n";
        }
    } else if (r == xolver::Result::Unsat) {
        std::cout << "unsat\n";
    } else {
        std::cout << "unknown\n";
    }
    return r == xolver::Result::Sat ? EXIT_SUCCESS : EXIT_FAILURE;
}

namespace {
// Run a shell command, capture combined stdout+stderr, return (exit-code, output).
// exit-code is the process exit status (127 = command not found), -1 on failure.
std::pair<int, std::string> runChecker(const std::string& cmd) {
    FILE* p = popen((cmd + " 2>&1").c_str(), "r");
    if (!p) return {-1, "popen failed"};
    std::string out;
    char buf[4096];
    size_t n;
    while ((n = std::fread(buf, 1, sizeof(buf), p)) > 0) out.append(buf, n);
    int status = pclose(p);
    int code = (status >= 0 && WIFEXITED(status)) ? WEXITSTATUS(status) : -1;
    return {code, out};
}
// Resolve a checker binary: explicit flag > env var > PATH name (default).
std::string resolveChecker(const std::string& flagVal, const char* envVar,
                           const std::string& dflt) {
    if (!flagVal.empty()) return flagVal;
    if (const char* e = std::getenv(envVar); e && *e) return e;
    return dflt;
}
bool proofFileExists(const std::string& p) { std::ifstream f(p); return f.good(); }
std::string shellQuote(const std::string& arg) {
    std::string out = "'";
    for (char c : arg) out += c == '\'' ? "'\\''" : std::string(1, c);
    return out + "'";
}
}  // namespace

// proof-check <base> [--drat-trim P] [--carcara P]
// Validates the proof artifacts Xolver emitted at <base> with an INDEPENDENT
// external checker: prefers the Alethe theory proof (<base>.alethe + <base>.smt2,
// checked by Carcara — certifies the theory reasoning), else the propositional
// DRAT proof (<base>.cnf + <base>.drat, checked by drat-trim). Exit 0 iff the
// checker accepts; non-zero on rejection / missing artifacts / missing checker —
// so a wrong proof can never pass silently.
static int cmdProofCheck(int argc, char* argv[]) {
    std::string base, dratTrim, carcara;
    for (int i = 2; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--drat-trim" && i + 1 < argc) dratTrim = argv[++i];
        else if (a == "--carcara" && i + 1 < argc) carcara = argv[++i];
        else if (base.empty() && !a.empty() && a[0] != '-') base = a;
    }
    if (base.empty()) {
        std::cerr << "usage: xolver proof-check <proof-base> [--drat-trim P] [--carcara P]\n"
                     "  checks <base>.alethe + <base>.smt2 (Carcara) or\n"
                     "         <base>.cnf + <base>.drat (drat-trim)\n";
        return EXIT_FAILURE;
    }
    // Accept a full artifact name too: strip a known proof extension to get <base>.
    for (const char* ext : {".alethe", ".drat", ".cnf", ".smt2"}) {
        const std::string e(ext);
        if (base.size() > e.size() && base.compare(base.size() - e.size(), e.size(), e) == 0) {
            base.resize(base.size() - e.size());
            break;
        }
    }

    // Prefer the Alethe theory proof — it certifies the theory reasoning, not just
    // the Boolean skeleton.
    if (proofFileExists(base + ".alethe") && proofFileExists(base + ".smt2")) {
        const std::string car = resolveChecker(carcara, "XOLVER_CARCARA", "carcara");
        auto [code, out] = runChecker(shellQuote(car) + " check " + shellQuote(base + ".alethe") +
                                      " " + shellQuote(base + ".smt2"));
        if (code == 0) {
            std::cout << "verified (alethe/carcara): " << base << ".alethe\n";
            return EXIT_SUCCESS;
        }
        std::cerr << (code == 127 ? "proof-check: carcara not found (set --carcara or $XOLVER_CARCARA)\n"
                                  : "NOT VERIFIED (carcara): " + base + ".alethe\n")
                  << out;
        return EXIT_FAILURE;
    }

    // Fall back to the propositional DRAT proof.
    if (proofFileExists(base + ".drat") && proofFileExists(base + ".cnf")) {
        const std::string dt = resolveChecker(dratTrim, "XOLVER_DRAT_TRIM", "drat-trim");
        auto [code, out] = runChecker(shellQuote(dt) + " " + shellQuote(base + ".cnf") +
                                      " " + shellQuote(base + ".drat"));
        if (code == 0 && out.find("s VERIFIED") != std::string::npos) {
            // DRAT checks only the supplied CNF. Theory lemmas supplied as
            // axioms do not become certified by checking the Boolean skeleton.
            std::ifstream cnf(base + ".cnf");
            std::string line;
            bool complete = false;
            while (std::getline(cnf, line)) {
                if (line.rfind("c xolver-proof:", 0) == 0)
                    complete = line.find(", 0 theory lemmas assumed as axioms") != std::string::npos;
                if (line.rfind("p cnf ", 0) == 0) break;
            }
            if (!complete) {
                std::cerr << "verified-skeleton only: theory lemmas or provenance unchecked\n";
                return EXIT_FAILURE;
            }
            std::cout << "verified (drat/drat-trim): " << base << ".drat\n";
            return EXIT_SUCCESS;
        }
        std::cerr << (code == 127 ? "proof-check: drat-trim not found (set --drat-trim or $XOLVER_DRAT_TRIM)\n"
                                  : "NOT VERIFIED (drat-trim): " + base + ".drat\n")
                  << out;
        return EXIT_FAILURE;
    }

    std::cerr << "proof-check: no proof artifacts at \"" << base
              << "\" (expected .alethe+.smt2 or .cnf+.drat)\n";
    return EXIT_FAILURE;
}

static int cmdVersion() {
    std::cout << "Xolver " << XOLVER_VERSION_MAJOR << "."
              << XOLVER_VERSION_MINOR << "." << XOLVER_VERSION_PATCH
              << " — NonLinear Constraint Solver\n"
              << "Stage: A (bootstrap)\n";
    return EXIT_SUCCESS;
}

int main(int argc, char* argv[]) {
    if (argc < 2) {
        printUsage(argv[0]);
        return EXIT_FAILURE;
    }
    xolverMaybeInstallSelfprof();

    const char* cmd = argv[1];
    if (std::strcmp(cmd, "solve") == 0)       return cmdSolve(argc, argv);
    if (std::strcmp(cmd, "bench") == 0)       return cmdBench(argc, argv);
    if (std::strcmp(cmd, "trace") == 0)       return cmdTrace(argc, argv);
    if (std::strcmp(cmd, "model-check") == 0) return cmdModelCheck(argc, argv);
    if (std::strcmp(cmd, "proof-check") == 0) return cmdProofCheck(argc, argv);
    if (std::strcmp(cmd, "version") == 0)     return cmdVersion();
    if (std::strcmp(cmd, "-h") == 0 ||
        std::strcmp(cmd, "--help") == 0) {
        printUsage(argv[0]);
        return EXIT_SUCCESS;
    }

    // Default: if the first arg doesn't start with '-', treat it as a file to solve
    if (cmd[0] != '-') {
        return cmdSolve(argc, argv, true);
    }

    std::cerr << "Unknown command: " << cmd << "\n";
    printUsage(argv[0]);
    return EXIT_FAILURE;
}
