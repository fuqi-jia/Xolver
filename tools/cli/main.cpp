#include <cstdlib>
#include <cstring>
#include <iostream>
#include <string>
#include <optional>
#include <functional>
#include <pthread.h>
#include <execinfo.h>
#include <csignal>
#include <sys/time.h>
#include <unistd.h>

// ZOLVER_SELFPROF: poor-man's CPU profiler. ITIMER_PROF fires SIGPROF on the
// thread consuming CPU (the large-stack solve worker), so the backtrace lands
// in the actual hot loop. backtrace_symbols_fd writes to the real fd 2,
// bypassing the std::cerr NullStreambuf, so samples survive non-verbose mode.
// Async-signal-safe (backtrace/backtrace_symbols_fd/write). Resolve frames with
// addr2line on the printed module+offset.
static void zolverSelfprofHandler(int) {
    void* bt[64];
    int n = backtrace(bt, 64);
    static const char hdr[] = "==SELFPROF-SAMPLE==\n";
    ssize_t w = write(2, hdr, sizeof(hdr) - 1); (void)w;
    backtrace_symbols_fd(bt, n, 2);
}
static void zolverMaybeInstallSelfprof() {
    if (!std::getenv("ZOLVER_SELFPROF")) return;
    struct sigaction sa{};
    sa.sa_handler = zolverSelfprofHandler;
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
              << "  model-check <model>    Validate model against assertions\n"
              << "  proof-check <proof>    Check proof certificate\n"
              << "  version                Print version\n"
              << "\nOptions:\n"
              << "  --logic <logic>        Set logic (e.g., QF_NRA)\n"
              << "  --produce-models       Enable model production\n"
              << "  --produce-proofs       Enable proof production\n"
              << "  --trace-out <file>     Write execution trace\n"
              << "  --seed <n>             Random seed for reproducibility\n"
              << "  --dump-stats <file>    Dump per-case stats JSON (requires ZOLVER_ENABLE_CASESTATS)\n"
              << "  --lia-safe-mode        Disable aggressive LIA reasoning (GCD tighten, bound rounding, eq norm)\n"
              << "  --lia-ultra-safe-mode  Disable ALL integer reasoning (LRA relaxation only)\n"
              << "  --lia-enable-single-var-tightening   Re-enable single-var bound tightening\n"
              << "  --lia-enable-gcd-ineq-tightening     Re-enable GCD inequality tightening\n"
              << "  --lia-enable-eq-gcd-normalization    Re-enable equality GCD normalization\n"
              << "  -v, --verbose          Verbose output\n";
}

#include <zolver/Solver.h>

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

static int cmdSolve(int argc, char* argv[], bool defaultMode = false) {
    int fileIdx = defaultMode ? 1 : 2;
    if (argc < fileIdx + 1) {
        std::cerr << "Error: solve requires an input file.\n";
        return EXIT_FAILURE;
    }

    zolver::Solver solver;

    // Parse options after the file path
    std::optional<std::string> logicOpt;
    bool checkModel = false;
    bool verbose = false;
    for (int i = fileIdx + 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (arg == "--logic" && i + 1 < argc) {
            logicOpt = argv[++i];
        } else if (arg == "--seed" && i + 1 < argc) {
            solver.setOption("seed", zolver::OptionValue(static_cast<int64_t>(std::stoll(argv[++i]))));
        } else if (arg == "--dump-stats" && i + 1 < argc) {
            solver.setDumpStatsPath(argv[++i]);
        } else if (arg == "--produce-models") {
            // TODO: enable model production
        } else if (arg == "--produce-proofs") {
            // TODO: enable proof production
        } else if (arg == "--lia-safe-mode") {
            solver.setOption("lia-safe-mode", zolver::OptionValue(true));
        } else if (arg == "--lia-ultra-safe-mode") {
            solver.setOption("lia-ultra-safe-mode", zolver::OptionValue(true));
        } else if (arg == "--lia-enable-single-var-tightening") {
            solver.setOption("lia-enable-single-var-tightening", zolver::OptionValue(true));
        } else if (arg == "--lia-enable-gcd-ineq-tightening") {
            solver.setOption("lia-enable-gcd-ineq-tightening", zolver::OptionValue(true));
        } else if (arg == "--lia-enable-eq-gcd-normalization") {
            solver.setOption("lia-enable-eq-gcd-normalization", zolver::OptionValue(true));
        } else if (arg == "-v" || arg == "--verbose") {
            verbose = true;
        } else if (arg == "--check-model") {
            checkModel = true;
        } else {
            std::cerr << "Warning: unknown option " << arg << "\n";
        }
    }

    // Silence the solver's internal stderr diagnostics by default. Kept live
    // for --verbose (debugging) and --check-model (whose MODEL_MISMATCH report
    // goes to stderr). The buffer must outlive every write, so it is static.
    static NullStreambuf nullCerr;
    if (!verbose && !checkModel) {
        std::cerr.rdbuf(&nullCerr);
    }

    // Parse + solve + emit on a large-stack worker thread so deeply-nested
    // inputs survive any remaining recursive walker (see runWithLargeStack).
    auto body = [&]() -> int {
      try {
        if (!solver.parseFile(argv[fileIdx])) {
            std::cerr << "Error: failed to parse " << argv[fileIdx] << "\n";
            return EXIT_FAILURE;
        }

        // Command-line --logic overrides file-declared logic
        if (logicOpt) {
            solver.setLogic(*logicOpt);
        }

        // SMT-COMP output contract: stdout carries ONLY the SMT-LIB result
        // tokens (sat / unsat / unknown). Diagnostics go to stderr so the
        // competition harness (which greps stdout) is not confused.
        zolver::Result r = solver.checkSat();
        std::cout << toString(r) << "\n";
        // Model-Validation track: if the input requested a model and we found
        // one, emit the SMT-LIB get-model response on stdout right after `sat`.
        if (r == zolver::Result::Sat && solver.modelRequested()) {
            solver.dumpModel(std::cout);
        }
        std::cout.flush();
        // Diagnostic: independent model self-check against original assertions.
        if (checkModel && r == zolver::Result::Sat && !solver.modelMatchesOriginal()) {
            std::cerr << "MODEL_MISMATCH\n";
        }
        if (r == zolver::Result::Unknown) {
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
    std::cout << "[Zolver trace] (stub)\n";
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

    zolver::Solver solver;
    if (logicOpt) solver.setLogic(*logicOpt);
    if (!solver.parseFile(argv[fileIdx])) {
        std::cerr << "Error: failed to parse " << argv[fileIdx] << "\n";
        return EXIT_FAILURE;
    }

    zolver::Result r = solver.checkSat();
    if (r == zolver::Result::Sat) {
        std::cout << "sat\n";
        auto model = solver.getModel();
        for (const auto& [varId, value] : model.values()) {
            std::cout << "  v" << varId << " = " << value << "\n";
        }
    } else if (r == zolver::Result::Unsat) {
        std::cout << "unsat\n";
    } else {
        std::cout << "unknown\n";
    }
    return EXIT_SUCCESS;
}

static int cmdProofCheck(int argc, char* argv[]) {
    std::cout << "[Zolver proof-check] (stub)\n";
    return EXIT_SUCCESS;
}

static int cmdVersion() {
    std::cout << "Zolver " << ZOLVER_VERSION_MAJOR << "."
              << ZOLVER_VERSION_MINOR << "." << ZOLVER_VERSION_PATCH
              << " — NonLinear Constraint Solver\n"
              << "Stage: A (bootstrap)\n";
    return EXIT_SUCCESS;
}

int main(int argc, char* argv[]) {
    if (argc < 2) {
        printUsage(argv[0]);
        return EXIT_FAILURE;
    }
    zolverMaybeInstallSelfprof();

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
