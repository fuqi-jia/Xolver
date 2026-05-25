#include <cstdlib>
#include <cstring>
#include <iostream>
#include <string>
#include <optional>

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
              << "  --dump-stats <file>    Dump per-case stats JSON (requires NLCOLVER_ENABLE_CASESTATS)\n"
              << "  --lia-safe-mode        Disable aggressive LIA reasoning (GCD tighten, bound rounding, eq norm)\n"
              << "  --lia-ultra-safe-mode  Disable ALL integer reasoning (LRA relaxation only)\n"
              << "  --lia-enable-single-var-tightening   Re-enable single-var bound tightening\n"
              << "  --lia-enable-gcd-ineq-tightening     Re-enable GCD inequality tightening\n"
              << "  --lia-enable-eq-gcd-normalization    Re-enable equality GCD normalization\n"
              << "  -v, --verbose          Verbose output\n";
}

#include <nlcolver/Solver.h>

static int cmdSolve(int argc, char* argv[], bool defaultMode = false) {
    int fileIdx = defaultMode ? 1 : 2;
    if (argc < fileIdx + 1) {
        std::cerr << "Error: solve requires an input file.\n";
        return EXIT_FAILURE;
    }

    nlcolver::Solver solver;

    // Parse options after the file path
    std::optional<std::string> logicOpt;
    bool checkModel = false;
    for (int i = fileIdx + 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (arg == "--logic" && i + 1 < argc) {
            logicOpt = argv[++i];
        } else if (arg == "--seed" && i + 1 < argc) {
            solver.setOption("seed", nlcolver::OptionValue(static_cast<int64_t>(std::stoll(argv[++i]))));
        } else if (arg == "--dump-stats" && i + 1 < argc) {
            solver.setDumpStatsPath(argv[++i]);
        } else if (arg == "--produce-models") {
            // TODO: enable model production
        } else if (arg == "--produce-proofs") {
            // TODO: enable proof production
        } else if (arg == "--lia-safe-mode") {
            solver.setOption("lia-safe-mode", nlcolver::OptionValue(true));
        } else if (arg == "--lia-ultra-safe-mode") {
            solver.setOption("lia-ultra-safe-mode", nlcolver::OptionValue(true));
        } else if (arg == "--lia-enable-single-var-tightening") {
            solver.setOption("lia-enable-single-var-tightening", nlcolver::OptionValue(true));
        } else if (arg == "--lia-enable-gcd-ineq-tightening") {
            solver.setOption("lia-enable-gcd-ineq-tightening", nlcolver::OptionValue(true));
        } else if (arg == "--lia-enable-eq-gcd-normalization") {
            solver.setOption("lia-enable-eq-gcd-normalization", nlcolver::OptionValue(true));
        } else if (arg == "-v" || arg == "--verbose") {
            // TODO: enable verbose output
        } else if (arg == "--check-model") {
            checkModel = true;
        } else {
            std::cerr << "Warning: unknown option " << arg << "\n";
        }
    }

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
    // competition harness (which greps stdout) is not confused. The old
    // `dumpSMT2(std::cout)` echo of the parsed formula is removed for the
    // same reason — use `--verbose` / stderr for debugging instead.
    nlcolver::Result r = solver.checkSat();
    std::cout << toString(r) << "\n";
    // Model-Validation track: if the input requested a model and we found
    // one, emit the SMT-LIB get-model response on stdout right after `sat`.
    if (r == nlcolver::Result::Sat && solver.modelRequested()) {
        solver.dumpModel(std::cout);
    }
    std::cout.flush();
    // Diagnostic: independent model self-check against original assertions.
    if (checkModel && r == nlcolver::Result::Sat && !solver.modelMatchesOriginal()) {
        std::cerr << "MODEL_MISMATCH\n";
    }
    if (r == nlcolver::Result::Unknown) {
        auto reason = solver.lastUnknownReason();
        if (!reason.empty()) {
            std::cerr << "(unknown-reason " << reason << ")\n";
        }
    }
    return EXIT_SUCCESS;
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
    std::cout << "[NLColver trace] (stub)\n";
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

    nlcolver::Solver solver;
    if (logicOpt) solver.setLogic(*logicOpt);
    if (!solver.parseFile(argv[fileIdx])) {
        std::cerr << "Error: failed to parse " << argv[fileIdx] << "\n";
        return EXIT_FAILURE;
    }

    nlcolver::Result r = solver.checkSat();
    if (r == nlcolver::Result::Sat) {
        std::cout << "sat\n";
        auto model = solver.getModel();
        for (const auto& [varId, value] : model.values()) {
            std::cout << "  v" << varId << " = " << value << "\n";
        }
    } else if (r == nlcolver::Result::Unsat) {
        std::cout << "unsat\n";
    } else {
        std::cout << "unknown\n";
    }
    return EXIT_SUCCESS;
}

static int cmdProofCheck(int argc, char* argv[]) {
    std::cout << "[NLColver proof-check] (stub)\n";
    return EXIT_SUCCESS;
}

static int cmdVersion() {
    std::cout << "NLColver " << NLCOLVER_VERSION_MAJOR << "."
              << NLCOLVER_VERSION_MINOR << "." << NLCOLVER_VERSION_PATCH
              << " — NonLinear Constraint Solver\n"
              << "Stage: A (bootstrap)\n";
    return EXIT_SUCCESS;
}

int main(int argc, char* argv[]) {
    if (argc < 2) {
        printUsage(argv[0]);
        return EXIT_FAILURE;
    }

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
