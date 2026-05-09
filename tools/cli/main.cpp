#include <cstdlib>
#include <cstring>
#include <iostream>
#include <string>

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
              << "  -v, --verbose          Verbose output\n";
}

#include <nlcolver/Solver.h>

static int cmdSolve(int argc, char* argv[]) {
    if (argc < 3) {
        std::cerr << "Error: solve requires an input file.\n";
        return EXIT_FAILURE;
    }

    nlcolver::Solver solver;
    if (!solver.parseFile(argv[2])) {
        std::cerr << "Error: failed to parse " << argv[2] << "\n";
        return EXIT_FAILURE;
    }

    solver.dumpSMT2(std::cout);

    nlcolver::Result r = solver.checkSat();
    std::cout << toString(r) << "\n";
    return EXIT_SUCCESS;
}

static int cmdBench(int argc, char* argv[]) {
    std::cout << "[NLColver bench] (stub)\n";
    return EXIT_SUCCESS;
}

static int cmdTrace(int argc, char* argv[]) {
    std::cout << "[NLColver trace] (stub)\n";
    return EXIT_SUCCESS;
}

static int cmdModelCheck(int argc, char* argv[]) {
    std::cout << "[NLColver model-check] (stub)\n";
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

    std::cerr << "Unknown command: " << cmd << "\n";
    printUsage(argv[0]);
    return EXIT_FAILURE;
}
