#include "ir/NativeFeatures.h"
#include "base/RuntimeConfig.h"
#include "base/EnvParam.h"
#include "runtime/SolverImpl.h"
#include "xolver/Script.h"
#include "frontend/parser/NativeTheoryPolicy.h"
#include <fstream>
#include <iterator>

namespace xolver {

// Relocated Solver::Impl method definitions (declared in SolverImpl.h).

void Solver::Impl::reset() {
        static std::atomic<uint64_t> nextContext{1};
        contextId_ = nextContext.fetch_add(1, std::memory_order_relaxed);
        symbolTerms_.clear();
        parser = std::make_unique<SOMTParser::Parser>();
        ir.reset();
        sat.reset();
        sharedTermRegistry_.reset();
        boolSortId_ = NullSort;
        intSortId_ = NullSort;
        realSortId_ = NullSort;
        lastModel_.reset();
        lastProof_.clear();
        lastAssumptions_.clear();
        assumptionRoots_.clear();
        lastUnsatCore_.clear();
        produceUnsatCores_ = false;
        indicatorRoots_.clear();
        indicatorCoreTerms_.clear();
        modelConverter_ = ModelConverter{};
        roaeReads_.clear();
        fixedBindings_.clear();
        originalAssertions_.clear();
        divModOrigins_.clear();
        partialFuncModel_ = PartialFuncModel{};
        lastUnknownReason_.clear();
        lastUnknownCode_.clear();
        lastUnknownComponent_.clear();
        lastUnknownDetail_.clear();
#ifdef XOLVER_ENABLE_CASESTATS
        caseStats_ = CaseStats{};
#endif
}
bool Solver::Impl::parseFile(std::string_view filename) {
        auto nextParser = std::make_unique<SOMTParser::Parser>();
        preserveNativeTheories(*nextParser->getOptions());
        // Keep response payloads for the selected query snapshot.
        nextParser->setCommandLogging(true);
        // whether parse-time expansion is the Certora blowup. Not for production.
        nextParser->setOption("expand_functions",
                          true);
        std::ifstream input{std::string(filename)};
        if (!input) return false;
        std::string source{std::istreambuf_iterator<char>(input), {}};
        std::vector<std::string> queries;
        try { queries = smtQuerySnapshots(source); }
        catch (const std::invalid_argument& e) {
            std::cerr << "SMT-LIB script: " << e.what() << '\n';
            return false;
        }
        if (!nextParser->parseStr(queries.back())) return false;
        // Auto-detect logic from the parsed file.
        auto opts = nextParser->getOptions();
        // Keep binders and explicit SL syntax intact for their solver entry
        // points. Ground preprocessing must not run across these boundaries.
        const auto native = nativeFeatures(nextParser->getAssertions());
        const bool nativeTheory = native.quantified || native.bitvector || native.floatingPoint || native.strings;
        const auto paOption = options.find("produce-pa-certificate");
        const bool recordPA = paOption != options.end() && paOption->second.kind == OptionValue::Bool && paOption->second.b;
        FrontendAdapter adapter(*nextParser);
        auto nextIr = adapter.importProblem(!nativeTheory && !recordPA && !nextParser->getHeapLocationSort());
        if (nextParser->getHeapLocationSort())
            for (auto variable : nextParser->getDeclaredVariables()) nextIr->index(std::move(variable));
        reset();
        parser = std::move(nextParser);
        ir = std::move(nextIr);
        for (ExprId id = 0; id < ir->size(); ++id) {
            const auto& e = ir->get(id);
            if (e.kind == Kind::Variable)
                if (auto name = std::get_if<std::string>(&e.payload.value)) symbolTerms_.emplace(*name, id);
        }
        logic = opts && opts->logic != "UNKNOWN_LOGIC" ? opts->logic : "ALL";
        boolSortId_ = adapter.getBoolSortId();
        // Propagate the Bool sort id into the NativeTerms now, before any
        // preprocessing pass creates Bool-sorted variables. Otherwise
        // ir->boolSortId() stays NullSort (getOrCreateBoolSort short-circuits
        // when the Solver member is already set, skipping cir.setBoolSortId),
        // so BoolSubtermPurifier creates `boolpur` vars with NullSort. The
        // Atomizer then fails to recognize those vars as Boolean and routes
        // boolean (= / distinct) iffs over them into the arithmetic theory as
        // difference (dis)equalities — an unbounded relaxation that yields
        // unsound SAT in QF_IDL/QF_LIA (Averest false-SAT cluster).
        if (boolSortId_ != NullSort) {
            ir->setBoolSortId(boolSortId_);
        }
        intSortId_ = ir->intSortId();
        realSortId_ = ir->realSortId();
        return true;
}
NativeTerms& Solver::Impl::ensureIr() {
        if (!ir) ir = std::make_unique<NativeTerms>(parser->getNodeManager());
        return *ir;
}
SortId Solver::Impl::getOrCreateBoolSort() {
        if (boolSortId_ != NullSort) return boolSortId_;
        auto& cir = ensureIr();
        if (boolSortId_ != NullSort) return boolSortId_;
        boolSortId_ = cir.allocateSortId();
        cir.registerSort(boolSortId_, SortKind::Bool);
        cir.setBoolSortId(boolSortId_);
        return boolSortId_;
}
SortId Solver::Impl::getOrCreateIntSort() {
        if (intSortId_ != NullSort) return intSortId_;
        auto& cir = ensureIr();
        if (intSortId_ != NullSort) return intSortId_;
        intSortId_ = cir.allocateSortId();
        cir.registerSort(intSortId_, SortKind::Int);
        cir.setIntSortId(intSortId_);
        return intSortId_;
}
SortId Solver::Impl::getOrCreateRealSort() {
        if (realSortId_ != NullSort) return realSortId_;
        auto& cir = ensureIr();
        if (realSortId_ != NullSort) return realSortId_;
        realSortId_ = cir.allocateSortId();
        cir.registerSort(realSortId_, SortKind::Real);
        cir.setRealSortId(realSortId_);
        return realSortId_;
}
} // namespace xolver
