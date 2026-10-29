#include "applications/satisfiability/smt/TheoryFactory.h"
#include "applications/satisfiability/smt/SolverRegistry.h"
#include "applications/satisfiability/smt/qflra/LraSolver.h"
#include "applications/satisfiability/smt/common/lia/LiaSolver.h"
#include "applications/satisfiability/smt/qflia/Builder.h"
#include "applications/satisfiability/smt/qfnra/NraSolver.h"
#include "applications/satisfiability/smt/qfnia/NiaSolver.h"
#include "applications/satisfiability/smt/qflira/LiraSolver.h"
#include "applications/satisfiability/smt/qfnira/NiraSolver.h"
#include "applications/satisfiability/smt/qfidl/IdlSolver.h"
#include "applications/satisfiability/smt/qfrdl/RdlSolver.h"
#include "applications/satisfiability/smt/qfuf/EufSolver.h"
#include "search/combination/Purifier.h"
#include <iostream>
#include <mutex>
#include <stdexcept>

namespace xolver {

namespace {

// ---------------------------------------------------------------------------
// Builders select and wire the solvers needed by each logic family.
// ---------------------------------------------------------------------------

void buildLRA(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto lra = std::make_unique<LraSolver>();
    lra->setRegistry(&registry);
    theoryManager.registerSolver(std::move(lra));
    theoryManager.setRegistry(&registry);  // needed by cb_decide evalTheoryAtom
}

void buildNRA(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto& result = *c.result;
    auto polyKernel = createPolynomialKernel();
    result.polyKernelRaw = polyKernel.get();
    auto lra = std::make_unique<LraSolver>();
    lra->setRegistry(&registry);
    auto nra = std::make_unique<NraSolver>(std::move(polyKernel));
    theoryManager.registerSolver(std::move(nra));
    theoryManager.registerSolver(std::move(lra));
}

void buildNIA(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto& result = *c.result;
    NativeTerms* ir = c.ir;
    auto polyKernel = createPolynomialKernel();
    result.polyKernelRaw = polyKernel.get();
    auto nia = std::make_unique<NiaSolver>(std::move(polyKernel));
    nia->setRegistry(&registry);
    nia->setNativeTerms(ir);  // needed by Z5 BOOL_EXTEND + Farkas-Or hooks
    theoryManager.registerSolver(std::move(nia));
    auto lia = std::make_unique<LiaSolver>();
    lia->setRegistry(&registry);
    theoryManager.registerSolver(std::move(lia));

}

void buildLIRA(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    NativeTerms* ir = c.ir;
    auto lira = std::make_unique<LiraSolver>();
    lira->setRegistry(&registry);
    lira->setNativeTerms(ir);
    theoryManager.registerSolver(std::move(lira));
}

void buildNIRA(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto& result = *c.result;
    NativeTerms* ir = c.ir;
    auto polyKernel = createPolynomialKernel();
    result.polyKernelRaw = polyKernel.get();
    auto nira = std::make_unique<NiraSolver>(std::move(polyKernel));
    nira->setRegistry(&registry);
    nira->setNativeTerms(ir);
    theoryManager.registerSolver(std::move(nira));

    auto lira = std::make_unique<LiraSolver>();
    lira->setRegistry(&registry);
    lira->setNativeTerms(ir);
    theoryManager.registerSolver(std::move(lira));
    theoryManager.setRegistry(&registry);
}

void buildIDL(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto idl = std::make_unique<IdlSolver>();
    idl->setRegistry(&registry);
    theoryManager.registerSolver(std::move(idl));
}

void buildRDL(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto rdl = std::make_unique<RdlSolver>();
    rdl->setRegistry(&registry);
    theoryManager.registerSolver(std::move(rdl));
}

void buildUF(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    NativeTerms* ir = c.ir;
    auto euf = std::make_unique<EufSolver>();
    euf->setNativeTerms(ir);
    euf->setEqualityAtomRegistry(&registry);  // XOLVER_EUF_PROP theory propagation
    theoryManager.registerSolver(std::move(euf));
}

void buildDT(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    NativeTerms* ir = c.ir;
    // #68: QF_DT / QF_UFDT have NO arithmetic in their signature, so a datatype
    // field declared with sort Int/Real is ill-typed — z3 and cvc5 reject it as
    // an unknown sort. Reject it here rather than silently solving an extended
    // logic; the CLI reports `unknown` (sound — no verdict on ill-typed input).
    // The arith-DT logics (QF_*DTLIA / QF_*DTNIA) take a different build branch
    // (buildUFDTLIA / buildUFDTNIA) and are unaffected.
    {
        const SortId intS = ir->intSortId(), realS = ir->realSortId();
        for (const auto& kv : ir->datatypes().all())
            for (const auto& ctor : kv.second.constructors)
                for (const auto& sel : ctor.selectors)
                    if ((intS != NullSort && sel.resultSort == intS) ||
                        (realS != NullSort && sel.resultSort == realS))
                        throw std::runtime_error(
                            "ill-typed: datatype field '" + sel.name +
                            "' has an arithmetic sort, but the logic has no "
                            "arithmetic (QF_DT/QF_UFDT); use a QF_*DTLIA/QF_*DTNIA logic");
    }
    theoryManager.setHasDatatypes(true);  // (#77) scope UF-arith arrangement out
    // Algebraic datatypes (+ UF). One shared egraph; DtReasoner layers the
    // free-algebra axioms on top. QF_DT and QF_UFDT share this branch.
    auto euf = std::make_unique<EufSolver>();
    euf->setNativeTerms(ir);
    euf->enableDts(&registry);
    theoryManager.registerSolver(std::move(euf));
}

void buildAX(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    NativeTerms* ir = c.ir;
    // Pure array theory (arrays + EUF, no arithmetic). ArrayReasoner adds axioms.
    auto euf = std::make_unique<EufSolver>();
    euf->setNativeTerms(ir);
    euf->enableArrays(&registry);
    theoryManager.registerSolver(std::move(euf));
}

void buildArrayLRA(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto& sharedTermRegistry = *c.sharedTermRegistry;
    NativeTerms* ir = c.ir;
    SortId boolSortId = c.boolSortId;
    // Arrays + LRA (+ UF). Nelson-Oppen exchanges index/element (dis)equalities.
    sharedTermRegistry = std::make_unique<SharedTermRegistry>();
    sharedTermRegistry->setNativeTerms(ir);
    {
        Purifier purifier(*ir, *sharedTermRegistry, boolSortId);
        purifier.run();
    }
    auto euf = std::make_unique<EufSolver>();
    euf->setNativeTerms(ir);
    euf->setSharedTermRegistry(sharedTermRegistry.get());
    euf->enableArrays(&registry);
    theoryManager.registerSolver(std::move(euf));
    auto lra = std::make_unique<LraSolver>();
    lra->setNativeTerms(ir);
    lra->setSharedTermRegistry(sharedTermRegistry.get());
    lra->setRegistry(&registry);
    theoryManager.registerSolver(std::move(lra));
    theoryManager.setSharedTermRegistry(sharedTermRegistry.get());
    theoryManager.setRegistry(&registry);
    theoryManager.setCombinationMode(true);
    theoryManager.setArrayCombinationMode(true);
}

void buildArrayLIA(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto& sharedTermRegistry = *c.sharedTermRegistry;
    NativeTerms* ir = c.ir;
    SortId boolSortId = c.boolSortId;
    // Arrays + LIA (+ UF). LIA is non-convex, so enable nonConvex combination.
    sharedTermRegistry = std::make_unique<SharedTermRegistry>();
    sharedTermRegistry->setNativeTerms(ir);
    {
        Purifier purifier(*ir, *sharedTermRegistry, boolSortId);
        purifier.setArithTheory(TheoryId::LIA);
        purifier.run();
    }
    auto euf = std::make_unique<EufSolver>();
    euf->setNativeTerms(ir);
    euf->setSharedTermRegistry(sharedTermRegistry.get());
    euf->enableArrays(&registry);
    theoryManager.registerSolver(std::move(euf));
    auto lia = std::make_unique<LiaSolver>();
    lia->setNativeTerms(ir);
    lia->setSharedTermRegistry(sharedTermRegistry.get());
    lia->setRegistry(&registry);
    theoryManager.registerSolver(std::move(lia));
    theoryManager.setSharedTermRegistry(sharedTermRegistry.get());
    theoryManager.setRegistry(&registry);
    theoryManager.setCombinationMode(true);
    theoryManager.setNonConvexMode(true);
    theoryManager.setArrayCombinationMode(true);
}

// the PURE UF-arith builders so the model-based arrangement can fire UF
// congruence over arith-equal arguments. Scoped here (not datatype/array).
void buildUFLRA(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto& sharedTermRegistry = *c.sharedTermRegistry;
    NativeTerms* ir = c.ir;
    SortId boolSortId = c.boolSortId;
    sharedTermRegistry = std::make_unique<SharedTermRegistry>();
    sharedTermRegistry->setNativeTerms(ir);
    {
        Purifier purifier(*ir, *sharedTermRegistry, boolSortId);
        purifier.run();
    }
    auto euf = std::make_unique<EufSolver>();
    euf->setNativeTerms(ir);
    euf->setSharedTermRegistry(sharedTermRegistry.get());
    theoryManager.registerSolver(std::move(euf));
    auto lra = std::make_unique<LraSolver>();
    lra->setNativeTerms(ir);
    lra->setSharedTermRegistry(sharedTermRegistry.get());
    lra->setRegistry(&registry);
    theoryManager.registerSolver(std::move(lra));
    theoryManager.setSharedTermRegistry(sharedTermRegistry.get());
    theoryManager.setRegistry(&registry);
    theoryManager.setCombinationMode(true);
}

void buildUFLIA(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto& sharedTermRegistry = *c.sharedTermRegistry;
    auto& result = *c.result;
    NativeTerms* ir = c.ir;
    SortId boolSortId = c.boolSortId;
    if (c.features.hasRealVar || c.features.hasNonlinear || c.features.hasMixedIntReal) {
        result.logicMismatch = true;
    } else {
        sharedTermRegistry = std::make_unique<SharedTermRegistry>();
        sharedTermRegistry->setNativeTerms(ir);
        {
            Purifier purifier(*ir, *sharedTermRegistry, boolSortId);
            purifier.setArithTheory(TheoryId::LIA);
            purifier.run();
        }
        auto euf = std::make_unique<EufSolver>();
        euf->setNativeTerms(ir);
        euf->setSharedTermRegistry(sharedTermRegistry.get());
        theoryManager.registerSolver(std::move(euf));
        auto lia = std::make_unique<LiaSolver>();
        lia->setNativeTerms(ir);
        lia->setSharedTermRegistry(sharedTermRegistry.get());
        lia->setRegistry(&registry);
        theoryManager.registerSolver(std::move(lia));
        theoryManager.setSharedTermRegistry(sharedTermRegistry.get());
        theoryManager.setRegistry(&registry);
        theoryManager.setCombinationMode(true);
        theoryManager.setNonConvexMode(true);
    }
}

void buildUFNIA(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto& sharedTermRegistry = *c.sharedTermRegistry;
    auto& result = *c.result;
    NativeTerms* ir = c.ir;
    SortId boolSortId = c.boolSortId;
    sharedTermRegistry = std::make_unique<SharedTermRegistry>();
    sharedTermRegistry->setNativeTerms(ir);
    {
        Purifier purifier(*ir, *sharedTermRegistry, boolSortId);
        purifier.setArithTheory(TheoryId::NIA);
        purifier.run();
    }
    auto polyKernel = createPolynomialKernel();
    result.polyKernelRaw = polyKernel.get();
    auto euf = std::make_unique<EufSolver>();
    euf->setNativeTerms(ir);
    euf->setSharedTermRegistry(sharedTermRegistry.get());
    theoryManager.registerSolver(std::move(euf));
    auto nia = std::make_unique<NiaSolver>(std::move(polyKernel));
    nia->setNativeTerms(ir);
    nia->setSharedTermRegistry(sharedTermRegistry.get());
    nia->setRegistry(&registry);
    theoryManager.registerSolver(std::move(nia));
    auto lia = std::make_unique<LiaSolver>();
    lia->setNativeTerms(ir);
    lia->setSharedTermRegistry(sharedTermRegistry.get());
    lia->setRegistry(&registry);
    theoryManager.registerSolver(std::move(lia));
    theoryManager.setSharedTermRegistry(sharedTermRegistry.get());
    theoryManager.setRegistry(&registry);
    theoryManager.setCombinationMode(true);
    theoryManager.setNonConvexMode(true);
}

void buildUFDTNIA(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto& sharedTermRegistry = *c.sharedTermRegistry;
    auto& result = *c.result;
    NativeTerms* ir = c.ir;
    SortId boolSortId = c.boolSortId;
    theoryManager.setHasDatatypes(true);  // (#77) scope UF-arith arrangement out
    // UF + datatypes + NIA. Same shape as QF_UFNIA with DtReasoner enabled.
    sharedTermRegistry = std::make_unique<SharedTermRegistry>();
    sharedTermRegistry->setNativeTerms(ir);
    {
        Purifier purifier(*ir, *sharedTermRegistry, boolSortId);
        purifier.setArithTheory(TheoryId::NIA);
        purifier.run();
    }
    auto polyKernel = createPolynomialKernel();
    result.polyKernelRaw = polyKernel.get();
    auto euf = std::make_unique<EufSolver>();
    euf->setNativeTerms(ir);
    euf->setSharedTermRegistry(sharedTermRegistry.get());
    euf->enableDts(&registry);
    theoryManager.registerSolver(std::move(euf));
    auto nia = std::make_unique<NiaSolver>(std::move(polyKernel));
    nia->setNativeTerms(ir);
    nia->setSharedTermRegistry(sharedTermRegistry.get());
    nia->setRegistry(&registry);
    theoryManager.registerSolver(std::move(nia));
    auto lia = std::make_unique<LiaSolver>();
    lia->setNativeTerms(ir);
    lia->setSharedTermRegistry(sharedTermRegistry.get());
    lia->setRegistry(&registry);
    theoryManager.registerSolver(std::move(lia));
    theoryManager.setSharedTermRegistry(sharedTermRegistry.get());
    theoryManager.setRegistry(&registry);
    theoryManager.setCombinationMode(true);
    theoryManager.setNonConvexMode(true);
}

void buildUFDTLIA(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto& sharedTermRegistry = *c.sharedTermRegistry;
    NativeTerms* ir = c.ir;
    SortId boolSortId = c.boolSortId;
    theoryManager.setHasDatatypes(true);  // (#77) scope UF-arith arrangement out
    // UF + datatypes + LIA.
    sharedTermRegistry = std::make_unique<SharedTermRegistry>();
    sharedTermRegistry->setNativeTerms(ir);
    {
        Purifier purifier(*ir, *sharedTermRegistry, boolSortId);
        purifier.setArithTheory(TheoryId::LIA);
        purifier.run();
    }
    auto euf = std::make_unique<EufSolver>();
    euf->setNativeTerms(ir);
    euf->setSharedTermRegistry(sharedTermRegistry.get());
    euf->enableDts(&registry);
    theoryManager.registerSolver(std::move(euf));
    auto lia = std::make_unique<LiaSolver>();
    lia->setNativeTerms(ir);
    lia->setSharedTermRegistry(sharedTermRegistry.get());
    lia->setRegistry(&registry);
    theoryManager.registerSolver(std::move(lia));
    theoryManager.setSharedTermRegistry(sharedTermRegistry.get());
    theoryManager.setRegistry(&registry);
    theoryManager.setCombinationMode(true);
    theoryManager.setNonConvexMode(true);
}

void buildUFNRA(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto& sharedTermRegistry = *c.sharedTermRegistry;
    auto& result = *c.result;
    NativeTerms* ir = c.ir;
    SortId boolSortId = c.boolSortId;
    sharedTermRegistry = std::make_unique<SharedTermRegistry>();
    sharedTermRegistry->setNativeTerms(ir);
    {
        Purifier purifier(*ir, *sharedTermRegistry, boolSortId);
        purifier.setArithTheory(TheoryId::NRA);
        purifier.run();
    }
    auto polyKernel = createPolynomialKernel();
    result.polyKernelRaw = polyKernel.get();
    auto euf = std::make_unique<EufSolver>();
    euf->setNativeTerms(ir);
    euf->setSharedTermRegistry(sharedTermRegistry.get());
    theoryManager.registerSolver(std::move(euf));
    auto nra = std::make_unique<NraSolver>(std::move(polyKernel));
    nra->setNativeTerms(ir);
    nra->setSharedTermRegistry(sharedTermRegistry.get());
    theoryManager.registerSolver(std::move(nra));
    auto lra = std::make_unique<LraSolver>();
    lra->setNativeTerms(ir);
    lra->setSharedTermRegistry(sharedTermRegistry.get());
    lra->setRegistry(&registry);
    theoryManager.registerSolver(std::move(lra));
    theoryManager.setSharedTermRegistry(sharedTermRegistry.get());
    theoryManager.setRegistry(&registry);
    theoryManager.setCombinationMode(true);
    theoryManager.setNonConvexMode(true);
}

void buildArrayNIA(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto& sharedTermRegistry = *c.sharedTermRegistry;
    auto& result = *c.result;
    NativeTerms* ir = c.ir;
    SortId boolSortId = c.boolSortId;
    // Arrays + NIA (+ UF). QF_UFNIA's stack crossed with array enablement.
    sharedTermRegistry = std::make_unique<SharedTermRegistry>();
    sharedTermRegistry->setNativeTerms(ir);
    {
        Purifier purifier(*ir, *sharedTermRegistry, boolSortId);
        purifier.setArithTheory(TheoryId::NIA);
        purifier.run();
    }
    auto polyKernel = createPolynomialKernel();
    result.polyKernelRaw = polyKernel.get();
    auto euf = std::make_unique<EufSolver>();
    euf->setNativeTerms(ir);
    euf->setSharedTermRegistry(sharedTermRegistry.get());
    euf->enableArrays(&registry);
    theoryManager.registerSolver(std::move(euf));
    auto nia = std::make_unique<NiaSolver>(std::move(polyKernel));
    nia->setNativeTerms(ir);
    nia->setSharedTermRegistry(sharedTermRegistry.get());
    nia->setRegistry(&registry);
    theoryManager.registerSolver(std::move(nia));
    auto lia = std::make_unique<LiaSolver>();
    lia->setNativeTerms(ir);
    lia->setSharedTermRegistry(sharedTermRegistry.get());
    lia->setRegistry(&registry);
    theoryManager.registerSolver(std::move(lia));
    theoryManager.setSharedTermRegistry(sharedTermRegistry.get());
    theoryManager.setRegistry(&registry);
    theoryManager.setCombinationMode(true);
    theoryManager.setNonConvexMode(true);
    theoryManager.setArrayCombinationMode(true);
}

void buildUnsupportedUF(BuildContext& c) {
    // Bare "UF" with no QF_ prefix: not supported here.
    c.result->success = false;
}

// Fallback when no builder is registered for the logic string: route by the
// detected features. Not registered in the table — called directly.
void buildFeatureRouted(BuildContext& c) {
    if (c.features.hasUF) {
        c.result->success = false;
        return;
    }
    switch (featureArithmeticTheory(c.features)) {
    case TheoryId::LIA: buildLIA(c); break;
    case TheoryId::LRA: buildLRA(c); break;
    case TheoryId::NIA: buildNIA(c); break;
    case TheoryId::NRA: buildNRA(c); break;
    case TheoryId::LIRA: buildLIRA(c); break;
    case TheoryId::NIRA: buildNIRA(c); break;
    default: break;
    }
}

} // namespace

TheoryId featureArithmeticTheory(const LogicFeatures& f) {
    if (f.hasMixedIntReal) return f.hasNonlinear ? TheoryId::NIRA : TheoryId::LIRA;
    // Literal sorts must not override the domain of a remaining variable.
    if (f.hasIntVar) return f.hasNonlinear ? TheoryId::NIA : TheoryId::LIA;
    if (f.hasRealVar) return f.hasNonlinear ? TheoryId::NRA : TheoryId::LRA;
    if (f.hasReal) return f.hasNonlinear ? TheoryId::NRA : TheoryId::LRA;
    if (f.hasInt) return f.hasNonlinear ? TheoryId::NIA : TheoryId::LIA;
    return TheoryId::Bool;
}

void SolverRegistry::ensureBuiltinsRegistered() {
    static std::once_flag once;
    std::call_once(once, [] {
        registerLogic({"QF_LIA", "LIA"}, 0, buildLIA, "LIA");
        registerLogic({"QF_LRA", "LRA"}, 0, buildLRA, "LRA");
        registerLogic({"QF_NRA", "NRA"}, 0, buildNRA, "NRA");
        registerLogic({"QF_NIA", "NIA"}, 0, buildNIA, "NIA");
        registerLogic({"QF_LIRA", "LIRA"}, 0, buildLIRA, "LIRA");
        registerLogic({"QF_NIRA", "NIRA"}, 0, buildNIRA, "NIRA");
        registerLogic({"QF_IDL", "IDL"}, 0, buildIDL, "IDL");
        registerLogic({"QF_RDL", "RDL"}, 0, buildRDL, "RDL");
        registerLogic({"QF_UF"}, 0, buildUF, "UF");
        registerLogic({"QF_DT", "QF_UFDT", "DT", "UFDT"}, 0, buildDT, "DT");
        registerLogic({"QF_AX"}, 0, buildAX, "AX");
        registerLogic({"QF_ALRA", "ALRA", "QF_AUFLRA", "AUFLRA"}, 0, buildArrayLRA, "ArrayLRA");
        registerLogic({"QF_ALIA", "ALIA", "QF_AUFLIA", "AUFLIA"}, 0, buildArrayLIA, "ArrayLIA");
        registerLogic({"QF_UFLRA", "UFLRA"}, 0, buildUFLRA, "UFLRA");
        registerLogic({"QF_UFLIA", "UFLIA"}, 0, buildUFLIA, "UFLIA");
        registerLogic({"QF_UFNIA", "UFNIA"}, 0, buildUFNIA, "UFNIA");
        registerLogic({"QF_UFDTNIA", "UFDTNIA"}, 0, buildUFDTNIA, "UFDTNIA");
        registerLogic({"QF_UFDTLIA", "UFDTLIA"}, 0, buildUFDTLIA, "UFDTLIA");
        registerLogic({"QF_UFNRA", "UFNRA"}, 0, buildUFNRA, "UFNRA");
        registerLogic({"QF_ANIA", "ANIA", "QF_AUFNIA", "AUFNIA"}, 0, buildArrayNIA, "ArrayNIA");
        registerLogic({"UF"}, 0, buildUnsupportedUF, "UF-unsupported");
    });
}

SolverSetupResult setupSolvers(
    const std::string& logic,
    const LogicFeatures& features,
    NativeTerms* ir,
    TheoryAtomRegistry& registry,
    TheoryManager& theoryManager,
    std::unique_ptr<SharedTermRegistry>& sharedTermRegistry,
    SortId boolSortId)
{
    SolverSetupResult result;
    // This factory constructs quantifier-free CDCL(T) stacks. Do not allow a
    // logic alias (LIA/NRA/ALL) to silently strip quantifiers at this boundary.
    if (features.hasQuantifier) {
        result.success = false;
        return result;
    }
    SolverRegistry::ensureBuiltinsRegistered();
    BuildContext ctx{
        logic, features, ir, &registry, &theoryManager, &sharedTermRegistry,
        boolSortId,
        &result};

    if (const LogicBuilder* builder = SolverRegistry::builderFor(logic)) {
        (*builder)(ctx);
    } else {
        // No declared logic or unrecognized logic: route by detected features.
        buildFeatureRouted(ctx);
    }
    return result;
}

} // namespace xolver
