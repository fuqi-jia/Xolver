#include "frontend/factory/TheoryFactory.h"
#include "frontend/factory/SolverRegistry.h"
#include "theory/arith/lra/LraSolver.h"
#include "theory/arith/lia/LiaSolver.h"
#include "theory/arith/nra/NraSolver.h"
#include "theory/arith/nia/NiaSolver.h"
#include "theory/arith/lira/LiraSolver.h"
#include "theory/arith/nira/NiraSolver.h"
#include "theory/arith/idl/IdlSolver.h"
#include "theory/arith/rdl/RdlSolver.h"
#include "theory/euf/EufSolver.h"
#include "theory/combination/Purifier.h"
#include "experimental/mcsat/McsatSolver.h"
#include "theory/arith/nia/mcsat/NiaMcsatEngine.h"
#include "theory/arith/nra/backend/LibpolyBackend.h"
#include "theory/arith/nra/nlsat/NlsatEngine.h"
#include <cstdlib>
#include <iostream>
#include <mutex>

namespace xolver {

namespace {

void configureLia(LiaSolver& lia, const LiaConfig& cfg) {
    lia.setSafeMode(cfg.safeMode);
    lia.setUltraSafeMode(cfg.ultraSafeMode);
    if (cfg.enableSingleVar) lia.setEnableSingleVarTightening(true);
    if (cfg.enableGcdIneq) lia.setEnableGcdIneqTightening(true);
    if (cfg.enableEqGcdNorm) lia.setEnableEqGcdNormalization(true);
}

// ---------------------------------------------------------------------------
// Builders — one per logic family. Each aliases the BuildContext fields it uses
// so the body matches the legacy TheoryFactory branch verbatim (the only change
// is configureLia(*lia) -> configureLia(*lia, c.lia)). createPolynomialKernel is
// declared in theory/arith/poly/PolynomialKernel.h.
// ---------------------------------------------------------------------------

void buildLIA(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto lia = std::make_unique<LiaSolver>();
    lia->setRegistry(&registry);
    configureLia(*lia, c.lia);
    theoryManager.registerSolver(std::move(lia));
}

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
    CoreIr* ir = c.ir;
    // XOLVER_NRA_MCSAT (default-OFF): swap NraSolver out for the experimental
    // MCSAT-style NlsatEngine. The LRA sibling stays registered. Sound: NlsatEngine
    // returns Unknown when it cannot decide; it never produces UNSAT.
    if (const char* e = std::getenv("XOLVER_NRA_MCSAT"); e && *e && *e != '0') {
        auto polyKernel = createPolynomialKernel();
        result.polyKernelRaw = polyKernel.get();
        auto algebra = std::make_unique<LibpolyBackend>(polyKernel.get());
        auto engine = std::make_unique<nlsat::NlsatEngine>();
        engine->setAlgebra(polyKernel.get(), algebra.get());
        engine->setCoreIr(ir);
        auto mcsat = std::make_unique<McsatSolver>();
        mcsat->setEngine(std::move(engine), TheoryId::NRA);
        mcsat->setKernel(std::move(polyKernel));
        mcsat->setAlgebra(std::move(algebra));
        theoryManager.registerSolver(std::move(mcsat));
        auto lra = std::make_unique<LraSolver>();
        lra->setRegistry(&registry);
        theoryManager.registerSolver(std::move(lra));
    } else {
        auto polyKernel = createPolynomialKernel();
        result.polyKernelRaw = polyKernel.get();
        auto lra = std::make_unique<LraSolver>();
        lra->setRegistry(&registry);
        LraSolver* lraPtr = lra.get();
        auto nra = std::make_unique<NraSolver>(std::move(polyKernel));
        nra->setRegistry(&registry);  // XOLVER_NRA_LINEARIZE cut-feeder
        nra->setLinearSibling(lraPtr);  // XOLVER_NRA_LINEARIZE relaxation-model source
        theoryManager.registerSolver(std::move(nra));
        theoryManager.registerSolver(std::move(lra));
    }
}

void buildNIA(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto& result = *c.result;
    CoreIr* ir = c.ir;
    // XOLVER_NIA_MCSAT (default-OFF): swap NiaSolver for the experimental MCSAT
    // NiaMcsatEngine. Sound floor identical to NRA — Unknown, never wrong UNSAT.
    if (const char* e = std::getenv("XOLVER_NIA_MCSAT"); e && *e && *e != '0') {
        auto polyKernel = createPolynomialKernel();
        result.polyKernelRaw = polyKernel.get();
        auto engine = std::make_unique<nia_mcsat::NiaMcsatEngine>();
        engine->setKernel(polyKernel.get());
        engine->setCoreIr(ir);
        engine->setRegistry(&registry);  // mints integrality-split bound atoms
        auto mcsat = std::make_unique<McsatSolver>();
        mcsat->setEngine(std::move(engine), TheoryId::NIA);
        mcsat->setKernel(std::move(polyKernel));
        theoryManager.registerSolver(std::move(mcsat));
        auto lia = std::make_unique<LiaSolver>();
        lia->setRegistry(&registry);
        configureLia(*lia, c.lia);
        theoryManager.registerSolver(std::move(lia));
    } else {
        auto polyKernel = createPolynomialKernel();
        result.polyKernelRaw = polyKernel.get();
        auto nia = std::make_unique<NiaSolver>(std::move(polyKernel));
        nia->setRegistry(&registry);
        nia->setCoreIr(ir);  // needed by Z5 BOOL_EXTEND + Farkas-Or hooks
        theoryManager.registerSolver(std::move(nia));
        auto lia = std::make_unique<LiaSolver>();
        lia->setRegistry(&registry);
        configureLia(*lia, c.lia);
        theoryManager.registerSolver(std::move(lia));
    }
}

void buildLIRA(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    CoreIr* ir = c.ir;
    auto lira = std::make_unique<LiraSolver>();
    lira->setRegistry(&registry);
    lira->setCoreIr(ir);
    theoryManager.registerSolver(std::move(lira));
}

void buildNIRA(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto& result = *c.result;
    CoreIr* ir = c.ir;
    auto polyKernel = createPolynomialKernel();
    result.polyKernelRaw = polyKernel.get();
    auto nira = std::make_unique<NiraSolver>(std::move(polyKernel));
    nira->setRegistry(&registry);
    nira->setCoreIr(ir);
    theoryManager.registerSolver(std::move(nira));

    auto lira = std::make_unique<LiraSolver>();
    lira->setRegistry(&registry);
    lira->setCoreIr(ir);
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
    CoreIr* ir = c.ir;
    auto euf = std::make_unique<EufSolver>();
    euf->setCoreIr(ir);
    euf->setEqualityAtomRegistry(&registry);  // XOLVER_EUF_PROP theory propagation
    theoryManager.registerSolver(std::move(euf));
}

void buildDT(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    CoreIr* ir = c.ir;
    // Algebraic datatypes (+ UF). One shared egraph; DtReasoner layers the
    // free-algebra axioms on top. QF_DT and QF_UFDT share this branch.
    auto euf = std::make_unique<EufSolver>();
    euf->setCoreIr(ir);
    euf->enableDts(&registry);
    theoryManager.registerSolver(std::move(euf));
}

void buildAX(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    CoreIr* ir = c.ir;
    // Pure array theory (arrays + EUF, no arithmetic). ArrayReasoner adds axioms.
    auto euf = std::make_unique<EufSolver>();
    euf->setCoreIr(ir);
    euf->enableArrays(&registry);
    theoryManager.registerSolver(std::move(euf));
}

void buildArrayLRA(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto& sharedTermRegistry = *c.sharedTermRegistry;
    CoreIr* ir = c.ir;
    SortId boolSortId = c.boolSortId;
    // Arrays + LRA (+ UF). Nelson-Oppen exchanges index/element (dis)equalities.
    sharedTermRegistry = std::make_unique<SharedTermRegistry>();
    sharedTermRegistry->setCoreIr(ir);
    {
        Purifier purifier(*ir, *sharedTermRegistry, boolSortId);
        purifier.run();
    }
    auto euf = std::make_unique<EufSolver>();
    euf->setCoreIr(ir);
    euf->setSharedTermRegistry(sharedTermRegistry.get());
    euf->enableArrays(&registry);
    theoryManager.registerSolver(std::move(euf));
    auto lra = std::make_unique<LraSolver>();
    lra->setCoreIr(ir);
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
    CoreIr* ir = c.ir;
    SortId boolSortId = c.boolSortId;
    // Arrays + LIA (+ UF). LIA is non-convex, so enable nonConvex combination.
    sharedTermRegistry = std::make_unique<SharedTermRegistry>();
    sharedTermRegistry->setCoreIr(ir);
    {
        Purifier purifier(*ir, *sharedTermRegistry, boolSortId);
        purifier.setArithTheory(TheoryId::LIA);
        purifier.run();
    }
    auto euf = std::make_unique<EufSolver>();
    euf->setCoreIr(ir);
    euf->setSharedTermRegistry(sharedTermRegistry.get());
    euf->enableArrays(&registry);
    theoryManager.registerSolver(std::move(euf));
    auto lia = std::make_unique<LiaSolver>();
    lia->setCoreIr(ir);
    lia->setSharedTermRegistry(sharedTermRegistry.get());
    lia->setRegistry(&registry);
    configureLia(*lia, c.lia);
    theoryManager.registerSolver(std::move(lia));
    theoryManager.setSharedTermRegistry(sharedTermRegistry.get());
    theoryManager.setRegistry(&registry);
    theoryManager.setCombinationMode(true);
    theoryManager.setNonConvexMode(true);
    theoryManager.setArrayCombinationMode(true);
}

void buildUFLRA(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto& sharedTermRegistry = *c.sharedTermRegistry;
    CoreIr* ir = c.ir;
    SortId boolSortId = c.boolSortId;
    sharedTermRegistry = std::make_unique<SharedTermRegistry>();
    sharedTermRegistry->setCoreIr(ir);
    {
        Purifier purifier(*ir, *sharedTermRegistry, boolSortId);
        purifier.run();
    }
    auto euf = std::make_unique<EufSolver>();
    euf->setCoreIr(ir);
    euf->setSharedTermRegistry(sharedTermRegistry.get());
    theoryManager.registerSolver(std::move(euf));
    auto lra = std::make_unique<LraSolver>();
    lra->setCoreIr(ir);
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
    CoreIr* ir = c.ir;
    SortId boolSortId = c.boolSortId;
    if (c.features.hasRealVar || c.features.hasNonlinear || c.features.hasMixedIntReal) {
        result.logicMismatch = true;
    } else {
        sharedTermRegistry = std::make_unique<SharedTermRegistry>();
        sharedTermRegistry->setCoreIr(ir);
        {
            Purifier purifier(*ir, *sharedTermRegistry, boolSortId);
            purifier.setArithTheory(TheoryId::LIA);
            purifier.run();
        }
        auto euf = std::make_unique<EufSolver>();
        euf->setCoreIr(ir);
        euf->setSharedTermRegistry(sharedTermRegistry.get());
        theoryManager.registerSolver(std::move(euf));
        auto lia = std::make_unique<LiaSolver>();
        lia->setCoreIr(ir);
        lia->setSharedTermRegistry(sharedTermRegistry.get());
        lia->setRegistry(&registry);
        configureLia(*lia, c.lia);
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
    CoreIr* ir = c.ir;
    SortId boolSortId = c.boolSortId;
    sharedTermRegistry = std::make_unique<SharedTermRegistry>();
    sharedTermRegistry->setCoreIr(ir);
    {
        Purifier purifier(*ir, *sharedTermRegistry, boolSortId);
        purifier.setArithTheory(TheoryId::NIA);
        purifier.run();
    }
    auto polyKernel = createPolynomialKernel();
    result.polyKernelRaw = polyKernel.get();
    auto euf = std::make_unique<EufSolver>();
    euf->setCoreIr(ir);
    euf->setSharedTermRegistry(sharedTermRegistry.get());
    theoryManager.registerSolver(std::move(euf));
    auto nia = std::make_unique<NiaSolver>(std::move(polyKernel));
    nia->setCoreIr(ir);
    nia->setSharedTermRegistry(sharedTermRegistry.get());
    nia->setRegistry(&registry);
    theoryManager.registerSolver(std::move(nia));
    auto lia = std::make_unique<LiaSolver>();
    lia->setCoreIr(ir);
    lia->setSharedTermRegistry(sharedTermRegistry.get());
    lia->setRegistry(&registry);
    configureLia(*lia, c.lia);
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
    CoreIr* ir = c.ir;
    SortId boolSortId = c.boolSortId;
    // UF + datatypes + NIA. Same shape as QF_UFNIA with DtReasoner enabled.
    sharedTermRegistry = std::make_unique<SharedTermRegistry>();
    sharedTermRegistry->setCoreIr(ir);
    {
        Purifier purifier(*ir, *sharedTermRegistry, boolSortId);
        purifier.setArithTheory(TheoryId::NIA);
        purifier.run();
    }
    auto polyKernel = createPolynomialKernel();
    result.polyKernelRaw = polyKernel.get();
    auto euf = std::make_unique<EufSolver>();
    euf->setCoreIr(ir);
    euf->setSharedTermRegistry(sharedTermRegistry.get());
    euf->enableDts(&registry);
    theoryManager.registerSolver(std::move(euf));
    auto nia = std::make_unique<NiaSolver>(std::move(polyKernel));
    nia->setCoreIr(ir);
    nia->setSharedTermRegistry(sharedTermRegistry.get());
    nia->setRegistry(&registry);
    theoryManager.registerSolver(std::move(nia));
    auto lia = std::make_unique<LiaSolver>();
    lia->setCoreIr(ir);
    lia->setSharedTermRegistry(sharedTermRegistry.get());
    lia->setRegistry(&registry);
    configureLia(*lia, c.lia);
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
    CoreIr* ir = c.ir;
    SortId boolSortId = c.boolSortId;
    // UF + datatypes + LIA.
    sharedTermRegistry = std::make_unique<SharedTermRegistry>();
    sharedTermRegistry->setCoreIr(ir);
    {
        Purifier purifier(*ir, *sharedTermRegistry, boolSortId);
        purifier.setArithTheory(TheoryId::LIA);
        purifier.run();
    }
    auto euf = std::make_unique<EufSolver>();
    euf->setCoreIr(ir);
    euf->setSharedTermRegistry(sharedTermRegistry.get());
    euf->enableDts(&registry);
    theoryManager.registerSolver(std::move(euf));
    auto lia = std::make_unique<LiaSolver>();
    lia->setCoreIr(ir);
    lia->setSharedTermRegistry(sharedTermRegistry.get());
    lia->setRegistry(&registry);
    configureLia(*lia, c.lia);
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
    CoreIr* ir = c.ir;
    SortId boolSortId = c.boolSortId;
    sharedTermRegistry = std::make_unique<SharedTermRegistry>();
    sharedTermRegistry->setCoreIr(ir);
    {
        Purifier purifier(*ir, *sharedTermRegistry, boolSortId);
        purifier.setArithTheory(TheoryId::NRA);
        purifier.run();
    }
    auto polyKernel = createPolynomialKernel();
    result.polyKernelRaw = polyKernel.get();
    auto euf = std::make_unique<EufSolver>();
    euf->setCoreIr(ir);
    euf->setSharedTermRegistry(sharedTermRegistry.get());
    theoryManager.registerSolver(std::move(euf));
    auto nra = std::make_unique<NraSolver>(std::move(polyKernel));
    nra->setCoreIr(ir);
    nra->setSharedTermRegistry(sharedTermRegistry.get());
    nra->setRegistry(&registry);  // XOLVER_NRA_LINEARIZE cut-feeder
    theoryManager.registerSolver(std::move(nra));
    auto lra = std::make_unique<LraSolver>();
    lra->setCoreIr(ir);
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
    CoreIr* ir = c.ir;
    SortId boolSortId = c.boolSortId;
    // Arrays + NIA (+ UF). QF_UFNIA's stack crossed with array enablement.
    sharedTermRegistry = std::make_unique<SharedTermRegistry>();
    sharedTermRegistry->setCoreIr(ir);
    {
        Purifier purifier(*ir, *sharedTermRegistry, boolSortId);
        purifier.setArithTheory(TheoryId::NIA);
        purifier.run();
    }
    auto polyKernel = createPolynomialKernel();
    result.polyKernelRaw = polyKernel.get();
    auto euf = std::make_unique<EufSolver>();
    euf->setCoreIr(ir);
    euf->setSharedTermRegistry(sharedTermRegistry.get());
    euf->enableArrays(&registry);
    theoryManager.registerSolver(std::move(euf));
    auto nia = std::make_unique<NiaSolver>(std::move(polyKernel));
    nia->setCoreIr(ir);
    nia->setSharedTermRegistry(sharedTermRegistry.get());
    nia->setRegistry(&registry);
    theoryManager.registerSolver(std::move(nia));
    auto lia = std::make_unique<LiaSolver>();
    lia->setCoreIr(ir);
    lia->setSharedTermRegistry(sharedTermRegistry.get());
    lia->setRegistry(&registry);
    configureLia(*lia, c.lia);
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
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto& result = *c.result;
    const LogicFeatures& features = c.features;
    if (features.hasUF) {
        result.success = false;
    } else if (features.hasMixedIntReal) {
        if (features.hasNonlinear) {
            auto polyKernel = createPolynomialKernel();
            result.polyKernelRaw = polyKernel.get();
            auto nira = std::make_unique<NiraSolver>(std::move(polyKernel));
            nira->setRegistry(&registry);
            theoryManager.registerSolver(std::move(nira));
        } else {
            auto lira = std::make_unique<LiraSolver>();
            lira->setRegistry(&registry);
            lira->setCoreIr(c.ir);
            theoryManager.registerSolver(std::move(lira));
        }
    } else if (features.hasIntVar && features.hasNonlinear) {
        auto polyKernel = createPolynomialKernel();
        result.polyKernelRaw = polyKernel.get();
        auto nia = std::make_unique<NiaSolver>(std::move(polyKernel));
        nia->setRegistry(&registry);
        theoryManager.registerSolver(std::move(nia));
        auto lia = std::make_unique<LiaSolver>();
        lia->setRegistry(&registry);
        configureLia(*lia, c.lia);
        theoryManager.registerSolver(std::move(lia));
    } else if (features.hasIntVar) {
        auto lia = std::make_unique<LiaSolver>();
        lia->setRegistry(&registry);
        configureLia(*lia, c.lia);
        theoryManager.registerSolver(std::move(lia));
    } else if (features.hasRealVar && features.hasNonlinear) {
        auto polyKernel = createPolynomialKernel();
        result.polyKernelRaw = polyKernel.get();
        auto lra = std::make_unique<LraSolver>();
        lra->setRegistry(&registry);
        LraSolver* lraPtr = lra.get();
        auto nra = std::make_unique<NraSolver>(std::move(polyKernel));
        nra->setRegistry(&registry);  // XOLVER_NRA_LINEARIZE cut-feeder
        nra->setLinearSibling(lraPtr);  // XOLVER_NRA_LINEARIZE relaxation-model source
        theoryManager.registerSolver(std::move(nra));
        theoryManager.registerSolver(std::move(lra));
    } else if (features.hasRealVar) {
        theoryManager.registerSolver(std::make_unique<LraSolver>());
    }
}

} // namespace

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
    CoreIr* ir,
    TheoryAtomRegistry& registry,
    TheoryManager& theoryManager,
    std::unique_ptr<SharedTermRegistry>& sharedTermRegistry,
    SortId boolSortId,
    bool liaSafeMode,
    bool liaUltraSafeMode,
    bool liaEnableSingleVar,
    bool liaEnableGcdIneq,
    bool liaEnableEqGcdNorm)
{
    SolverRegistry::ensureBuiltinsRegistered();

    SolverSetupResult result;
    BuildContext ctx{
        logic, features, ir, &registry, &theoryManager, &sharedTermRegistry,
        boolSortId,
        LiaConfig{liaSafeMode, liaUltraSafeMode, liaEnableSingleVar,
                  liaEnableGcdIneq, liaEnableEqGcdNorm},
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
