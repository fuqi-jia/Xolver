#include "frontend/factory/TheoryFactory.h"
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

namespace xolver {

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
    auto configureLia = [&](LiaSolver& lia) {
        lia.setSafeMode(liaSafeMode);
        lia.setUltraSafeMode(liaUltraSafeMode);
        if (liaEnableSingleVar) lia.setEnableSingleVarTightening(true);
        if (liaEnableGcdIneq) lia.setEnableGcdIneqTightening(true);
        if (liaEnableEqGcdNorm) lia.setEnableEqGcdNormalization(true);
    };
    SolverSetupResult result;
    result.polyKernelRaw = nullptr;

    // createPolynomialKernel is declared in theory/arith/poly/PolynomialKernel.h

    if (logic == "QF_LIA" || logic == "LIA") {
        auto lia = std::make_unique<LiaSolver>();
        lia->setRegistry(&registry);
        configureLia(*lia);
        theoryManager.registerSolver(std::move(lia));
    } else if (logic == "QF_LRA" || logic == "LRA") {
        auto lra = std::make_unique<LraSolver>();
        lra->setRegistry(&registry);
        theoryManager.registerSolver(std::move(lra));
        theoryManager.setRegistry(&registry);  // needed by cb_decide evalTheoryAtom
    } else if (logic == "QF_NRA" || logic == "NRA") {
        // XOLVER_NRA_MCSAT (default-OFF): swap NraSolver out for the
        // experimental MCSAT-style NlsatEngine. The LRA sibling is still
        // registered so combination/linearization paths keep working —
        // the engine declares TheoryId::NRA so TheoryManager routes NRA
        // atoms to it. Sound: NlsatEngine returns Unknown when it cannot
        // decide; it never produces UNSAT (see MCSatEngine.h §15.6).
        if (const char* e = std::getenv("XOLVER_NRA_MCSAT"); e && *e && *e != '0') {
            auto polyKernel = createPolynomialKernel();
            result.polyKernelRaw = polyKernel.get();
            // Limitation-(b) fix: wire the libpoly-backed AlgebraBackend so
            // NlsatEngine can use isolateRealRoots / specializeToUnivariate
            // for algebraic-root explain in future extensions. The backend
            // is owned by McsatSolver so its lifetime matches the engine's.
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
            // Create the LRA sibling first so NRA can hold a raw pointer to it for
            // the XOLVER_NRA_LINEARIZE relaxation-model read (harmless when OFF).
            auto lra = std::make_unique<LraSolver>();
            lra->setRegistry(&registry);
            LraSolver* lraPtr = lra.get();
            auto nra = std::make_unique<NraSolver>(std::move(polyKernel));
            nra->setRegistry(&registry);  // XOLVER_NRA_LINEARIZE cut-feeder
            nra->setLinearSibling(lraPtr);  // XOLVER_NRA_LINEARIZE relaxation-model source
            theoryManager.registerSolver(std::move(nra));
            theoryManager.registerSolver(std::move(lra));
        }
    } else if (logic == "QF_NIA" || logic == "NIA") {
        // XOLVER_NIA_MCSAT (default-OFF): swap NiaSolver out for the
        // experimental MCSAT NiaMcsatEngine. Sound floor identical to
        // the NRA variant — Unknown on indecision, never wrong UNSAT.
        if (const char* e = std::getenv("XOLVER_NIA_MCSAT"); e && *e && *e != '0') {
            auto polyKernel = createPolynomialKernel();
            result.polyKernelRaw = polyKernel.get();
            auto engine = std::make_unique<nia_mcsat::NiaMcsatEngine>();
            engine->setKernel(polyKernel.get());
            engine->setCoreIr(ir);
            auto mcsat = std::make_unique<McsatSolver>();
            mcsat->setEngine(std::move(engine), TheoryId::NIA);
            mcsat->setKernel(std::move(polyKernel));
            theoryManager.registerSolver(std::move(mcsat));
            auto lia = std::make_unique<LiaSolver>();
            lia->setRegistry(&registry);
            configureLia(*lia);
            theoryManager.registerSolver(std::move(lia));
        } else {
            auto polyKernel = createPolynomialKernel();
            result.polyKernelRaw = polyKernel.get();
            auto nia = std::make_unique<NiaSolver>(std::move(polyKernel));
            nia->setRegistry(&registry);
            nia->setCoreIr(ir);  // needed by Z5 BOOL_EXTEND + Farkas-Or hooks (added 2026-06-02)
            theoryManager.registerSolver(std::move(nia));
            auto lia = std::make_unique<LiaSolver>();
            lia->setRegistry(&registry);
            configureLia(*lia);
            theoryManager.registerSolver(std::move(lia));
        }
    } else if (logic == "QF_LIRA" || logic == "LIRA") {
        auto lira = std::make_unique<LiraSolver>();
        lira->setRegistry(&registry);
        lira->setCoreIr(ir);
        theoryManager.registerSolver(std::move(lira));
    } else if (logic == "QF_NIRA" || logic == "NIRA") {
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
    } else if (logic == "QF_IDL" || logic == "IDL") {
        auto idl = std::make_unique<IdlSolver>();
        idl->setRegistry(&registry);
        theoryManager.registerSolver(std::move(idl));
    } else if (logic == "QF_RDL" || logic == "RDL") {
        auto rdl = std::make_unique<RdlSolver>();
        rdl->setRegistry(&registry);
        theoryManager.registerSolver(std::move(rdl));
    } else if (logic == "QF_UF") {
        auto euf = std::make_unique<EufSolver>();
        euf->setCoreIr(ir);
        euf->setEqualityAtomRegistry(&registry);  // XOLVER_EUF_PROP theory propagation
        theoryManager.registerSolver(std::move(euf));
    } else if (logic == "QF_DT" || logic == "QF_UFDT" || logic == "DT" || logic == "UFDT") {
        // Algebraic datatypes (+ UF). One shared egraph hosts UF and the DT
        // operators; the DtReasoner layers the free-algebra axioms on top.
        // QF_DT and QF_UFDT share this branch (EUF already provides UF).
        auto euf = std::make_unique<EufSolver>();
        euf->setCoreIr(ir);
        euf->enableDts(&registry);
        theoryManager.registerSolver(std::move(euf));
    } else if (logic == "QF_AX") {
        // Pure array theory (arrays + EUF, uninterpreted/Int indices+elements,
        // no arithmetic). One shared egraph; ArrayReasoner adds the axioms.
        auto euf = std::make_unique<EufSolver>();
        euf->setCoreIr(ir);
        euf->enableArrays(&registry);
        theoryManager.registerSolver(std::move(euf));
    } else if (logic == "QF_ALRA" || logic == "ALRA" ||
               logic == "QF_AUFLRA" || logic == "AUFLRA") {
        // Arrays + LRA (+ UF). One shared EUF egraph hosts UF, the array
        // operators, and the shared index/element terms; LRA owns the reals.
        // Nelson-Oppen exchanges index/element (dis)equalities. UF is already
        // provided by EUF, so QF_ALRA and QF_AUFLRA share this branch.
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
    } else if (logic == "QF_ALIA" || logic == "ALIA" ||
               logic == "QF_AUFLIA" || logic == "AUFLIA") {
        // Arrays + LIA (+ UF). Same shape as the LRA array branch but over
        // integers. LIA is non-convex (disequalities), so enable nonConvex
        // combination mode (matching QF_UFLIA).
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
        configureLia(*lia);
        theoryManager.registerSolver(std::move(lia));
        theoryManager.setSharedTermRegistry(sharedTermRegistry.get());
        theoryManager.setRegistry(&registry);
        theoryManager.setCombinationMode(true);
        theoryManager.setNonConvexMode(true);
        theoryManager.setArrayCombinationMode(true);
    } else if (logic == "QF_UFLRA" || logic == "UFLRA") {
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
    } else if (logic == "QF_UFLIA" || logic == "UFLIA") {
        if (features.hasRealVar || features.hasNonlinear || features.hasMixedIntReal) {
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
            configureLia(*lia);
            theoryManager.registerSolver(std::move(lia));
            theoryManager.setSharedTermRegistry(sharedTermRegistry.get());
            theoryManager.setRegistry(&registry);
            theoryManager.setCombinationMode(true);
            theoryManager.setNonConvexMode(true);
        }
    } else if (logic == "QF_UFNIA" || logic == "UFNIA") {
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
        configureLia(*lia);
        theoryManager.registerSolver(std::move(lia));
        theoryManager.setSharedTermRegistry(sharedTermRegistry.get());
        theoryManager.setRegistry(&registry);
        theoryManager.setCombinationMode(true);
        theoryManager.setNonConvexMode(true);
    } else if (logic == "QF_UFDTNIA" || logic == "UFDTNIA") {
        // UF + algebraic datatypes + nonlinear integer arithmetic. Same shape as
        // QF_UFNIA with the DtReasoner enabled on the shared egraph: DT owns the
        // constructor/selector/tester structure, NIA owns the Int field values,
        // sharing via equality propagation through the egraph (Nelson-Oppen).
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
        configureLia(*lia);
        theoryManager.registerSolver(std::move(lia));
        theoryManager.setSharedTermRegistry(sharedTermRegistry.get());
        theoryManager.setRegistry(&registry);
        theoryManager.setCombinationMode(true);
        theoryManager.setNonConvexMode(true);
    } else if (logic == "QF_UFDTLIA" || logic == "UFDTLIA") {
        // UF + algebraic datatypes + linear integer arithmetic.
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
        configureLia(*lia);
        theoryManager.registerSolver(std::move(lia));
        theoryManager.setSharedTermRegistry(sharedTermRegistry.get());
        theoryManager.setRegistry(&registry);
        theoryManager.setCombinationMode(true);
        theoryManager.setNonConvexMode(true);
    } else if (logic == "QF_UFNRA" || logic == "UFNRA") {
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
    } else if (logic == "QF_ANIA" || logic == "ANIA" ||
               logic == "QF_AUFNIA" || logic == "AUFNIA") {
        // Arrays + NIA (+ UF). Mirrors QF_UFNIA's solver stack (NIA + its LIA
        // sibling, Purifier with the NIA arith theory) crossed with QF_ALIA's
        // array enablement: one shared EUF egraph hosts UF, the array operators,
        // and the shared index/element terms; ArrayReasoner layers
        // read-over-write on the e-graph; NIA owns the integer arithmetic.
        // Non-convex (NIA emits disequalities) + array-combination arrangement
        // splitting. UF is already provided by EUF, so QF_ANIA and QF_AUFNIA
        // share this branch. Reached only when XOLVER_COMB_ARRAY_NIA admits the
        // logic at the Solver-level array gate.
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
        configureLia(*lia);
        theoryManager.registerSolver(std::move(lia));
        theoryManager.setSharedTermRegistry(sharedTermRegistry.get());
        theoryManager.setRegistry(&registry);
        theoryManager.setCombinationMode(true);
        theoryManager.setNonConvexMode(true);
        theoryManager.setArrayCombinationMode(true);
    } else if (logic == "UF") {
        result.success = false;
    } else {
        // No declared logic or unrecognized logic: route by detected features.
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
                lira->setCoreIr(ir);
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
            configureLia(*lia);
            theoryManager.registerSolver(std::move(lia));
        } else if (features.hasIntVar) {
            auto lia = std::make_unique<LiaSolver>();
            lia->setRegistry(&registry);
            configureLia(*lia);
            theoryManager.registerSolver(std::move(lia));
        } else if (features.hasRealVar && features.hasNonlinear) {
            auto polyKernel = createPolynomialKernel();
            result.polyKernelRaw = polyKernel.get();
            // Create the LRA sibling first so NRA can hold a raw pointer to it
            // for the XOLVER_NRA_LINEARIZE relaxation-model read (OFF → unused).
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

    return result;
}

} // namespace xolver
