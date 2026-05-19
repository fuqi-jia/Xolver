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
#include <iostream>

namespace nlcolver {

SolverSetupResult setupSolvers(
    const std::string& logic,
    const LogicFeatures& features,
    CoreIr* ir,
    TheoryAtomRegistry& registry,
    TheoryManager& theoryManager,
    std::unique_ptr<SharedTermRegistry>& sharedTermRegistry,
    SortId boolSortId)
{
    SolverSetupResult result;
    result.polyKernelRaw = nullptr;

    // createPolynomialKernel is declared in theory/arith/poly/PolynomialKernel.h

    if (logic == "QF_LIA" || logic == "LIA") {
        auto lia = std::make_unique<LiaSolver>();
        lia->setRegistry(&registry);
        theoryManager.registerSolver(std::move(lia));
    } else if (logic == "QF_LRA" || logic == "LRA") {
        auto lra = std::make_unique<LraSolver>();
        lra->setRegistry(&registry);
        theoryManager.registerSolver(std::move(lra));
    } else if (logic == "QF_NRA" || logic == "NRA") {
        auto polyKernel = createPolynomialKernel();
        result.polyKernelRaw = polyKernel.get();
        theoryManager.registerSolver(
            std::make_unique<NraSolver>(std::move(polyKernel)));
        auto lra = std::make_unique<LraSolver>();
        lra->setRegistry(&registry);
        theoryManager.registerSolver(std::move(lra));
    } else if (logic == "QF_NIA" || logic == "NIA") {
        auto polyKernel = createPolynomialKernel();
        result.polyKernelRaw = polyKernel.get();
        auto nia = std::make_unique<NiaSolver>(std::move(polyKernel));
        nia->setRegistry(&registry);
        theoryManager.registerSolver(std::move(nia));
        auto lia = std::make_unique<LiaSolver>();
        lia->setRegistry(&registry);
        theoryManager.registerSolver(std::move(lia));
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
        theoryManager.registerSolver(std::move(euf));
    } else if (logic == "QF_UFLRA" || logic == "UFLRA") {
        sharedTermRegistry = std::make_unique<SharedTermRegistry>();
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
            theoryManager.registerSolver(std::move(lia));
            theoryManager.setSharedTermRegistry(sharedTermRegistry.get());
            theoryManager.setRegistry(&registry);
            theoryManager.setCombinationMode(true);
            theoryManager.setNonConvexMode(true);
        }
    } else if (logic == "QF_UFNIA" || logic == "UFNIA") {
        sharedTermRegistry = std::make_unique<SharedTermRegistry>();
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
        theoryManager.registerSolver(std::move(lia));
        theoryManager.setSharedTermRegistry(sharedTermRegistry.get());
        theoryManager.setRegistry(&registry);
        theoryManager.setCombinationMode(true);
        theoryManager.setNonConvexMode(true);
    } else if (logic == "QF_UFNRA" || logic == "UFNRA") {
        sharedTermRegistry = std::make_unique<SharedTermRegistry>();
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
            theoryManager.registerSolver(std::move(lia));
        } else if (features.hasIntVar) {
            auto lia = std::make_unique<LiaSolver>();
            lia->setRegistry(&registry);
            theoryManager.registerSolver(std::move(lia));
        } else if (features.hasRealVar && features.hasNonlinear) {
            auto polyKernel = createPolynomialKernel();
            result.polyKernelRaw = polyKernel.get();
            theoryManager.registerSolver(
                std::make_unique<NraSolver>(std::move(polyKernel)));
            theoryManager.registerSolver(std::make_unique<LraSolver>());
        } else if (features.hasRealVar) {
            theoryManager.registerSolver(std::make_unique<LraSolver>());
        }
    }

    return result;
}

} // namespace nlcolver
