import QuantumQueryComplexity
import QuantumQueryComplexity.Test.AxiomSupport

set_option linter.style.header false

/-!
# Axiom audit: adversary duality and quantum query characterization

Run directly on every CI run:

    lake env lean --trust=0 QuantumQueryComplexity/Test/AdversaryAxioms.lean

The audit checks the theorem dependencies transitively, including the
operational oracle model and the dual-to-algorithm construction, and the
general adversary bound for rectangular matrices (`Quantum/LowerBound/Rect`), weighted
counting (`Quantum/LowerBound/WeightedCounting`), additive oracles over a finite abelian
group with their two-query simulations (`Quantum/AddOracle`, `Quantum/AddSimulation`), arc-system
duals (`LearningGraph/ArcSystem`), algorithms at a fixed budget from promise duals with their
amplification (`Quantum/DualAlgorithm`), and the standard XOR model on the literal basis
`ι × Bool × W` with its equivalence to the library's XOR model (`Quantum/PlainOracle`,
`Quantum/PlainSimulation`), transducers [BJY23, Theorem 5.5] (`Quantum/Transducer`), and
reads-controlled unitaries, decision trees and derived oracles (`Quantum/ReadGadget`,
`Quantum/DecisionTree`).
-/

open QuantumQueryComplexity.AxiomAudit

#audit_axioms_of_modules [
    QuantumQueryComplexity.Duality.Main,
    QuantumQueryComplexity.Duality.MainOn,
    QuantumQueryComplexity.Duality.FiniteOutputOn,
    QuantumQueryComplexity.Composition.Main,
    QuantumQueryComplexity.Quantum.Characterization,
    QuantumQueryComplexity.Quantum.UniformExtraction,
    QuantumQueryComplexity.Quantum.UniformHasDual,
    QuantumQueryComplexity.Quantum.Simulation,
    QuantumQueryComplexity.Quantum.PlainOracle,
    QuantumQueryComplexity.Quantum.PlainSimulation,
    QuantumQueryComplexity.Quantum.LowerBound.Rect,
    QuantumQueryComplexity.Quantum.LowerBound.WeightedCounting,
    QuantumQueryComplexity.Quantum.AddOracle,
    QuantumQueryComplexity.Quantum.AddSimulation,
    QuantumQueryComplexity.LearningGraph.ArcSystem,
    QuantumQueryComplexity.LearningGraph.BlockSys,
    QuantumQueryComplexity.Quantum.DualAlgorithm,
    QuantumQueryComplexity.Quantum.Transducer,
    QuantumQueryComplexity.Quantum.ReadGadget,
    QuantumQueryComplexity.Quantum.DecisionTree]
  pins [
    QuantumQueryComplexity.advDual_eq_advPM,
    QuantumQueryComplexity.advPM_composeFun_eq,
    QuantumQueryComplexity.boundedErrorQQuery_characterized_by_advPM,
    QuantumQueryComplexity.xorQQuery_characterized_by_advPM,
    QuantumQueryComplexity.qQueryOn_characterized_by_advPMOn_third,
    QuantumQueryComplexity.exists_algorithm_of_dualPairOn_uniform,
    QuantumQueryComplexity.qQueryOn_third_le_of_hasDualOn_uniform,
    QuantumQueryComplexity.norm_div_le_advPMOn_rect,
    QuantumQueryComplexity.le_of_computes_rect,
    QuantumQueryComplexity.le_boundedErrorQQuery_rect,
    QuantumQueryComplexity.weighted_counting,
    QuantumQueryComplexity.l2_opNorm_sum_le_weighted_counting,
    QuantumQueryComplexity.conjTranspose_mul_eq_zero_of_rows,
    QuantumQueryComplexity.addSolvesWithErrorOn_eq_iff,
    QuantumQueryComplexity.simAddAlg_state,
    QuantumQueryComplexity.addState_simTransAddAlg,
    QuantumQueryComplexity.successProbOn_simAddAlg,
    QuantumQueryComplexity.addSuccessProbOn_simTransAddAlg,
    QuantumQueryComplexity.AddComputesWithErrorOn.simAddAlg,
    QuantumQueryComplexity.AddSolvesWithErrorOn.simAddAlg,
    QuantumQueryComplexity.ComputesWithErrorOn.simTransAddAlg,
    QuantumQueryComplexity.SolvesWithErrorOn.simTransAddAlg,
    QuantumQueryComplexity.addQueryCounts_nonempty,
    QuantumQueryComplexity.qQueryOn_le_two_mul_addQQueryOn,
    QuantumQueryComplexity.addQQueryOn_le_two_mul_qQueryOn,
    QuantumQueryComplexity.ArcSystem.hasDualOn,
    QuantumQueryComplexity.hasDualOn_of_paths,
    QuantumQueryComplexity.BlockSys.arcSys_cross,
    QuantumQueryComplexity.ArcSystem.cost_le_sum_stages,
    QuantumQueryComplexity.LGFlow.toArcSystem_feasible,
    QuantumQueryComplexity.LGFlow.hasDual_of_arcSystem,
    QuantumQueryComplexity.exists_alg_of_hasDualOn,
    QuantumQueryComplexity.exists_alg_amplify,
    QuantumQueryComplexity.Plain.plainOracleMat_mem_unitaryGroup,
    QuantumQueryComplexity.Plain.PAlg.state_isQState,
    QuantumQueryComplexity.Plain.qProb_toXor_state,
    QuantumQueryComplexity.Plain.qProb_toPlain_state,
    QuantumQueryComplexity.Plain.xorComputes_toXor,
    QuantumQueryComplexity.Plain.plainComputes_toPlain,
    QuantumQueryComplexity.Plain.plainQueryCounts_eq,
    QuantumQueryComplexity.Plain.plainQQueryOn_eq,
    QuantumQueryComplexity.Plain.plainQQuery_characterized_by_advPM,
    QuantumQueryComplexity.Transducer.circuit_mem_unitaryGroup,
    QuantumQueryComplexity.Transducer.loop_catalyst,
    QuantumQueryComplexity.Transducer.circuit_close,
    QuantumQueryComplexity.exists_transducerRoutine_encoded,
    QuantumQueryComplexity.exists_transducerRoutine,
    QuantumQueryComplexity.exists_transducerRoutine_of_realizes,
    QuantumQueryComplexity.exists_readGadget,
    QuantumQueryComplexity.readCtrlMat_mem_unitaryGroup,
    QuantumQueryComplexity.readGadget_run_readPark,
    QuantumQueryComplexity.ReadTree.realizes,
    QuantumQueryComplexity.exists_treeSim,
    QuantumQueryComplexity.Realizes.treeSim,
    QuantumQueryComplexity.exists_readsSim]
