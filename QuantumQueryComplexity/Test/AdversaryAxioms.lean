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
duals (`LearningGraph/ArcSystem`), and algorithms at a fixed budget from promise duals with their
amplification (`Quantum/DualAlgorithm`).
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
    QuantumQueryComplexity.Quantum.LowerBound.Rect,
    QuantumQueryComplexity.Quantum.LowerBound.WeightedCounting,
    QuantumQueryComplexity.Quantum.AddOracle,
    QuantumQueryComplexity.Quantum.AddSimulation,
    QuantumQueryComplexity.LearningGraph.ArcSystem,
    QuantumQueryComplexity.Quantum.DualAlgorithm]
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
    QuantumQueryComplexity.ArcSystem.cost_le_sum_stages,
    QuantumQueryComplexity.LGFlow.toArcSystem_feasible,
    QuantumQueryComplexity.LGFlow.hasDual_of_arcSystem,
    QuantumQueryComplexity.exists_alg_of_hasDualOn,
    QuantumQueryComplexity.exists_alg_amplify]
