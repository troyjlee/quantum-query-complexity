import QuantumQueryComplexity
import QuantumQueryComplexity.Test.AxiomSupport

set_option linter.style.header false

/-!
# Axiom audit: adversary duality and quantum query characterization

Run directly on every CI run:

    lake env lean --trust=0 QuantumQueryComplexity/Test/AdversaryAxioms.lean

The audit checks the theorem dependencies transitively, including the
operational oracle model and the dual-to-algorithm construction, and the
general adversary bound for rectangular matrices (`Quantum/LowerBound/Rect`), and weighted
counting (`Quantum/LowerBound/WeightedCounting`).
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
    QuantumQueryComplexity.Quantum.LowerBound.WeightedCounting]
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
    QuantumQueryComplexity.conjTranspose_mul_eq_zero_of_rows]
