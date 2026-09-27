import QuantumQueryComplexity
import QuantumQueryComplexity.Test.AxiomSupport

set_option linter.style.header false

/-!
# Axiom audit: adversary duality and quantum query characterization

Run directly on every CI run:

    lake env lean --trust=0 QuantumQueryComplexity/Test/AdversaryAxioms.lean

The audit checks the theorem dependencies transitively, including the
operational oracle model and the dual-to-algorithm construction.
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
    QuantumQueryComplexity.Quantum.Simulation]
  pins [
    QuantumQueryComplexity.advDual_eq_advPM,
    QuantumQueryComplexity.advPM_composeFun_eq,
    QuantumQueryComplexity.boundedErrorQQuery_characterized_by_advPM,
    QuantumQueryComplexity.xorQQuery_characterized_by_advPM,
    QuantumQueryComplexity.qQueryOn_characterized_by_advPMOn_third,
    QuantumQueryComplexity.exists_algorithm_of_dualPairOn_uniform,
    QuantumQueryComplexity.qQueryOn_third_le_of_hasDualOn_uniform]
