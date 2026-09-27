import QuantumQueryComplexity.Test.AxiomSupport
import QuantumQueryComplexity.Test.TreeSearch

/-!
# Axiom audit: tree search with shared subcomputations

Run on every CI run, directly:

    lake env lean --trust=0 QuantumQueryComplexity/Test/TreeSearchAxioms.lean

Every declaration of the listed modules (the old first-difference construction included) may
depend only on `propext`, `Classical.choice`, `Quot.sound`, transitively.
-/

open QuantumQueryComplexity.AxiomAudit

#audit_axioms_of_modules [
    QuantumQueryComplexity.TreeSearch,
    QuantumQueryComplexity.TreeSearch.Cost,
    QuantumQueryComplexity.TreeSearch.Optimal,
    QuantumQueryComplexity.TreeSearch.Examples,
    QuantumQueryComplexity.Promise.TreeSearch,
    QuantumQueryComplexity.Quantum.TreeSearch,
    QuantumQueryComplexity.Test.TreeSearch]
  pins [
    QuantumQueryComplexity.AncTree.recCost_eq,
    QuantumQueryComplexity.AncTree.sum_path_le_recCost,
    QuantumQueryComplexity.AncTree.optW_spec,
    QuantumQueryComplexity.AncTree.energy_lower,
    QuantumQueryComplexity.AncTree.recCost_sq_le_pathMax_mul_energy,
    QuantumQueryComplexity.AncTree.optValue_eq,
    QuantumQueryComplexity.AncTree.hasWeightedDual_treeSearch_recCost,
    QuantumQueryComplexity.AncTree.recCost_le_sqrt_depth_sqSum,
    QuantumQueryComplexity.AncTree.hasWeightedDual_treeSearch_sqSum,
    QuantumQueryComplexity.AncTree.hasDualOn_treeSearch_recCost,
    QuantumQueryComplexity.AncTree.hasDual_treeSearch_recCost,
    QuantumQueryComplexity.HasDualOn.one_le_of_ne,
    QuantumQueryComplexity.AncTree.qQueryOn_third_treeSearch,
    QuantumQueryComplexity.AncTree.qQueryOn_third_treeSearch_hom,
    QuantumQueryComplexity.AncTree.recCost_binary,
    QuantumQueryComplexity.AncTree.sqrtTwoSum_le_three_sqrt,
    QuantumQueryComplexity.TreeSearchAcceptance.acceptance_certificate,
    QuantumQueryComplexity.TreeSearchAcceptance.acceptance_quantum,
    QuantumQueryComplexity.TreeSearchAcceptance.Three.recCost_three,
    QuantumQueryComplexity.TreeSearchAcceptance.Three.energy_three,
    QuantumQueryComplexity.TreeSearchAcceptance.Uneven.recCost_uneven]

/-- error: axiom audit: `sorryAx` depends on the forbidden axiom(s) [sorryAx]. -/
#guard_msgs in
#audit_axioms_of_decl sorryAx
