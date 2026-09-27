import QuantumQueryComplexity.Test.AxiomSupport
import QuantumQueryComplexity.Test.RobustSearch

/-!
# Axiom audit: robust search

Run on every CI run, directly:

    lake env lean --trust=0 QuantumQueryComplexity/Test/RobustSearchAxioms.lean

Every declaration of the listed modules may depend only on `propext`, `Classical.choice`,
`Quot.sound`, transitively.  Extend the list when a production module is added.
-/

open QuantumQueryComplexity.AxiomAudit

#audit_axioms_of_modules [
    QuantumQueryComplexity.Quantum.Tail,
    QuantumQueryComplexity.Quantum.SelectRoutine,
    QuantumQueryComplexity.Quantum.CoherentMajority,
    QuantumQueryComplexity.Quantum.FirstOf,
    QuantumQueryComplexity.Quantum.RobustSearch.Defs,
    QuantumQueryComplexity.Quantum.RobustSearch.Recursion,
    QuantumQueryComplexity.Quantum.RobustSearch.Filter,
    QuantumQueryComplexity.Quantum.RobustSearch.Progress,
    QuantumQueryComplexity.Quantum.RobustSearch.Main,
    QuantumQueryComplexity.Quantum.RobustSearch.Public,
    QuantumQueryComplexity.Test.RobustSearch]
  pins [
    QuantumQueryComplexity.QRoutine.sig_run_mulVec_sum,
    QuantumQueryComplexity.selectPadded_prob,
    QuantumQueryComplexity.bankCtrl_mulVec_prodState,
    QuantumQueryComplexity.qProb_powReadout,
    QuantumQueryComplexity.maj_twelve_le,
    QuantumQueryComplexity.RSLevel.next_len,
    QuantumQueryComplexity.RSLevel.next_u,
    QuantumQueryComplexity.RobustSearch.progress,
    QuantumQueryComplexity.RobustSearch.bad_le,
    QuantumQueryComplexity.two_thirds_le_good,
    QuantumQueryComplexity.two_thirds_le_none,
    QuantumQueryComplexity.robustSearch_q,
    QuantumQueryComplexity.robustSearchBudget_le,
    QuantumQueryComplexity.robustSearch_solves,
    QuantumQueryComplexity.robustOr_computes,
    QuantumQueryComplexity.RobustSearchAcceptance.acceptance_robustSearch,
    QuantumQueryComplexity.RobustSearchAcceptance.Noisy.noisyTest_prob,
    QuantumQueryComplexity.RobustSearchAcceptance.Noisy.noisy_search]

/-- error: axiom audit: `sorryAx` depends on the forbidden axiom(s) [sorryAx]. -/
#guard_msgs in
#audit_axioms_of_decl sorryAx
