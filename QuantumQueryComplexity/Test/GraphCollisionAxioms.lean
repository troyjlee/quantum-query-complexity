import QuantumQueryComplexity.Test.AxiomSupport
import QuantumQueryComplexity.Quantum.Program
import QuantumQueryComplexity.Quantum.Amplitude.Median
import QuantumQueryComplexity.Quantum.Amplitude.LabelSearch
import QuantumQueryComplexity.Quantum.IndexCopy
import QuantumQueryComplexity.Quantum.PromiseOr
import QuantumQueryComplexity.Quantum.RoutineClose
import QuantumQueryComplexity.Quantum.Amplitude.CoherentPrep
import QuantumQueryComplexity.Quantum.Walk.Approx

/-!
# Axiom audit: subroutines for the graph collision algorithm

Run on every CI run, directly:

    lake env lean --trust=0 QuantumQueryComplexity/Test/GraphCollisionAxioms.lean

Every declaration of the listed modules, private helpers included, may depend only on `propext`,
`Classical.choice`, `Quot.sound`, transitively.  These are the general subroutines used by the
graph collision algorithm of Cornelissen, Gilani, Kintali, Le Gall, Patro and Zhou: adaptive
programs with fixed budgets, the median trick (with point masses kept), counting and sampling on
a known label set, copied input bits, combining one-sided promise tests with unequal costs,
approximate preparations inside larger routines, clean coherent preparation of the uniform
marked state, and walk search with input-dependent chains and approximate routines.  The walk
results are conditional on the contract `ApproxWalkOK`; no graph collision update or check is
shown here to satisfy it.  The pins are all the public results of these modules.
-/

open QuantumQueryComplexity.AxiomAudit

#audit_axioms_of_modules [
    QuantumQueryComplexity.Quantum.Program,
    QuantumQueryComplexity.Quantum.Amplitude.Median,
    QuantumQueryComplexity.Quantum.Amplitude.LabelSearch,
    QuantumQueryComplexity.Quantum.IndexCopy,
    QuantumQueryComplexity.Quantum.PromiseOr,
    QuantumQueryComplexity.Quantum.RoutineClose,
    QuantumQueryComplexity.Quantum.Amplitude.CoherentPrep,
    QuantumQueryComplexity.Quantum.Walk.Approx]
  pins [
    QuantumQueryComplexity.Prog.budget_call,
    QuantumQueryComplexity.Prog.law_call,
    QuantumQueryComplexity.Prog.law_nonneg,
    QuantumQueryComplexity.Prog.sum_law,
    QuantumQueryComplexity.Prog.realizes,
    QuantumQueryComplexity.Prog.budget_cutoff_le,
    QuantumQueryComplexity.Prog.cutoff_eq_self,
    QuantumQueryComplexity.Prog.overProb_eq_zero,
    QuantumQueryComplexity.Prog.law_cutoff_ge,
    QuantumQueryComplexity.Prog.bad_call_le,
    QuantumQueryComplexity.median_mem,
    QuantumQueryComplexity.Realizes.median,
    QuantumQueryComplexity.Realizes.median_pointMass,
    QuantumQueryComplexity.labelCountBudget_le,
    QuantumQueryComplexity.exists_count,
    QuantumQueryComplexity.sampleBudget_le,
    QuantumQueryComplexity.exists_sample,
    QuantumQueryComplexity.Realizes.reindex,
    QuantumQueryComplexity.promiseOrBudget_le,
    QuantumQueryComplexity.exists_promiseOr,
    QuantumQueryComplexity.QRoutine.run_comp_close,
    QuantumQueryComplexity.QRoutine.run_close_kronLift,
    QuantumQueryComplexity.QRoutine.run_close_sandwich,
    QuantumQueryComplexity.prepBudget_le,
    QuantumQueryComplexity.exists_coherentPrep,
    QuantumQueryComplexity.exists_coherentPrep_blank,
    QuantumQueryComplexity.RevChain.exists_walkChain,
    QuantumQueryComplexity.WalkSetup.walkSearch_congr,
    QuantumQueryComplexity.ApproxWalkOK.two_thirds_sub_le,
    QuantumQueryComplexity.ApproxWalkOK.bad_le,
    QuantumQueryComplexity.ApproxWalkOK.one_sub_le_none]
