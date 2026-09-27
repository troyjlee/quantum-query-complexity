import QuantumQueryComplexity.Test.AxiomSupport
import QuantumQueryComplexity.Test.QuantumWalk
import QuantumQueryComplexity.Quantum.Walk.Gap
import QuantumQueryComplexity.Quantum.Walk.MNRS
import QuantumQueryComplexity.Quantum.Walk.Chain

/-!
# Axiom audit: approximate-reflection search and quantum walks

Run on every CI run, directly:

    lake env lean --trust=0 QuantumQueryComplexity/Test/QuantumWalkAxioms.lean

Every declaration of the listed modules may depend only on `propext`, `Classical.choice`,
`Quot.sound`, transitively.  Extend the list when a production module is added.
-/

open QuantumQueryComplexity.AxiomAudit

#audit_axioms_of_modules [
    QuantumQueryComplexity.Quantum.Approximation,
    QuantumQueryComplexity.Quantum.Amplitude.ApproxReflection,
    QuantumQueryComplexity.Quantum.Amplitude.Recursive,
    QuantumQueryComplexity.Quantum.Amplitude.Tolerant,
    QuantumQueryComplexity.Quantum.Amplitude.CleanControl,
    QuantumQueryComplexity.Quantum.Amplitude.ChainRoutine,
    QuantumQueryComplexity.Quantum.Amplitude.SearchInv,
    QuantumQueryComplexity.Quantum.History,
    QuantumQueryComplexity.Quantum.Amplitude.TolerantPass,
    QuantumQueryComplexity.Quantum.Amplitude.ApproxSearch,
    QuantumQueryComplexity.Quantum.Amplitude.SearchInvUpTo,
    QuantumQueryComplexity.Quantum.Amplitude.NoisyRefl,
    QuantumQueryComplexity.Test.QuantumWalk,
    QuantumQueryComplexity.Quantum.Walk.Gap,
    QuantumQueryComplexity.Quantum.Walk.WeightedClock,
    QuantumQueryComplexity.Quantum.Walk.ClockWeights,
    QuantumQueryComplexity.Quantum.Walk.TwoReflections,
    QuantumQueryComplexity.Quantum.Walk.Detect,
    QuantumQueryComplexity.Quantum.Walk.Level,
    QuantumQueryComplexity.Quantum.Walk.KronSupport,
    QuantumQueryComplexity.Quantum.Walk.Global,
    QuantumQueryComplexity.Quantum.Walk.GlobalInv,
    QuantumQueryComplexity.Quantum.Walk.MNRS,
    QuantumQueryComplexity.Quantum.Walk.Chain]
  pins [
    QuantumQueryComplexity.IsApproxRefl.conj,
    QuantumQueryComplexity.abs_sqrt_step_le,
    QuantumQueryComplexity.ChainOK.exists_level,
    QuantumQueryComplexity.ChainOK.invariants,
    QuantumQueryComplexity.ChainOK.qNormSq_contV_le,
    QuantumQueryComplexity.IsApproxRefl.clean,
    QuantumQueryComplexity.cleanRefl_run,
    QuantumQueryComplexity.chainR_run,
    QuantumQueryComplexity.stageR_run,
    QuantumQueryComplexity.SearchInv.chainOK,
    QuantumQueryComplexity.SearchInv.pass_fail_le,
    QuantumQueryComplexity.recordMat_embed_false,
    QuantumQueryComplexity.suppIn_record_embed_true,
    QuantumQueryComplexity.SearchInv.passUpTo_run,
    QuantumQueryComplexity.qProb_slotReadout_none,
    QuantumQueryComplexity.approxSearch_q,
    QuantumQueryComplexity.approxSearch_pr_unmarked,
    QuantumQueryComplexity.two_thirds_le_approxSearch,
    QuantumQueryComplexity.approxSearch_pr_none_of_empty,
    QuantumQueryComplexity.passLen_le,
    QuantumQueryComplexity.QuantumWalkAcceptance.acceptance_approxSearch,
    QuantumQueryComplexity.QuantumWalkAcceptance.acceptance_pass,
    QuantumQueryComplexity.QuantumWalkAcceptance.searchInv_exact,
    QuantumQueryComplexity.QuantumWalkAcceptance.acceptance_exact,
    QuantumQueryComplexity.SearchInvUpTo.extend,
    QuantumQueryComplexity.approxSearch_congr,
    QuantumQueryComplexity.two_thirds_le_approxSearch_upTo,
    QuantumQueryComplexity.isApproxRefl_noisyRefl,
    QuantumQueryComplexity.QuantumWalkAcceptance.Noisy.reflN_ne_exact,
    QuantumQueryComplexity.QuantumWalkAcceptance.Noisy.contract,
    QuantumQueryComplexity.QuantumWalkAcceptance.Noisy.noisy_search,
    QuantumQueryComplexity.hermitian_gap_ineq,
    QuantumQueryComplexity.qNormSq_avg_le_of_gap,
    QuantumQueryComplexity.wDetector_len,
    QuantumQueryComplexity.qNormSq_wDetector_add,
    QuantumQueryComplexity.wDetector_run_mulVec_wClock_of_fixed,
    QuantumQueryComplexity.wAvg_kClock,
    QuantumQueryComplexity.WalkFam.gap,
    QuantumQueryComplexity.WalkFam.walkOp_mem_K,
    QuantumQueryComplexity.WalkFam.isApproxRefl_wDetector,
    QuantumQueryComplexity.LevelData.isApproxRefl_lvlR,
    QuantumQueryComplexity.LevelData.preserves_lvlR,
    QuantumQueryComplexity.WalkGlobal.searchInv,
    QuantumQueryComplexity.WalkOK.walkSearch_pr_unmarked,
    QuantumQueryComplexity.WalkOK.two_thirds_le_walkSearch,
    QuantumQueryComplexity.WalkOK.walkSearch_pr_none_of_empty,
    QuantumQueryComplexity.WalkSetup.walkSearch_q,
    QuantumQueryComplexity.WalkSetup.walkSearch_q_le,
    QuantumQueryComplexity.WalkSetup.walkSearch_q_le_real,
    QuantumQueryComplexity.RevChain.disc_herm,
    QuantumQueryComplexity.resampling_gap,
    QuantumQueryComplexity.lazy_gap,
    QuantumQueryComplexity.QuantumWalkAcceptance.acceptance_walk,
    QuantumQueryComplexity.QuantumWalkAcceptance.acceptance_walk_budget]

/-- error: axiom audit: `sorryAx` depends on the forbidden axiom(s) [sorryAx]. -/
#guard_msgs in
#audit_axioms_of_decl sorryAx
