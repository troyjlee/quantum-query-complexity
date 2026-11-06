import QuantumQueryComplexity.Test.AxiomSupport
import QuantumQueryComplexity.Quantum
import QuantumQueryComplexity.Quantum.Records.BooleanDegree

/-!
# Axiom audit: joint states, conditional resampling, and comparison of computations

Run on every CI run, directly:

    lake env lean --trust=0 QuantumQueryComplexity/Test/TransferRecordsAxioms.lean

Every declaration of the joint-state, record, and transfer modules, and of the adaptive
composition module, may depend only on
`propext`, `Classical.choice`, `Quot.sound`, transitively.  The pins are the headline results:
the joint-state and oracle adapters, Lemmas 4.2–4.6 of Cornelissen–Gilani–Zhou on conditional
resampling, domination of increasing events, the transfer lemma and comparison theorem
(Theorem 4.1), Belovs's anti-concentration endpoint, the BBBV validation, index restriction and
its monotonicity for the XOR query complexity, adaptive composition (`Realizes.bind`), and the
records of product distributions (Layer D: record projections, the record-count bound, the
polynomial-method consistency check, and the record budget of biased bits).
-/

open QuantumQueryComplexity.AxiomAudit

#audit_axioms_of_modules [
    QuantumQueryComplexity.Quantum.JointState.Basic,
    QuantumQueryComplexity.Quantum.JointState.Conditioning,
    QuantumQueryComplexity.Quantum.JointState.Oracle,
    QuantumQueryComplexity.Quantum.JointState.Success,
    QuantumQueryComplexity.Quantum.JointState.Restrict,
    QuantumQueryComplexity.Quantum.Records.Resolvent,
    QuantumQueryComplexity.Quantum.Records.CondExp,
    QuantumQueryComplexity.Quantum.Records.Resampling,
    QuantumQueryComplexity.Quantum.Records.CondBern,
    QuantumQueryComplexity.Quantum.Records.Interaction,
    QuantumQueryComplexity.Quantum.Records.PhaseCommutator,
    QuantumQueryComplexity.Quantum.Records.SumProjections,
    QuantumQueryComplexity.Quantum.Records.CommonBlock,
    QuantumQueryComplexity.Quantum.Records.MovingDifference,
    QuantumQueryComplexity.Quantum.Records.Domination,
    QuantumQueryComplexity.Quantum.Records.Product,
    QuantumQueryComplexity.Quantum.Records.RecordCount,
    QuantumQueryComplexity.Quantum.Records.BooleanDegree,
    QuantumQueryComplexity.Quantum.Records.BiasedBudget,
    QuantumQueryComplexity.Quantum.Transfer.Lemma,
    QuantumQueryComplexity.Quantum.Transfer.Sector,
    QuantumQueryComplexity.Quantum.Transfer.Endpoint,
    QuantumQueryComplexity.Quantum.Transfer.Verifier,
    QuantumQueryComplexity.Quantum.Transfer.Comparison,
    QuantumQueryComplexity.Quantum.Transfer.BBBV,
    QuantumQueryComplexity.Quantum.AdaptiveRun]
  pins [
    QuantumQueryComplexity.FinDist.lemma_4_2,
    QuantumQueryComplexity.jInner_le_of_le,
    QuantumQueryComplexity.jNormSq_mul_le,
    QuantumQueryComplexity.FinDist.sum_qNormSq_le_prob_mul_infNormSq,
    QuantumQueryComplexity.FinDist.jNormSq_jointState,
    QuantumQueryComplexity.FinDist.infNormSq_jointState,
    QuantumQueryComplexity.FinDist.wvec_condExp_mul,
    QuantumQueryComplexity.FinDist.jNormSq_condDiff_mul,
    QuantumQueryComplexity.FinDist.commute_condExp_coordDiag,
    QuantumQueryComplexity.FinDist.resolvent_fixed_point,
    QuantumQueryComplexity.CondBern.condWeight_eq,
    QuantumQueryComplexity.CondBern.wvec_condDiff_mul,
    QuantumQueryComplexity.CondBern.jNormSq_condDiff_mul_eq,
    QuantumQueryComplexity.CondBern.lemma_4_3,
    QuantumQueryComplexity.lemma_4_4,
    QuantumQueryComplexity.CondBern.lemma_4_5,
    QuantumQueryComplexity.CondBern.lemma_4_6,
    QuantumQueryComplexity.FinDist.phaseOp_comm_resolvent,
    QuantumQueryComplexity.CondBern.recordComm_sq_le,
    QuantumQueryComplexity.CondBern.infNormSq_recordComm_mul_le,
    QuantumQueryComplexity.CondBern.phaseOp_comm_resolvent_sq_le,
    QuantumQueryComplexity.CondBern.condDiff_comm_recordComm_sq_le,
    QuantumQueryComplexity.FinDist.mass_pos_condOn_iff,
    QuantumQueryComplexity.FinDist.probOf_condOn,
    QuantumQueryComplexity.FinDist.mass_pos_mixture_iff,
    QuantumQueryComplexity.mul_wsOp,
    QuantumQueryComplexity.FinDist.jointState_succ,
    QuantumQueryComplexity.FinDist.jointXorState_succ,
    QuantumQueryComplexity.FinDist.jNormSq_jointXorState,
    QuantumQueryComplexity.FinDist.infNormSq_jointXorState,
    QuantumQueryComplexity.xorOracleMat_eq_hadAns_phase,
    QuantumQueryComplexity.jOracle_xor_eq_hadAns_phase,
    QuantumQueryComplexity.sector_jOracle_phase,
    QuantumQueryComplexity.jOracle_phase_apply_of_not_sector,
    QuantumQueryComplexity.sum_jNormSq_sector_le,
    QuantumQueryComplexity.FinDist.infNormSq_sector_le,
    QuantumQueryComplexity.FinDist.avgSuccessProb_eq_jNormSq_goodMask,
    QuantumQueryComplexity.FinDist.avgXorSuccessProb_eq_jNormSq_goodMask,
    QuantumQueryComplexity.FinDist.avgSuccessProb_ge_of_solves,
    QuantumQueryComplexity.xorSuccessProbOn_simToXor,
    QuantumQueryComplexity.successProbOn_simToStd,
    QuantumQueryComplexity.jNorm_add_le,
    QuantumQueryComplexity.jNorm_jRun_sub_mul_le,
    QuantumQueryComplexity.FinDist.jointState_eq_jRun,
    QuantumQueryComplexity.FinDist.jointXorState_eq_jRun,
    QuantumQueryComplexity.jNorm_jointXorState_sub_le,
    QuantumQueryComplexity.jNormSq_phaseQueryErr,
    QuantumQueryComplexity.jNormSq_xorQueryErr,
    QuantumQueryComplexity.jNormSq_phaseQueryErr_le,
    QuantumQueryComplexity.jNormSq_xorQueryErr_le,
    QuantumQueryComplexity.FinDist.jNormSq_xorQueryErr_jointXorState_le,
    QuantumQueryComplexity.FinDist.jNorm_goodMask_le_add,
    QuantumQueryComplexity.FinDist.sqrt_avgXorSuccessProb_le,
    QuantumQueryComplexity.FinDist.sqrt_avgSuccessProb_le,
    QuantumQueryComplexity.FinDist.goodMask_const_mul_eq_zero,
    QuantumQueryComplexity.FinDist.wsMask_jointXorState_eq_zero,
    QuantumQueryComplexity.FinDist.jNorm_goodMask_le_of_stronglyAntiConc,
    QuantumQueryComplexity.FinDist.sqrt_avgXorSuccessProb_le_of_stronglyAntiConc,
    QuantumQueryComplexity.xorSuccessProbOn_appendVerifier,
    QuantumQueryComplexity.xorSuccessProbOn_le_appendVerifier,
    QuantumQueryComplexity.xorSuccessProbOn_appendVerifier_eq_zero,
    QuantumQueryComplexity.sqrt_avgXorSuccessProb_le_of_reject,
    QuantumQueryComplexity.theorem_4_1,
    QuantumQueryComplexity.theorem_4_1_std,
    QuantumQueryComplexity.bbbvMap_mulVec_ket,
    QuantumQueryComplexity.compBound_bbbvMap,
    QuantumQueryComplexity.sqrt_avgXorSuccessProb_search_le,
    QuantumQueryComplexity.sqrt_avgSuccessProb_search_le,
    QuantumQueryComplexity.FinDist.bern_harris,
    QuantumQueryComplexity.FinDist.probOf_and_le_of_isUpperSet_of_isLowerSet,
    QuantumQueryComplexity.FinDist.probOf_condOn_bern_le,
    QuantumQueryComplexity.CondBern.dist_eq_condOn,
    QuantumQueryComplexity.CondBern.probOf_le_prior,
    QuantumQueryComplexity.xorSuccessProbOn_restrictIdx,
    QuantumQueryComplexity.xorSuccessProbOn_postcomp,
    QuantumQueryComplexity.xorQQueryOn_le_of_padRead,
    QuantumQueryComplexity.Realizes.bind,
    QuantumQueryComplexity.FinDist.condExp_commute,
    QuantumQueryComplexity.FinDist.recProj_eq_prod,
    QuantumQueryComplexity.FinDist.recProj_mul_self,
    QuantumQueryComplexity.FinDist.recProj_mul_recProj,
    QuantumQueryComplexity.FinDist.sum_recProj,
    QuantumQueryComplexity.FinDist.recProj_mul_jOracle_mul_recProj,
    QuantumQueryComplexity.FinDist.recLe_mul_jointState,
    QuantumQueryComplexity.FinDist.recLe_mul_jointXorState,
    QuantumQueryComplexity.QAlg.hasAmpPoly_state_of_records,
    QuantumQueryComplexity.FinDist.recProj_bern_mulVec,
    QuantumQueryComplexity.FinDist.recCount_jOracle_xor_le,
    QuantumQueryComplexity.FinDist.recCount_jointXorState_le]

/-- error: axiom audit: `sorryAx` depends on the forbidden axiom(s) [sorryAx]. -/
#guard_msgs in
#audit_axioms_of_decl sorryAx
