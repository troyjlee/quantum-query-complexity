import QuantumQueryComplexity.Quantum.PlainOracle
import QuantumQueryComplexity.Quantum.XorOracle
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The standard XOR model and the library's XOR model are equivalent

The library's XOR model (`XorOracle.lean`) runs algorithms on `QBasis ι Bool W =
Option ι × Option Bool × W`, with an idle query index and a blank answer on which the oracle acts
as the identity. The standard model (`PlainOracle.lean`) runs them on the literal basis
`ι × Bool × W`. For every nonempty index type the two models achieve **exactly the same query
counts**, for every promise, output type and error (`Plain.plainQueryCounts_eq`), so their query
complexities are equal (`Plain.plainQQueryOn_eq`). Both simulations preserve the output
distribution exactly after every number of queries.

* **Standard to library** (`Plain.PAlg.toXor`, the same workspace, the same queries). A standard
  algorithm is a library algorithm that never leaves the sector of states `(some i, some b, w)`:
  its unitaries act as the standard ones on that sector and as the identity elsewhere, and on that
  sector the two oracles agree. No hypothesis on `ι` is needed, since a standard algorithm has a
  unit initial state, so its basis, and hence `ι`, is nonempty.
* **Library to standard** (`QAlg.toPlain`, workspace `QBasis ι Bool W`, the same queries). The
  simulation keeps the library algorithm's whole basis as its workspace. Its own query register
  holds a fixed index `i₀`, and its answer register the state `(|0⟩ + |1⟩)/√2`, which an XOR
  leaves unchanged. Around every query it applies an involutive basis permutation: when the
  simulated index and answer are `some i` and `some b`, it exchanges them with its own index and
  answer. A query of the simulated algorithm at `(some i, some b)` thus becomes a standard query
  at `i`, while an idle or blank query becomes a standard query at `i₀` that changes nothing.

The construction of the second simulation follows the index restriction
(`QAlg.restrictIdx`, `JointState/Restrict.lean`). The adversary characterization of the XOR model
holds verbatim on the literal basis; that corollary, `Plain.plainQQuery_characterized_by_advPM`,
is stated in the integration file `Characterization.lean`, since the characterization reaches
classical modules that the quantum aggregate may not import.

## Main results

* `Plain.xorComputes_toXor`, `Plain.plainComputes_toPlain` — the two simulations, for deciders.
* `Plain.qProb_toXor_state`, `Plain.qProb_toPlain_state` — they preserve the output distribution
  after every number of queries.
* `Plain.plainQueryCounts_eq`, `Plain.plainQQueryOn_eq` — equal query counts and complexities for
  a nonempty index type.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι W O X : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]

namespace Plain

/-! ## Standard-model algorithms are library algorithms -/

section ToXor

/-- The library basis, split into the sector `(some i, some b, w)` and the rest. -/
private def secEquiv : QBasis ι Bool W ≃ PBasis ι W ⊕ ((Option Bool × W) ⊕ (ι × W)) where
  toFun
    | (none, t, w) => Sum.inr (Sum.inl (t, w))
    | (some i, none, w) => Sum.inr (Sum.inr (i, w))
    | (some i, some b, w) => Sum.inl (i, b, w)
  invFun
    | Sum.inl (i, b, w) => (some i, some b, w)
    | Sum.inr (Sum.inl (t, w)) => (none, t, w)
    | Sum.inr (Sum.inr (i, w)) => (some i, none, w)
  left_inv := by rintro ⟨_ | i, _ | b, w⟩ <;> rfl
  right_inv := by rintro (⟨i, b, w⟩ | ⟨t, w⟩ | ⟨i, w⟩) <;> rfl

/-- A standard state, placed in the sector `(some i, some b, w)`. -/
private def secEmbed (ψ : PBasis ι W → ℂ) : QBasis ι Bool W → ℂ :=
  Sum.elim ψ 0 ∘ secEquiv

/-- A standard operator, acting on the sector `(some i, some b, w)` and as the identity
elsewhere. -/
private noncomputable def secMat (M : Matrix (PBasis ι W) (PBasis ι W) ℂ) :
    Matrix (QBasis ι Bool W) (QBasis ι Bool W) ℂ :=
  (Matrix.fromBlocks M 0 0 (1 : Matrix ((Option Bool × W) ⊕ (ι × W))
    ((Option Bool × W) ⊕ (ι × W)) ℂ)).submatrix secEquiv secEquiv

private lemma secMat_mem_unitaryGroup {M : Matrix (PBasis ι W) (PBasis ι W) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (PBasis ι W) ℂ) :
    secMat M ∈ Matrix.unitaryGroup (QBasis ι Bool W) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, secMat,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply]
  have h := Matrix.mem_unitaryGroup_iff'.mp hM
  rw [Matrix.star_eq_conjTranspose] at h
  simp [h, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

private lemma secMat_mulVec_secEmbed (M : Matrix (PBasis ι W) (PBasis ι W) ℂ)
    (ψ : PBasis ι W → ℂ) : secMat M *ᵥ secEmbed ψ = secEmbed (M *ᵥ ψ) := by
  rw [secMat, secEmbed, Matrix.submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm,
    Function.comp_id, Matrix.fromBlocks_mulVec, secEmbed]
  congr 1
  funext s
  rcases s with q | r <;> simp

private lemma xorOracleMat_mulVec_secEmbed (a : ι → Bool) (ψ : PBasis ι W → ℂ) :
    xorOracleMat a *ᵥ secEmbed ψ = secEmbed (plainOracleMat a *ᵥ ψ) := by
  funext p
  rw [xorOracleMat_mulVec_apply]
  rcases p with ⟨_ | i, _ | b, w⟩ <;>
    simp [secEmbed, secEquiv, plainOracleMat_mulVec_apply]

private lemma sum_secEmbed (ψ : PBasis ι W → ℂ) (g : QBasis ι Bool W → ℂ → ℝ)
    (hg : ∀ p, g p 0 = 0) :
    ∑ p, g p (secEmbed ψ p) = ∑ q, g (secEquiv.symm (Sum.inl q)) (ψ q) := by
  rw [← Equiv.sum_comp secEquiv.symm, Fintype.sum_sum_type]
  simp [secEmbed, hg]

private lemma isQState_secEmbed {ψ : PBasis ι W → ℂ} (hψ : IsQState ψ) :
    IsQState (secEmbed ψ) := by
  rw [IsQState, qNormSq_def, sum_secEmbed ψ (fun _ z => Complex.normSq z) (by simp)]
  exact hψ

/-- A space carrying a unit vector is nonempty. -/
private lemma nonempty_of_isQState {H : Type} [Fintype H] {ψ : H → ℂ} (hψ : IsQState ψ) :
    Nonempty H := by
  by_contra h
  rw [not_nonempty_iff] at h
  rw [IsQState, qNormSq_def, Finset.univ_eq_empty, Finset.sum_empty] at hψ
  exact zero_ne_one hψ

/-- The sector point of a library basis state, or a default point outside the sector. -/
private def secProj (d : PBasis ι W) (p : QBasis ι Bool W) : PBasis ι W :=
  Sum.elim id (fun _ => d) (secEquiv p)

/-- **A standard-model algorithm as a library XOR-model algorithm**, on the same workspace and
with the same number of queries: the same unitaries on the sector `(some i, some b, w)` and the
identity elsewhere, and the same readout on the sector. It never leaves the sector, so its output
distribution is that of `A` after every number of queries (`qProb_toXor_state`). -/
noncomputable def PAlg.toXor (A : PAlg ι O W) : QAlg ι Bool O W where
  init := secEmbed A.init
  init_isQState := isQState_secEmbed A.init_isQState
  step t := secMat (A.step t)
  step_unitary t := secMat_mem_unitaryGroup (A.step_unitary t)
  readout p := A.readout (secProj (Classical.choice (nonempty_of_isQState A.init_isQState)) p)

variable [DecidableEq O]

private lemma xorState_toXor (A : PAlg ι O W) (a : ι → Bool) (t : ℕ) :
    xorState A.toXor a t = secEmbed (A.state a t) := by
  induction t with
  | zero =>
      rw [xorState_zero, PAlg.state_zero]
      exact secMat_mulVec_secEmbed _ _
  | succ t ih =>
      rw [xorState_succ, PAlg.state_succ, ih, xorOracleMat_mulVec_secEmbed]
      exact secMat_mulVec_secEmbed _ _

private lemma qProb_toXor (A : PAlg ι O W) (ψ : PBasis ι W → ℂ) (o : O) :
    qProb A.toXor.readout (secEmbed ψ) o = qProb A.readout ψ o := by
  rw [qProb, qProb, sum_secEmbed ψ
    (fun p z => if A.toXor.readout p = o then Complex.normSq z else 0) (by simp)]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [PAlg.toXor, secProj]

/-- **The embedding preserves the output distribution**: after `t` queries on input `a`,
`A.toXor` (library XOR oracle) announces each output with the probability with which `A`
(standard oracle) announces it. -/
theorem qProb_toXor_state (A : PAlg ι O W) (a : ι → Bool) (t : ℕ) (o : O) :
    qProb A.toXor.readout (xorState A.toXor a t) o = qProb A.readout (A.state a t) o := by
  rw [xorState_toXor, qProb_toXor]

/-- **Standard to library**: a standard-model decider is a library XOR-model decider on the same
workspace, with the same query count and error. -/
theorem xorComputes_toXor {A : PAlg ι O W} {q : ℕ} {read : X → ι → Bool} {f : X → O} {ε : ℝ}
    (hA : PlainComputesWithErrorOn A q read f ε) : XorComputesWithErrorOn A.toXor q read f ε := by
  intro x
  rw [qProb_toXor_state]
  exact hA x

end ToXor

/-! ## Library algorithms are simulated by standard ones: the construction -/

section ToPlain

variable {R : Type} [Fintype R] [DecidableEq R]

/-- The standard basis over the workspace `R`, split as (workspace, standard registers). -/
private def wEquiv : PBasis ι R ≃ R × (ι × Bool) where
  toFun p := (p.2.2, (p.1, p.2.1))
  invFun x := (x.2.1, x.2.2, x.1)
  left_inv := by rintro ⟨i, b, r⟩; rfl
  right_inv := by rintro ⟨r, i, b⟩; rfl

/-- An operator on the workspace, acting as the identity on the standard registers. -/
private noncomputable def wLift (M : Matrix R R ℂ) : Matrix (PBasis ι R) (PBasis ι R) ℂ :=
  (Matrix.blockDiagonal fun _ : ι × Bool => M).submatrix wEquiv wEquiv

private lemma wLift_mem_unitaryGroup {M : Matrix R R ℂ} (hM : M ∈ Matrix.unitaryGroup R ℂ) :
    wLift (ι := ι) M ∈ Matrix.unitaryGroup (PBasis ι R) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, wLift,
    Matrix.conjTranspose_submatrix, Matrix.blockDiagonal_conjTranspose,
    Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]
  rw [show (fun _ : ι × Bool => Mᴴ * M) = (1 : ι × Bool → Matrix R R ℂ) from
      funext fun _ => conjTranspose_mul_self_of_unitary hM,
    Matrix.blockDiagonal_one, Matrix.submatrix_one_equiv]

private lemma wLift_mulVec_apply (M : Matrix R R ℂ) (v : PBasis ι R → ℂ) (p : PBasis ι R) :
    (wLift M *ᵥ v) p = (M *ᵥ fun r => v (p.1, p.2.1, r)) p.2.2 := by
  obtain ⟨i, b, r⟩ := p
  simp only [Matrix.mulVec, dotProduct, wLift, Matrix.submatrix_apply]
  rw [← Equiv.sum_comp wEquiv.symm, Fintype.sum_prod_type]
  simp [Matrix.blockDiagonal_apply, wEquiv]

/-- The amplitude `1/√2` of each value of the answer bit in `(|0⟩ + |1⟩)/√2`. -/
private noncomputable def halfAmp : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

private lemma normSq_halfAmp_mul (z : ℂ) : Complex.normSq (halfAmp * z) = Complex.normSq z / 2 := by
  rw [Complex.normSq_mul, halfAmp, Complex.normSq_ofReal, ← sq, inv_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- A workspace state, with the standard index register at `i₀` and the answer register in
`(|0⟩ + |1⟩)/√2`. -/
private noncomputable def sEmbed (i₀ : ι) (ψ : R → ℂ) : PBasis ι R → ℂ :=
  fun p => if p.1 = i₀ then halfAmp * ψ p.2.2 else 0

private lemma wLift_mulVec_sEmbed (i₀ : ι) (M : Matrix R R ℂ) (ψ : R → ℂ) :
    wLift M *ᵥ sEmbed i₀ ψ = sEmbed i₀ (M *ᵥ ψ) := by
  funext p
  rw [wLift_mulVec_apply]
  by_cases h : p.1 = i₀
  · have hψ : (fun r => sEmbed i₀ ψ (p.1, p.2.1, r)) = halfAmp • ψ :=
      funext fun r => by simp [sEmbed, h]
    rw [hψ, Matrix.mulVec_smul]
    simp [sEmbed, h]
  · have hψ : (fun r => sEmbed i₀ ψ (p.1, p.2.1, r)) = 0 :=
      funext fun r => by simp [sEmbed, h]
    rw [hψ, Matrix.mulVec_zero]
    simp [sEmbed, h]

/-- Sums over the embedded states: the two answer values each carry half of the weight. -/
private lemma sum_sEmbed (i₀ : ι) (ψ : R → ℂ) (g : R → ℝ) :
    ∑ p : PBasis ι R, (if p.1 = i₀ then g p.2.2 * (Complex.normSq (ψ p.2.2) / 2) else 0)
      = ∑ r, g r * Complex.normSq (ψ r) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i₀]
  · simp only [↓reduceIte, Fintype.sum_prod_type, Fintype.sum_bool]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  · intro j _ hj
    simp [hj]
  · simp

private lemma isQState_sEmbed (i₀ : ι) {ψ : R → ℂ} (hψ : IsQState ψ) :
    IsQState (sEmbed i₀ ψ) := by
  rw [IsQState, qNormSq_def] at hψ ⊢
  have h := sum_sEmbed i₀ ψ (fun _ => 1)
  simp only [one_mul] at h
  rw [← hψ, ← h]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p.1 = i₀ <;> simp [sEmbed, hp, normSq_halfAmp_mul]

/-- **The basis permutation around each query**: when the simulated index and answer are
`some i` and `some b`, exchange them with the standard index and answer. -/
private def sMap : PBasis ι (QBasis ι Bool W) → PBasis ι (QBasis ι Bool W)
  | (j, c, (some i, some b, w)) => (i, b, (some j, some c, w))
  | (j, c, (none, t, w)) => (j, c, (none, t, w))
  | (j, c, (some i, none, w)) => (j, c, (some i, none, w))

private lemma sMap_involutive : Function.Involutive (sMap (ι := ι) (W := W)) := by
  rintro ⟨j, c, _ | i, _ | b, w⟩ <;> rfl

/-- The permutation `sMap`. -/
private def sPerm : Equiv.Perm (PBasis ι (QBasis ι Bool W)) :=
  Function.Involutive.toPerm _ (sMap_involutive (ι := ι) (W := W))

private lemma sPerm_mulVec_apply (ψ : PBasis ι (QBasis ι Bool W) → ℂ)
    (p : PBasis ι (QBasis ι Bool W)) :
    (qPerm (sPerm (ι := ι) (W := W)) *ᵥ ψ) p = ψ (sMap p) := by
  rw [qPerm_mulVec_apply]
  rfl

/-- **One simulated query**: the permutation, the standard oracle on `a`, and the permutation
again act on the embedded states as the library's XOR oracle on `a`. -/
private lemma sPerm_plain_sPerm (i₀ : ι) (a : ι → Bool) (ψ : QBasis ι Bool W → ℂ) :
    qPerm (sPerm (ι := ι) (W := W)) *ᵥ (plainOracleMat a *ᵥ
        (qPerm (sPerm (ι := ι) (W := W)) *ᵥ sEmbed i₀ ψ))
      = sEmbed i₀ (xorOracleMat a *ᵥ ψ) := by
  funext p
  rw [sPerm_mulVec_apply, plainOracleMat_mulVec_apply, sPerm_mulVec_apply]
  rcases p with ⟨j, c, _ | i, _ | b, w⟩ <;>
    simp [sMap, sEmbed, xorOracleMat_mulVec_apply] <;> rfl

/-- The steps of the simulation: the library step on the workspace, conjugated by the
permutation around each query. -/
private noncomputable def sStep (A : QAlg ι Bool O W) :
    ℕ → Matrix (PBasis ι (QBasis ι Bool W)) (PBasis ι (QBasis ι Bool W)) ℂ
  | 0 => qPerm sPerm * wLift (A.step 0)
  | s + 1 => qPerm sPerm * wLift (A.step (s + 1)) * qPerm sPerm

private lemma sStep_mem_unitaryGroup (A : QAlg ι Bool O W) (s : ℕ) :
    sStep A s ∈ Matrix.unitaryGroup (PBasis ι (QBasis ι Bool W)) ℂ := by
  cases s with
  | zero =>
      exact (Matrix.unitaryGroup _ ℂ).mul_mem (qPerm_mem_unitaryGroup _)
        (wLift_mem_unitaryGroup (A.step_unitary 0))
  | succ s =>
      exact (Matrix.unitaryGroup _ ℂ).mul_mem ((Matrix.unitaryGroup _ ℂ).mul_mem
        (qPerm_mem_unitaryGroup _) (wLift_mem_unitaryGroup (A.step_unitary (s + 1))))
        (qPerm_mem_unitaryGroup _)

end ToPlain

end Plain

/-- **The standard-model simulation of a library XOR-model algorithm**, with the standard query
register parked at `i₀`. It makes the same number of queries; its workspace holds `A`'s whole
basis `QBasis ι Bool W`. Its output distribution is that of `A` after every number of queries
(`Plain.qProb_toPlain_state`). -/
noncomputable def QAlg.toPlain (A : QAlg ι Bool O W) (i₀ : ι) :
    Plain.PAlg ι O (QBasis ι Bool W) where
  init := Plain.sEmbed i₀ A.init
  init_isQState := Plain.isQState_sEmbed i₀ A.init_isQState
  step := Plain.sStep A
  step_unitary := Plain.sStep_mem_unitaryGroup A
  readout p := A.readout (Plain.sMap p).2.2

namespace Plain

/-! ## Library algorithms are simulated by standard ones: the results -/

variable [DecidableEq O]

private lemma state_toPlain (A : QAlg ι Bool O W) (i₀ : ι) (a : ι → Bool) (t : ℕ) :
    (A.toPlain i₀).state a t = qPerm sPerm *ᵥ sEmbed i₀ (xorState A a t) := by
  induction t with
  | zero =>
      rw [PAlg.state_zero, xorState_zero]
      change (qPerm sPerm * wLift (A.step 0)) *ᵥ sEmbed i₀ A.init = _
      rw [← Matrix.mulVec_mulVec, wLift_mulVec_sEmbed]
  | succ t ih =>
      rw [PAlg.state_succ, xorState_succ, ih]
      change (qPerm sPerm * wLift (A.step (t + 1)) * qPerm sPerm) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, sPerm_plain_sPerm,
        wLift_mulVec_sEmbed]

private lemma qProb_toPlain (A : QAlg ι Bool O W) (i₀ : ι) (ψ : QBasis ι Bool W → ℂ) (o : O) :
    qProb (A.toPlain i₀).readout (qPerm sPerm *ᵥ sEmbed i₀ ψ) o = qProb A.readout ψ o := by
  rw [qProb, qProb]
  conv_lhs => rw [← Equiv.sum_comp (sPerm (ι := ι) (W := W))]
  have h := sum_sEmbed i₀ ψ (fun r => if A.readout r = o then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at h
  rw [← h]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [sPerm_mulVec_apply, show sPerm p = sMap p from rfl, sMap_involutive p]
  by_cases hp : p.1 = i₀ <;> by_cases ho : A.readout p.2.2 = o <;>
    simp [QAlg.toPlain, sEmbed, hp, ho, normSq_halfAmp_mul, sMap_involutive p]

/-- **The simulation preserves the output distribution**: after `t` queries on input `a`,
`A.toPlain i₀` (standard oracle) announces each output with the probability with which `A`
(library XOR oracle) announces it. -/
theorem qProb_toPlain_state (A : QAlg ι Bool O W) (i₀ : ι) (a : ι → Bool) (t : ℕ) (o : O) :
    qProb (A.toPlain i₀).readout ((A.toPlain i₀).state a t) o
      = qProb A.readout (xorState A a t) o := by
  rw [state_toPlain, qProb_toPlain]

/-- **Library to standard**: a library XOR-model decider is simulated by a standard-model decider
with the same query count and error, for any parking index `i₀`. -/
theorem plainComputes_toPlain {A : QAlg ι Bool O W} (i₀ : ι) {q : ℕ} {read : X → ι → Bool}
    {f : X → O} {ε : ℝ} (hA : XorComputesWithErrorOn A q read f ε) :
    PlainComputesWithErrorOn (A.toPlain i₀) q read f ε := by
  intro x
  rw [qProb_toPlain_state]
  exact hA x

/-! ## Equal query counts -/

/-- A standard-model query count is a library XOR-model query count. -/
theorem xorQueryCounts_of_plain {read : X → ι → Bool} {f : X → O} {ε : ℝ} {q : ℕ}
    (h : q ∈ PlainQueryCounts read f ε) : q ∈ XorQueryCounts read f ε := by
  obtain ⟨W, _, _, A, hA⟩ := h
  exact ⟨W, inferInstance, inferInstance, A.toXor, xorComputes_toXor hA⟩

/-- For a nonempty index type, a library XOR-model query count is a standard-model query
count. -/
theorem plainQueryCounts_of_xor [Nonempty ι] {read : X → ι → Bool} {f : X → O} {ε : ℝ} {q : ℕ}
    (h : q ∈ XorQueryCounts read f ε) : q ∈ PlainQueryCounts read f ε := by
  obtain ⟨W, _, _, A, hA⟩ := h
  exact mem_plainQueryCounts (plainComputes_toPlain (Classical.arbitrary ι) hA)

/-- **The two XOR models are equivalent**: for a nonempty index type, the standard model and the
library's XOR model achieve exactly the same query counts, for every promise `read`, function `f`
and error `ε`. (For an empty index type the standard model has no algorithms at all.) -/
theorem plainQueryCounts_eq [Nonempty ι] (read : X → ι → Bool) (f : X → O) (ε : ℝ) :
    PlainQueryCounts read f ε = XorQueryCounts read f ε :=
  Set.ext fun _ => ⟨xorQueryCounts_of_plain, plainQueryCounts_of_xor⟩

/-- **Equal complexities**: for a nonempty index type, the standard-model query complexity equals
the library's XOR-model query complexity, for every promise, function and error. -/
theorem plainQQueryOn_eq [Nonempty ι] (read : X → ι → Bool) (f : X → O) (ε : ℝ) :
    plainQQueryOn read f ε = xorQQueryOn read f ε := by
  rw [plainQQueryOn, xorQQueryOn, plainQueryCounts_eq]

end Plain

end QuantumQueryComplexity
