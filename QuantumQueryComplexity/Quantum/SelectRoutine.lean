import QuantumQueryComplexity.Quantum.Mixture
import QuantumQueryComplexity.Quantum.ProductRun
import QuantumQueryComplexity.Quantum.Amplitude.Geometry
set_option synthInstance.maxSize 1600
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Coherently selecting a supplied subroutine

`QRoutine.sig L R` runs, on the sector `ω` of the direct-sum workspace `Σ ω, W ω`, the
routine `R ω`.  The sector label is the *candidate index*: it is preserved, and the routine
acts as the selected one on each sector **in superposition** — it is one block-diagonal
unitary per step (`sigFam`, from `Mixture.lean`), not a classical mixture, so it has an
inverse and different sectors interfere under later sector-mixing operations.

* `QRoutine.sig_runUpto`, `sig_run` — the operator equation, at every time;
* `sig_run_mulVec_embed`, `sig_run_mulVec_sum` — the state equation on one sector and on an
  arbitrary superposition of sectors;
* `sig_len` — **one invocation costs the common length `L`**, not the sum of the lengths.

Routines of different lengths are first padded: `selectPadded A q T` selects among the
algorithms `A ω` run for `q ω ≤ T` queries, each padded to exactly `T` queries by the parking
construction (`padRoutine`); workspaces, initial states and readouts may all differ.
`selectPadded_run` is its state equation and `selectPadded_prob` its sectorwise statistics.

## Selection controlled by a spectator

When the candidate index is carried by *another* register, entangled with anything at all,
the selected operation is `ctrlLift e fam`: block-diagonal in the control factor of a
factorization `e : β ≃ δ × γ`, acting by `fam g` on the target factor.  `bankCtrl c U`
specializes it to the bank layout of `pairRoutine`: the second bank is acted on by `U (c y)`,
where `y` is the basis state of the first.  `bankCtrl_mulVec_prodState` is the state
equation for an arbitrary first-bank vector: its `c = i` component gets `U i`.

`swapRefl u v` is a free unitary exchanging two orthogonal unit vectors; with it a blank bank
is initialized *coherently, depending on the index*, to the initial vector of the selected
algorithm (`bankCtrl` of the family `swapRefl blank (init i)`).
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {W : Ω → Type} [∀ ω, Fintype (W ω)]
  [∀ ω, DecidableEq (W ω)]

/-- **Coherent selection**: on the sector `ω`, the steps of `R ω`; `L` queries. -/
def QRoutine.sig (L : ℕ) (R : ∀ ω, QRoutine ι σ (W ω)) : QRoutine ι σ (Σ ω, W ω) where
  len := L
  step := fun t => sigFam fun ω => (R ω).step t
  step_unitary := fun t => sigFam_mem_unitaryGroup fun ω => (R ω).step_unitary t

@[simp] lemma QRoutine.sig_len (L : ℕ) (R : ∀ ω, QRoutine ι σ (W ω)) :
    (QRoutine.sig L R).len = L := rfl

/-- **The operator equation**: at every time the selected routine is the block family of
the partial runs. -/
theorem QRoutine.sig_runUpto (L : ℕ) (R : ∀ ω, QRoutine ι σ (W ω)) (a : ι → σ) (t : ℕ) :
    (QRoutine.sig L R).runUpto a t = sigFam fun ω => (R ω).runUpto a t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [QRoutine.runUpto_succ, ih, sigFam_oracle, sigFam_mul]
      show sigFam (fun ω => (R ω).step (t + 1)) * _ = _
      rw [sigFam_mul]
      rfl

theorem QRoutine.sig_run {L : ℕ} {R : ∀ ω, QRoutine ι σ (W ω)} (hL : ∀ ω, (R ω).len = L)
    (a : ι → σ) : (QRoutine.sig L R).run a = sigFam fun ω => (R ω).run a := by
  rw [QRoutine.run, QRoutine.sig_runUpto]
  congr 1
  funext ω
  rw [QRoutine.run, hL ω]
  rfl

/-- The state equation on one sector. -/
theorem QRoutine.sig_run_mulVec_embed {L : ℕ} {R : ∀ ω, QRoutine ι σ (W ω)}
    (hL : ∀ ω, (R ω).len = L) (a : ι → σ) (ω : Ω) (ψ : QBasis ι σ (W ω) → ℂ) :
    (QRoutine.sig L R).run a *ᵥ embedSig ω ψ = embedSig ω ((R ω).run a *ᵥ ψ) := by
  rw [QRoutine.sig_run hL, sigFam_mulVec_embed]

/-- **The state equation in superposition**: each sector evolves under its own routine. -/
theorem QRoutine.sig_run_mulVec_sum {L : ℕ} {R : ∀ ω, QRoutine ι σ (W ω)}
    (hL : ∀ ω, (R ω).len = L) (a : ι → σ) (φ : ∀ ω, QBasis ι σ (W ω) → ℂ) :
    (QRoutine.sig L R).run a *ᵥ (∑ ω, embedSig ω (φ ω))
      = ∑ ω, embedSig ω ((R ω).run a *ᵥ φ ω) := by
  rw [Matrix.mulVec_sum]
  exact Finset.sum_congr rfl fun ω _ => QRoutine.sig_run_mulVec_embed hL a ω (φ ω)

/-! ## One sector -/

lemma embedSig_zero (ω : Ω) : embedSig (ι := ι) (σ := σ) ω (0 : QBasis ι σ (W ω) → ℂ) = 0 := by
  funext p
  simp [embedSig, embedSig']

lemma embedSig_eq_sum_single (ω : Ω) (ψ : QBasis ι σ (W ω) → ℂ) :
    embedSig ω ψ = ∑ ω', embedSig ω' ((Pi.single ω ψ : ∀ ω', QBasis ι σ (W ω') → ℂ) ω') := by
  rw [Finset.sum_eq_single ω]
  · rw [Pi.single_eq_same]
  · intro ω' _ h
    rw [Pi.single_eq_of_ne h, embedSig_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma qNormSq_embedSig (ω : Ω) (ψ : QBasis ι σ (W ω) → ℂ) :
    qNormSq (embedSig ω ψ) = qNormSq ψ := by
  rw [embedSig_eq_sum_single, qNormSq_sum_embedSig, Finset.sum_eq_single ω]
  · rw [Pi.single_eq_same]
  · intro ω' _ h
    rw [Pi.single_eq_of_ne h, qNormSq_def]
    simp
  · intro h; exact absurd (Finset.mem_univ _) h

lemma qProb_sigReadout_embedSig {O : Type} [DecidableEq O] (rd : ∀ ω, QBasis ι σ (W ω) → O)
    (ω : Ω) (ψ : QBasis ι σ (W ω) → ℂ) (o : O) :
    qProb (sigReadout rd) (embedSig ω ψ) o = qProb (rd ω) ψ o := by
  rw [embedSig_eq_sum_single, qProb_sum_embedSig, Finset.sum_eq_single ω]
  · rw [Pi.single_eq_same]
  · intro ω' _ h
    rw [Pi.single_eq_of_ne h, qProb]
    simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## Algorithms with different budgets, workspaces, initial states and readouts -/

variable {O : Type} [DecidableEq O]

/-- **Selection among padded algorithms**: `A ω` run for `q ω` queries and parked up to `T`. -/
def selectPadded (A : ∀ ω, QAlg ι σ O (W ω)) (q : Ω → ℕ) (T : ℕ) :
    QRoutine ι σ (Σ ω, CtrlWork ι (W ω)) :=
  QRoutine.sig T fun ω => padRoutine (A ω) (q ω) (T - q ω)

@[simp] lemma selectPadded_len (A : ∀ ω, QAlg ι σ O (W ω)) (q : Ω → ℕ) (T : ℕ) :
    (selectPadded A q T).len = T := rfl

/-- The initial vector of the sector `ω`. -/
def selectInit (A : ∀ ω, QAlg ι σ O (W ω)) (ω : Ω) : QBasis ι σ (Σ ω, CtrlWork ι (W ω)) → ℂ :=
  embedSig ω (embedCtrl true (A ω).init)

/-- **The state equation of the adapter**: on the sector `ω` the final state of `A ω` after
its own `q ω` queries, in the idle sector of the parking construction. -/
theorem selectPadded_run {A : ∀ ω, QAlg ι σ O (W ω)} {q : Ω → ℕ} {T : ℕ} (hq : ∀ ω, q ω ≤ T)
    (a : ι → σ) (ω : Ω) :
    (selectPadded A q T).run a *ᵥ selectInit A ω
      = embedSig ω (embedCtrl false ((A ω).state a (q ω))) := by
  have hL : ∀ ω, (padRoutine (A ω) (q ω) (T - q ω)).len = T := fun ω => by
    rw [padRoutine_len]; have := hq ω; omega
  rw [selectPadded, selectInit, QRoutine.sig_run_mulVec_embed hL, padRoutine_run]

/-- The readout of the adapter: the readout of the algorithm of the sector. -/
def selectReadout (A : ∀ ω, QAlg ι σ O (W ω)) : QBasis ι σ (Σ ω, CtrlWork ι (W ω)) → O :=
  sigReadout fun ω => dropCtrl (A ω).readout

lemma isQState_selectInit (A : ∀ ω, QAlg ι σ O (W ω)) (ω : Ω) : IsQState (selectInit A ω) := by
  rw [IsQState, selectInit, qNormSq_embedSig]
  exact isQState_embedCtrl true (A ω).init_isQState

/-- **The statistics of the adapter on the sector `ω` are those of `A ω`.** -/
theorem selectPadded_prob {A : ∀ ω, QAlg ι σ O (W ω)} {q : Ω → ℕ} {T : ℕ} (hq : ∀ ω, q ω ≤ T)
    (a : ι → σ) (ω : Ω) (o : O) :
    qProb (selectReadout A) ((selectPadded A q T).run a *ᵥ selectInit A ω) o
      = (A ω).prob a (q ω) o := by
  rw [selectPadded_run hq, selectReadout, qProb_sigReadout_embedSig, qProb_embedCtrl]
  rfl

/-! ## Selection controlled by a spectator -/

section Ctrl

variable {β γ δ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
  [Fintype δ] [DecidableEq δ]

/-- The family `fam`, block-diagonal in the control factor `γ` of `e`. -/
def ctrlLift (e : β ≃ δ × γ) (fam : γ → Matrix δ δ ℂ) : Matrix β β ℂ :=
  (Matrix.blockDiagonal fam).submatrix e e

lemma ctrlLift_mem_unitaryGroup (e : β ≃ δ × γ) {fam : γ → Matrix δ δ ℂ}
    (h : ∀ g, fam g ∈ Matrix.unitaryGroup δ ℂ) : ctrlLift e fam ∈ Matrix.unitaryGroup β ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ctrlLift,
    Matrix.conjTranspose_submatrix, Matrix.blockDiagonal_conjTranspose,
    Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]
  have : (fun g => (fam g)ᴴ * fam g) = (1 : γ → Matrix δ δ ℂ) := by
    funext g
    exact conjTranspose_mul_self_of_unitary (h g)
  rw [this, Matrix.blockDiagonal_one, Matrix.submatrix_one_equiv]

/-- The action, pointwise: the block of the control value acts on the target factor. -/
theorem ctrlLift_mulVec_apply (e : β ≃ δ × γ) (fam : γ → Matrix δ δ ℂ) (ψ : β → ℂ) (b : β) :
    (ctrlLift e fam *ᵥ ψ) b = ∑ d, fam (e b).2 (e b).1 d * ψ (e.symm (d, (e b).2)) := by
  rw [Matrix.mulVec, dotProduct, ← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_eq_single (e b).2]
  · rw [ctrlLift, Matrix.submatrix_apply, Equiv.apply_symm_apply, Matrix.blockDiagonal_apply,
      if_pos rfl]
  · intro g _ hg
    rw [ctrlLift, Matrix.submatrix_apply, Equiv.apply_symm_apply, Matrix.blockDiagonal_apply,
      if_neg (Ne.symm hg), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

end Ctrl

section Bank

variable {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
  {I : Type} [Fintype I] [DecidableEq I]

/-- The second bank as the target; the global query registers and the first bank control. -/
def bankEquiv : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂)
    ≃ QBasis ι σ W₂ × ((Option ι × Option σ) × QBasis ι σ W₁) where
  toFun p := (p.2.2.2, ((p.1, p.2.1), p.2.2.1))
  invFun q := (q.2.1.1, q.2.1.2, (q.2.2, q.1))
  left_inv := by rintro ⟨k, t, y, b⟩; rfl
  right_inv := by rintro ⟨b, ⟨k, t⟩, y⟩; rfl

/-- **The second bank is acted on by `U (c y)`, `y` the basis state of the first.** -/
def bankCtrl (c : QBasis ι σ W₁ → I) (U : I → Matrix (QBasis ι σ W₂) (QBasis ι σ W₂) ℂ) :
    Matrix (QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂))
      (QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂)) ℂ :=
  ctrlLift bankEquiv fun g => U (c g.2)

lemma bankCtrl_mem_unitaryGroup (c : QBasis ι σ W₁ → I)
    {U : I → Matrix (QBasis ι σ W₂) (QBasis ι σ W₂) ℂ}
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup (QBasis ι σ W₂) ℂ) :
    bankCtrl c U ∈ Matrix.unitaryGroup _ ℂ :=
  ctrlLift_mem_unitaryGroup _ fun g => hU (c g.2)

/-- On a first-bank vector with control value `i`, the second bank gets `U i`. -/
theorem bankCtrl_mulVec_prodState_restrict (c : QBasis ι σ W₁ → I)
    (U : I → Matrix (QBasis ι σ W₂) (QBasis ι σ W₂) ℂ) (χ : Option ι × Option σ → ℂ)
    (φ : QBasis ι σ W₁ → ℂ) (ξ : QBasis ι σ W₂ → ℂ) (i : I) :
    bankCtrl c U *ᵥ prodState χ (qRestrict c i φ) ξ
      = prodState χ (qRestrict c i φ) (U i *ᵥ ξ) := by
  funext p
  obtain ⟨k, t, y, b⟩ := p
  rw [bankCtrl, ctrlLift_mulVec_apply]
  show ∑ d, U (c y) b d * (χ (k, t) * qRestrict c i φ y * ξ d)
    = χ (k, t) * qRestrict c i φ y * (U i *ᵥ ξ) b
  by_cases h : c y = i
  · rw [h, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  · rw [qRestrict, if_neg h, mul_zero, zero_mul]
    exact Finset.sum_eq_zero fun d _ => by rw [zero_mul, mul_zero]

lemma prodState_sum_left {α : Type*} (s : Finset α) (χ : Option ι × Option σ → ℂ)
    (φ : α → QBasis ι σ W₁ → ℂ) (ξ : QBasis ι σ W₂ → ℂ) :
    prodState χ (∑ i ∈ s, φ i) ξ = ∑ i ∈ s, prodState χ (φ i) ξ := by
  funext p
  simp only [prodState, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]

/-- **The state equation with an arbitrary spectator**: the component of the first bank
with control value `i` gets `U i` on the second bank. -/
theorem bankCtrl_mulVec_prodState (c : QBasis ι σ W₁ → I)
    (U : I → Matrix (QBasis ι σ W₂) (QBasis ι σ W₂) ℂ) (χ : Option ι × Option σ → ℂ)
    (φ : QBasis ι σ W₁ → ℂ) (ξ : QBasis ι σ W₂ → ℂ) :
    bankCtrl c U *ᵥ prodState χ φ ξ = ∑ i, prodState χ (qRestrict c i φ) (U i *ᵥ ξ) := by
  conv_lhs => rw [← sum_qRestrict c φ, prodState_sum_left, Matrix.mulVec_sum]
  exact Finset.sum_congr rfl fun i _ => bankCtrl_mulVec_prodState_restrict c U χ φ ξ i

end Bank

/-! ## Exchanging two orthogonal unit vectors -/

section Swap

variable {H : Type} [Fintype H] [DecidableEq H]

/-- The reflection about the bisector of `u` and `v`. -/
noncomputable def swapRefl (u v : H → ℂ) : Matrix H H ℂ :=
  stateRefl ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (u + v))

lemma isQState_bisector {u v : H → ℂ} (hu : IsQState u) (hv : IsQState v)
    (huv : qInner u v = 0) : IsQState ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (u + v)) := by
  rw [IsQState, qNormSq_smul, qNormSq_add, hu, hv, huv, Complex.zero_re, Complex.normSq_ofReal]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  nlinarith

lemma swapRefl_mem_unitaryGroup {u v : H → ℂ} (hu : IsQState u) (hv : IsQState v)
    (huv : qInner u v = 0) : swapRefl u v ∈ Matrix.unitaryGroup H ℂ :=
  stateRefl_mem_unitaryGroup (isQState_bisector hu hv huv)

/-- **It carries `u` to `v`.** -/
theorem swapRefl_mulVec {u v : H → ℂ} (hu : IsQState u) (huv : qInner u v = 0) :
    swapRefl u v *ᵥ u = v := by
  have hvu : qInner v u = 0 := by rw [← qInner_conj, huv, star_zero]
  rw [swapRefl, stateRefl_mulVec, qInner_smul_left, qInner_add_left, qInner_self, hu, hvu,
    add_zero, smul_smul]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  have hc : (2 * (star (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * ((1 : ℝ) : ℂ)))
      * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    field_simp
    linarith
  rw [hc, one_smul, add_sub_cancel_left]

end Swap

end QuantumQueryComplexity
