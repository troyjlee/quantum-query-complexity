import QuantumQueryComplexity.Quantum.Walk.Level
set_option synthInstance.maxSize 1600
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Supports, flags and the reflection contract under `kronLift`

For a factorization `e : β ≃ γ × δ` and an operator `M` on the factor `γ`:

* `eq_sum_splitVec_kSector` — every vector is a sum of split vectors over the basis of `δ`;
* `preserves_kronLift` — `kronLift e M` preserves `{p | (e p).1 ∈ G ∧ P (e p).2}` when `M`
  preserves `G`;
* `kronLift_comm_flagProj` — it commutes with a flag depending on the `δ`-factor only;
* `IsApproxRefl.kronLift` — a `β`-approximate reflection about `s₀` on `D₀` lifts to one about
  `s₀ ⊗ |d⟩` on `{w ⊗ |d⟩ | w ∈ D₀}`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {β γ δ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
  [Fintype δ] [DecidableEq δ]

/-- The `d`-sector of a vector on `β`, read on `γ`. -/
def kSector (e : β ≃ γ × δ) (d : δ) (ψ : β → ℂ) : γ → ℂ := fun c => ψ (e.symm (c, d))

lemma eq_sum_splitVec_kSector (e : β ≃ γ × δ) (ψ : β → ℂ) :
    ψ = ∑ d, splitVec e (kSector e d ψ) (qBasis d) := by
  funext p
  rw [Finset.sum_apply, Finset.sum_eq_single (e p).2]
  · rw [splitVec_apply, kSector, qBasis, Pi.single_eq_same, mul_one, Prod.mk.eta,
      Equiv.symm_apply_apply]
  · intro d _ hd
    rw [splitVec_apply, qBasis, Pi.single_eq_of_ne (Ne.symm hd), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma splitVec_add (e : β ≃ γ × δ) (φ φ' : γ → ℂ) (ξ : δ → ℂ) :
    splitVec e (φ + φ') ξ = splitVec e φ ξ + splitVec e φ' ξ := by
  funext p; simp [splitVec_apply, add_mul]

lemma splitVec_sub (e : β ≃ γ × δ) (φ φ' : γ → ℂ) (ξ : δ → ℂ) :
    splitVec e (φ - φ') ξ = splitVec e φ ξ - splitVec e φ' ξ := by
  funext p; simp [splitVec_apply, sub_mul]

lemma splitVec_smul (e : β ≃ γ × δ) (c : ℂ) (φ : γ → ℂ) (ξ : δ → ℂ) :
    splitVec e (c • φ) ξ = c • splitVec e φ ξ := by
  funext p; simp [splitVec_apply, mul_assoc]

lemma qInner_splitVec (e : β ≃ γ × δ) (φ φ' : γ → ℂ) (ξ ξ' : δ → ℂ) :
    qInner (splitVec e φ ξ) (splitVec e φ' ξ') = qInner φ φ' * qInner ξ ξ' := by
  rw [qInner_def, ← Equiv.sum_comp e.symm, Fintype.sum_prod_type, qInner_def, qInner_def,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [splitVec_apply, Equiv.apply_symm_apply, star_mul']
  ring

lemma qNorm_splitVec_qBasis (e : β ≃ γ × δ) (φ : γ → ℂ) (d : δ) :
    qNorm (splitVec e φ (qBasis d)) = qNorm φ := by
  rw [qNorm, qNormSq_splitVec, qNormSq_qBasis, mul_one, qNorm]

lemma qBasis_eq_splitVec (e : β ≃ γ × δ) (p : β) :
    qBasis p = splitVec e (qBasis (e p).1) (qBasis (e p).2) := by
  funext q
  rw [splitVec_apply, qBasis, qBasis, qBasis]
  by_cases hq : q = p
  · subst hq; simp
  · have : e q ≠ e p := fun h => hq (e.injective h)
    rw [Pi.single_eq_of_ne hq]
    by_cases h1 : (e q).1 = (e p).1
    · have h2 : (e q).2 ≠ (e p).2 := fun h2 => this (Prod.ext h1 h2)
      rw [Pi.single_eq_of_ne h2, mul_zero]
    · rw [Pi.single_eq_of_ne h1, zero_mul]

lemma splitVec_qBasis (e : β ≃ γ × δ) (c : γ) (d : δ) :
    splitVec e (qBasis c) (qBasis d) = qBasis (e.symm (c, d)) := by
  rw [qBasis_eq_splitVec e (e.symm (c, d)), Equiv.apply_symm_apply]

/-- **Supports under `kronLift`.** -/
theorem preserves_kronLift (e : β ≃ γ × δ) {M : Matrix γ γ ℂ} {G : Set γ} (hM : Preserves M G)
    (P : δ → Prop) : Preserves (kronLift e M) {p | (e p).1 ∈ G ∧ P (e p).2} := by
  intro ψ hψ p hp
  rw [eq_sum_splitVec_kSector e ψ, Matrix.mulVec_sum, Finset.sum_apply] at hp
  obtain ⟨d, _, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
  rw [kronLift_mulVec_splitVec, splitVec_apply] at hd
  have hd2 : (e p).2 = d := by
    by_contra hne
    rw [qBasis, Pi.single_eq_of_ne hne, mul_zero] at hd
    exact hd rfl
  have hsec : SuppIn G (kSector e d ψ) := fun c hc => by
    have := (hψ _ hc).1
    rwa [Equiv.apply_symm_apply] at this
  have hne : kSector e d ψ ≠ 0 := fun h0 => by
    rw [h0, Matrix.mulVec_zero] at hd; simp at hd
  obtain ⟨c, hc⟩ := Function.ne_iff.mp hne
  have hPd : P d := by
    have := (hψ _ hc).2
    rwa [Equiv.apply_symm_apply] at this
  refine ⟨hM _ hsec _ fun h0 => hd (by rw [h0, zero_mul]), hd2 ▸ hPd⟩

/-- **A flag on the other factor commutes with `kronLift`.** -/
theorem kronLift_comm_flagProj (e : β ≃ γ × δ) (M : Matrix γ γ ℂ) {c : β → Bool} {c' : δ → Bool}
    (hc : ∀ p, c p = c' (e p).2) :
    kronLift e M * flagProj c = flagProj c * kronLift e M := by
  have hflag : ∀ (φ : γ → ℂ) (d : δ), flagProj c *ᵥ splitVec e φ (qBasis d)
      = (if c' d then 1 else 0 : ℂ) • splitVec e φ (qBasis d) := by
    intro φ d
    funext p
    rw [flagProj, Matrix.mulVec_diagonal, Pi.smul_apply, splitVec_apply, hc, smul_eq_mul]
    by_cases hd : (e p).2 = d
    · rw [hd]
      try (split_ifs <;> ring)
    · rw [qBasis, Pi.single_eq_of_ne hd]; simp
  refine matrix_ext_of_mulVec_qBasis fun p => ?_
  have hp := qBasis_eq_splitVec e p
  rw [hp, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hflag, kronLift_mulVec_splitVec,
    Matrix.mulVec_smul, hflag, kronLift_mulVec_splitVec]

/-- **The contract lifts.** -/
theorem IsApproxRefl.kronLift (e : β ≃ γ × δ) {M : Matrix γ γ ℂ} {s₀ : γ → ℂ} {D₀ : Set (γ → ℂ)}
    {b : ℝ} (h : IsApproxRefl M s₀ D₀ b) (d : δ) :
    IsApproxRefl (kronLift e M) (splitVec e s₀ (qBasis d))
      {w | ∃ w₀ ∈ D₀, w = splitVec e w₀ (qBasis d)} b where
  fix := by rw [kronLift_mulVec_splitVec, h.fix]
  near := by
    rintro w ⟨w₀, hw₀, rfl⟩
    have hd : qInner (qBasis d) (qBasis d) = 1 := by
      rw [qInner_self, qNormSq_qBasis, Complex.ofReal_one]
    rw [kronLift_mulVec_splitVec, stateRefl_mulVec, qInner_splitVec, hd, mul_one,
      ← splitVec_smul, ← splitVec_sub, ← splitVec_sub, qNorm_splitVec_qBasis, ← splitVec_smul,
      ← splitVec_sub, qNorm_splitVec_qBasis, ← stateRefl_mulVec]
    exact h.near w₀ hw₀

/-! ## The lifted routine, at the matrix level -/

section Routine

variable {ι σ W W' D : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] [Fintype W'] [DecidableEq W'] [Fintype D] [DecidableEq D]

lemma oracleMat_eq_kronLift {e : QBasis ι σ W' ≃ QBasis ι σ W × D} (he : OracleCompat e)
    (a : ι → σ) : oracleMat (W := W') a = kronLift e (oracleMat (W := W) a) := by
  refine matrix_ext_of_mulVec_qBasis fun p => ?_
  rw [qBasis_eq_splitVec e p, oracleMat_mulVec_splitVec he, kronLift_mulVec_splitVec]

theorem QRoutine.kronLift_runUpto {e : QBasis ι σ W' ≃ QBasis ι σ W × D} (he : OracleCompat e)
    (R : QRoutine ι σ W) (a : ι → σ) (t : ℕ) :
    (R.kronLift e).runUpto a t = QuantumQueryComplexity.kronLift e (R.runUpto a t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [QRoutine.runUpto_succ, QRoutine.runUpto_succ, ih, oracleMat_eq_kronLift he,
        kronLift_mul, show (R.kronLift e).step (t + 1)
          = QuantumQueryComplexity.kronLift e (R.step (t + 1)) from rfl, kronLift_mul]

theorem QRoutine.kronLift_run {e : QBasis ι σ W' ≃ QBasis ι σ W × D} (he : OracleCompat e)
    (R : QRoutine ι σ W) (a : ι → σ) :
    (R.kronLift e).run a = QuantumQueryComplexity.kronLift e (R.run a) :=
  QRoutine.kronLift_runUpto he R a R.len

end Routine

end QuantumQueryComplexity
