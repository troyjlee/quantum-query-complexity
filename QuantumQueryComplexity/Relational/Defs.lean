import QuantumQueryComplexity.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option linter.style.header false

/-!
# The relational negative-weight adversary bound

Belovs (arXiv:1504.06943) extended the adversary bound to relations; the
primal characterization (Belovs–Lee arXiv:2004.06439, Theorem 14) reads:

  `ADV±_rel(f) = max λ_max(Γ)` over symmetric `Γ` with `‖Γ ⊙ D_i‖ ≤ 1` and
  `Γ ⊙ χ_a χ_aᵀ ⪯ 0` for every output `a`,

where `χ_a` is the 0/1 indicator of `{x | (x, a) ∈ f}`.  We take this primal
program as the *definition*, phrasing the objective as a supremum of Rayleigh
quotients `v ⬝ᵥ Γ *ᵥ v` over unit vectors `v` — this equals the maximum of
`λ_max` without requiring a standalone eigenvalue-maximum theory.

A relation on inputs `ι → Bool` with outputs `κ` is given by its indicator
family `χ : κ → (ι → Bool) → Bool`.  Following BL we assume totality
(`∀ x, ∃ a, χ a x`) where needed — without it the diagonal of `Γ` is
unconstrained and the program is unbounded.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- The 0/1 indicator vector of output `a`. -/
def chiVec (χ : κ → (ι → Bool) → Bool) (a : κ) : (ι → Bool) → ℝ :=
  fun x => if χ a x then 1 else 0

/-- A relational adversary matrix (BL Theorem 14): real symmetric with
`Γ ⊙ χ_a χ_aᵀ ⪯ 0` for every output `a`. -/
def IsRelAdvMatrix (χ : κ → (ι → Bool) → Bool)
    (Γ : Matrix (ι → Bool) (ι → Bool) ℝ) : Prop :=
  Γ.IsHermitian ∧ ∀ a : κ,
    (-(Γ ⊙ Matrix.vecMulVec (chiVec χ a) (chiVec χ a))).PosSemidef

namespace IsRelAdvMatrix

variable {χ : κ → (ι → Bool) → Bool} {Γ : Matrix (ι → Bool) (ι → Bool) ℝ}

lemma isHermitian (h : IsRelAdvMatrix χ Γ) : Γ.IsHermitian := h.1

/-- With totality, the diagonal of a relational adversary matrix is
nonpositive. -/
lemma diag_nonpos (h : IsRelAdvMatrix χ Γ) {x : ι → Bool} {a : κ}
    (ha : χ a x) : Γ x x ≤ 0 := by
  have hd := (h.2 a).diag_nonneg (i := x)
  simp only [Matrix.neg_apply, Matrix.hadamard_apply, Matrix.vecMulVec_apply,
    chiVec, if_pos ha] at hd
  linarith

end IsRelAdvMatrix

lemma posSemidef_zeroMatrix {n : Type*} [Fintype n] :
    (0 : Matrix n n ℝ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · show _ᴴ = _
    ext i j
    simp
  · simp [Matrix.mulVec_zero]

lemma isRelAdvMatrix_zero (χ : κ → (ι → Bool) → Bool) :
    IsRelAdvMatrix χ (0 : Matrix (ι → Bool) (ι → Bool) ℝ) := by
  refine ⟨Matrix.isHermitian_zero, fun a => ?_⟩
  rw [Matrix.zero_hadamard, neg_zero]
  exact posSemidef_zeroMatrix

/-- `ADV±_rel`, defined by the primal program of BL Theorem 14. -/
noncomputable def relAdvPM (χ : κ → (ι → Bool) → Bool) : ℝ :=
  sSup {r : ℝ | ∃ Γ v, IsRelAdvMatrix χ Γ ∧ (∀ i, ‖Γ ⊙ advD i‖ ≤ 1) ∧
    v ⬝ᵥ v = 1 ∧ r = v ⬝ᵥ Γ *ᵥ v}

/-- The a priori bound on Rayleigh quotients of feasible matrices (uses
totality for the diagonal). -/
lemma rayleigh_le_of_relFeasible {χ : κ → (ι → Bool) → Bool}
    {Γ : Matrix (ι → Bool) (ι → Bool) ℝ}
    (htot : ∀ x, ∃ a, χ a x)
    (h1 : IsRelAdvMatrix χ Γ) (h2 : ∀ i, ‖Γ ⊙ advD i‖ ≤ 1)
    {v : (ι → Bool) → ℝ} (hv : v ⬝ᵥ v = 1) :
    v ⬝ᵥ Γ *ᵥ v ≤ (Fintype.card (ι → Bool) : ℝ) ^ 2 := by
  have hvbound : ∀ x, |v x| ≤ 1 := by
    intro x
    have h := abs_apply_le_sqrt_dotProduct_self v x
    rwa [hv, Real.sqrt_one] at h
  rw [dotProduct_mulVec_eq_sum]
  calc ∑ x, ∑ y, v x * Γ x y * v y
      ≤ ∑ _x : ι → Bool, ∑ _y : ι → Bool, (1 : ℝ) := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        by_cases hxy : x = y
        · subst hxy
          obtain ⟨a, ha⟩ := htot x
          have hd := h1.diag_nonpos ha
          nlinarith [mul_self_nonneg (v x)]
        · have hoff : |Γ x y| ≤ 1 := by
            obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
            have h3 := abs_entry_le_l2_opNorm (Γ ⊙ advD i) x y
            rw [hadamard_advD_apply, if_neg hi] at h3
            exact h3.trans (h2 i)
          calc v x * Γ x y * v y ≤ |v x * Γ x y * v y| := le_abs_self _
            _ = |v x| * |Γ x y| * |v y| := by rw [abs_mul, abs_mul]
            _ ≤ 1 * 1 * 1 :=
                mul_le_mul
                  (mul_le_mul (hvbound x) hoff (abs_nonneg _) zero_le_one)
                  (hvbound y) (abs_nonneg _) (by norm_num)
            _ = 1 := by ring
    _ = (Fintype.card (ι → Bool) : ℝ) ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, pow_two]

lemma relAdvPM_set_nonempty (χ : κ → (ι → Bool) → Bool) :
    {r : ℝ | ∃ Γ v, IsRelAdvMatrix χ Γ ∧ (∀ i, ‖Γ ⊙ advD i‖ ≤ 1) ∧
      v ⬝ᵥ v = 1 ∧ r = v ⬝ᵥ Γ *ᵥ v}.Nonempty := by
  refine ⟨0, 0, Pi.single (fun _ => false) 1, isRelAdvMatrix_zero χ,
    fun i => by simp, ?_, ?_⟩
  · simp [single_dotProduct]
  · simp [Matrix.zero_mulVec]

lemma bddAbove_relAdvPM_set {χ : κ → (ι → Bool) → Bool}
    (htot : ∀ x, ∃ a, χ a x) :
    BddAbove {r : ℝ | ∃ Γ v, IsRelAdvMatrix χ Γ ∧ (∀ i, ‖Γ ⊙ advD i‖ ≤ 1) ∧
      v ⬝ᵥ v = 1 ∧ r = v ⬝ᵥ Γ *ᵥ v} := by
  refine ⟨(Fintype.card (ι → Bool) : ℝ) ^ 2, ?_⟩
  rintro r ⟨Γ, v, h1, h2, hv, rfl⟩
  exact rayleigh_le_of_relFeasible htot h1 h2 hv

theorem le_relAdvPM {χ : κ → (ι → Bool) → Bool}
    (htot : ∀ x, ∃ a, χ a x)
    {Γ : Matrix (ι → Bool) (ι → Bool) ℝ} {v : (ι → Bool) → ℝ}
    (h1 : IsRelAdvMatrix χ Γ) (h2 : ∀ i, ‖Γ ⊙ advD i‖ ≤ 1)
    (hv : v ⬝ᵥ v = 1) : v ⬝ᵥ Γ *ᵥ v ≤ relAdvPM χ :=
  le_csSup (bddAbove_relAdvPM_set htot) ⟨Γ, v, h1, h2, hv, rfl⟩

theorem relAdvPM_le {χ : κ → (ι → Bool) → Bool} {c : ℝ}
    (hc : ∀ Γ v, IsRelAdvMatrix χ Γ → (∀ i, ‖Γ ⊙ advD i‖ ≤ 1) →
      v ⬝ᵥ v = 1 → v ⬝ᵥ Γ *ᵥ v ≤ c) :
    relAdvPM χ ≤ c := by
  refine csSup_le (relAdvPM_set_nonempty χ) ?_
  rintro r ⟨Γ, v, h1, h2, hv, rfl⟩
  exact hc Γ v h1 h2 hv

theorem relAdvPM_nonneg {χ : κ → (ι → Bool) → Bool}
    (htot : ∀ x, ∃ a, χ a x) : 0 ≤ relAdvPM χ := by
  have h := le_relAdvPM htot (isRelAdvMatrix_zero χ)
    (fun i => by simp) (v := Pi.single (fun _ => false) 1)
    (by simp [single_dotProduct])
  simpa [Matrix.zero_mulVec] using h

/-- The un-normalized witness lemma for the relational bound. -/
theorem rayleigh_div_le_relAdvPM {χ : κ → (ι → Bool) → Bool}
    (htot : ∀ x, ∃ a, χ a x)
    {Γ : Matrix (ι → Bool) (ι → Bool) ℝ} (h1 : IsRelAdvMatrix χ Γ) {c : ℝ}
    (h2 : ∀ i, ‖Γ ⊙ advD i‖ ≤ c) (hc : 0 < c) {v : (ι → Bool) → ℝ}
    (hv : v ⬝ᵥ v = 1) : (v ⬝ᵥ Γ *ᵥ v) / c ≤ relAdvPM χ := by
  have k1 : IsRelAdvMatrix χ (c⁻¹ • Γ) := by
    refine ⟨h1.1.smul (star_trivial _), fun a => ?_⟩
    have heq : -((c⁻¹ • Γ) ⊙ Matrix.vecMulVec (chiVec χ a) (chiVec χ a))
        = c⁻¹ • (-(Γ ⊙ Matrix.vecMulVec (chiVec χ a) (chiVec χ a))) := by
      rw [Matrix.smul_hadamard]
      ext x y
      simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    have hP := h1.2 a
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (hP.isHermitian.smul (star_trivial _)) fun x => ?_
    rw [star_trivial, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    have h0 := hP.dotProduct_mulVec_nonneg x
    rw [star_trivial] at h0
    exact mul_nonneg (inv_pos.mpr hc).le h0
  have k2 : ∀ i, ‖(c⁻¹ • Γ) ⊙ advD i‖ ≤ 1 := fun i => by
    rw [Matrix.smul_hadamard, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hc)]
    calc c⁻¹ * ‖Γ ⊙ advD i‖ ≤ c⁻¹ * c :=
        mul_le_mul_of_nonneg_left (h2 i) (inv_pos.mpr hc).le
      _ = 1 := inv_mul_cancel₀ hc.ne'
  have k3 : v ⬝ᵥ (c⁻¹ • Γ) *ᵥ v = c⁻¹ * (v ⬝ᵥ Γ *ᵥ v) := by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have h := le_relAdvPM htot k1 k2 hv
  rw [k3] at h
  rwa [div_eq_inv_mul]

end QuantumQueryComplexity
