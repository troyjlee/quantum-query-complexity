import QuantumQueryComplexity.Promise.Defs
set_option linter.style.header false

/-!
# The primal witness API on a promise domain

`QuantumQueryComplexity/Promise/Defs.lean` supplies the *upper* eliminator
`advPMOn_le`; this file supplies the *introduction* rules, so that a witness
matrix certifies `‖Γ‖ ≤ advPMOn read f` directly.

There is one hypothesis here that the total case does not need.  `advPM` is a
supremum over feasible matrices, and boundedness of that set comes from the
observation that a feasible matrix vanishes wherever no query separates the two
inputs.  On a promise domain two *distinct* inputs may look identical at every
query, and then nothing constrains `Γ` there at all: the value set is unbounded
and `sSup` degenerates.  So every lemma below assumes

  `hdet : ∀ x y, read x = read y → f x = f y`,

i.e. the observations determine the output. Injectivity of `read` implies
this condition, as `separates_of_injective` records.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [DecidableEq σ]
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {O : Type*} {read : X → ι → σ} {f : X → O} {Γ : Matrix X X ℝ}

/-- An injective observation map determines the output. -/
lemma separates_of_injective (hread : Function.Injective read) (f : X → O) :
    ∀ x y, read x = read y → f x = f y := fun _ _ h => by rw [hread h]

/-- All entries of a feasible matrix are bounded by `1`: entries with equal
output vanish, and the rest are separated by some query. -/
lemma abs_apply_le_one_of_feasibleOn
    (hdet : ∀ x y, read x = read y → f x = f y) (h1 : IsAdvMatrixOn f Γ)
    (h2 : ∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1) (x y : X) : |Γ x y| ≤ 1 := by
  by_cases hf : f x = f y
  · simp [h1.2 x y hf]
  · have hxy : read x ≠ read y := fun h => hf (hdet x y h)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    have h3 := abs_entry_le_l2_opNorm (Γ ⊙ advDOn read i) x y
    rw [hadamard_advDOn_apply, if_neg hi] at h3
    exact h3.trans (h2 i)

/-- The a priori bound making the `advPMOn` value set bounded above. -/
lemma norm_le_of_feasibleOn (hdet : ∀ x y, read x = read y → f x = f y)
    (h1 : IsAdvMatrixOn f Γ) (h2 : ∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1) :
    ‖Γ‖ ≤ (Fintype.card X : ℝ) ^ 2 := by
  refine (l2_opNorm_le_sum_abs Γ).trans ?_
  calc ∑ x, ∑ y, |Γ x y| ≤ ∑ _x : X, ∑ _y : X, (1 : ℝ) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
        abs_apply_le_one_of_feasibleOn hdet h1 h2 x y
    _ = (Fintype.card X : ℝ) ^ 2 := by
      simp [Finset.sum_const, Finset.card_univ, pow_two]

lemma bddAbove_advPMOn_set (hdet : ∀ x y, read x = read y → f x = f y) :
    BddAbove {r : ℝ | ∃ Γ, IsAdvMatrixOn f Γ ∧
      (∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1) ∧ r = ‖Γ‖} := by
  refine ⟨(Fintype.card X : ℝ) ^ 2, ?_⟩
  rintro r ⟨Γ, h1, h2, rfl⟩
  exact norm_le_of_feasibleOn hdet h1 h2

/-- **Every feasible matrix certifies a lower bound on `advPMOn`.** -/
theorem le_advPMOn (hdet : ∀ x y, read x = read y → f x = f y)
    (h1 : IsAdvMatrixOn f Γ) (h2 : ∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1) :
    ‖Γ‖ ≤ advPMOn read f :=
  le_csSup (bddAbove_advPMOn_set hdet) ⟨Γ, h1, h2, rfl⟩

theorem advPMOn_nonneg (hdet : ∀ x y, read x = read y → f x = f y) :
    0 ≤ advPMOn read f := by
  simpa using le_advPMOn (Γ := (0 : Matrix X X ℝ)) hdet (isAdvMatrixOn_zero f)
    fun i => by simp

lemma IsAdvMatrixOn.smul (h : IsAdvMatrixOn f Γ) (c : ℝ) :
    IsAdvMatrixOn f (c • Γ) :=
  ⟨h.1.smul (star_trivial c), fun x y hxy => by
    rw [Matrix.smul_apply, h.2 x y hxy, smul_zero]⟩

/-- **The un-normalized witness lemma on a promise domain.** Exhibit a matrix,
bound its masked norms by `c`, and read off `‖Γ‖ / c`. -/
theorem norm_div_le_advPMOn (hdet : ∀ x y, read x = read y → f x = f y)
    (h1 : IsAdvMatrixOn f Γ) {c : ℝ}
    (h2 : ∀ i, ‖Γ ⊙ advDOn read i‖ ≤ c) (hc : 0 < c) :
    ‖Γ‖ / c ≤ advPMOn read f := by
  have k1 : IsAdvMatrixOn f (c⁻¹ • Γ) := h1.smul c⁻¹
  have k2 : ∀ i, ‖(c⁻¹ • Γ) ⊙ advDOn read i‖ ≤ 1 := fun i => by
    rw [Matrix.smul_hadamard, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hc)]
    calc c⁻¹ * ‖Γ ⊙ advDOn read i‖ ≤ c⁻¹ * c :=
        mul_le_mul_of_nonneg_left (h2 i) (inv_pos.mpr hc).le
      _ = 1 := inv_mul_cancel₀ hc.ne'
  have h := le_advPMOn hdet k1 k2
  rwa [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc),
    inv_mul_eq_div] at h

/-- The ε-accessor, for arguments that need a witness beating a given value. -/
theorem exists_lt_of_lt_advPMOn (hdet : ∀ x y, read x = read y → f x = f y)
    {c : ℝ} (h : c < advPMOn read f) :
    ∃ Γ, IsAdvMatrixOn f Γ ∧ (∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1) ∧ c < ‖Γ‖ := by
  obtain ⟨r, hr, hcr⟩ := exists_lt_of_lt_csSup (advPMOn_set_nonempty read f) h
  obtain ⟨Γ, h1, h2, rfl⟩ := hr
  exact ⟨Γ, h1, h2, hcr⟩

/-! ## The total case is a promise on the whole cube

A sanity check that the promise API really extends the total one: reading the
identity on the full cube gives back `advPM`. -/

section Total
variable [Fintype σ] [DecidableEq O]

@[simp] lemma advDOn_id (i : ι) :
    advDOn (fun x : ι → σ => x) i = advD i := rfl

lemma isAdvMatrixOn_id_iff {g : (ι → σ) → O}
    {Γ : Matrix (ι → σ) (ι → σ) ℝ} :
    IsAdvMatrixOn g Γ ↔ IsAdvMatrix g Γ := Iff.rfl

@[simp] theorem advPMOn_id (g : (ι → σ) → O) :
    advPMOn (fun x : ι → σ => x) g = advPM g := rfl

end Total

end QuantumQueryComplexity
