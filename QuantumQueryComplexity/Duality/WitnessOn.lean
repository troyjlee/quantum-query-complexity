import QuantumQueryComplexity.Duality.Witness
import QuantumQueryComplexity.Duality.GramOn
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# From a certificate to an adversary matrix, on a promise domain

The promise mirror of `Duality/Witness.lean`: the multipliers of the
separating hyperplane become a feasible `IsAdvMatrixOn` witness, so the
certificate forces `c < advPMOn read f`.  The two generic norm lemmas
(`l2_opNorm_le_two_of_quadratic` and the `±1` diagonal conjugation) are
imported, not re-proved; the `±1` mask argument uses only that the *output*
is two-valued, which holds verbatim for `f : X → Bool`.

`hdet` (read-determinacy) enters exactly once, through `le_advPMOn` — the
promise adversary bound is a supremum only over a bounded set when the
promise is determined.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

section Mask

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The `±1` sign vector of a Boolean function on the promise domain. -/
def boolSignOn (f : X → Bool) : X → ℝ := fun x => if f x then 1 else -1

lemma boolSignOn_eq_one_or (f : X → Bool) (x : X) :
    boolSignOn f x = 1 ∨ boolSignOn f x = -1 := by
  by_cases h : f x = true <;> simp [boolSignOn, h]

lemma boolSignOn_mul (f : X → Bool) (x y : X) :
    boolSignOn f x * boolSignOn f y = 1 - 2 * dualTargetOn f x y := by
  rcases Bool.eq_false_or_eq_true (f x) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (f y) with h2 | h2 <;>
      simp [boolSignOn, dualTargetOn, h1, h2] <;> norm_num

/-- Masking off the pairs with equal value does not increase the spectral
norm: for a two-valued `f` the mask is an average of the identity and a `±1`
diagonal conjugation. -/
lemma l2_opNorm_hadamard_dualTargetOn_le (f : X → Bool)
    (M : Matrix X X ℝ) : ‖M ⊙ dualTargetOn f‖ ≤ ‖M‖ := by
  set s := boolSignOn f with hs
  have hsplit : M ⊙ dualTargetOn f
      = (2 : ℝ)⁻¹ • (M - Matrix.diagonal s * M * Matrix.diagonal s) := by
    ext x y
    have hmul : (Matrix.diagonal s * M * Matrix.diagonal s) x y
        = s x * M x y * s y := by
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    have hsxy : s x * s y = 1 - 2 * dualTargetOn f x y := boolSignOn_mul f x y
    rw [Matrix.hadamard_apply, Matrix.smul_apply, Matrix.sub_apply, hmul,
      smul_eq_mul]
    have : s x * M x y * s y = M x y * (s x * s y) := by ring
    rw [this, hsxy]
    ring
  rw [hsplit, norm_smul]
  have hconj : ‖Matrix.diagonal s * M * Matrix.diagonal s‖ = ‖M‖ :=
    l2_opNorm_conj_diagonal_sign (boolSignOn_eq_one_or f) M
  have := norm_sub_le M (Matrix.diagonal s * M * Matrix.diagonal s)
  rw [hconj] at this
  have h2 : ‖(2 : ℝ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
  rw [h2]
  nlinarith [norm_nonneg M,
    norm_nonneg (M - Matrix.diagonal s * M * Matrix.diagonal s)]

end Mask

/-! ## The main construction -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **From a dual certificate to a primal witness, on a promise domain.** -/
theorem lt_advPMOn_of_certificate {read : X → ι → σ} {f : X → Bool}
    (hdet : ∀ x y, read x = read y → f x = f y)
    {Γ : Matrix X X ℝ} {p : X → ℝ} {c : ℝ}
    (hsym : ∀ x y, Γ y x = Γ x y) (hp : ∀ x, 0 < p x)
    (hquad : ∀ (i : ι) (s t : X → ℝ),
      |s ⬝ᵥ (Γ ⊙ advDOn read i) *ᵥ t|
        ≤ (∑ x, p x * (s x * s x)) + ∑ y, p y * (t y * t y))
    (hobj : 2 * c * (∑ x, p x) < ∑ x, ∑ y, Γ x y * dualTargetOn f x y) :
    c < advPMOn read f := by
  classical
  have hsum : 0 < ∑ x, p x := by
    rcases isEmpty_or_nonempty X with he | hne
    · exact absurd hobj (by simp)
    · exact Finset.sum_pos (fun x _ => hp x) Finset.univ_nonempty
  set r : X → ℝ := fun x => Real.sqrt (p x) with hr
  have hr0 : ∀ x, 0 < r x := fun x => Real.sqrt_pos.mpr (hp x)
  have hrr : ∀ x, r x * r x = p x := fun x => Real.mul_self_sqrt (hp x).le
  set Γ' : Matrix X X ℝ := Matrix.of fun x y => Γ x y / (r x * r y) with hΓ'
  have hΓ'sym : ∀ x y, Γ' y x = Γ' x y := by
    intro x y
    show Γ y x / (r y * r x) = Γ x y / (r x * r y)
    rw [hsym x y, mul_comm (r y) (r x)]
  have hmask : ∀ (i : ι) (x y : X),
      (Γ' ⊙ advDOn read i) x y = (Γ ⊙ advDOn read i) x y / (r x * r y) := by
    intro i x y
    rw [hadamard_advDOn_apply, hadamard_advDOn_apply]
    by_cases h : read x i = read y i
    · simp [h]
    · simp [h, hΓ']
  have hnorm : ∀ i : ι, ‖Γ' ⊙ advDOn read i‖ ≤ 2 := by
    intro i
    refine l2_opNorm_le_two_of_quadratic _ fun a b => ?_
    have e1 : (fun x => a x / r x) ⬝ᵥ (Γ ⊙ advDOn read i) *ᵥ (fun y => b y / r y)
        = a ⬝ᵥ (Γ' ⊙ advDOn read i) *ᵥ b := by
      simp only [dotProduct_mulVec_eq_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      rw [hmask i x y]
      have hx := (hr0 x).ne'
      have hy := (hr0 y).ne'
      field_simp
    have e2 : ∀ (w : X → ℝ),
        (∑ x, p x * ((w x / r x) * (w x / r x))) = w ⬝ᵥ w := by
      intro w
      rw [dotProduct]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hx := (hr0 x).ne'
      rw [← hrr x]
      field_simp
    have := hquad i (fun x => a x / r x) (fun y => b y / r y)
    rw [e1, e2 a, e2 b] at this
    exact this
  set Γ'' : Matrix X X ℝ := (2 : ℝ)⁻¹ • (Γ' ⊙ dualTargetOn f) with hΓ''
  have hadv : IsAdvMatrixOn f Γ'' := by
    constructor
    · ext x y
      show Γ'' y x = Γ'' x y
      simp only [hΓ'', Matrix.smul_apply, Matrix.hadamard_apply, smul_eq_mul,
        hΓ'sym x y, dualTargetOn_comm f x y]
    · intro x y hxy
      simp [hΓ'', Matrix.hadamard_apply, dualTargetOn, hxy]
  have hfeas : ∀ i : ι, ‖Γ'' ⊙ advDOn read i‖ ≤ 1 := by
    intro i
    have hswap : Γ'' ⊙ advDOn read i
        = (2 : ℝ)⁻¹ • ((Γ' ⊙ advDOn read i) ⊙ dualTargetOn f) := by
      ext x y
      simp only [hΓ'', Matrix.smul_apply, Matrix.hadamard_apply, smul_eq_mul]
      ring
    rw [hswap, norm_smul]
    have h1 : ‖(Γ' ⊙ advDOn read i) ⊙ dualTargetOn f‖ ≤ ‖Γ' ⊙ advDOn read i‖ :=
      l2_opNorm_hadamard_dualTargetOn_le f _
    have h2 : ‖(2 : ℝ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
    rw [h2]
    nlinarith [hnorm i, norm_nonneg ((Γ' ⊙ advDOn read i) ⊙ dualTargetOn f)]
  set R := Real.sqrt (∑ x, p x) with hR
  have hR0 : 0 < R := Real.sqrt_pos.mpr hsum
  have hRR : R * R = ∑ x, p x := Real.mul_self_sqrt hsum.le
  set a : X → ℝ := fun x => r x / R with ha
  have haa : a ⬝ᵥ a = 1 := by
    rw [dotProduct]
    have : ∀ x : X, a x * a x = p x / (R * R) := by
      intro x
      rw [ha]
      simp only []
      rw [div_mul_div_comm, hrr x]
    rw [Finset.sum_congr rfl fun x _ => this x, ← Finset.sum_div, hRR,
      div_self hsum.ne']
  have hval : a ⬝ᵥ Γ'' *ᵥ a
      = (∑ x, ∑ y, Γ x y * dualTargetOn f x y) / (2 * ∑ x, p x) := by
    rw [dotProduct_mulVec_eq_sum, ← hRR]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hx := (hr0 x).ne'
    have hy := (hr0 y).ne'
    have hRne := hR0.ne'
    show (r x / R) * ((2 : ℝ)⁻¹ * (Γ x y / (r x * r y) * dualTargetOn f x y)) *
        (r y / R) = _
    field_simp
  have hlt : c < a ⬝ᵥ Γ'' *ᵥ a := by
    rw [hval, lt_div_iff₀ (by positivity)]
    linarith [hobj]
  have hbound : a ⬝ᵥ Γ'' *ᵥ a ≤ ‖Γ''‖ := by
    have := abs_dotProduct_mulVec_le Γ'' a a
    rw [haa, Real.sqrt_one] at this
    simpa using (le_abs_self _).trans this
  exact lt_of_lt_of_le hlt (hbound.trans (le_advPMOn hdet hadv hfeas))

end QuantumQueryComplexity
