import QuantumQueryComplexity.Duality.Gram
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# From a positive semidefinite certificate to an adversary matrix

This file contains the elementary half of strong duality: the construction that
turns the multipliers produced by a separating hyperplane back into a feasible
*primal* witness.

The data is a symmetric matrix `Γ`, a strictly positive weight `p` on inputs,
and the inequality

  `|s ⬝ᵥ (Γ ⊙ advD i) *ᵥ t| ≤ ∑ₓ p x · s x ² + ∑ᵧ p y · t y ²`  (for every `i`),

which says exactly that the block matrix `[[diag p, (Γ ⊙ advD i)/2], [·, diag p]]`
is positive semidefinite.  Rescaling by `√p` on both sides turns it into the
adversary feasibility constraint: `Γ' x y = Γ x y / (√(p x) √(p y))` satisfies
`‖Γ' ⊙ advD i‖ ≤ 2`.  Masking off the pairs with equal `g`-value costs nothing
in norm (`l2_opNorm_hadamard_dualTarget_le`, using that a two-valued mask is an
average of the identity and a `±1` diagonal conjugation), and evaluating the
resulting adversary matrix on the unit vector `√p / ‖√p‖` returns the pairing
`⟪Γ, dualTarget g⟫ / (2 ∑ p)`.

Main result: `lt_advPM_of_certificate`.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-! ## Two auxiliary norm bounds -/

section OpNorm

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A bilinear form dominated by the sum of the squared lengths of its
arguments comes from a matrix of norm at most `2`.  (Optimising the scaling
`a ↦ λ a`, `b ↦ λ⁻¹ b` is what turns the arithmetic mean into the geometric
one.) -/
lemma l2_opNorm_le_two_of_quadratic (M : Matrix n n ℝ)
    (h : ∀ a b : n → ℝ, |a ⬝ᵥ M *ᵥ b| ≤ a ⬝ᵥ a + b ⬝ᵥ b) : ‖M‖ ≤ 2 := by
  refine l2_opNorm_le_of_forall_dotProduct M (by norm_num) fun a b => ?_
  have hA0 : (0 : ℝ) ≤ a ⬝ᵥ a := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hB0 : (0 : ℝ) ≤ b ⬝ᵥ b := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  rcases eq_or_ne b 0 with rfl | hb0
  · simp
  have hA1 : 0 < Real.sqrt (a ⬝ᵥ a) :=
    Real.sqrt_pos.mpr (lt_of_le_of_ne hA0 fun h =>
      ha0 (dotProduct_self_eq_zero.mp h.symm))
  have hB1 : 0 < Real.sqrt (b ⬝ᵥ b) :=
    Real.sqrt_pos.mpr (lt_of_le_of_ne hB0 fun h =>
      hb0 (dotProduct_self_eq_zero.mp h.symm))
  set A := Real.sqrt (a ⬝ᵥ a) with hA
  set B := Real.sqrt (b ⬝ᵥ b) with hB
  -- both lengths are positive: optimise the scaling
  set lam := Real.sqrt (B / A) with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.mpr (div_pos hB1 hA1)
  have hlamsq : lam ^ 2 = B / A := Real.sq_sqrt (le_of_lt (div_pos hB1 hA1))
  have hAsq : A ^ 2 = a ⬝ᵥ a := Real.sq_sqrt hA0
  have hBsq : B ^ 2 = b ⬝ᵥ b := Real.sq_sqrt hB0
  have key := h (fun x => lam * a x) (fun y => lam⁻¹ * b y)
  have e1 : ((fun x => lam * a x) : n → ℝ) ⬝ᵥ M *ᵥ (fun y => lam⁻¹ * b y)
      = a ⬝ᵥ M *ᵥ b := by
    simp only [dotProduct_mulVec_eq_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    field_simp
  have e2 : ((fun x => lam * a x) : n → ℝ) ⬝ᵥ (fun x => lam * a x)
      = lam ^ 2 * (a ⬝ᵥ a) := by
    simp only [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have e3 : ((fun y => lam⁻¹ * b y) : n → ℝ) ⬝ᵥ (fun y => lam⁻¹ * b y)
      = (lam ^ 2)⁻¹ * (b ⬝ᵥ b) := by
    simp only [dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    field_simp
  rw [e1, e2, e3, ← hAsq, ← hBsq, hlamsq] at key
  have hArg : (B / A) * A ^ 2 + (B / A)⁻¹ * B ^ 2 = 2 * A * B := by
    field_simp
    ring
  rw [hArg] at key
  exact key

end OpNorm

section Mask

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The `±1` sign vector of a Boolean function. -/
def boolSign (g : (ι → σ) → Bool) : (ι → σ) → ℝ := fun x => if g x then 1 else -1

lemma boolSign_eq_one_or (g : (ι → σ) → Bool) (x : ι → σ) :
    boolSign g x = 1 ∨ boolSign g x = -1 := by
  by_cases h : g x = true <;> simp [boolSign, h]

lemma boolSign_mul (g : (ι → σ) → Bool) (x y : ι → σ) :
    boolSign g x * boolSign g y = 1 - 2 * dualTarget g x y := by
  rcases Bool.eq_false_or_eq_true (g x) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (g y) with h2 | h2 <;>
      simp [boolSign, dualTarget, h1, h2] <;> norm_num

/-- Masking off the pairs of inputs with equal `g`-value does not increase the
spectral norm: for a two-valued `g` the mask is the average of the identity and
conjugation by a `±1` diagonal matrix. -/
lemma l2_opNorm_hadamard_dualTarget_le (g : (ι → σ) → Bool)
    (M : Matrix (ι → σ) (ι → σ) ℝ) : ‖M ⊙ dualTarget g‖ ≤ ‖M‖ := by
  set s := boolSign g with hs
  have hsplit : M ⊙ dualTarget g
      = (2 : ℝ)⁻¹ • (M - Matrix.diagonal s * M * Matrix.diagonal s) := by
    ext x y
    have hmul : (Matrix.diagonal s * M * Matrix.diagonal s) x y
        = s x * M x y * s y := by
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    have hsxy : s x * s y = 1 - 2 * dualTarget g x y := boolSign_mul g x y
    rw [Matrix.hadamard_apply, Matrix.smul_apply, Matrix.sub_apply, hmul,
      smul_eq_mul]
    have : s x * M x y * s y = M x y * (s x * s y) := by ring
    rw [this, hsxy]
    ring
  rw [hsplit, norm_smul]
  have hconj : ‖Matrix.diagonal s * M * Matrix.diagonal s‖ = ‖M‖ :=
    l2_opNorm_conj_diagonal_sign (boolSign_eq_one_or g) M
  have := norm_sub_le M (Matrix.diagonal s * M * Matrix.diagonal s)
  rw [hconj] at this
  have h2 : ‖(2 : ℝ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
  rw [h2]
  nlinarith [norm_nonneg M, norm_nonneg (M - Matrix.diagonal s * M * Matrix.diagonal s)]

end Mask

/-! ## The main construction -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- **From a dual certificate to a primal witness.**  If `Γ` is symmetric, `p`
is a strictly positive weight, the bilinear forms `Γ ⊙ advD i` are dominated by
the quadratic form of `p` on both sides, and the pairing of `Γ` with
`dualTarget g` exceeds `2 c ∑ p`, then `advPM g` exceeds `c`. -/
theorem lt_advPM_of_certificate {g : (ι → σ) → Bool}
    {Γ : Matrix (ι → σ) (ι → σ) ℝ} {p : (ι → σ) → ℝ} {c : ℝ}
    (hsym : ∀ x y, Γ y x = Γ x y) (hp : ∀ x, 0 < p x)
    (hquad : ∀ (i : ι) (s t : (ι → σ) → ℝ),
      |s ⬝ᵥ (Γ ⊙ advD i) *ᵥ t|
        ≤ (∑ x, p x * (s x * s x)) + ∑ y, p y * (t y * t y))
    (hobj : 2 * c * (∑ x, p x) < ∑ x, ∑ y, Γ x y * dualTarget g x y) :
    c < advPM g := by
  classical
  -- the total weight is positive
  have hsum : 0 < ∑ x, p x := by
    rcases isEmpty_or_nonempty (ι → σ) with he | hne
    · exact absurd hobj (by simp)
    · exact Finset.sum_pos (fun x _ => hp x) Finset.univ_nonempty
  set r : (ι → σ) → ℝ := fun x => Real.sqrt (p x) with hr
  have hr0 : ∀ x, 0 < r x := fun x => Real.sqrt_pos.mpr (hp x)
  have hrr : ∀ x, r x * r x = p x := fun x => Real.mul_self_sqrt (hp x).le
  -- the rescaled matrix
  set Γ' : Matrix (ι → σ) (ι → σ) ℝ :=
    Matrix.of fun x y => Γ x y / (r x * r y) with hΓ'
  have hΓ'sym : ∀ x y, Γ' y x = Γ' x y := by
    intro x y
    show Γ y x / (r y * r x) = Γ x y / (r x * r y)
    rw [hsym x y, mul_comm (r y) (r x)]
  -- masked norms of the rescaled matrix
  have hmask : ∀ (i : ι) (x y : ι → σ),
      (Γ' ⊙ advD i) x y = (Γ ⊙ advD i) x y / (r x * r y) := by
    intro i x y
    rw [hadamard_advD_apply, hadamard_advD_apply]
    by_cases h : x i = y i
    · simp [h]
    · simp [h, hΓ']
  have hnorm : ∀ i : ι, ‖Γ' ⊙ advD i‖ ≤ 2 := by
    intro i
    refine l2_opNorm_le_two_of_quadratic _ fun a b => ?_
    have e1 : (fun x => a x / r x) ⬝ᵥ (Γ ⊙ advD i) *ᵥ (fun y => b y / r y)
        = a ⬝ᵥ (Γ' ⊙ advD i) *ᵥ b := by
      simp only [dotProduct_mulVec_eq_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      rw [hmask i x y]
      have hx := (hr0 x).ne'
      have hy := (hr0 y).ne'
      field_simp
    have e2 : ∀ (w : (ι → σ) → ℝ),
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
  -- the adversary matrix
  set Γ'' : Matrix (ι → σ) (ι → σ) ℝ := (2 : ℝ)⁻¹ • (Γ' ⊙ dualTarget g) with hΓ''
  have hadv : IsAdvMatrix g Γ'' := by
    constructor
    · ext x y
      show Γ'' y x = Γ'' x y
      simp only [hΓ'', Matrix.smul_apply, Matrix.hadamard_apply, smul_eq_mul,
        hΓ'sym x y, dualTarget_comm g x y]
    · intro x y hxy
      simp [hΓ'', Matrix.hadamard_apply, dualTarget, hxy]
  have hfeas : ∀ i : ι, ‖Γ'' ⊙ advD i‖ ≤ 1 := by
    intro i
    have hswap : Γ'' ⊙ advD i = (2 : ℝ)⁻¹ • ((Γ' ⊙ advD i) ⊙ dualTarget g) := by
      ext x y
      simp only [hΓ'', Matrix.smul_apply, Matrix.hadamard_apply, smul_eq_mul]
      ring
    rw [hswap, norm_smul]
    have h1 : ‖(Γ' ⊙ advD i) ⊙ dualTarget g‖ ≤ ‖Γ' ⊙ advD i‖ :=
      l2_opNorm_hadamard_dualTarget_le g _
    have h2 : ‖(2 : ℝ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
    rw [h2]
    nlinarith [hnorm i, norm_nonneg ((Γ' ⊙ advD i) ⊙ dualTarget g)]
  -- evaluate on the unit vector √p / ‖√p‖
  set R := Real.sqrt (∑ x, p x) with hR
  have hR0 : 0 < R := Real.sqrt_pos.mpr hsum
  have hRR : R * R = ∑ x, p x := Real.mul_self_sqrt hsum.le
  set a : (ι → σ) → ℝ := fun x => r x / R with ha
  have haa : a ⬝ᵥ a = 1 := by
    rw [dotProduct]
    have : ∀ x : ι → σ, a x * a x = p x / (R * R) := by
      intro x
      rw [ha]
      simp only []
      rw [div_mul_div_comm, hrr x]
    rw [Finset.sum_congr rfl fun x _ => this x, ← Finset.sum_div, hRR,
      div_self hsum.ne']
  have hval : a ⬝ᵥ Γ'' *ᵥ a
      = (∑ x, ∑ y, Γ x y * dualTarget g x y) / (2 * ∑ x, p x) := by
    rw [dotProduct_mulVec_eq_sum, ← hRR]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hx := (hr0 x).ne'
    have hy := (hr0 y).ne'
    have hRne := hR0.ne'
    show (r x / R) * ((2 : ℝ)⁻¹ * (Γ x y / (r x * r y) * dualTarget g x y)) *
        (r y / R) = _
    field_simp
  -- conclude
  have hlt : c < a ⬝ᵥ Γ'' *ᵥ a := by
    rw [hval, lt_div_iff₀ (by positivity)]
    linarith [hobj]
  have hbound : a ⬝ᵥ Γ'' *ᵥ a ≤ ‖Γ''‖ := by
    have := abs_dotProduct_mulVec_le Γ'' a a
    rw [haa, Real.sqrt_one] at this
    simpa using (le_abs_self _).trans this
  exact lt_of_lt_of_le hlt (hbound.trans (le_advPM hadv hfeas))

end QuantumQueryComplexity
