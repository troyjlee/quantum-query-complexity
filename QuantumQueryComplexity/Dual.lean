import QuantumQueryComplexity.Basic
set_option linter.style.header false

/-!
# The dual (minimisation) form of the adversary bound

The dual of the adversary SDP (Lee–Mittal–Reichardt–Špalek–Szegedy; stated as
Theorem 7 of Belovs–Lee, arXiv:2004.06439) asks for two families of vectors
`u x i`, `v x i` indexed by inputs `x` and query positions `i`, satisfying

  `∑_{i : x i ≠ y i} ⟪u x i, v y i⟫ = 1` if `g x ≠ g y`, and `= 0` if `g x = g y`,

with objective `max_x ∑_i ‖u x i‖²` (and the same for `v`).  The constraints
on pairs with `g x = g y` are the extra ones isolated by LMRSS; they are what
makes dual solutions *compose*.

This file defines feasible dual solutions (`DualPair`), the dual value
`advDual` as an infimum of costs, and proves **weak duality**
`advPM g ≤ advDual g` (`advPM_le_advDual`) by the same Gram-plus-Cauchy–Schwarz
argument that underlies the Schur-multiplier bound.

Strong duality (`advDual = advPM`) is *not* proved here: it is genuine SDP
duality, for which mathlib has no infrastructure.  Everything downstream is
stated so that strong duality would be the only missing input — see
`QuantumQueryComplexity/DualCompose.lean`.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {O : Type*} [DecidableEq O]

/-- A feasible solution of the dual program for `g`, with vectors of
dimension `K`.  `DecidableEq σ` is what makes the coordinate mask
`if x i = y i` meaningful, and `DecidableEq O` the output test
`if g x = g y`; no finiteness of `σ` is needed here, since the constraint
never sums over inputs. -/
structure DualPair {ι : Type*} [Fintype ι] {σ : Type*} [DecidableEq σ]
    {O : Type*} [DecidableEq O] (K : Type*) [Fintype K]
    (g : (ι → σ) → O) where
  /-- The first vector family. -/
  u : (ι → σ) → ι → K → ℝ
  /-- The second vector family. -/
  v : (ι → σ) → ι → K → ℝ
  /-- The dual feasibility constraint, including the LMRSS constraints on
  pairs with equal `g`-value. -/
  constraint : ∀ x y : ι → σ,
    (∑ i, if x i = y i then 0 else ∑ k, u x i k * v y i k)
      = if g x = g y then 0 else 1

namespace DualPair

variable {K K' : Type*} [Fintype K] [Fintype K'] {g : (ι → σ) → O}

/-- The cost of a dual solution is bounded by `c`. -/
def IsCostLe (P : DualPair K g) (c : ℝ) : Prop :=
  (∀ x, ∑ i, ∑ k, P.u x i k * P.u x i k ≤ c) ∧
  (∀ x, ∑ i, ∑ k, P.v x i k * P.v x i k ≤ c)

lemma IsCostLe.mono {P : DualPair K g} {c d : ℝ} (h : P.IsCostLe c)
    (hcd : c ≤ d) : P.IsCostLe d :=
  ⟨fun x => (h.1 x).trans hcd, fun x => (h.2 x).trans hcd⟩

lemma isCostLe_nonneg [Nonempty σ] {P : DualPair K g} {c : ℝ}
    (h : P.IsCostLe c) : 0 ≤ c := by
  classical
  obtain ⟨x⟩ : Nonempty (ι → σ) := inferInstance
  refine le_trans ?_ (h.1 x)
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun k _ => mul_self_nonneg _

/-- Transporting a dual solution along a bijection of the dimension type. -/
def reindex (P : DualPair K g) (e : K ≃ K') : DualPair K' g where
  u x i k' := P.u x i (e.symm k')
  v x i k' := P.v x i (e.symm k')
  constraint x y := by
    rw [← P.constraint x y]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : x i = y i
    · rw [if_pos hi, if_pos hi]
    · rw [if_neg hi, if_neg hi]
      exact Fintype.sum_equiv e.symm _ _ fun k' => rfl

lemma reindex_isCostLe {P : DualPair K g} {c : ℝ} (h : P.IsCostLe c)
    (e : K ≃ K') : (P.reindex e).IsCostLe c := by
  constructor
  · intro x
    refine le_trans (le_of_eq ?_) (h.1 x)
    exact Finset.sum_congr rfl fun i _ =>
      Fintype.sum_equiv e.symm _ _ fun k' => rfl
  · intro x
    refine le_trans (le_of_eq ?_) (h.2 x)
    exact Finset.sum_congr rfl fun i _ =>
      Fintype.sum_equiv e.symm _ _ fun k' => rfl

end DualPair

/-! ## Weak duality -/

/-! The two estimates behind weak duality are stated for an arbitrary finite
type `X` of inputs rather than for the cube `ι → σ`.  Nothing in them uses the
product structure — only that the matrices are indexed by inputs — and the extra
generality is what lets `QuantumQueryComplexity/Promise/Defs.lean` reuse them verbatim for a
promise domain. -/

variable {X : Type*} [Fintype X] [DecidableEq X]

lemma sum_reweight_le {K : Type*} [Fintype K]
    (w : X → ℝ) (U : X → ι → K → ℝ) {c : ℝ}
    (h : ∀ x, ∑ i, ∑ k, U x i k * U x i k ≤ c) :
    (∑ p : ι × K, (fun x => w x * U x p.1 p.2) ⬝ᵥ
      (fun x => w x * U x p.1 p.2)) ≤ c * (w ⬝ᵥ w) := by
  have hstep : (∑ p : ι × K, (fun x => w x * U x p.1 p.2) ⬝ᵥ
      (fun x => w x * U x p.1 p.2))
      = ∑ x, (w x * w x) * ∑ i, ∑ k, U x i k * U x i k := by
    calc (∑ p : ι × K, (fun x => w x * U x p.1 p.2) ⬝ᵥ
          (fun x => w x * U x p.1 p.2))
        = ∑ i, ∑ k, ∑ x, (w x * w x) * (U x i k * U x i k) := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
          simp only [dotProduct]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ = ∑ i, ∑ x, ∑ k, (w x * w x) * (U x i k * U x i k) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ x, ∑ i, ∑ k, (w x * w x) * (U x i k * U x i k) := Finset.sum_comm
      _ = ∑ x, (w x * w x) * ∑ i, ∑ k, U x i k * U x i k := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  rw [hstep]
  calc ∑ x, (w x * w x) * ∑ i, ∑ k, U x i k * U x i k
      ≤ ∑ x, (w x * w x) * c :=
        Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (h x) (mul_self_nonneg _)
    _ = c * (w ⬝ᵥ w) := by rw [← Finset.sum_mul, mul_comm]; rfl

/-- The core estimate of weak duality: a sum of bilinear forms of norm at
most one, reweighted by dual vectors of cost at most `c`, is bounded by
`c` times the product of the vector lengths. -/
lemma key_bound {K : Type*} [Fintype K]
    (M : ι → Matrix X X ℝ) (hM : ∀ i, ‖M i‖ ≤ 1)
    (a b : X → ℝ) (U V : X → ι → K → ℝ) {c : ℝ}
    (hc : 0 ≤ c)
    (hU : ∀ x, ∑ i, ∑ k, U x i k * U x i k ≤ c)
    (hV : ∀ x, ∑ i, ∑ k, V x i k * V x i k ≤ c) :
    |∑ p : ι × K, (fun x => a x * U x p.1 p.2) ⬝ᵥ
        M p.1 *ᵥ (fun y => b y * V y p.1 p.2)|
      ≤ c * Real.sqrt (a ⬝ᵥ a) * Real.sqrt (b ⬝ᵥ b) := by
  calc |∑ p : ι × K, (fun x => a x * U x p.1 p.2) ⬝ᵥ
          M p.1 *ᵥ (fun y => b y * V y p.1 p.2)|
      ≤ ∑ p : ι × K, |(fun x => a x * U x p.1 p.2) ⬝ᵥ
          M p.1 *ᵥ (fun y => b y * V y p.1 p.2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : ι × K,
          Real.sqrt ((fun x => a x * U x p.1 p.2) ⬝ᵥ
            (fun x => a x * U x p.1 p.2)) *
          Real.sqrt ((fun y => b y * V y p.1 p.2) ⬝ᵥ
            (fun y => b y * V y p.1 p.2)) := by
        refine Finset.sum_le_sum fun p _ => ?_
        refine (abs_dotProduct_mulVec_le _ _ _).trans ?_
        have h1 : ‖M p.1‖ * Real.sqrt ((fun x => a x * U x p.1 p.2) ⬝ᵥ
              (fun x => a x * U x p.1 p.2))
            ≤ 1 * Real.sqrt ((fun x => a x * U x p.1 p.2) ⬝ᵥ
              (fun x => a x * U x p.1 p.2)) :=
          mul_le_mul_of_nonneg_right (hM p.1) (Real.sqrt_nonneg _)
        calc ‖M p.1‖ * Real.sqrt ((fun x => a x * U x p.1 p.2) ⬝ᵥ
              (fun x => a x * U x p.1 p.2)) *
              Real.sqrt ((fun y => b y * V y p.1 p.2) ⬝ᵥ
                (fun y => b y * V y p.1 p.2))
            ≤ 1 * Real.sqrt ((fun x => a x * U x p.1 p.2) ⬝ᵥ
                (fun x => a x * U x p.1 p.2)) *
              Real.sqrt ((fun y => b y * V y p.1 p.2) ⬝ᵥ
                (fun y => b y * V y p.1 p.2)) :=
              mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
          _ = _ := by ring
    _ ≤ Real.sqrt (∑ p : ι × K, (fun x => a x * U x p.1 p.2) ⬝ᵥ
            (fun x => a x * U x p.1 p.2)) *
          Real.sqrt (∑ p : ι × K, (fun y => b y * V y p.1 p.2) ⬝ᵥ
            (fun y => b y * V y p.1 p.2)) := by
        have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun p : ι × K => Real.sqrt ((fun x => a x * U x p.1 p.2) ⬝ᵥ
            (fun x => a x * U x p.1 p.2)))
          (fun p : ι × K => Real.sqrt ((fun y => b y * V y p.1 p.2) ⬝ᵥ
            (fun y => b y * V y p.1 p.2)))
        simpa [Real.sq_sqrt (dotProduct_self_nonneg _)] using hcs
    _ ≤ Real.sqrt (c * (a ⬝ᵥ a)) * Real.sqrt (c * (b ⬝ᵥ b)) :=
        mul_le_mul (Real.sqrt_le_sqrt (sum_reweight_le a U hU))
          (Real.sqrt_le_sqrt (sum_reweight_le b V hV))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = c * Real.sqrt (a ⬝ᵥ a) * Real.sqrt (b ⬝ᵥ b) := by
        rw [Real.sqrt_mul hc, Real.sqrt_mul hc]
        rw [show Real.sqrt c * Real.sqrt (a ⬝ᵥ a) *
            (Real.sqrt c * Real.sqrt (b ⬝ᵥ b))
            = Real.sqrt c * Real.sqrt c *
              (Real.sqrt (a ⬝ᵥ a) * Real.sqrt (b ⬝ᵥ b)) from by ring,
          Real.mul_self_sqrt hc]
        ring

set_option maxHeartbeats 800000 in
/-- **Weak duality**: every feasible dual solution of cost at most `c` bounds
the adversary bound by `c`. -/
theorem advPM_le_of_dualPair {K : Type*} [Fintype K] {g : (ι → σ) → O}
    (P : DualPair K g) {c : ℝ} (hc : 0 ≤ c) (hP : P.IsCostLe c) :
    advPM g ≤ c := by
  refine advPM_le fun Γ hΓ hΓD => ?_
  refine l2_opNorm_le_of_forall_dotProduct Γ hc fun a b => ?_
  have hsplit : ∀ x y, a x * Γ x y * b y
      = ∑ p : ι × K, (a x * P.u x p.1 p.2) * (Γ ⊙ advD p.1) x y *
          (b y * P.v y p.1 p.2) := by
    intro x y
    rw [Fintype.sum_prod_type]
    show a x * Γ x y * b y
      = ∑ i, ∑ k, (a x * P.u x i k) * (Γ ⊙ advD i) x y * (b y * P.v y i k)
    have hstep : ∀ i : ι,
        (∑ k, (a x * P.u x i k) * (Γ ⊙ advD i) x y * (b y * P.v y i k))
        = (a x * b y * Γ x y) *
            (if x i = y i then 0 else ∑ k, P.u x i k * P.v y i k) := by
      intro i
      by_cases hi : x i = y i
      · rw [if_pos hi, mul_zero]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hadamard_advD_apply, if_pos hi]
        ring
      · rw [if_neg hi, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hadamard_advD_apply, if_neg hi]
        ring
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i,
      ← Finset.mul_sum, P.constraint x y]
    by_cases hg : g x = g y
    · rw [if_pos hg, hΓ.apply_eq_zero hg]
      ring
    · rw [if_neg hg]
      ring
  have hexpand : a ⬝ᵥ Γ *ᵥ b
      = ∑ p : ι × K, (fun x => a x * P.u x p.1 p.2) ⬝ᵥ
          (fun i => Γ ⊙ advD i) p.1 *ᵥ (fun y => b y * P.v y p.1 p.2) := by
    rw [dotProduct_mulVec_eq_sum]
    have hrhs : (∑ p : ι × K, (fun x => a x * P.u x p.1 p.2) ⬝ᵥ
        (fun i => Γ ⊙ advD i) p.1 *ᵥ (fun y => b y * P.v y p.1 p.2))
        = ∑ p : ι × K, ∑ x, ∑ y, (a x * P.u x p.1 p.2) *
            (Γ ⊙ advD p.1) x y * (b y * P.v y p.1 p.2) :=
      Finset.sum_congr rfl fun p _ => dotProduct_mulVec_eq_sum _ _ _
    rw [hrhs]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => hsplit x y
  rw [hexpand]
  exact key_bound (fun i => Γ ⊙ advD i) hΓD a b P.u P.v hc hP.1 hP.2

/-! ## A feasible dual solution always exists -/

/-- The number of coordinates on which two inputs differ. -/
def diffCard (x y : ι → Bool) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ y i).card

lemma diffCard_ne_zero {x y : ι → Bool} (h : x ≠ y) : diffCard x y ≠ 0 := by
  rw [diffCard, Finset.card_ne_zero]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  exact ⟨i, by simp [hi]⟩

lemma sum_ite_diff_const (x y : ι → Bool) (C : ℝ) :
    (∑ i, if x i = y i then 0 else C) = (diffCard x y : ℝ) * C := by
  rw [show (∑ i, if x i = y i then (0:ℝ) else C)
      = ∑ i, if x i ≠ y i then C else 0 from
    Finset.sum_congr rfl fun i _ => by by_cases hi : x i = y i <;> simp [hi]]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rfl

/-- A dual solution of finite (very lossy) cost, showing the dual program is
always feasible: `u x i` is the standard basis vector of `x`, and the mass of
`v y i` is spread over the coordinates where the inputs differ. -/
noncomputable def trivialDual (g : (ι → Bool) → Bool) :
    DualPair (ι → Bool) g where
  u x _ k := if k = x then 1 else 0
  v y i k := if g k = g y then 0
    else (if k i = y i then 0 else (diffCard k y : ℝ)⁻¹)
  constraint x y := by
    by_cases hg : g x = g y
    · rw [if_pos hg]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : x i = y i
      · rw [if_pos hi]
      · rw [if_neg hi]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : k = x
        · subst hk
          simp [hg]
        · simp [hk]
    · rw [if_neg hg]
      have hxy : x ≠ y := fun h => hg (by rw [h])
      trans (∑ i : ι, if x i = y i then (0:ℝ) else (diffCard x y : ℝ)⁻¹)
      · refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : x i = y i
        · rw [if_pos hi, if_pos hi]
        · rw [if_neg hi, if_neg hi]
          rw [Finset.sum_eq_single x]
          · simp [hg, hi]
          · intro k _ hk
            simp [hk]
          · intro h
            exact absurd (Finset.mem_univ _) h
      · rw [sum_ite_diff_const]
        exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (diffCard_ne_zero hxy))

lemma trivialDual_isCostLe (g : (ι → Bool) → Bool) :
    (trivialDual g).IsCostLe
      ((Fintype.card ι : ℝ) + (Fintype.card (ι → Bool) : ℝ)) := by
  constructor
  · intro x
    show (∑ i : ι, ∑ k : ι → Bool,
      (if k = x then (1:ℝ) else 0) * (if k = x then (1:ℝ) else 0)) ≤ _
    have hk : ∀ i : ι, (∑ k : ι → Bool, (if k = x then (1:ℝ) else 0) *
        (if k = x then (1:ℝ) else 0)) = 1 := by
      intro i
      rw [Finset.sum_eq_single x]
      · norm_num
      · intro k _ hk
        rw [if_neg hk]
        ring
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hk i,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have := Nat.cast_nonneg (α := ℝ) (Fintype.card (ι → Bool))
    linarith
  · intro y
    show (∑ i : ι, ∑ k : ι → Bool,
      (if g k = g y then (0:ℝ) else if k i = y i then 0
        else (diffCard k y : ℝ)⁻¹) *
      (if g k = g y then (0:ℝ) else if k i = y i then 0
        else (diffCard k y : ℝ)⁻¹)) ≤ _
    rw [Finset.sum_comm]
    have hbound : ∀ k : ι → Bool,
        (∑ i : ι, (if g k = g y then (0:ℝ) else if k i = y i then 0
            else (diffCard k y : ℝ)⁻¹) *
          (if g k = g y then (0:ℝ) else if k i = y i then 0
            else (diffCard k y : ℝ)⁻¹)) ≤ 1 := by
      intro k
      by_cases hgk : g k = g y
      · simp [hgk]
      · have hky : k ≠ y := fun h => hgk (by rw [h])
        have hN : (diffCard k y : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (diffCard_ne_zero hky)
        have hN1 : (1:ℝ) ≤ (diffCard k y : ℝ) := by
          have h1 := Nat.one_le_iff_ne_zero.mpr (diffCard_ne_zero hky)
          exact_mod_cast h1
        trans (∑ i : ι, if k i = y i then (0:ℝ)
            else (diffCard k y : ℝ)⁻¹ * (diffCard k y : ℝ)⁻¹)
        · refine le_of_eq (Finset.sum_congr rfl fun i _ => ?_)
          by_cases hi : k i = y i <;> simp [hi, hgk]
        · rw [sum_ite_diff_const, ← mul_assoc, mul_inv_cancel₀ hN, one_mul]
          exact inv_le_one_of_one_le₀ hN1
    calc (∑ k : ι → Bool, ∑ i : ι,
          (if g k = g y then (0:ℝ) else if k i = y i then 0
            else (diffCard k y : ℝ)⁻¹) *
          (if g k = g y then (0:ℝ) else if k i = y i then 0
            else (diffCard k y : ℝ)⁻¹))
        ≤ ∑ _k : ι → Bool, (1:ℝ) := Finset.sum_le_sum fun k _ => hbound k
      _ = (Fintype.card (ι → Bool) : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      _ ≤ (Fintype.card ι : ℝ) + (Fintype.card (ι → Bool) : ℝ) := by
          have := Nat.cast_nonneg (α := ℝ) (Fintype.card ι)
          linarith

/-! ## The dual value -/

/-- The set of achievable dual costs (with dimensions normalised to `Fin n`). -/
def dualCosts (g : (ι → Bool) → Bool) : Set ℝ :=
  {c : ℝ | 0 ≤ c ∧ ∃ (n : ℕ) (P : DualPair (Fin n) g), P.IsCostLe c}

/-- The value of the dual program. -/
noncomputable def advDual (g : (ι → Bool) → Bool) : ℝ := sInf (dualCosts g)

lemma dualCosts_nonempty (g : (ι → Bool) → Bool) : (dualCosts g).Nonempty := by
  classical
  refine ⟨(Fintype.card ι : ℝ) + (Fintype.card (ι → Bool) : ℝ), ?_, ?_⟩
  · positivity
  · exact ⟨Fintype.card (ι → Bool),
      (trivialDual g).reindex (Fintype.equivFin _),
      DualPair.reindex_isCostLe (trivialDual_isCostLe g) _⟩

lemma bddBelow_dualCosts (g : (ι → Bool) → Bool) : BddBelow (dualCosts g) :=
  ⟨0, fun c hc => hc.1⟩

theorem advDual_nonneg (g : (ι → Bool) → Bool) : 0 ≤ advDual g :=
  le_csInf (dualCosts_nonempty g) fun c hc => hc.1

/-- Any feasible dual solution bounds the dual value. -/
theorem advDual_le_of_dualPair {K : Type*} [Fintype K]
    {g : (ι → Bool) → Bool} (P : DualPair K g) {c : ℝ} (hc : 0 ≤ c)
    (hP : P.IsCostLe c) : advDual g ≤ c := by
  classical
  refine csInf_le (bddBelow_dualCosts g) ⟨hc, Fintype.card K,
    P.reindex (Fintype.equivFin _), DualPair.reindex_isCostLe hP _⟩

/-- **Weak duality.** -/
theorem advPM_le_advDual (g : (ι → Bool) → Bool) : advPM g ≤ advDual g := by
  refine le_csInf (dualCosts_nonempty g) ?_
  rintro c ⟨hc, n, P, hP⟩
  exact advPM_le_of_dualPair P hc hP

/-- Any value above the dual optimum is achieved by some feasible dual
solution. -/
theorem exists_dualPair_of_lt {g : (ι → Bool) → Bool} {c : ℝ}
    (h : advDual g < c) :
    ∃ (n : ℕ) (P : DualPair (Fin n) g), P.IsCostLe c := by
  obtain ⟨a, ha, hac⟩ := exists_lt_of_csInf_lt (dualCosts_nonempty g) h
  obtain ⟨-, n, P, hP⟩ := ha
  exact ⟨n, P, hP.mono hac.le⟩

end QuantumQueryComplexity
