import QuantumQueryComplexity.WeightedDual
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Averaging dual solutions

The dual constraint is **linear** in `⟨u x i, v y i⟩`, so a convex combination
of solutions for the *same* function is again a solution: scale the `z`-th by
`√(p z)` and take an orthogonal direct sum, and the pairing averages copies of
the same number `[f x ≠ f y]`.

What makes this worth doing is the cost.  The averaged solution costs

  `∑ z, p z · (cost of the z-th solution at that input)`

*per input* — an average of costs, not a cost of averages.  A family of
solutions that is individually bad but good on average is therefore fine, which
is exactly the situation for maximum finding: for a fixed scan order an
increasing input sets a record at every step, but over a uniformly random order
the probability of a record at step `t` is only `1/t`.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [DecidableEq σ]
variable {O : Type*} [DecidableEq O]
variable {Z K : Type*} [Fintype Z] [Fintype K]
variable {f : (ι → σ) → O}

namespace DualPair

/-- **A convex combination of dual solutions for the same function.** -/
noncomputable def average (P : Z → DualPair K f) (p : Z → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∑ z, p z = 1) : DualPair (Z × K) f where
  u x i := fun zk => Real.sqrt (p zk.1) * (P zk.1).u x i zk.2
  v y i := fun zk => Real.sqrt (p zk.1) * (P zk.1).v y i zk.2
  constraint x y := by
    have hpt : ∀ i : ι,
        (∑ zk : Z × K, (Real.sqrt (p zk.1) * (P zk.1).u x i zk.2) *
          (Real.sqrt (p zk.1) * (P zk.1).v y i zk.2))
        = ∑ z : Z, p z * ∑ k : K, (P z).u x i k * (P z).v y i k := by
      intro i
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show (Real.sqrt (p z) * (P z).u x i k) * (Real.sqrt (p z) * (P z).v y i k)
          = (Real.sqrt (p z) * Real.sqrt (p z))
            * ((P z).u x i k * (P z).v y i k) from by ring,
        Real.mul_self_sqrt (hp0 z)]
    have hmask : ∀ i : ι,
        (if x i = y i then (0 : ℝ)
          else ∑ z : Z, p z * ∑ k : K, (P z).u x i k * (P z).v y i k)
        = ∑ z : Z, p z * (if x i = y i then (0 : ℝ)
            else ∑ k : K, (P z).u x i k * (P z).v y i k) := by
      intro i
      by_cases h : x i = y i
      · rw [if_pos h]
        exact (Finset.sum_eq_zero fun z _ => by rw [if_pos h, mul_zero]).symm
      · rw [if_neg h]
        exact Finset.sum_congr rfl fun z _ => by rw [if_neg h]
    simp only [hpt, hmask]
    rw [Finset.sum_comm]
    have hz : ∀ z : Z, (∑ i : ι, p z * (if x i = y i then (0 : ℝ)
        else ∑ k : K, (P z).u x i k * (P z).v y i k))
        = p z * (if f x = f y then 0 else 1) := by
      intro z
      rw [← Finset.mul_sum, (P z).constraint x y]
    rw [Finset.sum_congr rfl fun z (_ : z ∈ Finset.univ) => hz z, ← Finset.sum_mul,
      hp1, one_mul]

/-- The averaged squared mass at one coordinate is the average of the squared
masses there.  Stated per coordinate so that a *weighted* cost, which inserts a
different factor at each one, can use it too. -/
private lemma sum_average_sq_coord (p : Z → ℝ) (hp0 : ∀ z, 0 ≤ p z)
    (U : Z → (ι → σ) → ι → K → ℝ) (x : ι → σ) (i : ι) :
    (∑ zk : Z × K, (Real.sqrt (p zk.1) * U zk.1 x i zk.2)
        * (Real.sqrt (p zk.1) * U zk.1 x i zk.2))
      = ∑ z : Z, p z * ∑ k : K, U z x i k * U z x i k := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (Real.sqrt (p z) * U z x i k) * (Real.sqrt (p z) * U z x i k)
      = (Real.sqrt (p z) * Real.sqrt (p z)) * (U z x i k * U z x i k) from by ring,
    Real.mul_self_sqrt (hp0 z)]

lemma sum_average_sq (P : Z → DualPair K f) (p : Z → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (U : Z → (ι → σ) → ι → K → ℝ) (x : ι → σ) :
    (∑ i : ι, ∑ zk : Z × K, (Real.sqrt (p zk.1) * U zk.1 x i zk.2)
        * (Real.sqrt (p zk.1) * U zk.1 x i zk.2))
      = ∑ z : Z, p z * ∑ i : ι, ∑ k : K, U z x i k * U z x i k := by
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
    sum_average_sq_coord p hp0 U x i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun z _ => (Finset.mul_sum _ _ _).symm

private lemma sum_average_sq_weighted (p : Z → ℝ) (hp0 : ∀ z, 0 ≤ p z)
    (U : Z → (ι → σ) → ι → K → ℝ) (c : ι → ℝ) (x : ι → σ) :
    (∑ i : ι, c i * ∑ zk : Z × K, (Real.sqrt (p zk.1) * U zk.1 x i zk.2)
        * (Real.sqrt (p zk.1) * U zk.1 x i zk.2))
      = ∑ z : Z, p z * ∑ i : ι, c i * ∑ k : K, U z x i k * U z x i k := by
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by
      rw [sum_average_sq_coord p hp0 U x i, Finset.mul_sum],
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The averaged cost is the average of the costs, input by input.** -/
theorem average_isCostLe (P : Z → DualPair K f) (p : Z → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∑ z, p z = 1) {c : ℝ}
    (hu : ∀ x : ι → σ,
      (∑ z : Z, p z * ∑ i : ι, ∑ k : K, (P z).u x i k * (P z).u x i k) ≤ c)
    (hv : ∀ y : ι → σ,
      (∑ z : Z, p z * ∑ i : ι, ∑ k : K, (P z).v y i k * (P z).v y i k) ≤ c) :
    (average P p hp0 hp1).IsCostLe c := by
  constructor
  · intro x
    exact le_trans (le_of_eq (sum_average_sq P p hp0 (fun z => (P z).u) x)) (hu x)
  · intro y
    exact le_trans (le_of_eq (sum_average_sq P p hp0 (fun z => (P z).v) y)) (hv y)

/-- **The averaged weighted cost is the average of the weighted costs.** -/
theorem average_isWeightedCostLe (P : Z → DualPair K f) (p : Z → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∑ z, p z = 1) {c : ι → ℝ} {V : ℝ}
    (hu : ∀ x : ι → σ, (∑ z : Z, p z *
      ∑ i : ι, c i * ∑ k : K, (P z).u x i k * (P z).u x i k) ≤ V)
    (hv : ∀ y : ι → σ, (∑ z : Z, p z *
      ∑ i : ι, c i * ∑ k : K, (P z).v y i k * (P z).v y i k) ≤ V) :
    (average P p hp0 hp1).IsWeightedCostLe c V := by
  constructor
  · intro x
    exact le_trans (le_of_eq
      (sum_average_sq_weighted p hp0 (fun z => (P z).u) c x)) (hu x)
  · intro y
    exact le_trans (le_of_eq
      (sum_average_sq_weighted p hp0 (fun z => (P z).v) c y)) (hv y)

/-- The uniform average over a nonempty finite family. -/
noncomputable def averageUnif [Nonempty Z] (P : Z → DualPair K f) :
    DualPair (Z × K) f :=
  average P (fun _ => (Fintype.card Z : ℝ)⁻¹)
    (fun _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero))

/-- **The averaged `ℓ²` mass at a single input.**  Exposing this, rather than
only the cost bound it implies, is what lets a dual solution be restricted to a
*promise* domain: its cost there is the maximum of these over the promise
only. -/
theorem sum_averageUnif_u_sq [Nonempty Z] (P : Z → DualPair K f) (x : ι → σ) :
    (∑ i : ι, ∑ zk : Z × K, (averageUnif P).u x i zk * (averageUnif P).u x i zk)
      = (Fintype.card Z : ℝ)⁻¹
        * ∑ z : Z, ∑ i : ι, ∑ k : K, (P z).u x i k * (P z).u x i k := by
  have h := sum_average_sq P (fun _ => (Fintype.card Z : ℝ)⁻¹)
    (fun _ => by positivity) (fun z => (P z).u) x
  rw [← Finset.mul_sum] at h
  exact h

theorem sum_averageUnif_v_sq [Nonempty Z] (P : Z → DualPair K f) (y : ι → σ) :
    (∑ i : ι, ∑ zk : Z × K, (averageUnif P).v y i zk * (averageUnif P).v y i zk)
      = (Fintype.card Z : ℝ)⁻¹
        * ∑ z : Z, ∑ i : ι, ∑ k : K, (P z).v y i k * (P z).v y i k := by
  have h := sum_average_sq P (fun _ => (Fintype.card Z : ℝ)⁻¹)
    (fun _ => by positivity) (fun z => (P z).v) y
  rw [← Finset.mul_sum] at h
  exact h

theorem averageUnif_isWeightedCostLe [Nonempty Z] (P : Z → DualPair K f)
    {c : ι → ℝ} {V : ℝ}
    (hu : ∀ x : ι → σ, (Fintype.card Z : ℝ)⁻¹ *
      ∑ z : Z, (∑ i : ι, c i * ∑ k : K, (P z).u x i k * (P z).u x i k) ≤ V)
    (hv : ∀ y : ι → σ, (Fintype.card Z : ℝ)⁻¹ *
      ∑ z : Z, (∑ i : ι, c i * ∑ k : K, (P z).v y i k * (P z).v y i k) ≤ V) :
    (averageUnif P).IsWeightedCostLe c V := by
  refine average_isWeightedCostLe P _ _ _ (fun x => ?_) (fun y => ?_)
  · rw [← Finset.mul_sum]
    exact hu x
  · rw [← Finset.mul_sum]
    exact hv y

theorem averageUnif_isCostLe [Nonempty Z] (P : Z → DualPair K f) {c : ℝ}
    (hu : ∀ x : ι → σ, (Fintype.card Z : ℝ)⁻¹ *
      ∑ z : Z, (∑ i : ι, ∑ k : K, (P z).u x i k * (P z).u x i k) ≤ c)
    (hv : ∀ y : ι → σ, (Fintype.card Z : ℝ)⁻¹ *
      ∑ z : Z, (∑ i : ι, ∑ k : K, (P z).v y i k * (P z).v y i k) ≤ c) :
    (averageUnif P).IsCostLe c := by
  refine average_isCostLe P _ _ _ (fun x => ?_) (fun y => ?_)
  · rw [← Finset.mul_sum]
    exact hu x
  · rw [← Finset.mul_sum]
    exact hv y

end DualPair

end QuantumQueryComplexity
