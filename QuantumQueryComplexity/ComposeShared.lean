import QuantumQueryComplexity.WeightedDual
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Dual composition with shared inputs

The composition in `QuantumQueryComplexity/DualCompose.lean` gives each inner function its
own block of variables (`composeFunFam` over `α × β`).  Divide-and-conquer needs
the opposite: finitely many subproblems `g p`, all reading the *same* input `x`,
whose domains typically overlap.  Write

  `sharedFun h g x = h (fun p => g p x)`.

Duals compose in this setting too, and the argument is shorter than the disjoint
one.  Tensoring the outer solution at `p` with the `p`-th inner solution,

  `u x i = ⊕_p U_{g(x)} p ⊗ u^p x i`,   `v y i = ⊕_p V_{g(y)} p ⊗ v^p y i`,

the masked sum factors as

  `∑_{i : x i ≠ y i} ⟨u x i, v y i⟩ = ∑_p ⟨U_{g x} p, V_{g y} p⟩ · [g p x ≠ g p y]`,

which is exactly the outer constraint evaluated at the pair `(g x, g y)`.  No
property of the inner functions' supports is used, so they may overlap freely.

The cost telescopes the same way: the `p`-th block contributes
`‖U_{g x} p‖²` times the `p`-th inner cost, so an outer solution of *weighted*
cost `V` with weights `c` and inner solutions of cost `c p` compose to cost `V`
(`DualPair.composeShared_isCostLe`).  That is the whole quantitative content of
"solve subproblem `p` at cost `c p`, then optimise over `p`".
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [DecidableEq σ]
variable {P : Type*} [Fintype P] [DecidableEq P]
variable {V : Type*} [DecidableEq V]
variable {O : Type*} [DecidableEq O]

/-- The composition of an outer function with subproblems that all read the same
input. -/
def sharedFun (h : (P → V) → O) (g : P → (ι → σ) → V) : (ι → σ) → O :=
  fun x => h fun p => g p x

@[simp] lemma sharedFun_apply (h : (P → V) → O) (g : P → (ι → σ) → V)
    (x : ι → σ) : sharedFun h g x = h (fun p => g p x) := rfl

namespace DualPair

variable {K K' : Type*} [Fintype K] [Fintype K']
variable {h : (P → V) → O} {g : P → (ι → σ) → V}

/-- **Shared-input dual composition.** -/
noncomputable def composeShared (Q : DualPair K h) (R : ∀ p, DualPair K' (g p)) :
    DualPair (P × K × K') (sharedFun h g) where
  u x i := fun c => Q.u (fun p => g p x) c.1 c.2.1 * (R c.1).u x i c.2.2
  v y i := fun c => Q.v (fun p => g p y) c.1 c.2.1 * (R c.1).v y i c.2.2
  constraint x y := by
    classical
    simp only [sharedFun]
    set A : P → ℝ := fun p =>
      ∑ k : K, Q.u (fun p => g p x) p k * Q.v (fun p => g p y) p k with hA
    set B : P → ι → ℝ := fun p i =>
      ∑ k' : K', (R p).u x i k' * (R p).v y i k' with hB
    have hpt : ∀ i : ι,
        (∑ c : P × K × K',
          (Q.u (fun p => g p x) c.1 c.2.1 * (R c.1).u x i c.2.2) *
            (Q.v (fun p => g p y) c.1 c.2.1 * (R c.1).v y i c.2.2))
        = ∑ p : P, A p * B p i := by
      intro i
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Fintype.sum_prod_type, hA, hB, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => by ring
    calc (∑ i : ι, if x i = y i then (0 : ℝ)
            else ∑ c : P × K × K',
              (Q.u (fun p => g p x) c.1 c.2.1 * (R c.1).u x i c.2.2) *
                (Q.v (fun p => g p y) c.1 c.2.1 * (R c.1).v y i c.2.2))
        = ∑ i : ι, ∑ p : P, A p * (if x i = y i then (0 : ℝ) else B p i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hi : x i = y i
          · rw [if_pos hi]
            exact (Finset.sum_eq_zero fun p _ => by rw [if_pos hi, mul_zero]).symm
          · rw [if_neg hi, hpt i]
            exact Finset.sum_congr rfl fun p _ => by rw [if_neg hi]
      _ = ∑ p : P, A p * ∑ i : ι, (if x i = y i then (0 : ℝ) else B p i) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun p _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ p : P, A p * (if g p x = g p y then (0 : ℝ) else 1) :=
          Finset.sum_congr rfl fun p _ => by rw [hB, (R p).constraint x y]
      _ = if h (fun p => g p x) = h (fun p => g p y) then (0 : ℝ) else 1 := by
          rw [← Q.constraint (fun p => g p x) (fun p => g p y)]
          refine Finset.sum_congr rfl fun p _ => ?_
          by_cases hp : g p x = g p y
          · rw [if_pos hp, if_pos hp, mul_zero]
          · rw [if_neg hp, if_neg hp, mul_one, hA]

@[simp] lemma composeShared_u (Q : DualPair K h) (R : ∀ p, DualPair K' (g p))
    (x : ι → σ) (i : ι) (c : P × K × K') :
    (Q.composeShared R).u x i c
      = Q.u (fun p => g p x) c.1 c.2.1 * (R c.1).u x i c.2.2 := rfl

@[simp] lemma composeShared_v (Q : DualPair K h) (R : ∀ p, DualPair K' (g p))
    (y : ι → σ) (i : ι) (c : P × K × K') :
    (Q.composeShared R).v y i c
      = Q.v (fun p => g p y) c.1 c.2.1 * (R c.1).v y i c.2.2 := rfl

/-- The `ℓ²` mass of the composed solution splits as (outer mass at `p`) times
(inner mass of the `p`-th solution). -/
private lemma sum_composeShared_u_sq (Q : DualPair K h) (R : ∀ p, DualPair K' (g p))
    (x : ι → σ) :
    (∑ i : ι, ∑ c : P × K × K',
      (Q.composeShared R).u x i c * (Q.composeShared R).u x i c)
      = ∑ p : P, (∑ k : K, Q.u (fun p => g p x) p k * Q.u (fun p => g p x) p k)
          * ∑ i : ι, ∑ k' : K', (R p).u x i k' * (R p).u x i k' := by
  have hstep : ∀ i : ι,
      (∑ c : P × K × K', (Q.composeShared R).u x i c * (Q.composeShared R).u x i c)
        = ∑ p : P, (∑ k : K, Q.u (fun p => g p x) p k * Q.u (fun p => g p x) p k)
            * ∑ k' : K', (R p).u x i k' * (R p).u x i k' := by
    intro i
    simp only [composeShared_u]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => by ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => (Finset.mul_sum _ _ _).symm

private lemma sum_composeShared_v_sq (Q : DualPair K h) (R : ∀ p, DualPair K' (g p))
    (y : ι → σ) :
    (∑ i : ι, ∑ c : P × K × K',
      (Q.composeShared R).v y i c * (Q.composeShared R).v y i c)
      = ∑ p : P, (∑ k : K, Q.v (fun p => g p y) p k * Q.v (fun p => g p y) p k)
          * ∑ i : ι, ∑ k' : K', (R p).v y i k' * (R p).v y i k' := by
  have hstep : ∀ i : ι,
      (∑ c : P × K × K', (Q.composeShared R).v y i c * (Q.composeShared R).v y i c)
        = ∑ p : P, (∑ k : K, Q.v (fun p => g p y) p k * Q.v (fun p => g p y) p k)
            * ∑ k' : K', (R p).v y i k' * (R p).v y i k' := by
    intro i
    simp only [composeShared_v]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => by ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => (Finset.mul_sum _ _ _).symm

/-- **The cost of a shared composition.**  An outer solution of `c`-weighted cost
`V` composed with inner solutions of cost `c p` has cost `V`. -/
theorem composeShared_isCostLe {c : P → ℝ} {Vout : ℝ} (Q : DualPair K h)
    (R : ∀ p, DualPair K' (g p)) (hc : ∀ p, 0 ≤ c p)
    (hQ : Q.IsWeightedCostLe c Vout) (hR : ∀ p, (R p).IsCostLe (c p)) :
    (Q.composeShared R).IsCostLe Vout := by
  constructor
  · intro x
    rw [sum_composeShared_u_sq]
    refine le_trans (Finset.sum_le_sum fun p _ => ?_) (hQ.1 fun p => g p x)
    exact (mul_le_mul_of_nonneg_left ((hR p).1 x)
      (Finset.sum_nonneg fun k _ => mul_self_nonneg _)).trans_eq (mul_comm _ _)
  · intro y
    rw [sum_composeShared_v_sq]
    refine le_trans (Finset.sum_le_sum fun p _ => ?_) (hQ.2 fun p => g p y)
    exact (mul_le_mul_of_nonneg_left ((hR p).2 y)
      (Finset.sum_nonneg fun k _ => mul_self_nonneg _)).trans_eq (mul_comm _ _)

end DualPair

/-- The adversary bound of a shared composition, from an outer weighted solution
and inner solutions. -/
theorem advPM_sharedFun_le [Fintype σ] {K K' : Type*} [Fintype K] [Fintype K']
    {h : (P → V) → O} {g : P → (ι → σ) → V} {c : P → ℝ} {Vout : ℝ}
    (Q : DualPair K h) (R : ∀ p, DualPair K' (g p)) (hc : ∀ p, 0 ≤ c p)
    (hV : 0 ≤ Vout) (hQ : Q.IsWeightedCostLe c Vout)
    (hR : ∀ p, (R p).IsCostLe (c p)) :
    advPM (sharedFun h g) ≤ Vout :=
  advPM_le_of_dualPair (Q.composeShared R) hV
    (DualPair.composeShared_isCostLe Q R hc hQ hR)

end QuantumQueryComplexity
