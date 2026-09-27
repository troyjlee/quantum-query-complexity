import QuantumQueryComplexity.Promise.HasDual
import QuantumQueryComplexity.ComposeShared
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Shared-input dual composition on a promise domain

`QuantumQueryComplexity/ComposeShared.lean` composes an outer function with finitely many
subproblems that all read the same input.  A divide-and-conquer node needs
the same move *on a promise*: the node's `h` children are solved only on the
descriptor fiber they belong to, so their duals are `DualPairOn`s, while the
outer function — the weighted maximum scan — is an ordinary total dual
solution on the small cube of child values.

That asymmetry is exactly right, and it is what makes this file short: the
outer constraint is evaluated at the *values* `fun p => g p x`, which live in
the total cube `P → V` no matter what promise the inputs came from.  Only the
mask changes, from `x i = y i` to `read x i = read y i`, and the mask plays
no role in the algebra.  So the vectors, the constraint computation and the
cost telescoping are those of the total case verbatim:

  `u x i = ⊕_p U_{g x} p ⊗ u^p x i`,   cost `V` from an outer weighted cost
  `V` with weights `c` and inner promise duals of cost `c p`.
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} [DecidableEq σ]
variable {X : Type} [Fintype X] [DecidableEq X]
variable {P : Type} [Fintype P] [DecidableEq P]
variable {V : Type} [DecidableEq V]
variable {O : Type} [DecidableEq O]

/-- An outer function applied to finitely many subproblems of a promise
domain. -/
def sharedFunOn (h : (P → V) → O) (g : P → X → V) : X → O :=
  fun x => h fun p => g p x

@[simp] lemma sharedFunOn_apply (h : (P → V) → O) (g : P → X → V) (x : X) :
    sharedFunOn h g x = h (fun p => g p x) := rfl

variable {K K' : Type} [Fintype K] [Fintype K']
variable {read : X → ι → σ} {h : (P → V) → O} {g : P → X → V}

/-- **Shared-input dual composition on a promise.**  The outer solution is a
total one on the cube of child values; the inner ones live on the promise. -/
noncomputable def composeSharedOn (Q : DualPair K h)
    (R : ∀ p, DualPairOn read K' (g p)) :
    DualPairOn read (P × K × K') (sharedFunOn h g) where
  u x i := fun c => Q.u (fun p => g p x) c.1 c.2.1 * (R c.1).u x i c.2.2
  v y i := fun c => Q.v (fun p => g p y) c.1 c.2.1 * (R c.1).v y i c.2.2
  constraint x y := by
    classical
    simp only [sharedFunOn]
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
    calc (∑ i : ι, if read x i = read y i then (0 : ℝ)
            else ∑ c : P × K × K',
              (Q.u (fun p => g p x) c.1 c.2.1 * (R c.1).u x i c.2.2) *
                (Q.v (fun p => g p y) c.1 c.2.1 * (R c.1).v y i c.2.2))
        = ∑ i : ι, ∑ p : P, A p * (if read x i = read y i then (0 : ℝ) else B p i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hi : read x i = read y i
          · rw [if_pos hi]
            exact (Finset.sum_eq_zero fun p _ => by rw [if_pos hi, mul_zero]).symm
          · rw [if_neg hi, hpt i]
            exact Finset.sum_congr rfl fun p _ => by rw [if_neg hi]
      _ = ∑ p : P, A p * ∑ i : ι, (if read x i = read y i then (0 : ℝ) else B p i) := by
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

@[simp] lemma composeSharedOn_u (Q : DualPair K h)
    (R : ∀ p, DualPairOn read K' (g p)) (x : X) (i : ι) (c : P × K × K') :
    (composeSharedOn Q R).u x i c
      = Q.u (fun p => g p x) c.1 c.2.1 * (R c.1).u x i c.2.2 := rfl

@[simp] lemma composeSharedOn_v (Q : DualPair K h)
    (R : ∀ p, DualPairOn read K' (g p)) (y : X) (i : ι) (c : P × K × K') :
    (composeSharedOn Q R).v y i c
      = Q.v (fun p => g p y) c.1 c.2.1 * (R c.1).v y i c.2.2 := rfl

private lemma sum_composeSharedOn_u_sq (Q : DualPair K h)
    (R : ∀ p, DualPairOn read K' (g p)) (x : X) :
    (∑ i : ι, ∑ c : P × K × K',
      (composeSharedOn Q R).u x i c * (composeSharedOn Q R).u x i c)
      = ∑ p : P, (∑ k : K, Q.u (fun p => g p x) p k * Q.u (fun p => g p x) p k)
          * ∑ i : ι, ∑ k' : K', (R p).u x i k' * (R p).u x i k' := by
  have hstep : ∀ i : ι,
      (∑ c : P × K × K', (composeSharedOn Q R).u x i c * (composeSharedOn Q R).u x i c)
        = ∑ p : P, (∑ k : K, Q.u (fun p => g p x) p k * Q.u (fun p => g p x) p k)
            * ∑ k' : K', (R p).u x i k' * (R p).u x i k' := by
    intro i
    simp only [composeSharedOn_u]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => by ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => (Finset.mul_sum _ _ _).symm

private lemma sum_composeSharedOn_v_sq (Q : DualPair K h)
    (R : ∀ p, DualPairOn read K' (g p)) (y : X) :
    (∑ i : ι, ∑ c : P × K × K',
      (composeSharedOn Q R).v y i c * (composeSharedOn Q R).v y i c)
      = ∑ p : P, (∑ k : K, Q.v (fun p => g p y) p k * Q.v (fun p => g p y) p k)
          * ∑ i : ι, ∑ k' : K', (R p).v y i k' * (R p).v y i k' := by
  have hstep : ∀ i : ι,
      (∑ c : P × K × K', (composeSharedOn Q R).v y i c * (composeSharedOn Q R).v y i c)
        = ∑ p : P, (∑ k : K, Q.v (fun p => g p y) p k * Q.v (fun p => g p y) p k)
            * ∑ k' : K', (R p).v y i k' * (R p).v y i k' := by
    intro i
    simp only [composeSharedOn_v]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => by ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => (Finset.mul_sum _ _ _).symm

/-- **The cost of a promise shared composition**: an outer solution of
`c`-weighted cost `V` composed with promise solutions of cost `c p`. -/
theorem composeSharedOn_isCostLe {c : P → ℝ} {Vout : ℝ} (Q : DualPair K h)
    (R : ∀ p, DualPairOn read K' (g p)) (hQ : Q.IsWeightedCostLe c Vout)
    (hR : ∀ p, (R p).IsCostLe (c p)) :
    (composeSharedOn Q R).IsCostLe Vout := by
  constructor
  · intro x
    rw [sum_composeSharedOn_u_sq]
    refine le_trans (Finset.sum_le_sum fun p _ => ?_) (hQ.1 fun p => g p x)
    exact (mul_le_mul_of_nonneg_left ((hR p).1 x)
      (Finset.sum_nonneg fun k _ => mul_self_nonneg _)).trans_eq (mul_comm _ _)
  · intro y
    rw [sum_composeSharedOn_v_sq]
    refine le_trans (Finset.sum_le_sum fun p _ => ?_) (hQ.2 fun p => g p y)
    exact (mul_le_mul_of_nonneg_left ((hR p).2 y)
      (Finset.sum_nonneg fun k _ => mul_self_nonneg _)).trans_eq (mul_comm _ _)

/-- **Shared composition on a promise, bundled.**  Inner dimensions are
hidden; they are made uniform by direct-summing over the (finitely many)
subproblems. -/
theorem hasDualOn_sharedFunOn {read : X → ι → σ} {h : (P → V) → O}
    {g : P → X → V} {K : Type} [Fintype K] {c : P → ℝ} {Vout : ℝ}
    (Q : DualPair K h) (hQ : Q.IsWeightedCostLe c Vout)
    (hR : ∀ p, HasDualOn read (g p) (c p)) :
    HasDualOn read (sharedFunOn h g) Vout := by
  classical
  choose K' hK' R hRc using hR
  -- direct-sum the branch dimensions into one type
  letI := hK'
  set K₁ : Type := Σ p : P, K' p with hK₁
  set R' : ∀ p, DualPairOn read K₁ (g p) := fun p =>
    { u := fun x i k => if hk : k.1 = p then (R p).u x i (hk ▸ k.2) else 0
      v := fun y i k => if hk : k.1 = p then (R p).v y i (hk ▸ k.2) else 0
      constraint := fun x y => by
        rw [← (R p).constraint x y]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : read x i = read y i
        · rw [if_pos hi, if_pos hi]
        · rw [if_neg hi, if_neg hi]
          rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
          rw [Finset.sum_eq_single_of_mem p (Finset.mem_univ p)]
          · exact Finset.sum_congr rfl fun k _ => by simp
          · intro p' _ hp'
            exact Finset.sum_eq_zero fun k _ => by simp [hp'] } with hR'
  have hR'c : ∀ p, (R' p).IsCostLe (c p) := by
    intro p
    constructor
    · intro x
      refine le_trans (le_of_eq ?_) ((hRc p).1 x)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
      rw [Finset.sum_eq_single_of_mem p (Finset.mem_univ p)]
      · exact Finset.sum_congr rfl fun k _ => by simp [hR']
      · intro p' _ hp'
        exact Finset.sum_eq_zero fun k _ => by simp [hR', hp']
    · intro y
      refine le_trans (le_of_eq ?_) ((hRc p).2 y)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
      rw [Finset.sum_eq_single_of_mem p (Finset.mem_univ p)]
      · exact Finset.sum_congr rfl fun k _ => by simp [hR']
      · intro p' _ hp'
        exact Finset.sum_eq_zero fun k _ => by simp [hR', hp']
  exact ⟨P × K × K₁, inferInstance, composeSharedOn Q R',
    composeSharedOn_isCostLe Q R' hQ hR'c⟩

end QuantumQueryComplexity
