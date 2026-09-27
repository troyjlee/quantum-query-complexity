import QuantumQueryComplexity.PredictionTreeCompose
import QuantumQueryComplexity.Promise.ComposeShared
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Prediction trees over subroutine calls, on a promise domain

The main theorem, `PredTree.hasDualOn_compose`:

    inputs `x : X` observed through `read : X → ι → σ`,
    subroutines `g : P → X → V`, each with `HasDualOn read (g p) A`,
    a prediction tree `Tr` over indices `P` and return values `V`,
    at most `q` calls and `G` unpredicted answers **on every realizable
    table** `z_x = fun p => g p x`
      ⟹  HasDualOn read (fun x => Tr.eval (fun p => g p x)) (8·A·√(q·G)).

Budgets are needed only on the tables that actually occur; correlations
between the subroutine values may rule out expensive virtual executions, and
the theorem does not ask for a budget there.  The zero cases `q = 0`, `G = 0`
(and the case `A = 0`, which the construction handles as any other) give the
zero certificate, via the constancy lemmas of `PredictionTreeCompose.lean`.

The construction:

1. `PredTree.exists_dualPair_of_fintype` gives the tree's vectors with
   *pointwise* load bounds on every table; the bounds are evaluated only at
   `z_x`, where `uLoad_le_sum`/`vLoad_le_sum` and `budget_eq` give `8·√(q·G)`.
2. Restricting those vectors to the realizable tables is a promise dual
   `DualPairOn z K F` with observation map `z`.
3. `DualPairOn.composeShared` — the promise-outer version of shared-input
   composition, new here — composes it with the inner promise duals; the
   inner constraint `[g p x ≠ g p y]` is exactly the outer observation mask.

Also here: a cost-zero certificate forces constancy on the promise, and the
weighted cost / dimension-embedding conveniences for `DualPairOn` that the
composition needs.
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} [DecidableEq σ]
variable {X : Type} [Fintype X] [DecidableEq X]
variable {P : Type} [Fintype P] [DecidableEq P]
variable {V : Type} [DecidableEq V]
variable {O : Type} [DecidableEq O]

/-! ## A cost-zero certificate forces constancy -/

namespace DualPairOn

variable {K : Type} [Fintype K] {read : X → ι → σ} {f : X → O}

/-- A dual solution of cost `0` has zero vectors, so the constraint forces
every pair of promise inputs to share an output. -/
theorem eq_of_isCostLe_zero (Q : DualPairOn read K f) (hQ : Q.IsCostLe 0) (x y : X) :
    f x = f y := by
  have hnn : ∀ i k, 0 ≤ Q.u x i k * Q.u x i k := fun _ _ => mul_self_nonneg _
  have hu : ∀ i k, Q.u x i k = 0 := by
    intro i k
    have hle : Q.u x i k * Q.u x i k ≤ ∑ i, ∑ k, Q.u x i k * Q.u x i k :=
      calc Q.u x i k * Q.u x i k ≤ ∑ k, Q.u x i k * Q.u x i k :=
            Finset.single_le_sum (fun k _ => hnn i k) (Finset.mem_univ k)
        _ ≤ ∑ i, ∑ k, Q.u x i k * Q.u x i k :=
            Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun k _ => hnn i k)
              (Finset.mem_univ i)
    exact mul_self_eq_zero.mp (le_antisymm (hle.trans (hQ.1 x)) (hnn i k))
  have hc := Q.constraint x y
  have h0 : (∑ i, if read x i = read y i then (0 : ℝ)
      else ∑ k, Q.u x i k * Q.v y i k) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      split_ifs
      · rfl
      · exact Finset.sum_eq_zero fun k _ => by rw [hu i k, zero_mul]
  rw [h0] at hc
  by_contra hne
  rw [if_neg hne] at hc
  exact zero_ne_one hc

end DualPairOn

/-- **A cost-zero bundled certificate forces constancy on the promise.** -/
theorem HasDualOn.eq_of_cost_zero {read : X → ι → σ} {f : X → O}
    (h : HasDualOn read f 0) (x y : X) : f x = f y := by
  obtain ⟨K, hK, Q, hQ⟩ := h
  exact Q.eq_of_isCostLe_zero hQ x y

/-- The total form. -/
theorem HasDual.eq_of_cost_zero [Fintype σ] {g : (ι → σ) → O} (h : HasDual g 0)
    (x y : ι → σ) : g x = g y :=
  h.hasDualOn.eq_of_cost_zero x y

/-! ## Weighted cost and dimension embedding for promise duals -/

namespace DualPairOn

variable {K : Type} [Fintype K] {read : X → ι → σ} {f : X → O}

/-- Weighted cost of a promise dual solution (the promise mirror of
`DualPair.IsWeightedCostLe`). -/
def IsWeightedCostLe (Q : DualPairOn read K f) (c : ι → ℝ) (Vout : ℝ) : Prop :=
  (∀ x, ∑ i, c i * ∑ k, Q.u x i k * Q.u x i k ≤ Vout) ∧
  (∀ x, ∑ i, c i * ∑ k, Q.v x i k * Q.v x i k ≤ Vout)

/-- Uniform weights: a cost bound `W` is a `c₀`-weighted cost bound `c₀·W`. -/
lemma isWeightedCostLe_const {Q : DualPairOn read K f} {c₀ W : ℝ} (hc₀ : 0 ≤ c₀)
    (hQ : Q.IsCostLe W) : Q.IsWeightedCostLe (fun _ => c₀) (c₀ * W) := by
  constructor
  · intro x
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hQ.1 x) hc₀
  · intro x
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hQ.2 x) hc₀

/-- Padding a promise dual solution with zero coordinates along an injection
of dimension types (the promise mirror of `DualPair.embedDim`). -/
noncomputable def embedDim {K' : Type} [DecidableEq K] [Fintype K'] [DecidableEq K']
    {m : K → K'} (hm : Function.Injective m) (Q : DualPairOn read K f) :
    DualPairOn read K' f where
  u x i := fun k' => spread m (fun k => Q.u x i k) k'
  v y i := fun k' => spread m (fun k => Q.v y i k) k'
  constraint x y := by
    have hpt : ∀ i : ι,
        (∑ k' : K', spread m (fun k => Q.u x i k) k' * spread m (fun k => Q.v y i k) k')
          = ∑ k : K, Q.u x i k * Q.v y i k := by
      intro i
      rw [Finset.sum_congr rfl fun k' (_ : k' ∈ Finset.univ) =>
        spread_mul_spread hm k' (fun k => Q.u x i k) (fun k => Q.v y i k)]
      exact sum_spread hm _
    simp only [hpt]
    exact Q.constraint x y

theorem embedDim_isCostLe {K' : Type} [DecidableEq K] [Fintype K'] [DecidableEq K']
    {m : K → K'} (hm : Function.Injective m) {c : ℝ} (Q : DualPairOn read K f)
    (hQ : Q.IsCostLe c) : (Q.embedDim hm).IsCostLe c := by
  have key : ∀ (U : X → ι → K → ℝ) (x : X) (i : ι),
      (∑ k' : K', spread m (fun k => U x i k) k' * spread m (fun k => U x i k) k')
        = ∑ k : K, U x i k * U x i k := by
    intro U x i
    rw [Finset.sum_congr rfl fun k' (_ : k' ∈ Finset.univ) =>
      spread_mul_spread hm k' (fun k => U x i k) (fun k => U x i k)]
    exact sum_spread hm _
  refine ⟨fun x => ?_, fun y => ?_⟩
  · refine le_trans (le_of_eq ?_) (hQ.1 x)
    exact Finset.sum_congr rfl fun i _ => key Q.u x i
  · refine le_trans (le_of_eq ?_) (hQ.2 y)
    exact Finset.sum_congr rfl fun i _ => key Q.v y i

/-! ## Promise-outer shared composition

The outer solution lives on the same input type `X`, observed through the
table `obs : X → P → V` of subroutine values; the inner solutions are promise
duals for the columns `fun x => obs x p` relative to the real observation map
`read`.  The vectors are the usual direct sums of tensors; the inner
constraint `[obs x p ≠ obs y p]` supplies the outer mask. -/

variable {K' : Type} [Fintype K'] {obs : X → P → V} {F : X → O}

/-- **Shared composition with a promise outer solution.** -/
noncomputable def composeShared (Q : DualPairOn obs K F)
    (R : ∀ p, DualPairOn read K' (fun x => obs x p)) :
    DualPairOn read (P × K × K') F where
  u x i := fun c => Q.u x c.1 c.2.1 * (R c.1).u x i c.2.2
  v y i := fun c => Q.v y c.1 c.2.1 * (R c.1).v y i c.2.2
  constraint x y := by
    classical
    set A : P → ℝ := fun p => ∑ k : K, Q.u x p k * Q.v y p k with hA
    set B : P → ι → ℝ := fun p i => ∑ k' : K', (R p).u x i k' * (R p).v y i k' with hB
    have hpt : ∀ i : ι,
        (∑ c : P × K × K',
          (Q.u x c.1 c.2.1 * (R c.1).u x i c.2.2) * (Q.v y c.1 c.2.1 * (R c.1).v y i c.2.2))
        = ∑ p : P, A p * B p i := by
      intro i
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Fintype.sum_prod_type, hA, hB, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => by ring
    have hR : ∀ p, (∑ i : ι, if read x i = read y i then (0 : ℝ) else B p i)
        = if obs x p = obs y p then 0 else 1 := fun p => (R p).constraint x y
    calc (∑ i : ι, if read x i = read y i then (0 : ℝ)
            else ∑ c : P × K × K',
              (Q.u x c.1 c.2.1 * (R c.1).u x i c.2.2) *
                (Q.v y c.1 c.2.1 * (R c.1).v y i c.2.2))
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
      _ = ∑ p : P, A p * (if obs x p = obs y p then (0 : ℝ) else 1) :=
          Finset.sum_congr rfl fun p _ => by rw [hR p]
      _ = if F x = F y then (0 : ℝ) else 1 := by
          rw [← Q.constraint x y]
          refine Finset.sum_congr rfl fun p _ => ?_
          by_cases hp : obs x p = obs y p
          · rw [if_pos hp, if_pos hp, mul_zero]
          · rw [if_neg hp, if_neg hp, mul_one, hA]

@[simp] lemma composeShared_u (Q : DualPairOn obs K F)
    (R : ∀ p, DualPairOn read K' (fun x => obs x p)) (x : X) (i : ι) (c : P × K × K') :
    (Q.composeShared R).u x i c = Q.u x c.1 c.2.1 * (R c.1).u x i c.2.2 := rfl

@[simp] lemma composeShared_v (Q : DualPairOn obs K F)
    (R : ∀ p, DualPairOn read K' (fun x => obs x p)) (y : X) (i : ι) (c : P × K × K') :
    (Q.composeShared R).v y i c = Q.v y c.1 c.2.1 * (R c.1).v y i c.2.2 := rfl

private lemma sum_composeShared_u_sq (Q : DualPairOn obs K F)
    (R : ∀ p, DualPairOn read K' (fun x => obs x p)) (x : X) :
    (∑ i : ι, ∑ c : P × K × K',
      (Q.composeShared R).u x i c * (Q.composeShared R).u x i c)
      = ∑ p : P, (∑ k : K, Q.u x p k * Q.u x p k)
          * ∑ i : ι, ∑ k' : K', (R p).u x i k' * (R p).u x i k' := by
  have hstep : ∀ i : ι,
      (∑ c : P × K × K', (Q.composeShared R).u x i c * (Q.composeShared R).u x i c)
        = ∑ p : P, (∑ k : K, Q.u x p k * Q.u x p k)
            * ∑ k' : K', (R p).u x i k' * (R p).u x i k' := by
    intro i
    simp only [composeShared_u]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => by ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => (Finset.mul_sum _ _ _).symm

private lemma sum_composeShared_v_sq (Q : DualPairOn obs K F)
    (R : ∀ p, DualPairOn read K' (fun x => obs x p)) (y : X) :
    (∑ i : ι, ∑ c : P × K × K',
      (Q.composeShared R).v y i c * (Q.composeShared R).v y i c)
      = ∑ p : P, (∑ k : K, Q.v y p k * Q.v y p k)
          * ∑ i : ι, ∑ k' : K', (R p).v y i k' * (R p).v y i k' := by
  have hstep : ∀ i : ι,
      (∑ c : P × K × K', (Q.composeShared R).v y i c * (Q.composeShared R).v y i c)
        = ∑ p : P, (∑ k : K, Q.v y p k * Q.v y p k)
            * ∑ k' : K', (R p).v y i k' * (R p).v y i k' := by
    intro i
    simp only [composeShared_v]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => by ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => (Finset.mul_sum _ _ _).symm

/-- **The cost of a promise-outer shared composition**: an outer solution of
`c`-weighted cost `Vout` composed with inner promise solutions of cost `c p`
has cost `Vout`. -/
theorem composeShared_isCostLe {c : P → ℝ} {Vout : ℝ} (Q : DualPairOn obs K F)
    (R : ∀ p, DualPairOn read K' (fun x => obs x p)) (hQ : Q.IsWeightedCostLe c Vout)
    (hR : ∀ p, (R p).IsCostLe (c p)) : (Q.composeShared R).IsCostLe Vout := by
  constructor
  · intro x
    rw [sum_composeShared_u_sq]
    refine le_trans (Finset.sum_le_sum fun p _ => ?_) (hQ.1 x)
    exact (mul_le_mul_of_nonneg_left ((hR p).1 x)
      (Finset.sum_nonneg fun k _ => mul_self_nonneg _)).trans_eq (mul_comm _ _)
  · intro y
    rw [sum_composeShared_v_sq]
    refine le_trans (Finset.sum_le_sum fun p _ => ?_) (hQ.2 y)
    exact (mul_le_mul_of_nonneg_left ((hR p).2 y)
      (Finset.sum_nonneg fun k _ => mul_self_nonneg _)).trans_eq (mul_comm _ _)

/-- **Promise-outer shared composition, bundled.**  The inner dimensions are
made uniform by direct-summing over the subproblems. -/
theorem hasDualOn_composeShared {c : P → ℝ} {Vout : ℝ} (Q : DualPairOn obs K F)
    (hQ : Q.IsWeightedCostLe c Vout)
    (hR : ∀ p, HasDualOn read (fun x => obs x p) (c p)) : HasDualOn read F Vout := by
  classical
  choose K' hK' R hRc using hR
  letI := hK'
  let R' : ∀ p, DualPairOn read (Σ p, K' p) (fun x => obs x p) :=
    fun p => (R p).embedDim (sigma_mk_injective (i := p))
  exact ⟨P × K × (Σ p, K' p), inferInstance, Q.composeShared R',
    composeShared_isCostLe Q R' hQ fun p => embedDim_isCostLe _ _ (hRc p)⟩

end DualPairOn

/-- Tagging a subroutine's output into a sigma type (the representation of
heterogeneous return alphabets `Γ p` inside one common `V = Σ p, Γ p`) is
free: the tag is injective, so the level sets are unchanged. -/
theorem HasDualOn.sigmaMk {Γ : P → Type} [∀ p, DecidableEq (Γ p)] {read : X → ι → σ}
    {p : P} {f : X → Γ p} {c : ℝ} (h : HasDualOn read f c) :
    HasDualOn read (fun x => (⟨p, f x⟩ : Σ p, Γ p)) c :=
  h.ofKer fun x y => by simp

/-! ## The main theorem -/

namespace PredTree

variable {α : Type} [Fintype α] [DecidableEq α]

/-- **Compositional Beigi–Taghavi, certificate form**. A prediction tree `Tr`
over subroutine indices `P` and return values
`V`, run on the virtual table `fun p => g p x` of a promise input `x`, where
every `g p` has an all-pairs dual of cost `A` on the promise and every
*realizable* table makes at most `q` calls and receives at most `G`
unpredicted answers: the composite has an all-pairs dual of cost
`8·A·√(q·G)` on the promise.  Every budget `q, G ≥ 0` and every `A ≥ 0` is
allowed; at `q = 0` or `G = 0` the output is constant and the certificate is
the zero one.  No bound on other tables, no disjointness of the subroutines'
inputs, no injectivity of `g` is assumed. -/
theorem hasDualOn_compose (Tr : PredTree P V α Unit O) (read : X → ι → σ) (g : P → X → V)
    {A : ℝ} (hA : 0 ≤ A) (hg : ∀ p, HasDualOn read (g p) A) {q G : ℕ}
    (hvis : ∀ x, Tr.visits () (fun p => g p x) ≤ q)
    (hunp : ∀ x, Tr.unpreds () (fun p => g p x) ≤ G) :
    HasDualOn read (fun x => Tr.eval (fun p => g p x))
      (8 * A * Real.sqrt ((q : ℝ) * (G : ℝ))) := by
  classical
  -- no call: the output is constant
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have hconst : ∀ x y : X, Tr.eval (fun p => g p x) = Tr.eval (fun p => g p y) :=
      fun x y => eval_eq_of_visits_eq_zero Tr (fun _ => Nat.le_zero.mp (hvis x)) _
    exact (hasDualOn_of_const read hconst).mono (by simp)
  -- no unpredicted answer: the output is constant
  rcases Nat.eq_zero_or_pos G with rfl | hG
  · have hconst : ∀ x y : X, Tr.eval (fun p => g p x) = Tr.eval (fun p => g p y) :=
      fun x y => eval_eq_of_unpreds_eq_zero Tr
        (fun _ => Nat.le_zero.mp (hunp x)) (fun _ => Nat.le_zero.mp (hunp y))
    exact (hasDualOn_of_const read hconst).mono (by simp)
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hG' : (0 : ℝ) < G := by exact_mod_cast hG
  -- the realizable tables
  set z : X → P → V := fun x p => g p x with hz
  -- recode the reachable outputs into a finite type
  set S : Finset O := Finset.image (fun x => Tr.eval (z x)) Finset.univ with hS
  have hmem : ∀ x : X, Tr.eval (z x) ∈ S := fun x =>
    Finset.mem_image_of_mem _ (Finset.mem_univ x)
  set φ : O → Option {o // o ∈ S} :=
    fun o => if h : o ∈ S then some ⟨o, h⟩ else none with hφ
  set Tr' := Tr.mapOut φ with hTr'
  -- the tree's vectors, with pointwise load bounds
  set w : Unit → ℝ := fun _ => Real.sqrt ((q : ℝ) / G) with hw
  have hwpos : ∀ j, 0 < w j := fun _ => Real.sqrt_pos.mpr (div_pos hq' hG')
  obtain ⟨K, hK, Q, hQu, hQv⟩ := exists_dualPair_of_fintype w hwpos Tr'
  letI := hK
  -- the loads at realizable tables are within the budget
  have hload : ∀ x : X,
      (∑ j, (4 / w j * (Tr'.visits j (z x) : ℝ) + 4 * w j * (Tr'.unpreds j (z x) : ℝ)))
        ≤ 8 * Real.sqrt ((q : ℝ) * G) := by
    intro x
    rw [Fintype.sum_unique, ← budget_eq hq' hG']
    have h1 : (Tr'.visits default (z x) : ℝ) ≤ q := by
      rw [hTr', visits_mapOut]; exact_mod_cast hvis x
    have h2 : (Tr'.unpreds default (z x) : ℝ) ≤ G := by
      rw [hTr', unpreds_mapOut]; exact_mod_cast hunp x
    have hw0 : 0 < w default := hwpos default
    have e1 : 4 / w default * (Tr'.visits default (z x) : ℝ)
        ≤ 4 / Real.sqrt ((q : ℝ) / G) * q :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have e2 : 4 * w default * (Tr'.unpreds default (z x) : ℝ)
        ≤ 4 * Real.sqrt ((q : ℝ) / G) * G :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  -- the outer promise dual: the tree's vectors at the realizable tables
  let Qo : DualPairOn z K (fun x => Tr'.eval (z x)) :=
    { u := fun x => Q.u (z x)
      v := fun x => Q.v (z x)
      constraint := fun x y => Q.constraint (z x) (z y) }
  have hQo : Qo.IsCostLe (8 * Real.sqrt ((q : ℝ) * G)) :=
    ⟨fun x => (hQu (z x)).trans ((uLoad_le_sum w hwpos Tr' (z x)).trans (hload x)),
     fun x => (hQv (z x)).trans ((vLoad_le_sum w hwpos Tr' (z x)).trans (hload x))⟩
  -- compose with the inner promise duals
  have hmain : HasDualOn read (fun x => Tr'.eval (z x)) (A * (8 * Real.sqrt ((q : ℝ) * G))) :=
    Qo.hasDualOn_composeShared (DualPairOn.isWeightedCostLe_const hA hQo) fun p => hg p
  refine (hmain.ofKer fun x y => ?_).mono (le_of_eq (by ring))
  rw [hTr', eval_mapOut, eval_mapOut, hφ]
  simp only [dif_pos (hmem x), dif_pos (hmem y), Option.some.injEq, Subtype.mk.injEq]
  exact Iff.rfl

/-- **The total-input corollary**: `read = id`. -/
theorem hasDual_compose [Fintype σ] (Tr : PredTree P V α Unit O) (g : P → (ι → σ) → V)
    {A : ℝ} (hA : 0 ≤ A) (hg : ∀ p, HasDual (g p) A) {q G : ℕ}
    (hvis : ∀ x : ι → σ, Tr.visits () (fun p => g p x) ≤ q)
    (hunp : ∀ x : ι → σ, Tr.unpreds () (fun p => g p x) ≤ G) :
    HasDual (fun x => Tr.eval (fun p => g p x)) (8 * A * Real.sqrt ((q : ℝ) * (G : ℝ))) :=
  HasDual.of_hasDualOn_id
    (hasDualOn_compose Tr id g hA (fun p => (hg p).hasDualOn) hvis hunp)

/-- **Zero inner cost**: with `A = 0` the composite certificate has cost `0`,
so the procedure's output is constant on the promise. -/
theorem eval_eq_of_cost_zero (Tr : PredTree P V α Unit O) (read : X → ι → σ)
    (g : P → X → V) (hg : ∀ p, HasDualOn read (g p) 0) (x y : X) :
    Tr.eval (fun p => g p x) = Tr.eval (fun p => g p y) := by
  have hz : (fun p => g p x) = fun p => g p y := funext fun p => (hg p).eq_of_cost_zero x y
  rw [hz]

end PredTree

end QuantumQueryComplexity
