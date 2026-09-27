import QuantumQueryComplexity.PredictionTree
import QuantumQueryComplexity.HasDual
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Prediction trees over subroutine calls: the total-table wrapper

A *compositional* form of the Beigi–Taghavi prediction-tree construction
(`PredictionTree.lean`): the tree's "coordinates" are subroutine indices
`p : P`, its "letters" are the subroutines' return values `v : V`, and the tree
is run on the *virtual table* `fun p => g p x` of an actual input `x`.  Each
subroutine `g p` comes with an all-pairs dual of cost `A`; composing the tree's
own dual (cost `8·√(q·G)` from `q` calls and `G` unpredicted branches) with the
inner duals through `HasWeightedDual.composeShared` costs exactly the factor
`A`.

This file is the easy half — the budgets `q`, `G` are assumed on **every**
table `z : P → V`.  The main theorem, with budgets only on the realizable
tables `z_x = fun p => g p x` and on a promise domain, is
`Promise/PredictionTreeCompose.lean` (`PredTree.hasDualOn_compose`).  The two
constancy lemmas at the end (no unpredicted answer ⇒ same output; no call ⇒
same output) serve the zero-budget cases there.
-/

namespace QuantumQueryComplexity

namespace PredTree

/-! ## Constancy from zero budgets -/

section Constancy

variable {ι σ α J O : Type} [DecidableEq α] [DecidableEq J]

/-- **No unpredicted answer, no information**: two executions that never
receive an unpredicted answer (in any layer) follow the same predicted
branches and reach the same leaf. -/
theorem eval_eq_of_unpreds_eq_zero (T : PredTree ι σ α J O) {x y : ι → σ}
    (hx : ∀ j, T.unpreds j x = 0) (hy : ∀ j, T.unpreds j y = 0) :
    T.eval x = T.eval y := by
  induction T with
  | leaf o => rfl
  | query i lab pred j k ih =>
      have hxj : (if j = j ∧ unpred pred (lab (x i)) = true then 1 else 0)
          + (k (lab (x i))).unpreds j x = 0 := hx j
      have hyj : (if j = j ∧ unpred pred (lab (y i)) = true then 1 else 0)
          + (k (lab (y i))).unpreds j y = 0 := hy j
      have hux : unpred pred (lab (x i)) = false := by
        by_contra hne
        rw [Bool.not_eq_false] at hne
        rw [if_pos ⟨rfl, hne⟩] at hxj
        omega
      have huy : unpred pred (lab (y i)) = false := by
        by_contra hne
        rw [Bool.not_eq_false] at hne
        rw [if_pos ⟨rfl, hne⟩] at hyj
        omega
      have hpx : pred = some (lab (x i)) := by simpa [unpred] using hux
      have hpy : pred = some (lab (y i)) := by simpa [unpred] using huy
      have hlab : lab (y i) = lab (x i) :=
        (Option.some_inj.mp (hpy.symm.trans hpx))
      have hx' : ∀ j', (k (lab (x i))).unpreds j' x = 0 := fun j' =>
        (Nat.add_eq_zero_iff.mp (hx j')).2
      have hy' : ∀ j', (k (lab (x i))).unpreds j' y = 0 := fun j' => by
        have h := (Nat.add_eq_zero_iff.mp (hy j')).2
        rwa [hlab] at h
      show (k (lab (x i))).eval x = (k (lab (y i))).eval y
      rw [hlab]
      exact ih (lab (x i)) hx' hy'

/-- **No call, no information**: an execution that visits no node (of any
layer) is at a leaf, so every execution returns the same output. -/
theorem eval_eq_of_visits_eq_zero (T : PredTree ι σ α J O) {x : ι → σ}
    (hx : ∀ j, T.visits j x = 0) (y : ι → σ) : T.eval x = T.eval y := by
  cases T with
  | leaf o => rfl
  | query i lab pred j k =>
      exfalso
      have hxj : (if j = j then 1 else 0) + (k (lab (x i))).visits j x = 0 := hx j
      rw [if_pos rfl] at hxj
      omega

end Constancy

/-! ## The total-table wrapper -/

variable {ι σ P V α O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α]
  [DecidableEq O]

/-- **Layered composition with uniform inner certificates.**  A prediction
tree over subroutine indices `P` with return alphabet `V`, run on the virtual
table `fun p => g p x`, where every `g p` has a dual of cost `A` and every
table stays within the per-layer budgets `T j` calls / `G j` unpredicted
answers: the composite has a dual of cost `8·A·∑ⱼ √(T j · G j)`. -/
theorem hasDual_compose_layered {J : Type} [Fintype J] [DecidableEq J]
    (Tr : PredTree P V α J O) (g : P → (ι → σ) → V) {A : ℝ} (hA : 0 ≤ A)
    (hg : ∀ p, HasDual (g p) A) {T G : J → ℝ} (hT : ∀ j, 0 < T j) (hG : ∀ j, 0 < G j)
    (hvis : ∀ z j, (Tr.visits j z : ℝ) ≤ T j) (hunp : ∀ z j, (Tr.unpreds j z : ℝ) ≤ G j) :
    HasDual (fun x => Tr.eval (fun p => g p x)) (8 * A * ∑ j, Real.sqrt (T j * G j)) := by
  have h := ((hasDual_eval_layered' Tr hT hG hvis hunp).weighted_const hA).composeShared
    (fun _ => hA) hg
  exact h.mono (le_of_eq (by ring))

/-- **The single-layer total-table wrapper**: at most `q` calls and
`G` unpredicted answers on every
table, inner certificates of cost `A`, composite cost `8·A·√(q·G)`.  Positive
budgets only; the zero cases are handled by the main theorem. -/
theorem hasDual_compose_of_table_bounds (Tr : PredTree P V α Unit O) (g : P → (ι → σ) → V)
    {A : ℝ} (hA : 0 ≤ A) (hg : ∀ p, HasDual (g p) A) {q G : ℕ} (hq : 0 < q) (hG : 0 < G)
    (hvis : ∀ z, Tr.visits () z ≤ q) (hunp : ∀ z, Tr.unpreds () z ≤ G) :
    HasDual (fun x => Tr.eval (fun p => g p x)) (8 * A * Real.sqrt ((q : ℝ) * (G : ℝ))) := by
  have h := hasDual_compose_layered Tr g hA hg (T := fun _ : Unit => (q : ℝ))
    (G := fun _ : Unit => (G : ℝ)) (fun _ => by exact_mod_cast hq) (fun _ => by exact_mod_cast hG)
    (fun z _ => by exact_mod_cast hvis z) (fun z _ => by exact_mod_cast hunp z)
  rw [Fintype.sum_unique] at h
  exact h

end PredTree

end QuantumQueryComplexity
