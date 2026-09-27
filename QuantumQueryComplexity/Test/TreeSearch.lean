import QuantumQueryComplexity.Quantum.TreeSearch
import QuantumQueryComplexity.TreeSearch.Examples

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Acceptance: tree search with shared subcomputations

1. The public statements, pinned with their full types: the exact recurrence, the weighted
   certificate at cost `C_ρ`, optimality and attainment, the depth bound (old and new), the
   promise/heterogeneous certificate, the quantum endpoints.
2. A one-vertex tree (`C = t`, the leaf branch), a chain, a star with unequal leaf depths.
3. **Unequal costs** `2; 3, 4`: `C = 7`, normalized weights `2/7` at the root and `5/7` at
   *each* child (the residual budget is not divided), energy `49`.
4. Semantics: a marking depending on an ancestor cell and the current cell, inputs whose first
   difference is at a strict ancestor; identical query supports for different cells;
   distinct cell-output types; a proper promise with a noninjective observation map; an empty
   promise; always/never marked; marking restricted to a subset of vertices.
5. The perfect binary tree: `C_ρ = ∑ (√2)^h ≤ 3√N`, and the exact root-cost endpoint.
6. **Unequal leaf depths**: the tree `0 → {1, 2}`, `2 → 3` with unit costs has `C_0 = 1 + √5`,
   and the certificate for a marking at the deep leaf.  **A genuine promise**: two of four
   inputs observe `00` and two observe `11`, so the observation map is noninjective and its
   image misses `01`; cells read the observed bit, and no cell dual is demanded off the
   promise.  Empty cell-output types on an empty promise need no inhabitant.
-/

namespace QuantumQueryComplexity
namespace TreeSearchAcceptance

open Finset AncTree

variable {V : Type} [DecidableEq V] [Fintype V] (T : AncTree V)

/-! ## 1. Public statements -/

theorem acceptance_recCost (t : V → ℝ) (ht : ∀ v, 0 < t v) (v : V) {ρ : V} (hρ : T.IsRoot ρ) :
    T.recCost t v = t v + Real.sqrt (∑ u ∈ T.children v, (T.recCost t u) ^ 2)
    ∧ 0 < T.recCost t v ∧ ∑ a ∈ T.path v, t a ≤ T.recCost t ρ :=
  ⟨T.recCost_eq t v, T.recCost_pos ht v, T.sum_path_le_recCost ht hρ v⟩

theorem acceptance_certificate {E : Type} [Fintype E] [DecidableEq E] {ρ : V} (hρ : T.IsRoot ρ)
    {t : V → ℝ} (ht : ∀ v, 0 < t v) (mark : V → (V → E) → Prop)
    (hloc : ∀ v (x y : V → E),
      (∀ i ≤ T.depth v, x (T.ancAt v i) = y (T.ancAt v i)) → (mark v x ↔ mark v y)) :
    HasWeightedDual (treeSearch mark) t (T.recCost t ρ) :=
  T.hasWeightedDual_treeSearch_recCost ht hρ mark hloc

theorem acceptance_optimal {ρ : V} (hρ : T.IsRoot ρ) {t : V → ℝ} (ht : ∀ v, 0 < t v) :
    (∀ lam : V → ℝ, (∀ w, 0 < lam w) → T.recCost t ρ ^ 2 ≤ T.pathMax ρ lam * energy t lam)
    ∧ (∃ lam : V → ℝ, (∀ w, 0 < lam w) ∧ T.pathMax ρ lam * energy t lam = T.recCost t ρ ^ 2)
    ∧ T.optValue ρ t = T.recCost t ρ ^ 2 :=
  ⟨fun lam h => T.recCost_sq_le_pathMax_mul_energy ht hρ lam h, T.exists_weights_optimal ht hρ,
   T.optValue_eq ht hρ⟩

/-- The depth bound, old and new; the old declaration is untouched. -/
theorem acceptance_depth {E : Type} [Fintype E] [DecidableEq E] [Nonempty V] {ρ : V}
    (hρ : T.IsRoot ρ) {t : V → ℝ} (ht : ∀ v, 0 < t v) {d : ℕ} (hd : ∀ v, T.depth v ≤ d)
    (mark : V → (V → E) → Prop)
    (hloc : ∀ v (x y : V → E),
      (∀ i ≤ T.depth v, x (T.ancAt v i) = y (T.ancAt v i)) → (mark v x ↔ mark v y)) :
    T.recCost t ρ ≤ Real.sqrt (((d : ℝ) + 1) * ∑ w, t w ^ 2)
    ∧ HasWeightedDual (treeSearch mark) t (Real.sqrt (((d : ℝ) + 1) * ∑ w, t w ^ 2)) :=
  ⟨T.recCost_le_sqrt_depth_sqSum ht hρ hd, T.hasWeightedDual_treeSearch_sqSum d mark hd hloc t ht⟩

variable {ι σ X : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype X]
  [DecidableEq X]

/-- The promise/heterogeneous certificate and the quantum endpoints, at full generality. -/
theorem acceptance_quantum {Γ : V → Type} [∀ v, Fintype (Γ v)] [∀ v, DecidableEq (Γ v)] {ρ : V}
    (hρ : T.IsRoot ρ) {t : V → ℝ} (ht : ∀ v, 0 < t v) (read : X → ι → σ)
    (cell : ∀ v, X → Γ v) (mark : V → X → Prop) [DecidablePred fun x : X => ∃ v, mark v x]
    (hcell : ∀ v, HasDualOn read (cell v) (t v))
    (hloc : ∀ v x y, (∀ w ∈ T.path v, cell w x = cell w y) → (mark v x ↔ mark v y)) :
    HasDualOn read (fun x => decide (∃ v, mark v x)) (T.recCost t ρ)
    ∧ (qQueryOn read (fun x => decide (∃ v, mark v x)) (1 / 3) : ℝ)
        ≤ 8192 * (1 + T.recCost t ρ)
    ∧ (qQueryOn read (fun x => decide (∃ v, mark v x)) (1 / 3) : ℝ) ≤ 16384 * T.recCost t ρ :=
  ⟨T.hasDualOn_treeSearch_recCost hρ ht read cell mark hcell hloc,
   T.qQueryOn_third_treeSearch hρ ht read cell mark hcell hloc,
   T.qQueryOn_third_treeSearch_hom hρ ht read cell mark hcell hloc⟩

/-! ## 2. One vertex, chains, stars -/

/-- The one-vertex tree. -/
def one : AncTree Unit where
  depth := fun _ => 0
  ancAt := fun _ _ => ()
  depth_ancAt := fun _ i hi => by simp at hi; simp [hi]
  ancAt_self := fun _ => rfl
  ancAt_ancAt := fun _ _ _ _ _ => rfl

example (t : Unit → ℝ) : one.recCost t () = t () := one.recCost_leaf (by decide)

example : one.IsRoot () := fun _ => rfl

/-- A chain costs the sum of its weights; a star adds the root of the sum of squares. -/
example (t : V → ℝ) (ht : ∀ v, 0 ≤ t v) (hchain : ∀ v, (T.children v).card ≤ 1) (v : V) :
    T.recCost t v = ∑ w ∈ T.descendants v, t w := T.recCost_chain ht hchain v

example (t : V → ℝ) {ρ : V} (hleaf : ∀ u ∈ T.children ρ, T.children u = ∅) :
    T.recCost t ρ = t ρ + Real.sqrt (∑ u ∈ T.children ρ, t u ^ 2) := T.recCost_star t hleaf

/-! ## 3. Unequal costs: `2; 3, 4` -/

namespace Three

/-- Root `0` with leaf children `1, 2`. -/
def tree : AncTree (Fin 3) where
  depth := ![0, 1, 1]
  ancAt := fun v i => if i = 0 then 0 else v
  depth_ancAt := by
    intro v i hi
    have hi1 : i ≤ 1 := le_trans hi (by fin_cases v <;> decide)
    interval_cases i <;> revert v hi <;> decide
  ancAt_self := by decide
  ancAt_ancAt := by
    intro v i j hj hi
    have hi1 : i ≤ 1 := le_trans hi (by fin_cases v <;> decide)
    interval_cases i <;> interval_cases j <;> revert v hi hj <;> decide

lemma isRoot : tree.IsRoot 0 := fun _ => rfl

lemma children_zero : tree.children 0 = {1, 2} := by decide
lemma children_one : tree.children 1 = ∅ := by decide
lemma children_two : tree.children 2 = ∅ := by decide

/-- The costs `2, 3, 4`. -/
noncomputable def t : Fin 3 → ℝ := ![2, 3, 4]

lemma t_pos : ∀ v, 0 < t v := by intro v; fin_cases v <;> simp [t]

lemma sqrt25 : Real.sqrt (3 ^ 2 + 4 ^ 2) = 5 := by
  rw [show (3 : ℝ) ^ 2 + 4 ^ 2 = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- **`C = 7`.** -/
theorem recCost_three : tree.recCost t 0 = 7 := by
  rw [recCost_eq, children_zero, sum_pair (by decide), tree.recCost_leaf children_one,
    tree.recCost_leaf children_two]
  simp only [t, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [sqrt25]; norm_num

lemma resid_three : tree.resid t 0 = 5 := by
  rw [resid, children_zero, sum_pair (by decide), tree.recCost_leaf children_one,
    tree.recCost_leaf children_two]
  simp only [t, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  exact sqrt25

/-- **The normalized weights**: `2/7` at the root and `5/7` at each child. -/
theorem optWeights_three :
    tree.optWeights t 0 0 = 2 / 7 ∧ tree.optWeights t 0 1 = 5 / 7 ∧ tree.optWeights t 0 2 = 5 / 7 := by
  have h1 : (1 : Fin 3) ∈ tree.children 0 := by rw [children_zero]; decide
  have h2 : (2 : Fin 3) ∈ tree.children 0 := by rw [children_zero]; decide
  refine ⟨?_, ?_, ?_⟩
  · rw [optWeights, optW_self, recCost_three]; simp [t]
  · rw [optWeights, tree.optW_child t 1 h1 (tree.self_mem_descendants 1), optW_self,
      resid_three, recCost_three, tree.recCost_leaf children_one]
    simp [t]
  · rw [optWeights, tree.optW_child t 1 h2 (tree.self_mem_descendants 2), optW_self,
      resid_three, recCost_three, tree.recCost_leaf children_two]
    simp [t]

/-- **The energy is `49 = C²`.** -/
theorem energy_three : energy t (tree.optWeights t 0) = 49 := by
  obtain ⟨h0, h1, h2⟩ := optWeights_three
  rw [energy, Fin.sum_univ_three, h0, h1, h2]
  simp [t]; norm_num

end Three

/-! ## 4. Semantics -/

section Semantics

/-- Cells are coordinates of a Boolean table; the marking at `v` reads the **root cell and the
cell at `v`**. -/
def markRoot (v : Fin 3) (x : Fin 3 → Bool) : Prop := x 0 = true ∧ x v = true

instance (v : Fin 3) : DecidablePred (markRoot v) := fun x => by unfold markRoot; infer_instance

lemma markRoot_local (v : Fin 3) (x y : Fin 3 → Bool)
    (h : ∀ w ∈ Three.tree.path v, x w = y w) : markRoot v x ↔ markRoot v y := by
  have h0 : x 0 = y 0 := h 0 (Three.tree.mem_path.2 ⟨0, Nat.zero_le _, Three.isRoot v⟩)
  have hv : x v = y v := h v (Three.tree.self_mem_path v)
  simp [markRoot, h0, hv]

/-- The certificate for a marking that reads an ancestor cell; cells are the coordinates. -/
theorem semantic_certificate :
    HasDual (fun x : Fin 3 → Bool => decide (∃ v, markRoot v x))
      (Three.tree.recCost (fun _ => (2 : ℝ)) 0) :=
  Three.tree.hasDual_treeSearch_recCost Three.isRoot (fun _ => two_pos) (fun v x => x v) markRoot
    (fun v => hasDual_ofCoord v id) markRoot_local

/-- A positive and a negative input whose first difference is at the **root**, a strict
ancestor of the marked vertex `1`. -/
example : (∃ v, markRoot v ![true, true, false]) ∧ ¬ (∃ v, markRoot v ![false, true, false]) := by
  refine ⟨⟨1, by decide⟩, ?_⟩
  rintro ⟨v, hv⟩
  exact absurd hv.1 (by decide)

/-- Identical query supports for every cell: all cells read coordinate `0`. -/
example (mark : Fin 3 → (Fin 3 → Bool) → Prop) [DecidablePred fun x : Fin 3 → Bool => ∃ v, mark v x]
    (hloc : ∀ v x y, (∀ w ∈ Three.tree.path v, x 0 = y 0) → (mark v x ↔ mark v y)) :
    HasDual (fun x : Fin 3 → Bool => decide (∃ v, mark v x))
      (Three.tree.recCost (fun _ => (2 : ℝ)) 0) :=
  Three.tree.hasDual_treeSearch_recCost Three.isRoot (fun _ => two_pos) (fun _ x => x 0) mark
    (fun _ => hasDual_ofCoord 0 id) hloc

/-- **Distinct cell-output types** `Γ v = Bool × Fin (v+1)`. -/
example (mark : Fin 3 → (Fin 3 → Bool) → Prop) [DecidablePred fun x : Fin 3 → Bool => ∃ v, mark v x]
    (hloc : ∀ v x y, (∀ w ∈ Three.tree.path v, ((x w, (0 : Fin (w.val + 1))) : Bool × Fin (w.val + 1))
      = (y w, 0)) → (mark v x ↔ mark v y)) :
    HasDualOn (id : (Fin 3 → Bool) → Fin 3 → Bool) (fun x => decide (∃ v, mark v x))
      (Three.tree.recCost (fun _ => (2 : ℝ)) 0) :=
  Three.tree.hasDualOn_treeSearch_recCost (Γ := fun v => Bool × Fin (v.val + 1)) Three.isRoot
    (fun _ => two_pos) id (fun v x => (x v, 0)) mark
    (fun v => (hasDual_ofCoord v (fun b => ((b, 0) : Bool × Fin (v.val + 1)))).hasDualOn) hloc

/-- **A proper promise with a noninjective observation map**: four inputs, one observed bit;
cells read that bit, and no cell dual is demanded outside the promise. -/
def read4 : Fin 4 → Fin 1 → Bool := fun x _ => decide (x.val < 2)

example (mark : Fin 3 → Fin 4 → Prop) [DecidablePred fun x : Fin 4 => ∃ v, mark v x]
    (hloc : ∀ v x y, (∀ w ∈ Three.tree.path v, read4 x 0 = read4 y 0) → (mark v x ↔ mark v y)) :
    HasDualOn read4 (fun x => decide (∃ v, mark v x)) (Three.tree.recCost (fun _ => (2 : ℝ)) 0) :=
  Three.tree.hasDualOn_treeSearch_recCost' Three.isRoot (fun _ => two_pos) read4
    (fun _ x => read4 x 0) mark
    (fun _ => (hasDual_ofCoord (0 : Fin 1) (id : Bool → Bool)).hasDualOn.comap read4) hloc

/-- **An empty promise**: the certificate and the homogeneous quantum bound hold vacuously. -/
example (mark : Fin 3 → Empty → Prop) [DecidablePred fun x : Empty => ∃ v, mark v x] :
    HasDualOn (fun x : Empty => (x.elim : Fin 1 → Bool)) (fun x => decide (∃ v, mark v x))
      (Three.tree.recCost (fun _ => (1 : ℝ)) 0)
    ∧ (qQueryOn (fun x : Empty => (x.elim : Fin 1 → Bool)) (fun x => decide (∃ v, mark v x))
        (1 / 3) : ℝ) ≤ 16384 * Three.tree.recCost (fun _ => (1 : ℝ)) 0 := by
  have hcell : ∀ v : Fin 3, HasDualOn (fun x : Empty => (x.elim : Fin 1 → Bool))
      (fun x : Empty => (x.elim : Bool)) (1 : ℝ) := fun _ =>
    (hasDualOn_of_const (fun x : Empty => (x.elim : Fin 1 → Bool))
      (f := fun x : Empty => (x.elim : Bool)) (fun x _ => x.elim)).mono one_pos.le
  exact ⟨Three.tree.hasDualOn_treeSearch_recCost' Three.isRoot (fun _ => one_pos) _
      (fun _ x => x.elim) mark hcell fun v x => x.elim,
    Three.tree.qQueryOn_third_treeSearch_hom (Γ := fun _ => Bool) Three.isRoot (fun _ => one_pos) _
      (fun _ x => x.elim) mark hcell fun v x => x.elim⟩

/-- Always marked and never marked: constant decisions cost no queries, and the general theorem
still applies. -/
example :
    qQueryOn (id : (Fin 3 → Bool) → Fin 3 → Bool) (fun x => decide (∃ v : Fin 3, True)) (1 / 3) = 0
    ∧ qQueryOn (id : (Fin 3 → Bool) → Fin 3 → Bool) (fun x => decide (∃ v : Fin 3, False)) (1 / 3) = 0
    ∧ HasDual (fun x : Fin 3 → Bool => decide (∃ v : Fin 3, False))
        (Three.tree.recCost (fun _ => (2 : ℝ)) 0) :=
  ⟨qQueryOn_eq_zero_of_const _ (fun _ _ => rfl) (by norm_num),
   qQueryOn_eq_zero_of_const _ (fun _ _ => rfl) (by norm_num),
   Three.tree.hasDual_treeSearch_recCost Three.isRoot (fun _ => two_pos) (fun v x => x v)
    (fun _ _ => False) (fun v => hasDual_ofCoord v id) fun _ _ _ _ => Iff.rfl⟩

/-- Marking restricted to a subset `S` of vertices. -/
example (S : Finset (Fin 3)) :
    HasDual (fun x : Fin 3 → Bool => decide (∃ v, v ∈ S ∧ markRoot v x))
      (Three.tree.recCost (fun _ => (2 : ℝ)) 0) :=
  Three.tree.hasDual_treeSearch_recCost Three.isRoot (fun _ => two_pos) (fun v x => x v)
    (fun v x => v ∈ S ∧ markRoot v x) (fun v => hasDual_ofCoord v id)
    fun v x y h => and_congr_right fun _ => markRoot_local v x y h

end Semantics

/-! ## 5. The perfect binary tree -/

/-- `C_ρ = ∑_{h ≤ d} (√2)^h ≤ 3√N`, `N = 2^{d+1} − 1`: the exact root cost beats the generic
depth bound `√((d+1)·N)`. -/
theorem acceptance_binary {d : ℕ} (hd : ∀ v, T.depth v ≤ d)
    (htwo : ∀ v, T.depth v < d → (T.children v).card = 2)
    (hleaf : ∀ v, T.depth v = d → T.children v = ∅) {ρ : V} (hρ : T.IsRoot ρ) :
    T.recCost (fun _ => (1 : ℝ)) ρ = sqrtTwoSum d
    ∧ T.recCost (fun _ => (1 : ℝ)) ρ ≤ 3 * Real.sqrt ((2 : ℝ) ^ (d + 1) - 1) := by
  have h0 : T.depth ρ = 0 := by
    have := T.depth_ancAt ρ 0 (Nat.zero_le _); rwa [hρ ρ] at this
  have h := T.recCost_binary hd htwo hleaf ρ
  rw [h0, Nat.sub_zero] at h
  exact ⟨h, h ▸ sqrtTwoSum_le_three_sqrt d⟩

/-! ## 6. Unequal leaf depths and a genuine promise -/

namespace Uneven

/-- Root `0`, leaf `1` at depth one, `2 → 3` with the leaf `3` at depth two. -/
def tree : AncTree (Fin 4) where
  depth := ![0, 1, 1, 2]
  ancAt := fun v i => if i = 0 then 0 else if i = 1 ∧ v = 3 then 2 else v
  depth_ancAt := by
    intro v i hi
    have hi2 : i ≤ 2 := le_trans hi (by fin_cases v <;> decide)
    interval_cases i <;> revert v hi <;> decide
  ancAt_self := by decide
  ancAt_ancAt := by
    intro v i j hj hi
    have hi2 : i ≤ 2 := le_trans hi (by fin_cases v <;> decide)
    interval_cases i <;> interval_cases j <;> revert v hi hj <;> decide

lemma isRoot : tree.IsRoot 0 := fun _ => rfl
lemma children_zero : tree.children 0 = {1, 2} := by decide
lemma children_one : tree.children 1 = ∅ := by decide
lemma children_two : tree.children 2 = {3} := by decide
lemma children_three : tree.children 3 = ∅ := by decide

/-- **`C_0 = 1 + √5`** with unit costs: the leaves are at depths `1` and `2`. -/
theorem recCost_uneven : tree.recCost (fun _ => (1 : ℝ)) 0 = 1 + Real.sqrt 5 := by
  have h1 := tree.recCost_leaf (t := fun _ => (1 : ℝ)) children_one
  have h3 := tree.recCost_leaf (t := fun _ => (1 : ℝ)) children_three
  have h2 : tree.recCost (fun _ => (1 : ℝ)) 2 = 2 := by
    rw [recCost_eq, children_two, Finset.sum_singleton, h3]
    norm_num
  rw [recCost_eq, children_zero, Finset.sum_pair (by decide), h1, h2]
  norm_num

/-- A marking at the deep leaf that reads the root cell. -/
example : HasDual (fun x : Fin 4 → Bool => decide (∃ v : Fin 4, v = 3 ∧ x 0 = true ∧ x 3 = true))
    (tree.recCost (fun _ => (2 : ℝ)) 0) := by
  apply tree.hasDual_treeSearch_recCost isRoot (fun _ => two_pos) (fun v x => x v)
    (fun v x => v = 3 ∧ x 0 = true ∧ x 3 = true) (fun v => hasDual_ofCoord v id)
  intro v x y h
  by_cases hv : v = 3
  · subst hv
    have h0 := h 0 (tree.mem_path.2 ⟨0, Nat.zero_le _, isRoot 3⟩)
    have h3 := h 3 (tree.self_mem_path 3)
    simp [h0, h3]
  · simp [hv]

/-- Four inputs, two observed bits: the image is `{00, 11}`, a proper subset of the cube,
and the map is noninjective. -/
def properRead (x : Fin 4) (_ : Fin 2) : Bool := decide (x.val < 2)

example : properRead (0 : Fin 4) = properRead 1 ∧ (0 : Fin 4) ≠ 1 := ⟨funext fun _ => rfl, by decide⟩

example : ¬ ∃ x, properRead x = ![false, true] := by
  rintro ⟨x, hx⟩
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  simp only [properRead, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
  exact absurd (h0.symm.trans h1) (by decide)

def mark (v : Fin 4) (x : Fin 4) : Prop := v = 3 ∧ properRead x 0 = true

instance (v : Fin 4) : DecidablePred (mark v) := fun x => by unfold mark; infer_instance

/-- The certificate on the genuine promise: cells read the observed bit, their duals come from
the coordinate dual pulled back along `properRead`. -/
example : HasDualOn properRead (fun x => decide (∃ v, mark v x))
    (tree.recCost (fun _ => (2 : ℝ)) 0) := by
  apply tree.hasDualOn_treeSearch_recCost' isRoot (fun _ => two_pos) properRead
    (fun _ x => properRead x 0) mark
    (fun _ => (hasDual_ofCoord (0 : Fin 2) (id : Bool → Bool)).hasDualOn.comap properRead)
  intro v x y h
  have hv := h v (tree.self_mem_path v)
  simp only [mark, hv]

/-- Empty promise and **empty cell-output types**: no inhabitant of `Γ v` is needed. -/
example : HasDualOn (fun x : Empty => (x.elim : Fin 1 → Bool))
    (fun _x : Empty => decide (∃ _v : Fin 4, True)) (tree.recCost (fun _ => (1 : ℝ)) 0) := by
  apply tree.hasDualOn_treeSearch_recCost (Γ := fun _ => Empty) isRoot (fun _ => one_pos)
    (fun x : Empty => x.elim) (fun _ x => x.elim) (fun _ _ => True)
  · intro v
    exact (hasDualOn_of_const (fun x : Empty => (x.elim : Fin 1 → Bool))
      (f := fun x : Empty => (x.elim : Empty)) (fun x _ => x.elim)).mono one_pos.le
  · intro v x; exact x.elim

end Uneven

end TreeSearchAcceptance
end QuantumQueryComplexity
