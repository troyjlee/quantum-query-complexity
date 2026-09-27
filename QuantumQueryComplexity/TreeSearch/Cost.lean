import QuantumQueryComplexity.TreeSearch

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Finite-tree geometry and the recursive cost

A compatible layer over `AncTree`: a common root (`IsRoot`), children, descendants, the
maximum depth, and the **recursive cost**

    C_v = t_v + √(∑_{u child of v} C_u²)             (`recCost_eq`)

defined by a fuelled helper on the remaining depth and exported through the exact recurrence.

The combinatorial content is the partition of a subtree into its root and its child subtrees
(`sum_descendants`) and of a local root path into the subtree root and a path in exactly one
child subtree (`sum_localPath_succ`), for arbitrary finite branching and unequal leaf depths.
`recCost_pos`, `recCost_leaf`, and `sum_path_le_recCost` are the scalar facts used later.
-/

namespace QuantumQueryComplexity

namespace AncTree

open Finset

variable {V : Type} [DecidableEq V] [Fintype V] (T : AncTree V)

/-- `ρ` is the common root: the depth-`0` ancestor of every vertex. -/
def IsRoot (ρ : V) : Prop := ∀ v, T.ancAt v 0 = ρ

lemma mem_path_iff {v w : V} : v ∈ T.path w ↔ T.depth v ≤ T.depth w ∧ T.ancAt w (T.depth v) = v := by
  rw [mem_path]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [T.depth_ancAt w i hi]
    exact ⟨hi, rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨T.depth v, h1, h2⟩

/-- The children of `v`. -/
def children (v : V) : Finset V :=
  univ.filter fun u => T.depth u = T.depth v + 1 ∧ T.ancAt u (T.depth v) = v

lemma mem_children {u v : V} :
    u ∈ T.children v ↔ T.depth u = T.depth v + 1 ∧ T.ancAt u (T.depth v) = v := by
  simp [children]

/-- The descendants of `v` (including `v`). -/
def descendants (v : V) : Finset V := univ.filter fun w => v ∈ T.path w

lemma mem_descendants {v w : V} : w ∈ T.descendants v ↔ v ∈ T.path w := by simp [descendants]

lemma self_mem_descendants (v : V) : v ∈ T.descendants v :=
  T.mem_descendants.2 (T.self_mem_path v)

/-- The maximum depth. -/
def maxDepth : ℕ := univ.sup T.depth

lemma depth_le_maxDepth (v : V) : T.depth v ≤ T.maxDepth := Finset.le_sup (mem_univ v)

lemma depth_child {u v : V} (hu : u ∈ T.children v) : T.depth u = T.depth v + 1 :=
  (T.mem_children.1 hu).1

lemma children_eq_empty_of_maxDepth {v : V} (hv : T.maxDepth ≤ T.depth v) :
    T.children v = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro u hu
  have := T.depth_le_maxDepth u
  rw [T.depth_child hu] at this
  omega

/-- The child of `v` on the way to a proper descendant `w`. -/
lemma exists_child_of_mem_descendants {v w : V} (hw : w ∈ T.descendants v) (hne : w ≠ v) :
    ∃ u ∈ T.children v, w ∈ T.descendants u := by
  rw [mem_descendants, mem_path_iff] at hw
  obtain ⟨hd, ha⟩ := hw
  have hlt : T.depth v < T.depth w := by
    rcases lt_or_eq_of_le hd with h | h
    · exact h
    · exfalso; apply hne; rw [← ha, h, T.ancAt_self]
  refine ⟨T.ancAt w (T.depth v + 1), ?_, ?_⟩
  · rw [mem_children, T.depth_ancAt w _ hlt, T.ancAt_ancAt w _ _ (Nat.le_succ _) hlt]
    exact ⟨rfl, ha⟩
  · rw [mem_descendants, mem_path_iff, T.depth_ancAt w _ hlt]
    exact ⟨hlt, rfl⟩

/-- A vertex lies in the subtree of at most one child. -/
lemma child_unique {v u u' w : V} (hu : u ∈ T.children v) (hu' : u' ∈ T.children v)
    (hw : w ∈ T.descendants u) (hw' : w ∈ T.descendants u') : u = u' := by
  rw [mem_descendants, mem_path_iff] at hw hw'
  rw [← hw.2, ← hw'.2, T.depth_child hu, T.depth_child hu']

lemma notMem_descendants_child {v u : V} (hu : u ∈ T.children v) : v ∉ T.descendants u := by
  intro h
  rw [mem_descendants, mem_path_iff] at h
  have := T.depth_child hu
  omega

lemma descendants_child_subset {v u : V} (hu : u ∈ T.children v) :
    T.descendants u ⊆ T.descendants v := by
  intro w hw
  rw [mem_descendants, mem_path_iff] at hw ⊢
  obtain ⟨hd, ha⟩ := hw
  have hdu := T.depth_child hu
  have hav := (T.mem_children.1 hu).2
  refine ⟨by omega, ?_⟩
  rw [← T.ancAt_ancAt w (T.depth u) (T.depth v) (by omega) hd, ha, hav]

/-- **The subtree partition**: `v` and the child subtrees. -/
theorem descendants_eq (v : V) :
    T.descendants v = insert v ((T.children v).biUnion T.descendants) := by
  ext w
  rw [mem_insert, mem_biUnion]
  constructor
  · intro hw
    by_cases h : w = v
    · exact Or.inl h
    · exact Or.inr (T.exists_child_of_mem_descendants hw h)
  · rintro (rfl | ⟨u, hu, hw⟩)
    · exact T.self_mem_descendants w
    · exact T.descendants_child_subset hu hw

theorem sum_descendants {M : Type} [AddCommMonoid M] (v : V) (f : V → M) :
    ∑ w ∈ T.descendants v, f w = f v + ∑ u ∈ T.children v, ∑ w ∈ T.descendants u, f w := by
  rw [descendants_eq, sum_insert, sum_biUnion]
  · intro u hu u' hu' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro w hw hw'
    exact hne (T.child_unique hu hu' hw hw')
  · rw [mem_biUnion]
    rintro ⟨u, hu, hw⟩
    exact T.notMem_descendants_child hu hw

/-- The local root path from `v` down to its descendant `w`. -/
def localPath (v w : V) : Finset V := (T.path w).filter fun a => T.depth v ≤ T.depth a

lemma localPath_self (v : V) : T.localPath v v = {v} := by
  ext a
  rw [localPath, mem_filter, mem_singleton, mem_path_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have : T.depth a = T.depth v := le_antisymm h1 h3
    rw [← h2, this, T.ancAt_self]
  · rintro rfl
    exact ⟨⟨le_rfl, T.ancAt_self a⟩, le_rfl⟩

lemma localPath_eq_path {ρ : V} (hρ : T.IsRoot ρ) (w : V) : T.localPath ρ w = T.path w := by
  have h0 : T.depth ρ = 0 := by
    have := T.depth_ancAt ρ 0 (Nat.zero_le _)
    rwa [hρ ρ] at this
  ext a
  rw [localPath, mem_filter, h0]
  exact ⟨fun h => h.1, fun h => ⟨h, Nat.zero_le _⟩⟩

lemma descendants_eq_univ {ρ : V} (hρ : T.IsRoot ρ) : T.descendants ρ = univ := by
  ext w
  rw [mem_descendants, mem_path]
  exact ⟨fun _ => mem_univ w, fun _ => ⟨0, Nat.zero_le _, hρ w⟩⟩

/-- **The local path partition**: the subtree root and a local path in the child subtree. -/
theorem localPath_succ {v u w : V} (hu : u ∈ T.children v) (hw : w ∈ T.descendants u) :
    T.localPath v w = insert v (T.localPath u w) ∧ v ∉ T.localPath u w := by
  have hdu := T.depth_child hu
  have hvw : v ∈ T.path w := T.mem_descendants.1 (T.descendants_child_subset hu hw)
  constructor
  · ext a
    rw [localPath, localPath, mem_insert, mem_filter, mem_filter]
    constructor
    · rintro ⟨ha, hd⟩
      by_cases hav : a = v
      · exact Or.inl hav
      · refine Or.inr ⟨ha, ?_⟩
        rw [mem_path_iff] at ha hvw
        have hlt : T.depth v < T.depth a := by
          rcases lt_or_eq_of_le hd with h | h
          · exact h
          · exfalso; apply hav; rw [← ha.2, ← h, hvw.2]
        omega
    · rintro (rfl | ⟨ha, hd⟩)
      · exact ⟨hvw, le_rfl⟩
      · exact ⟨ha, by omega⟩
  · rw [localPath, mem_filter]
    rintro ⟨_, h⟩
    omega

theorem sum_localPath_succ {v u w : V} (hu : u ∈ T.children v) (hw : w ∈ T.descendants u)
    (f : V → ℝ) : ∑ a ∈ T.localPath v w, f a = f v + ∑ a ∈ T.localPath u w, f a := by
  obtain ⟨h1, h2⟩ := T.localPath_succ hu hw
  rw [h1, sum_insert h2]

/-! ## The recursive cost -/

/-- The fuelled recursion: `fuel` is the remaining depth allowed. -/
noncomputable def recCostF (t : V → ℝ) : ℕ → V → ℝ
  | 0, v => t v
  | n + 1, v => t v + Real.sqrt (∑ u ∈ T.children v, (recCostF t n u) ^ 2)

/-- **The recursive cost** `C_v`. -/
noncomputable def recCost (t : V → ℝ) (v : V) : ℝ := T.recCostF t (T.maxDepth - T.depth v) v

/-- **The exact recurrence** `C_v = t_v + √(∑_{u child} C_u²)`. -/
theorem recCost_eq (t : V → ℝ) (v : V) :
    T.recCost t v = t v + Real.sqrt (∑ u ∈ T.children v, (T.recCost t u) ^ 2) := by
  rcases Nat.lt_or_ge (T.depth v) T.maxDepth with h | h
  · obtain ⟨m, hm⟩ : ∃ m, T.maxDepth - T.depth v = m + 1 := ⟨T.maxDepth - T.depth v - 1, by omega⟩
    rw [recCost, hm, recCostF]
    congr 2
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [recCost, T.depth_child hu, show T.maxDepth - (T.depth v + 1) = m by omega]
  · rw [recCost, Nat.sub_eq_zero_of_le h, recCostF, T.children_eq_empty_of_maxDepth h,
      Finset.sum_empty, Real.sqrt_zero, add_zero]

/-- The square root of the children's energy. -/
noncomputable def resid (t : V → ℝ) (v : V) : ℝ :=
  Real.sqrt (∑ u ∈ T.children v, (T.recCost t u) ^ 2)

lemma recCost_eq_resid (t : V → ℝ) (v : V) : T.recCost t v = t v + T.resid t v := T.recCost_eq t v

lemma resid_nonneg (t : V → ℝ) (v : V) : 0 ≤ T.resid t v := Real.sqrt_nonneg _

lemma resid_sq (t : V → ℝ) (v : V) : T.resid t v ^ 2 = ∑ u ∈ T.children v, (T.recCost t u) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- A leaf costs its own weight. -/
theorem recCost_leaf {t : V → ℝ} {v : V} (hv : T.children v = ∅) : T.recCost t v = t v := by
  rw [recCost_eq, hv, Finset.sum_empty, Real.sqrt_zero, add_zero]

theorem recCost_pos {t : V → ℝ} (ht : ∀ v, 0 < t v) (v : V) : 0 < T.recCost t v := by
  rw [recCost_eq]
  exact add_pos_of_pos_of_nonneg (ht v) (Real.sqrt_nonneg _)

theorem le_recCost {t : V → ℝ} (v : V) : t v ≤ T.recCost t v := by
  rw [recCost_eq]
  linarith [Real.sqrt_nonneg (∑ u ∈ T.children v, (T.recCost t u) ^ 2)]

/-- A child's cost is at most the residual of its parent. -/
theorem recCost_child_le_resid {t : V → ℝ} {u v : V} (hu : u ∈ T.children v) :
    T.recCost t u ≤ T.resid t v := by
  rw [resid]
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (fun w _ => sq_nonneg (T.recCost t w)) hu

/-- The residual is positive when a child exists. -/
theorem resid_pos {t : V → ℝ} (ht : ∀ v, 0 < t v) {v : V} (hv : (T.children v).Nonempty) :
    0 < T.resid t v := by
  obtain ⟨u, hu⟩ := hv
  exact lt_of_lt_of_le (T.recCost_pos ht u) (T.recCost_child_le_resid hu)

/-- The induction principle on the remaining depth. -/
theorem induction_children {P : V → Prop}
    (step : ∀ v, (∀ u ∈ T.children v, P u) → P v) (v : V) : P v := by
  suffices h : ∀ n, ∀ v, T.maxDepth - T.depth v ≤ n → P v from h _ v le_rfl
  intro n
  induction n with
  | zero =>
      intro v hv
      refine step v fun u hu => ?_
      have := T.depth_le_maxDepth u
      rw [T.depth_child hu] at this
      omega
  | succ n ih =>
      intro v hv
      refine step v fun u hu => ih u ?_
      rw [T.depth_child hu]
      omega

/-- **The local path sum is at most the subtree cost.** -/
theorem sum_localPath_le_recCost {t : V → ℝ} (ht : ∀ v, 0 < t v) (v : V) :
    ∀ w ∈ T.descendants v, ∑ a ∈ T.localPath v w, t a ≤ T.recCost t v := by
  induction v using T.induction_children with
  | step v ih =>
    intro w hw
    by_cases hne : w = v
    · subst hne
      rw [T.localPath_self, sum_singleton]
      exact T.le_recCost w
    · obtain ⟨u, hu, hwu⟩ := T.exists_child_of_mem_descendants hw hne
      rw [T.sum_localPath_succ hu hwu, recCost_eq_resid]
      have := ih u hu w hwu
      have := T.recCost_child_le_resid (t := t) hu
      linarith

/-- **A root path sum is at most the root cost.** -/
theorem sum_path_le_recCost {t : V → ℝ} (ht : ∀ v, 0 < t v) {ρ : V} (hρ : T.IsRoot ρ) (w : V) :
    ∑ a ∈ T.path w, t a ≤ T.recCost t ρ := by
  rw [← T.localPath_eq_path hρ]
  exact T.sum_localPath_le_recCost ht ρ w (by rw [T.descendants_eq_univ hρ]; exact mem_univ w)

end AncTree

end QuantumQueryComplexity
