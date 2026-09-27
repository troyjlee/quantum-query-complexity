import QuantumQueryComplexity.HasDual
import QuantumQueryComplexity.FirstDiff
import Mathlib.Data.Nat.Log

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# An adaptive decision-tree dual

`HasDual.combine` evaluates *every* subproblem and pays `2 ∑ₚ cₚ`; the `Scan`
API fixes the query order in advance.  Neither expresses **binary search**,
where which subproblem is looked at next depends on the answers so far.  This
file supplies the missing component: a finite decision tree over Boolean queries
whose dual costs twice the most expensive root-to-leaf path — *not* twice the
total over all nodes.

The whole construction is one hand-built dual, `branchDual`, for a single query
node, applied by structural induction on the tree.  For inputs `z, y` the two
computation paths agree until they first diverge, and at the divergence node the
queried bit differs; `branchDual` puts the `[output differs]` factor exactly
there.  At a node querying `p` the dimension splits three ways:

* a copy of the `false` subtree's solution, switched on when `z p = false` and
  masked off at coordinate `p`;
* a copy of the `true` subtree's solution, likewise;
* one `Option O` block living entirely on coordinate `p`, carrying the
  `QuantumQueryComplexity/FirstDiff.lean` factorization `⟨φ a, ψ b⟩ = [a ≠ b]`.

If `z p = y p` the third block is killed by the coordinate mask and the matching
subtree block reproduces its own constraint verbatim; if `z p ≠ y p` the two
subtree blocks annihilate each other — one has `u = 0`, the other `v = 0` — and
the third block delivers the `1`.  Only one subtree block is ever charged for,
so the cost recurses as `2 cₚ + max V₀ V₁`: a maximum, not a sum.  That is the
whole point, and it is also why a query label may repeat on a path at no risk —
the two occurrences live in different summands of the dimension type.

`QueryTree.hasDual_shared` then composes the tree with subproblems reading a
*shared* input, which is what a search over the prefixes of one word needs, and
`boundaryTree` is binary search itself: `Nat.clog 2 (hi - lo)` queries locate a
sign change, with no monotonicity hypothesis anywhere.
-/

namespace QuantumQueryComplexity

/-! ## Trees -/

/-- A decision tree querying Boolean labels drawn from `P` and returning a value
in `O`. -/
inductive QueryTree (P O : Type) where
  /-- Stop and answer. -/
  | leaf : O → QueryTree P O
  /-- Query the label, then continue in the subtree named by the answer. -/
  | query : P → (Bool → QueryTree P O) → QueryTree P O

namespace QueryTree

variable {P O O' : Type}

/-- Running the tree on an assignment of the labels. -/
def eval : QueryTree P O → (P → Bool) → O
  | leaf o, _ => o
  | query p k, z => (k (z p)).eval z

@[simp] lemma eval_leaf (o : O) (z : P → Bool) :
    (leaf o : QueryTree P O).eval z = o := rfl

@[simp] lemma eval_query (p : P) (k : Bool → QueryTree P O) (z : P → Bool) :
    (query p k).eval z = (k (z p)).eval z := rfl

/-- The number of queries on the longest root-to-leaf path. -/
def depth : QueryTree P O → ℕ
  | leaf _ => 0
  | query _ k => max (k false).depth (k true).depth + 1

@[simp] lemma depth_leaf (o : O) : (leaf o : QueryTree P O).depth = 0 := rfl

@[simp] lemma depth_query (p : P) (k : Bool → QueryTree P O) :
    (query p k).depth = max (k false).depth (k true).depth + 1 := rfl

/-- The largest total weight of the labels queried on a root-to-leaf path. -/
def maxPathCost (c : P → ℝ) : QueryTree P O → ℝ
  | leaf _ => 0
  | query p k => c p + max ((k false).maxPathCost c) ((k true).maxPathCost c)

@[simp] lemma maxPathCost_leaf (c : P → ℝ) (o : O) :
    (leaf o : QueryTree P O).maxPathCost c = 0 := rfl

@[simp] lemma maxPathCost_query (c : P → ℝ) (p : P) (k : Bool → QueryTree P O) :
    (query p k).maxPathCost c
      = c p + max ((k false).maxPathCost c) ((k true).maxPathCost c) := rfl

lemma maxPathCost_nonneg {c : P → ℝ} (hc : ∀ p, 0 ≤ c p) (T : QueryTree P O) :
    0 ≤ T.maxPathCost c := by
  induction T with
  | leaf o => exact le_refl 0
  | query p k ih =>
      rw [maxPathCost_query]
      exact add_nonneg (hc p) (le_trans (ih false) (le_max_left _ _))

/-- The path cost is at most the depth times the most expensive label. -/
lemma maxPathCost_le_depth {c : P → ℝ} {q : ℝ} (hq : 0 ≤ q) (hc : ∀ p, c p ≤ q)
    (T : QueryTree P O) : T.maxPathCost c ≤ T.depth * q := by
  induction T with
  | leaf o => rw [maxPathCost_leaf, depth_leaf, Nat.cast_zero, zero_mul]
  | query p k ih =>
      rw [maxPathCost_query, depth_query]
      have hmax : max ((k false).maxPathCost c) ((k true).maxPathCost c)
          ≤ ((max (k false).depth (k true).depth : ℕ) : ℝ) * q := by
        refine max_le ((ih false).trans ?_) ((ih true).trans ?_)
        · exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (le_max_left _ _)) hq
        · exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (le_max_right _ _)) hq
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      linarith [hc p]

/-- Continue querying after reaching a leaf: `T.bind f` runs `T`, then runs the
tree `f` chooses from `T`'s answer.  A search that has to *check* what it found
is exactly this. -/
def bind : QueryTree P O → (O → QueryTree P O') → QueryTree P O'
  | leaf o, f => f o
  | query p k, f => query p fun b => (k b).bind f

@[simp] lemma eval_bind (T : QueryTree P O) (f : O → QueryTree P O')
    (z : P → Bool) : (T.bind f).eval z = (f (T.eval z)).eval z := by
  induction T with
  | leaf o => rfl
  | query p k ih => exact ih (z p)

/-- Paths compose additively, so a uniform bound on the continuations adds. -/
lemma maxPathCost_bind_le {c : P → ℝ} {D : ℝ} (T : QueryTree P O)
    (f : O → QueryTree P O') (hf : ∀ o, (f o).maxPathCost c ≤ D) :
    (T.bind f).maxPathCost c ≤ T.maxPathCost c + D := by
  induction T with
  | leaf o => rw [bind, maxPathCost_leaf, zero_add]; exact hf o
  | query p k ih =>
      rw [bind, maxPathCost_query, maxPathCost_query]
      have hb : max (maxPathCost c ((k false).bind f))
            (maxPathCost c ((k true).bind f))
          ≤ max (maxPathCost c (k false)) (maxPathCost c (k true)) + D := by
        rw [← max_add_add_right]
        exact max_le_max (ih false) (ih true)
      linarith

lemma depth_bind_le {D : ℕ} (T : QueryTree P O) (f : O → QueryTree P O')
    (hf : ∀ o, (f o).depth ≤ D) : (T.bind f).depth ≤ T.depth + D := by
  induction T with
  | leaf o => rw [bind, depth_leaf, Nat.zero_add]; exact hf o
  | query p k ih =>
      rw [bind, depth_query, depth_query]
      have := max_le_max (ih false) (ih true)
      omega

/-- Relabelling the leaves. -/
def mapOut (φ : O → O') : QueryTree P O → QueryTree P O'
  | leaf o => leaf (φ o)
  | query p k => query p fun b => (k b).mapOut φ

@[simp] lemma eval_mapOut (φ : O → O') (T : QueryTree P O) (z : P → Bool) :
    (T.mapOut φ).eval z = φ (T.eval z) := by
  induction T with
  | leaf o => rfl
  | query p k ih => exact ih (z p)

@[simp] lemma maxPathCost_mapOut (c : P → ℝ) (φ : O → O') (T : QueryTree P O) :
    (T.mapOut φ).maxPathCost c = T.maxPathCost c := by
  induction T with
  | leaf o => rfl
  | query p k ih => rw [mapOut, maxPathCost_query, maxPathCost_query, ih, ih]

@[simp] lemma depth_mapOut (φ : O → O') (T : QueryTree P O) :
    (T.mapOut φ).depth = T.depth := by
  induction T with
  | leaf o => rfl
  | query p k ih => rw [mapOut, depth_query, depth_query, ih, ih]

end QueryTree

/-! ## The dual of one query node -/

section Branch

variable {P O : Type} [Fintype P] [DecidableEq P] [Fintype O] [DecidableEq O]
variable {K₀ K₁ : Type} [Fintype K₀] [Fintype K₁]

/-- The vector family of a query node: two masked copies of the subtree
solutions, plus one `Option O` block on the queried coordinate. -/
def branchVec (p : P) (a : O → Option O → ℝ)
    (w₀ : (P → Bool) → P → K₀ → ℝ) (w₁ : (P → Bool) → P → K₁ → ℝ)
    (g : (P → Bool) → O) (z : P → Bool) (i : P) :
    K₀ ⊕ K₁ ⊕ Option O → ℝ :=
  Sum.elim (fun k => if z p then (0 : ℝ) else if i = p then 0 else w₀ z i k)
    (Sum.elim (fun k => if z p then (if i = p then (0 : ℝ) else w₁ z i k) else 0)
      (fun t => if i = p then a (g z) t else 0))

variable {f₀ f₁ f : (P → Bool) → O}

/-- **The dual solution of a single query.** -/
def branchDual (p : P) (hf : ∀ z, f z = if z p then f₁ z else f₀ z)
    (P₀ : DualPair K₀ f₀) (P₁ : DualPair K₁ f₁) :
    DualPair (K₀ ⊕ K₁ ⊕ Option O) f where
  u := branchVec p phiVec P₀.u P₁.u f
  v := branchVec p psiVec P₀.v P₁.v f
  constraint z y := by
    classical
    by_cases hz : z p = true <;> by_cases hy : y p = true
    · -- both take the `true` branch: `P₁` reproduces its own constraint
      have hfz : f z = f₁ z := by rw [hf, if_pos hz]
      have hfy : f y = f₁ y := by rw [hf, if_pos hy]
      rw [hfz, hfy, ← P₁.constraint z y]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : z i = y i
      · rw [if_pos hi, if_pos hi]
      · rw [if_neg hi, if_neg hi]
        have hip : i ≠ p := by rintro rfl; exact hi (by rw [hz, hy])
        simp [branchVec, Fintype.sum_sum_type, hz, hy, hip]
    · -- the branches differ: only the `Option O` block survives
      have hzy : ¬ (z p = y p) := by rw [hz]; exact fun h => hy h.symm
      rw [Finset.sum_eq_single p]
      · rw [if_neg hzy, ← sum_phiVec_mul_psiVec (f z) (f y)]
        simp [branchVec, Fintype.sum_sum_type, hz, hy]
      · intro i _ hip
        by_cases hi : z i = y i
        · rw [if_pos hi]
        · rw [if_neg hi]
          simp [branchVec, Fintype.sum_sum_type, hz, hy, hip]
      · exact fun h => absurd (Finset.mem_univ p) h
    · have hzy : ¬ (z p = y p) := by rw [hy]; exact fun h => hz h
      rw [Finset.sum_eq_single p]
      · rw [if_neg hzy, ← sum_phiVec_mul_psiVec (f z) (f y)]
        simp [branchVec, Fintype.sum_sum_type, hz, hy]
      · intro i _ hip
        by_cases hi : z i = y i
        · rw [if_pos hi]
        · rw [if_neg hi]
          simp [branchVec, Fintype.sum_sum_type, hz, hy, hip]
      · exact fun h => absurd (Finset.mem_univ p) h
    · -- both take the `false` branch
      have hfz : f z = f₀ z := by rw [hf, if_neg hz]
      have hfy : f y = f₀ y := by rw [hf, if_neg hy]
      have hzb : z p = false := by simpa using hz
      have hyb : y p = false := by simpa using hy
      rw [hfz, hfy, ← P₀.constraint z y]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : z i = y i
      · rw [if_pos hi, if_pos hi]
      · rw [if_neg hi, if_neg hi]
        have hip : i ≠ p := by rintro rfl; exact hi (by rw [hzb, hyb])
        simp [branchVec, Fintype.sum_sum_type, hz, hy, hip]

/-- The cost of a branch vector family: `2 cₚ` for the query itself, plus
whichever subtree the input takes. -/
lemma branchVec_cost {p : P} (a : O → Option O → ℝ)
    (ha : ∀ o, (∑ t, a o t * a o t) = 2)
    (w₀ : (P → Bool) → P → K₀ → ℝ) (w₁ : (P → Bool) → P → K₁ → ℝ)
    (g : (P → Bool) → O) {c : P → ℝ} {V₀ V₁ : ℝ} (hc : 0 ≤ c p)
    (h₀ : ∀ z, ∑ i, c i * ∑ k, w₀ z i k * w₀ z i k ≤ V₀)
    (h₁ : ∀ z, ∑ i, c i * ∑ k, w₁ z i k * w₁ z i k ≤ V₁) (z : P → Bool) :
    (∑ i, c i * ∑ k, branchVec p a w₀ w₁ g z i k * branchVec p a w₀ w₁ g z i k)
      ≤ 2 * c p + max V₀ V₁ := by
  classical
  by_cases hz : z p = true
  · have hpt : ∀ i : P, c i * (∑ k, branchVec p a w₀ w₁ g z i k
        * branchVec p a w₀ w₁ g z i k)
        ≤ (if i = p then 2 * c p else 0) + c i * ∑ k, w₁ z i k * w₁ z i k := by
      intro i
      by_cases hip : i = p
      · rw [hip]
        have hval : (∑ k, branchVec p a w₀ w₁ g z p k
            * branchVec p a w₀ w₁ g z p k) = 2 := by
          simp [branchVec, Fintype.sum_sum_type, hz, ha]
        rw [hval, if_pos rfl]
        have hnn : 0 ≤ c p * ∑ k, w₁ z p k * w₁ z p k :=
          mul_nonneg hc (Finset.sum_nonneg fun k _ => mul_self_nonneg _)
        linarith
      · have hval : (∑ k, branchVec p a w₀ w₁ g z i k
            * branchVec p a w₀ w₁ g z i k) = ∑ k, w₁ z i k * w₁ z i k := by
          simp [branchVec, Fintype.sum_sum_type, hz, hip]
        rw [hval, if_neg hip, zero_add]
    refine le_trans (Finset.sum_le_sum fun i _ => hpt i) ?_
    rw [Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ p (fun _ => 2 * c p),
      if_pos (Finset.mem_univ p)]
    linarith [(h₁ z).trans (le_max_right V₀ V₁)]
  · have hpt : ∀ i : P, c i * (∑ k, branchVec p a w₀ w₁ g z i k
        * branchVec p a w₀ w₁ g z i k)
        ≤ (if i = p then 2 * c p else 0) + c i * ∑ k, w₀ z i k * w₀ z i k := by
      intro i
      by_cases hip : i = p
      · rw [hip]
        have hval : (∑ k, branchVec p a w₀ w₁ g z p k
            * branchVec p a w₀ w₁ g z p k) = 2 := by
          simp [branchVec, Fintype.sum_sum_type, hz, ha]
        rw [hval, if_pos rfl]
        have hnn : 0 ≤ c p * ∑ k, w₀ z p k * w₀ z p k :=
          mul_nonneg hc (Finset.sum_nonneg fun k _ => mul_self_nonneg _)
        linarith
      · have hval : (∑ k, branchVec p a w₀ w₁ g z i k
            * branchVec p a w₀ w₁ g z i k) = ∑ k, w₀ z i k * w₀ z i k := by
          simp [branchVec, Fintype.sum_sum_type, hz, hip]
        rw [hval, if_neg hip, zero_add]
    refine le_trans (Finset.sum_le_sum fun i _ => hpt i) ?_
    rw [Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ p (fun _ => 2 * c p),
      if_pos (Finset.mem_univ p)]
    linarith [(h₀ z).trans (le_max_left V₀ V₁)]

/-- **A single query, bundled.**  The subtree costs enter through a maximum. -/
theorem hasWeightedDual_branch (p : P) {c : P → ℝ} {V₀ V₁ : ℝ} (hc : 0 ≤ c p)
    (hf : ∀ z, f z = if z p then f₁ z else f₀ z)
    (h₀ : HasWeightedDual f₀ c V₀) (h₁ : HasWeightedDual f₁ c V₁) :
    HasWeightedDual f c (2 * c p + max V₀ V₁) := by
  obtain ⟨K₀, hK₀, Q₀, hQ₀⟩ := h₀
  obtain ⟨K₁, hK₁, Q₁, hQ₁⟩ := h₁
  exact ⟨K₀ ⊕ K₁ ⊕ Option O, inferInstance, branchDual p hf Q₀ Q₁,
    branchVec_cost phiVec sum_phiVec_sq Q₀.u Q₁.u f hc hQ₀.1 hQ₁.1,
    branchVec_cost psiVec sum_psiVec_sq Q₀.v Q₁.v f hc hQ₀.2 hQ₁.2⟩

end Branch

/-! ## The dual of a tree -/

private lemma two_mul_max (A B : ℝ) : 2 * max A B = max (2 * A) (2 * B) := by
  rcases le_total A B with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]
  · rw [max_eq_left h, max_eq_left (by linarith)]

namespace QueryTree

/-- **The tree dual, for a finite output type.**  The cost is twice the most
expensive root-to-leaf path: the tree is *adaptive*, so nodes off the taken path
are never paid for. -/
theorem hasWeightedDual_eval_of_fintype {P O : Type} [Fintype P] [DecidableEq P]
    [Fintype O] [DecidableEq O] (T : QueryTree P O) (c : P → ℝ)
    (hc : ∀ p, 0 ≤ c p) : HasWeightedDual T.eval c (2 * T.maxPathCost c) := by
  induction T with
  | leaf o =>
      rw [maxPathCost_leaf, mul_zero]
      exact hasWeightedDual_const fun x y => rfl
  | query p k ih =>
      have hbr := hasWeightedDual_branch (f := (query p k).eval)
        (f₀ := (k false).eval) (f₁ := (k true).eval) p (hc p)
        (fun z => by cases hzp : z p <;> simp [hzp]) (ih false) (ih true)
      rw [maxPathCost_query, mul_add, two_mul_max]
      exact hbr

/-- **The tree dual.**  The output type is arbitrary: the input space is finite,
so `HasWeightedDual.ofKer` recodes the reachable outputs into a finite type at no
cost. -/
theorem hasWeightedDual_eval {P O : Type} [Fintype P] [DecidableEq P]
    [DecidableEq O] (T : QueryTree P O) (c : P → ℝ) (hc : ∀ p, 0 ≤ c p) :
    HasWeightedDual T.eval c (2 * T.maxPathCost c) := by
  classical
  set S : Finset O := Finset.image T.eval Finset.univ with hS
  have hmem : ∀ z : P → Bool, T.eval z ∈ S := fun z =>
    Finset.mem_image_of_mem _ (Finset.mem_univ z)
  set φ : O → Option {o // o ∈ S} :=
    fun o => if h : o ∈ S then some ⟨o, h⟩ else none with hφ
  have hbase := (T.mapOut φ).hasWeightedDual_eval_of_fintype c hc
  rw [maxPathCost_mapOut] at hbase
  refine hbase.ofKer fun x y => ?_
  rw [eval_mapOut, eval_mapOut, hφ]
  simp only [dif_pos (hmem x), dif_pos (hmem y), Option.some.injEq,
    Subtype.mk.injEq]

/-- **The tree dual with a uniform query price.** -/
theorem hasWeightedDual_eval_depth {P O : Type} [Fintype P] [DecidableEq P]
    [DecidableEq O] (T : QueryTree P O) {q : ℝ} (hq : 0 ≤ q) :
    HasWeightedDual T.eval (fun _ => q) (2 * T.depth * q) :=
  (T.hasWeightedDual_eval _ fun _ => hq).mono <| by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (maxPathCost_le_depth hq (fun _ => le_refl q) T) (by norm_num)

/-! ## Composition with shared subproblems

The point of the whole file: the queries are themselves functions of one shared
input `x`, and the tree decides *adaptively* which of them to look at. -/

/-- **The adaptive dual of a tree of subproblems.**  Every query label `p`
carries its own subproblem `g p` of cost `c p`, all reading the same input; the
composite costs twice the most expensive root-to-leaf path, with no dependence
at all on how many labels the tree could have queried. -/
theorem hasDual_shared {ι σ P O : Type} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] [Fintype P] [DecidableEq P] [DecidableEq O]
    (T : QueryTree P O) {g : P → (ι → σ) → Bool} {c : P → ℝ}
    (hc : ∀ p, 0 ≤ c p) (hg : ∀ p, HasDual (g p) (c p)) :
    HasDual (fun x => T.eval fun p => g p x) (2 * T.maxPathCost c) :=
  HasWeightedDual.composeShared (T.hasWeightedDual_eval c hc) hc hg

/-- The same with one price for every query: cost `2 · depth · c₀`. -/
theorem hasDual_shared_depth {ι σ P O : Type} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] [Fintype P] [DecidableEq P] [DecidableEq O]
    (T : QueryTree P O) {g : P → (ι → σ) → Bool} {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hg : ∀ p, HasDual (g p) c₀) :
    HasDual (fun x => T.eval fun p => g p x) (2 * T.depth * c₀) :=
  (T.hasDual_shared (fun _ => hc₀) hg).mono <| by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (maxPathCost_le_depth hc₀ (fun _ => le_refl c₀) T) (by norm_num)

end QueryTree


/-! ## Binary search

The tree the AGS prefix search runs.  No monotonicity is assumed: given only a
*sign change* between the endpoints, `boundaryTree` returns some position where
the sign changes, using `⌈log₂(hi-lo)⌉` queries. -/

namespace QueryTree

variable {P : Type}

/-- Binary search for a sign change of `z ∘ q` on `[lo, hi]`.  `fuel` bounds the
number of queries; it must be at least `⌈log₂ (hi - lo)⌉`. -/
def boundaryTree (q : ℕ → P) : ℕ → ℕ → ℕ → QueryTree P ℕ
  | 0, lo, _ => leaf lo
  | fuel + 1, lo, hi =>
      if hi ≤ lo + 1 then leaf lo
      else query (q ((lo + hi) / 2)) fun b =>
        if b then boundaryTree q fuel lo ((lo + hi) / 2)
        else boundaryTree q fuel ((lo + hi) / 2) hi

lemma depth_boundaryTree (q : ℕ → P) (fuel lo hi : ℕ) :
    (boundaryTree q fuel lo hi).depth ≤ fuel := by
  induction fuel generalizing lo hi with
  | zero => simp [boundaryTree]
  | succ fuel ih =>
      rw [boundaryTree]
      split
      · simp
      · rw [depth_query]
        simp only [Bool.false_eq_true, if_false, if_true]
        exact Nat.succ_le_succ (max_le (ih _ _) (ih _ _))

/-- **Correctness of binary search.**  The only hypothesis is a sign change
between the endpoints; the returned position is one place where it happens. -/
theorem boundaryTree_spec (q : ℕ → P) (z : P → Bool) :
    ∀ fuel lo hi : ℕ, lo < hi → hi - lo ≤ 2 ^ fuel →
      z (q lo) = false → z (q hi) = true →
      lo ≤ (boundaryTree q fuel lo hi).eval z ∧
        (boundaryTree q fuel lo hi).eval z < hi ∧
        z (q ((boundaryTree q fuel lo hi).eval z)) = false ∧
        z (q ((boundaryTree q fuel lo hi).eval z + 1)) = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo hi hlt hfuel h0 h1
      rw [pow_zero] at hfuel
      have hhi : hi = lo + 1 := by omega
      subst hhi
      simp only [boundaryTree, eval_leaf]
      exact ⟨le_refl _, by omega, h0, h1⟩
  | succ fuel ih =>
      intro lo hi hlt hfuel h0 h1
      rw [pow_succ] at hfuel
      rw [boundaryTree]
      by_cases hsmall : hi ≤ lo + 1
      · rw [if_pos hsmall]
        have hhi : hi = lo + 1 := by omega
        subst hhi
        simp only [eval_leaf]
        exact ⟨le_refl _, by omega, h0, h1⟩
      · rw [if_neg hsmall, eval_query]
        have hdm := Nat.div_add_mod (lo + hi) 2
        have hmod : (lo + hi) % 2 < 2 := Nat.mod_lt _ (by norm_num)
        by_cases hzm : z (q ((lo + hi) / 2)) = true
        · rw [hzm]
          simp only [if_true]
          obtain ⟨ha, hb, hc, hd⟩ :=
            ih lo ((lo + hi) / 2) (by omega) (by omega) h0 hzm
          exact ⟨ha, by omega, hc, hd⟩
        · have hzf : z (q ((lo + hi) / 2)) = false := by simpa using hzm
          rw [hzf]
          simp only [Bool.false_eq_true, if_false]
          obtain ⟨ha, hb, hc, hd⟩ :=
            ih ((lo + hi) / 2) hi (by omega) (by omega) hzf h1
          exact ⟨by omega, hb, hc, hd⟩

/-- `⌈log₂ (hi - lo)⌉` queries always suffice. -/
lemma boundaryTree_clog_spec (q : ℕ → P) (z : P → Bool) {lo hi : ℕ}
    (hlt : lo < hi) (h0 : z (q lo) = false) (h1 : z (q hi) = true) :
    let i := (boundaryTree q (Nat.clog 2 (hi - lo)) lo hi).eval z
    lo ≤ i ∧ i < hi ∧ z (q i) = false ∧ z (q (i + 1)) = true :=
  boundaryTree_spec q z _ lo hi hlt
    (Nat.le_pow_clog (by norm_num) _) h0 h1

/-! ### Monotone tests

`boundaryTree_spec` returns *a* sign change.  When the test is closed under
shortening, there is only one, so the search returns *the* boundary
and the position it names is the largest one that still passes. -/

/-- The tested sequence `j ↦ z (q j)` never switches back off along `[lo, hi]`. -/
def StepUp (q : ℕ → P) (z : P → Bool) (lo hi : ℕ) : Prop :=
  ∀ j k : ℕ, lo ≤ j → j ≤ k → k ≤ hi → z (q j) = true → z (q k) = true

/-- Reading `z (q j) = false` as "position `j` passes", a test closed under
shortening is `StepUp`. -/
lemma stepUp_of_shorteningClosed (q : ℕ → P) (z : P → Bool)
    (h : ∀ j k : ℕ, k ≤ j → z (q j) = false → z (q k) = false) (lo hi : ℕ) :
    StepUp q z lo hi := by
  intro j k _ hjk _ hjt
  by_contra hcon
  exact absurd (h k j hjk (by simpa using hcon)) (by rw [hjt]; simp)

/-- Under `StepUp` the returned position separates the interval cleanly. -/
theorem boundaryTree_stepUp (q : ℕ → P) (z : P → Bool) {fuel lo hi : ℕ}
    (hstep : StepUp q z lo hi) (hlt : lo < hi) (hfuel : hi - lo ≤ 2 ^ fuel)
    (h0 : z (q lo) = false) (h1 : z (q hi) = true) :
    (∀ j, lo ≤ j → j ≤ (boundaryTree q fuel lo hi).eval z → z (q j) = false) ∧
      (∀ j, (boundaryTree q fuel lo hi).eval z < j → j ≤ hi →
        z (q j) = true) := by
  obtain ⟨hlo, hhi, hf, ht⟩ := boundaryTree_spec q z fuel lo hi hlt hfuel h0 h1
  refine ⟨fun j hj1 hj2 => ?_, fun j hj1 hj2 => hstep _ j (by omega) (by omega) hj2 ht⟩
  by_contra hcon
  exact absurd (hstep j _ hj1 hj2 (by omega) (by simpa using hcon))
    (by rw [hf]; simp)

/-- **The greatest passing position.**  Under `StepUp`, `boundaryTree` returns
the largest position of `[lo, hi]` at which the test still fails — in the
prefix-closed reading, the longest passing prefix. -/
theorem boundaryTree_isGreatest (q : ℕ → P) (z : P → Bool) {fuel lo hi : ℕ}
    (hstep : StepUp q z lo hi) (hlt : lo < hi) (hfuel : hi - lo ≤ 2 ^ fuel)
    (h0 : z (q lo) = false) (h1 : z (q hi) = true) :
    IsGreatest {j : ℕ | lo ≤ j ∧ j ≤ hi ∧ z (q j) = false}
      ((boundaryTree q fuel lo hi).eval z) := by
  obtain ⟨hlo, hhi, hf, ht⟩ := boundaryTree_spec q z fuel lo hi hlt hfuel h0 h1
  obtain ⟨-, habove⟩ := boundaryTree_stepUp q z hstep hlt hfuel h0 h1
  refine ⟨⟨hlo, by omega, hf⟩, fun j hj => ?_⟩
  obtain ⟨hj1, hj2, hj3⟩ := hj
  by_contra hcon
  rw [habove j (by omega) hj2] at hj3
  simp at hj3

/-- Under `StepUp` the sign change is unique, so the search returns *the*
boundary. -/
theorem boundaryTree_eq_of_stepUp (q : ℕ → P) (z : P → Bool) {fuel lo hi j : ℕ}
    (hstep : StepUp q z lo hi) (hlt : lo < hi) (hfuel : hi - lo ≤ 2 ^ fuel)
    (h0 : z (q lo) = false) (h1 : z (q hi) = true) (hj1 : lo ≤ j) (hj2 : j < hi)
    (hjf : z (q j) = false) (hjt : z (q (j + 1)) = true) :
    (boundaryTree q fuel lo hi).eval z = j := by
  obtain ⟨hbelow, habove⟩ := boundaryTree_stepUp q z hstep hlt hfuel h0 h1
  rcases lt_trichotomy ((boundaryTree q fuel lo hi).eval z) j with h | h | h
  · rw [habove j h (le_of_lt hj2)] at hjf; simp at hjf
  · exact h
  · rw [hbelow (j + 1) (by omega) (by omega)] at hjt; simp at hjt

/-- Each candidate position carries its
own subproblem `g p` of cost `c₀`; locating a sign change among them costs
`2 · fuel · c₀`, which is logarithmic in the number of positions, not linear. -/
theorem hasDual_boundaryTree {ι σ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] [Fintype P] [DecidableEq P] (q : ℕ → P)
    {g : P → (ι → σ) → Bool} {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hg : ∀ p, HasDual (g p) c₀) (fuel lo hi : ℕ) :
    HasDual (fun x => (boundaryTree q fuel lo hi).eval fun p => g p x)
      (2 * fuel * c₀) := by
  refine ((boundaryTree q fuel lo hi).hasDual_shared_depth hc₀ hg).mono ?_
  refine mul_le_mul_of_nonneg_right ?_ hc₀
  have hd : ((boundaryTree q fuel lo hi).depth : ℝ) ≤ (fuel : ℝ) := by
    exact_mod_cast depth_boundaryTree q fuel lo hi
  linarith

end QueryTree

/-! ## Sanity checks

Zero-depth, single-query, weighted and shared-subproblem checks. -/

section Checks

open QueryTree

variable {P O : Type} [Fintype P] [DecidableEq P] [DecidableEq O]

/-- A depth-zero tree costs nothing. -/
example (o : O) (c : P → ℝ) : (leaf o : QueryTree P O).maxPathCost c = 0 := rfl

example {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (o : O) {g : P → (ι → σ) → Bool} {c : P → ℝ} (hc : ∀ p, 0 ≤ c p)
    (hg : ∀ p, HasDual (g p) (c p)) :
    HasDual (fun x => (leaf o : QueryTree P O).eval fun p => g p x) 0 := by
  simpa using (leaf o : QueryTree P O).hasDual_shared hc hg

/-- A one-node tree is a one-coordinate Boolean test, and its dual costs `2 cₚ` —
matching `hasDual_ofCoord`, which pays `2` for reading a single letter. -/
example (p : P) (z : P → Bool) :
    (query p fun b => leaf b : QueryTree P Bool).eval z = z p := rfl

theorem hasWeightedDual_coord (p : P) (c : P → ℝ) (hc : ∀ p, 0 ≤ c p) :
    HasWeightedDual (fun z : P → Bool => z p) c (2 * c p) := by
  have h := (query p fun b => leaf b : QueryTree P Bool).hasWeightedDual_eval c hc
  simp only [maxPathCost_query, maxPathCost_leaf, max_self, add_zero] at h
  exact h.ofKer fun x y => by simp

/-- **Repeating a query label on a path is safe.**  The two occurrences occupy
different summands of the dimension type, so nothing is double-counted; the tree
simply pays for the label twice. -/
example (p : P) (z : P → Bool) :
    (query p fun _ => query p fun b => leaf b : QueryTree P Bool).eval z = z p :=
  rfl

example (p : P) (c : P → ℝ) (hc : ∀ p, 0 ≤ c p) :
    HasWeightedDual (fun z : P → Bool => z p) c (2 * (c p + c p)) := by
  have h := (query p fun _ => query p fun b => leaf b :
    QueryTree P Bool).hasWeightedDual_eval c hc
  simp only [maxPathCost_query, maxPathCost_leaf, max_self, add_zero] at h
  exact h.ofKer fun x y => by simp

/-- A balanced binary search over `n+1` positions has depth at most
`Nat.clog 2 n`, so its dual costs `2 ⌈log₂ n⌉ c₀`, however large `n` is. -/
example (q : ℕ → P) (n : ℕ) :
    (boundaryTree q (Nat.clog 2 n) 0 n).depth ≤ Nat.clog 2 n :=
  depth_boundaryTree q _ 0 n

/-- A concrete run, as a guard against index-convention drift: searching
`[0,16]` for the switch point of `5 ≤ j` returns `4`, in four queries. -/
example : (boundaryTree (P := ℕ) id 4 0 16).eval (fun j => decide (5 ≤ j)) = 4 :=
  by decide

example : Nat.clog 2 16 = 4 := by decide

end Checks

end QuantumQueryComplexity
