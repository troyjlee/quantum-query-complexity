import QuantumQueryComplexity.HasDual

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Weighted transcript-tree search (dual form)

A finite rooted tree is given by an *ancestor structure* `AncTree`: a depth and, for
every vertex, its ancestor at each smaller depth.  A *table* assigns a value `x v : E`
to every vertex; the *transcript* of `v` is the table restricted to its root path.  A
*marking* `mark v x` is a predicate that depends on `x` only through the transcript of
`v`.  The search problem decides whether some vertex is marked.

**The dual.**  Positive tables carry their `u`-vectors in sector `false`, along the
root path of a chosen marked vertex, with the value `1/β_w` on the basis vector labelled
by the transcript of the *strict* ancestors of `w`; negative tables carry `β_w` on the
label of their own strict-ancestor transcript at every vertex, in sector `true`.  The
`v`-family is the same with the sectors exchanged.  Pairs with equal output are then
orthogonal, and a positive/negative pair pays exactly `1`: the two tables differ
somewhere on the marked path (marking is transcript-local), and only the *first*
difference along that path has agreeing strict-ancestor transcripts (`sum_firstDiff`).

With cell costs `t_w` (shared-input composition, `hasDual_treeSearch_comp`) the cost is
`max { max_v ∑_{w ∈ path v} t_w/β_w², ∑_w t_w β_w² }` (`hasWeightedDual_treeSearch`).
Choosing `β_w² = 2^{-depth w/2}` on a balanced tree whose costs are `A·√(m/2^depth)`
makes both sides `A√m·(d+1)`: the electric-network bound of the notes, with no
constant lost per level.  Repeated lookups of a cell need no persistence device here:
every cell is a deterministic function of the input, and each decision pays its own
cost through the composition.
-/

namespace QuantumQueryComplexity

open Finset

/-- **An ancestor structure**: a depth and the ancestor at every depth `≤` the vertex's. -/
structure AncTree (V : Type) where
  depth : V → ℕ
  ancAt : V → ℕ → V
  depth_ancAt : ∀ v i, i ≤ depth v → depth (ancAt v i) = i
  ancAt_self : ∀ v, ancAt v (depth v) = v
  ancAt_ancAt : ∀ v i j, j ≤ i → i ≤ depth v → ancAt (ancAt v i) j = ancAt v j

namespace AncTree

variable {V : Type} [DecidableEq V] (T : AncTree V)

/-- The root path of `v`: its ancestors at depths `0, …, depth v`. -/
def path (v : V) : Finset V := (Finset.range (T.depth v + 1)).image (T.ancAt v)

lemma mem_path {v w : V} : w ∈ T.path v ↔ ∃ i ≤ T.depth v, T.ancAt v i = w := by
  simp only [path, Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff]

lemma self_mem_path (v : V) : v ∈ T.path v := T.mem_path.2 ⟨_, le_rfl, T.ancAt_self v⟩

lemma ancAt_mem_path {v : V} {i : ℕ} (hi : i ≤ T.depth v) : T.ancAt v i ∈ T.path v :=
  T.mem_path.2 ⟨i, hi, rfl⟩

lemma ancAt_injOn (v : V) : ∀ i ∈ Finset.range (T.depth v + 1),
    ∀ j ∈ Finset.range (T.depth v + 1), T.ancAt v i = T.ancAt v j → i = j := by
  intro i hi j hj h
  rw [Finset.mem_range] at hi hj
  have := congrArg T.depth h
  rwa [T.depth_ancAt v i (by omega), T.depth_ancAt v j (by omega)] at this

lemma card_path (v : V) : (T.path v).card = T.depth v + 1 := by
  rw [path, Finset.card_image_of_injOn (fun i hi j hj h => T.ancAt_injOn v i hi j hj h),
    Finset.card_range]

section Transcript

variable {E : Type} [DecidableEq E] (D : ℕ)

/-- The transcript of the strict ancestors of `v` under the table `x`, indexed by depth. -/
def anc (x : V → E) (v : V) : Fin (D + 1) → Option E :=
  fun i => if (i : ℕ) < T.depth v then some (x (T.ancAt v (i : ℕ))) else none

lemma anc_eq_iff {v : V} (hv : T.depth v ≤ D) (x y : V → E) :
    T.anc D x v = T.anc D y v ↔ ∀ i < T.depth v, x (T.ancAt v i) = y (T.ancAt v i) := by
  constructor
  · intro h i hi
    have h' := congrFun h ⟨i, by omega⟩
    simp only [anc, hi, if_true, Option.some.injEq] at h'
    exact h'
  · intro h
    funext i
    simp only [anc]
    split_ifs with hi
    · rw [h i hi]
    · rfl

/-- The strict-ancestor transcript of the vertex at depth `i` on the path of `v`. -/
lemma anc_ancAt_eq_iff {v : V} (hv : T.depth v ≤ D) {i : ℕ} (hi : i ≤ T.depth v) (x y : V → E) :
    T.anc D x (T.ancAt v i) = T.anc D y (T.ancAt v i)
      ↔ ∀ j < i, x (T.ancAt v j) = y (T.ancAt v j) := by
  rw [T.anc_eq_iff D (by rw [T.depth_ancAt v i hi]; omega), T.depth_ancAt v i hi]
  constructor
  · intro h j hj
    have := h j hj
    rwa [T.ancAt_ancAt v i j hj.le hi] at this
  · intro h j hj
    rw [T.ancAt_ancAt v i j hj.le hi]
    exact h j hj

/-- **First difference.**  Two tables that differ somewhere on the root path of `v` differ at
exactly one vertex of that path whose strict-ancestor transcripts agree. -/
theorem sum_firstDiff {v : V} (hv : T.depth v ≤ D) (x y : V → E)
    (hne : ∃ i ≤ T.depth v, x (T.ancAt v i) ≠ y (T.ancAt v i)) :
    ∑ w ∈ T.path v, (if x w ≠ y w ∧ T.anc D x w = T.anc D y w then (1 : ℝ) else 0) = 1 := by
  classical
  rw [path, Finset.sum_image (T.ancAt_injOn v)]
  have hex : ∃ i, i ≤ T.depth v ∧ x (T.ancAt v i) ≠ y (T.ancAt v i) := hne
  have hspec := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, x (T.ancAt v j) = y (T.ancAt v j) := fun j hj => by
    by_contra hc
    exact Nat.find_min hex hj ⟨by omega, hc⟩
  rw [Finset.sum_eq_single (Nat.find hex)]
  · rw [if_pos ⟨hspec.2, (T.anc_ancAt_eq_iff D hv hspec.1 x y).2 hmin⟩]
  · intro i hi hne_i
    rw [Finset.mem_range] at hi
    rw [if_neg]
    rintro ⟨hxy, hanc⟩
    rw [T.anc_ancAt_eq_iff D hv (by omega) x y] at hanc
    rcases Nat.lt_or_gt_of_ne hne_i with h | h
    · exact hxy (hmin i h)
    · exact hspec.2 (hanc _ h)
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

end Transcript

/-! ## The dual -/

section Search

variable {E : Type} [Fintype V] [Fintype E] [DecidableEq E] (D : ℕ)
variable (mark : V → (V → E) → Prop)

open Classical in
/-- The search decision: is some vertex marked? -/
noncomputable def treeSearch (x : V → E) : Bool := decide (∃ v, mark v x)

/-- A sum against a single-support vector. -/
lemma sum_single_mul {K : Type} [Fintype K] [DecidableEq K] (k₁ k₂ : K) (a b : ℝ) :
    ∑ k, (if k = k₁ then a else 0) * (if k = k₂ then b else 0)
      = if k₁ = k₂ then a * b else 0 := by
  rw [Finset.sum_eq_single k₁]
  · rw [if_pos rfl]
    split_ifs <;> simp
  · intro k _ hk
    rw [if_neg hk, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The squared norm of a single-support vector. -/
lemma sum_single_sq {K : Type} [Fintype K] [DecidableEq K] (k₀ : K) (a : ℝ) :
    ∑ k, (if k = k₀ then a else 0) * (if k = k₀ then a else 0) = a * a := by
  rw [sum_single_mul, if_pos rfl]

open Classical in
/-- The `u`-family: positive tables in sector `false` along the marked path, negative
tables in sector `true` everywhere. -/
noncomputable def uVec (β : V → ℝ) (x : V → E) (w : V) (k : Bool × (Fin (D + 1) → Option E)) : ℝ :=
  if h : ∃ v, mark v x then
    (if w ∈ T.path (Classical.choose h) then (if k = (false, T.anc D x w) then 1 / β w else 0)
      else 0)
  else (if k = (true, T.anc D x w) then β w else 0)

open Classical in
/-- The `v`-family: the sectors exchanged. -/
noncomputable def vVec (β : V → ℝ) (y : V → E) (w : V) (k : Bool × (Fin (D + 1) → Option E)) : ℝ :=
  if h : ∃ v, mark v y then
    (if w ∈ T.path (Classical.choose h) then (if k = (true, T.anc D y w) then 1 / β w else 0)
      else 0)
  else (if k = (false, T.anc D y w) then β w else 0)

variable {β : V → ℝ} (hβ : ∀ w, β w ≠ 0)
include hβ

lemma sum_k_pos_neg {x y : V → E} (hx : ∃ v, mark v x) (hy : ¬ ∃ v, mark v y) (w : V) :
    ∑ k, uVec T D mark β x w k * vVec T D mark β y w k
      = if w ∈ T.path (Classical.choose hx) ∧ T.anc D x w = T.anc D y w then 1 else 0 := by
  simp only [uVec, vVec, dif_pos hx, dif_neg hy]
  by_cases hw : w ∈ T.path (Classical.choose hx)
  · simp only [hw, if_true, true_and]
    rw [sum_single_mul]
    by_cases ha : T.anc D x w = T.anc D y w
    · rw [if_pos (by rw [ha]), if_pos ha, one_div_mul_cancel (hβ w)]
    · rw [if_neg (fun h => ha (Prod.mk.inj h).2), if_neg ha]
  · simp [hw]

lemma sum_k_neg_pos {x y : V → E} (hx : ¬ ∃ v, mark v x) (hy : ∃ v, mark v y) (w : V) :
    ∑ k, uVec T D mark β x w k * vVec T D mark β y w k
      = if w ∈ T.path (Classical.choose hy) ∧ T.anc D x w = T.anc D y w then 1 else 0 := by
  simp only [uVec, vVec, dif_neg hx, dif_pos hy]
  by_cases hw : w ∈ T.path (Classical.choose hy)
  · simp only [hw, if_true, true_and]
    rw [sum_single_mul]
    by_cases ha : T.anc D x w = T.anc D y w
    · rw [if_pos (by rw [ha]), if_pos ha, mul_one_div_cancel (hβ w)]
    · rw [if_neg (fun h => ha (Prod.mk.inj h).2), if_neg ha]
  · simp [hw]

lemma sum_k_pos_pos {x y : V → E} (hx : ∃ v, mark v x) (hy : ∃ v, mark v y) (w : V) :
    ∑ k, uVec T D mark β x w k * vVec T D mark β y w k = 0 := by
  simp only [uVec, vVec, dif_pos hx, dif_pos hy]
  refine Finset.sum_eq_zero fun k _ => ?_
  split_ifs <;> simp_all

lemma sum_k_neg_neg {x y : V → E} (hx : ¬ ∃ v, mark v x) (hy : ¬ ∃ v, mark v y) (w : V) :
    ∑ k, uVec T D mark β x w k * vVec T D mark β y w k = 0 := by
  simp only [uVec, vVec, dif_neg hx, dif_neg hy]
  refine Finset.sum_eq_zero fun k _ => ?_
  split_ifs <;> simp_all

variable (hD : ∀ v, T.depth v ≤ D)
variable (hloc : ∀ v (x y : V → E),
  (∀ i ≤ T.depth v, x (T.ancAt v i) = y (T.ancAt v i)) → (mark v x ↔ mark v y))
include hD hloc

/-- A positive and a negative table differ somewhere on the marked path. -/
lemma exists_diff_on_path {x y : V → E} (hx : ∃ v, mark v x) (hy : ¬ ∃ v, mark v y) :
    ∃ i ≤ T.depth (Classical.choose hx),
      x (T.ancAt (Classical.choose hx) i) ≠ y (T.ancAt (Classical.choose hx) i) := by
  by_contra h
  push Not at h
  exact hy ⟨_, (hloc (Classical.choose hx) x y h).1 (Classical.choose_spec hx)⟩

omit hloc in
/-- The pairing indicator summed over all vertices is the first-difference count along the
path of `ν`. -/
lemma sum_pairing_of_path {x y : V → E} (ν : V)
    (hne : ∃ i ≤ T.depth ν, x (T.ancAt ν i) ≠ y (T.ancAt ν i)) :
    (∑ w, if x w = y w then 0 else
      (if w ∈ T.path ν ∧ T.anc D x w = T.anc D y w then (1 : ℝ) else 0)) = 1 := by
  refine Eq.trans ?_ (T.sum_firstDiff D (hD ν) x y hne)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ T.path ν)]
  have hz : ∑ w ∈ Finset.univ.filter (fun w => ¬ w ∈ T.path ν),
      (if x w = y w then 0 else
        (if w ∈ T.path ν ∧ T.anc D x w = T.anc D y w then (1 : ℝ) else 0)) = 0 := by
    refine Finset.sum_eq_zero fun w hw => ?_
    rw [Finset.mem_filter] at hw
    split_ifs with h1 h2
    · rfl
    · exact absurd h2.1 hw.2
    · rfl
  rw [hz, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
  refine Finset.sum_congr rfl fun w hw => ?_
  by_cases hxy : x w = y w
  · rw [if_pos hxy, if_neg (fun h => h.1 hxy)]
  · rw [if_neg hxy]
    by_cases ha : T.anc D x w = T.anc D y w
    · rw [if_pos ⟨hw, ha⟩, if_pos ⟨hxy, ha⟩]
    · rw [if_neg (fun h => ha h.2), if_neg (fun h => ha h.2)]

open Classical in
/-- **The dual constraint.** -/
theorem treeSearch_constraint (x y : V → E) :
    (∑ w, if x w = y w then 0 else ∑ k, uVec T D mark β x w k * vVec T D mark β y w k)
      = if treeSearch mark x = treeSearch mark y then 0 else 1 := by
  by_cases hx : ∃ v, mark v x <;> by_cases hy : ∃ v, mark v y
  · rw [if_pos (by simp [treeSearch, hx, hy])]
    exact Finset.sum_eq_zero fun w _ => by
      rw [sum_k_pos_pos T D mark hβ hx hy]; split_ifs <;> rfl
  · rw [if_neg (by simp [treeSearch, hx, hy])]
    exact (Finset.sum_congr rfl fun w _ => by rw [sum_k_pos_neg T D mark hβ hx hy]).trans
      (sum_pairing_of_path T D hβ hD _ (exists_diff_on_path T D mark hβ hD hloc hx hy))
  · rw [if_neg (by simp [treeSearch, hx, hy])]
    have hne : ∃ i ≤ T.depth (Classical.choose hy),
        x (T.ancAt (Classical.choose hy) i) ≠ y (T.ancAt (Classical.choose hy) i) := by
      obtain ⟨i, hi, h⟩ := exists_diff_on_path T D mark hβ hD hloc hy hx
      exact ⟨i, hi, fun h' => h h'.symm⟩
    exact (Finset.sum_congr rfl fun w _ => by rw [sum_k_neg_pos T D mark hβ hx hy]).trans
      (sum_pairing_of_path T D hβ hD _ hne)
  · rw [if_pos (by simp [treeSearch, hx, hy])]
    exact Finset.sum_eq_zero fun w _ => by
      rw [sum_k_neg_neg T D mark hβ hx hy]; split_ifs <;> rfl

/-- The bundled dual solution. -/
noncomputable def treeSearchDual : DualPair (Bool × (Fin (D + 1) → Option E)) (treeSearch mark) where
  u := uVec T D mark β
  v := vVec T D mark β
  constraint := treeSearch_constraint T D mark hβ hD hloc

/-- **The weighted cost**: positive tables pay `∑_{path} t_w/β_w²`, negative tables
`∑_w t_w β_w²`. -/
theorem treeSearchDual_isWeightedCostLe (t : V → ℝ) (Vc : ℝ)
    (hpath : ∀ v, ∑ w ∈ T.path v, t w / (β w) ^ 2 ≤ Vc) (hall : ∑ w, t w * (β w) ^ 2 ≤ Vc) :
    (treeSearchDual T D mark hβ hD hloc).IsWeightedCostLe t Vc := by
  classical
  have hpathcost : ∀ (ν : V) (a : Bool) (x : V → E),
      ∑ w, t w * ∑ k : Bool × (Fin (D + 1) → Option E),
        (if w ∈ T.path ν then (if k = (a, T.anc D x w) then 1 / β w else 0) else 0)
        * (if w ∈ T.path ν then (if k = (a, T.anc D x w) then 1 / β w else 0) else 0) ≤ Vc := by
    intro ν a x
    refine le_trans (le_of_eq ?_) (hpath ν)
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ T.path ν)]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter fun w => ¬ w ∈ T.path ν) (fun w hw => by
      rw [Finset.mem_filter] at hw
      simp [hw.2]), add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.sum_congr rfl fun w hw => ?_
    simp only [hw, if_true]
    rw [sum_single_sq (a, T.anc D x w) (1 / β w)]
    ring
  have hallcost : ∀ (a : Bool) (x : V → E),
      ∑ w, t w * ∑ k : Bool × (Fin (D + 1) → Option E),
        (if k = (a, T.anc D x w) then β w else 0) * (if k = (a, T.anc D x w) then β w else 0)
        ≤ Vc := by
    intro a x
    refine le_trans (le_of_eq ?_) hall
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [sum_single_sq (a, T.anc D x w) (β w), sq]
  constructor
  · intro x
    by_cases hx : ∃ v, mark v x
    · simp only [treeSearchDual, uVec, dif_pos hx]
      exact hpathcost _ false x
    · simp only [treeSearchDual, uVec, dif_neg hx]
      exact hallcost true x
  · intro y
    by_cases hy : ∃ v, mark v y
    · simp only [treeSearchDual, vVec, dif_pos hy]
      exact hpathcost _ true y
    · simp only [treeSearchDual, vVec, dif_neg hy]
      exact hallcost false y

/-- **Weighted transcript-tree search dual.**  With cell weights `t`, the decision "some
vertex is marked" has weighted cost `max { max_v ∑_{w ∈ path v} t_w/β_w², ∑_w t_w β_w² }`. -/
theorem hasWeightedDual_treeSearch (t : V → ℝ) (Vc : ℝ)
    (hpath : ∀ v, ∑ w ∈ T.path v, t w / (β w) ^ 2 ≤ Vc) (hall : ∑ w, t w * (β w) ^ 2 ≤ Vc) :
    HasWeightedDual (treeSearch mark) t Vc :=
  hasWeightedDual_of_dualPair (treeSearchDual T D mark hβ hD hloc)
    (treeSearchDual_isWeightedCostLe T D mark hβ hD hloc t Vc hpath hall)

/-- **Search over a table of computed cells**: each cell `cell v` is a function of the
input with a dual of cost `t v`; the composed decision inherits the weighted cost. -/
theorem hasDual_treeSearch_comp {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
    [DecidableEq σ] (cell : V → (ι → σ) → E) {t : V → ℝ} (ht : ∀ v, 0 ≤ t v)
    (hcell : ∀ v, HasDual (cell v) (t v)) (Vc : ℝ)
    (hpath : ∀ v, ∑ w ∈ T.path v, t w / (β w) ^ 2 ≤ Vc) (hall : ∑ w, t w * (β w) ^ 2 ≤ Vc) :
    HasDual (fun x : ι → σ => treeSearch mark (fun w => cell w x)) Vc :=
  (hasWeightedDual_treeSearch T D mark hβ hD hloc t Vc hpath hall).composeShared ht hcell

end Search

/-! ## The square-sum form -/

section SqSum

variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V] (T : AncTree V)
variable {E : Type} [Fintype E] [DecidableEq E] (D : ℕ) (mark : V → (V → E) → Prop)
variable (hD : ∀ v, T.depth v ≤ D)
variable (hloc : ∀ v (x y : V → E),
  (∀ i ≤ T.depth v, x (T.ancAt v i) = y (T.ancAt v i)) → (mark v x ↔ mark v y))
include hD hloc

/-- **The square-sum form of the weighted tree-search dual** (the depth corollary of the
recursive-cost theorem, `cor:beta-tree-search-depth`): with positive cell costs `t` and depth
at most `d`, the weights `β_w² = t_w / √(∑ t²/(d+1))` make the total sum equal to
`√((d+1)·∑_w t_w²)` and every path sum *at most* that value (a path of depth `< d` is strictly
below it).  The exact optimized form is `hasWeightedDual_treeSearch_recCost`
(`TreeSearch/Optimal.lean`); this statement holds for any ancestor structure, forests
included. -/
theorem hasWeightedDual_treeSearch_sqSum (t : V → ℝ) (ht : ∀ w, 0 < t w) :
    HasWeightedDual (treeSearch mark) t (Real.sqrt (((D : ℝ) + 1) * ∑ w, t w ^ 2)) := by
  set A : ℝ := ∑ w, t w ^ 2 with hA
  have hA0 : 0 < A :=
    Finset.sum_pos (fun w _ => by have := ht w; positivity) Finset.univ_nonempty
  have hD0 : (0 : ℝ) < (D : ℝ) + 1 := by positivity
  set S : ℝ := Real.sqrt (A / ((D : ℝ) + 1)) with hSdef
  have hS0 : 0 < S := Real.sqrt_pos.2 (by positivity)
  have hS2 : S ^ 2 = A / ((D : ℝ) + 1) := Real.sq_sqrt (by positivity)
  set β : V → ℝ := fun w => Real.sqrt (t w / S) with hβdef
  have hβ2 : ∀ w, β w ^ 2 = t w / S := fun w => Real.sq_sqrt (by have := ht w; positivity)
  have hβ : ∀ w, β w ≠ 0 := fun w => by
    have := ht w
    exact Real.sqrt_ne_zero'.2 (by positivity)
  -- the common value of both sums
  have hB : Real.sqrt (((D : ℝ) + 1) * A) = ((D : ℝ) + 1) * S := by
    have : ((D : ℝ) + 1) * A = ((D : ℝ) + 1) ^ 2 * (A / ((D : ℝ) + 1)) := by
      field_simp
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hD0.le]
  have hpath : ∀ v, ∑ w ∈ T.path v, t w / (β w) ^ 2 ≤ ((D : ℝ) + 1) * S := by
    intro v
    have hterm : ∀ w ∈ T.path v, t w / (β w) ^ 2 = S := fun w _ => by
      have h1 := (ht w).ne'
      have h2 := hS0.ne'
      rw [hβ2]
      field_simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, T.card_path, nsmul_eq_mul]
    have h1 : ((T.depth v + 1 : ℕ) : ℝ) ≤ (D : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ (hD v)
    exact mul_le_mul_of_nonneg_right h1 hS0.le
  have hall : ∑ w, t w * (β w) ^ 2 ≤ ((D : ℝ) + 1) * S := by
    have hterm : ∀ w ∈ (Finset.univ : Finset V), t w * (β w) ^ 2 = t w ^ 2 / S := fun w _ => by
      rw [hβ2]; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← hA]
    have hA' : A = ((D : ℝ) + 1) * S ^ 2 := by rw [hS2]; field_simp
    have h2 := hS0.ne'
    rw [hA']
    have : ((D : ℝ) + 1) * S ^ 2 / S = ((D : ℝ) + 1) * S := by field_simp
    rw [this]
  rw [hB]
  exact hasWeightedDual_treeSearch T D mark hβ hD hloc t _ hpath hall

end SqSum

end AncTree

end QuantumQueryComplexity
