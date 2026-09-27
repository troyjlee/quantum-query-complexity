import QuantumQueryComplexity.FirstDiff
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Weighted scans: the decision-tree dual with black/red weights

A **scan** orders the coordinates and records, for each input and coordinate,
the *branch* taken there and its *colour*.  This is the algebraic core of
Beigi–Taghavi's generalized-decision-tree dual, with weights assigned to nodes.

The point of the reformulation used here is that a scan is
`QuantumQueryComplexity/FirstDiff.lean` applied to the **branch sequence** instead of the raw
input.  A tree node is exactly a branch-prefix, so "two paths agree until their
first different branch" is literally `card_firstDiffSet`, and no tree datatype is
needed.  Three conditions make the argument go through:

* `br_ne` — a differing branch forces a differing symbol, so the coordinate is
  visible to the adversary mask;
* `out_eq` — equal branch sequences force equal outputs, so the pairing is
  switched on whenever the outputs differ;
* `black_unique` — at most one branch at a node is black, which is what makes
  the two square-root weights cancel.

The colours are what the ordinary first-difference dual lacks.  `u` pays
`1 / W` at the branch it takes, while `v` pays `∑ W` over the *other* colours;
choosing `W` per coordinate then trades the two costs off against each other.
With constant weights this collapses back to `ADV±(f) ≤ 2 D(f)`; with
depth-dependent weights it is what removes the alphabet dependence from maximum
finding.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {O : Type*} [Fintype O] [DecidableEq O]
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- A scan of the coordinates: an order, and for each input the branch taken at
each coordinate together with its colour. -/
structure Scan (ι σ O Q : Type*) [Fintype ι] where
  /-- The order in which coordinates are scanned. -/
  rank : ι → Fin (Fintype.card ι)
  /-- The order is a genuine ordering. -/
  rank_inj : Function.Injective rank
  /-- The branch taken at each coordinate. -/
  br : (ι → σ) → ι → Q
  /-- Its colour: `false` is black, `true` is red. -/
  col : (ι → σ) → ι → Bool
  /-- The value computed. -/
  out : (ι → σ) → O
  /-- At the same node, a differing branch forces a differing symbol: the
  branches at a node partition the alphabet, so the branch is determined by the
  symbol read. -/
  br_ne : ∀ x y i, (∀ j, rank j < rank i → br x j = br y j) →
    br x i ≠ br y i → x i ≠ y i
  /-- Equal branch sequences force equal outputs. -/
  out_eq : ∀ x y, (∀ i, br x i = br y i) → out x = out y
  /-- At most one branch at each node is black. -/
  black_unique : ∀ x y i, col x i = false → col y i = false →
    (∀ j, rank j < rank i → br x j = br y j) → br x i = br y i

namespace Scan

variable (S : Scan ι σ O Q)

/-- The node reached before scanning `i`: the branches taken so far. -/
def node (x : ι → σ) (i : ι) : ι → Option Q :=
  fun j => if S.rank j < S.rank i then some (S.br x j) else none

lemma node_eq_iff {x y : ι → σ} {i : ι} :
    S.node x i = S.node y i ↔ ∀ j, S.rank j < S.rank i → S.br x j = S.br y j := by
  constructor
  · intro h j hj
    have hj' := congrFun h j
    simp only [node, if_pos hj, Option.some.injEq] at hj'
    exact hj'
  · intro h
    funext j
    simp only [node]
    by_cases hj : S.rank j < S.rank i
    · rw [if_pos hj, if_pos hj, h j hj]
    · rw [if_neg hj, if_neg hj]

/-! ## Exactly one first divergence -/

/-- The coordinate at which two branch sequences first differ. -/
noncomputable def divSet (x y : ι → σ) : Finset ι :=
  Finset.univ.filter fun i => S.br x i ≠ S.br y i ∧ S.node x i = S.node y i

lemma card_divSet {x y : ι → σ} (h : S.br x ≠ S.br y) : (S.divSet x y).card = 1 := by
  classical
  have hD : (Finset.univ.filter fun i => S.br x i ≠ S.br y i).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact ⟨i, by simpa using hi⟩
  obtain ⟨i₀, hmem, hmin⟩ :=
    Finset.exists_min_image (Finset.univ.filter fun i => S.br x i ≠ S.br y i)
      S.rank hD
  rw [Finset.mem_filter] at hmem
  have hlow : ∀ j, S.rank j < S.rank i₀ → S.br x j = S.br y j := by
    intro j hj
    by_contra hne
    exact absurd (hmin j (by simpa using hne)) (by omega)
  rw [Finset.card_eq_one]
  refine ⟨i₀, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, fun i hi => ?_⟩⟩
  · simp only [divSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hmem.2, S.node_eq_iff.2 hlow⟩
  · simp only [divSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have h1 : S.rank i₀ ≤ S.rank i := hmin i (by simpa using hi.1)
    have h2 : ¬ S.rank i₀ < S.rank i := fun hlt =>
      hmem.2 (S.node_eq_iff.1 hi.2 i₀ hlt)
    exact S.rank_inj (le_antisymm (by omega) h1)

lemma card_divSet_of_out_ne {x y : ι → σ} (h : S.out x ≠ S.out y) :
    (S.divSet x y).card = 1 :=
  S.card_divSet fun hbr => h (S.out_eq x y (congrFun hbr))

end Scan

end QuantumQueryComplexity
