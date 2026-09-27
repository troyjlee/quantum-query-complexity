import QuantumQueryComplexity.Scan.Dual
import QuantumQueryComplexity.Max.Defs
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The maximum scan

Scan the coordinates in a fixed order, keeping the largest value seen.  At each
step the branch is black when the new value does not beat the running maximum,
and is the red singleton `{x i}` when it does.

The branch label is taken to be the **running maximum after scanning `i`**,
`runAfter`.  This is what makes the three `Scan` conditions nearly free, and it
avoids induction entirely:

* the running maximum *before* `i` is the sup of the labels strictly before `i`,
  so equal branch prefixes give equal running maxima — no recursion needed;
* `br_ne` then says `a ⊔ x i ≠ a ⊔ y i → x i ≠ y i`, which is immediate;
* `black_unique` says two non-records at the same node take the same branch —
  both labels are just the running maximum `a`;
* `out_eq` holds because `maxFun x` is the sup of the labels.

A branch is red exactly when the step is a *strict record*.  That is the event
whose probability, over a uniformly random scan order, is at most `1/t` — the
estimate that will make the weighted cost `O(√n)`.
-/

namespace QuantumQueryComplexity

/-- `WithBot α` is definitionally `Option α`; mathlib carries no `Fintype`
instance for it, and the scan needs one because the branch labels are running
maxima. -/
instance instFintypeWithBot {A : Type*} [Fintype A] : Fintype (WithBot A) :=
  inferInstanceAs (Fintype (Option A))

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-! ## The running join

Nothing about the *running value* of a scan needs a linear order: it is a
supremum, so a `SemilatticeSup` suffices.  Keeping this section general is what
lets `QuantumQueryComplexity/Scan/Join.lean` reuse it for products in a commutative
idempotent semigroup, where two values may be incomparable. -/

section Sup

variable [SemilatticeSup A]

/-- The coordinates scanned strictly before `i`. -/
def beforeSet (rk : ι → Fin (Fintype.card ι)) (i : ι) : Finset ι :=
  Finset.univ.filter fun j => rk j < rk i

/-- The running maximum strictly before `i` (`⊥` if nothing has been scanned). -/
def runBefore (rk : ι → Fin (Fintype.card ι)) (x : ι → A) (i : ι) : WithBot A :=
  (beforeSet rk i).sup fun j => (x j : WithBot A)

/-- The running maximum up to and including `i`. -/
def runAfter (rk : ι → Fin (Fintype.card ι)) (x : ι → A) (i : ι) : WithBot A :=
  runBefore rk x i ⊔ (x i : WithBot A)

lemma le_runBefore {rk : ι → Fin (Fintype.card ι)} {x : ι → A} {i j : ι}
    (h : rk j < rk i) : (x j : WithBot A) ≤ runBefore rk x i :=
  Finset.le_sup (f := fun j => (x j : WithBot A))
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)

lemma runBefore_le {rk : ι → Fin (Fintype.card ι)} {x : ι → A} {i : ι}
    {b : WithBot A} (h : ∀ j, rk j < rk i → (x j : WithBot A) ≤ b) :
    runBefore rk x i ≤ b :=
  Finset.sup_le fun j hj => h j (by simpa [beforeSet] using hj)

lemma le_runAfter (rk : ι → Fin (Fintype.card ι)) (x : ι → A) (i : ι) :
    (x i : WithBot A) ≤ runAfter rk x i := le_sup_right

/-- **The running maximum before `i` is the sup of the branch labels before
`i`.**  This is what replaces an induction on the scan order. -/
lemma runBefore_eq_sup_runAfter (rk : ι → Fin (Fintype.card ι)) (x : ι → A)
    (i : ι) :
    runBefore rk x i = (beforeSet rk i).sup fun j => runAfter rk x j := by
  refine le_antisymm (Finset.sup_le fun j hj => ?_) (Finset.sup_le fun j hj => ?_)
  · exact le_trans (le_runAfter rk x j) (Finset.le_sup hj)
  · have hj' : rk j < rk i := by simpa [beforeSet] using hj
    refine sup_le (runBefore_le fun j' hj'' => ?_) (le_runBefore hj')
    exact le_runBefore (lt_trans hj'' hj')

/-- Equal branch prefixes give equal running maxima. -/
lemma runBefore_congr {rk : ι → Fin (Fintype.card ι)} {x y : ι → A} {i : ι}
    (h : ∀ j, rk j < rk i → runAfter rk x j = runAfter rk y j) :
    runBefore rk x i = runBefore rk y i := by
  rw [runBefore_eq_sup_runAfter, runBefore_eq_sup_runAfter]
  refine Finset.sup_congr rfl fun j hj => ?_
  exact h j (by simpa [beforeSet] using hj)

end Sup

/-! ## The maximum scan -/

variable [LinearOrder A]

/-- `maxFun` is the sup of the branch labels. -/
lemma maxFun_eq_sup_runAfter (rk : ι → Fin (Fintype.card ι)) (x : ι → A) :
    ((maxFun x : A) : WithBot A) = Finset.univ.sup fun i => runAfter rk x i := by
  refine le_antisymm ?_ (Finset.sup_le fun i _ => ?_)
  · obtain ⟨i, hi⟩ := exists_eq_maxFun x
    rw [← hi]
    exact le_trans (le_runAfter rk x i) (Finset.le_sup (Finset.mem_univ i))
  · refine sup_le (runBefore_le fun j _ => ?_) ?_
    · exact_mod_cast le_maxFun x j
    · exact_mod_cast le_maxFun x i

/-! ## The scan -/

/-- Whether scanning `i` sets a strict record. -/
def isRecord (rk : ι → Fin (Fintype.card ι)) (x : ι → A) (i : ι) : Bool :=
  decide (runBefore rk x i < (x i : WithBot A))

lemma runAfter_eq_of_not_record {rk : ι → Fin (Fintype.card ι)} {x : ι → A}
    {i : ι} (h : isRecord rk x i = false) : runAfter rk x i = runBefore rk x i := by
  simp only [isRecord, decide_eq_false_iff_not, not_lt] at h
  exact sup_eq_left.2 h

/-- **The maximum scan**, for a given order of the coordinates and a given
*value map* `m : σ → A`.

The letters read by the queries need not be the values being maximised: a query
returns a whole letter `x i : σ`, and the quantity of interest is the largest
`m (x i)`.  This costs the construction nothing, because the three `Scan`
conditions only ever go in the direction "differing branch ⟹ differing letter",
and `m (x i) ≠ m (y i)` certainly forces `x i ≠ y i`.  A non-injective `m` is
therefore fine — which matters, since the entries of distinct letter matrices
routinely coincide. -/
noncomputable def maxScanMap (m : σ → A) (rk : ι → Fin (Fintype.card ι))
    (hrk : Function.Injective rk) : Scan ι σ A (WithBot A) where
  rank := rk
  rank_inj := hrk
  br x i := runAfter rk (fun j => m (x j)) i
  col x i := isRecord rk (fun j => m (x j)) i
  out x := maxFun fun j => m (x j)
  br_ne x y i hpre hbr := by
    intro hxy
    exact hbr (by rw [runAfter, runAfter, runBefore_congr hpre, hxy])
  out_eq x y h := by
    have : ((maxFun fun j => m (x j) : A) : WithBot A)
        = ((maxFun fun j => m (y j) : A) : WithBot A) := by
      rw [maxFun_eq_sup_runAfter rk, maxFun_eq_sup_runAfter rk]
      exact Finset.sup_congr rfl fun i _ => h i
    exact_mod_cast this
  black_unique x y i hx hy hpre := by
    rw [runAfter_eq_of_not_record hx, runAfter_eq_of_not_record hy,
      runBefore_congr hpre]

/-- The maximum scan of the input itself: the value map is the identity. -/
noncomputable def maxScan (rk : ι → Fin (Fintype.card ι))
    (hrk : Function.Injective rk) : Scan ι A A (WithBot A) :=
  maxScanMap id rk hrk

end QuantumQueryComplexity
