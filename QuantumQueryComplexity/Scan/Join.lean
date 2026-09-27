import QuantumQueryComplexity.Scan.Max
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The join scan

A commutative idempotent semigroup is a join-semilattice: `a ≤ b ↔ a * b = b`
and `a ⊔ b = a * b`.  The product of the letters read at the query positions is
therefore the join `⋁ᵢ m (x i)`, and this file scans it exactly as
`QuantumQueryComplexity/Scan/Max.lean` scans a maximum.

Two things change, and only two.

* **Red means `¬ (new ≤ running)`, not "the running value increases strictly".**
  In a partial order a new element may be *incomparable* with the running join;
  that is a genuine update and must be red.  Writing the condition as
  `running < new` would be wrong, and would silently reduce to the maximum case.
* **The output is a `sup'`, not an attained maximum.**  `maxFun_eq_sup_runAfter`
  picks a coordinate realising the maximum; here the corresponding identity is
  proved by two order inequalities instead.

Everything else — `runBefore`, `runAfter`, and the fact that equal branch
prefixes give equal running values — is reused verbatim from `Scan/Max.lean`,
whose running-value section needs only a `SemilatticeSup`.

The red condition is not decidable for an abstract semilattice, so `Classical`
supplies the instance once, inside the definition of `isJoinRecord`; downstream
files use only `isJoinRecord_eq_true_iff` and `isJoinRecord_eq_false_iff` and
never see it.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Type*} [SemilatticeSup A]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-! ## The product

The product needs no finiteness of the value type: it is one `sup'`.  Keeping
this section free of `Fintype A` permits a possibly infinite ambient
semilattice; only the input positions and alphabet must be finite. -/

/-- The join of the values read at the query positions: the product of the
letters in a commutative idempotent semigroup. -/
noncomputable def joinMap (m : σ → A) (x : ι → σ) : A :=
  Finset.univ.sup' Finset.univ_nonempty fun i => m (x i)

lemma le_joinMap (m : σ → A) (x : ι → σ) (i : ι) : m (x i) ≤ joinMap m x :=
  Finset.le_sup' (f := fun i => m (x i)) (Finset.mem_univ i)

lemma joinMap_le {m : σ → A} {x : ι → σ} {b : A} (h : ∀ i, m (x i) ≤ b) :
    joinMap m x ≤ b := Finset.sup'_le _ _ fun i _ => h i

/-! ## The scan needs a finite value type -/

variable [Fintype A] [DecidableEq A]

/-- The product, as a supremum in `WithBot A`. -/
lemma coe_joinMap (m : σ → A) (x : ι → σ) :
    ((joinMap m x : A) : WithBot A)
      = Finset.univ.sup fun i => ((m (x i) : A) : WithBot A) := by
  rw [joinMap, Finset.coe_sup']
  rfl

/-! ## The scan -/

open scoped Classical in
/-- **A red step**: the new value is *not* below the running join.  In a partial
order this is strictly weaker than "the running join grows", and it is the
correct condition. -/
noncomputable def isJoinRecord (rk : ι → Fin (Fintype.card ι)) (x : ι → A)
    (i : ι) : Bool :=
  decide (¬ (x i : WithBot A) ≤ runBefore rk x i)

lemma isJoinRecord_eq_true_iff (rk : ι → Fin (Fintype.card ι)) (x : ι → A)
    (i : ι) :
    isJoinRecord rk x i = true ↔ ¬ (x i : WithBot A) ≤ runBefore rk x i := by
  classical
  simp [isJoinRecord]

lemma isJoinRecord_eq_false_iff (rk : ι → Fin (Fintype.card ι)) (x : ι → A)
    (i : ι) :
    isJoinRecord rk x i = false ↔ (x i : WithBot A) ≤ runBefore rk x i := by
  classical
  simp [isJoinRecord]

lemma runAfter_eq_of_not_joinRecord {rk : ι → Fin (Fintype.card ι)} {x : ι → A}
    {i : ι} (h : isJoinRecord rk x i = false) :
    runAfter rk x i = runBefore rk x i :=
  sup_eq_left.2 ((isJoinRecord_eq_false_iff rk x i).1 h)

/-- The product is the join of the branch labels. -/
lemma joinMap_eq_sup_runAfter (m : σ → A) (rk : ι → Fin (Fintype.card ι))
    (x : ι → σ) :
    ((joinMap m x : A) : WithBot A)
      = Finset.univ.sup fun i => runAfter rk (fun j => m (x j)) i := by
  rw [coe_joinMap]
  refine le_antisymm (Finset.sup_le fun i _ => ?_) (Finset.sup_le fun i _ => ?_)
  · exact le_trans (le_runAfter rk (fun j => m (x j)) i)
      (Finset.le_sup (Finset.mem_univ i))
  · refine sup_le (runBefore_le fun j _ => ?_) ?_
    · exact Finset.le_sup (f := fun i => ((m (x i) : A) : WithBot A))
        (Finset.mem_univ j)
    · exact Finset.le_sup (f := fun i => ((m (x i) : A) : WithBot A))
        (Finset.mem_univ i)

/-- **The join scan**, for a given order of the coordinates and a value map
`m : σ → A`. -/
noncomputable def joinScanMap (m : σ → A) (rk : ι → Fin (Fintype.card ι))
    (hrk : Function.Injective rk) : Scan ι σ A (WithBot A) where
  rank := rk
  rank_inj := hrk
  br x i := runAfter rk (fun j => m (x j)) i
  col x i := isJoinRecord rk (fun j => m (x j)) i
  out x := joinMap m x
  br_ne x y i hpre hbr := by
    intro hxy
    exact hbr (by rw [runAfter, runAfter, runBefore_congr hpre, hxy])
  out_eq x y h := by
    have hc : ((joinMap m x : A) : WithBot A) = ((joinMap m y : A) : WithBot A) := by
      rw [joinMap_eq_sup_runAfter m rk, joinMap_eq_sup_runAfter m rk]
      exact Finset.sup_congr rfl fun i _ => h i
    exact_mod_cast hc
  black_unique x y i hx hy hpre := by
    rw [runAfter_eq_of_not_joinRecord hx, runAfter_eq_of_not_joinRecord hy,
      runBefore_congr hpre]

end QuantumQueryComplexity
