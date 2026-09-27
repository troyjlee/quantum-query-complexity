import QuantumQueryComplexity.Scan.Record
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# A fixed coordinate sits at a uniform time

Over all scan orders, a *fixed* coordinate is scanned at each time equally
often:

  `n * |{e | e i₀ = t}| = |orders|`.

The proof is the same shape as the record lemma but simpler: the sets
`{e | e i₀ = t}` for `t` ranging over all times are pairwise disjoint,
equinumerous (compose with the transposition of times `t` and `t'`), and
together exhaust every order.  Here the union is *all* orders, so the relation
is an equality rather than an inequality.

This is what a *weighted* scan needs and the unweighted one does not.  Weighting
coordinate `p` by `c p` turns the cost into `∑ p, (c p)² · f(time of p)`, and
uniformity replaces `f(time of p)` by its average over times, decoupling the
weights from the order.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The orders that scan `i₀` at time `t`. -/
def posSet (i₀ : ι) (t : Fin (Fintype.card ι)) : Finset (Order ι) :=
  Finset.univ.filter fun e => e i₀ = t

lemma mem_posSet {i₀ : ι} {t : Fin (Fintype.card ι)} {e : Order ι} :
    e ∈ posSet i₀ t ↔ e i₀ = t := by simp [posSet]

lemma posSet_disjoint (i₀ : ι) {t₁ t₂ : Fin (Fintype.card ι)} (h : t₁ ≠ t₂) :
    Disjoint (posSet i₀ t₁) (posSet i₀ t₂) := by
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  exact h ((mem_posSet.1 he₁).symm.trans (mem_posSet.1 he₂))

/-- Composing with the transposition of two times matches the two events. -/
lemma card_posSet_eq (i₀ : ι) (t₁ t₂ : Fin (Fintype.card ι)) :
    (posSet i₀ t₁).card = (posSet i₀ t₂).card := by
  classical
  refine Finset.card_nbij' (fun e => e.trans (Equiv.swap t₁ t₂))
    (fun e => e.trans (Equiv.swap t₁ t₂)) ?_ ?_ ?_ ?_
  · intro e he
    simp only [Finset.mem_coe, mem_posSet] at he ⊢
    simp [he, Equiv.swap_apply_left]
  · intro e he
    simp only [Finset.mem_coe, mem_posSet] at he ⊢
    simp [he, Equiv.swap_apply_right]
  · intro e _
    simp [Equiv.trans_assoc]
  · intro e _
    simp [Equiv.trans_assoc]

/-- Every order scans `i₀` at some time. -/
lemma posSet_biUnion (i₀ : ι) :
    (Finset.univ.biUnion fun t : Fin (Fintype.card ι) => posSet i₀ t)
      = (Finset.univ : Finset (Order ι)) := by
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true, mem_posSet]
  exact ⟨e i₀, rfl⟩

/-- **A fixed coordinate is scanned at a uniform time.** -/
theorem card_posSet_mul (i₀ : ι) (t : Fin (Fintype.card ι)) :
    Fintype.card ι * (posSet i₀ t).card = Fintype.card (Order ι) := by
  classical
  have hcard : (Finset.univ.biUnion fun t' : Fin (Fintype.card ι) => posSet i₀ t').card
      = ∑ t' : Fin (Fintype.card ι), (posSet i₀ t').card :=
    Finset.card_biUnion fun t₁ _ t₂ _ hne => posSet_disjoint i₀ hne
  have hconst : ∑ t' : Fin (Fintype.card ι), (posSet i₀ t').card
      = ∑ _t' : Fin (Fintype.card ι), (posSet i₀ t).card :=
    Finset.sum_congr rfl fun t' _ => card_posSet_eq i₀ t' t
  calc Fintype.card ι * (posSet i₀ t).card
      = ∑ _t' : Fin (Fintype.card ι), (posSet i₀ t).card := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ = (Finset.univ.biUnion fun t' : Fin (Fintype.card ι) => posSet i₀ t').card := by
        rw [hcard, hconst]
    _ = Fintype.card (Order ι) := by
        rw [posSet_biUnion, Finset.card_univ]

/-- Averaging a function of the scan time of a fixed coordinate. -/
theorem sum_orders_time (i₀ : ι) (F : Fin (Fintype.card ι) → ℝ) :
    (Fintype.card ι : ℝ) * ∑ e : Order ι, F (e i₀)
      = (Fintype.card (Order ι) : ℝ) * ∑ t : Fin (Fintype.card ι), F t := by
  classical
  have hsplit : (∑ e : Order ι, F (e i₀))
      = ∑ t : Fin (Fintype.card ι), ((posSet i₀ t).card : ℝ) * F t := by
    rw [← posSet_biUnion i₀, Finset.sum_biUnion
      (fun t₁ _ t₂ _ hne => posSet_disjoint i₀ hne)]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_congr rfl fun e (he : e ∈ posSet i₀ t) => by
      rw [mem_posSet.1 he], Finset.sum_const, nsmul_eq_mul]
  rw [hsplit, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h := card_posSet_mul i₀ t
  have hr : (Fintype.card ι : ℝ) * ((posSet i₀ t).card : ℝ)
      = (Fintype.card (Order ι) : ℝ) := by exact_mod_cast h
  rw [← mul_assoc, hr]

/-! ## The other direction: a fixed *time* holds a uniform coordinate

The same partition read the other way.  For a fixed time `t`, the sets
`{e | e i = t}` now range over `i` rather than over `t`; they are still pairwise
disjoint (an order scans one coordinate at a time), still exhaust every order,
and still all have the same size.  So the coordinate occupying a *fixed* time is
uniformly distributed, which is what averages a coordinate-dependent weight. -/

lemma posSet_disjoint' (t : Fin (Fintype.card ι)) {i₁ i₂ : ι} (h : i₁ ≠ i₂) :
    Disjoint (posSet i₁ t) (posSet i₂ t) := by
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  exact h (e.injective ((mem_posSet.1 he₁).trans (mem_posSet.1 he₂).symm))

lemma posSet_biUnion' (t : Fin (Fintype.card ι)) :
    (Finset.univ.biUnion fun i : ι => posSet i t)
      = (Finset.univ : Finset (Order ι)) := by
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true, mem_posSet]
  exact ⟨e.symm t, e.apply_symm_apply t⟩

/-- **The coordinate scanned at a fixed time is uniform.** -/
theorem sum_orders_coord (t : Fin (Fintype.card ι)) (G : ι → ℝ) :
    (Fintype.card ι : ℝ) * ∑ e : Order ι, G (e.symm t)
      = (Fintype.card (Order ι) : ℝ) * ∑ i : ι, G i := by
  classical
  have hsplit : (∑ e : Order ι, G (e.symm t))
      = ∑ i : ι, ((posSet i t).card : ℝ) * G i := by
    rw [← posSet_biUnion' t, Finset.sum_biUnion
      (fun i₁ _ i₂ _ hne => posSet_disjoint' t hne)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl fun e (he : e ∈ posSet i t) =>
      show G (e.symm t) = G i from by
        rw [show e.symm t = i from by rw [← mem_posSet.1 he, Equiv.symm_apply_apply]],
      Finset.sum_const, nsmul_eq_mul]
  rw [hsplit, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hr : (Fintype.card ι : ℝ) * ((posSet i t).card : ℝ)
      = (Fintype.card (Order ι) : ℝ) := by exact_mod_cast card_posSet_mul i t
  rw [← mul_assoc, hr]

end QuantumQueryComplexity
