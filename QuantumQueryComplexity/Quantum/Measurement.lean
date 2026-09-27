import QuantumQueryComplexity.Quantum.FiniteHilbert
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Computational-basis measurement

A measurement of the final state of a query algorithm is a projective
measurement in the computational basis, coarse-grained by a **readout map**
`p : H → O` that says which output each basis state announces.  So the only
definition needed is

  `qProb p ψ o = ∑ h with p h = o, ‖ψ h‖²`,

the probability of announcing `o`.  Deferring all measurements to the end is
without loss of generality in the query model, and general POVMs are not needed
for the characterization (see the plan, §"Design Decisions").

The companion definition `qRestrict p o ψ` is the unnormalized post-measurement
state; it is what turns statements about probabilities into statements about
inner products, which is how the adversary lower bound consumes the output
condition (`∑ o, qRestrict p o ψ = ψ`, and distinct outcomes are orthogonal).
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H : Type*} [Fintype H] [DecidableEq H]
variable {O : Type*} [DecidableEq O]

/-- The unnormalized part of `ψ` that announces the outcome `o`. -/
def qRestrict (p : H → O) (o : O) (ψ : H → ℂ) : H → ℂ :=
  fun h => if p h = o then ψ h else 0

/-- **The probability that measuring `ψ` announces the outcome `o`.** -/
def qProb (p : H → O) (ψ : H → ℂ) (o : O) : ℝ :=
  ∑ h, if p h = o then Complex.normSq (ψ h) else 0

lemma qProb_eq_qNormSq_qRestrict (p : H → O) (ψ : H → ℂ) (o : O) :
    qProb p ψ o = qNormSq (qRestrict p o ψ) := by
  rw [qProb, qNormSq_def]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [qRestrict]
  by_cases hh : p h = o <;> simp [hh]

lemma qProb_nonneg (p : H → O) (ψ : H → ℂ) (o : O) : 0 ≤ qProb p ψ o := by
  rw [qProb_eq_qNormSq_qRestrict]
  exact qNormSq_nonneg _

/-- Measuring a basis state announces its readout with certainty. -/
@[simp] lemma qProb_qBasis (p : H → O) (h : H) (o : O) :
    qProb p (qBasis h) o = if p h = o then 1 else 0 := by
  rw [qProb, Finset.sum_eq_single h]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-! ## The distance-to-success bridge

None of this needs `[Fintype O]` — the sums range over `H` alone — and the
cardinality-free extraction depends on exactly that: the bridge from a
conversion-distance bound to a success probability must not reintroduce an
output-cardinality assumption. -/

/-- The part of `ψ` that does **not** announce `o`. -/
lemma qNormSq_sub_qRestrict (p : H → O) (o : O) (ψ : H → ℂ) :
    qNormSq (ψ - qRestrict p o ψ) = qNormSq ψ - qProb p ψ o := by
  rw [qNormSq_def, qNormSq_def, qProb, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Pi.sub_apply, qRestrict]
  by_cases hh : p h = o <;> simp [hh]

/-- **Restriction is the best sector approximation**: against any `φ`
supported on the `o`-sector, the unannounced mass of `ψ` is dominated. -/
lemma qNormSq_sub_qRestrict_le (p : H → O) (o : O) (ψ : H → ℂ)
    {φ : H → ℂ} (hφ : qRestrict p o φ = φ) :
    qNormSq (ψ - qRestrict p o ψ) ≤ qNormSq (ψ - φ) := by
  rw [qNormSq_def, qNormSq_def]
  refine Finset.sum_le_sum fun h _ => ?_
  by_cases hh : p h = o
  · simp only [Pi.sub_apply, qRestrict, hh, if_pos]
    simp only [sub_self, Complex.normSq_zero]
    exact Complex.normSq_nonneg _
  · have hφh : φ h = 0 := by rw [← hφ, qRestrict, if_neg hh]
    simp [Pi.sub_apply, qRestrict, hh, hφh]

/-- **The distance-to-success bridge**, output-cardinality-free: a state
within squared distance `δ` of one supported on the `o`-sector announces
`o` with probability at least `qNormSq ψ − δ`. -/
lemma le_qProb_of_qNormSq_sub_le (p : H → O) (o : O) {ψ φ : H → ℂ}
    (hφ : qRestrict p o φ = φ) {δ : ℝ} (h : qNormSq (ψ - φ) ≤ δ) :
    qNormSq ψ - δ ≤ qProb p ψ o := by
  have h1 := qNormSq_sub_qRestrict p o ψ
  have h2 := qNormSq_sub_qRestrict_le p o ψ hφ
  linarith

/-! ## The outcomes partition the norm -/

variable [Fintype O]

lemma sum_qProb (p : H → O) (ψ : H → ℂ) : ∑ o, qProb p ψ o = qNormSq ψ := by
  simp only [qProb, qNormSq_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp

/-- On a state the outcome probabilities sum to one. -/
lemma sum_qProb_eq_one {ψ : H → ℂ} (hψ : IsQState ψ) (p : H → O) :
    ∑ o, qProb p ψ o = 1 := by
  rw [sum_qProb]
  exact hψ

lemma qProb_le_qNormSq (p : H → O) (ψ : H → ℂ) (o : O) :
    qProb p ψ o ≤ qNormSq ψ := by
  rw [← sum_qProb p ψ]
  exact Finset.single_le_sum (f := fun o => qProb p ψ o)
    (fun o _ => qProb_nonneg p ψ o) (Finset.mem_univ o)

lemma qProb_le_one {ψ : H → ℂ} (hψ : IsQState ψ) (p : H → O) (o : O) :
    qProb p ψ o ≤ 1 := by
  rw [← hψ]
  exact qProb_le_qNormSq p ψ o

/-- **Two distinct outcomes cannot both be likely.**  This is what forbids a
single state from answering two different questions, and hence what makes the
query model unable to compute an unobservable distinction. -/
lemma qProb_add_qProb_le_qNormSq (p : H → O) (ψ : H → ℂ) {a b : O} (hab : a ≠ b) :
    qProb p ψ a + qProb p ψ b ≤ qNormSq ψ := by
  rw [← sum_qProb p ψ]
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ ({a, b} : Finset O))
    (fun o _ _ => qProb_nonneg p ψ o)
  rwa [Finset.sum_pair hab] at h

lemma qProb_add_qProb_le_one {ψ : H → ℂ} (hψ : IsQState ψ) (p : H → O) {a b : O}
    (hab : a ≠ b) : qProb p ψ a + qProb p ψ b ≤ 1 := by
  rw [← hψ]
  exact qProb_add_qProb_le_qNormSq p ψ hab

/-- The probability of announcing anything other than `o` is `1 - qProb p ψ o`. -/
lemma sum_qProb_ne {ψ : H → ℂ} (hψ : IsQState ψ) (p : H → O) (o : O) :
    ∑ o' ∈ Finset.univ.erase o, qProb p ψ o' = 1 - qProb p ψ o := by
  have h := sum_qProb_eq_one hψ p
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ o)] at h
  linarith

/-! ## The post-measurement decomposition -/

lemma sum_qRestrict (p : H → O) (ψ : H → ℂ) : ∑ o, qRestrict p o ψ = ψ := by
  funext h
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single (p h)]
  · simp [qRestrict]
  · intro b _ hb
    simp [qRestrict, Ne.symm hb]
  · simp

/-- **The inner product decomposes over the outcomes.**  This is the form the
adversary lower bound uses, with the readout map taken to be the query-index
register: it splits a state into the sectors the oracle acts on independently. -/
lemma qInner_eq_sum_qRestrict (p : H → O) (ψ φ : H → ℂ) :
    qInner ψ φ = ∑ o, qInner (qRestrict p o ψ) (qRestrict p o φ) := by
  have key : ∀ (o : O) (h : H),
      star (qRestrict p o ψ h) * qRestrict p o φ h
        = if p h = o then star (ψ h) * φ h else 0 := by
    intro o h
    rw [qRestrict, qRestrict]
    by_cases hh : p h = o <;> simp [hh]
  calc qInner ψ φ = ∑ h, star (ψ h) * φ h := qInner_def ψ φ
    _ = ∑ h, ∑ o, (if p h = o then star (ψ h) * φ h else 0) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Finset.sum_ite_eq Finset.univ (p h) (fun _ => star (ψ h) * φ h),
          if_pos (Finset.mem_univ _)]
    _ = ∑ o, ∑ h, (if p h = o then star (ψ h) * φ h else 0) := Finset.sum_comm
    _ = ∑ o, qInner (qRestrict p o ψ) (qRestrict p o φ) := by
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [qInner_def]
        exact Finset.sum_congr rfl fun h _ => (key o h).symm

/-- Distinct outcomes are orthogonal. -/
lemma qInner_qRestrict_of_ne (p : H → O) {a b : O} (hab : a ≠ b) (ψ φ : H → ℂ) :
    qInner (qRestrict p a ψ) (qRestrict p b φ) = 0 := by
  rw [qInner_def]
  refine Finset.sum_eq_zero fun h _ => ?_
  rw [qRestrict, qRestrict]
  by_cases ha : p h = a
  · have hb : ¬ p h = b := by rw [ha]; exact hab
    simp [hb]
  · simp [ha]

end QuantumQueryComplexity
