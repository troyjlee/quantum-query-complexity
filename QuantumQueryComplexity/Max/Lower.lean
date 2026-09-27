import QuantumQueryComplexity.Star
import QuantumQueryComplexity.Max.Defs
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# `ADV±(MAX) ≥ √n`

Restricted to tuples valued in a two-element subset `{lo, hi}` of the alphabet,
`maxFun` *is* the `n`-bit OR: it returns `hi` exactly when some coordinate holds
`hi`.  So the OR witness transports verbatim — the star matrix centred at the
constant-`lo` tuple, with one leaf for each tuple holding `hi` in exactly one
coordinate.

Its norm is `√n` and each of its masked norms is `1` (masking at coordinate `j`
retains only the single leaf that differs from the centre there), giving
`√n ≤ advPM maxFun`.  Together with `QuantumQueryComplexity/Max/Dyadic.lean` this pins
`advPM maxFun` to within a factor `2⌈log₂ m⌉`.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Type*} [Fintype A] [DecidableEq A] [LinearOrder A]
variable {lo hi : A}

/-- The constant tuple. -/
def constVec (lo : A) : ι → A := fun _ => lo

/-- The tuple holding `hi` at `i` and `lo` elsewhere. -/
def spikeVec (lo hi : A) (i : ι) : ι → A := fun j => if j = i then hi else lo

@[simp] lemma constVec_apply (lo : A) (j : ι) : (constVec lo : ι → A) j = lo := rfl

@[simp] lemma spikeVec_apply (lo hi : A) (i j : ι) :
    spikeVec lo hi i j = if j = i then hi else lo := rfl

lemma maxFun_constVec (lo : A) : maxFun (constVec lo : ι → A) = lo :=
  maxFun_eq_iff.mpr ⟨⟨Classical.arbitrary ι, rfl⟩, fun _ => le_rfl⟩

lemma maxFun_spikeVec (h : lo < hi) (i : ι) :
    maxFun (spikeVec lo hi i : ι → A) = hi := by
  refine maxFun_eq_iff.mpr ⟨⟨i, by simp⟩, fun j => ?_⟩
  by_cases hj : j = i <;> simp [hj, h.le]

lemma spikeVec_injective (h : lo < hi) :
    Function.Injective (spikeVec lo hi : ι → (ι → A)) := by
  intro i j hij
  by_contra hne
  have hii := congrFun hij i
  rw [spikeVec_apply, spikeVec_apply, if_neg hne, if_pos (rfl : i = i)] at hii
  exact h.ne' hii

/-- The leaf set: one tuple per coordinate. -/
noncomputable def spikeSet (lo hi : A) : Finset (ι → A) :=
  Finset.univ.image (spikeVec lo hi)

lemma mem_spikeSet {z : ι → A} :
    z ∈ (spikeSet lo hi : Finset (ι → A)) ↔ ∃ i, spikeVec lo hi i = z := by
  simp [spikeSet]

lemma card_spikeSet (h : lo < hi) :
    (spikeSet lo hi : Finset (ι → A)).card = Fintype.card ι := by
  rw [spikeSet, Finset.card_image_of_injective _ (spikeVec_injective h),
    Finset.card_univ]

lemma constVec_notMem_spikeSet (h : lo < hi) :
    (constVec lo : ι → A) ∉ spikeSet lo hi := by
  intro hc
  obtain ⟨i, hi'⟩ := mem_spikeSet.mp hc
  have := congrFun hi' i
  rw [spikeVec_apply, if_pos rfl, constVec_apply] at this
  exact h.ne' this

/-- The star matrix is an adversary matrix for `maxFun`: its only nonzero
entries pair the constant tuple (max `lo`) with a spike (max `hi`). -/
lemma maxFun_isAdvMatrix (h : lo < hi) :
    IsAdvMatrix (maxFun : (ι → A) → A)
      (starMatrix (spikeSet lo hi) (constVec lo)) := by
  refine ⟨starMatrix_isHermitian _ _, fun x y hxy => ?_⟩
  rw [starMatrix, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun z hz => ?_
  obtain ⟨i, rfl⟩ := mem_spikeSet.mp hz
  refine pairMatrix_apply_eq_zero ?_ ?_
  · rintro ⟨rfl, rfl⟩
    rw [maxFun_spikeVec h, maxFun_constVec] at hxy
    exact h.ne' hxy
  · rintro ⟨rfl, rfl⟩
    rw [maxFun_spikeVec h, maxFun_constVec] at hxy
    exact h.ne hxy

/-- Masking at coordinate `j` retains exactly the leaf `spikeVec lo hi j`. -/
lemma spikeSet_filter (h : lo < hi) (j : ι) :
    ((spikeSet lo hi : Finset (ι → A)).filter
      fun z => ¬(z j = (constVec lo : ι → A) j)) = {spikeVec lo hi j} := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_singleton, mem_spikeSet]
  constructor
  · rintro ⟨⟨i, rfl⟩, hz⟩
    by_cases hij : j = i
    · rw [hij]
    · exact absurd (by rw [spikeVec_apply, if_neg hij, constVec_apply]) hz
  · rintro rfl
    refine ⟨⟨j, rfl⟩, ?_⟩
    rw [spikeVec_apply, if_pos rfl, constVec_apply]
    exact h.ne'

lemma maxFun_feasible (h : lo < hi) (j : ι) :
    ‖starMatrix (spikeSet lo hi : Finset (ι → A)) (constVec lo) ⊙ advD j‖ ≤ 1 := by
  rw [starMatrix_hadamard_advD, spikeSet_filter h, starMatrix, Finset.sum_singleton,
    norm_pairMatrix]
  intro hcon
  have := congrFun hcon j
  rw [spikeVec_apply, if_pos rfl, constVec_apply] at this
  exact h.ne' this

/-- **`√n ≤ ADV±(MAX)`** whenever the alphabet has two distinct values. -/
theorem sqrt_card_le_advPM_maxFun (h : lo < hi) :
    Real.sqrt (Fintype.card ι : ℝ) ≤ advPM (maxFun : (ι → A) → A) := by
  have hne : (spikeSet lo hi : Finset (ι → A)).Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨spikeVec lo hi i, mem_spikeSet.mpr ⟨i, rfl⟩⟩
  have h1 : ‖starMatrix (spikeSet lo hi : Finset (ι → A)) (constVec lo)‖
      ≤ advPM (maxFun : (ι → A) → A) :=
    le_advPM (maxFun_isAdvMatrix h) (maxFun_feasible h)
  rwa [norm_starMatrix (constVec_notMem_spikeSet h) hne, card_spikeSet h] at h1

end QuantumQueryComplexity
