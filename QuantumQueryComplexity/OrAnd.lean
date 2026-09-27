import QuantumQueryComplexity.Star
import QuantumQueryComplexity.AndOr
set_option linter.style.header false

/-!
# `ADV±(OR_n) = ADV±(AND_n) = √n`

We compute the adversary bound of the `n`-bit OR and AND functions, with
matching dual certificates, so strong duality holds at them and they compose
perfectly.

* the primal witness for `OR_n` is the star matrix centred at the all-zero
  input with the `n` weight-one inputs as leaves (`QuantumQueryComplexity/Star.lean`);
  its norm is `√n` and each masked norm is `1`;
* the dual witness is one-dimensional: weight `δ = n^(-1/4)` at the all-zero
  input, and `1/(|x| δ)` on the support of each nonzero `x`, where `|x|` is
  the Hamming weight.  Its cost is exactly `√n`.

`AND_n` follows from `OR_n` by De Morgan, using the relabelling invariance
lemmas of `QuantumQueryComplexity/AndOr.lean`.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The `n`-bit OR function -/

/-- The all-zero input. -/
def zeroVec : ι → Bool := fun _ => false

/-- The input with a single `true` in position `i`. -/
def unitVec (i : ι) : ι → Bool := fun j => decide (j = i)

/-- The `n`-bit OR function. -/
def orN (x : ι → Bool) : Bool := decide (∃ i, x i = true)

/-- The `n`-bit AND function. -/
def andN (x : ι → Bool) : Bool := decide (∀ i, x i = true)

@[simp] lemma unitVec_apply (i j : ι) : unitVec i j = decide (j = i) := rfl

@[simp] lemma zeroVec_apply (j : ι) : (zeroVec : ι → Bool) j = false := rfl

lemma orN_eq_false_iff {x : ι → Bool} : orN x = false ↔ x = zeroVec := by
  simp only [orN, decide_eq_false_iff_not, not_exists]
  constructor
  · intro h
    funext j
    simpa using h j
  · rintro rfl j
    simp

lemma orN_eq_true_iff {x : ι → Bool} : orN x = true ↔ x ≠ zeroVec := by
  constructor
  · intro h hz
    rw [orN_eq_false_iff.mpr hz] at h
    exact Bool.noConfusion h
  · intro h
    rcases Bool.eq_false_or_eq_true (orN x) with h' | h'
    · exact h'
    · exact absurd (orN_eq_false_iff.mp h') h

lemma orN_zeroVec : orN (zeroVec : ι → Bool) = false := orN_eq_false_iff.mpr rfl

lemma orN_unitVec (i : ι) : orN (unitVec i) = true :=
  orN_eq_true_iff.mpr fun h => by
    have := congrFun h i
    simp at this

lemma unitVec_injective : Function.Injective (unitVec : ι → (ι → Bool)) := by
  intro i j h
  have := congrFun h i
  simpa using this.symm

/-- The leaf set of the `OR` star matrix. -/
noncomputable def unitSet : Finset (ι → Bool) := Finset.univ.image unitVec

lemma mem_unitSet {z : ι → Bool} : z ∈ (unitSet : Finset (ι → Bool)) ↔
    ∃ i, unitVec i = z := by
  simp [unitSet]

lemma card_unitSet : (unitSet : Finset (ι → Bool)).card = Fintype.card ι := by
  rw [unitSet, Finset.card_image_of_injective Finset.univ unitVec_injective,
    Finset.card_univ]

lemma zeroVec_notMem_unitSet : (zeroVec : ι → Bool) ∉ unitSet := by
  rw [mem_unitSet]
  rintro ⟨i, hi⟩
  have := congrFun hi i
  simp at this

/-! ## The primal witness -/

lemma orN_isAdvMatrix :
    IsAdvMatrix (orN : (ι → Bool) → Bool) (starMatrix unitSet zeroVec) := by
  refine ⟨starMatrix_isHermitian _ _, fun x y hxy => ?_⟩
  rw [starMatrix, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun z hz => ?_
  obtain ⟨i, rfl⟩ := mem_unitSet.mp hz
  refine pairMatrix_apply_eq_zero ?_ ?_
  · rintro ⟨rfl, rfl⟩
    rw [orN_unitVec, orN_zeroVec] at hxy
    exact Bool.noConfusion hxy
  · rintro ⟨rfl, rfl⟩
    rw [orN_unitVec, orN_zeroVec] at hxy
    exact Bool.noConfusion hxy

lemma unitSet_filter (j : ι) :
    ((unitSet : Finset (ι → Bool)).filter
      fun z => ¬(z j = (zeroVec : ι → Bool) j)) = {unitVec j} := by
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨mem_unitSet.mpr ⟨j, rfl⟩, ?_⟩
    rw [zeroVec_apply, unitVec_apply]
    simp
  · intro z hz
    obtain ⟨hzu, hzj⟩ := Finset.mem_filter.mp hz
    obtain ⟨i, rfl⟩ := mem_unitSet.mp hzu
    rw [zeroVec_apply, unitVec_apply] at hzj
    have hij : j = i := by
      by_contra hne
      exact hzj (by simp [hne])
    rw [hij]

lemma orN_feasible (j : ι) :
    ‖starMatrix (unitSet : Finset (ι → Bool)) zeroVec ⊙ advD j‖ ≤ 1 := by
  rw [starMatrix_hadamard_advD, unitSet_filter, starMatrix, Finset.sum_singleton,
    norm_pairMatrix]
  intro h
  have := congrFun h j
  simp at this

theorem sqrt_card_le_advPM_orN :
    Real.sqrt (Fintype.card ι : ℝ) ≤ advPM (orN : (ι → Bool) → Bool) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : Fintype.card ι = 0 := Fintype.card_eq_zero
    rw [this]
    simpa using advPM_nonneg (orN : (ι → Bool) → Bool)
  · have hne : (unitSet : Finset (ι → Bool)).Nonempty := by
      obtain ⟨i⟩ := hι
      exact ⟨unitVec i, mem_unitSet.mpr ⟨i, rfl⟩⟩
    have h := le_advPM (Γ := starMatrix (unitSet : Finset (ι → Bool)) zeroVec)
      orN_isAdvMatrix orN_feasible
    rwa [norm_starMatrix zeroVec_notMem_unitSet hne, card_unitSet] at h

/-! ## The dual witness -/

/-- The Hamming weight of an input. -/
def supportCard (x : ι → Bool) : ℕ :=
  (Finset.univ.filter fun i => x i = true).card

lemma supportCard_pos {x : ι → Bool} (hx : x ≠ zeroVec) : 0 < supportCard x := by
  rw [supportCard, Finset.card_pos]
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
  exact hx (funext fun i => by simpa using h (Finset.mem_univ i))

/-- `δ = n^(-1/4)`. -/
noncomputable def orNDelta (ι : Type*) [Fintype ι] : ℝ :=
  (Real.sqrt (Real.sqrt (Fintype.card ι : ℝ)))⁻¹

lemma orNDelta_pos [Nonempty ι] : 0 < orNDelta ι := by
  rw [orNDelta, inv_pos]
  refine Real.sqrt_pos.mpr (Real.sqrt_pos.mpr ?_)
  exact_mod_cast Fintype.card_pos

lemma orNDelta_ne_zero [Nonempty ι] : orNDelta ι ≠ 0 := ne_of_gt orNDelta_pos

/-- `δ² = 1/√n`. -/
lemma orNDelta_sq [Nonempty ι] :
    orNDelta ι * orNDelta ι = 1 / Real.sqrt (Fintype.card ι : ℝ) := by
  have hn : (0:ℝ) ≤ Real.sqrt (Fintype.card ι : ℝ) := Real.sqrt_nonneg _
  rw [orNDelta, ← mul_inv, Real.mul_self_sqrt hn, one_div]

/-- `n δ² = √n`. -/
lemma card_mul_orNDelta_sq [Nonempty ι] :
    (Fintype.card ι : ℝ) * (orNDelta ι * orNDelta ι)
      = Real.sqrt (Fintype.card ι : ℝ) := by
  have hpos : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι : ℝ)
      = (Fintype.card ι : ℝ) := Real.mul_self_sqrt hpos.le
  have hsp : (0:ℝ) < Real.sqrt (Fintype.card ι : ℝ) := Real.sqrt_pos.mpr hpos
  rw [orNDelta_sq]
  field_simp
  linarith [hs]

/-- The one-dimensional dual weights for `OR_n`. -/
noncomputable def orNDualVec (x : ι → Bool) (i : ι) : ℝ :=
  if x = zeroVec then orNDelta ι
  else if x i then 1 / ((supportCard x : ℝ) * orNDelta ι) else 0

/-- The dual solution for `OR_n`. -/
noncomputable def orNDual [Nonempty ι] : DualPair Unit (orN : (ι → Bool) → Bool) where
  u x i _ := orNDualVec x i
  v x i _ := orNDualVec x i
  constraint x y := by
    have hδ : orNDelta ι ≠ 0 := orNDelta_ne_zero
    by_cases hx : x = zeroVec <;> by_cases hy : y = zeroVec
    · subst hx; subst hy
      rw [if_pos rfl]
      exact Finset.sum_eq_zero fun i _ => if_pos rfl
    · -- `x = 0`, `y ≠ 0`: the sum is `|y| δ γ_y = 1`
      subst hx
      rw [if_neg (by rw [orN_zeroVec, orN_eq_true_iff.mpr hy]; exact Bool.noConfusion)]
      have hstep : ∀ i : ι,
          (if (zeroVec : ι → Bool) i = y i then (0:ℝ)
            else ∑ _k : Unit, orNDualVec zeroVec i * orNDualVec y i)
          = if y i = true then
              orNDelta ι * (1 / ((supportCard y : ℝ) * orNDelta ι)) else 0 := by
        intro i
        by_cases hyi : y i = true
        · rw [if_neg (by rw [zeroVec_apply, hyi]; exact Bool.noConfusion),
            if_pos hyi]
          simp [orNDualVec, hy, hyi]
        · simp only [Bool.not_eq_true] at hyi
          rw [if_pos (by rw [zeroVec_apply, hyi]), if_neg (by simp [hyi])]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i,
        sum_ite_const]
      have hcard : ((Finset.univ.filter fun i : ι => y i = true).card : ℝ)
          = (supportCard y : ℝ) := rfl
      rw [hcard]
      have hpos : (0:ℝ) < (supportCard y : ℝ) := by
        exact_mod_cast supportCard_pos hy
      field_simp
    · -- `x ≠ 0`, `y = 0`: symmetric
      subst hy
      rw [if_neg (by rw [orN_zeroVec, orN_eq_true_iff.mpr hx]; simp)]
      have hstep : ∀ i : ι,
          (if x i = (zeroVec : ι → Bool) i then (0:ℝ)
            else ∑ _k : Unit, orNDualVec x i * orNDualVec zeroVec i)
          = if x i = true then
              (1 / ((supportCard x : ℝ) * orNDelta ι)) * orNDelta ι else 0 := by
        intro i
        by_cases hxi : x i = true
        · rw [if_neg (by rw [zeroVec_apply, hxi]; exact Bool.noConfusion),
            if_pos hxi]
          simp [orNDualVec, hx, hxi]
        · simp only [Bool.not_eq_true] at hxi
          rw [if_pos (by rw [zeroVec_apply, hxi]), if_neg (by simp [hxi])]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i,
        sum_ite_const]
      have hcard : ((Finset.univ.filter fun i : ι => x i = true).card : ℝ)
          = (supportCard x : ℝ) := rfl
      rw [hcard]
      have hpos : (0:ℝ) < (supportCard x : ℝ) := by
        exact_mod_cast supportCard_pos hx
      field_simp
    · -- both nonzero: every differing coordinate kills one of the two factors
      rw [if_pos (by rw [orN_eq_true_iff.mpr hx, orN_eq_true_iff.mpr hy])]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : x i = y i
      · rw [if_pos hi]
      · rw [if_neg hi]
        have hzero : orNDualVec x i * orNDualVec y i = 0 := by
          rcases Bool.eq_false_or_eq_true (x i) with hxi | hxi
          · have hyi : y i = false := by
              rcases Bool.eq_false_or_eq_true (y i) with h | h
              · exact absurd (hxi.trans h.symm) hi
              · exact h
            have h0 : orNDualVec y i = 0 := by
              rw [orNDualVec, if_neg hy, if_neg (by simp [hyi] : ¬(y i = true))]
            rw [h0, mul_zero]
          · have h0 : orNDualVec x i = 0 := by
              rw [orNDualVec, if_neg hx, if_neg (by simp [hxi] : ¬(x i = true))]
            rw [h0, zero_mul]
        simpa using hzero

lemma orNDual_isCostLe [Nonempty ι] :
    (orNDual (ι := ι)).IsCostLe (Real.sqrt (Fintype.card ι : ℝ)) := by
  have hδ : orNDelta ι ≠ 0 := orNDelta_ne_zero
  have hn : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι : ℝ)
      = (Fintype.card ι : ℝ) := Real.mul_self_sqrt hn.le
  have key : ∀ x : ι → Bool,
      (∑ i : ι, ∑ _k : Unit, orNDualVec x i * orNDualVec x i)
        ≤ Real.sqrt (Fintype.card ι : ℝ) := by
    intro x
    by_cases hx : x = zeroVec
    · subst hx
      have : (∑ i : ι, ∑ _k : Unit,
          orNDualVec (zeroVec : ι → Bool) i * orNDualVec zeroVec i)
          = (Fintype.card ι : ℝ) * (orNDelta ι * orNDelta ι) := by
        simp [orNDualVec, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [this, card_mul_orNDelta_sq]
    · have hpos : (0:ℝ) < (supportCard x : ℝ) := by
        exact_mod_cast supportCard_pos hx
      have hstep : ∀ i : ι,
          (∑ _k : Unit, orNDualVec x i * orNDualVec x i)
          = if x i = true then
              (1 / ((supportCard x : ℝ) * orNDelta ι)) *
              (1 / ((supportCard x : ℝ) * orNDelta ι)) else 0 := by
        intro i
        by_cases hxi : x i = true
        · rw [if_pos hxi]
          simp [orNDualVec, hx, hxi]
        · simp only [Bool.not_eq_true] at hxi
          rw [if_neg (by simp [hxi])]
          simp [orNDualVec, hx, hxi]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i,
        sum_ite_const]
      have hcard : ((Finset.univ.filter fun i : ι => x i = true).card : ℝ)
          = (supportCard x : ℝ) := rfl
      rw [hcard]
      -- the value is `1 / (|x| δ²) ≤ 1 / δ² = √n`
      have hval : (supportCard x : ℝ) *
          ((1 / ((supportCard x : ℝ) * orNDelta ι)) *
            (1 / ((supportCard x : ℝ) * orNDelta ι)))
          = Real.sqrt (Fintype.card ι : ℝ) / (supportCard x : ℝ) := by
        rw [orNDelta] at *
        field_simp
        nlinarith [hs, Real.sq_sqrt (Real.sqrt_nonneg (Fintype.card ι : ℝ)),
          Real.sqrt_nonneg (Fintype.card ι : ℝ),
          Real.mul_self_sqrt (Real.sqrt_nonneg (Fintype.card ι : ℝ))]
      rw [hval]
      have hone : (1:ℝ) ≤ (supportCard x : ℝ) := by
        exact_mod_cast supportCard_pos hx
      rw [div_le_iff₀ hpos]
      nlinarith [Real.sqrt_nonneg (Fintype.card ι : ℝ), hone]
  exact ⟨key, key⟩

theorem advDual_orN_le [Nonempty ι] :
    advDual (orN : (ι → Bool) → Bool) ≤ Real.sqrt (Fintype.card ι : ℝ) :=
  advDual_le_of_dualPair orNDual (Real.sqrt_nonneg _) orNDual_isCostLe

/-- **`ADV±(OR_n) = √n`, with a matching dual certificate.** -/
theorem hasAdvValue_orN :
    HasAdvValue (orN : (ι → Bool) → Bool) (Real.sqrt (Fintype.card ι : ℝ)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hcard : Fintype.card ι = 0 := Fintype.card_eq_zero
    have hconst : ∀ x y : ι → Bool, orN x = orN y := by
      intro x y
      have hx : x = zeroVec := funext fun i => (hι.false i).elim
      have hy : y = zeroVec := funext fun i => (hι.false i).elim
      rw [hx, hy]
    refine ⟨?_, ?_⟩
    · rw [hcard]
      simpa using advPM_eq_zero_of_forall_eq hconst
    · refine le_antisymm ?_ ?_
      · refine advDual_le_of_dualPair
          (K := Unit) ⟨fun _ _ _ => 0, fun _ _ _ => 0, fun x y => ?_⟩
          (by rw [hcard]; simp) ⟨fun x => by rw [hcard]; simp, fun x => by
            rw [hcard]; simp⟩
        rw [if_pos (hconst x y)]
        exact Finset.sum_eq_zero fun i _ => by simp
      · rw [hcard]
        simpa using advDual_nonneg (orN : (ι → Bool) → Bool)
  · exact hasAdvValue_of_le sqrt_card_le_advPM_orN advDual_orN_le

/-! ## The `n`-bit AND function -/

lemma andN_eq : (andN : (ι → Bool) → Bool) = fun x => !(orN (flipAll x)) := by
  funext x
  show andN x = !(orN (flipAll x))
  rw [andN, orN]
  by_cases h : ∀ i, x i = true
  · have hne : ¬ ∃ i, (flipAll x : ι → Bool) i = true := by
      rintro ⟨i, hi⟩
      rw [flipAll_apply, h i] at hi
      exact Bool.noConfusion hi
    rw [decide_eq_true h, decide_eq_false hne, Bool.not_false]
  · have hex : ∃ i, (flipAll x : ι → Bool) i = true := by
      by_contra hc
      push_neg at hc
      refine h fun i => ?_
      have hi := hc i
      rw [flipAll_apply] at hi
      simpa using hi
    rw [decide_eq_false h, decide_eq_true hex, Bool.not_true]

/-- **`ADV±(AND_n) = √n`, with a matching dual certificate.** -/
theorem hasAdvValue_andN :
    HasAdvValue (andN : (ι → Bool) → Bool) (Real.sqrt (Fintype.card ι : ℝ)) := by
  rw [andN_eq]
  exact hasAdvValue_orN.compFlipAll.not

end QuantumQueryComplexity
