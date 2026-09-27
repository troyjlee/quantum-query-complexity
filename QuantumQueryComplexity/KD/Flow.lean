import QuantumQueryComplexity.KD.Defs
import QuantumQueryComplexity.ED.Flow
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The (k+1)-stage flow for k-distinctness

Fix an injective constant-value tuple `a : Fin k → ι` of a positive input
and let `m = n - k`.  The flow routes one unit from `∅` along a uniformly
random `r`-arrangement of the coordinates outside `range a`, then loads
`a 0, a 1, ..., a (k-1)` in order:

* stage I: no `a i ∈ S`, `|S| = t < r`, `j ∉ S ∪ range a`
  carries `edW m t = 1/(C(m,t)·(m-t))`;
* stage `ℓ` (`0 ≤ ℓ < k`): `kdPrefix a ℓ S`, `|S| = r + ℓ`, `j = a ℓ`
  carries `edV m r = 1/C(m,r)`.

The prefix predicate `kdPrefix a ℓ S` ("exactly the first `ℓ` tuple entries
are loaded") replaces the two membership bits of the ED flow.  Conservation
at a stage-I level is the binomial identity of `edW_mul_identity`; each
stage transition carries the single value `1/C(m,r)` through unchanged.
Everything needs only `r ≤ m` (and `1 ≤ k` for the source).
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [DecidableEq σ]

/-! ## The prefix predicate -/

/-- Exactly the first `ℓ` entries of the tuple are loaded. -/
def kdPrefix {k : ℕ} (a : Fin k → ι) (ℓ : ℕ) (S : Finset ι) : Prop :=
  (∀ i : Fin k, (i : ℕ) < ℓ → a i ∈ S)
    ∧ (∀ i : Fin k, ℓ ≤ (i : ℕ) → a i ∉ S)

instance {k : ℕ} (a : Fin k → ι) (ℓ : ℕ) (S : Finset ι) :
    Decidable (kdPrefix a ℓ S) :=
  decidable_of_iff ((∀ i : Fin k, (i : ℕ) < ℓ → a i ∈ S)
    ∧ (∀ i : Fin k, ℓ ≤ (i : ℕ) → a i ∉ S)) Iff.rfl

/-- The prefix length is unique up to `k`. -/
lemma kdPrefix_eq {k : ℕ} {a : Fin k → ι} {S : Finset ι} {ℓ ℓ' : ℕ}
    (h : kdPrefix a ℓ S) (h' : kdPrefix a ℓ' S) (hℓ : ℓ ≤ k)
    (hℓ' : ℓ' ≤ k) : ℓ = ℓ' := by
  by_contra hne
  rcases Nat.lt_or_ge ℓ ℓ' with hlt | hge
  · exact (h.2 ⟨ℓ, by omega⟩ (le_refl ℓ)) (h'.1 ⟨ℓ, by omega⟩ hlt)
  · have hlt' : ℓ' < ℓ := by omega
    exact (h'.2 ⟨ℓ', by omega⟩ (le_refl ℓ')) (h.1 ⟨ℓ', by omega⟩ hlt')

/-- A positive prefix cannot coexist with an empty one. -/
lemma kdPrefix_zero_of_all_notMem {k : ℕ} {a : Fin k → ι} {S : Finset ι}
    (ha : ∀ i, a i ∉ S) : kdPrefix a 0 S :=
  ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun i _ => ha i⟩

/-! ## The flow -/

/-- The (k+1)-stage flow with collision tuple `a`. -/
noncomputable def kdFlow (k r : ℕ) (a : Fin k → ι) (S : Finset ι)
    (j : ι) : ℝ :=
  if (∀ i, a i ∉ S) ∧ j ∉ S ∧ (∀ i, j ≠ a i) ∧ S.card < r
  then edW (Fintype.card ι - k) S.card
  else if ∃ ℓ : Fin k, kdPrefix a (ℓ : ℕ) S ∧ S.card = r + (ℓ : ℕ)
      ∧ j = a ℓ
  then edV (Fintype.card ι - k) r
  else 0

/-- A nonzero flow value sits on a loading edge of one of the first
`r + k` levels. -/
lemma kdFlow_ne_zero_imp {k r : ℕ} {a : Fin k → ι} {S : Finset ι} {j : ι}
    (h : kdFlow k r a S j ≠ 0) : j ∉ S ∧ S.card ≤ r + k - 1 := by
  rw [kdFlow] at h
  by_cases h1 : (∀ i, a i ∉ S) ∧ j ∉ S ∧ (∀ i, j ≠ a i) ∧ S.card < r
  · refine ⟨h1.2.1, ?_⟩
    have hk : S.card < r := h1.2.2.2
    omega
  · rw [if_neg h1] at h
    by_cases h2 : ∃ ℓ : Fin k, kdPrefix a (ℓ : ℕ) S ∧ S.card = r + (ℓ : ℕ)
        ∧ j = a ℓ
    · obtain ⟨ℓ, hpre, hcard, hj⟩ := h2
      refine ⟨?_, ?_⟩
      · rw [hj]
        exact hpre.2 ℓ (le_refl _)
      · have hℓ : (ℓ : ℕ) < k := ℓ.isLt
        omega
    · rw [if_neg h2] at h
      exact absurd rfl h

/-! ## Outflow -/

/-- Summing a constant over the complement of `S` avoiding the tuple. -/
private lemma sum_ite_range_compl {k : ℕ} {S : Finset ι} {a : Fin k → ι}
    (hinj : Function.Injective a) (ha : ∀ i, a i ∉ S) (c : ℝ) :
    (∑ j ∈ Sᶜ, if ∃ i, j = a i then (0 : ℝ) else c)
      = ((Fintype.card ι - k - S.card : ℕ) : ℝ) * c := by
  have hsub : Finset.image a Finset.univ ⊆ Sᶜ := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_compl.mpr (ha i)
  have hcardim : (Finset.image a Finset.univ).card = k := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin]
  have hcardeq : (Sᶜ \ Finset.image a Finset.univ).card
      = Fintype.card ι - k - S.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
      Finset.card_compl, hcardim]
    omega
  calc (∑ j ∈ Sᶜ, if ∃ i, j = a i then (0 : ℝ) else c)
      = ∑ j ∈ Sᶜ.filter (fun j => ¬ ∃ i, j = a i), c := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h : ∃ i, j = a i
        · rw [if_pos h, if_neg (not_not_intro h)]
        · rw [if_neg h, if_pos h]
    _ = ((Sᶜ \ Finset.image a Finset.univ).card : ℝ) * c := by
        rw [show Sᶜ.filter (fun j => ¬ ∃ i, j = a i)
              = Sᶜ \ Finset.image a Finset.univ from by
            ext z
            simp [eq_comm],
          Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [hcardeq]

lemma kd_sum_out_stageI {k r : ℕ} {a : Fin k → ι}
    (hinj : Function.Injective a) (hr : r ≤ Fintype.card ι - k)
    {S : Finset ι} (ha : ∀ i, a i ∉ S) (hcard : S.card < r) :
    (∑ j ∈ Sᶜ, kdFlow k r a S j)
      = (((Fintype.card ι - k).choose S.card : ℝ))⁻¹ := by
  have hstep : ∀ j ∈ Sᶜ, kdFlow k r a S j
      = if ∃ i, j = a i then (0 : ℝ)
        else edW (Fintype.card ι - k) S.card := by
    intro j hj
    have hjS : j ∉ S := Finset.mem_compl.mp hj
    by_cases hja : ∃ i, j = a i
    · rw [if_pos hja]
      obtain ⟨i, rfl⟩ := hja
      rw [kdFlow, if_neg fun h => h.2.2.1 i rfl,
        if_neg fun ⟨ℓ, _, hc, _⟩ => by omega]
    · rw [if_neg hja, kdFlow,
        if_pos ⟨ha, hjS, fun i h => hja ⟨i, h⟩, hcard⟩]
  rw [Finset.sum_congr rfl hstep, sum_ite_range_compl hinj ha]
  exact edW_count_identity (lt_of_lt_of_le hcard hr)

lemma kd_sum_out_stage {k r : ℕ} {a : Fin k → ι} {S : Finset ι}
    {ℓ : Fin k} (hpre : kdPrefix a (ℓ : ℕ) S)
    (hcard : S.card = r + (ℓ : ℕ)) :
    (∑ j ∈ Sᶜ, kdFlow k r a S j) = edV (Fintype.card ι - k) r := by
  have hstep : ∀ j ∈ Sᶜ, kdFlow k r a S j
      = if j = a ℓ then edV (Fintype.card ι - k) r else 0 := by
    intro j _
    by_cases hja : j = a ℓ
    · rw [if_pos hja, kdFlow, if_neg fun h => by omega,
        if_pos ⟨ℓ, hpre, hcard, hja⟩]
    · rw [if_neg hja, kdFlow, if_neg fun h => by omega,
        if_neg fun ⟨ℓ', hpre', hc', hj'⟩ => hja (by
          have hv : (ℓ' : ℕ) = (ℓ : ℕ) := by omega
          rw [hj']
          exact congrArg a (Fin.ext hv))]
  rw [Finset.sum_congr rfl hstep,
    Finset.sum_ite_eq' Sᶜ (a ℓ) fun _ => edV (Fintype.card ι - k) r,
    if_pos (Finset.mem_compl.mpr (hpre.2 ℓ (le_refl _)))]

lemma kd_sum_out_zero {k r : ℕ} {a : Fin k → ι} {S : Finset ι}
    (h1 : ¬((∀ i, a i ∉ S) ∧ S.card < r))
    (h2 : ∀ ℓ : Fin k, ¬(kdPrefix a (ℓ : ℕ) S
      ∧ S.card = r + (ℓ : ℕ))) :
    (∑ j ∈ Sᶜ, kdFlow k r a S j) = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [kdFlow, if_neg fun h => h1 ⟨h.1, h.2.2.2⟩,
    if_neg fun ⟨ℓ, hpre, hc, _⟩ => h2 ℓ ⟨hpre, hc⟩]

/-! ## Inflow -/

lemma kd_sum_in_stageI {k r : ℕ} {a : Fin k → ι}
    (hr : r ≤ Fintype.card ι - k) {S : Finset ι} (ha : ∀ i, a i ∉ S)
    (hne : S ≠ ∅) (hcard : S.card ≤ r) :
    (∑ j ∈ S, kdFlow k r a (S.erase j) j)
      = (((Fintype.card ι - k).choose S.card : ℝ))⁻¹ := by
  have hpos : 0 < S.card :=
    Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  have hstep : ∀ j ∈ S, kdFlow k r a (S.erase j) j
      = edW (Fintype.card ι - k) (S.card - 1) := by
    intro j hj
    have hja : ∀ i, j ≠ a i := fun i h => ha i (h ▸ hj)
    have hce : (S.erase j).card = S.card - 1 :=
      Finset.card_erase_of_mem hj
    rw [kdFlow, if_pos ⟨fun i h => ha i (Finset.mem_of_mem_erase h),
      Finset.notMem_erase j S, hja, by rw [hce]; omega⟩, hce]
  rw [Finset.sum_congr rfl hstep, Finset.sum_const, nsmul_eq_mul]
  exact edW_mul_identity hpos (le_trans hcard hr)

/-- The possible sources of an in-edge: a stage-I edge (nothing loaded,
small set) or the stage-`ℓ` edge that has just loaded `a ℓ`. -/
lemma kdFlow_erase_cases {k r : ℕ} {a : Fin k → ι}
    (hinj : Function.Injective a) {S : Finset ι} {j : ι} (hj : j ∈ S)
    (h : kdFlow k r a (S.erase j) j ≠ 0) :
    ((∀ i, a i ∉ S) ∧ S.card ≤ r)
      ∨ ∃ ℓ : Fin k, j = a ℓ ∧ kdPrefix a ((ℓ : ℕ) + 1) S
          ∧ S.card = r + (ℓ : ℕ) + 1 := by
  rw [kdFlow] at h
  have hce : (S.erase j).card = S.card - 1 := Finset.card_erase_of_mem hj
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨j, hj⟩
  by_cases h1 : (∀ i, a i ∉ S.erase j) ∧ j ∉ S.erase j
      ∧ (∀ i, j ≠ a i) ∧ (S.erase j).card < r
  · left
    refine ⟨fun i hmem => ?_, by omega⟩
    exact h1.1 i (Finset.mem_erase.mpr
      ⟨fun hc => h1.2.2.1 i hc.symm, hmem⟩)
  · rw [if_neg h1] at h
    by_cases h2 : ∃ ℓ : Fin k, kdPrefix a (ℓ : ℕ) (S.erase j)
        ∧ (S.erase j).card = r + (ℓ : ℕ) ∧ j = a ℓ
    · right
      obtain ⟨ℓ, hpre, hcard, hjeq⟩ := h2
      refine ⟨ℓ, hjeq, ⟨?_, ?_⟩, by omega⟩
      · intro i hi
        rcases Nat.lt_or_ge (i : ℕ) (ℓ : ℕ) with hlt | hge
        · exact Finset.mem_of_mem_erase (hpre.1 i hlt)
        · have hie : i = ℓ := Fin.ext (by omega)
          rw [hie, ← hjeq]
          exact hj
      · intro i hi hmem
        have hne' : a i ≠ j := fun hc => by
          rw [hjeq] at hc
          have hv : (i : ℕ) = (ℓ : ℕ) := by rw [hinj hc]
          omega
        exact (hpre.2 i (by omega))
          (Finset.mem_erase.mpr ⟨hne', hmem⟩)
    · rw [if_neg h2] at h
      exact absurd rfl h

lemma kd_sum_in_zero {k r : ℕ} {a : Fin k → ι}
    (hinj : Function.Injective a) {S : Finset ι}
    (h1 : ¬((∀ i, a i ∉ S) ∧ S.card ≤ r))
    (h2 : ∀ ℓ : Fin k, ¬(kdPrefix a ((ℓ : ℕ) + 1) S
      ∧ S.card = r + (ℓ : ℕ) + 1)) :
    (∑ j ∈ S, kdFlow k r a (S.erase j) j) = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  by_contra hne
  rcases kdFlow_erase_cases hinj hj hne with hA | ⟨ℓ, _, hpre, hcard⟩
  · exact h1 hA
  · exact h2 ℓ ⟨hpre, hcard⟩

lemma kd_sum_in_stage {k r : ℕ} {a : Fin k → ι}
    (hinj : Function.Injective a) {S : Finset ι} {ℓ : ℕ}
    (hℓ1 : 1 ≤ ℓ) (hℓk : ℓ ≤ k) (hpre : kdPrefix a ℓ S)
    (hcard : S.card = r + ℓ) :
    (∑ j ∈ S, kdFlow k r a (S.erase j) j)
      = edV (Fintype.card ι - k) r := by
  have hlt : ℓ - 1 < k := by omega
  have hmem : a ⟨ℓ - 1, hlt⟩ ∈ S := hpre.1 ⟨ℓ - 1, hlt⟩ (by
    show ℓ - 1 < ℓ
    omega)
  have hstep : ∀ j ∈ S, kdFlow k r a (S.erase j) j
      = if j = a ⟨ℓ - 1, hlt⟩ then edV (Fintype.card ι - k) r
        else 0 := by
    intro j hj
    by_cases hja : j = a ⟨ℓ - 1, hlt⟩
    · rw [if_pos hja]
      subst hja
      have hce : (S.erase (a ⟨ℓ - 1, hlt⟩)).card = S.card - 1 :=
        Finset.card_erase_of_mem hj
      have hwit : ∃ ℓ'' : Fin k, kdPrefix a (ℓ'' : ℕ)
          (S.erase (a ⟨ℓ - 1, hlt⟩))
          ∧ (S.erase (a ⟨ℓ - 1, hlt⟩)).card = r + (ℓ'' : ℕ)
          ∧ a ⟨ℓ - 1, hlt⟩ = a ℓ'' := by
        refine ⟨⟨ℓ - 1, hlt⟩, ⟨?_, ?_⟩, ?_, rfl⟩
        · intro i hi
          refine Finset.mem_erase.mpr ⟨fun hc => ?_, hpre.1 i (by
            show (i : ℕ) < ℓ
            have hi' : (i : ℕ) < ℓ - 1 := hi
            omega)⟩
          have hv : (i : ℕ) = ℓ - 1 := by rw [hinj hc]
          have hi' : (i : ℕ) < ℓ - 1 := hi
          omega
        · intro i hi hmem'
          obtain ⟨hne', hmemS⟩ := Finset.mem_erase.mp hmem'
          rcases Nat.lt_or_ge (i : ℕ) ℓ with hilt | hige
          · have hi' : ℓ - 1 ≤ (i : ℕ) := hi
            have hv : (i : ℕ) = ℓ - 1 := by omega
            exact hne' (congrArg a (Fin.ext hv))
          · exact (hpre.2 i hige) hmemS
        · show (S.erase (a ⟨ℓ - 1, hlt⟩)).card = r + (ℓ - 1)
          rw [hce]
          omega
      rw [kdFlow, if_neg fun h => h.2.2.1 ⟨ℓ - 1, hlt⟩ rfl,
        if_pos hwit]
    · rw [if_neg hja, kdFlow]
      have hmem' : a ⟨ℓ - 1, hlt⟩ ∈ S.erase j :=
        Finset.mem_erase.mpr ⟨fun h => hja h.symm, hmem⟩
      have hce : (S.erase j).card = S.card - 1 :=
        Finset.card_erase_of_mem hj
      have hno : ¬ ∃ ℓ'' : Fin k, kdPrefix a (ℓ'' : ℕ) (S.erase j)
          ∧ (S.erase j).card = r + (ℓ'' : ℕ) ∧ j = a ℓ'' := by
        rintro ⟨ℓ'', hpre'', hc'', hj''⟩
        have hv : (ℓ'' : ℕ) = ℓ - 1 := by omega
        exact hja (by
          rw [hj'']
          exact congrArg a (Fin.ext hv))
      rw [if_neg fun h => h.1 ⟨ℓ - 1, hlt⟩ hmem', if_neg hno]
  rw [Finset.sum_congr rfl hstep,
    Finset.sum_ite_eq' S (a ⟨ℓ - 1, hlt⟩)
      fun _ => edV (Fintype.card ι - k) r, if_pos hmem]

/-! ## Conservation and the source -/

theorem kdFlow_conserve {k r : ℕ} {a : Fin k → ι}
    (hinj : Function.Injective a) (hr : r ≤ Fintype.card ι - k)
    {S : Finset ι} (hne : S ≠ ∅) (hnot : ¬ ∀ i, a i ∈ S) :
    (∑ j ∈ Sᶜ, kdFlow k r a S j)
      = ∑ j ∈ S, kdFlow k r a (S.erase j) j := by
  by_cases hex : ∃ ℓ : ℕ, ℓ ≤ k ∧ kdPrefix a ℓ S
  · obtain ⟨ℓ, hℓk, hp⟩ := hex
    have hℓk' : ℓ < k := by
      rcases Nat.lt_or_ge ℓ k with h | h
      · exact h
      · exact absurd (fun i => hp.1 i (by omega)) hnot
    rcases Nat.eq_zero_or_pos ℓ with h0 | hℓpos
    · subst h0
      have ha : ∀ i, a i ∉ S := fun i => hp.2 i (Nat.zero_le _)
      rcases lt_trichotomy S.card r with h | h | h
      · rw [kd_sum_out_stageI hinj hr ha h,
          kd_sum_in_stageI hr ha hne h.le]
      · rw [kd_sum_out_stage (ℓ := ⟨0, hℓk'⟩) hp (by
            show S.card = r + 0
            omega),
          kd_sum_in_stageI hr ha hne h.le, h, edV]
      · rw [kd_sum_out_zero (fun hh => by omega)
            (fun ℓ' hh => by
              have := kdPrefix_eq hp hh.1 (Nat.zero_le k) ℓ'.isLt.le
              omega),
          kd_sum_in_zero hinj (fun hh => by omega)
            (fun ℓ' hh => by
              have := kdPrefix_eq hp hh.1 (Nat.zero_le k)
                (by omega : (ℓ' : ℕ) + 1 ≤ k)
              omega)]
    · by_cases hc : S.card = r + ℓ
      · rw [kd_sum_out_stage (ℓ := ⟨ℓ, hℓk'⟩) hp (by
            show S.card = r + ℓ
            exact hc),
          kd_sum_in_stage hinj hℓpos hℓk'.le hp hc]
      · have hmem0 : a ⟨0, by omega⟩ ∈ S := hp.1 ⟨0, by omega⟩ (by
          show 0 < ℓ
          omega)
        rw [kd_sum_out_zero (fun hh => hh.1 ⟨0, by omega⟩ hmem0)
            (fun ℓ' hh => by
              have := kdPrefix_eq hp hh.1 hℓk'.le ℓ'.isLt.le
              omega),
          kd_sum_in_zero hinj (fun hh => hh.1 ⟨0, by omega⟩ hmem0)
            (fun ℓ' hh => by
              have := kdPrefix_eq hp hh.1 hℓk'.le
                (by omega : (ℓ' : ℕ) + 1 ≤ k)
              omega)]
  · rw [kd_sum_out_zero
        (fun hh => hex ⟨0, Nat.zero_le k,
          kdPrefix_zero_of_all_notMem hh.1⟩)
        (fun ℓ' hh => hex ⟨(ℓ' : ℕ), ℓ'.isLt.le, hh.1⟩),
      kd_sum_in_zero hinj
        (fun hh => hex ⟨0, Nat.zero_le k,
          kdPrefix_zero_of_all_notMem hh.1⟩)
        (fun ℓ' hh => hex ⟨(ℓ' : ℕ) + 1, by omega, hh.1⟩)]

theorem kdFlow_source {k r : ℕ} {a : Fin k → ι} (hk : 1 ≤ k)
    (hinj : Function.Injective a) (hr : r ≤ Fintype.card ι - k) :
    (∑ j : ι, kdFlow k r a ∅ j) = 1 := by
  have hempty : (∑ j ∈ (∅ : Finset ι)ᶜ, kdFlow k r a ∅ j)
      = ∑ j : ι, kdFlow k r a ∅ j := by rw [Finset.compl_empty]
  have ha : ∀ i, a i ∉ (∅ : Finset ι) := fun i => Finset.notMem_empty _
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0
    rw [← hempty, kd_sum_out_stage (ℓ := ⟨0, hk⟩)
      (kdPrefix_zero_of_all_notMem ha) (by
        show (∅ : Finset ι).card = 0 + 0
        rw [Finset.card_empty]),
      edV, Nat.choose_zero_right]
    norm_num
  · rw [← hempty, kd_sum_out_stageI hinj hr ha
      (by rw [Finset.card_empty]; exact hrpos), Finset.card_empty,
      Nat.choose_zero_right]
    norm_num

/-! ## The assembled learning-graph flow -/

/-- The learning-graph flow for k-distinctness, for any half-weight that
is nonzero on the loading edges of the first `r + k` levels.  The flow of
a positive input extracts its collision tuple by choice; the sink
predicate is choice-free. -/
noncomputable def kdLGFlow (k r : ℕ) (hk : 1 ≤ k)
    (hr : r ≤ Fintype.card ι - k) (ω : Finset ι × ι → ℝ)
    (hω : ∀ e : Finset ι × ι, e.2 ∉ e.1 → e.1.card ≤ r + k - 1 →
      ω e ≠ 0) :
    LGFlow (kdFun (ι := ι) (σ := σ) k) where
  ω := ω
  p := fun x e =>
    if h : ∃ a : Fin k → ι, Function.Injective a ∧
        ∀ i j : Fin k, x (a i) = x (a j)
    then kdFlow k r h.choose e.1 e.2 else 0
  sink := kdSink k
  supp := by
    intro x e hx hp
    rw [dif_pos (kdFun_eq_true_iff.mp hx)] at hp
    obtain ⟨hj, hc⟩ := kdFlow_ne_zero_imp hp
    exact hω e hj hc
  source := by
    intro x hx
    have hex := kdFun_eq_true_iff.mp hx
    simp only [dif_pos hex]
    exact kdFlow_source hk hex.choose_spec.1 hr
  conserve := by
    intro x hx S hne hsink
    have hex := kdFun_eq_true_iff.mp hx
    simp only [dif_pos hex]
    refine kdFlow_conserve hex.choose_spec.1 hr hne fun hall => hsink ?_
    exact ⟨hex.choose, hex.choose_spec.1, hall, hex.choose_spec.2⟩
  sinkCert := by
    intro x y hx hy S hsink
    exact kdSink_cert hy hsink

end QuantumQueryComplexity
