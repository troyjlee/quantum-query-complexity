import QuantumQueryComplexity.ED.Defs
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The three-stage flow for element distinctness

Fix a collision pair `a ≠ b` of a positive input and let `m = n - 2`.  The
flow routes one unit from `∅` along a uniformly random `r`-arrangement of the
coordinates outside `{a, b}`, then loads `a`, then `b`:

* stage I: `S ⊆ D`, `|S| = t < r`, `j ∈ D \ S` carries `1/(C(m,t)·(m-t))`;
* stage II: `S ⊆ D`, `|S| = r`, `j = a` carries `1/C(m,r)`;
* stage III: `a ∈ S`, `b ∉ S`, `|S| = r+1`, `j = b` carries `1/C(m,r)`,

where `D = univ \ {a, b}`.  Conservation at a stage-I level is the binomial
identity `C(m,t)·t = C(m,t-1)·(m-t+1)` (`Nat.choose_succ_right_eq`); the two
stage transitions carry the single value `1/C(m,r)` through unchanged.  The
whole construction needs only `r ≤ m` (and works at `r = 0`).

The file ends by assembling an `LGFlow (edFun)` from any half-weight that is
nonzero on the loading edges of the first `r + 2` levels.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [DecidableEq σ]

/-! ## The stage values -/

/-- The stage-I flow value at level `t` (with `m` ambient coordinates). -/
noncomputable def edW (m t : ℕ) : ℝ :=
  ((m.choose t : ℝ) * ((m - t : ℕ) : ℝ))⁻¹

/-- The stage-II/III flow value. -/
noncomputable def edV (m r : ℕ) : ℝ := ((m.choose r : ℝ))⁻¹

/-- Inflow at a stage-I level: `t` incoming edges of value `edW m (t-1)`
total the outflow `1/C(m,t)`.  This is `Nat.choose_succ_right_eq`. -/
lemma edW_mul_identity {m t : ℕ} (ht : 0 < t) (htm : t ≤ m) :
    (t : ℝ) * edW m (t - 1) = ((m.choose t : ℝ))⁻¹ := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  rw [edW]
  simp only [Nat.add_sub_cancel]
  have hc1 : ((m.choose k : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  have hc2 : ((m.choose (k + 1) : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos htm).ne'
  have h3 : (((m - k : ℕ) : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have key : ((m.choose (k + 1) : ℝ)) * (((k + 1 : ℕ) : ℝ))
      = ((m.choose k : ℝ)) * (((m - k : ℕ) : ℝ)) := by
    exact_mod_cast Nat.choose_succ_right_eq m k
  field_simp
  push_cast at key ⊢
  linear_combination key

/-- Outflow at a stage-I level: `m - t` outgoing edges of value `edW m t`
total `1/C(m,t)`. -/
lemma edW_count_identity {m t : ℕ} (htm : t < m) :
    (((m - t : ℕ)) : ℝ) * edW m t = ((m.choose t : ℝ))⁻¹ := by
  rw [edW]
  have h1 : ((m.choose t : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos htm.le).ne'
  have h2 : (((m - t : ℕ) : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-! ## The flow -/

/-- The three-stage flow with collision pair `(a, b)`. -/
noncomputable def edFlow (r : ℕ) (a b : ι) (S : Finset ι) (j : ι) : ℝ :=
  if a ∉ S ∧ b ∉ S ∧ j ∉ S ∧ j ≠ a ∧ j ≠ b ∧ S.card < r
  then edW (Fintype.card ι - 2) S.card
  else if a ∉ S ∧ b ∉ S ∧ S.card = r ∧ j = a then edV (Fintype.card ι - 2) r
  else if a ∈ S ∧ b ∉ S ∧ S.card = r + 1 ∧ j = b then edV (Fintype.card ι - 2) r
  else 0

/-- A nonzero flow value sits on a loading edge of one of the `r + 2` first
levels. -/
lemma edFlow_ne_zero_imp {r : ℕ} {a b : ι} {S : Finset ι} {j : ι}
    (h : edFlow r a b S j ≠ 0) : j ∉ S ∧ S.card ≤ r + 1 := by
  rw [edFlow] at h
  by_cases h1 : a ∉ S ∧ b ∉ S ∧ j ∉ S ∧ j ≠ a ∧ j ≠ b ∧ S.card < r
  · exact ⟨h1.2.2.1, by omega⟩
  · rw [if_neg h1] at h
    by_cases h2 : a ∉ S ∧ b ∉ S ∧ S.card = r ∧ j = a
    · exact ⟨by rw [h2.2.2.2]; exact h2.1, by omega⟩
    · rw [if_neg h2] at h
      by_cases h3 : a ∈ S ∧ b ∉ S ∧ S.card = r + 1 ∧ j = b
      · exact ⟨by rw [h3.2.2.2]; exact h3.2.1, by omega⟩
      · rw [if_neg h3] at h
        exact absurd rfl h

/-! ## Outflow -/

/-- Summing a constant over the complement of `S` avoiding the pair. -/
private lemma sum_ite_pair_compl {S : Finset ι} {a b : ι} (hab : a ≠ b)
    (ha : a ∉ S) (hb : b ∉ S) (c : ℝ) :
    (∑ j ∈ Sᶜ, if j = a ∨ j = b then (0 : ℝ) else c)
      = ((Fintype.card ι - 2 - S.card : ℕ) : ℝ) * c := by
  have hsub : ({a, b} : Finset ι) ⊆ Sᶜ := by
    intro z hz
    rcases Finset.mem_insert.mp hz with h | h
    · rw [h]; exact Finset.mem_compl.mpr ha
    · rw [Finset.mem_singleton.mp h]; exact Finset.mem_compl.mpr hb
  have hcardeq : (Sᶜ \ ({a, b} : Finset ι)).card
      = Fintype.card ι - 2 - S.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_compl,
      Finset.card_pair hab]
    omega
  calc (∑ j ∈ Sᶜ, if j = a ∨ j = b then (0 : ℝ) else c)
      = ∑ j ∈ Sᶜ.filter (fun j => ¬ (j = a ∨ j = b)), c := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h : j = a ∨ j = b
        · rw [if_pos h, if_neg (not_not_intro h)]
        · rw [if_neg h, if_pos h]
    _ = ((Sᶜ \ ({a, b} : Finset ι)).card : ℝ) * c := by
        rw [show Sᶜ.filter (fun j => ¬ (j = a ∨ j = b))
              = Sᶜ \ ({a, b} : Finset ι) from by
            ext z
            simp [not_or],
          Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [hcardeq]

lemma sum_out_stageI {r : ℕ} {a b : ι} (hab : a ≠ b)
    (hr : r ≤ Fintype.card ι - 2) {S : Finset ι} (ha : a ∉ S) (hb : b ∉ S)
    (hcard : S.card < r) :
    (∑ j ∈ Sᶜ, edFlow r a b S j)
      = (((Fintype.card ι - 2).choose S.card : ℝ))⁻¹ := by
  have hstep : ∀ j ∈ Sᶜ, edFlow r a b S j
      = if j = a ∨ j = b then (0 : ℝ)
        else edW (Fintype.card ι - 2) S.card := by
    intro j hj
    have hjS : j ∉ S := Finset.mem_compl.mp hj
    by_cases hja : j = a
    · rw [if_pos (Or.inl hja)]
      subst hja
      rw [edFlow, if_neg fun h => h.2.2.2.1 rfl,
        if_neg fun h => absurd hcard (by rw [h.2.2.1]; exact lt_irrefl r),
        if_neg fun h => ha h.1]
    · by_cases hjb : j = b
      · rw [if_pos (Or.inr hjb)]
        subst hjb
        rw [edFlow, if_neg fun h => h.2.2.2.2.1 rfl,
          if_neg fun h => hab h.2.2.2.symm,
          if_neg fun h => ha h.1]
      · rw [if_neg (not_or.mpr ⟨hja, hjb⟩), edFlow,
          if_pos ⟨ha, hb, hjS, hja, hjb, hcard⟩]
  rw [Finset.sum_congr rfl hstep, sum_ite_pair_compl hab ha hb]
  exact edW_count_identity (lt_of_lt_of_le hcard hr)

lemma sum_out_stageII {r : ℕ} {a b : ι} (hab : a ≠ b) {S : Finset ι}
    (ha : a ∉ S) (hb : b ∉ S) (hcard : S.card = r) :
    (∑ j ∈ Sᶜ, edFlow r a b S j) = edV (Fintype.card ι - 2) r := by
  have hstep : ∀ j ∈ Sᶜ, edFlow r a b S j
      = if j = a then edV (Fintype.card ι - 2) r else 0 := by
    intro j hj
    by_cases hja : j = a
    · rw [if_pos hja]
      subst hja
      rw [edFlow, if_neg fun h => h.2.2.2.1 rfl, if_pos ⟨ha, hb, hcard, rfl⟩]
    · rw [if_neg hja, edFlow,
        if_neg fun h => absurd h.2.2.2.2.2 (by rw [hcard]; exact lt_irrefl r),
        if_neg fun h => hja h.2.2.2,
        if_neg fun h => ha h.1]
  rw [Finset.sum_congr rfl hstep,
    Finset.sum_ite_eq' Sᶜ a fun _ => edV (Fintype.card ι - 2) r,
    if_pos (Finset.mem_compl.mpr ha)]

lemma sum_out_stageIII {r : ℕ} {a b : ι} {S : Finset ι}
    (ha : a ∈ S) (hb : b ∉ S) (hcard : S.card = r + 1) :
    (∑ j ∈ Sᶜ, edFlow r a b S j) = edV (Fintype.card ι - 2) r := by
  have hstep : ∀ j ∈ Sᶜ, edFlow r a b S j
      = if j = b then edV (Fintype.card ι - 2) r else 0 := by
    intro j hj
    by_cases hjb : j = b
    · rw [if_pos hjb]
      subst hjb
      rw [edFlow, if_neg fun h => h.1 ha, if_neg fun h => h.1 ha,
        if_pos ⟨ha, hb, hcard, rfl⟩]
    · rw [if_neg hjb, edFlow, if_neg fun h => h.1 ha, if_neg fun h => h.1 ha,
        if_neg fun h => hjb h.2.2.2]
  rw [Finset.sum_congr rfl hstep,
    Finset.sum_ite_eq' Sᶜ b fun _ => edV (Fintype.card ι - 2) r,
    if_pos (Finset.mem_compl.mpr hb)]

lemma sum_out_zero_of_gt {r : ℕ} {a b : ι} {S : Finset ι}
    (ha : a ∉ S) (hb : b ∉ S) (hcard : r < S.card) :
    (∑ j ∈ Sᶜ, edFlow r a b S j) = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [edFlow, if_neg fun h => absurd h.2.2.2.2.2 (by omega),
    if_neg fun h => absurd h.2.2.1 (by omega),
    if_neg fun h => ha h.1]

lemma sum_out_zero_a_mem {r : ℕ} {a b : ι} {S : Finset ι}
    (ha : a ∈ S) (hcard : S.card ≠ r + 1) :
    (∑ j ∈ Sᶜ, edFlow r a b S j) = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [edFlow, if_neg fun h => h.1 ha, if_neg fun h => h.1 ha,
    if_neg fun h => hcard h.2.2.1]

lemma sum_out_zero_b_mem {r : ℕ} {a b : ι} {S : Finset ι} (hb : b ∈ S) :
    (∑ j ∈ Sᶜ, edFlow r a b S j) = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [edFlow, if_neg fun h => h.2.1 hb, if_neg fun h => h.2.1 hb,
    if_neg fun h => h.2.1 hb]

/-! ## Inflow -/

lemma sum_in_stageI {r : ℕ} {a b : ι} (hab : a ≠ b)
    (hr : r ≤ Fintype.card ι - 2) {S : Finset ι} (ha : a ∉ S) (hb : b ∉ S)
    (hne : S ≠ ∅) (hcard : S.card ≤ r) :
    (∑ j ∈ S, edFlow r a b (S.erase j) j)
      = (((Fintype.card ι - 2).choose S.card : ℝ))⁻¹ := by
  have hpos : 0 < S.card :=
    Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  have hstep : ∀ j ∈ S, edFlow r a b (S.erase j) j
      = edW (Fintype.card ι - 2) (S.card - 1) := by
    intro j hj
    have hja : j ≠ a := fun h => ha (h ▸ hj)
    have hjb : j ≠ b := fun h => hb (h ▸ hj)
    have hce : (S.erase j).card = S.card - 1 := Finset.card_erase_of_mem hj
    rw [edFlow, if_pos ⟨fun h => ha (Finset.mem_of_mem_erase h),
      fun h => hb (Finset.mem_of_mem_erase h), Finset.notMem_erase j S,
      hja, hjb, by rw [hce]; omega⟩, hce]
  rw [Finset.sum_congr rfl hstep, Finset.sum_const, nsmul_eq_mul]
  exact edW_mul_identity hpos (le_trans hcard hr)

lemma sum_in_stageIII {r : ℕ} {a b : ι} {S : Finset ι}
    (ha : a ∈ S) (hb : b ∉ S) (hcard : S.card = r + 1) :
    (∑ j ∈ S, edFlow r a b (S.erase j) j) = edV (Fintype.card ι - 2) r := by
  have hstep : ∀ j ∈ S, edFlow r a b (S.erase j) j
      = if j = a then edV (Fintype.card ι - 2) r else 0 := by
    intro j hj
    by_cases hja : j = a
    · rw [if_pos hja]
      subst hja
      rw [edFlow, if_neg fun h => h.2.2.2.1 rfl,
        if_pos ⟨Finset.notMem_erase j S,
          fun h => hb (Finset.mem_of_mem_erase h),
          by rw [Finset.card_erase_of_mem hj, hcard]; omega, rfl⟩]
    · have haej : a ∈ S.erase j := Finset.mem_erase.mpr ⟨fun h => hja h.symm, ha⟩
      have hjb : j ≠ b := fun h => hb (h ▸ hj)
      rw [if_neg hja, edFlow, if_neg fun h => h.1 haej,
        if_neg fun h => h.1 haej, if_neg fun h => hjb h.2.2.2]
  rw [Finset.sum_congr rfl hstep,
    Finset.sum_ite_eq' S a fun _ => edV (Fintype.card ι - 2) r, if_pos ha]

lemma sum_in_zero_of_gt {r : ℕ} {a b : ι} {S : Finset ι}
    (ha : a ∉ S) (hb : b ∉ S) (hcard : r < S.card) :
    (∑ j ∈ S, edFlow r a b (S.erase j) j) = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  have hja : j ≠ a := fun h => ha (h ▸ hj)
  have hce : (S.erase j).card = S.card - 1 := Finset.card_erase_of_mem hj
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨j, hj⟩
  rw [edFlow, if_neg fun h => absurd h.2.2.2.2.2 (by rw [hce]; omega),
    if_neg fun h => hja h.2.2.2,
    if_neg fun h => ha (Finset.mem_of_mem_erase h.1)]

lemma sum_in_zero_a_mem {r : ℕ} {a b : ι} {S : Finset ι}
    (ha : a ∈ S) (hb : b ∉ S) (hcard : S.card ≠ r + 1) :
    (∑ j ∈ S, edFlow r a b (S.erase j) j) = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨j, hj⟩
  by_cases hja : j = a
  · subst hja
    have hce : (S.erase j).card = S.card - 1 := Finset.card_erase_of_mem hj
    rw [edFlow, if_neg fun h => h.2.2.2.1 rfl,
      if_neg fun h => absurd h.2.2.1 (by rw [hce]; omega),
      if_neg fun h => (Finset.notMem_erase j S) h.1]
  · have haej : a ∈ S.erase j := Finset.mem_erase.mpr ⟨fun h => hja h.symm, ha⟩
    have hjb : j ≠ b := fun h => hb (h ▸ hj)
    rw [edFlow, if_neg fun h => h.1 haej, if_neg fun h => h.1 haej,
      if_neg fun h => hjb h.2.2.2]

lemma sum_in_zero_b_mem {r : ℕ} {a b : ι} (hab : a ≠ b) {S : Finset ι}
    (ha : a ∉ S) (hb : b ∈ S) :
    (∑ j ∈ S, edFlow r a b (S.erase j) j) = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  by_cases hjb : j = b
  · subst hjb
    rw [edFlow, if_neg fun h => h.2.2.2.2.1 rfl,
      if_neg fun h => hab h.2.2.2.symm,
      if_neg fun h => ha (Finset.mem_of_mem_erase h.1)]
  · have hbej : b ∈ S.erase j := Finset.mem_erase.mpr ⟨fun h => hjb h.symm, hb⟩
    rw [edFlow, if_neg fun h => h.2.1 hbej, if_neg fun h => h.2.1 hbej,
      if_neg fun h => h.2.1 hbej]

/-! ## Conservation and the source -/

theorem edFlow_conserve {r : ℕ} {a b : ι} (hab : a ≠ b)
    (hr : r ≤ Fintype.card ι - 2) {S : Finset ι} (hne : S ≠ ∅)
    (hnot : ¬ (a ∈ S ∧ b ∈ S)) :
    (∑ j ∈ Sᶜ, edFlow r a b S j) = ∑ j ∈ S, edFlow r a b (S.erase j) j := by
  by_cases ha : a ∈ S
  · have hb : b ∉ S := fun hb => hnot ⟨ha, hb⟩
    by_cases hcard : S.card = r + 1
    · rw [sum_out_stageIII ha hb hcard, sum_in_stageIII ha hb hcard]
    · rw [sum_out_zero_a_mem ha hcard, sum_in_zero_a_mem ha hb hcard]
  · by_cases hb : b ∈ S
    · rw [sum_out_zero_b_mem hb, sum_in_zero_b_mem hab ha hb]
    · rcases lt_trichotomy S.card r with h | h | h
      · rw [sum_out_stageI hab hr ha hb h,
          sum_in_stageI hab hr ha hb hne h.le]
      · rw [sum_out_stageII hab ha hb h, sum_in_stageI hab hr ha hb hne h.le,
          h, edV]
      · rw [sum_out_zero_of_gt ha hb h, sum_in_zero_of_gt ha hb h]

theorem edFlow_source {r : ℕ} {a b : ι} (hab : a ≠ b)
    (hr : r ≤ Fintype.card ι - 2) :
    (∑ j : ι, edFlow r a b ∅ j) = 1 := by
  have hempty : (∑ j ∈ (∅ : Finset ι)ᶜ, edFlow r a b ∅ j)
      = ∑ j : ι, edFlow r a b ∅ j := by rw [Finset.compl_empty]
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0
    rw [← hempty, sum_out_stageII hab (Finset.notMem_empty a)
      (Finset.notMem_empty b) Finset.card_empty, edV, Nat.choose_zero_right]
    norm_num
  · rw [← hempty, sum_out_stageI hab hr (Finset.notMem_empty a)
      (Finset.notMem_empty b) (by rw [Finset.card_empty]; exact hrpos),
      Finset.card_empty, Nat.choose_zero_right]
    norm_num

/-! ## The assembled learning-graph flow -/

/-- The learning-graph flow for element distinctness, for any half-weight
that is nonzero on the loading edges of the first `r + 2` levels.  The flow
of a positive input extracts its collision pair by choice; the sink predicate
is choice-free. -/
noncomputable def edLGFlow (r : ℕ) (hr : r ≤ Fintype.card ι - 2)
    (ω : Finset ι × ι → ℝ)
    (hω : ∀ e : Finset ι × ι, e.2 ∉ e.1 → e.1.card ≤ r + 1 → ω e ≠ 0) :
    LGFlow (edFun (ι := ι) (σ := σ)) where
  ω := ω
  p := fun x e =>
    if h : ∃ q : ι × ι, q.1 ≠ q.2 ∧ x q.1 = x q.2
    then edFlow r h.choose.1 h.choose.2 e.1 e.2 else 0
  sink := edSink
  supp := by
    intro x e hx hp
    rw [dif_pos (edFun_eq_true_iff.mp hx)] at hp
    obtain ⟨hj, hc⟩ := edFlow_ne_zero_imp hp
    exact hω e hj hc
  source := by
    intro x hx
    have hex := edFun_eq_true_iff.mp hx
    simp only [dif_pos hex]
    exact edFlow_source hex.choose_spec.1 hr
  conserve := by
    intro x hx S hne hsink
    have hex := edFun_eq_true_iff.mp hx
    simp only [dif_pos hex]
    refine edFlow_conserve hex.choose_spec.1 hr hne fun hmem => hsink ?_
    exact ⟨hex.choose.1, hmem.1, hex.choose.2, hmem.2,
      hex.choose_spec.1, hex.choose_spec.2⟩
  sinkCert := by
    intro x y hx hy S hsink
    exact edSink_cert hy hsink

end QuantumQueryComplexity
