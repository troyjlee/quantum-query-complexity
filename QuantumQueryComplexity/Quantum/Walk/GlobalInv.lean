import QuantumQueryComplexity.Quantum.Walk.Global
set_option synthInstance.maxSize 3200
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The walk data satisfies the search contract

`WalkGlobal.searchInv G Lc : SearchInvUpTo vtxG Marked Lc markG reflG cleanG x s β FG` with
`β j = 2^{-(j+8)}`, `s` the `√π` vertex state with all blocks blank.  Each clause reduces to the
level results of `Level.lean` transported along `blkEquiv j` (`KronSupport.lean`), and to the
description of the vectors supported on "everything blank" as `|0⟩ ⊗ (vertex combination)`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ V : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype V] [DecidableEq V]

/-! ## Lifting a full phase marker -/

section PhaseLift

variable {W U O : Type} [Fintype W] [DecidableEq W] [Fintype U] [DecidableEq U]
  (rd : QBasis ι σ W → O) (Gd : O → Prop) [DecidablePred Gd]

lemma phaseFlip_apply' {H : Type} [Fintype H] [DecidableEq H] (rd' : H → O) (ψ : H → ℂ) (h : H) :
    phaseFlip rd' Gd ψ h = if Gd (rd' h) then -ψ h else ψ h := by
  rw [phaseFlip, Pi.sub_apply, badPart_apply, goodPart_apply]
  split_ifs <;> simp

lemma phaseFlip_sum {H α : Type} [Fintype H] [DecidableEq H] (rd' : H → O) (s : Finset α) (f : α → H → ℂ) :
    phaseFlip rd' Gd (∑ i ∈ s, f i) = ∑ i ∈ s, phaseFlip rd' Gd (f i) := by
  funext h
  rw [phaseFlip_apply', Finset.sum_apply, Finset.sum_apply]
  simp only [phaseFlip_apply']
  split_ifs <;> simp [Finset.sum_neg_distrib]

lemma phaseFlip_embedReg (u : U) (ψ : QBasis ι σ W → ℂ) :
    phaseFlip (fun p : QBasis ι σ (U × W) => rd (p.1, p.2.1, p.2.2.2)) Gd (embedReg u ψ)
      = embedReg u (phaseFlip rd Gd ψ) := by
  funext p
  rw [phaseFlip_apply', embedReg_apply, embedReg_apply, phaseFlip_apply']
  split_ifs <;> simp

/-- **A full phase marker lifts to a full phase marker.** -/
theorem liftReg_phaseFlip {M : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
    (hM : ∀ φ, M *ᵥ φ = phaseFlip rd Gd φ) (w : QBasis ι σ (U × W) → ℂ) :
    liftReg U M *ᵥ w = phaseFlip (fun p : QBasis ι σ (U × W) => rd (p.1, p.2.1, p.2.2.2)) Gd w := by
  rw [eq_sum_embedReg_sectorOf w, Matrix.mulVec_sum, phaseFlip_sum]
  exact Finset.sum_congr rfl fun u _ => by rw [liftReg_mulVec_embed, hM, phaseFlip_embedReg]

end PhaseLift

/-! ## Supports and the blank vectors -/

section Supp

variable {Lc T : ℕ} {kk : Fin Lc → ℕ}

lemma goodPart_eq_self_of_suppIn {H : Type} [Fintype H] [DecidableEq H] {c : H → Bool} {w : H → ℂ}
    (hw : SuppIn {p | c p = true} w) : goodPart c (· = true) w = w := by
  funext p
  rw [goodPart_apply]
  by_cases hc : c p = true
  · rw [if_pos hc]
  · rw [if_neg hc]
    by_contra hne
    exact hc (hw p (Ne.symm hne))

lemma suppIn_sum_gPt (c : V → ℂ) :
    SuppIn {p | ∃ u, p = gPt (ι := ι) (σ := σ) (Lc := Lc) (T := T) (kk := kk) u}
      (∑ u, c u • qBasis (gPt u)) := by
  intro p hp
  rw [Finset.sum_apply] at hp
  obtain ⟨u, _, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
  refine ⟨u, ?_⟩
  by_contra hne
  rw [Pi.smul_apply, qBasis, Pi.single_eq_of_ne hne, smul_zero] at hu
  exact hu rfl

lemma gPt_mem_FG (u : V) (l : ℕ) : gPt (ι := ι) (σ := σ) (Lc := Lc) (T := T) (kk := kk) u ∈ FG l :=
  ⟨rfl, rfl, fun _ => ⟨⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩⟩

lemma cleanG_gPt (u : V) (j : ℕ) :
    cleanG (ι := ι) (σ := σ) (V := V) (Lc := Lc) (T := T) (kk := kk) j (gPt u) = true := by
  rw [cleanG, decide_eq_true_eq]
  intro i _
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A vector supported on `FG j` and where `cleanG j` holds is supported on the blank vertex
states. -/
lemma suppIn_gPt_of {j : ℕ} {w : QBasis ι σ (Wg ι V Lc T kk) → ℂ} (hw : SuppIn (FG j) w)
    (hb : badPart (cleanG j) (· = true) w = 0) :
    SuppIn {p | ∃ u, p = gPt u} w := by
  intro p hp
  obtain ⟨hk, ht, hall⟩ := hw p hp
  have hc : cleanG (V := V) (T := T) (kk := kk) j p = true := by
    by_contra hc
    have := congrFun hb p
    rw [badPart_apply, if_neg hc, Pi.zero_apply] at this
    exact hp this
  rw [cleanG, decide_eq_true_eq] at hc
  refine ⟨p.2.2.2, ?_⟩
  obtain ⟨k, t, f, u⟩ := p
  simp only at hk ht
  subst hk ht
  change ((none, none, (f, u)) : QBasis ι σ (Wg ι V Lc T kk))
    = (none, none, (blankAll ι V Lc T kk, u))
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl))
  funext i
  by_cases hi : i.val < j
  · obtain ⟨h1, h2, h3, h4⟩ := hc i hi
    exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))
  · obtain ⟨⟨h1, h2⟩, h34⟩ := hall i
    obtain ⟨h3, h4⟩ := h34 (by omega)
    exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))

end Supp

/-! ## The instance -/

namespace WalkGlobal

variable {x : ι → σ} (G : WalkGlobal ι σ V x) (Lc : ℕ)

lemma blockRefl_run (j : Fin Lc) :
    (G.blockRefl Lc j).run x
      = kronLift (blkEquiv j) ((G.L.lvlR G.T (kkG Lc j) G.hT0).run x) :=
  QRoutine.kronLift_run (oracleCompat_blkEquiv j) _ x

lemma blockRefl_run_conjTranspose (j : Fin Lc) :
    ((G.blockRefl Lc j).run x)ᴴ = (G.blockRefl Lc j).run x := by
  rw [blockRefl_run, kronLift_conjTranspose, G.L.lvlR_run_conjTranspose]

lemma splitVec_sum' {β γ δ α : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    [Fintype δ] [DecidableEq δ] (e : β ≃ γ × δ) (s : Finset α) (f : α → γ → ℂ) (ξ : δ → ℂ) :
    splitVec e (∑ i ∈ s, f i) ξ = ∑ i ∈ s, splitVec e (f i) ξ := by
  funext p; simp [splitVec_apply, Finset.sum_apply, Finset.sum_mul]

/-- **`|0⟩ ⊗ (vertex combination)` on block `j`, everything else blank, is the blank vertex
combination.** -/
theorem splitVec_embedClock_vx (j : Fin Lc) (y : V → ℂ) :
    splitVec (blkEquiv j) (embedClock 0 false (G.L.vx y)) (qBasis (blankOthers j))
      = ∑ u, y u • qBasis (gPt (ι := ι) (σ := σ) (Lc := Lc) (T := G.T) (kk := kkG Lc) u) := by
  rw [LevelData.vx, lin, G.he, embedClock_sum, splitVec_sum']
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [embedClock_smul, splitVec_smul, embedClock_vertE_qBasis, splitVec_qBasis, blkEquiv_symm_vtxPt]


/-- The support of level `l`, seen through block `j < l`. -/
lemma FG_eq_lift {j : ℕ} (hj : j < Lc) {l : ℕ} (hjl : j + 1 ≤ l) :
    {p : QBasis ι σ (Wg ι V Lc G.T (kkG Lc)) | (blkEquiv ⟨j, hj⟩ p).1 ∈ Glvl G.L.Qb _
      ∧ ∀ i : {i : Fin Lc // i ≠ ⟨j, hj⟩}, blkCtrl ((blkEquiv ⟨j, hj⟩ p).2 i)
        ∧ (l ≤ i.1.val → ((blkEquiv ⟨j, hj⟩ p).2 i).2.2.1 = 0
          ∧ ((blkEquiv ⟨j, hj⟩ p).2 i).2.2.2 = none)}
    = FG l := by
  ext p
  obtain ⟨k, t, f, u⟩ := p
  simp only [Set.mem_setOf_eq, blkEquiv_fst, blkEquiv_snd, Glvl, G.hQ, QbSys, FG, blkCtrl,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hb, hpk, hk, ht⟩, hP⟩
    refine ⟨hk, ht, fun i => ?_⟩
    by_cases hi : i = ⟨j, hj⟩
    · subst hi
      exact ⟨⟨hb, hpk⟩, fun hli => absurd hli (by simp only [not_le]; omega)⟩
    · exact hP ⟨i, hi⟩
  · rintro ⟨hk, ht, hall⟩
    exact ⟨⟨(hall ⟨j, hj⟩).1.1, (hall ⟨j, hj⟩).1.2, hk, ht⟩, fun i => hall i.1⟩

/-- **The walk data satisfies the search contract up to level `Lc`.** -/
theorem searchInv :
    SearchInvUpTo (vtxG (ι := ι) (σ := σ) (V := V) (Lc := Lc) (T := G.T) (kk := kkG Lc)) G.Marked
      Lc (G.markG Lc) (G.reflG Lc) (cleanG (V := V) (Lc := Lc) (T := G.T) (kk := kkG Lc)) x
      ((G.prepG Lc).run x *ᵥ G.initG Lc) (fun j => (1 / 2) ^ (j + 8))
      (FG (V := V) (Lc := Lc) (T := G.T) (kk := kkG Lc)) where
  unit := IsQState.mulVec ((G.prepG Lc).run_mem_unitaryGroup x) (G.initG_unit Lc)
  mono := fun _ _ p hp =>
    ⟨hp.1, hp.2.1, fun i => ⟨(hp.2.2 i).1, fun h => (hp.2.2 i).2 (by omega)⟩⟩
  s_supp := by
    rw [G.prepG_run]
    exact (suppIn_sum_gPt _).mono (by rintro p ⟨u, rfl⟩; exact gPt_mem_FG u 0)
  s_clean := fun j _ => by
    rw [G.prepG_run]
    exact goodPart_eq_self_of_suppIn ((suppIn_sum_gPt _).mono
      (by rintro p ⟨u, rfl⟩; exact cleanG_gPt u j))
  mark_flip := fun _ _ w _ => by
    rw [markG, QRoutine.liftReg_run]
    exact liftReg_phaseFlip _ _ G.mark_flip w
  refl_comm := fun j hj => by
    rw [G.reflG_succ Lc hj, G.blockRefl_run]
    refine kronLift_comm_flagProj _ _
      (c' := fun g => decide (∀ i : {i : Fin Lc // i ≠ ⟨j, hj⟩}, i.1.val < j → blkBlank (g i)))
      fun p => ?_
    rw [cleanG]
    refine decide_eq_decide.mpr ⟨fun h i hi => h i.1 hi, fun h i hi => h ⟨i, ?_⟩ hi⟩
    intro h'
    rw [h'] at hi
    exact lt_irrefl _ hi
  refl_pres := fun j l hjl hl => by
    have hj : j < Lc := by omega
    rw [G.reflG_succ Lc hj, G.blockRefl_run]
    exact Preserves.congr_set (preserves_kronLift (blkEquiv ⟨j, hj⟩)
      (G.L.preserves_lvlR G.T _ G.hT0) fun g : ∀ i : {i : Fin Lc // i ≠ ⟨j, hj⟩},
        Blk ι V Lc G.T (kkG Lc) i => ∀ i, blkCtrl (g i)
          ∧ (l ≤ i.1.val → (g i).2.2.1 = 0 ∧ (g i).2.2.2 = none)) (G.FG_eq_lift Lc hj hjl)
  refl_pres_adj := fun j l hjl hl => by
    have hj : j < Lc := by omega
    rw [G.reflG_succ Lc hj, G.blockRefl_run_conjTranspose, G.blockRefl_run]
    exact Preserves.congr_set (preserves_kronLift (blkEquiv ⟨j, hj⟩)
      (G.L.preserves_lvlR G.T _ G.hT0) fun g : ∀ i : {i : Fin Lc // i ≠ ⟨j, hj⟩},
        Blk ι V Lc G.T (kkG Lc) i => ∀ i, blkCtrl (g i)
          ∧ (l ≤ i.1.val → (g i).2.2.1 = 0 ∧ (g i).2.2.2 = none)) (G.FG_eq_lift Lc hj hjl)
  β_nonneg := fun _ _ => by positivity
  β_le := fun _ _ => le_rfl
  refl_approx := fun j hj => by
    rw [G.reflG_succ Lc hj, G.blockRefl_run, G.prepG_run]
    have h0 := (G.L.isApproxRefl_lvlR G.T (kkG Lc ⟨j, hj⟩) G.hT0 G.hT).kronLift
      (blkEquiv ⟨j, hj⟩) (blankOthers ⟨j, hj⟩)
    rw [G.splitVec_embedClock_vx] at h0
    refine h0.mono ?_ (le_of_eq ?_)
    · rintro w ⟨hw, hb⟩
      refine ⟨embedClock 0 false (G.L.vx fun u => w (gPt u)), ⟨_, rfl⟩, ?_⟩
      rw [G.splitVec_embedClock_vx]
      exact eq_sum_gPt (suppIn_gPt_of hw hb)
    · show 2 * (1 / 2 : ℝ) ^ (j + 10) = (1 / 2) ^ (j + 1 + 8)
      ring

end WalkGlobal

end QuantumQueryComplexity
