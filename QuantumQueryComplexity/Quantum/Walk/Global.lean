import QuantumQueryComplexity.Quantum.Walk.KronSupport
import QuantumQueryComplexity.Quantum.Amplitude.SearchInvUpTo
set_option synthInstance.maxSize 3200
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The global walk workspace and the search contract

`Lc` ancilla **blocks**, block `j` serving the reflection of level `j+1`:

    Blk j = control bit × parking register × clock (size `kk j·(T−1) + 1`) × neighbor register

on the workspace `(∀ j, Blk j) × V`.  `blkEquiv j` reads block `j` together with the shared
vertex register as the clocked system `ClockWork ι _ (V × Option V)` of `Level.lean`, the other
blocks riding along; `blockRefl j` is the level routine lifted along it.

`WalkGlobal x` collects the caller's data (the level data with the standard vertex encoding,
a preparation of the `√π` vertex state, an exact phase marker on the vertex register) and
`WalkGlobal.searchInv` proves **`SearchInvUpTo Lc`** for it: the flags are "all earlier blocks
blank", the supports are "query registers blank, every block control-clean, blocks `≥ l`
blank", and the precision of level `j+1` is `2^{-(j+9)}` from `kk j = j + 10`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ V : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype V] [DecidableEq V]

/-- The standard vertex encoding in the system `V × Option V`: query registers blank, neighbor
blank. -/
def vertE (u : V) : QBasis ι σ (V × Option V) := (none, none, (u, none))

/-- Query registers blank. -/
def QbSys : QBasis ι σ (V × Option V) → Bool := fun q => decide (q.1 = none ∧ q.2.1 = none)

/-- The `√π` vertex state. -/
def sqrtPiV (r : V → ℂ) : QBasis ι σ V → ℂ := fun p =>
  if p.1 = none ∧ p.2.1 = none then r p.2.2 else 0

section Blocks

variable (ι σ V) (Lc T : ℕ) (kk : Fin Lc → ℕ)

/-- Block `j`. -/
abbrev Blk (j : Fin Lc) : Type := Bool × Option ι × (Fin (kk j * (T - 1) + 1) × Option V)

/-- The global workspace. -/
abbrev Wg : Type := (∀ j, Blk ι V Lc T kk j) × V

/-- All blocks blank. -/
def blankAll : ∀ j, Blk ι V Lc T kk j := fun _ => (false, none, (0, none))

variable {ι σ V Lc T kk}

/-- Block `j` with the vertex register, as the clocked system of `Level.lean`. -/
def blkEquiv (j : Fin Lc) :
    QBasis ι σ (Wg ι V Lc T kk)
      ≃ QBasis ι σ (ClockWork ι (kk j * (T - 1) + 1) (V × Option V))
        × (∀ i : {i // i ≠ j}, Blk ι V Lc T kk i) where
  toFun p :=
    ((p.1, p.2.1, ((p.2.2.1 j).1, (p.2.2.1 j).2.1, ((p.2.2.1 j).2.2.1, (p.2.2.2, (p.2.2.1 j).2.2.2)))),
      fun i => p.2.2.1 i.1)
  invFun q :=
    (q.1.1, q.1.2.1, ((Equiv.piSplitAt j (Blk ι V Lc T kk)).symm
      ((q.1.2.2.1, q.1.2.2.2.1, (q.1.2.2.2.2.1, q.1.2.2.2.2.2.2)), q.2), q.1.2.2.2.2.2.1))
  left_inv p := by
    obtain ⟨k, t, f, u⟩ := p
    exact Prod.ext rfl (Prod.ext rfl (Prod.ext
      ((Equiv.piSplitAt j (Blk ι V Lc T kk)).symm_apply_apply f) rfl))
  right_inv q := by
    obtain ⟨⟨k, t, b, pk, c, u, nb⟩, g⟩ := q
    have H := (Equiv.piSplitAt j (Blk ι V Lc T kk)).apply_symm_apply ((b, pk, (c, nb)), g)
    have h1 : (Equiv.piSplitAt j (Blk ι V Lc T kk)).symm ((b, pk, (c, nb)), g) j
        = (b, pk, (c, nb)) := congrArg Prod.fst H
    have h2 : (fun i : {i // i ≠ j} =>
        (Equiv.piSplitAt j (Blk ι V Lc T kk)).symm ((b, pk, (c, nb)), g) i.1) = g :=
      congrArg Prod.snd H
    refine Prod.ext ?_ h2
    show (k, t, (((Equiv.piSplitAt j (Blk ι V Lc T kk)).symm ((b, pk, (c, nb)), g) j).1,
      ((Equiv.piSplitAt j (Blk ι V Lc T kk)).symm ((b, pk, (c, nb)), g) j).2.1,
      (((Equiv.piSplitAt j (Blk ι V Lc T kk)).symm ((b, pk, (c, nb)), g) j).2.2.1,
        (u, ((Equiv.piSplitAt j (Blk ι V Lc T kk)).symm ((b, pk, (c, nb)), g) j).2.2.2)))) = _
    rw [h1]

lemma blkEquiv_snd (j : Fin Lc) (p : QBasis ι σ (Wg ι V Lc T kk)) (i : {i // i ≠ j}) :
    (blkEquiv j p).2 i = p.2.2.1 i.1 := rfl

lemma blkEquiv_fst (j : Fin Lc) (p : QBasis ι σ (Wg ι V Lc T kk)) :
    (blkEquiv j p).1
      = (p.1, p.2.1, ((p.2.2.1 j).1, (p.2.2.1 j).2.1,
          ((p.2.2.1 j).2.2.1, (p.2.2.2, (p.2.2.1 j).2.2.2)))) := rfl

lemma oracleCompat_blkEquiv (j : Fin Lc) :
    OracleCompat (blkEquiv (ι := ι) (σ := σ) (V := V) (T := T) (kk := kk) j) := by
  rintro a ⟨(_ | i), t, f, u⟩ <;> rfl

/-- A block is blank. -/
def blkBlank {j : Fin Lc} (x : Blk ι V Lc T kk j) : Prop :=
  x.1 = false ∧ x.2.1 = none ∧ x.2.2.1 = 0 ∧ x.2.2.2 = none

/-- A block is control-clean. -/
def blkCtrl {j : Fin Lc} (x : Blk ι V Lc T kk j) : Prop := x.1 = false ∧ x.2.1 = none

instance {j : Fin Lc} (x : Blk ι V Lc T kk j) : Decidable (blkBlank x) := by
  unfold blkBlank; infer_instance

/-- The vertex readout. -/
def vtxG : QBasis ι σ (Wg ι V Lc T kk) → V := fun p => p.2.2.2

/-- The flag of level `j`: all blocks below `j` are blank. -/
def cleanG (j : ℕ) : QBasis ι σ (Wg ι V Lc T kk) → Bool := fun p =>
  decide (∀ i : Fin Lc, i.val < j → blkBlank (p.2.2.1 i))

/-- The support of level `l`: query registers blank, every block control-clean, blocks `≥ l`
blank. -/
def FG (l : ℕ) : Set (QBasis ι σ (Wg ι V Lc T kk)) :=
  {p | p.1 = none ∧ p.2.1 = none ∧ ∀ i : Fin Lc, blkCtrl (p.2.2.1 i)
    ∧ (l ≤ i.val → (p.2.2.1 i).2.2.1 = 0 ∧ (p.2.2.1 i).2.2.2 = none)}

/-- The global basis state of a vertex with everything blank. -/
def gPt (u : V) : QBasis ι σ (Wg ι V Lc T kk) := (none, none, (blankAll ι V Lc T kk, u))

/-- The clocked-system basis state of a vertex with everything blank. -/
def vtxPt (j : Fin Lc) (u : V) : QBasis ι σ (ClockWork ι (kk j * (T - 1) + 1) (V × Option V)) :=
  (none, none, (false, none, (0, (u, none))))

/-- The other blocks, blank. -/
def blankOthers (j : Fin Lc) : ∀ i : {i // i ≠ j}, Blk ι V Lc T kk i := fun _ => (false, none, (0, none))

lemma blkEquiv_symm_vtxPt (j : Fin Lc) (u : V) :
    (blkEquiv (ι := ι) (σ := σ) (V := V) (T := T) (kk := kk) j).symm (vtxPt j u, blankOthers j)
      = gPt u := by
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl))
  funext i
  by_cases hi : i = j
  · subst hi; simp [blkEquiv, Equiv.piSplitAt, blankAll, blankOthers, vtxPt, gPt]
  · simp [blkEquiv, Equiv.piSplitAt, hi, blankAll, blankOthers, vtxPt, gPt]

end Blocks

/-! ## Vectors on the vertex basis -/

section Vectors

variable {Lc T : ℕ} {kk : Fin Lc → ℕ}

lemma eq_sum_gPt {w : QBasis ι σ (Wg ι V Lc T kk) → ℂ}
    (hw : SuppIn {p | ∃ u, p = gPt u} w) : w = ∑ u, w (gPt u) • qBasis (gPt u) := by
  funext p
  rw [Finset.sum_apply]
  by_cases hp : ∃ u, p = gPt u
  · obtain ⟨u, rfl⟩ := hp
    rw [Finset.sum_eq_single u]
    · simp [qBasis]
    · intro v _ hv
      have : gPt (ι := ι) (σ := σ) (Lc := Lc) (T := T) (kk := kk) u ≠ gPt v := by
        intro h
        have h' : u = v := congrArg (fun q : QBasis ι σ (Wg ι V Lc T kk) => q.2.2.2) h
        exact hv h'.symm
      simp [qBasis, Pi.single_eq_of_ne this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have h0 : w p = 0 := by by_contra hne; exact hp (hw p hne)
    rw [h0]
    refine (Finset.sum_eq_zero fun u _ => ?_).symm
    have : p ≠ gPt u := fun h => hp ⟨u, h⟩
    simp [qBasis, Pi.single_eq_of_ne this]

lemma sqrtPiV_eq_sum (r : V → ℂ) :
    sqrtPiV (ι := ι) (σ := σ) r = ∑ u, r u • qBasis ((none, none, u) : QBasis ι σ V) := by
  funext p
  obtain ⟨k, t, u⟩ := p
  rw [Finset.sum_apply]
  by_cases hkt : k = none ∧ t = none
  · obtain ⟨rfl, rfl⟩ := hkt
    rw [Finset.sum_eq_single u]
    · simp [sqrtPiV, qBasis]
    · intro v _ hv
      have hne : ((none, none, u) : QBasis ι σ V) ≠ (none, none, v) := by
        intro h
        simp only [Prod.mk.injEq] at h
        exact hv h.2.2.symm
      simp [qBasis, Pi.single_eq_of_ne hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [sqrtPiV, if_neg hkt]
    refine (Finset.sum_eq_zero fun v _ => ?_).symm
    have hne : ((k, t, u) : QBasis ι σ V) ≠ (none, none, v) := by
      intro h; simp only [Prod.mk.injEq] at h; exact hkt ⟨h.1, h.2.1⟩
    simp [qBasis, Pi.single_eq_of_ne hne]

lemma embedReg_blankAll_qBasis (u : V) :
    embedReg (blankAll ι V Lc T kk) (qBasis ((none, none, u) : QBasis ι σ V)) = qBasis (gPt u) := by
  funext p
  obtain ⟨k, t, f, v⟩ := p
  rw [embedReg_apply]
  simp only [qBasis]
  by_cases hf : f = blankAll ι V Lc T kk
  · rw [if_pos hf]
    subst hf
    by_cases h : ((k, t, v) : QBasis ι σ V) = (none, none, u)
    · have h' : ((k, t, (blankAll ι V Lc T kk, v)) : QBasis ι σ (Wg ι V Lc T kk)) = gPt u := by
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rfl
      rw [h, h', Pi.single_eq_same, Pi.single_eq_same]
    · have h' : ((k, t, (blankAll ι V Lc T kk, v)) : QBasis ι σ (Wg ι V Lc T kk)) ≠ gPt u := by
        intro h'
        simp only [gPt, Prod.mk.injEq] at h'
        exact h (by obtain ⟨rfl, rfl, -, rfl⟩ := h'; rfl)
      rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
  · rw [if_neg hf]
    have h' : ((k, t, (f, v)) : QBasis ι σ (Wg ι V Lc T kk)) ≠ gPt u := by
      intro h'
      simp only [gPt, Prod.mk.injEq] at h'
      exact hf h'.2.2.1
    rw [Pi.single_eq_of_ne h']

lemma embedClock_vertE_qBasis (j : Fin Lc) (u : V) :
    embedClock (ι := ι) (σ := σ) (W := V × Option V) (T := kk j * (T - 1) + 1) 0 false
      (qBasis (vertE u)) = qBasis (vtxPt j u) := by
  funext p
  obtain ⟨k, t, b, pk, c, v, nb⟩ := p
  simp only [embedClock, embedCtrl_apply, embedReg_apply, qBasis, vertE, vtxPt]
  by_cases h : ((k, t, (b, (pk, (c, (v, nb))))) : QBasis ι σ (ClockWork ι (kk j * (T - 1) + 1) (V × Option V)))
      = (none, none, (false, none, (0, (u, none))))
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    simp
  · rw [Pi.single_eq_of_ne h]
    simp only [Prod.mk.injEq] at h
    split_ifs with h1 h2
    · rw [Pi.single_eq_of_ne]
      intro h3; simp only [Prod.mk.injEq] at h3
      exact h ⟨h3.1, h3.2.1, h1.1, h1.2, h2, h3.2.2.1, h3.2.2.2⟩
    · rfl
    · rfl

end Vectors

/-! ## The caller's data -/

/-- **The caller's data for the walk search.** -/
structure WalkGlobal (ι σ V : Type) [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    [Fintype V] [DecidableEq V] (x : ι → σ) where
  L : LevelData ι σ (V × Option V) V x
  he : L.e = vertE
  hQ : L.Qb = QbSys
  T : ℕ
  hT0 : 0 < T
  hT : 4 ≤ (T : ℝ) ^ 2 * L.δ
  markV : QRoutine ι σ V
  Marked : V → Prop
  [decM : DecidablePred Marked]
  mark_flip : ∀ φ, markV.run x *ᵥ φ = phaseFlip (fun p : QBasis ι σ V => p.2.2) Marked φ
  prepV : QRoutine ι σ V
  initV : QBasis ι σ V → ℂ
  hinit : IsQState initV
  prep_run : prepV.run x *ᵥ initV = sqrtPiV L.r

attribute [instance] WalkGlobal.decM

namespace WalkGlobal

variable {x : ι → σ} (G : WalkGlobal ι σ V x) (Lc : ℕ)

/-- The clock multiplicity of block `j`: level `j+1` has precision `2·2^{-(j+10)} = 2^{-(j+9)}`. -/
def kkG (Lc : ℕ) : Fin Lc → ℕ := fun j => j.val + 10

/-- The reflection of block `j`. -/
noncomputable def blockRefl (j : Fin Lc) : QRoutine ι σ (Wg ι V Lc G.T (kkG Lc)) :=
  (G.L.lvlR G.T (kkG Lc j) G.hT0).kronLift (blkEquiv j)

/-- The reflections, level `j+1` on block `j`. -/
noncomputable def reflG (n : ℕ) : QRoutine ι σ (Wg ι V Lc G.T (kkG Lc)) :=
  if h : 0 < n ∧ n - 1 < Lc then G.blockRefl Lc ⟨n - 1, h.2⟩ else QRoutine.identity

lemma reflG_succ {j : ℕ} (hj : j < Lc) : G.reflG Lc (j + 1) = G.blockRefl Lc ⟨j, hj⟩ := by
  rw [reflG, dif_pos ⟨Nat.succ_pos j, by simpa using hj⟩]
  exact congrArg (G.blockRefl Lc) (Fin.ext (Nat.add_sub_cancel j 1))

noncomputable def markG : QRoutine ι σ (Wg ι V Lc G.T (kkG Lc)) :=
  G.markV.liftReg (∀ j, Blk ι V Lc G.T (kkG Lc) j)

noncomputable def prepG : QRoutine ι σ (Wg ι V Lc G.T (kkG Lc)) :=
  G.prepV.liftReg (∀ j, Blk ι V Lc G.T (kkG Lc) j)

noncomputable def initG : QBasis ι σ (Wg ι V Lc G.T (kkG Lc)) → ℂ :=
  embedReg (blankAll ι V Lc G.T (kkG Lc)) G.initV

lemma initG_unit : IsQState (G.initG Lc) := by
  rw [IsQState, initG, qNormSq_embedReg]; exact G.hinit

/-- The prepared state. -/
theorem prepG_run : (G.prepG Lc).run x *ᵥ G.initG Lc
    = ∑ u, G.L.r u • qBasis (gPt (ι := ι) (σ := σ) (Lc := Lc) (T := G.T) (kk := kkG Lc) u) := by
  rw [prepG, initG, QRoutine.liftReg_run_embed, G.prep_run, sqrtPiV_eq_sum, embedReg_sum]
  exact Finset.sum_congr rfl fun u _ => by rw [embedReg_smul, embedReg_blankAll_qBasis]

end WalkGlobal

end QuantumQueryComplexity
