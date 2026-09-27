import QuantumQueryComplexity.Quantum.Walk.Detect
import QuantumQueryComplexity.Quantum.History
import QuantumQueryComplexity.Quantum.Amplitude.NoisyRefl
set_option synthInstance.maxSize 1600
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# One level of the walk reflection, as a routine

`LevelData x` bundles what a level needs on the input `x`: a two-reflection walk realized by a
routine `walkR` (`4U` queries), a row update `upd` (`U` queries) carrying the vertex basis
states `e u` to the row states `a u`, the row states supported on query-blank basis states,
and `upd` commuting with the query-blank flag.

`lvlR L T k` is the level routine on `ClockWork ι (k(T−1)+1) W`:

    upd ; prepare the clock in the `k`-clock state ; detector ; unprepare ; upd⁻¹

* `lvlR_len = 2·U + 2·k(T−1)·walkR.len`;
* `lvlR_run` — its operator, Hermitian and unitary;
* `isApproxRefl_lvlR` — a **`2^{1−k}`-approximate reflection about `|0⟩ ⊗ (√π vertex state)`**
  on the vectors `|0⟩ ⊗ (vertex combination)`, when `4 ≤ T²δ`;
* `preserves_lvlR` — it preserves the support `{query blank, control false, parking blank}`
  (clock and system otherwise arbitrary).

Support lemmas for lifted operators (`preserves_liftReg'`, `preserves_regOp`, the
`clockPack` decomposition of a control-clean vector) are here as well.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-! ## Supports under lifted operators -/

section Lifts

variable {U : Type} [Fintype U] [DecidableEq U]

lemma sectorOf_suppIn {G : Set (QBasis ι σ W)} {P : U → Prop}
    {ψ : QBasis ι σ (U × W) → ℂ} (hψ : SuppIn {p | (p.1, p.2.1, p.2.2.2) ∈ G ∧ P p.2.2.1} ψ)
    (u : U) : SuppIn G (sectorOf u ψ) := fun q hq => (hψ _ hq).1

lemma sectorOf_eq_zero {G : Set (QBasis ι σ W)} {P : U → Prop}
    {ψ : QBasis ι σ (U × W) → ℂ} (hψ : SuppIn {p | (p.1, p.2.1, p.2.2.2) ∈ G ∧ P p.2.2.1} ψ)
    {u : U} (hu : ¬ P u) : sectorOf u ψ = 0 := by
  funext q
  by_contra hne
  exact hu (hψ _ hne).2

/-- **A lifted operator preserves a support of the form "system in `G`, register in `P`".** -/
theorem preserves_liftReg' {M : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ} {G : Set (QBasis ι σ W)}
    (hM : Preserves M G) (P : U → Prop) :
    Preserves (liftReg U M) {p : QBasis ι σ (U × W) | (p.1, p.2.1, p.2.2.2) ∈ G ∧ P p.2.2.1} := by
  intro ψ hψ p hp
  rw [eq_sum_embedReg_sectorOf ψ, Matrix.mulVec_sum, Finset.sum_apply] at hp
  obtain ⟨u, _, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
  rw [liftReg_mulVec_embed, embedReg_apply] at hu
  split_ifs at hu with hpu
  · refine ⟨hM _ (sectorOf_suppIn hψ u) _ hu, ?_⟩
    rw [hpu]
    by_contra hP
    rw [sectorOf_eq_zero hψ hP, Matrix.mulVec_zero] at hu
    exact hu rfl
  · exact absurd rfl hu

/-- **An operator on the register alone preserves every support defined on the system.** -/
theorem preserves_regOp (A : Matrix U U ℂ) (G : Set (QBasis ι σ W)) :
    Preserves (regOp A) {p : QBasis ι σ (U × W) | (p.1, p.2.1, p.2.2.2) ∈ G} := by
  intro ψ hψ p hp
  rw [eq_sum_embedReg_sectorOf ψ, Matrix.mulVec_sum, Finset.sum_apply] at hp
  obtain ⟨u, _, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
  rw [regOp_mulVec_embedReg, Finset.sum_apply] at hu
  obtain ⟨u', _, hu'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
  rw [Pi.smul_apply, embedReg_apply] at hu'
  split_ifs at hu' with hpu
  · have : sectorOf u ψ (p.1, p.2.1, p.2.2.2) ≠ 0 := fun h0 => hu' (by rw [h0, smul_zero])
    exact hψ (p.1, p.2.1, (u, p.2.2.2)) this
  · exact absurd (by simp) hu'

end Lifts

/-! ## Control-clean vectors are packed histories -/

section Pack

variable {T : ℕ}

/-- The clock-`c` sector of a control-clean vector. -/
def clockSector (c : Fin T) (ψ : QBasis ι σ (ClockWork ι T W) → ℂ) : QBasis ι σ W → ℂ :=
  fun q => ψ (q.1, q.2.1, (false, none, (c, q.2.2)))

/-- Control false and parking blank. -/
def CtrlClean (ι σ W : Type) (T : ℕ) : Set (QBasis ι σ (ClockWork ι T W)) :=
  {p | p.2.2.1 = false ∧ p.2.2.2.1 = none}

theorem eq_clockPack_of_ctrlClean {ψ : QBasis ι σ (ClockWork ι T W) → ℂ}
    (hψ : SuppIn (CtrlClean ι σ W T) ψ) : ψ = clockPack fun c => clockSector c ψ := by
  funext p
  obtain ⟨k, t, b, pk, c, w⟩ := p
  rw [clockPack, Finset.sum_apply]
  by_cases hb : b = false ∧ pk = none
  · obtain ⟨rfl, rfl⟩ := hb
    rw [Finset.sum_eq_single c]
    · simp [embedClock, embedCtrl_apply, embedReg_apply, clockSector]
    · intro c' _ hc'
      simp [embedClock, embedCtrl_apply, embedReg_apply, Ne.symm hc']
    · intro h; exact absurd (Finset.mem_univ _) h
  · have h0 : ψ (k, t, b, pk, c, w) = 0 := by
      by_contra hne
      exact hb (hψ _ hne)
    rw [h0]
    refine (Finset.sum_eq_zero fun c' _ => ?_).symm
    simp only [embedClock, embedCtrl_apply]
    exact if_neg hb

/-- The system parts of a packed history are supported where the whole is. -/
lemma suppIn_clockPack {G : Set (QBasis ι σ W)} {f : Fin T → (QBasis ι σ W → ℂ)}
    (hf : ∀ c, SuppIn G (f c)) :
    SuppIn {p : QBasis ι σ (ClockWork ι T W) | p ∈ CtrlClean ι σ W T
      ∧ (p.1, p.2.1, p.2.2.2.2.2) ∈ G} (clockPack f) := by
  intro p hp
  obtain ⟨k, t, b, pk, c, w⟩ := p
  rw [clockPack, Finset.sum_apply] at hp
  obtain ⟨c', _, hc'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
  simp only [embedClock, embedCtrl_apply, embedReg_apply] at hc'
  by_cases h1 : b = false ∧ pk = none
  · rw [if_pos h1] at hc'
    by_cases h2 : c = c'
    · rw [if_pos h2] at hc'
      subst h2
      exact ⟨⟨h1.1, h1.2⟩, hf c _ hc'⟩
    · rw [if_neg h2] at hc'; exact absurd rfl hc'
  · rw [if_neg h1] at hc'; exact absurd rfl hc'

lemma clockSector_suppIn {G : Set (QBasis ι σ W)} {ψ : QBasis ι σ (ClockWork ι T W) → ℂ}
    (hψ : SuppIn {p : QBasis ι σ (ClockWork ι T W) | p ∈ CtrlClean ι σ W T
      ∧ (p.1, p.2.1, p.2.2.2.2.2) ∈ G} ψ) (c : Fin T) : SuppIn G (clockSector c ψ) :=
  fun q hq => (hψ _ hq).2

/-- **`SELECT` preserves the control-clean, system-in-`G` support** when `R.run` does. -/
theorem preserves_selectPowers {R : QRoutine ι σ W} {x : ι → σ} {G : Set (QBasis ι σ W)}
    (hR : Preserves (R.run x) G) (T : ℕ) :
    Preserves ((selectPowers R T).run x) {p : QBasis ι σ (ClockWork ι T W) |
      p ∈ CtrlClean ι σ W T ∧ (p.1, p.2.1, p.2.2.2.2.2) ∈ G} := by
  intro ψ hψ
  rw [eq_clockPack_of_ctrlClean (fun p hp => (hψ p hp).1), selectPowers_run_clockPack]
  refine suppIn_clockPack fun c => ?_
  have hpow : ∀ n, Preserves ((R.run x) ^ n) G := fun n => by
    induction n with
    | zero => rw [pow_zero]; exact preserves_one G
    | succ n ih => rw [pow_succ]; exact ih.mul hR
  exact hpow _ _ (clockSector_suppIn hψ c)

theorem preserves_selectPowers_adj {R : QRoutine ι σ W} {x : ι → σ} {G : Set (QBasis ι σ W)}
    (hR : Preserves ((R.run x)ᴴ) G) (T : ℕ) :
    Preserves (((selectPowers R T).run x)ᴴ) {p : QBasis ι σ (ClockWork ι T W) |
      p ∈ CtrlClean ι σ W T ∧ (p.1, p.2.1, p.2.2.2.2.2) ∈ G} := by
  intro ψ hψ
  rw [eq_clockPack_of_ctrlClean (fun p hp => (hψ p hp).1),
    selectPowers_conjTranspose_mulVec_clockPack]
  refine suppIn_clockPack fun c => ?_
  have hpow : ∀ n, Preserves (((R.run x) ^ n)ᴴ) G := fun n => by
    induction n with
    | zero => rw [pow_zero, Matrix.conjTranspose_one]; exact preserves_one G
    | succ n ih => rw [pow_succ, Matrix.conjTranspose_mul]; exact hR.mul ih
  exact hpow _ _ (clockSector_suppIn hψ c)

end Pack

/-! ## The level data -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- What one level needs, on the input `x`. -/
structure LevelData (ι σ W V : Type) [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] (x : ι → σ) where
  a : V → (QBasis ι σ W → ℂ)
  b : V → (QBasis ι σ W → ℂ)
  D : Matrix V V ℂ
  r : V → ℂ
  δ : ℝ
  fam : WalkFam a b D r δ
  walkR : QRoutine ι σ W
  walk_run : walkR.run x = WalkFam.walkOp a b
  upd : QRoutine ι σ W
  /-- The vertex basis states. -/
  e : V → QBasis ι σ W
  e_inj : Function.Injective e
  upd_e : ∀ u, upd.run x *ᵥ qBasis (e u) = a u
  /-- The query-blank flag. -/
  Qb : QBasis ι σ W → Bool
  Qb_e : ∀ u, Qb (e u) = true
  a_supp : ∀ u, SuppIn {q | Qb q = true} (a u)
  b_supp : ∀ u, SuppIn {q | Qb q = true} (b u)
  upd_comm : upd.run x * flagProj Qb = flagProj Qb * upd.run x

namespace LevelData

variable {x : ι → σ} (L : LevelData ι σ W V x)

/-- The vertex-state combination. -/
noncomputable def vx (L : LevelData ι σ W V x) (y : V → ℂ) : QBasis ι σ W → ℂ :=
  lin (fun u => qBasis (L.e u)) y

lemma qInner_qBasis_e (u v : V) :
    qInner (qBasis (L.e u)) (qBasis (L.e v)) = if u = v then 1 else 0 := by
  rw [qInner_def]
  by_cases huv : u = v
  · subst huv; rw [if_pos rfl, Finset.sum_eq_single (L.e u)]
    · simp [qBasis]
    · intro q _ hq; simp [qBasis, Pi.single_eq_of_ne hq]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg huv]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases h1 : q = L.e u
    · subst h1
      have : L.e u ≠ L.e v := fun h => huv (L.e_inj h)
      simp [qBasis, Pi.single_eq_of_ne this]
    · simp [qBasis, Pi.single_eq_of_ne h1]

lemma upd_vx (y : V → ℂ) : L.upd.run x *ᵥ L.vx y = lin L.a y := by
  rw [vx, lin, lin, Matrix.mulVec_sum]
  exact Finset.sum_congr rfl fun u _ => by rw [Matrix.mulVec_smul, L.upd_e]

lemma preserves_upd : Preserves (L.upd.run x) {q | L.Qb q = true} := fun w hw => by
  have hw' : goodPart L.Qb (· = true) w = w := by
    funext q; rw [goodPart_apply]
    by_cases hq : L.Qb q = true
    · rw [if_pos hq]
    · rw [if_neg hq]
      by_contra hne; exact hq (hw q (Ne.symm hne))
  have : L.upd.run x *ᵥ w = goodPart L.Qb (· = true) (L.upd.run x *ᵥ w) := by
    rw [← flagProj_mulVec, Matrix.mulVec_mulVec, ← L.upd_comm, ← Matrix.mulVec_mulVec,
      flagProj_mulVec, hw']
  rw [this]
  exact fun q hq => by
    by_contra hQ; exact hq (by rw [goodPart_apply, if_neg (show ¬ L.Qb q = true from hQ)])

lemma preserves_upd_adj : Preserves ((L.upd.run x)ᴴ) {q | L.Qb q = true} := fun w hw => by
  have hcomm : (L.upd.run x)ᴴ * flagProj L.Qb = flagProj L.Qb * (L.upd.run x)ᴴ := by
    have := congrArg Matrix.conjTranspose L.upd_comm
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, flagProj_conjTranspose] at this
    exact this.symm
  have hw' : goodPart L.Qb (· = true) w = w := by
    funext q; rw [goodPart_apply]
    by_cases hq : L.Qb q = true
    · rw [if_pos hq]
    · rw [if_neg hq]
      by_contra hne; exact hq (hw q (Ne.symm hne))
  have : (L.upd.run x)ᴴ *ᵥ w = goodPart L.Qb (· = true) ((L.upd.run x)ᴴ *ᵥ w) := by
    rw [← flagProj_mulVec, Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec,
      flagProj_mulVec, hw']
  rw [this]
  exact fun q hq => by
    by_contra hQ; exact hq (by rw [goodPart_apply, if_neg (show ¬ L.Qb q = true from hQ)])

lemma preserves_projA {f : V → (QBasis ι σ W → ℂ)} (hf : ∀ u, SuppIn {q | L.Qb q = true} (f u)) :
    Preserves (WalkFam.projA f) {q | L.Qb q = true} := fun w _ => by
  rw [WalkFam.projA_mulVec, lin]
  intro q hq
  rw [Finset.sum_apply] at hq
  obtain ⟨u, _, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
  rw [Pi.smul_apply] at hu
  exact hf u q fun h0 => hu (by rw [h0, smul_zero])

lemma _root_.QuantumQueryComplexity.SuppIn.smul {H : Type} [Fintype H] {F : Set H} {w : H → ℂ}
    (h : SuppIn F w) (c : ℂ) : SuppIn F (c • w) :=
  fun y hy => h y fun h0 => hy (by rw [Pi.smul_apply, h0, smul_zero])

lemma preserves_qRefl {P : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ} {G : Set (QBasis ι σ W)}
    (hP : Preserves P G) : Preserves (qRefl P) G := fun w hw => by
  rw [WalkFam.qRefl_mulVec']
  exact ((hP w hw).smul 2).sub hw

lemma preserves_walk : Preserves (WalkFam.walkOp L.a L.b) {q | L.Qb q = true} :=
  (preserves_qRefl (L.preserves_projA L.b_supp)).mul (preserves_qRefl (L.preserves_projA L.a_supp))

lemma walkOp_conjTranspose : (WalkFam.walkOp L.a L.b)ᴴ
    = qRefl (WalkFam.projA L.a) * qRefl (WalkFam.projA L.b) := by
  rw [WalkFam.walkOp, Matrix.conjTranspose_mul,
    qRefl_conjTranspose (WalkFam.isQProjector_projA L.fam.orthA),
    qRefl_conjTranspose (WalkFam.isQProjector_projA L.fam.orthB)]

lemma preserves_walk_adj : Preserves ((WalkFam.walkOp L.a L.b)ᴴ) {q | L.Qb q = true} := by
  rw [L.walkOp_conjTranspose]
  exact (preserves_qRefl (L.preserves_projA L.a_supp)).mul
    (preserves_qRefl (L.preserves_projA L.b_supp))

end LevelData

/-! ## The level routine -/

section Routine

variable {T : ℕ}

/-- A system routine, lifted past the control bit, parking register and clock. -/
def liftClk (T : ℕ) (R : QRoutine ι σ W) : QRoutine ι σ (ClockWork ι T W) :=
  ((R.liftReg (Fin T)).liftReg (Option ι)).liftReg Bool

@[simp] lemma liftClk_len (T : ℕ) (R : QRoutine ι σ W) : (liftClk T R).len = R.len := rfl

lemma liftClk_run (T : ℕ) (R : QRoutine ι σ W) :
    (liftClk T R).run x = liftReg Bool (liftReg (Option ι) (liftReg (Fin T) (R.run x))) := by
  rw [liftClk, QRoutine.liftReg_run, QRoutine.liftReg_run, QRoutine.liftReg_run]

lemma liftClk_run_embedClock (T : ℕ) (R : QRoutine ι σ W) (c : Fin T) (b : Bool)
    (ψ : QBasis ι σ W → ℂ) :
    (liftClk T R).run x *ᵥ embedClock c b ψ = embedClock c b (R.run x *ᵥ ψ) := by
  rw [liftClk_run, embedClock, embedCtrl, liftReg_mulVec_embed, liftReg_mulVec_embed,
    liftReg_mulVec_embed]
  rfl

lemma liftClk_run_conjTranspose (T : ℕ) (R : QRoutine ι σ W) :
    ((liftClk T R).run x)ᴴ = liftReg Bool (liftReg (Option ι) (liftReg (Fin T) (R.run x)ᴴ)) := by
  rw [liftClk_run, liftReg_conjTranspose, liftReg_conjTranspose, liftReg_conjTranspose]

/-- Control false, parking blank, system query-blank. -/
def Glvl (Qb : QBasis ι σ W → Bool) (T : ℕ) : Set (QBasis ι σ (ClockWork ι T W)) :=
  {p | p.2.2.1 = false ∧ p.2.2.2.1 = none ∧ Qb (p.1, p.2.1, p.2.2.2.2.2) = true}

lemma Glvl_eq_nested (Qb : QBasis ι σ W → Bool) (T : ℕ) :
    Glvl Qb T = {p : QBasis ι σ (Bool × (Option ι × (Fin T × W))) |
      (p.1, p.2.1, p.2.2.2) ∈ {q : QBasis ι σ (Option ι × (Fin T × W)) |
        (q.1, q.2.1, q.2.2.2) ∈ {q' : QBasis ι σ (Fin T × W) |
          (q'.1, q'.2.1, q'.2.2.2) ∈ {w | Qb w = true} ∧ True} ∧ q.2.2.1 = none}
      ∧ p.2.2.1 = false} := by
  ext ⟨k, t, b, pk, c, w⟩
  simp [Glvl]
  tauto

lemma Glvl_eq_ctrlClean (Qb : QBasis ι σ W → Bool) (T : ℕ) :
    Glvl Qb T = {p | p ∈ CtrlClean ι σ W T ∧ (p.1, p.2.1, p.2.2.2.2.2) ∈ {w | Qb w = true}} := by
  ext ⟨k, t, b, pk, c, w⟩
  simp [Glvl, CtrlClean]
  tauto

lemma Preserves.congr_set {H : Type} [Fintype H] [DecidableEq H] {M : Matrix H H ℂ}
    {G G' : Set H} (h : Preserves M G) (hG : G = G') : Preserves M G' := hG ▸ h

theorem preserves_liftClk_of {M : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
    {Qb : QBasis ι σ W → Bool} (hM : Preserves M {w | Qb w = true}) (T : ℕ) :
    Preserves (liftReg Bool (liftReg (Option ι) (liftReg (Fin T) M))) (Glvl Qb T) :=
  Preserves.congr_set (preserves_liftReg' (preserves_liftReg' (preserves_liftReg' hM
    fun _ => True) (· = none)) (· = false)) (Glvl_eq_nested Qb T).symm

theorem preserves_clockReg (A : Matrix (Fin T) (Fin T) ℂ) (Qb : QBasis ι σ W → Bool) :
    Preserves (liftReg Bool (liftReg (Option ι) (regOp A))) (Glvl Qb T) :=
  Preserves.congr_set (preserves_liftReg' (preserves_liftReg' (preserves_regOp A
    {w | Qb w = true}) (· = none)) (· = false)) (by
      rw [Glvl_eq_nested]
      ext ⟨k, t, b, pk, c, w⟩
      simp)

lemma qInner_qBasis_left {H : Type} [Fintype H] [DecidableEq H] (i : H) (φ : H → ℂ) :
    qInner (qBasis i) φ = φ i := by
  rw [qInner_def, Finset.sum_eq_single i]
  · simp [qBasis]
  · intro j _ hj; simp [qBasis, Pi.single_eq_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ _) h

end Routine

namespace LevelData

variable {x : ι → σ} (L : LevelData ι σ W V x) (T k : ℕ)

/-- The nonnegative overlap of the `k`-clock state with `|0⟩`. -/
noncomputable def t0 (T k : ℕ) : ℝ := Real.sqrt (((avgPoly T) ^ k).coeff 0)

lemma t0_nonneg : 0 ≤ t0 T k := Real.sqrt_nonneg _

lemma qInner_zero_kClock : qInner (qBasis 0) (kClock T k) = ((t0 T k : ℝ) : ℂ) := by
  rw [qInner_qBasis_left]; rfl

/-- The clock preparation of the level. -/
noncomputable def prepR (hT0 : 0 < T) : QRoutine ι σ (ClockWork ι (k * (T - 1) + 1) W) :=
  QRoutine.ofUnitary (clockPrep (kClock T k) (t0 T k))
    (clockPrep_mem_unitaryGroup (isQState_kClock hT0 k) (t0_nonneg T k) (qInner_zero_kClock T k))

noncomputable def prepRH (hT0 : 0 < T) : QRoutine ι σ (ClockWork ι (k * (T - 1) + 1) W) :=
  QRoutine.ofUnitary (clockPrep (kClock T k) (t0 T k))ᴴ
    (conjTranspose_mem_qUnitary (clockPrep_mem_unitaryGroup (isQState_kClock hT0 k)
      (t0_nonneg T k) (qInner_zero_kClock T k)))

/-- **The level routine**, from the update and walk routines alone (no proofs, so that the
compiled algorithm is visibly input-independent). -/
noncomputable def _root_.QuantumQueryComplexity.lvlRoutine (upd walkR : QRoutine ι σ W)
    (T k : ℕ) (hT0 : 0 < T) : QRoutine ι σ (ClockWork ι (k * (T - 1) + 1) W) :=
  (liftClk _ upd).comp ((prepR (ι := ι) (σ := σ) (W := W) T k hT0).comp
    ((wDetector walkR _ (isQState_kClock hT0 k)).comp
      ((prepRH (ι := ι) (σ := σ) (W := W) T k hT0).comp (liftClk _ upd).inv)))

/-- The level routine of the level data. -/
noncomputable abbrev lvlR (hT0 : 0 < T) : QRoutine ι σ (ClockWork ι (k * (T - 1) + 1) W) :=
  lvlRoutine L.upd L.walkR T k hT0

theorem lvlR_len (hT0 : 0 < T) :
    (L.lvlR T k hT0).len = 2 * L.upd.len + 2 * (k * (T - 1) * L.walkR.len) := by
  simp only [lvlR, lvlRoutine, QRoutine.comp_len, liftClk_len, prepR, prepRH, QRoutine.ofUnitary_len,
    wDetector_len, QRoutine.inv_len, Nat.add_sub_cancel]
  ring

local notation "Pm" => clockPrep (ι := ι) (σ := σ) (W := W) (kClock T k) (t0 T k)
local notation "Um" =>
  liftReg Bool (liftReg (Option ι) (liftReg (Fin (k * (T - 1) + 1)) (L.upd.run x)))

theorem lvlR_run (hT0 : 0 < T) :
    (L.lvlR T k hT0).run x
      = (Um)ᴴ * ((Pm)ᴴ * ((wDetector L.walkR _ (isQState_kClock hT0 k)).run x * (Pm * Um))) := by
  simp only [lvlR, lvlRoutine, QRoutine.comp_run, prepR, prepRH, QRoutine.ofUnitary_run,
    QRoutine.inv_run,
    liftClk_run, liftClk_run_conjTranspose, Matrix.mul_assoc]

lemma wDetector_run_conjTranspose {α : Fin (k * (T - 1) + 1) → ℂ} (hα : IsQState α) :
    ((wDetector L.walkR _ hα).run x)ᴴ = (wDetector L.walkR _ hα).run x := by
  rw [wDetector_run, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, clockStateRefl,
    qRefl_conjTranspose (isQProjector_clockStateProj hα), Matrix.mul_assoc]

theorem lvlR_run_conjTranspose (hT0 : 0 < T) :
    ((L.lvlR T k hT0).run x)ᴴ = (L.lvlR T k hT0).run x := by
  rw [lvlR_run]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    L.wDetector_run_conjTranspose, Matrix.mul_assoc]

/-- **The level routine is a `2^{1−k}`-approximate reflection about `|0⟩ ⊗ vx r`, on the
vectors `|0⟩ ⊗ (vertex combination)`.** -/
theorem isApproxRefl_lvlR (hT0 : 0 < T) (hT : 4 ≤ (T : ℝ) ^ 2 * L.δ) :
    IsApproxRefl ((L.lvlR T k hT0).run x) (embedClock 0 false (L.vx L.r))
      {χ | ∃ y : V → ℂ, χ = embedClock 0 false (L.vx y)} (2 * (1 / 2) ^ k) := by
  have hα := isQState_kClock hT0 k
  have hPu : Pm ∈ Matrix.unitaryGroup _ ℂ :=
    clockPrep_mem_unitaryGroup hα (t0_nonneg T k) (qInner_zero_kClock T k)
  have hUu : Um ∈ Matrix.unitaryGroup _ ℂ := by
    rw [← liftClk_run]; exact (liftClk _ L.upd).run_mem_unitaryGroup x
  have hPP : ∀ ψ, (Pm)ᴴ *ᵥ (Pm *ᵥ ψ) = ψ := fun ψ => by
    rw [Matrix.mulVec_mulVec, conjTranspose_mul_self_of_unitary hPu, Matrix.one_mulVec]
  have hUU : ∀ ψ, (Um)ᴴ *ᵥ (Um *ᵥ ψ) = ψ := fun ψ => by
    rw [Matrix.mulVec_mulVec, conjTranspose_mul_self_of_unitary hUu, Matrix.one_mulVec]
  have hP0 : ∀ ψ, Pm *ᵥ embedClock 0 false ψ = wClock (kClock T k) ψ := fun ψ =>
    clockPrep_mulVec_embedClock_zero (t0_nonneg T k) (qInner_zero_kClock T k) ψ
  have hU0 : ∀ ψ, Um *ᵥ embedClock (0 : Fin (k * (T - 1) + 1)) false ψ
      = embedClock 0 false (L.upd.run x *ᵥ ψ) := fun ψ => by
    rw [← liftClk_run]; exact liftClk_run_embedClock _ _ _ _ _
  have h1 := (L.fam.isApproxRefl_wDetector L.walk_run hT0 hT k).conj
    (conjTranspose_mem_qUnitary hPu)
  have h2 := h1.conj (conjTranspose_mem_qUnitary hUu)
  rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose] at h2
  have hassoc : (Um)ᴴ * ((Pm)ᴴ * (wDetector L.walkR _ hα).run x * Pm) * Um
      = (Um)ᴴ * ((Pm)ᴴ * ((wDetector L.walkR _ hα).run x * (Pm * Um))) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc] at h2
  rw [lvlR_run]
  -- the centre
  have hs : (Um)ᴴ *ᵥ ((Pm)ᴴ *ᵥ wClock (kClock T k) L.fam.s) = embedClock 0 false (L.vx L.r) := by
    rw [← hP0, hPP, show L.fam.s = lin L.a L.r from rfl, ← L.upd_vx, ← hU0, hUU]
  rw [hs] at h2
  refine h2.mono ?_ le_rfl
  rintro χ ⟨y, rfl⟩
  change Pm *ᵥ (Um *ᵥ embedClock 0 false (L.vx y)) ∈
    {w | ∃ (c : ℂ) (v : QBasis ι σ W → ℂ), v ∈ L.fam.K ∧ w = wClock (kClock T k) (c • L.fam.s + v)}
  rw [hU0, L.upd_vx, hP0]
  obtain ⟨hdec, hK⟩ := L.fam.A_decomp y
  exact ⟨qInner L.r y, _, hK, by rw [← hdec]⟩

/-- **The level routine preserves the control-clean, query-blank support.** -/
theorem preserves_lvlR (hT0 : 0 < T) : Preserves ((L.lvlR T k hT0).run x) (Glvl L.Qb _) := by
  have hα := isQState_kClock hT0 k
  have hU : Preserves Um (Glvl L.Qb _) := preserves_liftClk_of L.preserves_upd _
  have hUH : Preserves (Um)ᴴ (Glvl L.Qb _) := by
    rw [liftReg_conjTranspose, liftReg_conjTranspose, liftReg_conjTranspose]
    exact preserves_liftClk_of L.preserves_upd_adj _
  have hP : Preserves Pm (Glvl L.Qb _) := preserves_clockReg _ _
  have hPH : Preserves (Pm)ᴴ (Glvl L.Qb _) := by
    rw [clockPrep, liftReg_conjTranspose, liftReg_conjTranspose, regOp_conjTranspose]
    exact preserves_clockReg _ _
  have hD : Preserves ((wDetector L.walkR _ hα).run x) (Glvl L.Qb _) := by
    rw [wDetector_run, Glvl_eq_ctrlClean]
    refine (preserves_selectPowers_adj (by rw [L.walk_run]; exact L.preserves_walk_adj) _).mul
      (Preserves.mul ?_ (preserves_selectPowers (by rw [L.walk_run]; exact L.preserves_walk) _))
    rw [← Glvl_eq_ctrlClean, clockStateRefl]
    exact preserves_qRefl (preserves_clockReg _ _)
  rw [lvlR_run]
  exact hUH.mul (hPH.mul (hD.mul (hP.mul hU)))

end LevelData

end QuantumQueryComplexity
