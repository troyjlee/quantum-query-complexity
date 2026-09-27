import QuantumQueryComplexity.Quantum.Control
import QuantumQueryComplexity.Quantum.RoutineLift
-- The clocked workspace nests five products deep, which exceeds the default
-- instance-synthesis size budget; `DecidableEq` on the basis then fails to
-- synthesize even though every component instance exists.
set_option synthInstance.maxSize 800

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The clock compiler: coherent powers of a routine

A uniform clock needs `selectPowers`, the **coherent** map

  `|c⟩|ψ⟩ ↦ |c⟩ Uᶜ|ψ⟩`,

which is *not* `QRoutine.iterate` — that applies a global `Uⁿ` to every branch.
The compilation is the standard one: `T-1` rounds, the `j`-th applying `U`
exactly on the branches whose clock has reached `j`.  Each round is

  XOR the predicate `j ≤ c` into the control bit  (a basis permutation, free)
  → `QRoutine.control` of the lifted routine        (`R.len` queries)
  → XOR it back                                     (free),

so a round costs exactly `R.len` and `selectPowers R T` costs `(T-1)·R.len`.

On top of `SELECT` this file builds the rest of the **operational** side of a
uniform-clock detector:

* `clockPack` — a *packed history*, one workspace vector per clock branch.  The
  branches are orthogonal, so Pythagoras holds and `SELECT` acts entrywise.
* `uniformClock` — the constant packed history, normalized.
* `clockAvgProj` — projection of the clock register onto its uniform
  superposition.  On a packed history it returns the **exact vector average**
  `T⁻¹ ∑_{c<T} f c`; on `SELECT` applied to a uniform clock, `T⁻¹ ∑_{c<T} Uᶜψ`.
* `clockPhaseRefl` — the conjugation `SELECTᴴ · clockRefl · SELECT`, of exact
  length `2(T-1)·R.len`: the reflection is a fixed unitary, so conjugation is
  the only cost.

The workspace is `CtrlWork ι (Fin T × W)`: the control bit and parking slot of
`Control.lean`, then the clock register, then the routine's own workspace.  This
file depends only on `Control` and `RoutineLift`; **whether that average is
small — the spectral half of the detector — is proved elsewhere**, and the
connection to spectral suppression belongs in a later file, not here.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] {T : ℕ}

/-- The workspace of a clocked routine. -/
abbrev ClockWork (ι : Type) (T : ℕ) (W : Type) : Type := CtrlWork ι (Fin T × W)

/-- The state with clock `c`, control bit `b`, blank parking slot, and `ψ`
elsewhere. -/
noncomputable def embedClock (c : Fin T) (b : Bool) (ψ : QBasis ι σ W → ℂ) :
    QBasis ι σ (ClockWork ι T W) → ℂ :=
  embedCtrl b (embedReg c ψ)

/-! ## Flipping the control bit on the clock -/

/-- Flip the control bit exactly on the branches whose clock has reached `j`. -/
def clockXorMap (j : ℕ) :
    QBasis ι σ (ClockWork ι T W) → QBasis ι σ (ClockWork ι T W)
  | (k, t, (b, s, (c, w))) => (k, t, (xor b (decide (j ≤ (c : ℕ))), s, (c, w)))

lemma clockXorMap_involutive (j : ℕ) :
    Function.Involutive (clockXorMap (ι := ι) (σ := σ) (W := W) (T := T) j) := by
  rintro ⟨k, t, b, s, c, w⟩
  show ((k, t, (xor (xor b (decide (j ≤ (c : ℕ)))) (decide (j ≤ (c : ℕ))), s, (c, w))) :
      QBasis ι σ (ClockWork ι T W)) = (k, t, (b, s, (c, w)))
  rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The bit flip, as a permutation of the basis. -/
def clockXorPerm (j : ℕ) : Equiv.Perm (QBasis ι σ (ClockWork ι T W)) :=
  Function.Involutive.toPerm _ (clockXorMap_involutive j)

/-- The bit flip, as a zero-query unitary. -/
def clockXorMat (j : ℕ) :
    Matrix (QBasis ι σ (ClockWork ι T W)) (QBasis ι σ (ClockWork ι T W)) ℂ :=
  qPerm (clockXorPerm j)

lemma clockXorMat_mem_unitaryGroup (j : ℕ) :
    clockXorMat (ι := ι) (σ := σ) (W := W) (T := T) j
      ∈ Matrix.unitaryGroup (QBasis ι σ (ClockWork ι T W)) ℂ :=
  qPerm_mem_unitaryGroup _

lemma clockXorMat_mulVec_apply (j : ℕ) (Φ : QBasis ι σ (ClockWork ι T W) → ℂ)
    (p : QBasis ι σ (ClockWork ι T W)) :
    (clockXorMat j *ᵥ Φ) p = Φ (clockXorMap j p) := by
  rw [clockXorMat, qPerm_mulVec_apply]
  rfl

/-- **The bit flip reads the clock and touches nothing else.** -/
theorem clockXorMat_mulVec_embedClock (j : ℕ) (c : Fin T) (b : Bool)
    (ψ : QBasis ι σ W → ℂ) :
    clockXorMat j *ᵥ embedClock c b ψ
      = embedClock c (xor b (decide (j ≤ (c : ℕ)))) ψ := by
  funext p
  rw [clockXorMat_mulVec_apply]
  obtain ⟨k, t, b', s, c', w⟩ := p
  rw [embedClock, embedClock, embedCtrl_apply, embedCtrl_apply]
  show (if xor b' (decide (j ≤ (c' : ℕ))) = b ∧ s = none then
      embedReg c ψ (k, t, (c', w)) else 0)
    = if b' = xor b (decide (j ≤ (c : ℕ))) ∧ s = none then
      embedReg c ψ (k, t, (c', w)) else 0
  by_cases hc : c' = c
  · subst hc
    by_cases hs : s = none
    · simp only [hs, and_true]
      by_cases hb : b' = xor b (decide (j ≤ (c' : ℕ)))
      · rw [if_pos, if_pos hb]
        rw [hb]
        cases b <;> cases (decide (j ≤ (c' : ℕ))) <;> rfl
      · rw [if_neg, if_neg hb]
        intro hcon
        exact hb (by rw [← hcon]; cases b' <;> cases (decide (j ≤ (c' : ℕ))) <;> rfl)
    · simp [hs]
  · have h0 : embedReg c ψ ((k, t, (c', w)) : QBasis ι σ (Fin T × W)) = 0 := by
      rw [embedReg_apply, if_neg hc]
    simp [h0]

/-! ## One round -/

/-- One clocked round: apply `R` exactly on the branches whose clock has reached
`j`.  The two bit flips are free, so this costs exactly `R.len` queries. -/
noncomputable def clockRound (R : QRoutine ι σ W) (T : ℕ) (j : ℕ) :
    QRoutine ι σ (ClockWork ι T W) :=
  ((QRoutine.ofUnitary (clockXorMat j) (clockXorMat_mem_unitaryGroup j)).comp
      ((R.liftReg (Fin T)).control)).comp
    (QRoutine.ofUnitary (clockXorMat j) (clockXorMat_mem_unitaryGroup j))

@[simp] lemma clockRound_len (R : QRoutine ι σ W) (T : ℕ) (j : ℕ) :
    (clockRound R T j).len = R.len := by
  show 0 + ((R.liftReg (Fin T)).control).len + 0 = R.len
  rw [control_len, QRoutine.liftReg_len]
  omega

lemma clockRound_run_matrix (R : QRoutine ι σ W) (T : ℕ) (j : ℕ) (a : ι → σ) :
    (clockRound R T j).run a
      = clockXorMat j * (((R.liftReg (Fin T)).control).run a * clockXorMat j) := by
  rw [clockRound, QRoutine.comp_run, QRoutine.comp_run, QRoutine.ofUnitary_run]

/-- **One round applies `R` exactly on the branches that have reached `j`.** -/
theorem clockRound_run (R : QRoutine ι σ W) (T : ℕ) (j : ℕ) (a : ι → σ)
    (c : Fin T) (ψ : QBasis ι σ W → ℂ) :
    (clockRound R T j).run a *ᵥ embedClock c false ψ
      = embedClock c false (if j ≤ (c : ℕ) then R.run a *ᵥ ψ else ψ) := by
  rw [clockRound_run_matrix, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    clockXorMat_mulVec_embedClock, Bool.false_xor]
  by_cases hj : j ≤ (c : ℕ)
  · have hd : decide (j ≤ (c : ℕ)) = true := decide_eq_true hj
    rw [hd, if_pos hj, embedClock, control_run_true, QRoutine.liftReg_run_embed,
      show embedCtrl true (embedReg c (R.run a *ᵥ ψ))
        = embedClock c true (R.run a *ᵥ ψ) from rfl,
      clockXorMat_mulVec_embedClock, hd, Bool.xor_self]
  · have hd : decide (j ≤ (c : ℕ)) = false := decide_eq_false hj
    rw [hd, if_neg hj, embedClock, control_run_false,
      show embedCtrl false (embedReg c ψ) = embedClock c false ψ from rfl,
      clockXorMat_mulVec_embedClock, hd, Bool.xor_self]

/-! ## Coherent powers -/

/-- The first `n` clocked rounds. -/
noncomputable def selectUpto (R : QRoutine ι σ W) (T : ℕ) :
    ℕ → QRoutine ι σ (ClockWork ι T W)
  | 0 => QRoutine.identity
  | n + 1 => (selectUpto R T n).comp (clockRound R T (n + 1))

/-- **Coherent powers**: `|c⟩|ψ⟩ ↦ |c⟩ Uᶜ|ψ⟩`, compiled as `T-1` rounds. -/
noncomputable def selectPowers (R : QRoutine ι σ W) (T : ℕ) :
    QRoutine ι σ (ClockWork ι T W) :=
  selectUpto R T (T - 1)

@[simp] lemma selectUpto_len (R : QRoutine ι σ W) (T : ℕ) (n : ℕ) :
    (selectUpto R T n).len = n * R.len := by
  induction n with
  | zero =>
      show (0 : ℕ) = 0 * R.len
      omega
  | succ n ih =>
      show (selectUpto R T n).len + (clockRound R T (n + 1)).len = (n + 1) * R.len
      rw [ih, clockRound_len]
      ring

/-- **The exact query count**: `(T-1) · R.len`. -/
@[simp] theorem selectPowers_len (R : QRoutine ι σ W) (T : ℕ) :
    (selectPowers R T).len = (T - 1) * R.len :=
  selectUpto_len R T (T - 1)

theorem selectUpto_run (R : QRoutine ι σ W) (T : ℕ) (n : ℕ) (a : ι → σ)
    (c : Fin T) (ψ : QBasis ι σ W → ℂ) :
    (selectUpto R T n).run a *ᵥ embedClock c false ψ
      = embedClock c false ((R.run a) ^ (min n (c : ℕ)) *ᵥ ψ) := by
  induction n with
  | zero =>
      show (1 : Matrix (QBasis ι σ (ClockWork ι T W)) (QBasis ι σ (ClockWork ι T W)) ℂ)
        *ᵥ embedClock c false ψ = _
      rw [Matrix.one_mulVec, Nat.zero_min, pow_zero, Matrix.one_mulVec]
  | succ n ih =>
      show ((selectUpto R T n).comp (clockRound R T (n + 1))).run a *ᵥ _ = _
      rw [QRoutine.comp_run, ← Matrix.mulVec_mulVec, ih, clockRound_run]
      congr 1
      by_cases hj : n + 1 ≤ (c : ℕ)
      · rw [if_pos hj,
          show min (n + 1) (c : ℕ) = min n (c : ℕ) + 1 from by omega,
          pow_succ', Matrix.mulVec_mulVec]
      · rw [if_neg hj, show min (n + 1) (c : ℕ) = min n (c : ℕ) from by omega]

/-- **Coherent powers, verified**: on a branch with clock `c` the routine has
been applied exactly `c` times. -/
theorem selectPowers_run (R : QRoutine ι σ W) (T : ℕ) (a : ι → σ) (c : Fin T)
    (ψ : QBasis ι σ W → ℂ) :
    (selectPowers R T).run a *ᵥ embedClock c false ψ
      = embedClock c false ((R.run a) ^ (c : ℕ) *ᵥ ψ) := by
  rw [selectPowers, selectUpto_run]
  have hc : (c : ℕ) < T := c.isLt
  rw [show min (T - 1) (c : ℕ) = (c : ℕ) from by omega]

/-! ## Packed histories

A **packed history** places a clock-indexed family in the clock branches, all
with a blank control bit.  It is the shape every statement about the clock takes:
`selectPowers` acts on one entrywise, the branches are mutually orthogonal, and
the uniform clock is the constant packed history, normalized. -/

/-- The packed history: `f c` in the branch whose clock reads `c`. -/
noncomputable def clockPack (f : Fin T → (QBasis ι σ W → ℂ)) :
    QBasis ι σ (ClockWork ι T W) → ℂ :=
  ∑ c : Fin T, embedClock c false (f c)

lemma embedClock_smul (c : Fin T) (b : Bool) (a : ℂ) (ψ : QBasis ι σ W → ℂ) :
    embedClock c b (a • ψ) = a • embedClock c b ψ := by
  simp only [embedClock, embedCtrl]
  rw [embedReg_smul, embedReg_smul, embedReg_smul]

lemma embedClock_sum {α : Type*} (c : Fin T) (b : Bool) (s : Finset α)
    (f : α → (QBasis ι σ W → ℂ)) :
    embedClock c b (∑ i ∈ s, f i) = ∑ i ∈ s, embedClock c b (f i) := by
  simp only [embedClock, embedCtrl]
  rw [embedReg_sum, embedReg_sum, embedReg_sum]

/-- **`SELECT` acts on a packed history entrywise**: branch `c` gets `Uᶜ`. -/
theorem selectPowers_run_clockPack (R : QRoutine ι σ W) (T : ℕ) (a : ι → σ)
    (f : Fin T → (QBasis ι σ W → ℂ)) :
    (selectPowers R T).run a *ᵥ clockPack f
      = clockPack (fun c => (R.run a) ^ (c : ℕ) *ᵥ f c) := by
  rw [clockPack, Matrix.mulVec_sum, clockPack]
  exact Finset.sum_congr rfl fun c _ => selectPowers_run R T a c (f c)

/-- **Distinct clock branches are orthogonal**, and a branch is an isometry. -/
theorem qInner_embedClock (c c' : Fin T) (b b' : Bool) (ψ φ : QBasis ι σ W → ℂ) :
    qInner (embedClock c b ψ) (embedClock c' b' φ)
      = if c = c' ∧ b = b' then qInner ψ φ else 0 := by
  simp only [embedClock, embedCtrl, qInner_embedReg]
  by_cases hb : b = b' <;> by_cases hc : c = c' <;> simp [hb, hc]

/-- **Pythagoras for a packed history.** -/
theorem qNormSq_clockPack (f : Fin T → (QBasis ι σ W → ℂ)) :
    qNormSq (clockPack f) = ∑ c : Fin T, qNormSq (f c) := by
  have h : ((qNormSq (clockPack f) : ℝ) : ℂ)
      = ∑ c : Fin T, ((qNormSq (f c) : ℝ) : ℂ) := by
    rw [← qInner_self, clockPack, qInner_sum_left]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [qInner_sum_right, Finset.sum_eq_single c]
    · rw [qInner_embedClock, if_pos ⟨rfl, rfl⟩, qInner_self]
    · intro c' _ hc'
      rw [qInner_embedClock, if_neg fun hcon => hc' hcon.1.symm]
    · simp
  exact_mod_cast h

/-! ## The uniform clock -/

/-- The uniform clock: `ψ` in every branch, normalized. -/
noncomputable def uniformClock (T : ℕ) (ψ : QBasis ι σ W → ℂ) :
    QBasis ι σ (ClockWork ι T W) → ℂ :=
  ((Real.sqrt T : ℝ) : ℂ)⁻¹ • clockPack (fun _ : Fin T => ψ)

/-- **The uniform clock is normalized** (for `0 < T`). -/
theorem qNormSq_uniformClock (hT : 0 < T) (ψ : QBasis ι σ W → ℂ) :
    qNormSq (uniformClock T ψ) = qNormSq ψ := by
  have hT0 : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have h1 : Complex.normSq (((Real.sqrt T : ℝ) : ℂ)⁻¹) = ((T : ℝ))⁻¹ := by
    rw [Complex.normSq_inv, Complex.normSq_ofReal,
      Real.mul_self_sqrt (Nat.cast_nonneg T)]
  rw [uniformClock, qNormSq_smul, h1, qNormSq_clockPack, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **The clock spread preserves basis support**: where the underlying
vector vanishes at the stripped coordinate, the clocked vector vanishes at
the full one.  This is what lets a readout of the underlying workspace act
through the clock. -/
lemma uniformClock_apply_eq_zero (T : ℕ) (ψ : QBasis ι σ W → ℂ)
    {b : QBasis ι σ (ClockWork ι T W)}
    (h : ψ (b.1, b.2.1, b.2.2.2.2.2) = 0) :
    uniformClock T ψ b = 0 := by
  obtain ⟨k, t, bb, s, c', w⟩ := b
  have h' : ψ (k, t, w) = 0 := h
  have hz : ∀ c : Fin T,
      embedClock c false ψ ((k, t, (bb, s, (c', w)))
        : QBasis ι σ (ClockWork ι T W)) = 0 := by
    intro c
    simp [embedClock, embedCtrl, embedReg_apply, h']
  rw [uniformClock, Pi.smul_apply, clockPack, Finset.sum_apply,
    Finset.sum_eq_zero fun c _ => hz c, smul_zero]

/-- **`SELECT` on the uniform clock** builds the history `Uᶜψ`. -/
theorem selectPowers_run_uniformClock (R : QRoutine ι σ W) (T : ℕ) (a : ι → σ)
    (ψ : QBasis ι σ W → ℂ) :
    (selectPowers R T).run a *ᵥ uniformClock T ψ
      = ((Real.sqrt T : ℝ) : ℂ)⁻¹ • clockPack (fun c => (R.run a) ^ (c : ℕ) *ᵥ ψ) := by
  rw [uniformClock, Matrix.mulVec_smul, selectPowers_run_clockPack]

/-! ## The averaging projector

Projecting the clock register back onto the uniform superposition is what turns a
packed history into the **vector average** `T⁻¹ ∑_{c<T} Uᶜψ`.  That average is
the whole point of a uniform clock: it is `1` on a fixed vector and small on a
vector whose chord distance is large, which is the suppression the detector
needs. -/

/-- The uniform-average matrix on the clock register. -/
noncomputable def avgMat (T : ℕ) : Matrix (Fin T) (Fin T) ℂ :=
  Matrix.of fun _ _ => (T : ℂ)⁻¹

theorem isQProjector_avgMat (T : ℕ) : IsQProjector (avgMat T) := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    exact ⟨by ext i j; exact i.elim0, by ext i j; exact i.elim0⟩
  have hT0 : (T : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  constructor
  · ext i j
    rw [Matrix.conjTranspose_apply]
    change star ((T : ℂ)⁻¹) = (T : ℂ)⁻¹
    rw [star_inv₀, star_natCast]
  · ext i j
    rw [Matrix.mul_apply]
    change (∑ _k : Fin T, (T : ℂ)⁻¹ * (T : ℂ)⁻¹) = (T : ℂ)⁻¹
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

/-- **The averaging projector on the clock register.** -/
noncomputable def clockAvgProj (T : ℕ) :
    Matrix (QBasis ι σ (ClockWork ι T W)) (QBasis ι σ (ClockWork ι T W)) ℂ :=
  liftReg Bool (liftReg (Option ι) (regOp (avgMat T)))

theorem isQProjector_clockAvgProj (T : ℕ) :
    IsQProjector (clockAvgProj (ι := ι) (σ := σ) (W := W) T) :=
  isQProjector_liftReg (isQProjector_liftReg (isQProjector_regOp (isQProjector_avgMat T)))

theorem clockAvgProj_mulVec_embedClock (T : ℕ) (c : Fin T) (ψ : QBasis ι σ W → ℂ) :
    clockAvgProj T *ᵥ embedClock c false ψ
      = ∑ c' : Fin T, (T : ℂ)⁻¹ • embedClock c' false ψ := by
  rw [clockAvgProj, embedClock, embedCtrl, liftReg_mulVec_embed, liftReg_mulVec_embed,
    regOp_mulVec_embedReg, embedReg_sum, embedReg_sum]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [embedReg_smul, embedReg_smul]
  rfl

/-- **The averaging projector produces the exact vector average.**  On the packed
history `f` it returns the constant history `T⁻¹ ∑_{c<T} f c` — in particular, on
`SELECT` applied to a uniform clock, `T⁻¹ ∑_{c<T} Uᶜψ`. -/
theorem clockAvgProj_mulVec_clockPack (T : ℕ) (f : Fin T → (QBasis ι σ W → ℂ)) :
    clockAvgProj T *ᵥ clockPack f
      = clockPack (fun _ => (T : ℂ)⁻¹ • ∑ c : Fin T, f c) := by
  rw [clockPack, Matrix.mulVec_sum,
    Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) =>
      clockAvgProj_mulVec_embedClock T c (f c),
    Finset.sum_comm, clockPack]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [embedClock_smul, embedClock_sum, Finset.smul_sum]

/-! ## The phase reflection

`clockRefl` reflects about the uniform-clock subspace; it is a fixed unitary,
touching no oracle.  Conjugating it by `SELECT` is the phase reflection of a
uniform-clock detector, and the conjugation is where the query count doubles —
and only doubles. -/

/-- The reflection about the uniform-clock subspace. -/
noncomputable def clockRefl (T : ℕ) :
    Matrix (QBasis ι σ (ClockWork ι T W)) (QBasis ι σ (ClockWork ι T W)) ℂ :=
  qRefl (clockAvgProj T)

theorem clockRefl_mem_unitaryGroup (T : ℕ) :
    clockRefl (ι := ι) (σ := σ) (W := W) T
      ∈ Matrix.unitaryGroup (QBasis ι σ (ClockWork ι T W)) ℂ :=
  qRefl_mem_unitaryGroup (isQProjector_clockAvgProj T)

/-- **`SELECTᴴ` undoes the powers branchwise.** -/
theorem selectPowers_conjTranspose_mulVec_embedClock (R : QRoutine ι σ W) (T : ℕ)
    (a : ι → σ) (c : Fin T) (ψ : QBasis ι σ W → ℂ) :
    ((selectPowers R T).run a)ᴴ *ᵥ embedClock c false ψ
      = embedClock c false (((R.run a) ^ (c : ℕ))ᴴ *ᵥ ψ) := by
  have hpow : (R.run a) ^ (c : ℕ) ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ :=
    pow_mem (R.run_mem_unitaryGroup a) _
  have hinv : (R.run a) ^ (c : ℕ) * (((R.run a) ^ (c : ℕ))ᴴ) = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hpow
    rwa [Matrix.star_eq_conjTranspose] at h
  have hS : (selectPowers R T).run a
      *ᵥ embedClock c false (((R.run a) ^ (c : ℕ))ᴴ *ᵥ ψ) = embedClock c false ψ := by
    rw [selectPowers_run, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  rw [← hS, Matrix.mulVec_mulVec,
    conjTranspose_mul_self_of_unitary
      ((selectPowers R T).run_mem_unitaryGroup a), Matrix.one_mulVec]

/-- **`SELECTᴴ` on a packed history.** -/
theorem selectPowers_conjTranspose_mulVec_clockPack (R : QRoutine ι σ W) (T : ℕ)
    (a : ι → σ) (f : Fin T → (QBasis ι σ W → ℂ)) :
    ((selectPowers R T).run a)ᴴ *ᵥ clockPack f
      = clockPack (fun c => ((R.run a) ^ (c : ℕ))ᴴ *ᵥ f c) := by
  rw [clockPack, Matrix.mulVec_sum, clockPack]
  exact Finset.sum_congr rfl fun c _ =>
    selectPowers_conjTranspose_mulVec_embedClock R T a c (f c)

/-- **The clock reflection is self-adjoint** — it is the reflection about a
projector.  No positivity hypothesis. -/
theorem clockRefl_conjTranspose (T : ℕ) :
    (clockRefl (ι := ι) (σ := σ) (W := W) T)ᴴ = clockRefl T :=
  qRefl_conjTranspose (isQProjector_clockAvgProj T)

/-- **The phase reflection**: `SELECTᴴ · clockRefl · SELECT`. -/
noncomputable def clockPhaseRefl (R : QRoutine ι σ W) (T : ℕ) :
    QRoutine ι σ (ClockWork ι T W) :=
  (selectPowers R T).conjFixed (clockRefl T) (clockRefl_mem_unitaryGroup T)

/-- **The exact query count of the phase reflection**: `2(T-1)·R.len`.  The
reflection itself is free, so conjugation is the only cost. -/
@[simp] theorem clockPhaseRefl_len (R : QRoutine ι σ W) (T : ℕ) :
    (clockPhaseRefl R T).len = 2 * ((T - 1) * R.len) := by
  rw [clockPhaseRefl, QRoutine.conjFixed_len, selectPowers_len]

theorem clockPhaseRefl_run (R : QRoutine ι σ W) (T : ℕ) (a : ι → σ) :
    (clockPhaseRefl R T).run a
      = ((selectPowers R T).run a)ᴴ * (clockRefl T * (selectPowers R T).run a) :=
  QRoutine.conjFixed_run _ _ _ _

/-- **The detector is self-adjoint.**  Conjugating a self-adjoint reflection
by a unitary keeps it self-adjoint.  With unitarity this is what makes the
two signed conversion errors *orthogonal*, so they combine by an exact
half-sum rather than a triangle inequality — which is where the constant
would otherwise be lost. -/
theorem clockPhaseRefl_run_conjTranspose (R : QRoutine ι σ W) (T : ℕ)
    (a : ι → σ) :
    ((clockPhaseRefl R T).run a)ᴴ = (clockPhaseRefl R T).run a := by
  rw [clockPhaseRefl_run, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, clockRefl_conjTranspose,
    Matrix.mul_assoc]

/-! ## The averaging identity, and exact completeness

Two facts fix the detector's behaviour at the two extremes.  On a **fixed**
vector it is exactly the identity — not approximately, which is what lets the
effective-gap argument conclude anything at all.  On a general vector it returns
the **vector average** `T⁻¹ ∑_{c<T} Uᶜψ`, whose size is the detector's entire
content; bounding *that* is the spectral half, proved elsewhere. -/

/-- **The normalized averaging identity.**  Projecting `SELECT` applied to a
uniform clock returns a uniform clock carrying the exact vector average. -/
theorem clockAvgProj_mulVec_selectPowers_uniformClock (R : QRoutine ι σ W) (T : ℕ)
    (a : ι → σ) (ψ : QBasis ι σ W → ℂ) :
    clockAvgProj T *ᵥ ((selectPowers R T).run a *ᵥ uniformClock T ψ)
      = uniformClock T ((T : ℂ)⁻¹ • ∑ c : Fin T, (R.run a) ^ (c : ℕ) *ᵥ ψ) := by
  rw [selectPowers_run_uniformClock, Matrix.mulVec_smul,
    clockAvgProj_mulVec_clockPack, uniformClock]

/-- **The uniform clock is fixed by the averaging projector**: averaging a
constant history changes nothing. -/
theorem clockAvgProj_mulVec_uniformClock (hT : 0 < T) (ψ : QBasis ι σ W → ℂ) :
    clockAvgProj T *ᵥ uniformClock T ψ = uniformClock T ψ := by
  have hT0 : (T : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have hconst : ((T : ℂ)⁻¹ • ∑ _c : Fin T, ψ) = ψ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hT0, one_smul]
  simp only [uniformClock, Matrix.mulVec_smul, clockAvgProj_mulVec_clockPack, hconst]

/-- **The reflection fixes the uniform clock** (`+1`). -/
theorem clockRefl_mulVec_uniformClock (hT : 0 < T) (ψ : QBasis ι σ W → ℂ) :
    clockRefl T *ᵥ uniformClock T ψ = uniformClock T ψ := by
  rw [clockRefl, qRefl, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    clockAvgProj_mulVec_uniformClock hT]
  module

/-- **The reflection negates the complement** (`-1`).  This is the sign: with
`qRefl P = 2P - 1` the *uniform* subspace is the `+1` eigenspace, so a detector
built from it reports agreement as `+1` and disagreement as `-1`. -/
theorem clockRefl_mulVec_of_avg_eq_zero {T : ℕ} {v : QBasis ι σ (ClockWork ι T W) → ℂ}
    (h : clockAvgProj T *ᵥ v = 0) : clockRefl T *ᵥ v = -v := by
  rw [clockRefl, qRefl, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h,
    smul_zero, zero_sub]

lemma pow_mulVec_eq_self {U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
    {ψ : QBasis ι σ W → ℂ} (h : U *ᵥ ψ = ψ) (n : ℕ) : U ^ n *ᵥ ψ = ψ := by
  induction n with
  | zero => rw [pow_zero, Matrix.one_mulVec]
  | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h, ih]

/-- **`SELECT` fixes a uniform clock over a fixed vector**: every branch applies
a power of `U`, and every power fixes `ψ`. -/
theorem selectPowers_run_mulVec_uniformClock_of_fixed (R : QRoutine ι σ W) (T : ℕ)
    (a : ι → σ) {ψ : QBasis ι σ W → ℂ} (h : R.run a *ᵥ ψ = ψ) :
    (selectPowers R T).run a *ᵥ uniformClock T ψ = uniformClock T ψ := by
  have hf : (fun c : Fin T => (R.run a) ^ (c : ℕ) *ᵥ ψ) = (fun _ : Fin T => ψ) :=
    funext fun c => pow_mulVec_eq_self h _
  rw [selectPowers_run_uniformClock, hf, uniformClock]

/-- **Exact completeness**: on a fixed vector the detector is the identity, with
no error term at all. -/
theorem clockPhaseRefl_run_mulVec_uniformClock_of_fixed (R : QRoutine ι σ W) {T : ℕ}
    (hT : 0 < T) (a : ι → σ) {ψ : QBasis ι σ W → ℂ} (h : R.run a *ᵥ ψ = ψ) :
    (clockPhaseRefl R T).run a *ᵥ uniformClock T ψ = uniformClock T ψ := by
  have hS : (selectPowers R T).run a *ᵥ uniformClock T ψ = uniformClock T ψ :=
    selectPowers_run_mulVec_uniformClock_of_fixed R T a h
  have hSt : ((selectPowers R T).run a)ᴴ *ᵥ uniformClock T ψ = uniformClock T ψ := by
    conv_lhs => rw [← hS]
    rw [Matrix.mulVec_mulVec, conjTranspose_mul_self_of_unitary
      ((selectPowers R T).run_mem_unitaryGroup a), Matrix.one_mulVec]
  rw [clockPhaseRefl_run, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hS,
    clockRefl_mulVec_uniformClock hT, hSt]


/-! ## The uniform clock, as an isometry

Moved down from `Detection.lean`: this geometry is generic, and the uniform
witness needs the clock isometry without importing the Boolean detection
layer. -/

lemma embedReg_add {V : Type} [Fintype V] [DecidableEq V] (v : V)
    (ψ φ : QBasis ι σ W → ℂ) :
    embedReg v (ψ + φ) = embedReg v ψ + embedReg v φ := by
  funext p
  by_cases h : p.2.2.1 = v <;> simp [embedReg_apply, h]

lemma embedClock_add (c : Fin T) (b : Bool) (ψ φ : QBasis ι σ W → ℂ) :
    embedClock c b (ψ + φ) = embedClock c b ψ + embedClock c b φ := by
  simp only [embedClock, embedCtrl]
  rw [embedReg_add, embedReg_add, embedReg_add]

/-- **The uniform clock is additive.** -/
lemma uniformClock_add (T : ℕ) (ψ φ : QBasis ι σ W → ℂ) :
    uniformClock T (ψ + φ) = uniformClock T ψ + uniformClock T φ := by
  simp only [uniformClock, clockPack]
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun c _ => embedClock_add c false ψ φ

/-- **The inner product of two packed histories** is branchwise. -/
theorem qInner_clockPack (f g : Fin T → (QBasis ι σ W → ℂ)) :
    qInner (clockPack f) (clockPack g) = ∑ c : Fin T, qInner (f c) (g c) := by
  rw [clockPack, clockPack, qInner_sum_left]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [qInner_sum_right, Finset.sum_eq_single c]
  · rw [qInner_embedClock, if_pos ⟨rfl, rfl⟩]
  · intro c' _ hc'
    rw [qInner_embedClock, if_neg fun hcon => hc' hcon.1.symm]
  · simp

/-- **The uniform clock is an isometry** (for `0 < T`). -/
theorem qInner_uniformClock (hT : 0 < T) (ψ φ : QBasis ι σ W → ℂ) :
    qInner (uniformClock T ψ) (uniformClock T φ) = qInner ψ φ := by
  have hcast : ((T : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  rw [uniformClock, uniformClock, qInner_smul_left, qInner_smul_right,
    qInner_clockPack, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, star_inv₀, RCLike.star_def, Complex.conj_ofReal]
  rw [show (((Real.sqrt T : ℝ) : ℂ))⁻¹
        * ((((Real.sqrt T : ℝ) : ℂ))⁻¹ * ((T : ℂ) * qInner ψ φ))
      = (((Real.sqrt T : ℝ) : ℂ) * ((Real.sqrt T : ℝ) : ℂ))⁻¹
        * ((T : ℂ) * qInner ψ φ) from by rw [mul_inv]; ring]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg T),
    show (((T : ℝ) : ℂ)) = ((T : ℕ) : ℂ) from by push_cast; ring,
    inv_mul_cancel_left₀ hcast]

/-- **The uniform clock is `ℂ`-homogeneous.** -/
lemma uniformClock_smul (T : ℕ) (r : ℂ) (ψ : QBasis ι σ W → ℂ) :
    uniformClock T (r • ψ) = r • uniformClock T ψ := by
  simp only [uniformClock, clockPack]
  rw [Finset.sum_congr rfl fun c _ => embedClock_smul c false r ψ,
    ← Finset.smul_sum, smul_comm]

/-- **The uniform clock is subtractive.** -/
lemma uniformClock_sub (T : ℕ) (ψ φ : QBasis ι σ W → ℂ) :
    uniformClock T (ψ - φ) = uniformClock T ψ - uniformClock T φ := by
  have h2 := uniformClock_add T (ψ - φ) φ
  rw [sub_add_cancel] at h2
  rw [h2, add_sub_cancel_right]

/-- **The empty clock carries nothing**: at `T = 0` the clock pack is an empty
sum, so `uniformClock 0 ψ = 0`.  This is what lets `T = 0` splits downstream
avoid positivity hypotheses. -/
lemma uniformClock_zero (ψ : QBasis ι σ W → ℂ) :
    uniformClock 0 ψ = 0 := by
  rw [uniformClock, clockPack]
  simp


end QuantumQueryComplexity
