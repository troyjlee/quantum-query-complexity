import QuantumQueryComplexity.Quantum.UniformWitness
import QuantumQueryComplexity.Quantum.InputDetector
set_option synthInstance.maxSize 2000

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Milestone D: the uniform detector and its conversion errors

The detector of the cardinality-free construction: the clocked phase
reflection of the reflection product built from the physical generators and
the one global projector `uniformL P α`, at exactly `4(T-1)` queries.  The
two signed conversion errors are

    e₊ = D·clock(t_{x+}) − clock(t_{x+}),
    e₋ = D·clock(t_{x−}) + clock(t_{x−}),

and this file proves the three conversion-distance facts:

* the positive bound `‖e₊‖² ≤ 8α²c` — the detector fixes the clocked
  witness `clock(φ_x)` **exactly**, so on the bare target the error is the
  moved packet, `e₊ = α·(1 − D)·clock(V_x)`, one unitary-move bound away
  from the `v`-mass that `P.IsCostLe` controls.  A `T = 0` split
  (`uniformClock_zero`) keeps the statement free of any positivity
  hypothesis on `T`;
* the negative bound `‖e₋‖ ≤ Δ√(1 + c/(2α²)) + 4/(TΔ)` by one near/far
  split of the `−` target, the only statement needing `hα`, `hT`, `hΔ`;
* the **combination**: the end-to-end error `D·clock(common) − clock(out)`
  is `(e₊ + e₋)/√2` by pure linearity, and `e₊ ⟂ e₋` **exactly** — the
  detector is self-adjoint and unitary — so its squared norm is the exact
  half-sum `(‖e₊‖² + ‖e₋‖²)/2`, never a triangle bound.

## The one load-bearing setting: `synthInstance.maxSize 2000`

The ambient basis here is

    QBasis ι σ (ClockWork ι T (UWork ↥(Set.range f) ι K))

— five products deep with a set-coercion subtype inside.  Its canonical
`Fintype`/`DecidableEq` instances synthesize fine, but the derivation no
longer fits the clock layer's usual `synthInstance.maxSize 800` once
`↥(Set.range f)` sits inside `ClockWork`; this file needs `2000`.  The size
raise is the **entire** fix, established by probing every regime
(2026-08-24): at the Lean default (128) and at `800` synthesis fails
outright; at `2000` this file compiles at default heartbeats — with or
without the opacity conventions below, and even with a gratuitous
`classical`.

**The trap this diagnosis replaces.**  The failure reads as a bare "failed
to synthesize DecidableEq", which invites exactly the wrong repairs, and
those repairs produced the previous round's misdiagnosis:

* `classical` "fixes" the failure because the low-priority
  `Classical.propDecidable` steps in as a fallback — but only in the
  under-provisioned regime, i.e. precisely where it gets baked into terms in
  place of the canonical `instDecidableEqProd` chain.  The `whnf` timeout
  observed downstream in that regime is consistent with a non-defeq instance
  clash, though the probe matrix does not independently establish that
  causal chain.  (At `2000` the fallback never fires, and `classical` is
  inert.)
* local `haveI` copies of `Set.fintypeRange`/`Subtype.instDecidableEq` mask
  the failure the same way; the same qualification applies to their
  downstream pathology.

So on this basis, treat "failed to synthesize" as a **capacity signal**:
raise `synthInstance.maxSize`, never paper over it with `classical` or
`haveI`.

Style, not correctness: the proofs below keep the large terms opaque
(`let D := …`, `let V := …`) and type-ascribe the unitarity fact `hD` to
the ambient basis.  The fully inline forms also compile at `2000`; the
conventions are kept for readability and to keep every instance visibly
canonical.

Genericizing the target register `R` was considered and rejected: the whole
scaled layer (`realizedTPlus/Minus`, `uniformPhi/W/Psi`, `uniformL`) already
specializes `R := ↥(Set.range f)`, and the concrete form needs nothing
beyond the size raise.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ K X O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [DecidableEq σ] [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq O]
  {read : X → ι → σ} {f : X → O}

/-- **The uniform detector**: the clocked phase reflection of the reflection
product `R_P·R_L`, for the physical generators and the global projector
`uniformL P α`. -/
noncomputable def uniformDetector (P : DualPairOn read K f) (α : ℝ) (T : ℕ) :
    QRoutine ι σ (ClockWork ι T (UWork ↥(Set.range f) ι K)) :=
  clockPhaseRefl (inputReflProduct
    (uniformGen (R := ↥(Set.range f)) (ι := ι) (σ := σ) (K := K))
    (uniformL P α) (isQProjector_uniformL P α)) T

/-- The unfolding equation, so nothing downstream unfolds the definition. -/
theorem uniformDetector_eq (P : DualPairOn read K f) (α : ℝ) (T : ℕ) :
    uniformDetector P α T
      = clockPhaseRefl (inputReflProduct
          (uniformGen (R := ↥(Set.range f)) (ι := ι) (σ := σ) (K := K))
          (uniformL P α) (isQProjector_uniformL P α)) T := rfl

/-- **The exact cost of the uniform detector**: `4(T-1)` queries. -/
@[simp] theorem uniformDetector_len (P : DualPairOn read K f) (α : ℝ) (T : ℕ) :
    (uniformDetector P α T).len = 4 * (T - 1) := by
  rw [uniformDetector_eq, clockPhaseRefl_len_inputReflProduct]

/-- **The detector fixes the clocked witness exactly** — `φ_x` is a positive
witness, so this is completeness with no error term. -/
theorem uniformDetector_run_mulVec_uniformClock_uniformPhi
    (P : DualPairOn read K f) (α : ℝ) {T : ℕ} (hT : 0 < T) (x : X) :
    (uniformDetector P α T).run (read x)
        *ᵥ uniformClock T (uniformPhi P α x)
      = uniformClock T (uniformPhi P α x) := by
  rw [uniformDetector_eq]
  exact (isPosWitness_uniformPhi P α x).clockPhaseRefl_run_mulVec_uniformClock
    (isQProjector_uniformL P α) hT

/-! ## The two conversion errors -/

/-- `e₊ = D·clock(t_{x+}) − clock(t_{x+})`: the deviation of the detector
from `+1` on the clocked `+` target. -/
noncomputable def uniformPlusError (P : DualPairOn read K f) (α : ℝ) (T : ℕ)
    (x : X) : QBasis ι σ (ClockWork ι T (UWork ↥(Set.range f) ι K)) → ℂ :=
  (uniformDetector P α T).run (read x)
      *ᵥ uniformClock T (realizedTPlus (K := K) f x)
    - uniformClock T (realizedTPlus (K := K) f x)

/-- `e₋ = D·clock(t_{x−}) + clock(t_{x−})`: the deviation of the detector
from `-1` on the clocked `−` target.  The `+` is the sign of the detector's
`-1` verdict. -/
noncomputable def uniformMinusError (P : DualPairOn read K f) (α : ℝ) (T : ℕ)
    (x : X) : QBasis ι σ (ClockWork ι T (UWork ↥(Set.range f) ι K)) → ℂ :=
  (uniformDetector P α T).run (read x)
      *ᵥ uniformClock T (realizedTMinus (K := K) f x)
    + uniformClock T (realizedTMinus (K := K) f x)

/-! ## The positive bound -/

/-- **The rearranged plus error**: the detector fixes `clock(φ_x)` and
`φ_x = t_{x+} + α·V_x`, so the error on the bare target is the moved packet,
`e₊ = α·(1 − D)·clock(V_x)`. -/
theorem uniformPlusError_eq (P : DualPairOn read K f) (α : ℝ) {T : ℕ}
    (hT : 0 < T) (x : X) :
    uniformPlusError P α T x
      = ((α : ℝ) : ℂ) •
          ((1 - (uniformDetector P α T).run (read x))
            *ᵥ uniformClock T (realizedPacketV P.v read x)) := by
  have hfix := uniformDetector_run_mulVec_uniformClock_uniformPhi P α hT x
  have hphi : uniformClock T (uniformPhi P α x)
      = uniformClock T (realizedTPlus (K := K) f x)
        + ((α : ℝ) : ℂ) • uniformClock T (realizedPacketV P.v read x) := by
    rw [show uniformPhi P α x
          = realizedTPlus (K := K) f x
            + ((α : ℝ) : ℂ) • realizedPacketV P.v read x from rfl,
      uniformClock_add, uniformClock_smul]
  rw [hphi, Matrix.mulVec_add, Matrix.mulVec_smul] at hfix
  rw [show uniformPlusError P α T x
        = (uniformDetector P α T).run (read x)
            *ᵥ uniformClock T (realizedTPlus (K := K) f x)
          - uniformClock T (realizedTPlus (K := K) f x) from rfl,
    Matrix.sub_mulVec, Matrix.one_mulVec]
  linear_combination (norm := module) hfix

/-- **The positive conversion bound**: `‖e₊‖² ≤ 8α²c`.  No hypothesis on `T`
or `α`: the `T = 0` clock is zero, and the bound's sign comes from the cost
hypothesis itself. -/
theorem qNormSq_uniformPlusError_le (P : DualPairOn read K f) {c : ℝ}
    (hP : P.IsCostLe c) (α : ℝ) (T : ℕ) (x : X) :
    qNormSq (uniformPlusError P α T x) ≤ 8 * α ^ 2 * c := by
  have hmass : (∑ p : ι × K, P.v x p.1 p.2 * P.v x p.1 p.2) ≤ c := by
    simpa only [Fintype.sum_prod_type] using hP.2 x
  have hc : 0 ≤ c :=
    le_trans (Finset.sum_nonneg fun p _ => mul_self_nonneg _) hmass
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    rw [show uniformPlusError P α 0 x
          = (uniformDetector P α 0).run (read x)
              *ᵥ uniformClock 0 (realizedTPlus (K := K) f x)
            - uniformClock 0 (realizedTPlus (K := K) f x) from rfl,
      uniformClock_zero, Matrix.mulVec_zero, sub_zero, qNormSq_zero]
    exact mul_nonneg (by positivity) hc
  · let D := (uniformDetector P α T).run (read x)
    let V := realizedPacketV (R := ↥(Set.range f)) P.v read x
    have heq : uniformPlusError P α T x
        = ((α : ℝ) : ℂ) • ((1 - D) *ᵥ uniformClock T V) :=
      uniformPlusError_eq P α hT x
    have hD : D ∈ Matrix.unitaryGroup
        (QBasis ι σ (ClockWork ι T (UWork ↥(Set.range f) ι K))) ℂ :=
      (uniformDetector P α T).run_mem_unitaryGroup (read x)
    have hmove := qNormSq_one_sub_pow_mulVec_le hD 1 (uniformClock T V)
    rw [pow_one] at hmove
    have hclock : qNormSq (uniformClock T V) = qNormSq V :=
      qNormSq_uniformClock hT V
    have hV : qNormSq V = 2 * ∑ p : ι × K, P.v x p.1 p.2 * P.v x p.1 p.2 :=
      qNormSq_realizedPacketV (R := ↥(Set.range f)) P.v read x
    have hE : qNormSq ((1 - D) *ᵥ uniformClock T V) ≤ 8 * c := by
      rw [hclock, hV] at hmove
      linarith
    rw [heq, qNormSq_smul, Complex.normSq_ofReal]
    calc α * α * qNormSq ((1 - D) *ᵥ uniformClock T V)
        ≤ α * α * (8 * c) :=
          mul_le_mul_of_nonneg_left hE (mul_self_nonneg α)
      _ = 8 * α ^ 2 * c := by ring

/-! ## The negative bound

`w_x` is a negative witness — `uniformL` kills it — and `inputProj` sends it
to the bare `−` target, so the effective gap and the divided detector bound
apply to the near/far split of `t_{x−}` directly:

* the near part is small — `‖N‖² ≤ (Δ²/4)‖w_x‖²` by
  `effective_chord_gap_sq_inputReflProduct` — so its detector error costs
  at most `2‖N‖`;
* on the far part the detector reads `-1` up to `4/(TΔ)`, by
  `qNormSq_clockPhaseRefl_add_le_div_inputReflProduct` and `‖t_{x−}‖ = 1`.

One near/far triangle inequality combines the two.  This is the only place
`hα`, `hT`, `hΔ` are genuinely needed. -/

/-- The near part of the realized `−` target, at window `Δ`. -/
noncomputable def uniformNear (P : DualPairOn read K f) (α : ℝ) (Δ : ℝ)
    (x : X) : UQBasis ↥(Set.range f) ι σ K → ℂ :=
  chordNearProj ((inputReflProduct
      (uniformGen (R := ↥(Set.range f)) (ι := ι) (σ := σ) (K := K))
      (uniformL P α) (isQProjector_uniformL P α)).run (read x)) Δ
    *ᵥ realizedTMinus (K := K) f x

/-- The far part of the realized `−` target, at window `Δ`. -/
noncomputable def uniformFar (P : DualPairOn read K f) (α : ℝ) (Δ : ℝ)
    (x : X) : UQBasis ↥(Set.range f) ι σ K → ℂ :=
  chordFarProj ((inputReflProduct
      (uniformGen (R := ↥(Set.range f)) (ι := ι) (σ := σ) (K := K))
      (uniformL P α) (isQProjector_uniformL P α)).run (read x)) Δ
    *ᵥ realizedTMinus (K := K) f x

/-- **The near/far split of the `−` target.** -/
theorem uniformNear_add_uniformFar (P : DualPairOn read K f) (α : ℝ) (Δ : ℝ)
    (x : X) :
    uniformNear P α Δ x + uniformFar P α Δ x
      = realizedTMinus (K := K) f x := by
  rw [uniformNear, uniformFar, ← Matrix.add_mulVec,
    chordNearProj_add_chordFarProj, Matrix.one_mulVec]

/-- **The near part is small**: the effective gap charges it to `‖w_x‖²`,
which the cost hypothesis bounds. -/
theorem qNormSq_uniformNear_le (P : DualPairOn read K f) {c : ℝ}
    (hP : P.IsCostLe c) {α : ℝ} (hα : α ≠ 0) (Δ : ℝ) (x : X) :
    qNormSq (uniformNear P α Δ x)
      ≤ Δ ^ 2 / 4 * (1 + c / (2 * α ^ 2)) := by
  have hgap := effective_chord_gap_sq_inputReflProduct
    (uniformGen (R := ↥(Set.range f)) (ι := ι) (σ := σ) (K := K))
    (uniformL P α) (isQProjector_uniformL P α) (read x)
    (uniformL_mulVec_uniformW P hα x) Δ
  rw [inputProj_mulVec_uniformW] at hgap
  rw [uniformNear]
  calc qNormSq (chordNearProj ((inputReflProduct
          (uniformGen (R := ↥(Set.range f)) (ι := ι) (σ := σ) (K := K))
          (uniformL P α) (isQProjector_uniformL P α)).run (read x)) Δ
        *ᵥ realizedTMinus (K := K) f x)
      ≤ Δ ^ 2 / 4 * qNormSq (uniformW P α x) := hgap
    _ ≤ Δ ^ 2 / 4 * (1 + c / (2 * α ^ 2)) :=
        mul_le_mul_of_nonneg_left (qNormSq_uniformW_le P hP hα x)
          (by positivity)

/-- **The detector reads `-1` on the far part**, up to `16/(T²Δ²)` — the
`−` target is a unit vector, so no witness norm enters. -/
theorem qNormSq_uniformDetector_far_add_le (P : DualPairOn read K f) (α : ℝ)
    {T : ℕ} (hT : 0 < T) {Δ : ℝ} (hΔ : 0 < Δ) (x : X) :
    qNormSq ((uniformDetector P α T).run (read x)
          *ᵥ uniformClock T (uniformFar P α Δ x)
        + uniformClock T (uniformFar P α Δ x))
      ≤ 16 / ((T : ℝ) ^ 2 * Δ ^ 2) := by
  have h := qNormSq_clockPhaseRefl_add_le_div_inputReflProduct
    (uniformGen (R := ↥(Set.range f)) (ι := ι) (σ := σ) (K := K))
    (uniformL P α) (isQProjector_uniformL P α) hT (read x) hΔ
    (uniformW P α x)
  rw [inputProj_mulVec_uniformW, qNormSq_realizedTMinus, mul_one] at h
  rw [uniformDetector_eq, uniformFar]
  exact h

/-- **The negative conversion bound**:
`‖e₋‖ ≤ Δ·√(1 + c/(2α²)) + 4/(TΔ)`, by one near/far triangle
inequality. -/
theorem sqrt_qNormSq_uniformMinusError_le (P : DualPairOn read K f) {c : ℝ}
    (hP : P.IsCostLe c) {α : ℝ} (hα : α ≠ 0) {T : ℕ} (hT : 0 < T) {Δ : ℝ}
    (hΔ : 0 < Δ) (x : X) :
    Real.sqrt (qNormSq (uniformMinusError P α T x))
      ≤ Δ * Real.sqrt (1 + c / (2 * α ^ 2)) + 4 / ((T : ℝ) * Δ) := by
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  -- e₋ splits along the near/far decomposition of the `−` target
  have hsplit : uniformMinusError P α T x
      = ((uniformDetector P α T).run (read x)
            *ᵥ uniformClock T (uniformNear P α Δ x)
          + uniformClock T (uniformNear P α Δ x))
        + ((uniformDetector P α T).run (read x)
            *ᵥ uniformClock T (uniformFar P α Δ x)
          + uniformClock T (uniformFar P α Δ x)) := by
    rw [show uniformMinusError P α T x
          = (uniformDetector P α T).run (read x)
              *ᵥ uniformClock T (realizedTMinus (K := K) f x)
            + uniformClock T (realizedTMinus (K := K) f x) from rfl,
      ← uniformNear_add_uniformFar P α Δ x, uniformClock_add,
      Matrix.mulVec_add]
    abel
  -- the near error: both summands are moved unit-length copies of `N`
  have hnear : Real.sqrt (qNormSq ((uniformDetector P α T).run (read x)
          *ᵥ uniformClock T (uniformNear P α Δ x)
        + uniformClock T (uniformNear P α Δ x)))
      ≤ Δ * Real.sqrt (1 + c / (2 * α ^ 2)) := by
    have htri := sqrt_qNormSq_add_le
      ((uniformDetector P α T).run (read x)
        *ᵥ uniformClock T (uniformNear P α Δ x))
      (uniformClock T (uniformNear P α Δ x))
    have hU : qNormSq ((uniformDetector P α T).run (read x)
          *ᵥ uniformClock T (uniformNear P α Δ x))
        = qNormSq (uniformClock T (uniformNear P α Δ x)) :=
      qNormSq_mulVec
        ((uniformDetector P α T).run_mem_unitaryGroup (read x)) _
    rw [hU, qNormSq_uniformClock hT] at htri
    have hN : Real.sqrt (qNormSq (uniformNear P α Δ x))
        ≤ Δ / 2 * Real.sqrt (1 + c / (2 * α ^ 2)) := by
      calc Real.sqrt (qNormSq (uniformNear P α Δ x))
          ≤ Real.sqrt (Δ ^ 2 / 4 * (1 + c / (2 * α ^ 2))) :=
            Real.sqrt_le_sqrt (qNormSq_uniformNear_le P hP hα Δ x)
        _ = Δ / 2 * Real.sqrt (1 + c / (2 * α ^ 2)) := by
            rw [show Δ ^ 2 / 4 * (1 + c / (2 * α ^ 2))
                = (Δ / 2) ^ 2 * (1 + c / (2 * α ^ 2)) from by ring,
              Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    linarith [htri, hN]
  -- the far error: the divided detector bound, square-rooted
  have hfar : Real.sqrt (qNormSq ((uniformDetector P α T).run (read x)
          *ᵥ uniformClock T (uniformFar P α Δ x)
        + uniformClock T (uniformFar P α Δ x)))
      ≤ 4 / ((T : ℝ) * Δ) := by
    calc Real.sqrt (qNormSq ((uniformDetector P α T).run (read x)
            *ᵥ uniformClock T (uniformFar P α Δ x)
          + uniformClock T (uniformFar P α Δ x)))
        ≤ Real.sqrt (16 / ((T : ℝ) ^ 2 * Δ ^ 2)) :=
          Real.sqrt_le_sqrt
            (qNormSq_uniformDetector_far_add_le P α hT hΔ x)
      _ = 4 / ((T : ℝ) * Δ) := by
          rw [show (16 : ℝ) / ((T : ℝ) ^ 2 * Δ ^ 2)
              = (4 / ((T : ℝ) * Δ)) ^ 2 from by
            rw [div_pow]; congr 1 <;> ring,
            Real.sqrt_sq (div_nonneg (by norm_num)
              (mul_nonneg hT0.le hΔ.le))]
  have htotal := sqrt_qNormSq_add_le
    ((uniformDetector P α T).run (read x)
        *ᵥ uniformClock T (uniformNear P α Δ x)
      + uniformClock T (uniformNear P α Δ x))
    ((uniformDetector P α T).run (read x)
        *ᵥ uniformClock T (uniformFar P α Δ x)
      + uniformClock T (uniformFar P α Δ x))
  rw [hsplit]
  linarith [htotal, hnear, hfar]

/-! ## The combined conversion error

The end-to-end error runs the detector on the clocked input-independent
`common` state against the clocked output-labelled target; by linearity it
is `(e₊ + e₋)/√2`.  The two signed errors are **exactly orthogonal**: the
detector is self-adjoint (a reflection conjugated by a unitary) and
unitary, so in

    ⟪e₊, e₋⟫ = ⟪Ds₊, Ds₋⟫ + ⟪Ds₊, s₋⟫ − ⟪s₊, Ds₋⟫ − ⟪s₊, s₋⟫

the outer terms cancel by unitarity and the middle terms by
self-adjointness.  The conversion error is therefore the exact half-sum
`½(‖e₊‖² + ‖e₋‖²)` — a triangle bound here would not support `8192`. -/

/-- **The detector is self-adjoint**, inherited from
`clockPhaseRefl_run_conjTranspose`. -/
theorem uniformDetector_run_conjTranspose (P : DualPairOn read K f) (α : ℝ)
    (T : ℕ) (a : ι → σ) :
    ((uniformDetector P α T).run a)ᴴ = (uniformDetector P α T).run a := by
  rw [uniformDetector_eq]
  exact clockPhaseRefl_run_conjTranspose _ T a

/-- **The two signed errors are orthogonal** — exactly, for every `T` and
`α`. -/
theorem qInner_uniformPlusError_uniformMinusError (P : DualPairOn read K f)
    (α : ℝ) (T : ℕ) (x : X) :
    qInner (uniformPlusError P α T x) (uniformMinusError P α T x) = 0 := by
  let D := (uniformDetector P α T).run (read x)
  let sp := uniformClock T (realizedTPlus (ι := ι) (σ := σ) (K := K) f x)
  let sm := uniformClock T (realizedTMinus (ι := ι) (σ := σ) (K := K) f x)
  have hD : D ∈ Matrix.unitaryGroup
      (QBasis ι σ (ClockWork ι T (UWork ↥(Set.range f) ι K))) ℂ :=
    (uniformDetector P α T).run_mem_unitaryGroup (read x)
  have hDH : Dᴴ = D := uniformDetector_run_conjTranspose P α T (read x)
  have h1 : qInner (D *ᵥ sp) (D *ᵥ sm) = qInner sp sm :=
    qInner_mulVec_mulVec hD sp sm
  have h2 : qInner (D *ᵥ sp) sm = qInner sp (D *ᵥ sm) := by
    rw [qInner_mulVec_left, hDH]
  rw [show uniformPlusError P α T x = D *ᵥ sp - sp from rfl,
    show uniformMinusError P α T x = D *ᵥ sm + sm from rfl,
    qInner_sub_left, qInner_add_right, qInner_add_right, h1, h2]
  ring

/-- **The end-to-end conversion error**: the detector applied to the clocked
input-independent common state, against the clocked output-labelled
target. -/
noncomputable def uniformConvError (P : DualPairOn read K f) (α : ℝ) (T : ℕ)
    (x : X) : QBasis ι σ (ClockWork ι T (UWork ↥(Set.range f) ι K)) → ℂ :=
  (uniformDetector P α T).run (read x)
      *ᵥ uniformClock T (realizedCommon (K := K) f)
    - uniformClock T (realizedOut (K := K) f x)

/-- **The conversion error is the scaled sum of the signed errors** — pure
linearity, no hypotheses at all. -/
theorem uniformConvError_eq (P : DualPairOn read K f) (α : ℝ) (T : ℕ)
    (x : X) :
    uniformConvError P α T x
      = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
          (uniformPlusError P α T x + uniformMinusError P α T x) := by
  rw [show uniformConvError P α T x
        = (uniformDetector P α T).run (read x)
            *ᵥ uniformClock T (realizedCommon (K := K) f)
          - uniformClock T (realizedOut (K := K) f x) from rfl,
    realizedCommon_eq_smul (K := K) f x, realizedOut_eq_smul (K := K) f x,
    uniformClock_smul, uniformClock_smul, uniformClock_add,
    uniformClock_sub, Matrix.mulVec_smul, Matrix.mulVec_add,
    show uniformPlusError P α T x
        = (uniformDetector P α T).run (read x)
            *ᵥ uniformClock T (realizedTPlus (K := K) f x)
          - uniformClock T (realizedTPlus (K := K) f x) from rfl,
    show uniformMinusError P α T x
        = (uniformDetector P α T).run (read x)
            *ᵥ uniformClock T (realizedTMinus (K := K) f x)
          + uniformClock T (realizedTMinus (K := K) f x) from rfl]
  module

/-- **The exact half-sum**: with `e₊ ⟂ e₋`,
`‖err‖² = (‖e₊‖² + ‖e₋‖²)/2` — an equality, not a triangle bound. -/
theorem qNormSq_uniformConvError (P : DualPairOn read K f) (α : ℝ) (T : ℕ)
    (x : X) :
    qNormSq (uniformConvError P α T x)
      = (qNormSq (uniformPlusError P α T x)
          + qNormSq (uniformMinusError P α T x)) / 2 := by
  rw [uniformConvError_eq, qNormSq_smul, normSq_inv_sqrt_two, qNormSq_add,
    qInner_uniformPlusError_uniformMinusError P α T x, Complex.zero_re]
  ring

/-- **The combined conversion bound** — the two component estimates through
the exact half-sum; the only statement needing all three parameter
hypotheses. -/
theorem qNormSq_uniformConvError_le (P : DualPairOn read K f) {c : ℝ}
    (hP : P.IsCostLe c) {α : ℝ} (hα : α ≠ 0) {T : ℕ} (hT : 0 < T) {Δ : ℝ}
    (hΔ : 0 < Δ) (x : X) :
    qNormSq (uniformConvError P α T x)
      ≤ (8 * α ^ 2 * c
          + (Δ * Real.sqrt (1 + c / (2 * α ^ 2)) + 4 / ((T : ℝ) * Δ)) ^ 2)
        / 2 := by
  have hplus := qNormSq_uniformPlusError_le P hP α T x
  have hminus : qNormSq (uniformMinusError P α T x)
      ≤ (Δ * Real.sqrt (1 + c / (2 * α ^ 2)) + 4 / ((T : ℝ) * Δ)) ^ 2 := by
    have h := sqrt_qNormSq_uniformMinusError_le P hP hα hT hΔ x
    have h2 := mul_self_le_mul_self (Real.sqrt_nonneg _) h
    rw [Real.mul_self_sqrt (qNormSq_nonneg _), ← pow_two] at h2
    exact h2
  rw [qNormSq_uniformConvError]
  linarith

/-! ## The parameters

With `B = 1 + c`:

    α = (√(128B))⁻¹,   Δ = (64B)⁻¹,   T = ⌈2048B⌉.

Then `8α²c = c/(16B) ≤ 1/16`; the near coefficient `1 + c/(2α²) = 1 + 64cB
≤ 64B²` so the near term is at most `Δ·8B = 1/8`; `TΔ ≥ 2048B/(64B) = 32`
so the far term is at most `1/8`; hence `‖e₋‖² ≤ 1/16` and the combined
squared conversion distance is at most `(1/16 + 1/16)/2 = 1/16` — at
`4(T − 1) ≤ 8192(1 + c)` queries — the
`uniformExtractionConstant`, attained.  Only `Δ` and `α` balance against `c`; the
budget hypothesis is just `0 ≤ c`. -/

/-- The witness scale: `α = (√(128(1+c)))⁻¹`. -/
noncomputable def uniformAlpha (c : ℝ) : ℝ :=
  (Real.sqrt (128 * (1 + c)))⁻¹

/-- The window: `Δ = (64(1+c))⁻¹`. -/
noncomputable def uniformDelta (c : ℝ) : ℝ := (64 * (1 + c))⁻¹

/-- The clock: `T = ⌈2048(1+c)⌉`. -/
noncomputable def uniformT (c : ℝ) : ℕ := ⌈(2048 : ℝ) * (1 + c)⌉₊

lemma uniformAlpha_ne_zero {c : ℝ} (hc : 0 ≤ c) : uniformAlpha c ≠ 0 := by
  rw [uniformAlpha]
  exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by linarith)))

lemma uniformAlpha_sq {c : ℝ} (hc : 0 ≤ c) :
    uniformAlpha c ^ 2 = (128 * (1 + c))⁻¹ := by
  rw [uniformAlpha, inv_pow,
    Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 128 * (1 + c))]

lemma uniformDelta_pos {c : ℝ} (hc : 0 ≤ c) : 0 < uniformDelta c := by
  rw [uniformDelta]
  exact inv_pos.mpr (by linarith)

lemma uniformT_pos {c : ℝ} (hc : 0 ≤ c) : 0 < uniformT c := by
  rw [uniformT]
  exact Nat.ceil_pos.mpr (by linarith)

/-- **The instantiated conversion bound**: at the chosen parameters the
squared conversion distance is at most `1/16`, for every promise input. -/
theorem qNormSq_uniformConvError_le_sixteenth (P : DualPairOn read K f)
    {c : ℝ} (hP : P.IsCostLe c) (hc : 0 ≤ c) (x : X) :
    qNormSq (uniformConvError P (uniformAlpha c) (uniformT c) x)
      ≤ 1 / 16 := by
  have hB0 : (0 : ℝ) < 1 + c := by linarith
  have hα := uniformAlpha_ne_zero hc
  have hαsq := uniformAlpha_sq hc
  have hT := uniformT_pos hc
  have hΔ := uniformDelta_pos hc
  have h := qNormSq_uniformConvError_le P hP hα hT hΔ x
  -- the positive budget: `8α²c = c/(16(1+c)) ≤ 1/16`
  have h1 : 8 * uniformAlpha c ^ 2 * c ≤ 1 / 16 := by
    rw [hαsq, show (8 : ℝ) * (128 * (1 + c))⁻¹ * c
          = 8 * c / (128 * (1 + c)) from by rw [div_eq_mul_inv]; ring,
      div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 16)]
    linarith
  -- the near coefficient: `1 + c/(2α²) = 1 + 64c(1+c) ≤ 64(1+c)²`
  have hval : 1 + c / (2 * uniformAlpha c ^ 2) ≤ 64 * (1 + c) ^ 2 := by
    rw [hαsq, show c / (2 * (128 * (1 + c))⁻¹) = 64 * c * (1 + c) from by
      rw [div_eq_mul_inv, mul_inv, inv_inv]; ring]
    nlinarith
  have hsqrt : Real.sqrt (1 + c / (2 * uniformAlpha c ^ 2))
      ≤ 8 * (1 + c) := by
    calc Real.sqrt (1 + c / (2 * uniformAlpha c ^ 2))
        ≤ Real.sqrt (64 * (1 + c) ^ 2) := Real.sqrt_le_sqrt hval
      _ = 8 * (1 + c) := by
          rw [show (64 : ℝ) * (1 + c) ^ 2 = (8 * (1 + c)) ^ 2 from by ring,
            Real.sqrt_sq (by positivity)]
  -- the near term: `Δ·8(1+c) = 1/8`
  have hnear : uniformDelta c
      * Real.sqrt (1 + c / (2 * uniformAlpha c ^ 2)) ≤ 1 / 8 := by
    have h8 : uniformDelta c * (8 * (1 + c)) = 1 / 8 := by
      rw [uniformDelta, mul_inv, show (64 : ℝ)⁻¹ * (1 + c)⁻¹ * (8 * (1 + c))
          = 64⁻¹ * 8 * ((1 + c)⁻¹ * (1 + c)) from by ring,
        inv_mul_cancel₀ hB0.ne', mul_one]
      norm_num
    calc uniformDelta c * Real.sqrt (1 + c / (2 * uniformAlpha c ^ 2))
        ≤ uniformDelta c * (8 * (1 + c)) :=
          mul_le_mul_of_nonneg_left hsqrt hΔ.le
      _ = 1 / 8 := h8
  -- the far term: `TΔ ≥ 32`
  have hTge : (2048 : ℝ) * (1 + c) ≤ (uniformT c : ℝ) := by
    rw [uniformT]
    exact Nat.le_ceil _
  have hTΔ : (32 : ℝ) ≤ (uniformT c : ℝ) * uniformDelta c := by
    have h32 : (2048 : ℝ) * (1 + c) * uniformDelta c = 32 := by
      rw [uniformDelta, mul_inv, show (2048 : ℝ) * (1 + c)
          * (64⁻¹ * (1 + c)⁻¹) = 2048 * 64⁻¹ * ((1 + c) * (1 + c)⁻¹) from by
        ring, mul_inv_cancel₀ hB0.ne', mul_one]
      norm_num
    calc (32 : ℝ) = 2048 * (1 + c) * uniformDelta c := h32.symm
      _ ≤ (uniformT c : ℝ) * uniformDelta c :=
          mul_le_mul_of_nonneg_right hTge hΔ.le
  have hfar : 4 / ((uniformT c : ℝ) * uniformDelta c) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 8)]
    linarith
  -- square the `e₋` budget and combine through the exact half-sum
  have hn0 : 0 ≤ uniformDelta c
      * Real.sqrt (1 + c / (2 * uniformAlpha c ^ 2)) :=
    mul_nonneg hΔ.le (Real.sqrt_nonneg _)
  have hf0 : 0 ≤ 4 / ((uniformT c : ℝ) * uniformDelta c) := by
    have : (0 : ℝ) < (uniformT c : ℝ) * uniformDelta c := by linarith
    positivity
  have hsq : (uniformDelta c * Real.sqrt (1 + c / (2 * uniformAlpha c ^ 2))
      + 4 / ((uniformT c : ℝ) * uniformDelta c)) ^ 2 ≤ 1 / 16 := by
    nlinarith [hnear, hfar, hn0, hf0]
  linarith

/-- **The detector at the chosen clock stays within the acceptance
budget**: `4(T − 1) ≤ 8192(1 + c)` — the
`uniformExtractionConstant` is attained. -/
theorem uniformDetector_len_uniformT_le (P : DualPairOn read K f) (α : ℝ)
    {c : ℝ} (hc : 0 ≤ c) :
    ((uniformDetector P α (uniformT c)).len : ℝ) ≤ 8192 * (1 + c) := by
  have hT : 0 < uniformT c := uniformT_pos hc
  have hceil : ((uniformT c : ℕ) : ℝ) < 2048 * (1 + c) + 1 := by
    rw [uniformT]
    exact Nat.ceil_lt_add_one (by linarith)
  rw [uniformDetector_len, Nat.cast_mul, Nat.cast_sub hT]
  push_cast
  linarith

end QuantumQueryComplexity
