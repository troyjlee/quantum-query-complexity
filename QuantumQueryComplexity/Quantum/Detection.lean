import QuantumQueryComplexity.Quantum.Witness
import QuantumQueryComplexity.Quantum.Fidelity
set_option synthInstance.maxSize 800

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The detector on the witness states: the two acceptance estimates

The last quantitative step of the state-conversion construction.
`Witness.lean` built the witness states from a `DualPairOn` and discharged the
exact contracts; this file adds the *estimates* and combines them with the
fidelity bounds of `Fidelity.lean` into the two numbers the eventual
measurement reads: for the detector `D = scDetector` at clock length `T` and
the initial state `u = uniformClock T scTarget`,

* **`f x = o`** (`le_re_qInner_scDetector_of_eq`):
  `Re⟪u, D_x u⟫ ≥ 2/(1 + (|σ|−1)cu) − 1`, from the exact fixed point
  `posWitness x`, its overlap `⟪τ, φₓ⟫ = 1`, and its norm
  `‖φₓ‖² ≤ 1 + (|σ|−1)cu`;
* **`f y ≠ o`** (`re_qInner_scDetector_le_of_ne`):
  `Re⟪u, D_y u⟫ ≤ (Δ/2)√(1+cv) + 4/(TΔ) − (1 − (Δ²/4)(1+cv))`, from the
  effective gap applied to `negWitness y` (whose input projection is exactly
  `τ`) and the uniform-clock suppression on the far window.

With `Δ ~ 1/√(1+cv)` and `T ~ 1/Δ ~ √(1+cv)` the second bound is `≈ −1` while the
first is `≈ +1` for small `(|σ|−1)cu` — the separation a Hadamard test turns
into a bounded-error measurement.  Choosing those parameters, and the dual
rescaling `DualPairOn.scale` that balances `cu` against `cv`, is the algorithm
extraction's job; this file keeps every bound parametric.

The clock geometry those estimates ride on — the isometry
`qInner_uniformClock`, additivity `uniformClock_add`, and their companions —
now lives in `Clock.lean`, where it belongs: it is generic, and the uniform
extraction of Milestone D needs it without importing this Boolean detection
layer.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix



/-! ## Rescaling a dual pair -/

namespace DualPairOn

variable {ι σ X O K : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [DecidableEq σ] [Fintype X] [DecidableEq X] [DecidableEq O] [Fintype K]
  [DecidableEq K] {read : X → ι → σ} {f : X → O}

/-- **Rescaling a dual pair**: `u ↦ αu`, `v ↦ α⁻¹v`.  Feasibility is
scale-invariant, and the two sides' masses trade against each other — the
balancing device of the algorithm extraction. -/
noncomputable def scale (P : DualPairOn read K f) {α : ℝ} (hα : α ≠ 0) :
    DualPairOn read K f where
  u x i k := α * P.u x i k
  v y i k := α⁻¹ * P.v y i k
  constraint x y := by
    rw [← P.constraint x y]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : read x i = read y i
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show α * P.u x i k * (α⁻¹ * P.v y i k)
          = (α * α⁻¹) * (P.u x i k * P.v y i k) from by ring,
        mul_inv_cancel₀ hα, one_mul]

@[simp] lemma scale_u (P : DualPairOn read K f) {α : ℝ} (hα : α ≠ 0)
    (x : X) (i : ι) (k : K) : (P.scale hα).u x i k = α * P.u x i k := rfl

@[simp] lemma scale_v (P : DualPairOn read K f) {α : ℝ} (hα : α ≠ 0)
    (y : X) (i : ι) (k : K) : (P.scale hα).v y i k = α⁻¹ * P.v y i k := rfl

/-- The `u`-mass scales by `α²`. -/
lemma scale_u_mass (P : DualPairOn read K f) {α : ℝ} (hα : α ≠ 0) (x : X) :
    ∑ i, ∑ k, (P.scale hα).u x i k * (P.scale hα).u x i k
      = α ^ 2 * ∑ i, ∑ k, P.u x i k * P.u x i k := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [scale_u]; ring

/-- The `v`-mass scales by `α⁻²`. -/
lemma scale_v_mass (P : DualPairOn read K f) {α : ℝ} (hα : α ≠ 0) (y : X) :
    ∑ i, ∑ k, (P.scale hα).v y i k * (P.scale hα).v y i k
      = (α⁻¹) ^ 2 * ∑ i, ∑ k, P.v y i k * P.v y i k := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [scale_v]; ring

end DualPairOn

/-! ## The witness norms, bounded -/

variable {ι σ X O K : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [DecidableEq σ] [Fintype X] [DecidableEq X] [DecidableEq O] [Fintype K]
  [DecidableEq K]

variable (read : X → ι → σ) (f : X → O)

@[simp] lemma qNormSq_scTarget :
    qNormSq (scTarget : QBasis ι σ (Option K) → ℂ) = 1 := by
  rw [scTarget, qNormSq_scState]
  simp

/-- The positive witness is at least a unit vector. -/
theorem one_le_qNormSq_posWitness (P : DualPairOn read K f) (x : X) :
    1 ≤ qNormSq (posWitness read f P x) := by
  rw [qNormSq_posWitness]
  have h : 0 ≤ ∑ i : ι, ∑ s : σ, (if s = read x i then 0
      else ∑ k : K, P.u x i k * P.u x i k) := by
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun s _ => ?_
    by_cases hs : s = read x i
    · rw [if_pos hs]
    · rw [if_neg hs]
      exact Finset.sum_nonneg fun k _ => mul_self_nonneg _
  linarith

/-- **The positive witness is short**: `‖φₓ‖² ≤ 1 + (|σ|−1)·cu` when the
dual's `u`-mass at `x` is at most `cu`.  The `|σ|−1` is the price of spreading
`u x` over every false letter; it is `1` for a Boolean alphabet. -/
theorem qNormSq_posWitness_le [Nonempty σ] {cu : ℝ} (P : DualPairOn read K f)
    (x : X) (hcu : ∑ i, ∑ k, P.u x i k * P.u x i k ≤ cu) :
    qNormSq (posWitness read f P x)
      ≤ 1 + ((Fintype.card σ : ℝ) - 1) * cu := by
  rw [qNormSq_posWitness]
  have hrow : ∀ i : ι, (∑ s : σ, if s = read x i then 0
        else ∑ k : K, P.u x i k * P.u x i k)
      = ((Fintype.card σ : ℝ) - 1) * ∑ k : K, P.u x i k * P.u x i k := by
    intro i
    have h1 : ∀ s : σ, (if s = read x i then (0 : ℝ)
          else ∑ k : K, P.u x i k * P.u x i k)
        = (∑ k : K, P.u x i k * P.u x i k)
          - (if s = read x i then ∑ k : K, P.u x i k * P.u x i k else 0) := by
      intro s
      by_cases hs : s = read x i <;> simp [hs]
    rw [Finset.sum_congr rfl fun s _ => h1 s, Finset.sum_sub_distrib,
      Finset.sum_const,
      Finset.sum_ite_eq' Finset.univ (read x i)
        (fun _ => ∑ k : K, P.u x i k * P.u x i k),
      if_pos (Finset.mem_univ _), Finset.card_univ, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun i _ => hrow i, ← Finset.mul_sum]
  have hσ : (0 : ℝ) ≤ (Fintype.card σ : ℝ) - 1 := by
    have h1 : 1 ≤ Fintype.card σ := Fintype.card_pos_iff.mpr ‹Nonempty σ›
    have h2 : (1 : ℝ) ≤ (Fintype.card σ : ℝ) := by exact_mod_cast h1
    linarith
  have := mul_le_mul_of_nonneg_left hcu hσ
  linarith

/-! ## The detector -/

/-- **The detector for output `o`**: the uniform-clock phase detector of the
reflection product built from the witness construction's generators and the
span of the positive witnesses of `f⁻¹(o)`.  Cost: `4(T−1)` queries. -/
noncomputable def scDetector (P : DualPairOn read K f) (o : O) (T : ℕ) :
    QRoutine ι σ (ClockWork ι T (Option K)) :=
  clockPhaseRefl (inputReflProduct scGen (scKer read f P o)
    (isQProjector_scKer read f P o)) T

lemma scDetector_eq (P : DualPairOn read K f) (o : O) (T : ℕ) :
    scDetector read f P o T
      = clockPhaseRefl (inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)) T := rfl

@[simp] theorem scDetector_len (P : DualPairOn read K f) (o : O) (T : ℕ) :
    (scDetector read f P o T).len = 4 * (T - 1) :=
  clockPhaseRefl_len_inputReflProduct _ _ _ T

/-! ## The negative input, prepared

For `f y ≠ o` the fixed subspace annihilates `negWitness y`, whose input
projection is exactly the target.  So the effective gap bounds the near part
*of the target itself*, and the detector's far-window guarantee applies to the
rest — with `‖·‖² = 1` on the right of both. -/

/-- **The near part of the target is small** on a negative input:
`‖N_Δ τ‖² ≤ (Δ²/4)(1 + cv)`. -/
theorem qNormSq_chordNear_scTarget_le (P : DualPairOn read K f) {o : O}
    {y : X} (hy : f y ≠ o) {cv : ℝ}
    (hcv : ∑ i, ∑ k, P.v y i k * P.v y i k ≤ cv) (Δ : ℝ) :
    qNormSq (chordNearProj
        ((inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget)
      ≤ Δ ^ 2 / 4 * (1 + cv) := by
  have h := effective_chord_gap_sq_inputReflProduct scGen (scKer read f P o)
    (isQProjector_scKer read f P o) (read y)
    (scKer_mulVec_negWitness read f P hy) Δ
  rw [inputProj_mulVec_negWitness] at h
  have hwn : qNormSq (negWitness read f P y) ≤ 1 + cv := by
    rw [qNormSq_negWitness]; linarith
  calc qNormSq (chordNearProj _ Δ *ᵥ scTarget)
      ≤ Δ ^ 2 / 4 * qNormSq (negWitness read f P y) := h
    _ ≤ Δ ^ 2 / 4 * (1 + cv) :=
        mul_le_mul_of_nonneg_left hwn (by positivity)

/-- **The detector reads `−1` on the target's far part**, up to `16/(T²Δ²)`.
(The bound holds for every input; only its use is specific to `f y ≠ o`.) -/
theorem qNormSq_scDetector_far_add_le (P : DualPairOn read K f) (o : O)
    (y : X) {T : ℕ} (hT : 0 < T) {Δ : ℝ} (hΔ : 0 < Δ) :
    qNormSq ((scDetector read f P o T).run (read y)
        *ᵥ uniformClock T (chordFarProj
            ((inputReflProduct scGen (scKer read f P o)
              (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget)
      + uniformClock T (chordFarProj
          ((inputReflProduct scGen (scKer read f P o)
            (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget))
      ≤ 16 / ((T : ℝ) ^ 2 * Δ ^ 2) := by
  have h := qNormSq_clockPhaseRefl_add_le_div_inputReflProduct scGen
    (scKer read f P o) (isQProjector_scKer read f P o) hT (read y) hΔ
    (negWitness read f P y)
  rw [inputProj_mulVec_negWitness, qNormSq_scTarget, mul_one] at h
  rw [scDetector_eq]
  exact h

/-! ## The two acceptance estimates -/

/-- **The detector accepts a positive input**: for `f x = o`,
`Re⟪u, D u⟫ ≥ 2/(1 + (|σ|−1)cu) − 1` on `u = uniformClock T scTarget`. -/
theorem le_re_qInner_scDetector_of_eq [Nonempty σ] (P : DualPairOn read K f)
    {o : O} {x : X} (hx : f x = o) {T : ℕ} (hT : 0 < T) {cu : ℝ}
    (hcu : ∑ i, ∑ k, P.u x i k * P.u x i k ≤ cu) :
    2 / (1 + ((Fintype.card σ : ℝ) - 1) * cu) - 1
      ≤ (qInner (uniformClock T (scTarget : QBasis ι σ (Option K) → ℂ))
          ((scDetector read f P o T).run (read x)
            *ᵥ uniformClock T scTarget)).re := by
  have hUnit := (scDetector read f P o T).run_mem_unitaryGroup (read x)
  have hfix : (scDetector read f P o T).run (read x)
      *ᵥ uniformClock T (posWitness read f P x)
      = uniformClock T (posWitness read f P x) := by
    rw [scDetector_eq]
    exact (isPosWitness_posWitness read f P hx).clockPhaseRefl_run_mulVec_uniformClock
      (isQProjector_scKer read f P o) hT
  have hkey := le_mul_re_qInner_mulVec_of_fixed hUnit hfix
    (uniformClock T (scTarget : QBasis ι σ (Option K) → ℂ))
  -- the three scalar inputs
  have hb : qInner (uniformClock T (posWitness read f P x))
      (uniformClock T (scTarget : QBasis ι σ (Option K) → ℂ)) = 1 := by
    rw [qInner_uniformClock hT]
    have h := congrArg star (qInner_scTarget_posWitness read f P x)
    rwa [qInner_conj, star_one] at h
  have hτn : qNormSq (uniformClock T (scTarget : QBasis ι σ (Option K) → ℂ))
      = 1 := by
    rw [qNormSq_uniformClock hT, qNormSq_scTarget]
  rw [hb, hτn, Complex.normSq_one] at hkey
  -- hkey : 2·1·N − N²·1 ≤ N²·Re, with N the witness norm
  set N : ℝ := qNormSq (uniformClock T (posWitness read f P x)) with hN
  set Re : ℝ := (qInner (uniformClock T (scTarget : QBasis ι σ (Option K) → ℂ))
      ((scDetector read f P o T).run (read x)
        *ᵥ uniformClock T scTarget)).re with hRe
  have hN1 : 1 ≤ N := by
    rw [hN, qNormSq_uniformClock hT]
    exact one_le_qNormSq_posWitness read f P x
  have hNM : N ≤ 1 + ((Fintype.card σ : ℝ) - 1) * cu := by
    rw [hN, qNormSq_uniformClock hT]
    exact qNormSq_posWitness_le read f P x hcu
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN1
  have hM0 : (0 : ℝ) < 1 + ((Fintype.card σ : ℝ) - 1) * cu :=
    lt_of_lt_of_le one_pos (hN1.trans hNM)
  have hkey' : 2 * N - N ^ 2 ≤ N ^ 2 * Re := by
    calc 2 * N - N ^ 2 = 2 * 1 * N - N ^ 2 * 1 := by ring
      _ ≤ N ^ 2 * Re := hkey
  -- divide out one `N`, then trade `N` for its upper bound
  have hstep1 : 2 ≤ N * Re + N := by
    have hh : N * (2 - N) ≤ N * (N * Re) := by
      calc N * (2 - N) = 2 * N - N ^ 2 := by ring
        _ ≤ N ^ 2 * Re := hkey'
        _ = N * (N * Re) := by ring
    have := le_of_mul_le_mul_left hh hN0
    linarith
  have hRe1 : (0 : ℝ) ≤ Re + 1 := by
    by_contra hneg
    have hneg' : Re + 1 < 0 := lt_of_not_ge hneg
    nlinarith [hstep1, hN0]
  have hstep2 : 2 ≤ (1 + ((Fintype.card σ : ℝ) - 1) * cu) * Re
      + (1 + ((Fintype.card σ : ℝ) - 1) * cu) := by
    nlinarith [hstep1, mul_nonneg (sub_nonneg.mpr hNM) hRe1]
  rw [sub_le_iff_le_add, div_le_iff₀ hM0]
  linarith [hstep2]

/-- **The detector rejects a negative input**: for `f y ≠ o`,
`Re⟪u, D u⟫ ≤ (Δ/2)√(1+cv) + 4/(TΔ) − (1 − (Δ²/4)(1+cv))` on
`u = uniformClock T scTarget`. -/
theorem re_qInner_scDetector_le_of_ne (P : DualPairOn read K f) {o : O}
    {y : X} (hy : f y ≠ o) {T : ℕ} (hT : 0 < T) {Δ : ℝ} (hΔ : 0 < Δ)
    {cv : ℝ} (hcv : ∑ i, ∑ k, P.v y i k * P.v y i k ≤ cv) :
    (qInner (uniformClock T (scTarget : QBasis ι σ (Option K) → ℂ))
        ((scDetector read f P o T).run (read y)
          *ᵥ uniformClock T scTarget)).re
      ≤ Δ / 2 * Real.sqrt (1 + cv) + 4 / ((T : ℝ) * Δ)
        - (1 - Δ ^ 2 / 4 * (1 + cv)) := by
  have hcv0 : (0 : ℝ) ≤ cv :=
    le_trans (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun k _ => mul_self_nonneg _) hcv
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  -- the near/far split of the target
  have hsum : chordNearProj
        ((inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)).run (read y)) Δ
          *ᵥ (scTarget : QBasis ι σ (Option K) → ℂ)
      + chordFarProj
        ((inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget
      = scTarget := by
    rw [← Matrix.add_mulVec, chordNearProj_add_chordFarProj, Matrix.one_mulVec]
  have horth : qInner
      (uniformClock T (chordNearProj
        ((inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget))
      (uniformClock T (chordFarProj
        ((inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget)) = 0 := by
    rw [qInner_uniformClock hT, chordFarProj]
    exact qInner_mulVec_one_sub_mulVec (isQProjector_chordNearProj _ Δ) _
  have hUnit := (scDetector read f P o T).run_mem_unitaryGroup (read y)
  have hkey := re_qInner_mulVec_le_of_perp hUnit horth
  rw [← uniformClock_add, hsum] at hkey
  -- the norms
  have hu1 : qNormSq (uniformClock T (scTarget : QBasis ι σ (Option K) → ℂ))
      = 1 := by rw [qNormSq_uniformClock hT, qNormSq_scTarget]
  rw [hu1, Real.sqrt_one, one_mul, one_mul] at hkey
  have hnear := qNormSq_chordNear_scTarget_le read f P hy hcv Δ
  have hN' : Real.sqrt (qNormSq (uniformClock T (chordNearProj
        ((inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget)))
      ≤ Δ / 2 * Real.sqrt (1 + cv) := by
    rw [qNormSq_uniformClock hT]
    calc Real.sqrt (qNormSq (chordNearProj _ Δ *ᵥ scTarget))
        ≤ Real.sqrt (Δ ^ 2 / 4 * (1 + cv)) := Real.sqrt_le_sqrt hnear
      _ = Δ / 2 * Real.sqrt (1 + cv) := by
          rw [show Δ ^ 2 / 4 * (1 + cv) = (Δ / 2) ^ 2 * (1 + cv) from by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have herr := qNormSq_scDetector_far_add_le read f P o y hT hΔ
  have hE' : Real.sqrt (qNormSq ((scDetector read f P o T).run (read y)
        *ᵥ uniformClock T (chordFarProj
            ((inputReflProduct scGen (scKer read f P o)
              (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget)
      + uniformClock T (chordFarProj
          ((inputReflProduct scGen (scKer read f P o)
            (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget)))
      ≤ 4 / ((T : ℝ) * Δ) := by
    calc Real.sqrt (qNormSq _) ≤ Real.sqrt (16 / ((T : ℝ) ^ 2 * Δ ^ 2)) :=
        Real.sqrt_le_sqrt herr
      _ = 4 / ((T : ℝ) * Δ) := by
          rw [show (16 : ℝ) / ((T : ℝ) ^ 2 * Δ ^ 2)
              = (4 / ((T : ℝ) * Δ)) ^ 2 from by
            rw [div_pow]; congr 1 <;> ring,
            Real.sqrt_sq (div_nonneg (by norm_num)
              (mul_nonneg hT0.le hΔ.le))]
  have hdec : qNormSq (chordNearProj
        ((inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget)
      + qNormSq (chordFarProj
        ((inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget)
      = 1 := by
    have h := qNormSq_chord_decomp
      ((inputReflProduct scGen (scKer read f P o)
        (isQProjector_scKer read f P o)).run (read y)) Δ
      (scTarget : QBasis ι σ (Option K) → ℂ)
    rw [qNormSq_scTarget] at h
    linarith
  have hF' : -(qNormSq (uniformClock T (chordFarProj
        ((inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget)))
      ≤ -(1 - Δ ^ 2 / 4 * (1 + cv)) := by
    rw [qNormSq_uniformClock hT]
    linarith [hdec, hnear]
  have hNn : (0 : ℝ) ≤ Real.sqrt (qNormSq (uniformClock T (chordNearProj
        ((inputReflProduct scGen (scKer read f P o)
          (isQProjector_scKer read f P o)).run (read y)) Δ *ᵥ scTarget))) :=
    Real.sqrt_nonneg _
  linarith [hkey, hN', hE', hF']

end QuantumQueryComplexity
