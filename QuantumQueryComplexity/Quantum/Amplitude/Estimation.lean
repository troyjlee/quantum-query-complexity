import QuantumQueryComplexity.Quantum.Amplitude.PhaseEstimation
import Mathlib.Analysis.Real.Pi.Bounds
set_option synthInstance.maxSize 4096
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Amplitude estimation

Phase estimation applied to the **undiluted** Grover iterate of `Amplitude/Routine.lean`
(the original success predicate; the dilution of Stage I plays no role here), on the state
prepared by the supplied routine:

    aeRoutine M = (prep, in every clock branch) ; peRoutine grover M
    aeRoutine_len : S + (M − 1)·(2S + C)

with output a **finite label** `y : Fin M` and the public decoder
`aeEstimate M y = sin²(π·y/M) ∈ [0, 1]`.

`aeAlg_prob`: for every `0 ≤ p ≤ 1` (endpoints included, with no normalization of the good
and bad parts), the clock outcome law is the equal mixture of the two eigenphase laws,

    Pr[y] = ( |k(θ/π − y/M)|² + |k(−θ/π − y/M)|² ) / 2,        sin² θ = p.

It is proved from finite sums — the state equation `G^c ψ = α_c g + β_c b`, the exponential
form of `sin` and `cos`, and the parallelogram identity — with no density matrices.  The
eigenphases `±2θ` of `G = (2|ψ⟩⟨ψ| − I)(I − 2Π)` enter through `sin((2c+1)θ)`,
`cos((2c+1)θ)`; with `−G` the decoder would be wrong (`Test/AmplitudeEstimation.lean` checks
`p = 1/4`, `M = 6`).

`five_sixths_le_ae_accurate`: with probability at least `5/6`,

    |aeEstimate M y − p| ≤ 8π·√(p(1−p))/M + 16π²/M².

These are the coarse constants of the conservative concentration bound, not the sharp
`2π√(p(1−p))/M + π²/M²` at `8/π²`.  `ae_additive_five_sixths`: `M ≥ 8π/η` gives additive
error `η` (`0 < η ≤ 1`) with probability `≥ 5/6`, with no lower bound on `p`.  The
`three_quarters_le_ae_accurate` and `ae_additive` statements are kept as weakenings.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix Finset

/-! ## Exponential form of sine and cosine -/

/-- `e^{ix}`. -/
noncomputable def eI (x : ℝ) : ℂ := Complex.exp (Complex.I * (x : ℂ))

lemma eI_add (x y : ℝ) : eI (x + y) = eI x * eI y := by
  rw [eI, eI, eI, ← Complex.exp_add]; congr 1; push_cast; ring

lemma normSq_eI (x : ℝ) : Complex.normSq (eI x) = 1 := by
  rw [Complex.normSq_eq_norm_sq, eI, mul_comm, Complex.norm_exp_ofReal_mul_I, one_pow]

lemma cexp1_eq_eI (t : ℝ) : cexp1 t = eI (2 * Real.pi * t) := rfl

lemma two_I_mul_sin (x : ℝ) : 2 * Complex.I * (Real.sin x : ℂ) = eI x - eI (-x) := by
  rw [Complex.ofReal_sin, Complex.sin, eI, eI]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have e1 : Complex.I * ((-x : ℝ) : ℂ) = -(x : ℂ) * Complex.I := by push_cast; ring
  have e2 : Complex.I * (x : ℂ) = (x : ℂ) * Complex.I := by ring
  rw [e1, e2]
  linear_combination (Complex.exp (-(x : ℂ) * Complex.I) - Complex.exp ((x : ℂ) * Complex.I)) * hI

lemma two_mul_cos (x : ℝ) : 2 * (Real.cos x : ℂ) = eI x + eI (-x) := by
  rw [Complex.ofReal_cos, Complex.cos, eI, eI]
  have e1 : Complex.I * ((-x : ℝ) : ℂ) = -(x : ℂ) * Complex.I := by push_cast; ring
  have e2 : Complex.I * (x : ℂ) = (x : ℂ) * Complex.I := by ring
  rw [e1, e2]
  ring

/-- The parallelogram identity behind the mixture law. -/
lemma normSq_half_sub_add (u v a b : ℂ) (ha : 2 * Complex.I * a = u - v) (hb : 2 * b = u + v) :
    Complex.normSq a + Complex.normSq b = (Complex.normSq u + Complex.normSq v) / 2 := by
  have h1 : Complex.normSq (2 * Complex.I * a) = 4 * Complex.normSq a := by
    rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_I]
    norm_num [Complex.normSq_ofNat]
  have h2 : Complex.normSq (2 * b) = 4 * Complex.normSq b := by
    rw [Complex.normSq_mul]; norm_num [Complex.normSq_ofNat]
  rw [ha, Complex.normSq_sub] at h1
  rw [hb, Complex.normSq_add] at h2
  linarith

/-- **The two-phase kernel identity**: the sine- and cosine-weighted inverse transforms
carry, together, half the mass of each of the two eigenphase kernels `±θ/π`. -/
theorem normSq_sinSum_add_cosSum {M : ℕ} (θ : ℝ) (y : ℕ) :
    Complex.normSq ((1 / (M : ℂ)) * ∑ c ∈ range M,
        cexp1 (-((c : ℝ) * y / M)) * (Real.sin ((2 * c + 1) * θ) : ℂ))
      + Complex.normSq ((1 / (M : ℂ)) * ∑ c ∈ range M,
        cexp1 (-((c : ℝ) * y / M)) * (Real.cos ((2 * c + 1) * θ) : ℂ))
      = (Complex.normSq (peKernel M (θ / Real.pi - y / M))
          + Complex.normSq (peKernel M (-(θ / Real.pi) - y / M))) / 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hterm : ∀ (c : ℕ) (s : ℝ), eI (s * θ) * cexp1 (c * (s * θ / Real.pi - y / M))
      = cexp1 (-((c : ℝ) * y / M)) * eI (s * ((2 * c + 1) * θ)) := by
    intro c s
    rw [cexp1_eq_eI, cexp1_eq_eI, ← eI_add, ← eI_add]
    congr 1
    field_simp
    ring
  refine (normSq_half_sub_add (eI θ * peKernel M (θ / Real.pi - y / M))
    (eI (-θ) * peKernel M (-(θ / Real.pi) - y / M)) _ _ ?_ ?_).trans ?_
  · rw [peKernel, peKernel]
    simp only [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun c _ => ?_
    have h1 := hterm c 1
    have h2 := hterm c (-1)
    simp only [one_mul, neg_mul, neg_div] at h1 h2
    have hs := two_I_mul_sin ((2 * c + 1) * θ)
    linear_combination (1 / (M : ℂ)) * cexp1 (-((c : ℝ) * y / M)) * hs
      - (1 / (M : ℂ)) * h1 + (1 / (M : ℂ)) * h2
  · rw [peKernel, peKernel]
    simp only [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun c _ => ?_
    have h1 := hterm c 1
    have h2 := hterm c (-1)
    simp only [one_mul, neg_mul, neg_div] at h1 h2
    have hc := two_mul_cos ((2 * c + 1) * θ)
    linear_combination (1 / (M : ℂ)) * cexp1 (-((c : ℝ) * y / M)) * hc
      - (1 / (M : ℂ)) * h1 - (1 / (M : ℂ)) * h2
  · rw [Complex.normSq_mul, Complex.normSq_mul, normSq_eI, normSq_eI, one_mul, one_mul]

/-! ## The decoder and its accuracy -/

/-- **The public decoder**: `sin²(π·y/M)`. -/
noncomputable def aeEstimate (M : ℕ) (y : Fin M) : ℝ := Real.sin (Real.pi * (y : ℕ) / M) ^ 2

lemma aeEstimate_nonneg (M : ℕ) (y : Fin M) : 0 ≤ aeEstimate M y := sq_nonneg _

lemma aeEstimate_le_one (M : ℕ) (y : Fin M) : aeEstimate M y ≤ 1 := Real.sin_sq_le_one _

/-- `|sin²(θ+ε) − sin² θ| ≤ |sin 2θ|·|ε| + ε²`. -/
lemma abs_sin_sq_add_sub_le (θ ε : ℝ) :
    |Real.sin (θ + ε) ^ 2 - Real.sin θ ^ 2| ≤ |Real.sin (2 * θ)| * |ε| + ε ^ 2 := by
  have hid : Real.sin (θ + ε) ^ 2 - Real.sin θ ^ 2 = Real.sin (2 * θ + ε) * Real.sin ε := by
    rw [show 2 * θ + ε = (θ + ε) + θ by ring, Real.sin_add (θ + ε) θ]
    have h1 : Real.sin ε = Real.sin ((θ + ε) - θ) := by ring_nf
    rw [h1, Real.sin_sub]
    have := Real.sin_sq_add_cos_sq θ
    have := Real.sin_sq_add_cos_sq (θ + ε)
    nlinarith
  have hε : |Real.sin ε| ≤ |ε| := Real.abs_sin_le_abs
  have h2 : |Real.sin (2 * θ + ε)| ≤ |Real.sin (2 * θ)| + |Real.sin ε| := by
    rw [Real.sin_add]
    calc |Real.sin (2 * θ) * Real.cos ε + Real.cos (2 * θ) * Real.sin ε|
        ≤ |Real.sin (2 * θ) * Real.cos ε| + |Real.cos (2 * θ) * Real.sin ε| := abs_add_le _ _
      _ ≤ |Real.sin (2 * θ)| * 1 + 1 * |Real.sin ε| := by
          rw [abs_mul, abs_mul]
          gcongr
          · exact Real.abs_cos_le_one _
          · exact Real.abs_cos_le_one _
      _ = |Real.sin (2 * θ)| + |Real.sin ε| := by ring
  rw [hid, abs_mul]
  calc |Real.sin (2 * θ + ε)| * |Real.sin ε|
      ≤ (|Real.sin (2 * θ)| + |Real.sin ε|) * |Real.sin ε| :=
        mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
    _ ≤ (|Real.sin (2 * θ)| + |ε|) * |ε| := by gcongr
    _ = |Real.sin (2 * θ)| * |ε| + ε ^ 2 := by rw [add_mul, ← sq, sq_abs]

/-- **A clock outcome close to either eigenphase decodes accurately.**  Periodicity and the
sign symmetry of `sin²` are used explicitly. -/
theorem abs_aeEstimate_sub_le {M : ℕ} (hM : 0 < M) (θ : ℝ) (y : Fin M) {s : ℝ}
    (hs : s = 1 ∨ s = -1) (hclose : circDist (s * θ / Real.pi - (y : ℕ) / M) ≤ 4 / (M : ℝ)) :
    |aeEstimate M y - Real.sin θ ^ 2|
      ≤ |Real.sin (2 * θ)| * (4 * Real.pi / M) + (4 * Real.pi / M) ^ 2 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hpi := Real.pi_pos
  set δ := s * θ / Real.pi - (y : ℕ) / M with hδ
  set n := round δ with hn
  set e := Real.pi * (δ - n) with he
  have habs : |e| ≤ 4 * Real.pi / M := by
    rw [he, abs_mul, abs_of_pos hpi]
    have : |δ - n| ≤ 4 / (M : ℝ) := hclose
    calc Real.pi * |δ - n| ≤ Real.pi * (4 / M) := by gcongr
      _ = 4 * Real.pi / M := by ring
  -- `π·y/M = s·θ − e − n·π`
  have hang : Real.pi * (y : ℕ) / M = s * θ - e - n * Real.pi := by
    rw [he, hδ]; field_simp; ring
  have hsq : aeEstimate M y = Real.sin (θ + -(s * e)) ^ 2 := by
    rw [aeEstimate, hang, Real.sin_sub_int_mul_pi, mul_pow, ← zpow_natCast, ← zpow_mul,
      mul_comm (n : ℤ), zpow_mul, zpow_natCast, neg_one_sq, one_zpow, one_mul]
    rcases hs with rfl | rfl
    · congr 2; ring
    · rw [show (-1 : ℝ) * θ - e = -(θ + -(-1 * e)) by ring, Real.sin_neg, neg_sq]
  rw [hsq]
  have hse : |-(s * e)| = |e| := by
    rcases hs with rfl | rfl <;> simp
  refine (abs_sin_sq_add_sub_le θ _).trans ?_
  rw [hse, ← sq_abs (-(s * e)), hse]
  gcongr

/-! ## The algorithm -/

variable {ι σ W X O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] [Fintype X]

/-- Run `R` on the data register of every clock branch. -/
def QRoutine.liftClock (R : QRoutine ι σ W) (M : ℕ) : QRoutine ι σ (ClockWork ι M W) :=
  (R.liftReg (Fin M)).liftCtrl

@[simp] lemma QRoutine.liftClock_len (R : QRoutine ι σ W) (M : ℕ) :
    (R.liftClock M).len = R.len := rfl

lemma QRoutine.liftClock_run_uniformClock (R : QRoutine ι σ W) (M : ℕ) (a : ι → σ)
    (ψ : QBasis ι σ W → ℂ) :
    (R.liftClock M).run a *ᵥ uniformClock M ψ = uniformClock M (R.run a *ᵥ ψ) := by
  rw [uniformClock, uniformClock, clockPack, clockPack, Matrix.mulVec_smul, Matrix.mulVec_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [embedClock, QRoutine.liftClock, QRoutine.liftCtrl_run_embedCtrl,
    QRoutine.liftReg_run_embed]
  rfl

namespace AmpSetup

variable (P : AmpSetup ι σ W O)

/-- **The amplitude-estimation routine.** -/
noncomputable def aeRoutine {M : ℕ} (hM : 0 < M) : QRoutine ι σ (ClockWork ι M W) :=
  (P.prep.liftClock M).comp (peRoutine P.grover hM)

/-- **The exact query count: `S + (M − 1)·(2S + C)`.** -/
@[simp] theorem aeRoutine_len {M : ℕ} (hM : 0 < M) :
    (P.aeRoutine hM).len = P.prep.len + (M - 1) * (2 * P.prep.len + P.mark.len) := by
  rw [aeRoutine, QRoutine.comp_len, QRoutine.liftClock_len, peRoutine_len, grover_len]

/-- **The amplitude-estimation algorithm**, with the finite output label `y : Fin M`. -/
noncomputable def aeAlg {M : ℕ} (hM : 0 < M) : QAlg ι σ (Fin M) (ClockWork ι M W) :=
  (P.aeRoutine hM).toAlg (uniformClock M P.init)
    (by rw [IsQState, qNormSq_uniformClock hM]; exact P.init_isQState) clockReadout

variable {read : X → ι → σ} {Good : X → O → Prop} [∀ x, DecidablePred (Good x)]

/-- **The outcome law of amplitude estimation**: the equal mixture of the two eigenphase
laws, for every `0 ≤ p ≤ 1`. -/
theorem aeAlg_prob (hP : P.Marks read Good) (x : X) {M : ℕ} (hM : 0 < M) (y : Fin M) :
    (P.aeAlg hM).prob (read x) (P.aeRoutine hM).len y
      = (Complex.normSq (peKernel M
            (groverAngle (P.succProb read Good x) / Real.pi - (y : ℕ) / M))
          + Complex.normSq (peKernel M
            (-(groverAngle (P.succProb read Good x) / Real.pi) - (y : ℕ) / M))) / 2 := by
  set p := P.succProb read Good x with hp
  set θ := groverAngle p with hθ
  set g := goodPart P.readout (Good x) (P.prepared (read x)) with hg
  set b := badPart P.readout (Good x) (P.prepared (read x)) with hb
  have hp0 : 0 ≤ p := P.succProb_nonneg x
  have hp1 : p ≤ 1 := P.succProb_le_one x
  have hsplit := groverSplit_parts P.readout (Good x) (P.isQState_prepared (read x))
  have hng : qNormSq g = p := qNormSq_goodPart _ _ _
  have hnb : qNormSq b = 1 - p := by rw [hb, hsplit.qNormSq_bad, ← hg, hng]
  -- the powers of the Grover iterate on the prepared state
  have hpow : ∀ c : ℕ, (P.grover.run (read x)) ^ c *ᵥ P.prepared (read x)
      = ((ampA p c : ℝ) : ℂ) • g + ((ampB p c : ℝ) : ℂ) • b := by
    intro c
    rw [grover_run]
    have := hsplit.grover_pow_mulVec (hP x).1 (hP x).2 c
    rwa [hng] at this
  -- the final state, branch by branch
  have hstate : (P.aeAlg hM).state (read x) (P.aeRoutine hM).len
      = clockPack (fun y : Fin M =>
          (∑ c : Fin M, (fourierMat M)ᴴ y c * ((((Real.sqrt M : ℝ) : ℂ)⁻¹) * (ampA p c : ℝ))) • g
          + (∑ c : Fin M, (fourierMat M)ᴴ y c * ((((Real.sqrt M : ℝ) : ℂ)⁻¹) * (ampB p c : ℝ)))
            • b) := by
    rw [aeAlg, QRoutine.toAlg_state_len, aeRoutine, QRoutine.comp_run, ← Matrix.mulVec_mulVec,
      QRoutine.liftClock_run_uniformClock, peRoutine_run_uniformClock]
    congr 1
    funext y'
    rw [Finset.sum_smul, Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    have := hpow c
    rw [AmpSetup.prepared] at this
    rw [this]
    module
  rw [QAlg.prob, hstate]
  change qProb clockReadout _ y = _
  rw [qProb_clockReadout_clockPack]
  -- the squared norm of `A·g + B·b`
  set A := ∑ c : Fin M, (fourierMat M)ᴴ y c * ((((Real.sqrt M : ℝ) : ℂ)⁻¹) * (ampA p c : ℝ))
    with hA
  set B := ∑ c : Fin M, (fourierMat M)ᴴ y c * ((((Real.sqrt M : ℝ) : ℂ)⁻¹) * (ampB p c : ℝ))
    with hB
  have hnorm : qNormSq (A • g + B • b) = Complex.normSq A * p + Complex.normSq B * (1 - p) := by
    rw [qNormSq_add, qNormSq_smul, qNormSq_smul, hng, hnb, qInner_smul_left, qInner_smul_right,
      hsplit.orth]
    simp
  rw [hnorm]
  -- bring in `sin θ`, `cos θ`
  have hsin : Real.sin θ ^ 2 = p := sin_sq_groverAngle hp0 hp1
  have hcos : Real.cos θ ^ 2 = 1 - p := by rw [Real.cos_sq', hsin]
  have hs : ∀ c : ℕ, Real.sin θ * ampA p c = Real.sin ((2 * c + 1) * θ) := fun c => by
    have := sin_mul_ampA θ c; rwa [hsin] at this
  have hc : ∀ c : ℕ, Real.cos θ * ampB p c = Real.cos ((2 * c + 1) * θ) := fun c => by
    have := cos_mul_ampB θ c; rwa [hsin] at this
  have hsc : (((Real.sqrt M : ℝ) : ℂ)⁻¹) * (((Real.sqrt M : ℝ) : ℂ)⁻¹) = 1 / (M : ℂ) := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg M)]
    push_cast; rw [one_div]
  have hAs : ((Real.sin θ : ℝ) : ℂ) * A = (1 / (M : ℂ)) * ∑ c ∈ range M,
      cexp1 (-((c : ℝ) * (y : ℕ) / M)) * (Real.sin ((2 * c + 1) * θ) : ℂ) := by
    rw [hA, Finset.mul_sum, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range
      (fun c => 1 / (M : ℂ) * (cexp1 (-((c : ℝ) * (y : ℕ) / M))
        * (Real.sin ((2 * c + 1) * θ) : ℂ))) M]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [fourierMat_conjTranspose_apply, ← hs c]
    simp only [Complex.ofReal_mul, Complex.ofReal_inv]
    linear_combination (cexp1 (-(((c : ℕ) : ℝ) * (y : ℕ) / M)) * (Real.sin θ : ℂ)
      * (ampA p c : ℂ)) * hsc
  have hBc : ((Real.cos θ : ℝ) : ℂ) * B = (1 / (M : ℂ)) * ∑ c ∈ range M,
      cexp1 (-((c : ℝ) * (y : ℕ) / M)) * (Real.cos ((2 * c + 1) * θ) : ℂ) := by
    rw [hB, Finset.mul_sum, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range
      (fun c => 1 / (M : ℂ) * (cexp1 (-((c : ℝ) * (y : ℕ) / M))
        * (Real.cos ((2 * c + 1) * θ) : ℂ))) M]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [fourierMat_conjTranspose_apply, ← hc c]
    simp only [Complex.ofReal_mul, Complex.ofReal_inv]
    linear_combination (cexp1 (-(((c : ℕ) : ℝ) * (y : ℕ) / M)) * (Real.cos θ : ℂ)
      * (ampB p c : ℂ)) * hsc
  have hkey := normSq_sinSum_add_cosSum (M := M) θ (y : ℕ)
  rw [← hAs, ← hBc, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_ofReal, ← sq, ← sq, hsin, hcos] at hkey
  linarith

/-- The accuracy of the coarse bound: `8π·√(p(1−p))/M + 16π²/M²`. -/
noncomputable def aeError (M : ℕ) (p : ℝ) : ℝ :=
  8 * Real.pi * Real.sqrt (p * (1 - p)) / M + 16 * Real.pi ^ 2 / (M : ℝ) ^ 2

/-- **Amplitude estimation is accurate with probability at least `5/6`.**  Each of the two
eigenphase laws puts mass `≥ 5/6` on an event implying the accuracy event, so their equal
mixture does too (a mixture argument, not a union bound). -/
theorem five_sixths_le_ae_accurate (hP : P.Marks read Good) (x : X) {M : ℕ} (hM : 0 < M) :
    5 / 6 ≤ ∑ y : Fin M,
      if |aeEstimate M y - P.succProb read Good x| ≤ aeError M (P.succProb read Good x)
      then (P.aeAlg hM).prob (read x) (P.aeRoutine hM).len y else 0 := by
  set p := P.succProb read Good x with hp
  set θ := groverAngle p with hθ
  have hp0 : 0 ≤ p := P.succProb_nonneg x
  have hp1 : p ≤ 1 := P.succProb_le_one x
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hsin : Real.sin θ ^ 2 = p := sin_sq_groverAngle hp0 hp1
  have hsin2 : |Real.sin (2 * θ)| = 2 * Real.sqrt (p * (1 - p)) := by
    rw [hθ, sin_two_mul_groverAngle hp0 hp1, Real.sqrt_mul hp0, abs_of_nonneg (by positivity)]
    ring
  -- closeness to either eigenphase implies accuracy
  have hacc : ∀ (y : Fin M) (s : ℝ), s = 1 ∨ s = -1 →
      circDist (s * θ / Real.pi - (y : ℕ) / M) ≤ 4 / (M : ℝ) →
      |aeEstimate M y - p| ≤ aeError M p := by
    intro y s hs hclose
    have h := abs_aeEstimate_sub_le hM θ y hs hclose
    rw [hsin, hsin2] at h
    refine h.trans (le_of_eq ?_)
    rw [aeError]; field_simp; ring
  have h1 := five_sixths_le_good_mass hM (θ / Real.pi)
  have h2 := five_sixths_le_good_mass hM (-(θ / Real.pi))
  have hle : ∀ y : Fin M,
      ((if circDist (θ / Real.pi - (y : ℕ) / M) ≤ 4 / (M : ℝ)
          then Complex.normSq (peKernel M (θ / Real.pi - (y : ℕ) / M)) else 0)
        + (if circDist (-(θ / Real.pi) - (y : ℕ) / M) ≤ 4 / (M : ℝ)
          then Complex.normSq (peKernel M (-(θ / Real.pi) - (y : ℕ) / M)) else 0)) / 2
      ≤ if |aeEstimate M y - p| ≤ aeError M p
        then (P.aeAlg hM).prob (read x) (P.aeRoutine hM).len y else 0 := by
    intro y
    have hk1 := Complex.normSq_nonneg (peKernel M (θ / Real.pi - (y : ℕ) / M))
    have hk2 := Complex.normSq_nonneg (peKernel M (-(θ / Real.pi) - (y : ℕ) / M))
    by_cases hE : |aeEstimate M y - p| ≤ aeError M p
    · rw [if_pos hE, P.aeAlg_prob hP x hM y]
      split_ifs <;> linarith
    · rw [if_neg hE]
      have hn1 : ¬ circDist (θ / Real.pi - (y : ℕ) / M) ≤ 4 / (M : ℝ) := fun h =>
        hE (hacc y 1 (Or.inl rfl) (by rwa [one_mul]))
      have hn2 : ¬ circDist (-(θ / Real.pi) - (y : ℕ) / M) ≤ 4 / (M : ℝ) := fun h =>
        hE (hacc y (-1) (Or.inr rfl) (by rwa [neg_one_mul, neg_div]))
      rw [if_neg hn1, if_neg hn2]; norm_num
  have hsum := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) => hle y
  rw [← Finset.sum_div, Finset.sum_add_distrib] at hsum
  linarith

/-- The `3/4` form, kept for compatibility. -/
theorem three_quarters_le_ae_accurate (hP : P.Marks read Good) (x : X) {M : ℕ} (hM : 0 < M) :
    3 / 4 ≤ ∑ y : Fin M,
      if |aeEstimate M y - P.succProb read Good x| ≤ aeError M (P.succProb read Good x)
      then (P.aeAlg hM).prob (read x) (P.aeRoutine hM).len y else 0 :=
  le_trans (by norm_num) (P.five_sixths_le_ae_accurate hP x hM)

/-! ## Additive accuracy -/

/-- For `M ≥ 8π/η`, `0 < η ≤ 1`, the coarse error is at most `η`. -/
lemma aeError_le {M : ℕ} {p η : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (hMη : 8 * Real.pi / η ≤ M) : aeError M p ≤ η := by
  have hpi := Real.pi_pos
  have hM' : (0 : ℝ) < M := lt_of_lt_of_le (by positivity) hMη
  have hsq : Real.sqrt (p * (1 - p)) ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (p - 1 / 2)])
  have hb : 8 * Real.pi / M ≤ η := by
    rw [div_le_iff₀ hM']
    rw [div_le_iff₀ hη] at hMη
    linarith
  have h1 : 8 * Real.pi * Real.sqrt (p * (1 - p)) / M ≤ η / 2 := by
    calc 8 * Real.pi * Real.sqrt (p * (1 - p)) / M
        ≤ 8 * Real.pi * (1 / 2) / M := by gcongr
      _ = (8 * Real.pi / M) / 2 := by ring
      _ ≤ η / 2 := by linarith
  have h2 : 16 * Real.pi ^ 2 / (M : ℝ) ^ 2 ≤ η / 4 := by
    have : 16 * Real.pi ^ 2 / (M : ℝ) ^ 2 = (8 * Real.pi / M) ^ 2 / 4 := by
      field_simp; ring
    rw [this]
    have hb0 : 0 ≤ 8 * Real.pi / M := by positivity
    nlinarith
  rw [aeError]; linarith

/-- **Additive accuracy `η` with probability at least `5/6`**, for any clock size
`M ≥ 8π/η`; no lower bound on the success probability is needed. -/
theorem ae_additive_five_sixths (hP : P.Marks read Good) (x : X) {M : ℕ} (hM : 0 < M) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hMη : 8 * Real.pi / η ≤ M) :
    5 / 6 ≤ ∑ y : Fin M, if |aeEstimate M y - P.succProb read Good x| ≤ η
      then (P.aeAlg hM).prob (read x) (P.aeRoutine hM).len y else 0 := by
  refine (P.five_sixths_le_ae_accurate hP x hM).trans (Finset.sum_le_sum fun y _ => ?_)
  have hle := aeError_le (P.succProb_nonneg (read := read) (Good := Good) x)
    (P.succProb_le_one x) hη hη1 hMη
  by_cases h : |aeEstimate M y - P.succProb read Good x| ≤ aeError M (P.succProb read Good x)
  · rw [if_pos h, if_pos (h.trans hle)]
  · rw [if_neg h]
    split_ifs
    · exact QAlg.prob_nonneg _ _ _ _
    · exact le_rfl

/-- The `3/4` form, kept for compatibility. -/
theorem ae_additive (hP : P.Marks read Good) (x : X) {M : ℕ} (hM : 0 < M) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hMη : 8 * Real.pi / η ≤ M) :
    3 / 4 ≤ ∑ y : Fin M, if |aeEstimate M y - P.succProb read Good x| ≤ η
      then (P.aeAlg hM).prob (read x) (P.aeRoutine hM).len y else 0 :=
  le_trans (by norm_num) (P.ae_additive_five_sixths hP x hM hη hη1 hMη)

/-- The clock size for additive accuracy `η`: `⌈8π/η⌉`. -/
noncomputable def aeClock (η : ℝ) : ℕ := ⌈8 * Real.pi / η⌉₊

lemma aeClock_pos {η : ℝ} (hη : 0 < η) : 0 < aeClock η :=
  Nat.ceil_pos.mpr (by have := Real.pi_pos; positivity)

lemma le_aeClock (η : ℝ) : 8 * Real.pi / η ≤ aeClock η := Nat.le_ceil _

/-- **The budget for additive accuracy `η`: at most `18π·(S+C)/η`.** -/
theorem aeRoutine_len_le_real {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ((P.aeRoutine (aeClock_pos hη)).len : ℝ)
      ≤ 18 * Real.pi * ((P.prep.len : ℝ) + P.mark.len) / η := by
  have hpi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hMpos := aeClock_pos hη
  have hlen : (P.aeRoutine hMpos).len ≤ aeClock η * (2 * P.prep.len + P.mark.len) := by
    rw [aeRoutine_len]
    obtain ⟨k, hk⟩ : ∃ k, aeClock η = k + 1 := ⟨aeClock η - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]
    omega
  have hlen' : ((P.aeRoutine hMpos).len : ℝ)
      ≤ (aeClock η : ℝ) * (2 * P.prep.len + P.mark.len) := by exact_mod_cast hlen
  have hM : (aeClock η : ℝ) ≤ 9 * Real.pi / η := by
    have h := (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 8 * Real.pi / η)).le
    have h1 : (1 : ℝ) ≤ Real.pi / η := by rw [le_div_iff₀ hη]; linarith
    calc (aeClock η : ℝ) ≤ 8 * Real.pi / η + 1 := h
      _ ≤ 8 * Real.pi / η + Real.pi / η := by linarith
      _ = 9 * Real.pi / η := by ring
  have hSC : (2 * (P.prep.len : ℝ) + P.mark.len) ≤ 2 * ((P.prep.len : ℝ) + P.mark.len) := by
    have : (0 : ℝ) ≤ P.mark.len := Nat.cast_nonneg _
    linarith
  calc ((P.aeRoutine hMpos).len : ℝ)
      ≤ (aeClock η : ℝ) * (2 * P.prep.len + P.mark.len) := hlen'
    _ ≤ (9 * Real.pi / η) * (2 * ((P.prep.len : ℝ) + P.mark.len)) := by gcongr
    _ = 18 * Real.pi * ((P.prep.len : ℝ) + P.mark.len) / η := by ring

end AmpSetup

end QuantumQueryComplexity
