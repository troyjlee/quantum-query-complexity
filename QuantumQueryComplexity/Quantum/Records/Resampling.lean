import QuantumQueryComplexity.Quantum.Records.CondExp
import QuantumQueryComplexity.Quantum.Records.Resolvent

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Conditional resampling: Lemma 4.2

For a distribution `ρ` on `ι → σ`, nonnegative weights `w`, and `R > 0`, put

  `H = ∑ᵢ wᵢ Dᵢ`  (`FinDist.varOp ρ w`),    `F = (I + H/R)⁻¹`  (`resolvent R H`).

`⟨f, Hf⟩` is the weighted sum of conditional variances, and `F` is the averaging operator of
conditional resampling: stop with probability `R/(R + ∑ᵢ wᵢ)`, otherwise resample a coordinate
chosen with probability proportional to `wᵢ` from its conditional distribution, and repeat
(Cornelissen–Gilani–Zhou, Section 4.2).  We never formalize the random process.  The resolvent
form `F = (I + H/R)⁻¹` is the definition, and the infinity-norm contraction is proved directly
from the fixed-point identity `(R + ∑ᵢ wᵢ) F f = R f + ∑ᵢ wᵢ Eᵢ F f`
(`resolvent_fixed_point`), at an input maximizing the workspace norm of `F f`.

## Main results

* `FinDist.lemma_4_2` — Lemma 4.2 of the paper, with `σ`-valued coordinates in place of bits:
  `F` is Hermitian, `0 ≤ F² ≤ F ≤ I`, `F |ρ⟩ = |ρ⟩`, `‖F f‖∞ ≤ ‖f‖∞`, monotonicity (4.8),
  the commutator identity (4.9), and the energy bound (4.10), the last two parts holding
  on every finite workspace.
-/

namespace QuantumQueryComplexity

open scoped Matrix MatrixOrder ComplexOrder
open Matrix

variable {ι σ A : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype A]

namespace FinDist

variable (ρ : FinDist (ι → σ))

/-- `H = ∑ᵢ wᵢ Dᵢ`: `⟨f, Hf⟩` is the `w`-weighted sum of conditional variances. -/
noncomputable def varOp (w : ι → ℝ) : Matrix ρ.Supp ρ.Supp ℂ :=
  ∑ i, ((w i : ℝ) : ℂ) • ρ.condDiff i

variable {ρ}

theorem varOp_posSemidef {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) : (ρ.varOp w).PosSemidef := by
  unfold varOp
  exact Matrix.posSemidef_sum _ fun i _ =>
    (Matrix.nonneg_iff_posSemidef.mp (ρ.condDiff_nonneg i)).smul
      (Complex.zero_le_real.mpr (hw i))

variable (ρ)

theorem varOp_mulVec_ket (w : ι → ℝ) : ρ.varOp w *ᵥ ρ.ket = 0 := by
  unfold varOp
  rw [Matrix.sum_mulVec]
  exact Finset.sum_eq_zero fun i _ => by rw [Matrix.smul_mulVec, ρ.condDiff_mulVec_ket, smul_zero]

/-- `⟨f, Hf⟩ = ∑ᵢ wᵢ ‖Dᵢ f‖²`. -/
theorem jInner_varOp_mul (w : ι → ℝ) (f : JVec ρ.Supp A) :
    (jInner f (ρ.varOp w * f)).re = ∑ i, w i * jNormSq (ρ.condDiff i * f) := by
  rw [jInner_eq_trace, varOp, Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, ← jInner_eq_trace,
    ρ.jInner_condDiff_mul, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_re]

variable {ρ}

/-- **The fixed-point identity** `(R + ∑ᵢ wᵢ) F f = R f + ∑ᵢ wᵢ Eᵢ F f`, the resolvent form of
"stop, or resample one coordinate and continue". -/
theorem resolvent_fixed_point {R : ℝ} {w : ι → ℝ} (hR : 0 < R) (hw : ∀ i, 0 ≤ w i)
    (f : JVec ρ.Supp A) :
    (((R + ∑ i, w i : ℝ)) : ℂ) • (resolvent R (ρ.varOp w) * f)
      = (R : ℂ) • f + ∑ i, ((w i : ℝ) : ℂ) • (ρ.condExp i * (resolvent R (ρ.varOp w) * f)) := by
  have hH := varOp_posSemidef (ρ := ρ) hw
  have h0 := congrArg (· * f) (one_add_smul_mul_resolvent hR hH)
  simp only [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc] at h0
  set g := resolvent R (ρ.varOp w) * f
  -- `(1 + R⁻¹ H) g = f`
  have h1 : g + ((R⁻¹ : ℝ) : ℂ) • (ρ.varOp w * g) = f := h0
  -- `R g + H g = R f`
  have h1' : (R : ℂ) • g + ρ.varOp w * g = (R : ℂ) • f := by
    rw [← h1, smul_add, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hR.ne',
      Complex.ofReal_one, one_smul]
  -- `H g = (∑ wᵢ) g - ∑ wᵢ Eᵢ g`
  have h2 : ρ.varOp w * g
      = ((∑ i, w i : ℝ) : ℂ) • g - ∑ i, ((w i : ℝ) : ℂ) • (ρ.condExp i * g) := by
    rw [varOp, Matrix.sum_mul, Complex.ofReal_sum, Finset.sum_smul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_mul, condDiff, Matrix.sub_mul, Matrix.one_mul, smul_sub]
  rw [Complex.ofReal_add]
  linear_combination (norm := module) h1' - h2

/-- The averaging operator fixes the initial state: `F |ρ⟩ = |ρ⟩`. -/
theorem resolvent_varOp_mulVec_ket {R : ℝ} {w : ι → ℝ} (hR : 0 < R) (hw : ∀ i, 0 ≤ w i) :
    resolvent R (ρ.varOp w) *ᵥ ρ.ket = ρ.ket :=
  resolvent_mulVec_of_mulVec_eq_zero hR (varOp_posSemidef hw) (ρ.varOp_mulVec_ket w)

/-! ### Helpers for the infinity-norm contraction -/

private lemma wvec_add' (f g : JVec ρ.Supp A) (x : ρ.Supp) :
    ρ.wvec (f + g) x = ρ.wvec f x + ρ.wvec g x := by
  funext a
  simp [wvec, mul_add]

private lemma wvec_smul' (c : ℂ) (f : JVec ρ.Supp A) (x : ρ.Supp) :
    ρ.wvec (c • f) x = c • ρ.wvec f x := by
  funext a
  simp only [wvec, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private lemma wvec_sum' {β : Type*} (s : Finset β) (f : β → JVec ρ.Supp A) (x : ρ.Supp) :
    ρ.wvec (∑ i ∈ s, f i) x = ∑ i ∈ s, ρ.wvec (f i) x := by
  funext a
  simp [wvec, Finset.mul_sum, Matrix.sum_apply]

/-- The triangle inequality for finite sums, in squared-norm form. -/
private lemma sqrt_qNormSq_sum_le {β : Type*} (s : Finset β) (v : β → A → ℂ) :
    √(qNormSq (∑ i ∈ s, v i)) ≤ ∑ i ∈ s, √(qNormSq (v i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb]
    exact (sqrt_qNormSq_add_le _ _).trans (by linarith)

private lemma sqrt_qNormSq_ofReal_smul {r : ℝ} (hr : 0 ≤ r) (v : A → ℂ) :
    √(qNormSq ((r : ℂ) • v)) = r * √(qNormSq v) := by
  classical
  rw [qNormSq_smul, Complex.normSq_ofReal, Real.sqrt_mul (mul_self_nonneg r),
    Real.sqrt_mul_self hr]

/-- **Infinity-norm contraction** `‖F f‖∞ ≤ ‖f‖∞`, on every finite workspace. -/
theorem infNormSq_resolvent_mul_le {R : ℝ} {w : ι → ℝ} (hR : 0 < R) (hw : ∀ i, 0 ≤ w i)
    (f : JVec ρ.Supp A) :
    ρ.infNormSq (resolvent R (ρ.varOp w) * f) ≤ ρ.infNormSq f := by
  classical
  have hfp := resolvent_fixed_point (ρ := ρ) hR hw f
  set g := resolvent R (ρ.varOp w) * f
  set a := ∑ i, w i with ha
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun i _ => hw i
  -- the fixed-point identity, read off at each input
  have hpt : ∀ x, ((R + a : ℝ) : ℂ) • ρ.wvec g x = (R : ℂ) • ρ.wvec f x
      + ∑ i, ((w i : ℝ) : ℂ) • ∑ y, (ρ.condWeight i x y : ℂ) • ρ.wvec g y := by
    intro x
    have := congrArg (fun u => ρ.wvec u x) hfp
    simpa only [wvec_smul', wvec_add', wvec_sum', wvec_condExp_mul] using this
  -- an input maximizing the workspace norm of `g = F f`
  obtain ⟨x₀, hx₀⟩ := Finite.exists_max (fun x => qNormSq (ρ.wvec g x))
  set M := √(qNormSq (ρ.wvec g x₀))
  set K := √(ρ.infNormSq f)
  have hM : ∀ y, √(qNormSq (ρ.wvec g y)) ≤ M := fun y => Real.sqrt_le_sqrt (hx₀ y)
  have hK : √(qNormSq (ρ.wvec f x₀)) ≤ K :=
    Real.sqrt_le_sqrt (ρ.qNormSq_wvec_le_infNormSq f x₀)
  have key : (R + a) * M ≤ R * K + a * M := by
    rw [← sqrt_qNormSq_ofReal_smul (by linarith) (ρ.wvec g x₀), hpt x₀]
    refine (sqrt_qNormSq_add_le _ _).trans ?_
    gcongr
    · rw [sqrt_qNormSq_ofReal_smul hR.le]
      gcongr
    · refine (sqrt_qNormSq_sum_le _ _).trans ?_
      rw [ha, Finset.sum_mul]
      gcongr with i
      rw [sqrt_qNormSq_ofReal_smul (hw i)]
      gcongr
      · exact hw i
      refine (sqrt_qNormSq_sum_le _ _).trans ?_
      calc ∑ y, √(qNormSq ((ρ.condWeight i x₀ y : ℂ) • ρ.wvec g y))
          = ∑ y, ρ.condWeight i x₀ y * √(qNormSq (ρ.wvec g y)) :=
            Finset.sum_congr rfl fun y _ =>
              sqrt_qNormSq_ofReal_smul (ρ.condWeight_nonneg i x₀ y) _
        _ ≤ ∑ y, ρ.condWeight i x₀ y * M := by
            gcongr with y
            · exact ρ.condWeight_nonneg i x₀ y
            · exact hM y
        _ = M := by rw [← Finset.sum_mul, ρ.sum_condWeight, one_mul]
  have hMK : M ≤ K := by nlinarith
  apply infNormSq_le
  intro x
  calc qNormSq (ρ.wvec g x) ≤ qNormSq (ρ.wvec g x₀) := hx₀ x
    _ = M ^ 2 := (Real.sq_sqrt (qNormSq_nonneg _)).symm
    _ ≤ K ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hMK 2
    _ = ρ.infNormSq f := Real.sq_sqrt (ρ.infNormSq_nonneg f)

/-- **Hilbert-norm contraction** `‖F f‖ ≤ ‖f‖`, on every finite workspace. -/
theorem jNormSq_resolvent_mul_le {R : ℝ} {w : ι → ℝ} (hR : 0 < R) (hw : ∀ i, 0 ≤ w i)
    (f : JVec ρ.Supp A) :
    jNormSq (resolvent R (ρ.varOp w) * f) ≤ jNormSq f := by
  have hH := varOp_posSemidef (ρ := ρ) hw
  have h : (resolvent R (ρ.varOp w))ᴴ * resolvent R (ρ.varOp w)
      ≤ ((1 : ℝ) : ℂ) • (1 : Matrix ρ.Supp ρ.Supp ℂ) := by
    rw [(resolvent_isHermitian hR hH).eq, Complex.ofReal_one, one_smul]
    exact (resolvent_sq_le hR hH).trans (resolvent_le_one hR hH)
  simpa using jNormSq_mul_le_smul h f

/-- **The energy bound** `⟨F f, H F f⟩ ≤ (R/4) ‖f‖²`, on every finite workspace. -/
theorem jInner_resolvent_varOp_le {R : ℝ} {w : ι → ℝ} (hR : 0 < R) (hw : ∀ i, 0 ≤ w i)
    (f : JVec ρ.Supp A) :
    (jInner (resolvent R (ρ.varOp w) * f)
        (ρ.varOp w * (resolvent R (ρ.varOp w) * f))).re ≤ R / 4 * jNormSq f := by
  have hH := varOp_posSemidef (ρ := ρ) hw
  have hFh := (resolvent_isHermitian hR hH).eq
  set F := resolvent R (ρ.varOp w)
  have h1 : jInner (F * f) (ρ.varOp w * (F * f)) = jInner f (F * ρ.varOp w * F * f) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, jInner_mul_right F f, hFh]
  have h2 : jInner f ((((R / 4 : ℝ)) : ℂ) • (1 : Matrix ρ.Supp ρ.Supp ℂ) * f)
      = (((R / 4 * jNormSq f : ℝ)) : ℂ) := by
    rw [Matrix.smul_mul, Matrix.one_mul, jInner_eq_trace, Matrix.mul_smul, Matrix.trace_smul,
      ← jInner_eq_trace, jInner_self, smul_eq_mul, Complex.ofReal_mul]
  rw [h1]
  have := jInner_le_of_le (resolvent_mul_mul_resolvent_le hR hH) f
  rwa [h2, Complex.ofReal_re] at this

/-- **Lemma 4.2 (properties of conditional resampling).**  For a distribution `ρ` on `ι → σ`,
nonnegative weights `w`, and `R > 0`, the averaging operator `F = (I + H/R)⁻¹` with
`H = ∑ᵢ wᵢ Dᵢ` satisfies:

1. `F` is Hermitian and `0 ≤ F² ≤ F ≤ I`;
2. `F |ρ⟩ = |ρ⟩`;
3. `‖F f‖∞ ≤ ‖f‖∞` for joint vectors on every finite workspace;
4. if `H ≤ H'` and `F' = (I + H'/R)⁻¹`, then `0 ≤ F'² ≤ F' ≤ F`;
5. `[B, F] = R⁻¹ F [H, B] F` for every input-register operator `B`;
6. `⟨F f, H F f⟩ ≤ (R/4) ‖f‖²` for joint vectors on every finite workspace.

All infinity norms use `ρ`. -/
theorem lemma_4_2 {R : ℝ} {w : ι → ℝ} (hR : 0 < R) (hw : ∀ i, 0 ≤ w i) :
    (resolvent R (ρ.varOp w)).IsHermitian ∧
    0 ≤ resolvent R (ρ.varOp w) * resolvent R (ρ.varOp w) ∧
    resolvent R (ρ.varOp w) * resolvent R (ρ.varOp w) ≤ resolvent R (ρ.varOp w) ∧
    resolvent R (ρ.varOp w) ≤ 1 ∧
    resolvent R (ρ.varOp w) *ᵥ ρ.ket = ρ.ket ∧
    (∀ (A : Type) [Fintype A] (f : JVec ρ.Supp A),
      ρ.infNormSq (resolvent R (ρ.varOp w) * f) ≤ ρ.infNormSq f) ∧
    (∀ H' : Matrix ρ.Supp ρ.Supp ℂ, ρ.varOp w ≤ H' →
      0 ≤ resolvent R H' * resolvent R H' ∧
      resolvent R H' * resolvent R H' ≤ resolvent R H' ∧
      resolvent R H' ≤ resolvent R (ρ.varOp w)) ∧
    (∀ B : Matrix ρ.Supp ρ.Supp ℂ,
      B * resolvent R (ρ.varOp w) - resolvent R (ρ.varOp w) * B
        = ((R⁻¹ : ℝ) : ℂ) • (resolvent R (ρ.varOp w) * (ρ.varOp w * B - B * ρ.varOp w)
            * resolvent R (ρ.varOp w))) ∧
    (∀ (A : Type) [Fintype A] (f : JVec ρ.Supp A),
      (jInner (resolvent R (ρ.varOp w) * f)
          (ρ.varOp w * (resolvent R (ρ.varOp w) * f))).re ≤ R / 4 * jNormSq f) := by
  have hH := varOp_posSemidef (ρ := ρ) hw
  refine ⟨resolvent_isHermitian hR hH, resolvent_sq_nonneg hR hH, resolvent_sq_le hR hH,
    resolvent_le_one hR hH, resolvent_varOp_mulVec_ket hR hw,
    fun _ _ f => infNormSq_resolvent_mul_le hR hw f, fun H' hHH' => ?_,
    fun B => commutator_resolvent hR hH B, fun _ _ f => jInner_resolvent_varOp_le hR hw f⟩
  have hH' : H'.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp ((Matrix.nonneg_iff_posSemidef.mpr hH).trans hHH')
  exact ⟨resolvent_sq_nonneg hR hH', resolvent_sq_le hR hH', resolvent_le_resolvent hR hH hHH'⟩

end FinDist

end QuantumQueryComplexity
