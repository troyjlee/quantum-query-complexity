import QuantumQueryComplexity.Quantum.Approximation
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# One amplification step with an approximate reflection

Everything here is **intrinsic to the actual state** `ψ`: no ideal two-dimensional plane, no
angle, no comparison with an exact algorithm.  Let `M` be a `β`-approximate reflection about
the unit vector `ψ` (in the recursion `M = A R̃ A†` and `ψ = A s`, by `IsApproxRefl.conj`), let
`m = ‖Π ψ‖²` be the marked mass, and let `ψ' = M (S ψ)` with `S ψ` the phase-flipped state.

* `stateRefl_phaseFlip` — the exact step: `(2|ψ⟩⟨ψ| − 1) S ψ = (3 − 4m)·Πψ + (1 − 4m)·(1−Π)ψ`,
  the division-free geometry again;
* `qNormSq_phaseFlip_orth` — the component of `S ψ` orthogonal to `ψ` has squared norm
  `4m(1−m)`: **the error of the step is proportional to `√m`**, because `ψ` itself is fixed;
* `abs_sqrt_step_le` — `|√m' − |3 − 4m|·√m| ≤ 2β·√(m(1−m))`, two-sided;
* `qNorm_step_sub_le` — the state moves by at most `(2 + 2β)·√m`.

For the tolerant protocol, with `ν` an unmarked vector (`Π ν = 0`) and `χ = M ν`:

* `le_qNorm_goodPart_stage` — `‖Π χ‖ ≥ 2·|⟨ψ, ν⟩|·√m − β·‖ν‖`;
* `qNorm_badPart_stage_sub_le` — `‖(1−Π)χ − (2⟨ψ,ν⟩·(1−Π)ψ − ν)‖ ≤ β·‖ν‖`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H O : Type} [Fintype H] [DecidableEq H] (rd : H → O) (G : O → Prop) [DecidablePred G]

lemma qNormSq_goodPart_le (ψ : H → ℂ) : qNormSq (goodPart rd G ψ) ≤ qNormSq ψ := by
  rw [qNormSq_def, qNormSq_def]
  refine Finset.sum_le_sum fun h _ => ?_
  rw [goodPart_apply]
  split_ifs
  · exact le_rfl
  · rw [map_zero]; exact Complex.normSq_nonneg _

lemma qNormSq_badPart_le (ψ : H → ℂ) : qNormSq (badPart rd G ψ) ≤ qNormSq ψ := by
  rw [qNormSq_def, qNormSq_def]
  refine Finset.sum_le_sum fun h _ => ?_
  rw [badPart_apply]
  split_ifs
  · rw [map_zero]; exact Complex.normSq_nonneg _
  · exact le_rfl

lemma qNorm_goodPart_le (ψ : H → ℂ) : qNorm (goodPart rd G ψ) ≤ qNorm ψ :=
  Real.sqrt_le_sqrt (qNormSq_goodPart_le rd G ψ)

lemma qNorm_badPart_le (ψ : H → ℂ) : qNorm (badPart rd G ψ) ≤ qNorm ψ :=
  Real.sqrt_le_sqrt (qNormSq_badPart_le rd G ψ)

/-- Orthogonal combination of the two parts. -/
lemma qNormSq_smul_good_add_smul_bad (ψ : H → ℂ) (x y : ℝ) :
    qNormSq ((x : ℂ) • goodPart rd G ψ + (y : ℂ) • badPart rd G ψ)
      = x ^ 2 * qNormSq (goodPart rd G ψ) + y ^ 2 * qNormSq (badPart rd G ψ) := by
  rw [qNormSq_add, qNormSq_smul, qNormSq_smul, qInner_smul_left, qInner_smul_right,
    qInner_goodPart_badPart, Complex.normSq_ofReal, Complex.normSq_ofReal]
  simp only [mul_zero, Complex.zero_re]
  ring

lemma qNorm_goodPart_eq (ψ : H → ℂ) :
    qNorm (goodPart rd G ψ) = Real.sqrt (goodProb rd G ψ) := by
  rw [qNorm, qNormSq_goodPart]

variable {rd G}

section Step

variable {ψ : H → ℂ} (hψ : IsQState ψ)

include hψ

lemma qNormSq_badPart_eq : qNormSq (badPart rd G ψ) = 1 - goodProb rd G ψ := by
  rw [← qNormSq_goodPart]
  exact (groverSplit_parts rd G hψ).qNormSq_bad

lemma qInner_phaseFlip : qInner ψ (phaseFlip rd G ψ) = ((1 - 2 * goodProb rd G ψ : ℝ) : ℂ) := by
  have hs := groverSplit_parts rd G hψ
  rw [phaseFlip, qInner_sub_right, hs.qInner_good, hs.qInner_bad, qNormSq_goodPart]
  push_cast
  ring

/-- **The exact step.** -/
theorem stateRefl_phaseFlip :
    stateRefl ψ *ᵥ phaseFlip rd G ψ
      = ((3 - 4 * goodProb rd G ψ : ℝ) : ℂ) • goodPart rd G ψ
        + ((1 - 4 * goodProb rd G ψ : ℝ) : ℂ) • badPart rd G ψ := by
  rw [stateRefl_mulVec, qInner_phaseFlip hψ, phaseFlip]
  generalize goodProb rd G ψ = m
  have hsplit : (2 * ((1 - 2 * m : ℝ) : ℂ)) • ψ
      = (2 * ((1 - 2 * m : ℝ) : ℂ)) • (goodPart rd G ψ + badPart rd G ψ) := by
    rw [goodPart_add_badPart]
  rw [hsplit]
  push_cast
  module

/-- The component of `S ψ` orthogonal to `ψ`. -/
theorem qNormSq_phaseFlip_orth :
    qNormSq (phaseFlip rd G ψ - qInner ψ (phaseFlip rd G ψ) • ψ)
      = 4 * goodProb rd G ψ * (1 - goodProb rd G ψ) := by
  have h : phaseFlip rd G ψ - qInner ψ (phaseFlip rd G ψ) • ψ
      = ((-(2 - 2 * goodProb rd G ψ) : ℝ) : ℂ) • goodPart rd G ψ
        + ((2 * goodProb rd G ψ : ℝ) : ℂ) • badPart rd G ψ := by
    rw [qInner_phaseFlip hψ, phaseFlip]
    generalize goodProb rd G ψ = m
    have hsplit : ((1 - 2 * m : ℝ) : ℂ) • ψ
        = ((1 - 2 * m : ℝ) : ℂ) • (goodPart rd G ψ + badPart rd G ψ) := by
      rw [goodPart_add_badPart]
    rw [hsplit]
    push_cast
    module
  rw [h, qNormSq_smul_good_add_smul_bad, qNormSq_goodPart, qNormSq_badPart_eq hψ]
  ring

variable {M : Matrix H H ℂ} {D : Set (H → ℂ)} {β : ℝ}

/-- The error vector of the step. -/
lemma qNorm_step_err_le (hM : IsApproxRefl M ψ D β) (hβ : 0 ≤ β) (hD : phaseFlip rd G ψ ∈ D) :
    qNorm (M *ᵥ phaseFlip rd G ψ - stateRefl ψ *ᵥ phaseFlip rd G ψ)
      ≤ 2 * β * Real.sqrt (goodProb rd G ψ) := by
  refine (hM.near _ hD).trans ?_
  have hm0 : 0 ≤ goodProb rd G ψ := goodProb_nonneg _ _ _
  have hm1 : goodProb rd G ψ ≤ 1 := goodProb_le_one _ _ hψ
  have : qNorm (phaseFlip rd G ψ - qInner ψ (phaseFlip rd G ψ) • ψ)
      ≤ 2 * Real.sqrt (goodProb rd G ψ) := by
    refine qNorm_le_of_qNormSq_le (by positivity) ?_
    rw [qNormSq_phaseFlip_orth hψ, mul_pow, Real.sq_sqrt hm0]
    nlinarith
  calc β * _ ≤ β * (2 * Real.sqrt (goodProb rd G ψ)) := mul_le_mul_of_nonneg_left this hβ
    _ = _ := by ring

/-- **The marked amplitude after one step**, two-sided. -/
theorem abs_sqrt_step_le (hM : IsApproxRefl M ψ D β) (hβ : 0 ≤ β) (hD : phaseFlip rd G ψ ∈ D) :
    |Real.sqrt (goodProb rd G (M *ᵥ phaseFlip rd G ψ))
        - |3 - 4 * goodProb rd G ψ| * Real.sqrt (goodProb rd G ψ)|
      ≤ 2 * β * Real.sqrt (goodProb rd G ψ) := by
  set e := M *ᵥ phaseFlip rd G ψ - stateRefl ψ *ᵥ phaseFlip rd G ψ with he
  have herr := qNorm_step_err_le hψ hM hβ hD
  have hgood : goodPart rd G (M *ᵥ phaseFlip rd G ψ)
      = ((3 - 4 * goodProb rd G ψ : ℝ) : ℂ) • goodPart rd G ψ + goodPart rd G e := by
    have : M *ᵥ phaseFlip rd G ψ = stateRefl ψ *ᵥ phaseFlip rd G ψ + e := by rw [he]; abel
    rw [this, goodPart_add, stateRefl_phaseFlip hψ, goodPart_add, goodPart_smul, goodPart_smul,
      goodPart_goodPart, goodPart_badPart, smul_zero, add_zero]
  have hmain : qNorm (((3 - 4 * goodProb rd G ψ : ℝ) : ℂ) • goodPart rd G ψ)
      = |3 - 4 * goodProb rd G ψ| * Real.sqrt (goodProb rd G ψ) := by
    rw [qNorm_smul, Complex.norm_real, Real.norm_eq_abs, qNorm_goodPart_eq]
  have hge : qNorm (goodPart rd G e) ≤ 2 * β * Real.sqrt (goodProb rd G ψ) :=
    (qNorm_goodPart_le rd G e).trans herr
  have hL : Real.sqrt (goodProb rd G (M *ᵥ phaseFlip rd G ψ))
      = qNorm (goodPart rd G (M *ᵥ phaseFlip rd G ψ)) := (qNorm_goodPart_eq rd G _).symm
  rw [hL, hgood, ← hmain, abs_le]
  constructor
  · have := qNorm_sub_le_qNorm_add (((3 - 4 * goodProb rd G ψ : ℝ) : ℂ) • goodPart rd G ψ)
      (goodPart rd G e)
    linarith
  · have := qNorm_add_le (((3 - 4 * goodProb rd G ψ : ℝ) : ℂ) • goodPart rd G ψ)
      (goodPart rd G e)
    linarith

/-- **The state moves by at most `(2 + 2β)·√m`.** -/
theorem qNorm_step_sub_le (hM : IsApproxRefl M ψ D β) (hβ : 0 ≤ β) (hD : phaseFlip rd G ψ ∈ D) :
    qNorm (M *ᵥ phaseFlip rd G ψ - ψ) ≤ (2 + 2 * β) * Real.sqrt (goodProb rd G ψ) := by
  have herr := qNorm_step_err_le hψ hM hβ hD
  have hfix : stateRefl ψ *ᵥ ψ = ψ := (isApproxRefl_stateRefl hψ).fix
  have hsplit : M *ᵥ phaseFlip rd G ψ - ψ
      = (M *ᵥ phaseFlip rd G ψ - stateRefl ψ *ᵥ phaseFlip rd G ψ)
        + stateRefl ψ *ᵥ (phaseFlip rd G ψ - ψ) := by
    rw [Matrix.mulVec_sub, hfix]; abel
  have hdiff : phaseFlip rd G ψ - ψ = ((-2 : ℝ) : ℂ) • goodPart rd G ψ := by
    have h := goodPart_add_badPart rd G ψ
    rw [phaseFlip]
    calc badPart rd G ψ - goodPart rd G ψ - ψ
        = badPart rd G ψ - goodPart rd G ψ - (goodPart rd G ψ + badPart rd G ψ) := by rw [h]
      _ = ((-2 : ℝ) : ℂ) • goodPart rd G ψ := by push_cast; module
  rw [hsplit]
  refine (qNorm_add_le _ _).trans ?_
  rw [qNorm_mulVec (stateRefl_mem_unitaryGroup hψ), hdiff, qNorm_smul, Complex.norm_real,
    Real.norm_eq_abs, qNorm_goodPart_eq]
  have h2 : |(-2 : ℝ)| = 2 := by norm_num
  rw [h2]
  linarith

/-! ## A stage of the tolerant protocol -/

variable {ν : H → ℂ}

lemma qNorm_stage_err_le (hM : IsApproxRefl M ψ D β) (hβ : 0 ≤ β) (hD : ν ∈ D) :
    qNorm (M *ᵥ ν - stateRefl ψ *ᵥ ν) ≤ β * qNorm ν := by
  exact (hM.near _ hD).trans (mul_le_mul_of_nonneg_left (qNorm_sub_proj_le hψ ν) hβ)

/-- The marked amplitude produced by a stage. -/
theorem le_qNorm_goodPart_stage (hM : IsApproxRefl M ψ D β) (hβ : 0 ≤ β) (hD : ν ∈ D)
    (hν : goodPart rd G ν = 0) :
    2 * ‖qInner ψ ν‖ * Real.sqrt (goodProb rd G ψ) - β * qNorm ν
      ≤ qNorm (goodPart rd G (M *ᵥ ν)) := by
  set e := M *ᵥ ν - stateRefl ψ *ᵥ ν with he
  have herr := qNorm_stage_err_le hψ hM hβ hD
  have hgood : goodPart rd G (M *ᵥ ν) = (2 * qInner ψ ν) • goodPart rd G ψ + goodPart rd G e := by
    have : M *ᵥ ν = stateRefl ψ *ᵥ ν + e := by rw [he]; abel
    rw [this, goodPart_add, stateRefl_mulVec, goodPart_sub, goodPart_smul, hν, sub_zero]
  have hmain : qNorm ((2 * qInner ψ ν) • goodPart rd G ψ)
      = 2 * ‖qInner ψ ν‖ * Real.sqrt (goodProb rd G ψ) := by
    rw [qNorm_smul, norm_mul, Complex.norm_ofNat, qNorm_goodPart_eq]
  have h1 := qNorm_sub_le_qNorm_add ((2 * qInner ψ ν) • goodPart rd G ψ) (goodPart rd G e)
  have h2 := (qNorm_goodPart_le rd G e).trans herr
  rw [hgood, ← hmain]
  linarith

/-- The continuing vector of a stage. -/
theorem qNorm_badPart_stage_sub_le (hM : IsApproxRefl M ψ D β) (hβ : 0 ≤ β) (hD : ν ∈ D)
    (hν : goodPart rd G ν = 0) :
    qNorm (badPart rd G (M *ᵥ ν) - ((2 * qInner ψ ν) • badPart rd G ψ - ν)) ≤ β * qNorm ν := by
  set e := M *ᵥ ν - stateRefl ψ *ᵥ ν with he
  have herr := qNorm_stage_err_le hψ hM hβ hD
  have hνb : badPart rd G ν = ν := by
    have := goodPart_add_badPart rd G ν
    rwa [hν, zero_add] at this
  have hbad : badPart rd G (M *ᵥ ν)
      = ((2 * qInner ψ ν) • badPart rd G ψ - ν) + badPart rd G e := by
    have : M *ᵥ ν = stateRefl ψ *ᵥ ν + e := by rw [he]; abel
    rw [this, badPart_add, stateRefl_mulVec, badPart_sub, badPart_smul, hνb]
  rw [hbad, add_sub_cancel_left]
  exact (qNorm_badPart_le rd G e).trans herr

end Step

end QuantumQueryComplexity
