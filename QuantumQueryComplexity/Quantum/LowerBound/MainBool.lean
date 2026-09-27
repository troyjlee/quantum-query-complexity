import QuantumQueryComplexity.Quantum.LowerBound.Main
import QuantumQueryComplexity.Quantum.LowerBound.OutputBool
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The adversary lower bound at the sharp Boolean constant

`Main.lean` proves the lower bound with output constant `2√ε + ε`, which
requires `ε < 3 − 2√2 ≈ 0.1716`.  For **Boolean** outputs the sharp constant
`2√(ε(1−ε))` of `OutputBool.lean` plugs into the same parametric endgame
(`advPMOn_le_of_bilinear`), and `2√(ε(1−ε)) < 1` holds for every
`ε < 1/2` — in particular at the conventional `ε = 1/3`:

    mul_advPMOn_le_qQueryOn_of_error_third :
      (1/36) · advPMOn read f ≤ Q_{1/3}(f)

promise-native, no amplification, no repetition compiler.  The constant check
behind `1/36` is `(3 − 2√2)/6 ≥ 1/36 ⟺ 289 ≥ 288` — the sharp constant at
`ε = 1/3` is `(3 − 2√2)/6 ≈ 0.0286`, and `1/36 ≈ 0.0278` sits just under it.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X] [DecidableEq X]
variable {W : Type} [Fintype W] [DecidableEq W]

section

variable {A : QAlg ι σ Bool W} {q : ℕ} {read : X → ι → σ} {f : X → Bool} {ε : ℝ}

/-- **The Boolean-sharp adversary bound**: a `q`-query algorithm with error
`ε ≤ 1/2` forces `(1 − 2√(ε(1−ε)))·advPMOn read f ≤ 2q`. -/
theorem advPMOn_le_of_computes_bool (hε0 : 0 ≤ ε) (hε2 : ε ≤ 1 / 2)
    (hlt : 2 * Real.sqrt (ε * (1 - ε)) < 1)
    (hcomp : ComputesWithErrorOn A q read f ε) :
    (1 - 2 * Real.sqrt (ε * (1 - ε))) * advPMOn read f ≤ 2 * q := by
  refine advPMOn_le_of_bilinear
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hlt ?_
  intro Γ hΓ hfeas δ δ' hδ hδ'
  have hout : |algProgress Γ δ δ' A read q|
      ≤ ‖Γ‖ * (2 * Real.sqrt (ε * (1 - ε))) := by
    rw [algProgress]
    exact abs_progress_output_le_bool (fun x y h => hΓ.2 x y h)
      (fun x => A.state_isQState (read x) q) hε0 hε2 (fun x => hcomp x) hδ hδ'
  exact abs_dotProduct_mulVec_le_of_algProgress hfeas hδ hδ' hout

end

/-- **The sharp lower bound on Boolean query complexity**: every `ε ≤ 1/2`
with `2√(ε(1−ε)) < 1` works — the threshold is `ε < 1/2`, not
`ε < 3 − 2√2`. -/
theorem mul_advPMOn_le_qQueryOn_bool {read : X → ι → σ} {f : X → Bool} {ε : ℝ}
    (hdet : ∀ x y, read x = read y → f x = f y)
    (hε0 : 0 ≤ ε) (hε2 : ε ≤ 1 / 2)
    (hlt : 2 * Real.sqrt (ε * (1 - ε)) < 1) :
    (1 - 2 * Real.sqrt (ε * (1 - ε))) / 2 * advPMOn read f
      ≤ (qQueryOn read f ε : ℝ) := by
  refine le_qQueryOn_real (queryCounts_nonempty hdet hε0) fun q W' _ _ A hA => ?_
  have h := advPMOn_le_of_computes_bool hε0 hε2 hlt hA
  linarith

/-- **The conventional-error instance**: `(1/36)·advPMOn read f ≤ Q_{1/3}(f)`
for Boolean `f`, promise-native. -/
theorem mul_advPMOn_le_qQueryOn_of_error_third {read : X → ι → σ}
    {f : X → Bool} (hdet : ∀ x y, read x = read y → f x = f y) :
    (1 / 36 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 3) : ℝ) := by
  have hs : Real.sqrt ((1 : ℝ) / 3 * (1 - 1 / 3)) ≤ 17 / 36 := by
    calc Real.sqrt ((1 : ℝ) / 3 * (1 - 1 / 3))
        ≤ Real.sqrt ((17 / 36 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 17 / 36 := Real.sqrt_sq (by norm_num)
  have h := mul_advPMOn_le_qQueryOn_bool (read := read) (f := f) (ε := 1 / 3)
    hdet (by norm_num) (by norm_num) (by linarith [hs])
  have hcoef : (1 / 36 : ℝ)
      ≤ (1 - 2 * Real.sqrt ((1 : ℝ) / 3 * (1 - 1 / 3))) / 2 := by
    linarith [hs]
  rcases le_or_gt 0 (advPMOn read f) with hadv | hadv
  · calc (1 / 36 : ℝ) * advPMOn read f
        ≤ (1 - 2 * Real.sqrt ((1 : ℝ) / 3 * (1 - 1 / 3))) / 2 * advPMOn read f :=
          mul_le_mul_of_nonneg_right hcoef hadv
      _ ≤ (qQueryOn read f (1 / 3) : ℝ) := h
  · have hq : (0 : ℝ) ≤ (qQueryOn read f (1 / 3) : ℝ) := Nat.cast_nonneg _
    nlinarith

end QuantumQueryComplexity
