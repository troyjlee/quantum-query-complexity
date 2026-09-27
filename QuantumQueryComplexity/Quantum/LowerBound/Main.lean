import QuantumQueryComplexity.Quantum.LowerBound.Output
import QuantumQueryComplexity.Quantum.ReadAll
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The adversary lower bound

**Milestone A.**  Every quantum algorithm that computes `f` on the promise
`read` with error at most `ε` makes at least

  `(1 - (2√ε + ε)) / 2 · advPMOn read f`

queries.  The three ingredients are the ones proved in `Progress.lean` and
`Output.lean`: the progress starts at `δ ⬝ᵥ Γ *ᵥ δ'`, moves by at most `2` per
query, and ends below `‖Γ‖ (2√ε + ε)`.

**Why two weight vectors.**  The classical proof takes `δ` to be a
norm-attaining eigenvector of `Γ`, so that the initial progress *is* `‖Γ‖`.
That needs the spectral theorem for real symmetric matrices, which this project
has deliberately avoided.  Carrying two weight vectors instead makes the initial
progress the **bilinear** form `δ ⬝ᵥ Γ *ᵥ δ'`, and `Spectral.lean`'s
`l2_opNorm_le_of_forall_dotProduct` — already proved, and used throughout the
adversary side — converts a bound on all of those into a bound on `‖Γ‖`.  The
only extra work is normalizing an arbitrary pair of vectors, which is four
lines.

The error threshold is `2√ε + ε < 1`, i.e. `ε < 3 - 2√2 ≈ 0.1716`; see
`Output.lean` for why this is not the sharp `2√(ε(1-ε))` and what recovers the
conventional `ε = 1/3`.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι σ O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype O] [DecidableEq O]
variable {X : Type} [Fintype X] [DecidableEq X]
variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## The progress of an algorithm -/

/-- The progress carried by an algorithm's states after `t` queries. -/
noncomputable def algProgress (Γ : Matrix X X ℝ) (δ δ' : X → ℝ)
    (A : QAlg ι σ O W) (read : X → ι → σ) (t : ℕ) : ℝ :=
  progress Γ δ δ' (fun x => A.state (read x) t)

/-- **Before any query the progress is the bilinear form.** -/
lemma algProgress_zero (Γ : Matrix X X ℝ) (δ δ' : X → ℝ) (A : QAlg ι σ O W)
    (read : X → ι → σ) : algProgress Γ δ δ' A read 0 = δ ⬝ᵥ Γ *ᵥ δ' := by
  rw [algProgress, show (fun x => A.state (read x) 0) = fun _ => A.step 0 *ᵥ A.init from rfl]
  exact progress_const Γ δ δ'
    (IsQState.mulVec (A.step_unitary 0) A.init_isQState)

/-- **One query moves the progress by at most `2`.** -/
lemma abs_algProgress_succ_sub_le {Γ : Matrix X X ℝ} {δ δ' : X → ℝ}
    (A : QAlg ι σ O W) {read : X → ι → σ}
    (hfeas : ∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1)
    (hδ : ∑ x, δ x ^ 2 = 1) (hδ' : ∑ y, δ' y ^ 2 = 1) (t : ℕ) :
    |algProgress Γ δ δ' A read (t + 1) - algProgress Γ δ δ' A read t| ≤ 2 := by
  have hstep : (fun x => A.state (read x) (t + 1))
      = fun x => A.step (t + 1) *ᵥ (oracleMat (read x) *ᵥ A.state (read x) t) := rfl
  rw [algProgress, algProgress, hstep, progress_mulVec (A.step_unitary (t + 1))]
  have h := abs_progress_oracle_sub_le read Γ δ (fun x => A.state (read x) t) δ'
    hfeas zero_le_one
  have hw : ∑ x, δ x ^ 2 * qNormSq (A.state (read x) t) = 1 := by
    rw [← hδ]
    exact Finset.sum_congr rfl fun x _ => by rw [A.state_isQState (read x) t, mul_one]
  have hw' : ∑ y, δ' y ^ 2 * qNormSq (A.state (read y) t) = 1 := by
    rw [← hδ']
    exact Finset.sum_congr rfl fun y _ => by rw [A.state_isQState (read y) t, mul_one]
  rw [hw, hw', Real.sqrt_one, mul_one, mul_one] at h
  linarith

/-- **After `q` queries the progress has moved by at most `2q`.** -/
lemma abs_algProgress_sub_zero_le {Γ : Matrix X X ℝ} {δ δ' : X → ℝ}
    (A : QAlg ι σ O W) {read : X → ι → σ}
    (hfeas : ∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1)
    (hδ : ∑ x, δ x ^ 2 = 1) (hδ' : ∑ y, δ' y ^ 2 = 1) (q : ℕ) :
    |algProgress Γ δ δ' A read q - algProgress Γ δ δ' A read 0| ≤ 2 * q := by
  induction q with
  | zero => simp
  | succ t ih =>
      have h1 := abs_algProgress_succ_sub_le A hfeas hδ hδ' t
      have h2 : |algProgress Γ δ δ' A read (t + 1) - algProgress Γ δ δ' A read 0|
          ≤ |algProgress Γ δ δ' A read (t + 1) - algProgress Γ δ δ' A read t|
            + |algProgress Γ δ δ' A read t - algProgress Γ δ δ' A read 0| :=
        abs_sub_le _ _ _
      push_cast
      linarith

/-! ## The lower bound -/

section

variable {A : QAlg ι σ O W} {q : ℕ} {read : X → ι → σ} {f : X → O} {ε : ℝ}

/-- **The telescoping step, parametric in the output constant**: any bound
`‖Γ‖·κ` on the progress after `q` queries bounds the initial bilinear form by
`‖Γ‖·κ + 2q`. -/
lemma abs_dotProduct_mulVec_le_of_algProgress {Γ : Matrix X X ℝ} {κ : ℝ}
    (hfeas : ∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1)
    {δ δ' : X → ℝ} (hδ : ∑ x, δ x ^ 2 = 1) (hδ' : ∑ y, δ' y ^ 2 = 1)
    (hout : |algProgress Γ δ δ' A read q| ≤ ‖Γ‖ * κ) :
    |δ ⬝ᵥ Γ *ᵥ δ'| ≤ ‖Γ‖ * κ + 2 * q := by
  have htel := abs_algProgress_sub_zero_le A hfeas hδ hδ' q
  have h0 := algProgress_zero Γ δ δ' A read
  have hsplit : |algProgress Γ δ δ' A read 0|
      ≤ |algProgress Γ δ δ' A read q|
        + |algProgress Γ δ δ' A read q - algProgress Γ δ δ' A read 0| := by
    have := abs_sub_le (algProgress Γ δ δ' A read 0) (algProgress Γ δ δ' A read q) 0
    simp only [sub_zero] at this
    rw [abs_sub_comm (algProgress Γ δ δ' A read 0)] at this
    linarith
  rw [h0] at hsplit htel
  linarith

/-- The bilinear form of any feasible adversary matrix is bounded by the
algorithm's query count and error. -/
lemma abs_dotProduct_mulVec_le_of_computes {Γ : Matrix X X ℝ}
    (hΓ : IsAdvMatrixOn f Γ) (hfeas : ∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1)
    (hε0 : 0 ≤ ε) (hcomp : ComputesWithErrorOn A q read f ε)
    {δ δ' : X → ℝ} (hδ : ∑ x, δ x ^ 2 = 1) (hδ' : ∑ y, δ' y ^ 2 = 1) :
    |δ ⬝ᵥ Γ *ᵥ δ'| ≤ ‖Γ‖ * (2 * Real.sqrt ε + ε) + 2 * q := by
  have hout : |algProgress Γ δ δ' A read q| ≤ ‖Γ‖ * (2 * Real.sqrt ε + ε) := by
    rw [algProgress]
    exact abs_progress_output_le (fun x y h => hΓ.2 x y h)
      (fun x => A.state_isQState (read x) q) hε0 (fun x => hcomp x) hδ hδ'
  exact abs_dotProduct_mulVec_le_of_algProgress hfeas hδ hδ' hout

/-- **The endgame, parametric in the output constant.**  If every feasible
adversary matrix satisfies the bilinear bound `‖Γ‖·κ + 2q` on unit weight
vectors, then `(1 − κ)·advPMOn ≤ 2q`.  Instantiated by
`advPMOn_le_of_computes` with `κ = 2√ε + ε`, and by the Boolean sharpening
(`MainBool.lean`) with `κ = 2√(ε(1−ε))`. -/
theorem advPMOn_le_of_bilinear {κ : ℝ} (hκ0 : 0 ≤ κ) (hlt : κ < 1)
    (hbil : ∀ Γ : Matrix X X ℝ, IsAdvMatrixOn f Γ →
      (∀ i, ‖Γ ⊙ advDOn read i‖ ≤ 1) →
      ∀ δ δ' : X → ℝ, (∑ x, δ x ^ 2 = 1) → (∑ y, δ' y ^ 2 = 1) →
        |δ ⬝ᵥ Γ *ᵥ δ'| ≤ ‖Γ‖ * κ + 2 * q) :
    (1 - κ) * advPMOn read f ≤ 2 * q := by
  have hpos : 0 < 1 - κ := by linarith
  rw [← le_div_iff₀' hpos]
  refine advPMOn_le fun Γ hΓ hfeas => ?_
  set K : ℝ := ‖Γ‖ * κ + 2 * q with hK
  have hK0 : 0 ≤ K := by
    have h1 : (0 : ℝ) ≤ ‖Γ‖ := norm_nonneg _
    have h3 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
    have : 0 ≤ ‖Γ‖ * κ := mul_nonneg h1 hκ0
    rw [hK]
    linarith
  -- the bilinear bound, for arbitrary (not necessarily unit) vectors
  have key : ∀ a b : X → ℝ,
      |a ⬝ᵥ Γ *ᵥ b| ≤ K * Real.sqrt (a ⬝ᵥ a) * Real.sqrt (b ⬝ᵥ b) := by
    intro a b
    have hsum : ∀ w : X → ℝ, (∑ x, w x ^ 2) = w ⬝ᵥ w := by
      intro w
      exact Finset.sum_congr rfl fun x _ => pow_two (w x)
    rcases eq_or_lt_of_le (dotProduct_self_nonneg a) with ha | ha
    · have ha0 : a = 0 := by
        funext x
        have := (Finset.sum_eq_zero_iff_of_nonneg
          (fun x (_ : x ∈ Finset.univ) => mul_self_nonneg (a x))).mp ha.symm x
            (Finset.mem_univ x)
        exact mul_self_eq_zero.mp this
      rw [ha0]
      simp
    rcases eq_or_lt_of_le (dotProduct_self_nonneg b) with hb | hb
    · have hb0 : b = 0 := by
        funext x
        have := (Finset.sum_eq_zero_iff_of_nonneg
          (fun x (_ : x ∈ Finset.univ) => mul_self_nonneg (b x))).mp hb.symm x
            (Finset.mem_univ x)
        exact mul_self_eq_zero.mp this
      rw [hb0]
      simp
    -- normalize
    set s : ℝ := Real.sqrt (a ⬝ᵥ a) with hs
    set s' : ℝ := Real.sqrt (b ⬝ᵥ b) with hs'
    have hs0 : 0 < s := Real.sqrt_pos.mpr ha
    have hs'0 : 0 < s' := Real.sqrt_pos.mpr hb
    have hsne : s ≠ 0 := ne_of_gt hs0
    have hs'ne : s' ≠ 0 := ne_of_gt hs'0
    have hss : s * s = a ⬝ᵥ a := Real.mul_self_sqrt (dotProduct_self_nonneg a)
    have hss' : s' * s' = b ⬝ᵥ b := Real.mul_self_sqrt (dotProduct_self_nonneg b)
    have hunit : ∑ x, (s⁻¹ * a x) ^ 2 = 1 := by
      have : ∑ x, (s⁻¹ * a x) ^ 2 = s⁻¹ ^ 2 * ∑ x, a x ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [this, hsum, ← hss]
      field_simp
    have hunit' : ∑ y, (s'⁻¹ * b y) ^ 2 = 1 := by
      have : ∑ y, (s'⁻¹ * b y) ^ 2 = s'⁻¹ ^ 2 * ∑ y, b y ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
      rw [this, hsum, ← hss']
      field_simp
    have hmaster := hbil Γ hΓ hfeas _ _ hunit hunit'
    have hscale : (fun x => s⁻¹ * a x) ⬝ᵥ Γ *ᵥ (fun y => s'⁻¹ * b y)
        = s⁻¹ * s'⁻¹ * (a ⬝ᵥ Γ *ᵥ b) := by
      rw [dotProduct_mulVec_eq_sum, dotProduct_mulVec_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [hscale] at hmaster
    rw [abs_mul] at hmaster
    have habs : |s⁻¹ * s'⁻¹| = s⁻¹ * s'⁻¹ := abs_of_pos (by positivity)
    rw [habs] at hmaster
    have h2 : (0 : ℝ) < s * s' := by positivity
    calc |a ⬝ᵥ Γ *ᵥ b| = (s * s') * (s⁻¹ * s'⁻¹ * |a ⬝ᵥ Γ *ᵥ b|) := by field_simp
      _ ≤ (s * s') * K := mul_le_mul_of_nonneg_left hmaster h2.le
      _ = K * s * s' := by ring
  have hnorm := l2_opNorm_le_of_forall_dotProduct Γ hK0 key
  rw [hK] at hnorm
  rw [le_div_iff₀' hpos]
  linarith

/-- **The adversary lower bound.**  A `q`-query algorithm with error `ε` forces
`advPMOn read f ≤ 2q / (1 - (2√ε + ε))`. -/
theorem advPMOn_le_of_computes (hε0 : 0 ≤ ε) (hlt : 2 * Real.sqrt ε + ε < 1)
    (hcomp : ComputesWithErrorOn A q read f ε) :
    (1 - (2 * Real.sqrt ε + ε)) * advPMOn read f ≤ 2 * q :=
  advPMOn_le_of_bilinear
    (add_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg ε)) hε0) hlt
    (fun Γ hΓ hfeas δ δ' hδ hδ' =>
      abs_dotProduct_mulVec_le_of_computes hΓ hfeas hε0 hcomp hδ hδ')

end

/-! ## The bound on the query complexity -/

/-- **Milestone A.**  Bounded-error quantum query complexity is at least
`(1 - (2√ε + ε))/2` times the adversary bound, for any error `ε` with
`2√ε + ε < 1`. -/
theorem mul_advPMOn_le_qQueryOn {read : X → ι → σ} {f : X → O} {ε : ℝ} [Nonempty O]
    (hdet : ∀ x y, read x = read y → f x = f y)
    (hε0 : 0 ≤ ε) (hlt : 2 * Real.sqrt ε + ε < 1) :
    (1 - (2 * Real.sqrt ε + ε)) / 2 * advPMOn read f ≤ (qQueryOn read f ε : ℝ) := by
  refine le_qQueryOn_real (queryCounts_nonempty hdet hε0) fun q W' _ _ A hA => ?_
  have h := advPMOn_le_of_computes hε0 hlt hA
  linarith

/-- A concrete instance of the lower bound: at error `1/16` the constant is
`7/32`.  (The threshold `2√ε + ε < 1` holds for every `ε < 3 - 2√2 ≈ 0.1716`.) -/
theorem mul_advPMOn_le_qQueryOn_of_error_sixteenth {read : X → ι → σ} {f : X → O}
    [Nonempty O] (hdet : ∀ x y, read x = read y → f x = f y) :
    (7 / 32 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 16) : ℝ) := by
  have hs : Real.sqrt (1 / 16 : ℝ) = 1 / 4 := by
    rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h := mul_advPMOn_le_qQueryOn (read := read) (f := f) (ε := 1 / 16) hdet
    (by norm_num) (by rw [hs]; norm_num)
  rw [hs] at h
  norm_num at h
  linarith

end QuantumQueryComplexity
