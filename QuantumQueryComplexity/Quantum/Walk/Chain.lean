import QuantumQueryComplexity.Quantum.Walk.TwoReflections
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Reversible chains, the discriminant, and two example chains

A reversible chain `(P, π)` on `V`: `P` row-stochastic, `π` positive summing to `1`, detailed
balance `π u · P u v = π v · P v u`.  Its **discriminant** `disc P π u v = √(π u) · P u v / √(π v)`
is symmetric (`disc_herm`), fixes `r = √π` (`disc_r`), and `r` is a unit vector (`r_unit`) —
the three chain facts of `WalkFam` and `WalkOK`.  The absolute gap certificate
`‖D y‖ ≤ (1−δ)‖y‖` on `r^⊥` is supplied separately; it is an *absolute* gap (both ends of the
spectrum), not `1 − λ₂`.

Two example chains:

* **complete resampling** `P u v = π v`, any positive `π`: `D = |r⟩⟨r|` has rank one and
  certified absolute gap `δ = 1` (`resampling_gap`);
* **the lazy two-state chain** `P = [[1−p, p], [p, 1−p]]`, `0 < p ≤ 1/2`, uniform `π`: absolute
  gap `δ = 2p` (`lazy_gap`).  At `p = 1` the ordinary gap `1 − λ₂` would be `2` but the chain is
  periodic: `D = [[0,1],[1,0]]` has eigenvalue `−1`, and `lazy_gap` indeed requires `p ≤ 1/2`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A reversible chain. -/
structure RevChain (V : Type) [Fintype V] where
  P : Matrix V V ℝ
  π : V → ℝ
  P_nonneg : ∀ u v, 0 ≤ P u v
  P_row : ∀ u, ∑ v, P u v = 1
  π_pos : ∀ u, 0 < π u
  π_sum : ∑ u, π u = 1
  balance : ∀ u v, π u * P u v = π v * P v u

namespace RevChain

variable (M : RevChain V)

/-- `√π`. -/
noncomputable def r : V → ℂ := fun u => ((Real.sqrt (M.π u) : ℝ) : ℂ)

/-- The discriminant `√π_u P_{uv} / √π_v`. -/
noncomputable def disc : Matrix V V ℂ := fun u v =>
  ((Real.sqrt (M.π u) * M.P u v / Real.sqrt (M.π v) : ℝ) : ℂ)

lemma sqrt_pos (u : V) : 0 < Real.sqrt (M.π u) := Real.sqrt_pos.mpr (M.π_pos u)

theorem r_unit : IsQState M.r := by
  rw [IsQState, qNormSq_def]
  simp only [r, Complex.normSq_ofReal, Real.mul_self_sqrt (M.π_pos _).le]
  exact M.π_sum

theorem disc_herm : (M.disc)ᴴ = M.disc := by
  ext u v
  rw [Matrix.conjTranspose_apply, disc, disc, Complex.star_def, Complex.conj_ofReal]
  congr 1
  have hu := M.sqrt_pos u
  have hv := M.sqrt_pos v
  have hb := M.balance u v
  have hsu := Real.mul_self_sqrt (M.π_pos u).le
  have hsv := Real.mul_self_sqrt (M.π_pos v).le
  rw [div_eq_div_iff hu.ne' hv.ne']
  calc Real.sqrt (M.π v) * M.P v u * Real.sqrt (M.π v) = M.π v * M.P v u := by
        rw [mul_right_comm, hsv]
    _ = M.π u * M.P u v := hb.symm
    _ = Real.sqrt (M.π u) * M.P u v * Real.sqrt (M.π u) := by rw [mul_right_comm, hsu]

theorem disc_r : M.disc *ᵥ M.r = M.r := by
  funext u
  rw [Matrix.mulVec, dotProduct]
  simp only [disc, r, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  congr 1
  have : ∀ v, Real.sqrt (M.π u) * M.P u v / Real.sqrt (M.π v) * Real.sqrt (M.π v)
      = Real.sqrt (M.π u) * M.P u v := fun v => by
    field_simp [(M.sqrt_pos v).ne']
  simp only [this, ← Finset.mul_sum, M.P_row, mul_one]

end RevChain

/-! ## Complete resampling -/

/-- `P u v = π v`. -/
noncomputable def resampling (π : V → ℝ) (hπ : ∀ u, 0 < π u) (hs : ∑ u, π u = 1) : RevChain V where
  P := fun _ v => π v
  π := π
  P_nonneg := fun _ v => (hπ v).le
  P_row := fun _ => hs
  π_pos := hπ
  π_sum := hs
  balance := fun u v => mul_comm _ _

lemma resampling_disc (π : V → ℝ) (hπ : ∀ u, 0 < π u) (hs : ∑ u, π u = 1) (u v : V) :
    (resampling π hπ hs).disc u v = (resampling π hπ hs).r u * (resampling π hπ hs).r v := by
  simp only [RevChain.disc, RevChain.r, resampling, ← Complex.ofReal_mul]
  congr 1
  have hv := Real.sqrt_pos.mpr (hπ v)
  have := Real.mul_self_sqrt (hπ v).le
  rw [mul_div_assoc, (div_eq_iff hv.ne').mpr this.symm]

/-- **Rank one, gap `1`**: on `r^⊥` the discriminant vanishes. -/
theorem resampling_gap (π : V → ℝ) (hπ : ∀ u, 0 < π u) (hs : ∑ u, π u = 1) (y : V → ℂ)
    (hy : qInner (resampling π hπ hs).r y = 0) :
    qNormSq ((resampling π hπ hs).disc *ᵥ y) ≤ (1 - 1) ^ 2 * qNormSq y := by
  have h0 : (resampling π hπ hs).disc *ᵥ y = 0 := by
    funext u
    rw [Matrix.mulVec, dotProduct]
    simp only [resampling_disc, mul_assoc, ← Finset.mul_sum]
    have : ∑ v, (resampling π hπ hs).r v * y v = qInner (resampling π hπ hs).r y := by
      rw [qInner_def]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp [RevChain.r, Complex.star_def, Complex.conj_ofReal]
    rw [this, hy, mul_zero]
    rfl
  rw [h0]
  simp [qNormSq_def]

/-! ## The lazy two-state chain -/

/-- `P = [[1−p, p], [p, 1−p]]` on `Bool`, uniform `π`. -/
noncomputable def lazyTwo (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : RevChain Bool where
  P := fun u v => if u = v then 1 - p else p
  π := fun _ => 1 / 2
  P_nonneg := fun u v => by split_ifs <;> linarith
  P_row := fun u => by cases u <;> simp
  π_pos := fun _ => by norm_num
  π_sum := by simp
  balance := fun u v => by cases u <;> cases v <;> simp

lemma lazyTwo_disc (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (u v : Bool) :
    (lazyTwo p hp hp1).disc u v = ((if u = v then 1 - p else p : ℝ) : ℂ) := by
  simp only [RevChain.disc, lazyTwo]
  congr 1
  have : Real.sqrt (1 / 2) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  field_simp

/-- **Absolute gap `2p`** for `0 < p ≤ 1/2`. -/
theorem lazy_gap (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1 / 2) (y : Bool → ℂ)
    (hy : qInner (lazyTwo p hp.le (by linarith)).r y = 0) :
    qNormSq ((lazyTwo p hp.le (by linarith)).disc *ᵥ y) ≤ (1 - 2 * p) ^ 2 * qNormSq y := by
  have hr : (lazyTwo p hp.le (by linarith)).r = fun _ => ((Real.sqrt (1 / 2) : ℝ) : ℂ) := rfl
  have hsum : y false + y true = 0 := by
    rw [qInner_def, Fintype.sum_bool, hr] at hy
    simp only [Complex.star_def, Complex.conj_ofReal] at hy
    have hne : ((Real.sqrt (1 / 2) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 1 / 2)).ne'
    have : ((Real.sqrt (1 / 2) : ℝ) : ℂ) * (y true + y false) = 0 := by rw [← hy]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hne
    · rw [← h]; ring
  have hDy : (lazyTwo p hp.le (by linarith)).disc *ᵥ y = ((1 - 2 * p : ℝ) : ℂ) • y := by
    funext u
    rw [Matrix.mulVec, dotProduct, Fintype.sum_bool]
    simp only [lazyTwo_disc, Pi.smul_apply, smul_eq_mul]
    cases u
    · simp only [Bool.false_eq_true, if_false, if_true]
      have : y true = -y false := by linear_combination hsum
      rw [this]; push_cast; ring
    · simp only [Bool.true_eq_false, if_false, if_true]
      have : y false = -y true := by linear_combination hsum
      rw [this]; push_cast; ring
  rw [hDy, qNormSq_smul, Complex.normSq_ofReal]
  exact le_of_eq (by ring)

end QuantumQueryComplexity
