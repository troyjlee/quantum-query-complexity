import QuantumQueryComplexity.Quantum.Detection
import QuantumQueryComplexity.Quantum.HadamardTest
import QuantumQueryComplexity.Quantum.Complexity
set_option synthInstance.maxSize 800

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The dual-to-algorithm upper bound (Milestone B step 6)

The extraction: a feasible `DualPairOn read K f` for a **Boolean** `f` becomes
a quantum query algorithm.  The algorithm is nothing but the Hadamard test of
the `o = true` detector on the target state,

    scAlg = hadTest (scDetector read f P true T) (uniformClock T scTarget),

at exactly `4(T−1)` queries, and its correctness is the two acceptance
estimates of `Detection.lean` pushed through `hadTest_prob_true/false`:

* `scAlg_computes` — the **parametric** correctness: any `(T, Δ, cu, cv, ε)`
  satisfying the two explicit inequalities gives
  `ComputesWithErrorOn (scAlg …) (4(T−1)) read f ε`;
* `exists_algorithm_of_dualPairOn` — the **endgame**: a dual of cost `c > 0`
  is compiled, after the `scale` balancing `α² = (16|σ|c)⁻¹` and the choices
  `Δ = (16√B)⁻¹`, `T = ⌈2048√B⌉` for `B = 1 + 16|σ|c²`, into membership

      4(T−1) ∈ QueryCounts read f (1/16),   4(T−1) ≤ 8192·(1 + 4√|σ|·c),

  with the `qQueryOn` corollary `qQueryOn_le_of_dualPairOn`.  For a Boolean
  alphabet `√|σ| = √2`, so the bound is `O(c)` with an explicit constant.

The error budget of the endgame, for the record: positive side
`s·cu = (|σ|−1)/(16|σ|) ≤ 1/16`, so the acceptance is at least
`1/(1 + 1/16) = 16/17 ≥ 15/16`; negative side
`1/64 + 1/64 + 1/2048 = 65/2048 ≤ 1/16`.  Nothing is tight — the constants
are chosen round, not small.

The output convention: `scAlg` announces `true` on constructive interference
(control `0`), which is the `f x = true` side because `scKer read f P true`
spans the positive witnesses of `f⁻¹(true)`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ X K : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [DecidableEq σ] [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]

variable (read : X → ι → σ) (f : X → Bool)

lemma isQState_uniformClock_scTarget {T : ℕ} (hT : 0 < T) :
    IsQState (uniformClock T (scTarget : QBasis ι σ (Option K) → ℂ)) := by
  rw [IsQState, qNormSq_uniformClock hT, qNormSq_scTarget]

/-- **The extracted algorithm**: the Hadamard test of the `o = true` detector
on the target state.  Cost: exactly `4(T−1)` queries. -/
noncomputable def scAlg (P : DualPairOn read K f) (T : ℕ) (hT : 0 < T) :
    QAlg ι σ Bool (CtrlWork ι (ClockWork ι T (Option K))) :=
  hadTest (scDetector read f P true T) (uniformClock T scTarget)
    (isQState_uniformClock_scTarget hT)

/-- **Parametric correctness of the extracted algorithm.**  The two
hypotheses are exactly the two acceptance estimates' final forms; any
parameter choice satisfying them gives a bounded-error algorithm. -/
theorem scAlg_computes [Nonempty σ] (P : DualPairOn read K f)
    {T : ℕ} (hT : 0 < T) {Δ : ℝ} (hΔ : 0 < Δ) {cu cv ε : ℝ}
    (hcu : ∀ x, ∑ i, ∑ k, P.u x i k * P.u x i k ≤ cu)
    (hcv : ∀ y, ∑ i, ∑ k, P.v y i k * P.v y i k ≤ cv)
    (hpos : 1 - ε ≤ 1 / (1 + ((Fintype.card σ : ℝ) - 1) * cu))
    (hneg : Δ / 4 * Real.sqrt (1 + cv) + 2 / ((T : ℝ) * Δ)
      + Δ ^ 2 / 8 * (1 + cv) ≤ ε) :
    ComputesWithErrorOn (scAlg read f P T hT) (4 * (T - 1)) read f ε := by
  intro x
  have hlen : (scDetector read f P true T).len = 4 * (T - 1) :=
    scDetector_len read f P true T
  rw [scAlg, ← hlen]
  cases hfx : f x with
  | true =>
      rw [hadTest_prob_true]
      have hRe := le_re_qInner_scDetector_of_eq read f P hfx hT (hcu x)
      have hb : 2 / (1 + ((Fintype.card σ : ℝ) - 1) * cu)
          = 2 * (1 / (1 + ((Fintype.card σ : ℝ) - 1) * cu)) := by ring
      linarith [hRe, hpos, hb]
  | false =>
      rw [hadTest_prob_false]
      have hRe := re_qInner_scDetector_le_of_ne read f P
        (show f x ≠ true by simp [hfx]) hT hΔ (hcv x)
      have hb1 : Δ / 2 * Real.sqrt (1 + cv)
          = 2 * (Δ / 4 * Real.sqrt (1 + cv)) := by ring
      have hb2 : (4 : ℝ) / ((T : ℝ) * Δ) = 2 * (2 / ((T : ℝ) * Δ)) := by ring
      have hb3 : Δ ^ 2 / 4 * (1 + cv) = 2 * (Δ ^ 2 / 8 * (1 + cv)) := by ring
      linarith [hRe, hneg, hb1, hb2, hb3]

/-! ## The endgame: choosing the parameters

Balance with `α² = (16|σ|c)⁻¹`, detect at radius `Δ = (16√B)⁻¹` with clock
`T = ⌈2048√B⌉`, where `B = 1 + 16|σ|c²`. -/

section Endgame

variable [Nonempty σ]

private lemma card_pos : (0 : ℝ) < (Fintype.card σ : ℝ) := by
  exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty σ›

/-- **A dual solution of cost `c` is an algorithm**: error `1/16`, at most
`8192(1 + 4√|σ|·c)` queries. -/
theorem exists_algorithm_of_dualPairOn {c : ℝ} (P : DualPairOn read K f)
    (hP : P.IsCostLe c) (hc : 0 < c) :
    ∃ q ∈ QueryCounts read f (1 / 16),
      (q : ℝ) ≤ 8192 * (1 + 4 * Real.sqrt (Fintype.card σ) * c) := by
  have hσ : (0 : ℝ) < (Fintype.card σ : ℝ) := card_pos (σ := σ)
  -- the balancing scale
  set z : ℝ := 16 * (Fintype.card σ : ℝ) * c with hz
  have hz0 : 0 < z := by positivity
  have hα0 : Real.sqrt z ≠ 0 := by
    positivity
  set Q : DualPairOn read K f := P.scale (α := (Real.sqrt z)⁻¹)
    (inv_ne_zero hα0) with hQ
  have hαsq : ((Real.sqrt z)⁻¹) ^ 2 = z⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hz0.le]
  -- the balanced masses
  have hcu : ∀ x, ∑ i, ∑ k, Q.u x i k * Q.u x i k
      ≤ (16 * (Fintype.card σ : ℝ))⁻¹ := by
    intro x
    rw [hQ, DualPairOn.scale_u_mass, hαsq]
    have h1 : z⁻¹ * (∑ i, ∑ k, P.u x i k * P.u x i k) ≤ z⁻¹ * c :=
      mul_le_mul_of_nonneg_left (hP.1 x) (by positivity)
    calc z⁻¹ * (∑ i, ∑ k, P.u x i k * P.u x i k) ≤ z⁻¹ * c := h1
      _ = (16 * (Fintype.card σ : ℝ))⁻¹ := by
          rw [hz]
          field_simp
  have hcv : ∀ y, ∑ i, ∑ k, Q.v y i k * Q.v y i k
      ≤ 16 * (Fintype.card σ : ℝ) * c ^ 2 := by
    intro y
    rw [hQ, DualPairOn.scale_v_mass, inv_inv, Real.sq_sqrt hz0.le]
    have h1 : z * (∑ i, ∑ k, P.v y i k * P.v y i k) ≤ z * c :=
      mul_le_mul_of_nonneg_left (hP.2 y) hz0.le
    calc z * (∑ i, ∑ k, P.v y i k * P.v y i k) ≤ z * c := h1
      _ = 16 * (Fintype.card σ : ℝ) * c ^ 2 := by rw [hz]; ring
  -- the detection parameters
  set B : ℝ := 1 + 16 * (Fintype.card σ : ℝ) * c ^ 2 with hB
  have hB1 : (1 : ℝ) ≤ B := by
    rw [hB]
    nlinarith [hσ, sq_nonneg c]
  have hBs1 : (1 : ℝ) ≤ Real.sqrt B := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hB1
  have hBs0 : (0 : ℝ) < Real.sqrt B := lt_of_lt_of_le one_pos hBs1
  set T : ℕ := ⌈(2048 : ℝ) * Real.sqrt B⌉₊ with hTdef
  have hT : 0 < T := by
    rw [hTdef]
    exact Nat.ceil_pos.mpr (by positivity)
  have hTge : (2048 : ℝ) * Real.sqrt B ≤ (T : ℝ) := by
    rw [hTdef]; exact Nat.le_ceil _
  have hTle : (T : ℝ) ≤ 2048 * Real.sqrt B + 1 := by
    rw [hTdef]
    exact le_of_lt (Nat.ceil_lt_add_one (by positivity))
  set Δ : ℝ := (16 * Real.sqrt B)⁻¹ with hΔdef
  have hΔ : 0 < Δ := by rw [hΔdef]; positivity
  -- the two error-budget inequalities
  have hpos : 1 - (1 / 16 : ℝ)
      ≤ 1 / (1 + ((Fintype.card σ : ℝ) - 1) * (16 * (Fintype.card σ : ℝ))⁻¹) := by
    have hle : ((Fintype.card σ : ℝ) - 1) * (16 * (Fintype.card σ : ℝ))⁻¹
        ≤ 1 / 16 := by
      rw [div_eq_mul_inv, show ((Fintype.card σ : ℝ) - 1)
          * (16 * (Fintype.card σ : ℝ))⁻¹
          = (((Fintype.card σ : ℝ) - 1) / (Fintype.card σ : ℝ)) * 16⁻¹ from by
        rw [mul_inv]; ring]
      have h2 : ((Fintype.card σ : ℝ) - 1) / (Fintype.card σ : ℝ) ≤ 1 := by
        rw [div_le_one hσ]; linarith
      nlinarith [h2]
    have hden : (0 : ℝ) < 1 + ((Fintype.card σ : ℝ) - 1)
        * (16 * (Fintype.card σ : ℝ))⁻¹ := by
      have h0 : (0 : ℝ) ≤ ((Fintype.card σ : ℝ) - 1)
          * (16 * (Fintype.card σ : ℝ))⁻¹ := by
        have h1 : (1 : ℝ) ≤ (Fintype.card σ : ℝ) := by
          exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty σ›
        have : (0 : ℝ) ≤ (Fintype.card σ : ℝ) - 1 := by linarith
        positivity
      linarith
    rw [le_div_iff₀ hden]
    nlinarith [hle]
  have hsqB : Real.sqrt B * Real.sqrt B = B :=
    Real.mul_self_sqrt (by linarith)
  have hneg : Δ / 4 * Real.sqrt (1 + 16 * (Fintype.card σ : ℝ) * c ^ 2)
      + 2 / ((T : ℝ) * Δ) + Δ ^ 2 / 8
        * (1 + 16 * (Fintype.card σ : ℝ) * c ^ 2) ≤ 1 / 16 := by
    rw [← hB]
    have e1 : Δ / 4 * Real.sqrt B = 1 / 64 := by
      rw [hΔdef]
      field_simp
      linarith [hsqB]
    have e2 : Δ ^ 2 / 8 * B = 1 / 2048 := by
      rw [hΔdef, inv_pow, mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ B)]
      rw [show ((16 : ℝ) ^ 2 * B)⁻¹ / 8 * B = B / B * (2048 : ℝ)⁻¹ from by
        rw [mul_inv]; ring]
      rw [div_self (by linarith : B ≠ 0)]
      norm_num
    have e3 : 2 / ((T : ℝ) * Δ) ≤ 1 / 64 := by
      have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
      have hTΔval : (T : ℝ) * Δ = (T : ℝ) / (16 * Real.sqrt B) := by
        rw [hΔdef, div_eq_mul_inv]
      rw [hTΔval, div_div_eq_mul_div,
        div_le_div_iff₀ hT0 (by norm_num : (0 : ℝ) < 64)]
      calc 2 * (16 * Real.sqrt B) * 64 = 2048 * Real.sqrt B := by ring
        _ ≤ (T : ℝ) := hTge
        _ = 1 * (T : ℝ) := (one_mul _).symm
    linarith [e1, e2, e3]
  -- assemble
  have halg := scAlg_computes read f Q hT hΔ hcu hcv hpos hneg
  refine ⟨4 * (T - 1), mem_queryCounts halg, ?_⟩
  -- the query count, bounded
  have hT1 : ((4 * (T - 1) : ℕ) : ℝ) = 4 * ((T : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hT]
    norm_num
  have hBle : Real.sqrt B ≤ 1 + 4 * Real.sqrt (Fintype.card σ) * c := by
    have hsq : B ≤ (1 + 4 * Real.sqrt (Fintype.card σ) * c) ^ 2 := by
      have hs : Real.sqrt (Fintype.card σ) * Real.sqrt (Fintype.card σ)
          = (Fintype.card σ : ℝ) := Real.mul_self_sqrt hσ.le
      have hs0 : (0 : ℝ) ≤ Real.sqrt (Fintype.card σ) := Real.sqrt_nonneg _
      rw [hB]
      nlinarith [hs, hs0, hc.le]
    calc Real.sqrt B ≤ Real.sqrt ((1 + 4 * Real.sqrt (Fintype.card σ) * c) ^ 2) :=
        Real.sqrt_le_sqrt hsq
      _ = 1 + 4 * Real.sqrt (Fintype.card σ) * c := by
          rw [Real.sqrt_sq (by positivity)]
  rw [hT1]
  calc 4 * ((T : ℝ) - 1) ≤ 4 * (2048 * Real.sqrt B) := by linarith [hTle]
    _ = 8192 * Real.sqrt B := by ring
    _ ≤ 8192 * (1 + 4 * Real.sqrt (Fintype.card σ) * c) := by linarith [hBle]

/-- **The `qQueryOn` corollary**: `Q_{1/16}(f) ≤ 8192(1 + 4√|σ|·c)` for any
dual of cost `c`. -/
theorem qQueryOn_le_of_dualPairOn {c : ℝ} (P : DualPairOn read K f)
    (hP : P.IsCostLe c) (hc : 0 < c) :
    (qQueryOn read f (1 / 16) : ℝ)
      ≤ 8192 * (1 + 4 * Real.sqrt (Fintype.card σ) * c) := by
  obtain ⟨q, hq, hqle⟩ := exists_algorithm_of_dualPairOn read f P hP hc
  have h1 : qQueryOn read f (1 / 16) ≤ q := Nat.sInf_le hq
  have h2 : (qQueryOn read f (1 / 16) : ℝ) ≤ (q : ℝ) := by exact_mod_cast h1
  linarith [h2, hqle]

end Endgame

end QuantumQueryComplexity
