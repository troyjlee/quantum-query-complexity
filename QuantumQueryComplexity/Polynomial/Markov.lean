import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial

set_option linter.style.header false

/-!
# Markov's and Bernstein's inequalities for real polynomials

Derivative bounds for a real polynomial `p` of degree at most `d` that is bounded by `B` on an
interval:

* `abs_derivative_eval_one_le` (**Markov at the endpoint**): if `|P| ≤ 1` on `[-1, 1]` then
  `|P'(1)| ≤ d²`. This is Mathlib's Chebyshev extremal theorem
  (`Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one`, one derivative at
  `x = 1`) together with `T_d'(1) = d · U_{d-1}(1) = d²`, applied to `P` and `-P`.
* `abs_derivative_eval_le_markov` (**Markov on an interval**): if `|p| ≤ B` on `[α, β]` then
  `|p'(x)| ≤ 4 d² B / (β - α)` at every `x ∈ [α, β]`. The longer of `[α, x]` and `[x, β]` is
  mapped affinely onto `[-1, 1]` with `x ↦ 1`.
* `abs_derivative_eval_le_bernstein` (**Bernstein at the centre**): if `|p| ≤ B` on
  `[c - r, c + r]` then `|p'(c)| ≤ 3 d B / r`. Normalize to `c = 0`, `r = 1`, `B = 1` and write
  the odd part as `(P(y) - P(-y)) / 2 = y · S(y²)`, so `deg S = e ≤ (d - 1) / 2`,
  `|S(u)| ≤ 1 / √u` on `(0, 1]`, and `P'(0) = S(0)`. At a maximum point `u*` of `|S|` on
  `[0, 1]`, either `u* ≥ ε` and `|S(u*)| ≤ 1 / √ε`, or Markov on `[0, 1]` moves the value to
  `ε` at a cost of `4 ε e² max |S|`; `ε = 1 / (9 e²)` gives `max |S| ≤ 27 e / 5 ≤ 3 d`.

The constants `4` and `3` are not optimal (the sharp ones are `2` and `1`); they are what the
short proofs give, and they only enter explicit constants downstream.
-/

namespace QuantumQueryComplexity

open Polynomial

/-- **Markov's inequality at the endpoint.** A real polynomial of degree at most `d` bounded by
`1` on `[-1, 1]` has `|P'(1)| ≤ d²`. -/
theorem abs_derivative_eval_one_le {P : ℝ[X]} {d : ℕ} (hP : P.natDegree ≤ d)
    (hB : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1) :
    |P.derivative.eval 1| ≤ (d : ℝ) ^ 2 := by
  have hT : (Chebyshev.T ℝ (d : ℤ)).derivative.eval 1 = (d : ℝ) ^ 2 := by
    rw [Chebyshev.T_derivative_eq_U, eval_mul, Chebyshev.U_eval_one]
    simp
    ring
  have h1 := Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one (n := d) (k := 1)
    le_rfl (degree_le_of_natDegree_le hP) hB
  have h2 := Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one (n := d) (k := 1)
    (P := -P) le_rfl (degree_le_of_natDegree_le (by rw [natDegree_neg]; exact hP))
    (by simpa using hB)
  simp only [Function.iterate_one, derivative_neg, eval_neg] at h1 h2
  rw [hT] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- A polynomial bounded by `0` on a nondegenerate interval is zero. -/
private lemma eq_zero_of_abs_eval_le_zero {p : ℝ[X]} {α β : ℝ} (hαβ : α < β)
    (hB : ∀ x ∈ Set.Icc α β, |p.eval x| ≤ 0) : p = 0 :=
  p.eq_zero_of_infinite_isRoot <| (Set.Icc_infinite hαβ).mono fun x hx ↦
    abs_nonpos_iff.mp (hB x hx)

private lemma natDegree_rescale_le {p : ℝ[X]} {d : ℕ} (hp : p.natDegree ≤ d) (b a m : ℝ) :
    (C b * p.comp (C a * X + C m)).natDegree ≤ d := by
  refine (natDegree_C_mul_le _ _).trans (natDegree_comp_le.trans ?_)
  calc p.natDegree * (C a * X + C m).natDegree ≤ d * 1 :=
        Nat.mul_le_mul hp natDegree_linear_le
    _ = d := mul_one d

private lemma eval_rescale (p : ℝ[X]) (b a m t : ℝ) :
    (C b * p.comp (C a * X + C m)).eval t = b * p.eval (a * t + m) := by
  simp

private lemma eval_derivative_rescale (p : ℝ[X]) (b a m t : ℝ) :
    (C b * p.comp (C a * X + C m)).derivative.eval t =
      b * a * p.derivative.eval (a * t + m) := by
  simp [derivative_comp]
  ring

/-- Markov's inequality transported along an affine map `t ↦ a t + m`. -/
private lemma markov_affine {p : ℝ[X]} {d : ℕ} (hp : p.natDegree ≤ d) {B a m : ℝ} (hB : 0 < B)
    (hb : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |p.eval (a * t + m)| ≤ B) :
    |a| * |p.derivative.eval (a + m)| ≤ (d : ℝ) ^ 2 * B := by
  have hBi : 0 < B⁻¹ := inv_pos.mpr hB
  have h := abs_derivative_eval_one_le (natDegree_rescale_le hp B⁻¹ a m) fun t ht ↦ by
    rw [eval_rescale, abs_mul, abs_of_pos hBi, inv_mul_le_iff₀ hB, mul_one]
    exact hb t ht
  rw [eval_derivative_rescale, mul_one, abs_mul, abs_mul, abs_of_pos hBi, mul_assoc,
    inv_mul_le_iff₀ hB] at h
  linarith

/-- **Markov's inequality on an interval.** A real polynomial of degree at most `d` bounded by
`B` on `[α, β]` has `|p'(x)| ≤ 4 d² B / (β - α)` at every point of the interval. -/
theorem abs_derivative_eval_le_markov {p : ℝ[X]} {d : ℕ} (hp : p.natDegree ≤ d)
    {α β B : ℝ} (hαβ : α < β) (hB : ∀ x ∈ Set.Icc α β, |p.eval x| ≤ B)
    {x : ℝ} (hx : x ∈ Set.Icc α β) :
    |p.derivative.eval x| ≤ 4 * (d : ℝ) ^ 2 * B / (β - α) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x hx)
  rcases hB0.eq_or_lt with h | h
  · subst h
    rw [eq_zero_of_abs_eval_le_zero hαβ hB]
    simp
  obtain ⟨hx1, hx2⟩ := hx
  have hD := abs_nonneg (p.derivative.eval x)
  rw [le_div_iff₀ (sub_pos.mpr hαβ)]
  rcases le_total (β - x) (x - α) with hc | hc
  · have := markov_affine hp h (a := (x - α) / 2) (m := (x + α) / 2) fun t ht ↦
      hB _ ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩
    rw [show (x - α) / 2 + (x + α) / 2 = x by ring, abs_of_nonneg (by linarith)] at this
    nlinarith
  · have := markov_affine hp h (a := -((β - x) / 2)) (m := (β + x) / 2) fun t ht ↦
      hB _ ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩
    rw [show -((β - x) / 2) + (β + x) / 2 = x by ring, abs_neg,
      abs_of_nonneg (by linarith)] at this
    nlinarith

private lemma sum_range_two_mul (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n), f i = ∑ k ∈ Finset.range n, (f (2 * k) + f (2 * k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

/-- The odd part of `P`, written as `y · S(y²)`. -/
private noncomputable def oddPart (P : ℝ[X]) (d : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1), C (P.coeff (2 * k + 1)) * X ^ k

private lemma eval_zero_oddPart (P : ℝ[X]) (d : ℕ) : (oddPart P d).eval 0 = P.coeff 1 := by
  simp [oddPart, eval_finsetSum, Finset.sum_range_succ']

private lemma natDegree_oddPart_le {P : ℝ[X]} {d : ℕ} (hP : P.natDegree ≤ d) :
    (oddPart P d).natDegree ≤ (d - 1) / 2 := by
  refine natDegree_sum_le_of_forall_le _ _ fun k _ ↦ ?_
  by_cases hk : k ≤ (d - 1) / 2
  · exact (natDegree_C_mul_X_pow_le _ _).trans hk
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

private lemma two_mul_eval_oddPart {P : ℝ[X]} {d : ℕ} (hP : P.natDegree ≤ d) (y : ℝ) :
    2 * (y * (oddPart P d).eval (y ^ 2)) = P.eval y - P.eval (-y) := by
  have hlt : P.natDegree < 2 * (d + 1) := by omega
  rw [eval_eq_sum_range' hlt, eval_eq_sum_range' hlt, sum_range_two_mul, sum_range_two_mul,
    ← Finset.sum_sub_distrib, oddPart, eval_finsetSum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  rw [(even_two_mul k).neg_pow, (odd_two_mul_add_one k).neg_pow, pow_succ, pow_mul]
  ring

/-- If `|y · S(y²)| ≤ 1` on `[-1, 1]` and `deg S ≤ e` with `e ≥ 1`, then `|S(0)| ≤ 27 e / 5`. -/
private lemma abs_eval_zero_le_of_odd {S : ℝ[X]} {e : ℕ} (he : 1 ≤ e) (hS : S.natDegree ≤ e)
    (hb : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |y * S.eval (y ^ 2)| ≤ 1) :
    |S.eval 0| ≤ 27 * e / 5 := by
  have he0 : (1 : ℝ) ≤ e := by exact_mod_cast he
  set ε : ℝ := 1 / (9 * (e : ℝ) ^ 2) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one (by positivity)]
    nlinarith
  -- away from `0`, the bound `|y · S(y²)| ≤ 1` gives `|S| ≤ 3 e`
  have hhigh : ∀ u ∈ Set.Icc ε 1, |S.eval u| ≤ 3 * e := by
    intro u ⟨hu1, hu2⟩
    have hu0 : 0 < u := hε0.trans_le hu1
    have hy2 : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
    have hy0 : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
    have h := hb (Real.sqrt u) ⟨by linarith, Real.sqrt_le_one.mpr hu2⟩
    rw [hy2, abs_mul, abs_of_nonneg hy0] at h
    have h9 : 1 ≤ 9 * (e : ℝ) ^ 2 * u := by
      rw [hε, div_le_iff₀ (by positivity)] at hu1
      linarith
    have hsq : (Real.sqrt u * |S.eval u|) ^ 2 ≤ 1 :=
      pow_le_one₀ (mul_nonneg hy0 (abs_nonneg _)) h
    rw [mul_pow, hy2, sq_abs] at hsq
    apply abs_le_of_sq_le_sq _ (by positivity)
    nlinarith [mul_nonneg (sq_nonneg (S.eval u)) (sub_nonneg.mpr h9)]
  obtain ⟨u₀, hu₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr zero_le_one)
    (S.differentiable.continuous.abs.continuousOn (s := Set.Icc (0 : ℝ) 1))
  have hA : ∀ u ∈ Set.Icc (0 : ℝ) 1, |S.eval u| ≤ |S.eval u₀| := fun u hu ↦ by
    simpa using hmax hu
  have hAle : |S.eval u₀| ≤ 27 * e / 5 := by
    rcases le_or_gt ε u₀ with h | h
    · linarith [hhigh u₀ ⟨h, hu₀.2⟩]
    · have hder : ∀ u ∈ Set.Icc (0 : ℝ) 1,
          ‖deriv (fun u ↦ S.eval u) u‖ ≤ 4 * (e : ℝ) ^ 2 * |S.eval u₀| := fun u hu ↦ by
        rw [Polynomial.deriv, Real.norm_eq_abs]
        simpa using abs_derivative_eval_le_markov hS zero_lt_one hA hu
      have hmvt := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
        (fun u _ ↦ S.differentiableAt) hder hu₀ ⟨hε0.le, hε1⟩
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr h)] at hmvt
      have hSε := hhigh ε ⟨le_rfl, hε1⟩
      have hcost : 4 * (e : ℝ) ^ 2 * |S.eval u₀| * ε = 4 * |S.eval u₀| / 9 := by
        rw [hε]
        field_simp
      have htri : |S.eval u₀| ≤ |S.eval ε| + |S.eval ε - S.eval u₀| := by
        have := abs_sub_abs_le_abs_sub (S.eval u₀) (S.eval ε)
        rw [abs_sub_comm] at this
        linarith
      nlinarith [abs_nonneg (S.eval u₀), hu₀.1]
  exact (hA 0 ⟨le_rfl, zero_le_one⟩).trans hAle

/-- Bernstein's inequality at `0` for a polynomial bounded by `1` on `[-1, 1]`. -/
private lemma abs_derivative_eval_zero_le {P : ℝ[X]} {d : ℕ} (hP : P.natDegree ≤ d)
    (hb : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ 1) :
    |P.derivative.eval 0| ≤ 3 * d := by
  rw [← coeff_zero_eq_eval_zero, coeff_derivative, zero_add, Nat.cast_zero, zero_add,
    mul_one]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hSb : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |y * (oddPart P d).eval (y ^ 2)| ≤ 1 := by
    intro y ⟨hy1, hy2⟩
    have h := two_mul_eval_oddPart hP y
    have h1 := hb y ⟨hy1, hy2⟩
    have h2 := hb (-y) ⟨by linarith, by linarith⟩
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  rw [← eval_zero_oddPart P d]
  rcases Nat.eq_zero_or_pos ((d - 1) / 2) with he | he
  · have hc := eq_C_of_natDegree_le_zero ((natDegree_oddPart_le hP).trans he.le)
    have h1 := hSb 1 ⟨by norm_num, le_rfl⟩
    rw [hc, eval_C] at h1 ⊢
    rw [one_mul] at h1
    linarith
  · have h := abs_eval_zero_le_of_odd he (natDegree_oddPart_le hP) hSb
    have h2 : (2 * ((d - 1) / 2) + 1 : ℕ) ≤ d := by omega
    have h2' : 2 * (((d - 1) / 2 : ℕ) : ℝ) + 1 ≤ d := by exact_mod_cast h2
    linarith

/-- **Bernstein's inequality at the centre.** A real polynomial of degree at most `d` bounded by
`B` on `[c - r, c + r]` has `|p'(c)| ≤ 3 d B / r`. -/
theorem abs_derivative_eval_le_bernstein {p : ℝ[X]} {d : ℕ} (hp : p.natDegree ≤ d)
    {c r B : ℝ} (hr : 0 < r) (hB : ∀ x ∈ Set.Icc (c - r) (c + r), |p.eval x| ≤ B) :
    |p.derivative.eval c| ≤ 3 * (d : ℝ) * B / r := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB c ⟨by linarith, by linarith⟩)
  rcases hB0.eq_or_lt with h | h
  · subst h
    rw [eq_zero_of_abs_eval_le_zero (by linarith) hB]
    simp
  have hBi : 0 < B⁻¹ := inv_pos.mpr h
  have key := abs_derivative_eval_zero_le (natDegree_rescale_le hp B⁻¹ r c) fun t ht ↦ by
    rw [eval_rescale, abs_mul, abs_of_pos hBi, inv_mul_le_iff₀ h, mul_one]
    exact hB _ ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩
  rw [eval_derivative_rescale, mul_zero, zero_add, abs_mul, abs_mul, abs_of_pos hBi,
    abs_of_pos hr, mul_assoc, inv_mul_le_iff₀ h] at key
  rw [le_div_iff₀ hr]
  linarith

end QuantumQueryComplexity
