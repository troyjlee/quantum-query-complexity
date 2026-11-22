import QuantumQueryComplexity.Polynomial.Markov
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Algebra.Polynomial

set_option linter.style.header false

/-!
# Polynomials bounded on an integer grid

Two explicit special cases of Paturi's theorem (R. Paturi, *On the degree of polynomials that
approximate symmetric Boolean functions*, STOC 1992), in the forms used by the polynomial-method
lower bound for the collision problem (S. Kutin, *Quantum lower bound for the collision problem
with small range*, Theory of Computing 1 (2005), Theorem 2.1 and Section 3). Paturi's theorem is
cited there with unspecified constants; here the constants are explicit.

* `sq_natDegree_ge_of_endpoint_jump` (**a jump at the end of the grid**): if `|p(i)| ≤ B` at the
  integers `1 ≤ i ≤ K` and `|p(2) - p(1)| ≥ c > 0`, then
  `min ((K - 1) / 4, c (K - 1) / (8 B)) ≤ (deg p)²`. Proof: at a maximum point of `|p|` on
  `[1, K]`, the nearest integer is within `1/2`, so Markov's inequality gives `max |p| ≤ 2 B`
  once `4 d² ≤ K - 1`; the jump over `[1, 2]` then forces `c ≤ 8 d² B / (K - 1)`.
* `natDegree_ge_of_center_bump` (**a bump near the centre**): if `|p(i)| ≤ 1` at the integers
  `0 ≤ i ≤ L` and `|p(ξ)| ≥ 5` at a real `ξ` within `2` of `L / 2`, then `L ≤ 2000 · deg p`.
  The degree is **linear** in `L`, which an endpoint argument cannot give. Proof: suppose
  `d < L / 2000` (so `L > 2000`, as `d ≥ 1`). Lagrange interpolation at `0, …, d` bounds
  `|p| ≤ B₀ = (2L)^d / d!` on `[0, L]`, and `B₀ ≤ 4^m` for `m = ⌈L / 128⌉` (using
  `d! ≥ (d/3)^d`). The damped polynomial `q = p · W^m` with `W(x) = 4x(L - x)/L²` is at most `1`
  at the integers and on the outer sixteenths of `[0, L]` (where `W ≤ 1/4`); elsewhere
  Bernstein's inequality at the centre (`abs_derivative_eval_le_bernstein`, radius
  `L/16 - 1/2`) moves a maximum of `|q|` to an integer, as `3 (d + 2m) ≤ L/16 - 1/2`; so
  `|q| ≤ 2` on `[0, L]`, and `W(ξ)^m ≥ 1 - 16 m / L² ≥ 1/2` gives `|p(ξ)| ≤ 4`.
-/

namespace QuantumQueryComplexity

open Polynomial

/-- Mean value bound: if `|q'| ≤ C` between `x` and `y`, then `|q(y) - q(x)| ≤ C |y - x|`. -/
private lemma abs_eval_sub_le_of_deriv {q : ℝ[X]} {x y C : ℝ}
    (h : ∀ z ∈ Set.uIcc x y, |q.derivative.eval z| ≤ C) :
    |q.eval y - q.eval x| ≤ C * |y - x| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun t => q.eval t)
    (fun z _ => q.differentiableAt) (fun z hz => by simpa [Polynomial.deriv] using h z hz)
    (convex_uIcc x y) Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using this

/-- `|q|` attains its maximum on a nonempty closed interval. -/
private lemma exists_max_abs_eval (q : ℝ[X]) {a b : ℝ} (hab : a ≤ b) :
    ∃ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |q.eval y| ≤ |q.eval x| := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hab)
    q.continuous.abs.continuousOn
  exact ⟨x, hx, fun y hy => hmax hy⟩

/-- A point of `[a, b]` (`a, b` natural) is within `1/2` of an integer of `[a, b]`. -/
private lemma exists_nat_near {a b : ℕ} {x : ℝ} (ha : (a : ℝ) ≤ x) (hb : x ≤ b) :
    ∃ i : ℕ, a ≤ i ∧ i ≤ b ∧ |x - i| ≤ 1 / 2 := by
  have hx0 : 0 ≤ x + 1 / 2 := by linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
  refine ⟨⌊x + 1 / 2⌋₊, Nat.le_floor (by linarith), ?_, ?_⟩
  · have : ⌊x + 1 / 2⌋₊ < b + 1 := (Nat.floor_lt hx0).2 (by push_cast; linarith)
    omega
  · have h1 := Nat.floor_le hx0
    have h2 := Nat.lt_floor_add_one (x + 1 / 2)
    rw [abs_le]
    constructor <;> linarith

/-- If `|q'| ≤ |q(x)|` between `x` and an integer `i` with `|x - i| ≤ 1/2` and `|q(i)| ≤ A`,
then `|q(x)| ≤ 2 A`. -/
private lemma abs_eval_le_two_mul {q : ℝ[X]} {x : ℝ} {i : ℕ} {A : ℝ}
    (hi : |q.eval (i : ℝ)| ≤ A) (hxi : |x - i| ≤ 1 / 2)
    (hder : ∀ y ∈ Set.uIcc x (i : ℝ), |q.derivative.eval y| ≤ |q.eval x|) :
    |q.eval x| ≤ 2 * A := by
  have h := abs_eval_sub_le_of_deriv hder
  have h2 : |(i : ℝ) - x| ≤ 1 / 2 := by rwa [abs_sub_comm]
  have h3 := abs_sub_abs_le_abs_sub (q.eval x) (q.eval (i : ℝ))
  rw [abs_sub_comm] at h3
  nlinarith [mul_le_mul_of_nonneg_left h2 (abs_nonneg (q.eval x))]

/-- `∏_{k < n} |n - k| = n!`. -/
private lemma prod_abs_sub_range (n : ℕ) :
    ∏ k ∈ Finset.range n, |(n : ℝ) - k| = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ', Nat.factorial_succ]
    have : ∀ k ∈ Finset.range n, |((n + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)| = |(n : ℝ) - k| := by
      intro k _; push_cast; ring_nf
    rw [Finset.prod_congr rfl this, ih]
    push_cast
    rw [sub_zero, abs_of_pos (by positivity)]
    ring

/-- `∏_{k ≤ d, k ≠ j} |j - k| = j! (d - j)!`. -/
private lemma prod_abs_sub_erase {d j : ℕ} (hj : j ≤ d) :
    ∏ k ∈ (Finset.range (d + 1)).erase j, |(j : ℝ) - k| =
      j.factorial * (d - j).factorial := by
  induction d, hj using Nat.le_induction with
  | base =>
    rw [Finset.range_add_one, Finset.erase_insert Finset.notMem_range_self, prod_abs_sub_range]
    simp
  | succ d hjd ih =>
    rw [Finset.range_add_one (n := d + 1), Finset.erase_insert_of_ne (by omega),
      Finset.prod_insert (by simp), ih, show d + 1 - j = (d - j) + 1 by omega,
      Nat.factorial_succ]
    have hjd' : (j : ℝ) ≤ d := by exact_mod_cast hjd
    rw [abs_of_nonpos (by push_cast; linarith)]
    push_cast [Nat.cast_sub hjd]
    ring

/-- Lagrange interpolation at `0, …, d`: a polynomial of degree `≤ d` bounded by `1` at these
nodes satisfies `|p(x)| ≤ (2L)^d / d!` for `x ∈ [0, L]` when `d ≤ L`. -/
private lemma abs_eval_le_lagrange {p : ℝ[X]} {d : ℕ} (hd : p.natDegree ≤ d) {L : ℝ}
    (hdL : (d : ℝ) ≤ L) (hB : ∀ j : ℕ, j ≤ d → |p.eval (j : ℝ)| ≤ 1) {x : ℝ} (hx0 : 0 ≤ x)
    (hxL : x ≤ L) : |p.eval x| ≤ (2 * L) ^ d / d.factorial := by
  set s := Finset.range (d + 1)
  have hinj : Set.InjOn (fun k : ℕ => (k : ℝ)) s := Nat.cast_injective.injOn
  have hdeg : p.degree < s.card := by
    rw [Finset.card_range]
    exact (degree_le_natDegree).trans_lt (by exact_mod_cast Nat.lt_succ_of_le hd)
  rw [Lagrange.eq_interpolate hinj hdeg, Lagrange.interpolate_apply, eval_finsetSum]
  have hterm : ∀ j ∈ s, |eval x (C (eval (j : ℝ) p) * Lagrange.basis s (fun k : ℕ => (k : ℝ)) j)|
      ≤ L ^ d / d.factorial * (d.choose j : ℝ) := by
    intro j hj
    have hjd : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [eval_mul, eval_C, abs_mul, Lagrange.basis, eval_prod, Finset.abs_prod,
      Nat.cast_choose ℝ hjd]
    have hprod : ∏ k ∈ s.erase j, |eval x (Lagrange.basisDivisor (j : ℝ) (k : ℝ))| ≤
        ∏ k ∈ s.erase j, (L / |(j : ℝ) - k|) := by
      refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun k hk => ?_)
      have hkd : (k : ℝ) ≤ d := by
        have := Finset.mem_range.mp (Finset.mem_of_mem_erase hk)
        exact_mod_cast Nat.lt_succ_iff.mp this
      rw [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X, eval_C, abs_mul, abs_inv,
        inv_mul_eq_div]
      gcongr
      rw [abs_le]
      constructor <;> linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_erase_of_mem hj,
      Finset.card_range, Nat.add_sub_cancel, prod_abs_sub_erase hjd] at hprod
    have hpj : |eval (j : ℝ) p| ≤ 1 := hB j hjd
    calc |eval (j : ℝ) p| * ∏ k ∈ s.erase j, |eval x (Lagrange.basisDivisor (j : ℝ) (k : ℝ))|
        ≤ 1 * (L ^ d / (j.factorial * (d - j).factorial)) :=
          mul_le_mul hpj hprod (Finset.prod_nonneg fun _ _ => abs_nonneg _) zero_le_one
      _ = L ^ d / d.factorial * (d.factorial / (j.factorial * (d - j).factorial)) := by
          field_simp
  calc |∑ j ∈ s, eval x (C (eval (j : ℝ) p) * Lagrange.basis s (fun k : ℕ => (k : ℝ)) j)|
      ≤ ∑ j ∈ s, L ^ d / d.factorial * (d.choose j : ℝ) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = (2 * L) ^ d / d.factorial := by
        rw [← Finset.mul_sum]
        have : (∑ j ∈ s, (d.choose j : ℝ)) = 2 ^ d := by exact_mod_cast Nat.sum_range_choose d
        rw [this, mul_pow]
        ring

/-- `768 (n + 1) ≤ 4^n` for `n ≥ 15`. -/
private lemma nat_four_pow_ge {n : ℕ} (hn : 15 ≤ n) : 768 * (n + 1) ≤ 4 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n _ ih => rw [pow_succ]; omega

/-- If `2000 d < L` and `m ≥ L / 128`, then `(2L)^d / d! ≤ 4^m`. -/
private lemma crude_le_four_pow {d : ℕ} {L : ℝ} (hd : 1 ≤ d) (hL : 2000 * d < L) {m : ℕ}
    (hm : L / 128 ≤ m) : (2 * L) ^ d / d.factorial ≤ 4 ^ m := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hLpos : 0 < L := by linarith
  set n := ⌊L / (128 * d)⌋₊
  have hn15 : 15 ≤ n := Nat.le_floor (by rw [le_div_iff₀ (by positivity)]; push_cast; linarith)
  have hn_lt : L / (128 * d) < n + 1 := Nat.lt_floor_add_one _
  have hnd : n * d ≤ m := by
    have h1 : (n : ℝ) * d ≤ L / 128 := by
      have := Nat.floor_le (a := L / (128 * d)) (by positivity)
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    exact_mod_cast h1.trans hm
  have h4n : (768 : ℝ) * (n + 1) ≤ 4 ^ n := by exact_mod_cast nat_four_pow_ge hn15
  have h6L : 6 * L ≤ d * 4 ^ n := by
    rw [div_lt_iff₀ (by positivity)] at hn_lt
    nlinarith [mul_le_mul_of_nonneg_left h4n hdpos.le]
  have hfact : (d : ℝ) ^ d ≤ 3 ^ d * d.factorial := by
    have h := Real.pow_div_factorial_le_exp (x := d) hdpos.le d
    have he : Real.exp d ≤ 3 ^ d := by
      rw [← Real.exp_one_pow]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le (Real.exp_one_lt_d9.le.trans (by norm_num)) d
    rw [div_le_iff₀ (by positivity)] at h
    nlinarith [Nat.factorial_pos d]
  have h1 : (6 * L) ^ d ≤ (d * 4 ^ n) ^ d := pow_le_pow_left₀ (by positivity) h6L d
  have h2 : ((4 : ℝ) ^ n) ^ d ≤ 4 ^ m := by
    rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) hnd
  rw [div_le_iff₀ (by positivity)]
  have h3 : (3 : ℝ) ^ d * (2 * L) ^ d ≤ 3 ^ d * (d.factorial * 4 ^ m) := by
    calc (3 : ℝ) ^ d * (2 * L) ^ d = (6 * L) ^ d := by rw [← mul_pow]; ring
      _ ≤ (d * 4 ^ n) ^ d := h1
      _ = d ^ d * (4 ^ n) ^ d := mul_pow _ _ _
      _ ≤ (3 ^ d * d.factorial) * 4 ^ m :=
          mul_le_mul hfact h2 (by positivity) (by positivity)
      _ = 3 ^ d * (d.factorial * 4 ^ m) := by ring
  have := le_of_mul_le_mul_left h3 (by positivity)
  linarith

/-- **Paturi's theorem, endpoint form.** A real polynomial bounded by `B` at the integers
`1, …, K` (`K ≥ 2`) whose values at `1` and `2` differ by at least `c > 0` has
`min ((K - 1) / 4, c (K - 1) / (8 B)) ≤ (deg p)²`. -/
theorem sq_natDegree_ge_of_endpoint_jump {p : ℝ[X]} {K : ℕ} (hK : 2 ≤ K) {B c : ℝ}
    (hc : 0 < c) (hB : ∀ i : ℕ, 1 ≤ i → i ≤ K → |p.eval (i : ℝ)| ≤ B)
    (hjump : c ≤ |p.eval 2 - p.eval 1|) :
    min (((K : ℝ) - 1) / 4) (c * ((K : ℝ) - 1) / (8 * B)) ≤ (p.natDegree : ℝ) ^ 2 := by
  set d := p.natDegree
  have hB0 : 0 < B := by
    have h1 := hB 1 le_rfl (by omega)
    have h2 := hB 2 (by norm_num) hK
    push_cast at h1 h2
    have := abs_sub (p.eval 2) (p.eval 1)
    linarith
  have h2K : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) < K := by linarith
  by_cases hcase : ((K : ℝ) - 1) / 4 ≤ (d : ℝ) ^ 2
  · exact min_le_of_left_le hcase
  push Not at hcase
  have hdK : 4 * (d : ℝ) ^ 2 ≤ K - 1 := by linarith
  apply min_le_of_right_le
  obtain ⟨xs, hxs, hmax⟩ := exists_max_abs_eval p hK1.le
  have hM0 : 0 ≤ |p.eval xs| := abs_nonneg _
  have hmark : ∀ y ∈ Set.Icc (1 : ℝ) K,
      |p.derivative.eval y| ≤ 4 * (d : ℝ) ^ 2 * |p.eval xs| / (K - 1) :=
    fun y hy => abs_derivative_eval_le_markov le_rfl hK1 hmax hy
  have hmark' : 4 * (d : ℝ) ^ 2 * |p.eval xs| / (K - 1) ≤ |p.eval xs| := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  obtain ⟨i, hi1, hiK, hi⟩ := exists_nat_near (a := 1) (b := K) (by simpa using hxs.1) hxs.2
  have hM : |p.eval xs| ≤ 2 * B := by
    refine abs_eval_le_two_mul (hB i hi1 hiK) hi (fun y hy => (hmark y ?_).trans hmark')
    exact Set.uIcc_subset_Icc hxs ⟨by exact_mod_cast hi1, by exact_mod_cast hiK⟩ hy
  have hjump' : |p.eval 2 - p.eval 1| ≤ 4 * (d : ℝ) ^ 2 * |p.eval xs| / (K - 1) * |2 - 1| := by
    refine abs_eval_sub_le_of_deriv fun z hz => hmark z ?_
    rw [Set.uIcc_of_le (by norm_num)] at hz
    exact ⟨hz.1, hz.2.trans h2K⟩
  have hc' : c ≤ 4 * (d : ℝ) ^ 2 * (2 * B) / (K - 1) := by
    calc c ≤ 4 * (d : ℝ) ^ 2 * |p.eval xs| / (K - 1) * |2 - 1| := hjump.trans hjump'
      _ = 4 * (d : ℝ) ^ 2 * |p.eval xs| / (K - 1) := by norm_num
      _ ≤ 4 * (d : ℝ) ^ 2 * (2 * B) / (K - 1) := by gcongr
  rw [le_div_iff₀ (by linarith)] at hc'
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **Paturi's theorem, centre form.** A real polynomial bounded by `1` at the integers
`0, …, L` that reaches absolute value `5` at a real point within `2` of `L / 2` has degree at
least `L / 2000`. -/
theorem natDegree_ge_of_center_bump {p : ℝ[X]} {L : ℕ}
    (hB : ∀ i : ℕ, i ≤ L → |p.eval (i : ℝ)| ≤ 1) {ξ : ℝ} (hξ : |ξ - (L : ℝ) / 2| ≤ 2)
    (hbig : 5 ≤ |p.eval ξ|) : (L : ℝ) ≤ 2000 * p.natDegree := by
  set d := p.natDegree
  by_contra hcon
  push Not at hcon
  have hd1 : 1 ≤ d := by
    by_contra h0
    have hpC := eq_C_of_natDegree_eq_zero (show p.natDegree = 0 by omega)
    have h1 := hB 0 (Nat.zero_le _)
    rw [hpC, eval_C] at h1 hbig
    linarith
  have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hL : (2000 : ℝ) < L := by linarith
  have hLpos : (0 : ℝ) < L := by linarith
  have hconN : 2000 * d < L := by exact_mod_cast hcon
  set m := ⌈(L : ℝ) / 128⌉₊
  have hm1 : (L : ℝ) / 128 ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) < L / 128 + 1 := Nat.ceil_lt_add_one (by positivity)
  -- the crude bound `|p| ≤ 4 ^ m` on `[0, L]`
  have hcrude : ∀ x ∈ Set.Icc (0 : ℝ) L, |p.eval x| ≤ 4 ^ m := fun x hx =>
    (abs_eval_le_lagrange le_rfl (by exact_mod_cast (by omega : d ≤ L))
      (fun j hj => hB j (by omega)) hx.1 hx.2).trans (crude_le_four_pow hd1 hcon hm1)
  -- the damping factor `W(x) = 4 x (L - x) / L²`
  set W : ℝ[X] := C (4 / (L : ℝ) ^ 2) * (X * (C (L : ℝ) - X))
  have hWeval : ∀ x, W.eval x = 4 * (x * (L - x)) / L ^ 2 := fun x => by
    simp only [W, eval_mul, eval_C, eval_X, eval_sub]
    ring
  have hWdeg : W.natDegree ≤ 2 := by
    simp only [W]
    compute_degree
  have hW0 : ∀ x ∈ Set.Icc (0 : ℝ) L, 0 ≤ W.eval x := fun x hx => by
    rw [hWeval]
    apply div_nonneg _ (by positivity)
    nlinarith [hx.1, hx.2]
  have hW1 : ∀ x, W.eval x ≤ 1 := fun x => by
    rw [hWeval, div_le_one (by positivity)]
    nlinarith [sq_nonneg (2 * x - L)]
  have hWout : ∀ x ∈ Set.Icc (0 : ℝ) L, (x ≤ L / 16 ∨ 15 * L / 16 ≤ x) →
      W.eval x ≤ 1 / 4 := by
    intro x hx hout
    rw [hWeval, div_le_iff₀ (by positivity)]
    rcases hout with h | h <;> nlinarith [hx.1, hx.2]
  -- the damped polynomial `q = p W^m`
  set q := p * W ^ m
  have hqeval : ∀ x, q.eval x = p.eval x * W.eval x ^ m := fun x => by
    simp only [q, eval_mul, eval_pow]
  have hqdeg : q.natDegree ≤ d + 2 * m :=
    natDegree_mul_le.trans (add_le_add le_rfl
      ((natDegree_pow_le.trans (Nat.mul_le_mul_left m hWdeg)).trans (by omega)))
  have hqint : ∀ i : ℕ, i ≤ L → |q.eval (i : ℝ)| ≤ 1 := by
    intro i hi
    have hi' : (i : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨Nat.cast_nonneg i, by exact_mod_cast hi⟩
    rw [hqeval, abs_mul, abs_pow, abs_of_nonneg (hW0 _ hi')]
    calc |p.eval (i : ℝ)| * W.eval (i : ℝ) ^ m ≤ 1 * 1 :=
          mul_le_mul (hB i hi) (pow_le_one₀ (hW0 _ hi') (hW1 _)) (pow_nonneg (hW0 _ hi') _)
            zero_le_one
      _ = 1 := one_mul 1
  have hqout : ∀ x ∈ Set.Icc (0 : ℝ) L, (x ≤ L / 16 ∨ 15 * L / 16 ≤ x) →
      |q.eval x| ≤ 1 := by
    intro x hx hout
    rw [hqeval, abs_mul, abs_pow, abs_of_nonneg (hW0 _ hx)]
    calc |p.eval x| * W.eval x ^ m ≤ 4 ^ m * (1 / 4) ^ m :=
          mul_le_mul (hcrude x hx) (pow_le_pow_left₀ (hW0 _ hx) (hWout x hx hout) m)
            (pow_nonneg (hW0 _ hx) _) (by positivity)
      _ = 1 := by rw [← mul_pow]; norm_num
  -- a maximum point of `|q|` on `[0, L]`
  obtain ⟨xs, hxs, hmax⟩ := exists_max_abs_eval q hLpos.le
  have hM2 : |q.eval xs| ≤ 2 := by
    by_cases hout : xs ≤ L / 16 ∨ 15 * L / 16 ≤ xs
    · linarith [hqout xs hxs hout]
    push Not at hout
    obtain ⟨i, -, hiL, hi⟩ := exists_nat_near (a := 0) (b := L) (by simpa using hxs.1) hxs.2
    have hr : (0 : ℝ) < L / 16 - 1 / 2 := by linarith
    have hDr : 3 * ((d + 2 * m : ℕ) : ℝ) ≤ L / 16 - 1 / 2 := by
      have hdL : (d : ℝ) < L / 2000 := by linarith
      push_cast
      linarith
    have key : ∀ y ∈ Set.uIcc xs (i : ℝ), |q.derivative.eval y| ≤ |q.eval xs| := by
      intro y hy
      have hy' : |y - xs| ≤ 1 / 2 :=
        (Set.abs_sub_left_of_mem_uIcc hy).trans (by rwa [abs_sub_comm])
      rw [abs_le] at hy'
      refine (abs_derivative_eval_le_bernstein hqdeg (c := y) hr (B := |q.eval xs|)
        fun z hz => hmax z ⟨by linarith [hz.1], by linarith [hz.2]⟩).trans ?_
      rw [div_le_iff₀ hr]
      nlinarith [mul_le_mul_of_nonneg_left hDr (abs_nonneg (q.eval xs))]
    linarith [abs_eval_le_two_mul (hqint i hiL) hi key]
  -- evaluate at `ξ`
  rw [abs_le] at hξ
  have hξI : ξ ∈ Set.Icc (0 : ℝ) L := ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
  have hqξ : |q.eval ξ| ≤ 2 := (hmax ξ hξI).trans hM2
  have hWξ : 1 + (-16 / (L : ℝ) ^ 2) ≤ W.eval ξ := by
    have : W.eval ξ = 1 - (2 * ξ - L) ^ 2 / (L : ℝ) ^ 2 := by
      rw [hWeval]
      field_simp
      ring
    rw [this, neg_div, ← sub_eq_add_neg]
    gcongr
    nlinarith [hξ.1, hξ.2]
  have hWξm : 1 / 2 ≤ W.eval ξ ^ m := by
    have h16 : -2 ≤ -16 / (L : ℝ) ^ 2 := by
      rw [neg_div, neg_le_neg_iff, div_le_iff₀ (by positivity)]
      nlinarith
    have hbern := one_add_mul_le_pow h16 m
    have hm16 : (m : ℝ) * (-16 / (L : ℝ) ^ 2) ≥ -(1 / 2) := by
      rw [mul_div_assoc', ge_iff_le, le_div_iff₀ (by positivity)]
      nlinarith
    have h1a : 0 ≤ 1 + (-16 / (L : ℝ) ^ 2) := by
      rw [neg_div, ← sub_eq_add_neg, sub_nonneg, div_le_one (by positivity)]
      nlinarith
    have hpow : (1 + (-16 / (L : ℝ) ^ 2)) ^ m ≤ W.eval ξ ^ m :=
      pow_le_pow_left₀ h1a hWξ m
    linarith
  rw [hqeval, abs_mul, abs_pow, abs_of_nonneg (hW0 _ hξI)] at hqξ
  nlinarith [mul_le_mul hbig hWξm (by norm_num) (abs_nonneg (p.eval ξ))]

end QuantumQueryComplexity
