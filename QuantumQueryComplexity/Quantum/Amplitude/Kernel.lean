import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.Floor.Semiring
set_option linter.style.header false

/-!
# The phase-estimation kernel and its concentration

For a clock of size `M` and a phase offset `δ`, the amplitude of phase estimation is

    peKernel M δ = (1/M) · ∑_{c<M} exp(2πi·c·δ).

This file is pure analysis (no quantum model):

* `peKernel_add_int`: the kernel is `1`-periodic; `peKernel_int`: it is `1` at integers;
* `circDist δ = |δ − round δ|`, the circular distance of `δ` to `0` modulo one;
* `normSq_peKernel_le`: away from the grid, `|k(δ)|² ≤ 1/(4·M²·d²)`, `d = circDist δ > 0`
  — from the geometric sum and `sin(πd) ≥ 2d` on `[0, 1/2]`.  The quotient is never formed
  without `d > 0`;
* `sum_inv_sq_Icc_le`: the telescoping tail `∑_{k=4}^{N} 1/k² ≤ 1/3`;
* `bad_mass_le`: for any phase `φ`, the grid points `y/M` at circular distance more than
  `4/M` from `φ` carry total kernel mass at most `1/6`.

The last statement needs no normalization; combined with Parseval (`Fourier.lean`) it gives
`Pr[circDist(φ − y/M) ≤ 4/M] ≥ 3/4`.
-/

namespace QuantumQueryComplexity

open Finset

/-! ## `e(t) = exp(2πi t)` -/

/-- `e(t) = exp(2πi·t)`. -/
noncomputable def cexp1 (t : ℝ) : ℂ := Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))

lemma cexp1_add (s t : ℝ) : cexp1 (s + t) = cexp1 s * cexp1 t := by
  rw [cexp1, cexp1, cexp1, ← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] lemma cexp1_zero : cexp1 0 = 1 := by simp [cexp1]

lemma cexp1_int (n : ℤ) : cexp1 n = 1 := by
  rw [cexp1, Complex.exp_eq_one_iff]
  exact ⟨n, by push_cast; ring⟩

lemma cexp1_add_int (t : ℝ) (n : ℤ) : cexp1 (t + n) = cexp1 t := by
  rw [cexp1_add, cexp1_int, mul_one]

lemma norm_cexp1 (t : ℝ) : ‖cexp1 t‖ = 1 := by
  rw [cexp1, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

lemma cexp1_nat_mul (c : ℕ) (t : ℝ) : cexp1 (c * t) = cexp1 t ^ c := by
  rw [cexp1, cexp1, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma star_cexp1 (t : ℝ) : star (cexp1 t) = cexp1 (-t) := by
  rw [cexp1, cexp1, Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal]
  congr 1
  push_cast
  ring

/-- `‖e(t) − 1‖ = 2·|sin(πt)|`. -/
lemma norm_cexp1_sub_one (t : ℝ) : ‖cexp1 t - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
  rw [cexp1, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2),
    show 2 * Real.pi * t / 2 = Real.pi * t by ring]

/-! ## Circular distance -/

/-- The circular distance of `δ` to `0` modulo one. -/
noncomputable def circDist (δ : ℝ) : ℝ := |δ - round δ|

lemma circDist_nonneg (δ : ℝ) : 0 ≤ circDist δ := abs_nonneg _

lemma circDist_le_half (δ : ℝ) : circDist δ ≤ 1 / 2 := abs_sub_round δ

/-- `|sin(πδ)| ≥ 2·circDist δ`. -/
lemma two_mul_circDist_le_abs_sin (δ : ℝ) : 2 * circDist δ ≤ |Real.sin (Real.pi * δ)| := by
  set u := δ - round δ with hu
  have hδ : Real.pi * δ = Real.pi * u + (round δ : ℤ) * Real.pi := by rw [hu]; ring
  rw [hδ, Real.sin_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul,
    circDist]
  have hu2 : |u| ≤ 1 / 2 := abs_sub_round δ
  have key : ∀ v : ℝ, 0 ≤ v → v ≤ 1 / 2 → 2 * v ≤ Real.sin (Real.pi * v) := by
    intro v h0 h1
    have h := Real.mul_le_sin (x := Real.pi * v) (by positivity)
      (by nlinarith [Real.pi_pos])
    have hpi : 2 / Real.pi * (Real.pi * v) = 2 * v := by field_simp
    linarith
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg h] at hu2 ⊢
    exact (key u h hu2).trans (le_abs_self _)
  · rw [abs_of_nonpos h] at hu2 ⊢
    have := key (-u) (by linarith) hu2
    rw [show Real.pi * -u = -(Real.pi * u) by ring, Real.sin_neg] at this
    exact this.trans (neg_le_abs _)

/-! ## The kernel -/

/-- The phase-estimation kernel. -/
noncomputable def peKernel (M : ℕ) (δ : ℝ) : ℂ :=
  (1 / (M : ℂ)) * ∑ c ∈ range M, cexp1 (c * δ)

lemma peKernel_add_int (M : ℕ) (δ : ℝ) (n : ℤ) : peKernel M (δ + n) = peKernel M δ := by
  rw [peKernel, peKernel]
  congr 1
  refine sum_congr rfl fun c _ => ?_
  rw [mul_add, show (c : ℝ) * (n : ℝ) = ((c * n : ℤ) : ℝ) by push_cast; ring, cexp1_add_int]

lemma peKernel_int {M : ℕ} (hM : 0 < M) (n : ℤ) : peKernel M n = 1 := by
  have h := peKernel_add_int M 0 n
  rw [zero_add] at h
  rw [h, peKernel]
  simp only [mul_zero, cexp1_zero, sum_const, card_range, nsmul_eq_mul, mul_one]
  have : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp

/-- **The tail bound**: `|k(δ)|² ≤ 1/(4·M²·d²)` for `d = circDist δ > 0`. -/
theorem normSq_peKernel_le {M : ℕ} (hM : 0 < M) {δ : ℝ} (hd : 0 < circDist δ) :
    Complex.normSq (peKernel M δ) ≤ 1 / (4 * (M : ℝ) ^ 2 * circDist δ ^ 2) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  set z := cexp1 δ with hz
  have hgeom : (∑ c ∈ range M, cexp1 (c * δ)) * (z - 1) = z ^ M - 1 := by
    rw [← geom_sum_mul]
    congr 1
    exact sum_congr rfl fun c _ => cexp1_nat_mul c δ
  have hden : 4 * circDist δ ≤ ‖z - 1‖ := by
    rw [hz, norm_cexp1_sub_one]
    have := two_mul_circDist_le_abs_sin δ
    linarith
  have hnum : ‖z ^ M - 1‖ ≤ 2 := by
    calc ‖z ^ M - 1‖ ≤ ‖z ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz, norm_cexp1, one_pow, norm_one]; norm_num
  have hsum : ‖∑ c ∈ range M, cexp1 (c * δ)‖ ≤ 1 / (2 * circDist δ) := by
    have h1 : ‖∑ c ∈ range M, cexp1 (c * δ)‖ * ‖z - 1‖ ≤ 2 := by
      rw [← norm_mul, hgeom]; exact hnum
    rw [le_div_iff₀ (by positivity)]
    nlinarith [norm_nonneg (∑ c ∈ range M, cexp1 (c * δ))]
  have hk : ‖peKernel M δ‖ ≤ 1 / (2 * M * circDist δ) := by
    rw [peKernel, norm_mul, norm_div, norm_one, Complex.norm_natCast]
    calc 1 / (M : ℝ) * ‖∑ c ∈ range M, cexp1 (c * δ)‖
        ≤ 1 / (M : ℝ) * (1 / (2 * circDist δ)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 1 / (2 * M * circDist δ) := by field_simp
  rw [Complex.normSq_eq_norm_sq]
  calc ‖peKernel M δ‖ ^ 2 ≤ (1 / (2 * M * circDist δ)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hk 2
    _ = 1 / (4 * (M : ℝ) ^ 2 * circDist δ ^ 2) := by ring

/-! ## The telescoping tail -/

lemma sum_inv_sq_Icc_le_aux : ∀ N : ℕ, 3 ≤ N →
    ∑ k ∈ Icc 4 N, 1 / ((k : ℕ) : ℝ) ^ 2 ≤ 1 / 3 - 1 / (N : ℝ) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
      rw [sum_Icc_succ_top (by omega)]
      have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
      have hstep : 1 / (((N + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / (N : ℝ) - 1 / ((N + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      linarith

/-- `∑_{k=4}^{N} 1/k² ≤ 1/3`. -/
theorem sum_inv_sq_Icc_le (N : ℕ) : ∑ k ∈ Icc 4 N, 1 / ((k : ℕ) : ℝ) ^ 2 ≤ 1 / 3 := by
  rcases Nat.lt_or_ge N 3 with h | h
  · rw [Icc_eq_empty (by omega), sum_empty]; norm_num
  · have := sum_inv_sq_Icc_le_aux N h
    have hN : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have : 0 ≤ 1 / (N : ℝ) := by positivity
    linarith

/-- A finite family of reals `> 4`, bounded by `N`, with pairwise distinct integer parts:
the sum of their inverse squares is at most `1/3`. -/
theorem sum_inv_sq_le {α : Type*} (B : Finset α) (v : α → ℝ) (N : ℕ)
    (hv : ∀ y ∈ B, 4 < v y ∧ v y ≤ N)
    (hinj : ∀ y ∈ B, ∀ y' ∈ B, ⌊v y⌋₊ = ⌊v y'⌋₊ → y = y') :
    ∑ y ∈ B, 1 / v y ^ 2 ≤ 1 / 3 := by
  have hfl : ∀ y ∈ B, 4 ≤ ⌊v y⌋₊ ∧ ⌊v y⌋₊ ≤ N ∧ ((⌊v y⌋₊ : ℕ) : ℝ) ≤ v y := by
    intro y hy
    have h4 := (hv y hy).1
    have h0 : 0 ≤ v y := by linarith
    refine ⟨Nat.le_floor (by push_cast; linarith), ?_, Nat.floor_le h0⟩
    exact Nat.floor_le_of_le (hv y hy).2
  calc ∑ y ∈ B, 1 / v y ^ 2 ≤ ∑ y ∈ B, 1 / ((⌊v y⌋₊ : ℕ) : ℝ) ^ 2 := by
        refine sum_le_sum fun y hy => ?_
        obtain ⟨h4, -, hle⟩ := hfl y hy
        have hpos : (0 : ℝ) < ((⌊v y⌋₊ : ℕ) : ℝ) := by
          exact_mod_cast (by omega : 0 < ⌊v y⌋₊)
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hpos.le hle 2)
    _ = ∑ k ∈ B.image (fun y => ⌊v y⌋₊), 1 / ((k : ℕ) : ℝ) ^ 2 := by
        rw [sum_image]
        exact fun y hy y' hy' h => hinj y hy y' hy' h
    _ ≤ ∑ k ∈ Icc 4 N, 1 / ((k : ℕ) : ℝ) ^ 2 := by
        refine sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => by positivity
        intro k hk
        obtain ⟨y, hy, rfl⟩ := mem_image.mp hk
        exact mem_Icc.mpr ⟨(hfl y hy).1, (hfl y hy).2.1⟩
    _ ≤ 1 / 3 := sum_inv_sq_Icc_le N

/-! ## The mass far from the phase -/

/-- The signed grid offset of `y` from the phase `φ`, in grid units: `M·(δ − round δ)`,
`δ = φ − y/M`. -/
noncomputable def gridOffset (M : ℕ) (φ : ℝ) (y : ℕ) : ℝ :=
  (M : ℝ) * ((φ - y / M) - round (φ - y / M))

lemma abs_gridOffset (M : ℕ) (φ : ℝ) (y : ℕ) :
    |gridOffset M φ y| = M * circDist (φ - y / M) := by
  rw [gridOffset, abs_mul, abs_of_nonneg (Nat.cast_nonneg M), circDist]

/-- Offsets of two grid points differ by an integer, which vanishes only for equal points. -/
lemma eq_of_abs_gridOffset_sub_lt {M : ℕ} (hM : 0 < M) (φ : ℝ) {y y' : ℕ} (hy : y < M)
    (hy' : y' < M) (h : |gridOffset M φ y - gridOffset M φ y'| < 1) : y = y' := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  set r := round (φ - y / M) with hr
  set r' := round (φ - y' / M) with hr'
  have hdiff : gridOffset M φ y - gridOffset M φ y'
      = (((y' : ℤ) - y + M * (r' - r) : ℤ) : ℝ) := by
    have e1 : (M : ℝ) * ((y : ℝ) / M) = y := by field_simp
    have e2 : (M : ℝ) * ((y' : ℝ) / M) = y' := by field_simp
    rw [gridOffset, gridOffset]
    push_cast
    linear_combination (-1 : ℝ) * e1 + e2
  rw [hdiff, ← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at h
  have hdvd : (M : ℤ) ∣ ((y' : ℤ) - y) := ⟨r - r', by linarith⟩
  have habs : |(y' : ℤ) - y| < M := by
    rw [abs_lt]; constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hdvd habs
  omega

/-- **The kernel mass far from the phase is at most `1/6`.** -/
theorem bad_mass_le {M : ℕ} (hM : 0 < M) (φ : ℝ) :
    ∑ y ∈ (range M).filter (fun y : ℕ => 4 / (M : ℝ) < circDist (φ - (y : ℝ) / M)),
      Complex.normSq (peKernel M (φ - (y : ℝ) / M)) ≤ 1 / 6 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  set B := (range M).filter (fun y : ℕ => 4 / (M : ℝ) < circDist (φ - (y : ℝ) / M)) with hB
  have hmem : ∀ y ∈ B, y < M ∧ 4 < |gridOffset M φ y| := by
    intro y hy
    obtain ⟨h1, h2⟩ := mem_filter.mp hy
    refine ⟨mem_range.mp h1, ?_⟩
    rw [abs_gridOffset]
    rw [div_lt_iff₀ hM'] at h2
    linarith
  -- each bad term is at most `1/(4·u²)`
  have hterm : ∀ y ∈ B, Complex.normSq (peKernel M (φ - y / M))
      ≤ (1 / 4) * (1 / gridOffset M φ y ^ 2) := by
    intro y hy
    have h4 := (hmem y hy).2
    have hd : 0 < circDist (φ - y / M) := by
      rw [abs_gridOffset] at h4
      by_contra hcon
      have : circDist (φ - y / M) = 0 := le_antisymm (not_lt.mp hcon) (circDist_nonneg _)
      rw [this, mul_zero] at h4
      linarith
    refine (normSq_peKernel_le hM hd).trans (le_of_eq ?_)
    rw [← sq_abs (gridOffset M φ y), abs_gridOffset]
    field_simp
  have hbound : ∀ y ∈ B, |gridOffset M φ y| ≤ M := by
    intro y _
    rw [abs_gridOffset]
    have := circDist_le_half (φ - y / M)
    nlinarith
  -- split by the sign of the offset
  set Bp := B.filter (fun y => 0 < gridOffset M φ y) with hBp
  set Bn := B.filter (fun y => ¬ 0 < gridOffset M φ y) with hBn
  have hsplit : ∑ y ∈ B, 1 / gridOffset M φ y ^ 2
      = ∑ y ∈ Bp, 1 / gridOffset M φ y ^ 2 + ∑ y ∈ Bn, 1 / gridOffset M φ y ^ 2 :=
    (sum_filter_add_sum_filter_not B _ _).symm
  have hp : ∑ y ∈ Bp, 1 / gridOffset M φ y ^ 2 ≤ 1 / 3 := by
    refine sum_inv_sq_le Bp (gridOffset M φ) M ?_ ?_
    · intro y hy
      obtain ⟨hyB, hpos⟩ := mem_filter.mp hy
      have h4 := (hmem y hyB).2
      have hb := hbound y hyB
      rw [abs_of_pos hpos] at h4 hb
      exact ⟨h4, hb⟩
    · intro y hy y' hy' hfl
      obtain ⟨hyB, hpos⟩ := mem_filter.mp hy
      obtain ⟨hyB', hpos'⟩ := mem_filter.mp hy'
      refine eq_of_abs_gridOffset_sub_lt hM φ (hmem y hyB).1 (hmem y' hyB').1 ?_
      have h1 := Nat.floor_le hpos.le
      have h2 := Nat.lt_floor_add_one (gridOffset M φ y)
      have h3 := Nat.floor_le hpos'.le
      have h4 := Nat.lt_floor_add_one (gridOffset M φ y')
      rw [hfl] at h1 h2
      rw [abs_lt]; constructor <;> linarith
  have hn : ∑ y ∈ Bn, 1 / gridOffset M φ y ^ 2 ≤ 1 / 3 := by
    have hrew : ∑ y ∈ Bn, 1 / gridOffset M φ y ^ 2 = ∑ y ∈ Bn, 1 / (-gridOffset M φ y) ^ 2 :=
      sum_congr rfl fun y _ => by rw [neg_sq]
    rw [hrew]
    have hneg : ∀ y ∈ Bn, y ∈ B ∧ gridOffset M φ y < 0 := by
      intro y hy
      obtain ⟨hyB, hnp⟩ := mem_filter.mp hy
      have h4 := (hmem y hyB).2
      refine ⟨hyB, lt_of_le_of_ne (not_lt.mp hnp) fun h0 => ?_⟩
      rw [h0, abs_zero] at h4
      linarith
    refine sum_inv_sq_le Bn (fun y => -gridOffset M φ y) M ?_ ?_
    · intro y hy
      obtain ⟨hyB, hlt⟩ := hneg y hy
      have h4 := (hmem y hyB).2
      have hb := hbound y hyB
      rw [abs_of_neg hlt] at h4 hb
      exact ⟨h4, hb⟩
    · intro y hy y' hy' hfl
      obtain ⟨hyB, hlt⟩ := hneg y hy
      obtain ⟨hyB', hlt'⟩ := hneg y' hy'
      refine eq_of_abs_gridOffset_sub_lt hM φ (hmem y hyB).1 (hmem y' hyB').1 ?_
      have h1 := Nat.floor_le (neg_pos.mpr hlt).le
      have h2 := Nat.lt_floor_add_one (-gridOffset M φ y)
      have h3 := Nat.floor_le (neg_pos.mpr hlt').le
      have h4 := Nat.lt_floor_add_one (-gridOffset M φ y')
      rw [hfl] at h1 h2
      rw [abs_lt]; constructor <;> linarith
  calc ∑ y ∈ B, Complex.normSq (peKernel M (φ - y / M))
      ≤ ∑ y ∈ B, (1 / 4) * (1 / gridOffset M φ y ^ 2) := sum_le_sum hterm
    _ = (1 / 4) * ∑ y ∈ B, 1 / gridOffset M φ y ^ 2 := by rw [mul_sum]
    _ ≤ (1 / 4) * (1 / 3 + 1 / 3) := by rw [hsplit]; gcongr
    _ = 1 / 6 := by norm_num

end QuantumQueryComplexity
