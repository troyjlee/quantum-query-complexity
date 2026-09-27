import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Field.GeomSum

set_option linter.style.header false
set_option maxRecDepth 4000

/-!
# The outer scan's cost

The dyadic slots of `LDS/Outer.lean` carry
per-block costs `nodeCost L (block size) ≤ C · L · (2^(s+1))^{2/3}`, and the
weighted scan charges `16 √(∑ c²)`.  The sum to bound is

    ∑_{s ≤ L} ⌈n / 2^(s+1)⌉ · (2^(s+1))^{4/3}
      ≤ n · ∑_s (2^(s+1))^{1/3}  +  ∑_s (2^(s+1))^{4/3},

two geometric series with ratios `2^{1/3}` and `2^{4/3}`.  **Both are dominated
by their last term** — that is the whole point of the dyadic decomposition:
a crude "largest term times the number of scales" bound would cost an extra
`√L`, turning the headline `n^{2/3} log n` into `n^{2/3} log^{3/2} n`, which is
worse than the paper's `n^{2/3} log n log log n`.

With `2 ^ L ≤ 2 n` the last terms are `O(n^{1/3})` and `O(n^{4/3})`, so the sum
is `O(n^{4/3})` and the scan costs `O(C · L · n^{2/3})`.
-/

namespace QuantumQueryComplexity

/-! ## Powers and roots -/

/-- Taking a natural power commutes with taking a real power. -/
lemma pow_rpow_comm {a : ℝ} (ha : 0 ≤ a) (k : ℕ) (r : ℝ) :
    ((a ^ k : ℝ)) ^ r = (a ^ r) ^ k := by
  rw [← Real.rpow_natCast a k, ← Real.rpow_mul ha, ← Real.rpow_natCast (a ^ r) k,
    ← Real.rpow_mul ha, mul_comm]

/-- `5/4 ≤ 2^{1/3}`, since `(5/4)^3 = 125/64 ≤ 2`. -/
lemma five_quarters_le_two_rpow_third : (5 : ℝ) / 4 ≤ (2 : ℝ) ^ ((1 : ℝ) / 3) := by
  have hcube : ((125 : ℝ) / 64) ^ ((1 : ℝ) / 3) = 5 / 4 := by
    rw [show (125 : ℝ) / 64 = (5 / 4) ^ ((3 : ℕ) : ℝ) by
      rw [Real.rpow_natCast]; norm_num,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5 / 4)]
    norm_num
  calc (5 : ℝ) / 4 = ((125 : ℝ) / 64) ^ ((1 : ℝ) / 3) := hcube.symm
    _ ≤ (2 : ℝ) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)

lemma one_lt_two_rpow_third : (1 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 3) := by
  have := five_quarters_le_two_rpow_third
  linarith

lemma two_rpow_four_third_eq : (2 : ℝ) ^ ((4 : ℝ) / 3)
    = 2 * (2 : ℝ) ^ ((1 : ℝ) / 3) := by
  rw [show (4 : ℝ) / 3 = 1 + (1 : ℝ) / 3 by ring, Real.rpow_add (by norm_num),
    Real.rpow_one]

lemma one_lt_two_rpow_four_third : (1 : ℝ) < (2 : ℝ) ^ ((4 : ℝ) / 3) := by
  rw [two_rpow_four_third_eq]
  have := five_quarters_le_two_rpow_third
  linarith

/-! ## The geometric bound -/

/-- A geometric series with ratio `x > 1` is dominated by its last term over
`x - 1`. -/
lemma geom_bound {x : ℝ} (hx : 1 < x) (L : ℕ) :
    ∑ s ∈ Finset.range (L + 1), x ^ (s + 1) ≤ x ^ (L + 2) / (x - 1) := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hsub : 0 < x - 1 := by linarith
  have hfac : ∑ s ∈ Finset.range (L + 1), x ^ (s + 1)
      = x * ∑ s ∈ Finset.range (L + 1), x ^ s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hkey : x * (x ^ (L + 1) - 1) ≤ x ^ (L + 2) := by
    have hpow : x * x ^ (L + 1) = x ^ (L + 2) := by ring
    nlinarith
  calc ∑ s ∈ Finset.range (L + 1), x ^ (s + 1)
      = x * ((x ^ (L + 1) - 1) / (x - 1)) := by
        rw [hfac, geom_sum_eq (ne_of_gt hx)]
    _ = (x * (x ^ (L + 1) - 1)) / (x - 1) := by ring
    _ ≤ x ^ (L + 2) / (x - 1) := by gcongr

/-- The `1/3`-series over the dyadic scales. -/
lemma sum_third_le (L : ℕ) :
    ∑ s ∈ Finset.range (L + 1), (((2 : ℝ) ^ (s + 1))) ^ ((1 : ℝ) / 3)
      ≤ 4 * ((2 : ℝ) ^ (L + 2)) ^ ((1 : ℝ) / 3) := by
  have hcomm : ∀ k : ℕ, (((2 : ℝ) ^ k)) ^ ((1 : ℝ) / 3)
      = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ k := fun k =>
    pow_rpow_comm (by norm_num) k _
  have hx := one_lt_two_rpow_third
  have hquart : (1 : ℝ) / 4 ≤ (2 : ℝ) ^ ((1 : ℝ) / 3) - 1 := by
    have := five_quarters_le_two_rpow_third
    linarith
  have hsub : 0 < (2 : ℝ) ^ ((1 : ℝ) / 3) - 1 := by linarith
  have hgeom := geom_bound hx L
  have hpos : (0 : ℝ) ≤ ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ (L + 2) := by positivity
  calc ∑ s ∈ Finset.range (L + 1), (((2 : ℝ) ^ (s + 1))) ^ ((1 : ℝ) / 3)
      = ∑ s ∈ Finset.range (L + 1), ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ (s + 1) :=
        Finset.sum_congr rfl fun s _ => hcomm (s + 1)
    _ ≤ ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ (L + 2) / ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1) := hgeom
    _ ≤ 4 * ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ (L + 2) := by
        rw [div_le_iff₀ hsub]
        nlinarith
    _ = 4 * ((2 : ℝ) ^ (L + 2)) ^ ((1 : ℝ) / 3) := by rw [hcomm (L + 2)]

/-- The `4/3`-series over the dyadic scales. -/
lemma sum_four_third_le (L : ℕ) :
    ∑ s ∈ Finset.range (L + 1), (((2 : ℝ) ^ (s + 1))) ^ ((4 : ℝ) / 3)
      ≤ 2 * ((2 : ℝ) ^ (L + 2)) ^ ((4 : ℝ) / 3) := by
  have hcomm : ∀ k : ℕ, (((2 : ℝ) ^ k)) ^ ((4 : ℝ) / 3)
      = ((2 : ℝ) ^ ((4 : ℝ) / 3)) ^ k := fun k =>
    pow_rpow_comm (by norm_num) k _
  have hx := one_lt_two_rpow_four_third
  have hhalf : (1 : ℝ) / 2 ≤ (2 : ℝ) ^ ((4 : ℝ) / 3) - 1 := by
    rw [two_rpow_four_third_eq]
    have := five_quarters_le_two_rpow_third
    linarith
  have hsub : 0 < (2 : ℝ) ^ ((4 : ℝ) / 3) - 1 := by linarith
  have hgeom := geom_bound hx L
  have hpos : (0 : ℝ) ≤ ((2 : ℝ) ^ ((4 : ℝ) / 3)) ^ (L + 2) := by positivity
  calc ∑ s ∈ Finset.range (L + 1), (((2 : ℝ) ^ (s + 1))) ^ ((4 : ℝ) / 3)
      = ∑ s ∈ Finset.range (L + 1), ((2 : ℝ) ^ ((4 : ℝ) / 3)) ^ (s + 1) :=
        Finset.sum_congr rfl fun s _ => hcomm (s + 1)
    _ ≤ ((2 : ℝ) ^ ((4 : ℝ) / 3)) ^ (L + 2) / ((2 : ℝ) ^ ((4 : ℝ) / 3) - 1) := hgeom
    _ ≤ 2 * ((2 : ℝ) ^ ((4 : ℝ) / 3)) ^ (L + 2) := by
        rw [div_le_iff₀ hsub]
        nlinarith
    _ = 2 * ((2 : ℝ) ^ (L + 2)) ^ ((4 : ℝ) / 3) := by rw [hcomm (L + 2)]

/-! ## The combined bound -/

lemma eight_rpow_third : ((8 : ℝ)) ^ ((1 : ℝ) / 3) = 2 := by
  rw [show (8 : ℝ) = 2 ^ ((3 : ℕ) : ℝ) by rw [Real.rpow_natCast]; norm_num,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma eight_rpow_four_third : ((8 : ℝ)) ^ ((4 : ℝ) / 3) = 16 := by
  rw [show (8 : ℝ) = 2 ^ ((3 : ℕ) : ℝ) by rw [Real.rpow_natCast]; norm_num,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show ((3 : ℕ) : ℝ) * ((4 : ℝ) / 3) = ((4 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]
  norm_num

/-- **The outer scan's cost sum.**  Over the dyadic scales, the slot costs
squared add up to `O(n^{4/3})` — so the scan itself costs `O(n^{2/3})` times
the per-node constant.  The hypothesis `2^(L+2) ≤ 8n` is what `L = ⌈log₂ n⌉`
provides. -/
theorem outer_sum_le {n L : ℕ} (hn : 1 ≤ n) (hL : (2 : ℕ) ^ (L + 2) ≤ 8 * n) :
    ∑ s ∈ Finset.range (L + 1),
        ((n : ℝ) * (((2 : ℝ) ^ (s + 1))) ^ ((1 : ℝ) / 3)
          + (((2 : ℝ) ^ (s + 1))) ^ ((4 : ℝ) / 3))
      ≤ 40 * (n : ℝ) ^ ((4 : ℝ) / 3) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h8 : ((2 : ℝ) ^ (L + 2)) ≤ 8 * (n : ℝ) := by exact_mod_cast hL
  have hn3 : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hnpos.le _
  have hn43 : (0 : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 3) := Real.rpow_nonneg hnpos.le _
  -- the two last terms, in terms of `n`
  have hc1 : ((2 : ℝ) ^ (L + 2)) ^ ((1 : ℝ) / 3) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 3) := by
    calc ((2 : ℝ) ^ (L + 2)) ^ ((1 : ℝ) / 3)
        ≤ (8 * (n : ℝ)) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (by positivity) h8 (by norm_num)
      _ = 2 * (n : ℝ) ^ ((1 : ℝ) / 3) := by
          rw [Real.mul_rpow (by norm_num) hnpos.le, eight_rpow_third]
  have hc2 : ((2 : ℝ) ^ (L + 2)) ^ ((4 : ℝ) / 3) ≤ 16 * (n : ℝ) ^ ((4 : ℝ) / 3) := by
    calc ((2 : ℝ) ^ (L + 2)) ^ ((4 : ℝ) / 3)
        ≤ (8 * (n : ℝ)) ^ ((4 : ℝ) / 3) :=
          Real.rpow_le_rpow (by positivity) h8 (by norm_num)
      _ = 16 * (n : ℝ) ^ ((4 : ℝ) / 3) := by
          rw [Real.mul_rpow (by norm_num) hnpos.le, eight_rpow_four_third]
  have hsplit : (n : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 3) = (n : ℝ) ^ ((4 : ℝ) / 3) := by
    rw [show (4 : ℝ) / 3 = 1 + (1 : ℝ) / 3 by ring, Real.rpow_add hnpos, Real.rpow_one]
  have h1 := sum_third_le L
  have h2 := sum_four_third_le L
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  nlinarith

end QuantumQueryComplexity
