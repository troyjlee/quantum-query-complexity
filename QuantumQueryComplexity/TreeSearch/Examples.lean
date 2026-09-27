import QuantumQueryComplexity.TreeSearch.Optimal

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The recursive cost on three shapes of tree

* a **chain** (every vertex has at most one child): `C_v = ∑_{w ∈ subtree of v} t_w`;
* a **star** (the children of the root are leaves): `C_ρ = t_ρ + √(∑_{u child} t_u²)`;
* a **perfect binary tree** of depth `d` with unit costs (every vertex of depth `< d` has two
  children, every vertex of depth `d` none): `C_v = ∑_{i ≤ d − depth v} (√2)^i`, so
  `C_ρ = ∑_{h=0}^d (√2)^h`, and with `N = 2^{d+1} − 1` vertices `C_ρ ≤ 3√N` — against the
  generic depth bound `√((d+1)·N)`.

All three are stated for an `AncTree` satisfying the shape hypotheses; no particular
representation of the vertices is imported.
-/

namespace QuantumQueryComplexity

namespace AncTree

open Finset

variable {V : Type} [DecidableEq V] [Fintype V] (T : AncTree V)

/-- **A chain costs the sum of its weights.** -/
theorem recCost_chain {t : V → ℝ} (ht : ∀ v, 0 ≤ t v) (hchain : ∀ v, (T.children v).card ≤ 1)
    (v : V) : T.recCost t v = ∑ w ∈ T.descendants v, t w := by
  induction v using T.induction_children with
  | step v ih =>
    rw [T.sum_descendants v, recCost_eq]
    congr 1
    rcases Finset.card_le_one_iff_subsingleton.1 (hchain v) |> fun _ =>
        (Nat.le_one_iff_eq_zero_or_eq_one.1 (hchain v)) with h0 | h1
    · rw [Finset.card_eq_zero.1 h0, sum_empty, sum_empty, Real.sqrt_zero]
    · obtain ⟨u, hu⟩ := Finset.card_eq_one.1 h1
      rw [hu, sum_singleton, sum_singleton, ih u (by rw [hu]; exact mem_singleton_self u)]
      refine Real.sqrt_sq (Finset.sum_nonneg fun w _ => ht w)

/-- **A star**: root cost plus the root of the sum of the squared leaf costs. -/
theorem recCost_star (t : V → ℝ) {ρ : V} (hleaf : ∀ u ∈ T.children ρ, T.children u = ∅) :
    T.recCost t ρ = t ρ + Real.sqrt (∑ u ∈ T.children ρ, t u ^ 2) := by
  rw [recCost_eq]
  congr 2
  exact Finset.sum_congr rfl fun u hu => by rw [T.recCost_leaf (hleaf u hu)]

/-- The geometric sum `∑_{i ≤ n} (√2)^i`. -/
noncomputable def sqrtTwoSum (n : ℕ) : ℝ := ∑ i ∈ Finset.range (n + 1), Real.sqrt 2 ^ i

lemma sqrtTwoSum_succ (n : ℕ) : sqrtTwoSum (n + 1) = 1 + Real.sqrt 2 * sqrtTwoSum n := by
  rw [sqrtTwoSum, sqrtTwoSum, Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_succ, pow_zero]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **A perfect binary tree with unit costs**: `C_v = ∑_{i ≤ d − depth v} (√2)^i`. -/
theorem recCost_binary {d : ℕ} (hd : ∀ v, T.depth v ≤ d)
    (htwo : ∀ v, T.depth v < d → (T.children v).card = 2)
    (hleaf : ∀ v, T.depth v = d → T.children v = ∅) (v : V) :
    T.recCost (fun _ => (1 : ℝ)) v = sqrtTwoSum (d - T.depth v) := by
  induction v using T.induction_children with
  | step v ih =>
    rw [recCost_eq]
    rcases Nat.lt_or_ge (T.depth v) d with hlt | hge
    · obtain ⟨m, hm⟩ : ∃ m, d - T.depth v = m + 1 := ⟨d - T.depth v - 1, by omega⟩
      rw [hm, sqrtTwoSum_succ]
      congr 1
      have hval : ∀ u ∈ T.children v, T.recCost (fun _ => (1 : ℝ)) u ^ 2 = sqrtTwoSum m ^ 2 :=
        fun u hu => by rw [ih u hu, T.depth_child hu, show d - (T.depth v + 1) = m by omega]
      rw [Finset.sum_congr rfl hval, sum_const, htwo v hlt, nsmul_eq_mul, Nat.cast_ofNat,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq]
      exact Finset.sum_nonneg fun i _ => pow_nonneg (Real.sqrt_nonneg 2) i
    · have h0 : d - T.depth v = 0 := by omega
      rw [h0, hleaf v (le_antisymm (hd v) hge), sum_empty, Real.sqrt_zero, add_zero]
      simp [sqrtTwoSum]

lemma sqrtTwoSum_le (n : ℕ) : sqrtTwoSum n ≤ (Real.sqrt 2 + 1) * Real.sqrt 2 ^ (n + 1) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  -- geometric sum: (√2 − 1)·∑_{i ≤ n} √2^i = √2^{n+1} − 1
  have hgeom : (Real.sqrt 2 - 1) * sqrtTwoSum n = Real.sqrt 2 ^ (n + 1) - 1 := by
    rw [sqrtTwoSum, Finset.mul_sum]
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hinv : (Real.sqrt 2 - 1) * (Real.sqrt 2 + 1) = 1 := by nlinarith
  have hpos : 0 < Real.sqrt 2 - 1 := by linarith
  have hpow : 0 ≤ Real.sqrt 2 ^ (n + 1) := by positivity
  have : sqrtTwoSum n = (Real.sqrt 2 + 1) * (Real.sqrt 2 ^ (n + 1) - 1) := by
    have := congrArg (fun z => (Real.sqrt 2 + 1) * z) hgeom
    rw [← mul_assoc, mul_comm (Real.sqrt 2 + 1), hinv, one_mul] at this
    exact this
  rw [this]
  nlinarith

/-- **`C_ρ ≤ 3√N`** on the perfect binary tree, `N = 2^{d+1} − 1`. -/
theorem sqrtTwoSum_le_three_sqrt (d : ℕ) :
    sqrtTwoSum d ≤ 3 * Real.sqrt ((2 : ℝ) ^ (d + 1) - 1) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hle : Real.sqrt 2 ≤ 71 / 50 := by
    rw [show (71 / 50 : ℝ) = Real.sqrt ((71 / 50) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [sqrtTwoSum, zero_add, Finset.sum_range_one, pow_zero]
    norm_num
  · have h1 := sqrtTwoSum_le d
    have hpow : Real.sqrt 2 ^ (d + 1) = Real.sqrt ((2 : ℝ) ^ (d + 1)) := by
      symm
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← pow_add, ← two_mul,
        pow_mul, hs]
    have hN : (2 : ℝ) ^ (d + 1) ≤ (3 / 2) * ((2 : ℝ) ^ (d + 1) - 1) := by
      have : (4 : ℝ) ≤ (2 : ℝ) ^ (d + 1) := by
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (d + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have hsqN : Real.sqrt ((2 : ℝ) ^ (d + 1))
        ≤ Real.sqrt (3 / 2) * Real.sqrt ((2 : ℝ) ^ (d + 1) - 1) := by
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt hN
    have hs32 : Real.sqrt (3 / 2) ≤ 123 / 100 := by
      rw [show (123 / 100 : ℝ) = Real.sqrt ((123 / 100) ^ 2) from
        (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hN0 : 0 ≤ Real.sqrt ((2 : ℝ) ^ (d + 1) - 1) := Real.sqrt_nonneg _
    have hB : Real.sqrt ((2 : ℝ) ^ (d + 1)) ≤ (123 / 100) * Real.sqrt ((2 : ℝ) ^ (d + 1) - 1) :=
      hsqN.trans (mul_le_mul_of_nonneg_right hs32 hN0)
    have hA : Real.sqrt 2 + 1 ≤ 121 / 50 := by linarith
    calc sqrtTwoSum d ≤ (Real.sqrt 2 + 1) * Real.sqrt 2 ^ (d + 1) := h1
      _ = (Real.sqrt 2 + 1) * Real.sqrt ((2 : ℝ) ^ (d + 1)) := by rw [hpow]
      _ ≤ (121 / 50) * ((123 / 100) * Real.sqrt ((2 : ℝ) ^ (d + 1) - 1)) :=
          mul_le_mul hA hB (Real.sqrt_nonneg _) (by norm_num)
      _ ≤ 3 * Real.sqrt ((2 : ℝ) ^ (d + 1) - 1) := by linarith

end AncTree

end QuantumQueryComplexity
