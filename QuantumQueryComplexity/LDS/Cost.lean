import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option linter.style.header false
set_option maxRecDepth 8000

/-!
# The cost function of the node recursion

A node of arena size `m` pays for `3 + 2h` anchors and for the
maximum of its `h` children:

    D(m) = (3 + 2h) · g_L(m) + 16 √(h+1) · D(m'),   m' ≤ 2m/h + 2,

with `g_L(m) = L · 8 m^{2/3}` the anchor cost and `L` the binary-search depth
(`m ≤ 2^L`).  The base case `m ≤ h` is the read-everything dual, of cost `2m`.

**Carrying `L` rather than recomputing it** is what keeps this arithmetic
elementary: `L` is fixed by the *top-level* word once and for all, so the
closed form is `D(m) ≤ nodeConst · L · m^{2/3}` — a single `rpow`, no
logarithm inside the induction.  The `log n` of the headline bound appears
only at the top, where `L = ⌈log₂ n⌉`.

The two theorems here are exactly the hypotheses the recursion will discharge:
`nodeCost_base` for a small arena and `nodeCost_step` for a split.  The
constants are honest and unoptimised: with

    h = 2^42,   C = 2^49,

the children fit in three quarters of the budget (`nodeCost_child`) and the
anchors in the remaining quarter.  The binding constraint is
`16 √(h+1) (4/h)^{2/3} < 1`, i.e. `h^{1/6} > 96`; `2^42` clears it with
`h^{1/6} = 128`.
-/

namespace QuantumQueryComplexity

/-- The arity of the node recursion: how many parts a node splits into. -/
def nodeArity : ℕ := 2 ^ 42

/-- The constant of the node recursion. -/
def nodeConst : ℝ := 2 ^ 49

/-- **The cost bound of a node** of arena size `m`, with the binary-search
depth `L` carried as a parameter. -/
noncomputable def nodeCost (L m : ℕ) : ℝ := nodeConst * L * (m : ℝ) ^ ((2 : ℝ) / 3)

lemma nodeConst_pos : (0 : ℝ) < nodeConst := by
  unfold nodeConst
  positivity

lemma nodeCost_nonneg (L m : ℕ) : 0 ≤ nodeCost L m := by
  unfold nodeCost
  have := nodeConst_pos
  positivity

lemma nodeCost_mono (L : ℕ) {m m' : ℕ} (h : m' ≤ m) : nodeCost L m' ≤ nodeCost L m := by
  unfold nodeCost
  have hC := nodeConst_pos
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h) (by norm_num)

/-! ## The two numerical facts about the arity -/

private lemma sqrt_arity_le : Real.sqrt ((nodeArity : ℝ) + 1) ≤ 3 * 2 ^ 20 := by
  have h1 : ((nodeArity : ℝ) + 1) ≤ ((3 : ℝ) * 2 ^ 20) ^ 2 := by
    unfold nodeArity
    push_cast
    norm_num
  calc Real.sqrt ((nodeArity : ℝ) + 1) ≤ Real.sqrt (((3 : ℝ) * 2 ^ 20) ^ 2) :=
        Real.sqrt_le_sqrt h1
    _ = 3 * 2 ^ 20 := Real.sqrt_sq (by positivity)

private lemma arity_rpow : ((nodeArity : ℝ)) ^ ((2 : ℝ) / 3) = 2 ^ 28 := by
  have h2 : ((nodeArity : ℝ)) = (2 : ℝ) ^ ((42 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    unfold nodeArity
    push_cast
    ring
  rw [h2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show ((42 : ℕ) : ℝ) * ((2 : ℝ) / 3) = ((28 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]

private lemma arity_rpow_third : ((nodeArity : ℝ)) ^ ((1 : ℝ) / 3) = 2 ^ 14 := by
  have h2 : ((nodeArity : ℝ)) = (2 : ℝ) ^ ((42 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    unfold nodeArity
    push_cast
    ring
  rw [h2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show ((42 : ℕ) : ℝ) * ((1 : ℝ) / 3) = ((14 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]

/-! ## The recursion -/

/-- **The children fit in three quarters of the budget.**  This is the
inequality that fixes the arity: `16 √(h+1) · (4/h)^{2/3} ≤ 3/4`. -/
theorem nodeCost_child {L m m' : ℕ} (hm : nodeArity ≤ m)
    (hm' : (m' : ℝ) ≤ 2 * m / nodeArity + 2) :
    16 * (nodeCost L m' * Real.sqrt ((nodeArity : ℝ) + 1)) ≤ 3 / 4 * nodeCost L m := by
  have hApos : (0 : ℝ) < (nodeArity : ℝ) := by
    unfold nodeArity
    positivity
  have hmA : (nodeArity : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  -- the child is at most `4 m / h`
  have h4 : (m' : ℝ) ≤ 4 * m / nodeArity := by
    have h2 : (2 : ℝ) ≤ 2 * m / nodeArity := by
      rw [le_div_iff₀ hApos]
      nlinarith
    have : 2 * (m : ℝ) / nodeArity + 2 ≤ 4 * m / nodeArity := by
      rw [div_add' _ _ _ (ne_of_gt hApos), div_le_div_iff_of_pos_right hApos]
      nlinarith
    linarith
  -- so its `2/3` power shrinks by `4^{2/3} / h^{2/3}`
  have hrpow : ((m' : ℝ)) ^ ((2 : ℝ) / 3)
      ≤ 4 * ((m : ℝ)) ^ ((2 : ℝ) / 3) / 2 ^ 28 := by
    have hstep : ((m' : ℝ)) ^ ((2 : ℝ) / 3)
        ≤ (4 * (m : ℝ) / nodeArity) ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) h4 (by norm_num)
    have hsplit : (4 * (m : ℝ) / nodeArity) ^ ((2 : ℝ) / 3)
        = (4 : ℝ) ^ ((2 : ℝ) / 3) * ((m : ℝ)) ^ ((2 : ℝ) / 3) / 2 ^ 28 := by
      rw [Real.div_rpow (by positivity) hApos.le, Real.mul_rpow (by norm_num)
        (Nat.cast_nonneg _), arity_rpow]
    have hfour : (4 : ℝ) ^ ((2 : ℝ) / 3) ≤ 4 := by
      calc (4 : ℝ) ^ ((2 : ℝ) / 3) ≤ (4 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 4 := Real.rpow_one 4
    have hm23 : (0 : ℝ) ≤ ((m : ℝ)) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [hsplit] at hstep
    refine hstep.trans ?_
    gcongr
  -- assemble
  have hsq := sqrt_arity_le
  have hsqnn : (0 : ℝ) ≤ Real.sqrt ((nodeArity : ℝ) + 1) := Real.sqrt_nonneg _
  have hCL : (0 : ℝ) ≤ nodeConst * L := by
    have := nodeConst_pos
    positivity
  have hm23 : (0 : ℝ) ≤ ((m : ℝ)) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc 16 * (nodeCost L m' * Real.sqrt ((nodeArity : ℝ) + 1))
      = 16 * ((nodeConst * L) * ((m' : ℝ)) ^ ((2 : ℝ) / 3))
          * Real.sqrt ((nodeArity : ℝ) + 1) := by
        unfold nodeCost
        ring
    _ ≤ 16 * ((nodeConst * L) * (4 * ((m : ℝ)) ^ ((2 : ℝ) / 3) / 2 ^ 28))
          * (3 * 2 ^ 20) := by
        gcongr
    _ = 3 / 4 * nodeCost L m := by
        unfold nodeCost
        ring

/-- **The recursion step**: `3 + 2h` anchors plus the children fit in the
budget of a node of size `m`. -/
theorem nodeCost_step {L m m' : ℕ} (hm : nodeArity ≤ m)
    (hm' : (m' : ℝ) ≤ 2 * m / nodeArity + 2) :
    ((3 + 2 * nodeArity : ℕ) : ℝ) * ((L : ℝ) * (8 * (m : ℝ) ^ ((2 : ℝ) / 3)))
      + 16 * (nodeCost L m' * Real.sqrt ((nodeArity : ℝ) + 1)) ≤ nodeCost L m := by
  have hchild := nodeCost_child (L := L) hm hm'
  have hm23 : (0 : ℝ) ≤ ((m : ℝ)) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  -- the anchors fit in the remaining quarter
  have hanchor : ((3 + 2 * nodeArity : ℕ) : ℝ) * ((L : ℝ) * (8 * (m : ℝ) ^ ((2 : ℝ) / 3)))
      ≤ 1 / 4 * nodeCost L m := by
    have hcoeff : (8 : ℝ) * ((3 + 2 * nodeArity : ℕ) : ℝ) ≤ 1 / 4 * nodeConst := by
      unfold nodeArity nodeConst
      push_cast
      norm_num
    unfold nodeCost
    calc ((3 + 2 * nodeArity : ℕ) : ℝ) * ((L : ℝ) * (8 * (m : ℝ) ^ ((2 : ℝ) / 3)))
        = (8 * ((3 + 2 * nodeArity : ℕ) : ℝ)) * ((L : ℝ) * (m : ℝ) ^ ((2 : ℝ) / 3)) := by
          ring
      _ ≤ (1 / 4 * nodeConst) * ((L : ℝ) * (m : ℝ) ^ ((2 : ℝ) / 3)) := by
          gcongr
      _ = 1 / 4 * (nodeConst * L * (m : ℝ) ^ ((2 : ℝ) / 3)) := by ring
  linarith

/-- **The base case**: on a small arena the read-everything dual, of cost
`2m`, is within budget. -/
theorem nodeCost_base {L m : ℕ} (hL : 1 ≤ L) (hm : m ≤ nodeArity) :
    (2 * m : ℝ) ≤ nodeCost L m := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    simpa using nodeCost_nonneg L 0
  · have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hpos
    have hsplit : ((m : ℝ)) ^ ((1 : ℝ) / 3) * ((m : ℝ)) ^ ((2 : ℝ) / 3) = (m : ℝ) := by
      rw [← Real.rpow_add hmpos]
      norm_num
    have hthird : ((m : ℝ)) ^ ((1 : ℝ) / 3) ≤ 2 ^ 14 := by
      rw [← arity_rpow_third]
      exact Real.rpow_le_rpow hmpos.le (by exact_mod_cast hm) (by norm_num)
    have hm23 : (0 : ℝ) ≤ ((m : ℝ)) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hmpos.le _
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    unfold nodeCost nodeConst
    calc (2 : ℝ) * (m : ℝ)
        = 2 * (((m : ℝ)) ^ ((1 : ℝ) / 3) * ((m : ℝ)) ^ ((2 : ℝ) / 3)) := by rw [hsplit]
      _ ≤ 2 * ((2 : ℝ) ^ 14 * ((m : ℝ)) ^ ((2 : ℝ) / 3)) := by gcongr
      _ ≤ (2 : ℝ) ^ 49 * (L : ℝ) * ((m : ℝ)) ^ ((2 : ℝ) / 3) := by
          have : (2 : ℝ) * (2 : ℝ) ^ 14 ≤ (2 : ℝ) ^ 49 * (L : ℝ) := by
            nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) 49]
          nlinarith

end QuantumQueryComplexity
