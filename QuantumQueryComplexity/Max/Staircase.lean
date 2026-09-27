import QuantumQueryComplexity.Dual
import QuantumQueryComplexity.Max.Defs
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# From a staircase factorization to a dual solution for `maxFun`

A **staircase** is a factorization of the strict order relation on the alphabet
`A` through a finite coordinate set `C`: each coordinate `c` carries an
upward-closed cut `up c : A → Bool`, and two real families `a` (indexed by the
smaller value) and `G` (indexed by the larger value) with

* `a j c ≠ 0 → up c j = false`  — `a j` lives strictly above the cut,
* `G k c ≠ 0 → up c k = true`   — `G k` lives at or above the cut,
* `∑ c, a j c * G k c = 1` whenever `j < k`.

The two support conditions make `∑ c, a j c * G k c = 0` automatic when
`k ≤ j` (upward-closure would force `up c j = true`, contradicting the first),
so only the `j < k` equations have to be supplied.

The cut is a *predicate*, not a threshold element of `A`.  That is what lets a
staircase be transported along an order embedding into a larger alphabet (as the
dyadic staircase requires), since a predicate pulls back along any monotone map
whereas a threshold element would need an inverse.

**Main result** (`advPM_maxFun_le`): a staircase with row mass `≤ α` and column
mass `≤ β` yields

  `advPM (maxFun : (ι → A) → A) ≤ 2 * √(n * α * β)`,  `n = |ι|`.

The dual solution has dimension type `C ⊕ C`; the `inl` block certifies the
pairs with `maxFun x < maxFun y` and the `inr` block the pairs with
`maxFun y < maxFun x`, and both blocks vanish on pairs of equal `maxFun`-value —
which is exactly what the LMRSS equality constraints demand.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Type*} [Fintype A] [DecidableEq A] [LinearOrder A]
variable {C : Type*} [Fintype C]

/-- A staircase factorization of the strict order relation on `A`. -/
structure Staircase (A : Type*) [LinearOrder A] (C : Type*) [Fintype C] where
  /-- The upward-closed cut carried by each coordinate. -/
  up : C → A → Bool
  /-- Each cut is upward closed. -/
  up_mono : ∀ (c : C) {v w : A}, v ≤ w → up c v → up c w
  /-- The row family, indexed by the smaller value. -/
  a : A → C → ℝ
  /-- The column family, indexed by the larger value. -/
  G : A → C → ℝ
  /-- Rows live strictly above the cut. -/
  a_supp : ∀ j c, a j c ≠ 0 → up c j = false
  /-- Columns live at or above the cut. -/
  G_supp : ∀ k c, G k c ≠ 0 → up c k = true
  /-- The factorization identity. -/
  pairing : ∀ j k : A, j < k → ∑ c, a j c * G k c = 1

namespace Staircase

variable (S : Staircase A C)

/-- If `a j c ≠ 0` then *every* value at or below `j` fails the cut — this is
what lets the `inl` block of `u` be independent of the coordinate `i`. -/
lemma not_up_of_a_ne_zero {j : A} {c : C} (h : S.a j c ≠ 0) {v : A} (hv : v ≤ j) :
    S.up c v = false := by
  by_contra hc
  rw [Bool.not_eq_false] at hc
  have h1 : S.up c j = true := S.up_mono c hv hc
  rw [S.a_supp j c h] at h1
  exact Bool.noConfusion h1

/-- The pairing vanishes unless `j < k`: the supports are disjoint otherwise. -/
lemma sum_a_mul_G (j k : A) :
    (∑ c, S.a j c * S.G k c) = if j < k then 1 else 0 := by
  by_cases hjk : j < k
  · rw [if_pos hjk]
    exact S.pairing j k hjk
  · rw [if_neg hjk]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases ha : S.a j c = 0
    · rw [ha, zero_mul]
    · by_cases hG : S.G k c = 0
      · rw [hG, mul_zero]
      · exact absurd (S.not_up_of_a_ne_zero ha (not_lt.mp hjk))
          (by rw [S.G_supp k c hG]; exact Bool.noConfusion)

/-! ## The two blocks -/

/-- One block of the constraint sum: the `inl` block for the pair `(x, y)`,
and (with the arguments swapped) the `inr` block as well. -/
noncomputable def blk (x y : ι → A) (i : ι) : ℝ :=
  ∑ c, S.a (maxFun x) c * S.G (maxFun y) c * wt (S.up c) y i

/-- The block vanishes wherever `x` and `y` agree — so the adversary mask
`if x i = y i then 0 else _` may simply be dropped. -/
lemma blk_eq_zero {x y : ι → A} {i : ι} (h : x i = y i) : S.blk x y i = 0 := by
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases ha : S.a (maxFun x) c = 0
  · rw [ha, zero_mul, zero_mul]
  · have hy : S.up c (y i) = false := by
      rw [← h]
      exact S.not_up_of_a_ne_zero ha (le_maxFun x i)
    rw [wt_eq_zero y hy, mul_zero]

/-- Summing a block over the coordinates gives the pairing, because the
normalised indicator has total mass one on every column that occurs. -/
lemma sum_blk (x y : ι → A) :
    (∑ i, S.blk x y i) = if maxFun x < maxFun y then 1 else 0 := by
  rw [← S.sum_a_mul_G (maxFun x) (maxFun y)]
  simp only [blk]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hG : S.G (maxFun y) c = 0
  · simp [hG]
  · rw [← Finset.mul_sum, sum_wt y (S.G_supp _ c hG), mul_one]

/-! ## The dual solution -/

/-- The first vector family of the dual solution, at scale `lam` and with
per-coordinate weights `w`.

The weight sits on the "spread" block of `u` and is divided out on the
"concentrated" block of `v`, so it cancels in every product and the feasibility
argument below is *unchanged*.  It is a pure cost-balancing device: taking
`w i = √(c i)` turns the `c`-weighted cost into `∑ i, (c i)²`
(`dual_isWeightedCostLe`), which is what a composition over subproblems of
differing costs needs. -/
noncomputable def dualU (lam : ℝ) (w : ι → ℝ) (x : ι → A) (i : ι) : C ⊕ C → ℝ :=
  Sum.elim (fun c => lam * S.a (maxFun x) c * w i)
    (fun c => lam⁻¹ * S.G (maxFun x) c * wt (S.up c) x i / w i)

/-- The second vector family: the same data with the two blocks exchanged. -/
noncomputable def dualV (lam : ℝ) (w : ι → ℝ) (y : ι → A) (i : ι) : C ⊕ C → ℝ :=
  Sum.elim (fun c => lam⁻¹ * S.G (maxFun y) c * wt (S.up c) y i / w i)
    (fun c => lam * S.a (maxFun y) c * w i)

lemma dualV_eq_dualU_swap (lam : ℝ) (w : ι → ℝ) (y : ι → A) (i : ι) (k : C ⊕ C) :
    S.dualV lam w y i k = S.dualU lam w y i k.swap := by
  cases k <;> rfl

/-- The pointwise pairing of `u` and `v` splits into the two blocks; the
weights cancel. -/
lemma sum_dualU_mul_dualV {lam : ℝ} (hlam : lam ≠ 0) {w : ι → ℝ}
    (hw : ∀ i, w i ≠ 0) (x y : ι → A) (i : ι) :
    (∑ k : C ⊕ C, S.dualU lam w x i k * S.dualV lam w y i k)
      = S.blk x y i + S.blk y x i := by
  have hwi := hw i
  rw [Fintype.sum_sum_type]
  simp only [dualU, dualV, Sum.elim_inl, Sum.elim_inr, blk]
  congr 1
  · exact Finset.sum_congr rfl fun c _ => by field_simp
  · exact Finset.sum_congr rfl fun c _ => by field_simp

/-- **The dual solution attached to a staircase.** -/
noncomputable def dual {lam : ℝ} (hlam : lam ≠ 0) {w : ι → ℝ} (hw : ∀ i, w i ≠ 0) :
    DualPair (C ⊕ C) (maxFun : (ι → A) → A) where
  u := S.dualU lam w
  v := S.dualV lam w
  constraint x y := by
    have hmask : ∀ i : ι,
        (if x i = y i then (0 : ℝ)
          else ∑ k : C ⊕ C, S.dualU lam w x i k * S.dualV lam w y i k)
        = S.blk x y i + S.blk y x i := by
      intro i
      by_cases h : x i = y i
      · rw [if_pos h, S.blk_eq_zero h, S.blk_eq_zero h.symm, add_zero]
      · rw [if_neg h, S.sum_dualU_mul_dualV hlam hw]
    simp only [hmask]
    rw [Finset.sum_add_distrib, S.sum_blk x y, S.sum_blk y x]
    rcases lt_trichotomy (maxFun x) (maxFun y) with h | h | h
    · rw [if_pos h, if_neg (asymm h), if_neg (ne_of_lt h)]
      norm_num
    · rw [if_neg (by rw [h]; exact lt_irrefl _), if_neg (by rw [h]; exact lt_irrefl _),
        if_pos h]
      norm_num
    · rw [if_neg (asymm h), if_pos h, if_neg (ne_of_gt h)]
      norm_num

/-! ## The cost -/

/-- The `c`-weighted `ℓ²` mass of `u` at a single input, split into its two
blocks, when the balancing weights are `w i = √(c i)`.

The first block picks up `∑ i, (c i)²` — this is the whole point of the weights:
uniform weights would give `(∑ i, c i)` there, which is far too large when the
`c i` vary over many orders of magnitude, as they do across the levels of a
divide-and-conquer recursion. -/
lemma sum_dualU_sq_weighted_le {lam : ℝ} (hlam : lam ≠ 0) {c : ι → ℝ}
    (hc : ∀ i, 0 < c i) (x : ι → A) {α β : ℝ}
    (hα : ∀ j, (∑ d, S.a j d * S.a j d) ≤ α)
    (hβ : ∀ k, (∑ d, S.G k d * S.G k d) ≤ β) :
    (∑ i, c i * ∑ k : C ⊕ C,
        S.dualU lam (fun i => Real.sqrt (c i)) x i k
          * S.dualU lam (fun i => Real.sqrt (c i)) x i k)
      ≤ (lam * lam) * α * (∑ i, c i * c i) + lam⁻¹ * lam⁻¹ * β := by
  have hsq : ∀ i, Real.sqrt (c i) * Real.sqrt (c i) = c i := fun i =>
    Real.mul_self_sqrt (hc i).le
  have hne : ∀ i, Real.sqrt (c i) ≠ 0 := fun i =>
    (Real.sqrt_pos.mpr (hc i)).ne'
  have hsplit : ∀ i : ι, c i * (∑ k : C ⊕ C,
        S.dualU lam (fun i => Real.sqrt (c i)) x i k
          * S.dualU lam (fun i => Real.sqrt (c i)) x i k)
      = (lam * lam) * (∑ d, S.a (maxFun x) d * S.a (maxFun x) d) * (c i * c i)
        + ∑ d, (lam⁻¹ * lam⁻¹) * (S.G (maxFun x) d * S.G (maxFun x) d)
            * (wt (S.up d) x i * wt (S.up d) x i) := by
    intro i
    rw [Fintype.sum_sum_type]
    simp only [dualU, Sum.elim_inl, Sum.elim_inr]
    rw [mul_add]
    congr 1
    · rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [show c i * (lam * S.a (maxFun x) d * Real.sqrt (c i)
            * (lam * S.a (maxFun x) d * Real.sqrt (c i)))
          = c i * ((lam * lam) * (S.a (maxFun x) d * S.a (maxFun x) d))
            * (Real.sqrt (c i) * Real.sqrt (c i)) from by ring, hsq i]
      ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      have hci : c i ≠ 0 := (hc i).ne'
      rw [div_mul_div_comm, hsq i]
      field_simp
      try ring
  simp only [hsplit]
  rw [Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hα _) (mul_self_nonneg lam))
      (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  · -- the second block: swap the sums and use `∑ i, wt² ≤ 1`
    rw [Finset.sum_comm]
    calc (∑ d, ∑ i, (lam⁻¹ * lam⁻¹) * (S.G (maxFun x) d * S.G (maxFun x) d)
              * (wt (S.up d) x i * wt (S.up d) x i))
        ≤ ∑ d, (lam⁻¹ * lam⁻¹) * (S.G (maxFun x) d * S.G (maxFun x) d) := by
          refine Finset.sum_le_sum fun d _ => ?_
          rw [← Finset.mul_sum]
          by_cases hG : S.G (maxFun x) d = 0
          · simp [hG]
          · refine le_of_le_of_eq
              (mul_le_mul_of_nonneg_left (sum_wt_sq_le_one x (S.G_supp _ d hG))
                (mul_nonneg (mul_self_nonneg lam⁻¹) (mul_self_nonneg _)))
              (mul_one _)
      _ = lam⁻¹ * lam⁻¹ * ∑ d, S.G (maxFun x) d * S.G (maxFun x) d :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ lam⁻¹ * lam⁻¹ * β :=
          mul_le_mul_of_nonneg_left (hβ _) (mul_self_nonneg lam⁻¹)

/-- The unweighted mass, recovered at `c = 1` (so `w = 1`). -/
lemma sum_dualU_sq_le {lam : ℝ} (hlam : lam ≠ 0) (x : ι → A) {α β : ℝ}
    (hα : ∀ j, (∑ c, S.a j c * S.a j c) ≤ α)
    (hβ : ∀ k, (∑ c, S.G k c * S.G k c) ≤ β) :
    (∑ i, ∑ k : C ⊕ C, S.dualU lam (fun _ => 1) x i k
        * S.dualU lam (fun _ => 1) x i k)
      ≤ (Fintype.card ι : ℝ) * (lam * lam) * α + lam⁻¹ * lam⁻¹ * β := by
  have h := S.sum_dualU_sq_weighted_le (c := fun _ : ι => (1 : ℝ)) hlam
    (fun _ => zero_lt_one) x hα hβ
  simp only [Real.sqrt_one] at h
  refine le_trans (le_of_eq ?_) (le_trans h (le_of_eq ?_))
  · exact Finset.sum_congr rfl fun i _ => (one_mul _).symm
  · rw [show (∑ _i : ι, (1 : ℝ) * 1) = (Fintype.card ι : ℝ) from by
      simp [Finset.card_univ]]
    ring

/-- The cost bound for the dual solution, at any scale.  The `v` side needs no
separate argument: `v` is `u` with its two blocks exchanged, so its `ℓ²` mass is
the same sum reindexed by `Equiv.sumComm`. -/
lemma dual_isCostLe {lam : ℝ} (hlam : lam ≠ 0) {α β : ℝ}
    (hα : ∀ j, (∑ c, S.a j c * S.a j c) ≤ α)
    (hβ : ∀ k, (∑ c, S.G k c * S.G k c) ≤ β) :
    (S.dual (ι := ι) hlam (w := fun _ => 1) (fun _ => one_ne_zero)).IsCostLe
      ((Fintype.card ι : ℝ) * (lam * lam) * α + lam⁻¹ * lam⁻¹ * β) := by
  refine ⟨fun x => S.sum_dualU_sq_le hlam x hα hβ, fun y => ?_⟩
  have h : (∑ i, ∑ k : C ⊕ C, S.dualV lam (fun _ => 1) y i k * S.dualV lam (fun _ => 1) y i k)
      = ∑ i, ∑ k : C ⊕ C, S.dualU lam (fun _ => 1) y i k * S.dualU lam (fun _ => 1) y i k :=
    Finset.sum_congr rfl fun i _ =>
      Fintype.sum_equiv (Equiv.sumComm C C) _ _ fun k => by
        rw [S.dualV_eq_dualU_swap]
        rfl
  show (∑ i, ∑ k : C ⊕ C, S.dualV lam (fun _ => 1) y i k * S.dualV lam (fun _ => 1) y i k) ≤ _
  rw [h]
  exact S.sum_dualU_sq_le hlam y hα hβ

/-- **A staircase bounds the adversary bound of `maxFun`.**

Balancing the two blocks at `lam² = √(β / (n α))` makes them contribute equally,
giving `2√(n α β)`. -/
theorem _root_.QuantumQueryComplexity.advPM_maxFun_le (S : Staircase A C) {α β : ℝ}
    (hα : ∀ j, (∑ c, S.a j c * S.a j c) ≤ α)
    (hβ : ∀ k, (∑ c, S.G k c * S.G k c) ≤ β)
    (hα0 : 0 < α) (hβ0 : 0 < β) :
    advPM (maxFun : (ι → A) → A)
      ≤ 2 * Real.sqrt ((Fintype.card ι : ℝ) * α * β) := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  set s : ℝ := Real.sqrt ((Fintype.card ι : ℝ) * α) with hsdef
  set r : ℝ := Real.sqrt β with hrdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hr0 : 0 < r := Real.sqrt_pos.mpr hβ0
  have hs2 : s * s = (Fintype.card ι : ℝ) * α := Real.mul_self_sqrt (by positivity)
  have hr2 : r * r = β := Real.mul_self_sqrt hβ0.le
  set lam : ℝ := Real.sqrt (r / s) with hlamdef
  have hlam0 : 0 < lam := Real.sqrt_pos.mpr (div_pos hr0 hs0)
  have hlam2 : lam * lam = r / s := Real.mul_self_sqrt (le_of_lt (div_pos hr0 hs0))
  have hinv : lam⁻¹ * lam⁻¹ = s / r := by
    rw [← mul_inv, hlam2, inv_div]
  -- each block contributes `s * r`
  have h1 : (Fintype.card ι : ℝ) * (lam * lam) * α = s * r := by
    rw [hlam2, show (Fintype.card ι : ℝ) * (r / s) * α
        = ((Fintype.card ι : ℝ) * α) * r / s from by ring, ← hs2]
    field_simp
  have h2 : lam⁻¹ * lam⁻¹ * β = s * r := by
    rw [hinv, ← hr2]
    field_simp
  have hcost : (Fintype.card ι : ℝ) * (lam * lam) * α + lam⁻¹ * lam⁻¹ * β
      = 2 * Real.sqrt ((Fintype.card ι : ℝ) * α * β) := by
    rw [h1, h2, hsdef, hrdef, ← Real.sqrt_mul (by positivity)]
    ring
  refine le_of_le_of_eq (advPM_le_of_dualPair
    (S.dual (ι := ι) hlam0.ne' (w := fun _ => 1) (fun _ => one_ne_zero)) ?_
    (S.dual_isCostLe hlam0.ne' hα hβ)) hcost
  rw [hcost]
  positivity

end Staircase

end QuantumQueryComplexity
