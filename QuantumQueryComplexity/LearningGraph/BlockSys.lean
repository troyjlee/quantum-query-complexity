import QuantumQueryComplexity.LearningGraph.ArcSystem
import QuantumQueryComplexity.FirstDiff

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Block arc systems and certifying paths

An arc system (`ArcSystem`) whose arcs come in **blocks**, for a promise problem `f : X → Bool`
observed through `read : X → ι → σ`. A block `b` starts from an incoming loaded set `inn b`,
loads the positions `load b` one at a time in the fixed global order `idxRank`, and carries one
conductance `cond b r ≥ 0`, which may depend on the record `r` of the observed input on `inn b`
(`BlockSys`). The arc `(b, i)` queries `i ∈ load b`; its state is the record of the observed
input on `dom b i`, the incoming set together with the positions of the block loaded before `i`.
A negative input puts amplitude `√c / λ` on each arc of a block of conductance `c`; a positive
input puts `λ · m / √c`, where `m` is its **mass** on the block (`BlockSys.arcSys`).

* Inside a block the first disagreements telescope (`BlockSys.sum_load_firstDiff`): their
  indicator sum is the agreement indicator on `inn b` minus the one on `out b = inn b ∪ load b`.
  A position that is already loaded never contributes.
* So the cross sum of a positive and a negative input is `∑_b m_b (agree(inn b) − agree(out b))`
  (`BlockSys.arcSys_cross`), as soon as the conductance is positive wherever the mass is not
  zero. The conductance agrees at a first disagreement because it is read from the record on
  `inn b`.
* A positive input chooses a weighted family of block paths (`pathMass`); the mass of a block is
  the total weight of the paths through it. Along one path the differences telescope, so a family
  of total weight one whose every path telescopes to one gives cross sum one
  (`sum_pathMass_mul`, `hasDualOn_of_paths`).
* The costs are `∑_b |load b| c_b / λ²` for a negative input and `λ² ∑_b |load b| m_b² / c_b` for
  a positive one (`BlockSys.arcSys_cost_neg`, `BlockSys.arcSys_cost_pos`).
  `posCost_le_of_budget` bounds the positive sum by a per-block budget `τ` that adds up to at
  most one along every path.

This module generalizes the block arc systems of the triangle upper bound in the downstream
`quantum-query-problems` package (`QuantumQueryProblems/Triangle/Upper/Arcs.lean`, total
functions read by `id`) to promise problems with an arbitrary observation map `read`.
-/

namespace QuantumQueryComplexity

open Finset

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X]

/-- **The agreement indicator** of two observed inputs on a set of positions. -/
def agree (D : Finset ι) (x y : ι → σ) : ℝ :=
  if ∀ i ∈ D, x i = y i then 1 else 0

private lemma agree_insert_key (a : ι) (E : Finset ι) (x y : ι → σ) :
    (if x a = y a then 0 else agree E x y) = agree E x y - agree (insert a E) x y := by
  unfold agree
  by_cases ha : x a = y a
  · simp [ha]
  · have : ¬ ∀ i ∈ insert a E, x i = y i := fun h => ha (h a (mem_insert_self a E))
    simp only [ha, ite_false, this, sub_zero]

/-- Telescoping over any set `T` of positions loaded in the order `idxRank` after `D`. -/
private lemma sum_firstDiff_gen (D T : Finset ι) (x y : ι → σ) :
    ∑ i ∈ T, (if x i = y i then 0
        else agree (D ∪ T.filter (fun j => idxRank j < idxRank i)) x y)
      = agree D x y - agree (D ∪ T) x y := by
  induction T using Finset.induction_on_max_value (idxRank : ι → Fin (Fintype.card ι)) with
  | empty => simp
  | insert a s has hmax ih =>
    have hlt : ∀ j ∈ s, idxRank j < idxRank a := fun j hj =>
      lt_of_le_of_ne (hmax j hj) fun h => has (idxRank_inj h ▸ hj)
    have hfa : (insert a s).filter (fun j => idxRank j < idxRank a) = s := by
      ext j
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hj, hr⟩
        · exact absurd hr (lt_irrefl _)
        · exact hj
      · intro hj
        exact ⟨Or.inr hj, hlt j hj⟩
    have hfi : ∀ i ∈ s, (insert a s).filter (fun j => idxRank j < idxRank i)
        = s.filter (fun j => idxRank j < idxRank i) := by
      intro i hi
      rw [filter_insert]
      have : ¬ idxRank a < idxRank i := not_lt.mpr (hlt i hi).le
      simp [this]
    rw [sum_insert has, hfa, sum_congr rfl fun i hi => by rw [hfi i hi], ih,
      agree_insert_key, union_insert]
    ring

/-- **A block system** on the positions `ι`: block `b` starts from the loaded set `inn b`, loads
the positions `load b` in the order `idxRank`, and has conductance `cond b r` when the record of
the observed input on `inn b` is `r`. -/
structure BlockSys (ι σ β : Type) where
  /-- The positions loaded before the block. -/
  inn : β → Finset ι
  /-- The positions the block loads. -/
  load : β → Finset ι
  /-- The conductance, read from the record on `inn b`. -/
  cond : β → (ι → Option σ) → ℝ

namespace BlockSys

variable {β : Type} (S : BlockSys ι σ β)

/-- The positions loaded after the block. -/
def out (b : β) : Finset ι := S.inn b ∪ S.load b

/-- **The loaded set at the arc `(b, i)`**: the incoming set and the block's positions before
`i` in the order `idxRank`. -/
noncomputable def dom (b : β) (i : ι) : Finset ι :=
  S.inn b ∪ (S.load b).filter fun j => idxRank j < idxRank i

/-- The conductance of the block `b` for the observed input `z`, read from its record on
`inn b`. -/
def condOf (b : β) (z : ι → σ) : ℝ := S.cond b (setMask z (S.inn b))

/-- **The arc system of a block system** for the promise problem `f` observed through `read`,
with masses `mass x b` for the positive inputs and the scale `λ`: the arc `(b, i)` queries `i`,
its state is the record of `read x` on `dom b i`, and its amplitude is
`λ · mass x b / √(condOf b (read x))` for a positive input and `√(condOf b (read x)) / λ` for a
negative one when `i ∈ load b` (and `0` otherwise). -/
noncomputable def arcSys (read : X → ι → σ) (f : X → Bool) (mass : X → β → ℝ) (lam : ℝ) :
    ArcSystem read f (β × ι) (ι → Option σ) Unit where
  load e := e.2
  state e z := setMask (read z) (S.dom e.1 e.2)
  amp e z _ :=
    if e.2 ∈ S.load e.1 then
      (if f z then lam * mass z e.1 / Real.sqrt (S.condOf e.1 (read z))
        else Real.sqrt (S.condOf e.1 (read z)) / lam)
    else 0

/-- **Telescoping inside a block.** Summed over the positions of the block, the indicator that
the arc is a first disagreement (the inputs differ at the queried position and agree on the
arc's loaded set) is the agreement indicator on `inn b` minus the one on `out b`. -/
theorem sum_load_firstDiff (b : β) (x y : ι → σ) :
    ∑ i ∈ S.load b, (if x i = y i then 0 else agree (S.dom b i) x y)
      = agree (S.inn b) x y - agree (S.out b) x y :=
  sum_firstDiff_gen (S.inn b) (S.load b) x y

variable [Fintype β]

/-- **The cross sum of a block arc system.** For a positive `x` and a negative `y`, if every block
on which `x` has nonzero mass has positive conductance for `x`, the cross sum is
`∑_b mass x b · (agree(inn b) − agree(out b))` on the observed inputs. -/
theorem arcSys_cross {read : X → ι → σ} {f : X → Bool} {mass : X → β → ℝ} {lam : ℝ}
    (hlam : lam ≠ 0) {x y : X} (hx : f x = true) (hy : f y = false)
    (hsupp : ∀ b, mass x b ≠ 0 → 0 < S.condOf b (read x)) :
    (S.arcSys read f mass lam).cross x y
      = ∑ b, mass x b * (agree (S.inn b) (read x) (read y)
          - agree (S.out b) (read x) (read y)) := by
  unfold ArcSystem.cross
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun b _ => ?_
  rw [← S.sum_load_firstDiff b (read x) (read y), mul_sum,
    ← Finset.sum_ite_mem_eq (S.load b)]
  refine sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ S.load b
  · by_cases hxy : read x i = read y i
    · simp [arcSys, hxy]
    · simp only [arcSys, hi, ite_true, hx, hy, Bool.false_eq_true, ite_false, hxy,
        Finset.univ_unique, Finset.sum_singleton]
      by_cases hdom : setMask (read x) (S.dom b i) = setMask (read y) (S.dom b i)
      · have hag : ∀ j ∈ S.dom b i, read x j = read y j := setMask_eq_iff.1 hdom
        have hc : S.condOf b (read x) = S.condOf b (read y) := by
          unfold condOf
          congr 1
          exact setMask_eq_iff.2 fun j hj => hag j (by simp [dom, hj])
        have hA : agree (S.dom b i) (read x) (read y) = 1 :=
          ite_eq_left_of_eq_true _ _ (eq_true hag)
        rw [hA, mul_one, ← hc]
        simp only [hdom, ite_true]
        by_cases hm : mass x b = 0
        · simp [hm]
        · have hpos := Real.sqrt_pos.2 (hsupp b hm)
          field_simp
      · have hag : ¬ ∀ j ∈ S.dom b i, read x j = read y j := fun h => hdom (setMask_eq_iff.2 h)
        simp [hdom, agree, hag]
  · simp [arcSys, hi]

/-- **The cost of a negative input**: `∑_b |load b| · condOf b (read y) / λ²`. -/
theorem arcSys_cost_neg {read : X → ι → σ} {f : X → Bool} {mass : X → β → ℝ} {lam : ℝ}
    (hcond : ∀ b r, 0 ≤ S.cond b r) {y : X} (hy : f y = false) :
    (S.arcSys read f mass lam).cost y
      = (∑ b, (#(S.load b) : ℝ) * S.condOf b (read y)) / lam ^ 2 := by
  unfold ArcSystem.cost
  rw [Fintype.sum_prod_type, sum_div]
  refine sum_congr rfl fun b _ => ?_
  have hc : Real.sqrt (S.condOf b (read y)) ^ 2 = S.condOf b (read y) :=
    Real.sq_sqrt (hcond _ _)
  have hpt : ∀ i, (∑ c : Unit, (S.arcSys read f mass lam).amp (b, i) y c
      * (S.arcSys read f mass lam).amp (b, i) y c)
      = if i ∈ S.load b then S.condOf b (read y) / lam ^ 2 else 0 := by
    intro i
    by_cases hi : i ∈ S.load b
    · simp only [arcSys, hi, hy, Bool.false_eq_true, ite_false, ite_true, Finset.univ_unique,
        Finset.sum_singleton]
      rw [div_mul_div_comm, ← pow_two, ← pow_two, hc]
    · simp [arcSys, hi]
  rw [sum_congr rfl fun i _ => hpt i, Finset.sum_ite_mem_eq, sum_const, nsmul_eq_mul]
  ring

/-- **The cost of a positive input**: `λ² ∑_b |load b| · mass x b² / condOf b (read x)`. -/
theorem arcSys_cost_pos {read : X → ι → σ} {f : X → Bool} {mass : X → β → ℝ} {lam : ℝ}
    (hcond : ∀ b r, 0 ≤ S.cond b r) {x : X} (hx : f x = true) :
    (S.arcSys read f mass lam).cost x
      = lam ^ 2 * ∑ b, (#(S.load b) : ℝ) * mass x b ^ 2 / S.condOf b (read x) := by
  unfold ArcSystem.cost
  rw [Fintype.sum_prod_type, mul_sum]
  refine sum_congr rfl fun b _ => ?_
  have hc : Real.sqrt (S.condOf b (read x)) ^ 2 = S.condOf b (read x) :=
    Real.sq_sqrt (hcond _ _)
  have hpt : ∀ i, (∑ c : Unit, (S.arcSys read f mass lam).amp (b, i) x c
      * (S.arcSys read f mass lam).amp (b, i) x c)
      = if i ∈ S.load b then lam ^ 2 * mass x b ^ 2 / S.condOf b (read x) else 0 := by
    intro i
    by_cases hi : i ∈ S.load b
    · simp only [arcSys, hi, hx, ite_true, Finset.univ_unique, Finset.sum_singleton]
      rw [div_mul_div_comm, ← pow_two, ← pow_two, hc]
      ring
    · simp [arcSys, hi]
  rw [sum_congr rfl fun i _ => hpt i, Finset.sum_ite_mem_eq, sum_const, nsmul_eq_mul]
  ring

end BlockSys

section Paths

variable {β : Type} [Fintype β] [DecidableEq β]

/-- **The mass of a weighted family of block paths** on a block: the total weight of the paths
through it. -/
def pathMass {P : Type} [Fintype P] (μ : P → ℝ) (path : P → List β) (b : β) : ℝ :=
  ∑ p, if b ∈ path p then μ p else 0

/-- **Path decomposition**: summing a function of the blocks against the mass is summing it along
each path, weighted, provided no path repeats a block. -/
theorem sum_pathMass_mul {P : Type} [Fintype P] (μ : P → ℝ) (path : P → List β)
    (hnd : ∀ p, (path p).Nodup) (F : β → ℝ) :
    ∑ b, pathMass μ path b * F b = ∑ p, μ p * ((path p).map F).sum := by
  unfold pathMass
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [← List.sum_toFinset F (hnd p), mul_sum, ← Finset.sum_ite_mem_eq (path p).toFinset]
  refine sum_congr rfl fun b _ => ?_
  simp only [List.mem_toFinset, ite_mul, zero_mul]

/-- **The positive cost by budgets.** Let `μ ≥ 0`. If the budget `τ b` satisfies
`|load b| · m_b ≤ τ b · c_b` on every block (with `c_b > 0` wherever `m_b ≠ 0`), and the budgets
along every path of nonzero weight add up to at most one, then
`∑_b |load b| m_b² / c_b ≤ ∑_p μ p`. -/
theorem posCost_le_of_budget (S : BlockSys ι σ β) {P : Type} [Fintype P] (μ : P → ℝ)
    (path : P → List β) (hnd : ∀ p, (path p).Nodup) (hμ : ∀ p, 0 ≤ μ p) (z : ι → σ)
    (τ : β → ℝ)
    (hτ : ∀ b, (#(S.load b) : ℝ) * pathMass μ path b ≤ τ b * S.condOf b z)
    (hsupp : ∀ b, pathMass μ path b ≠ 0 → 0 < S.condOf b z)
    (hbudget : ∀ p, μ p ≠ 0 → ((path p).map τ).sum ≤ 1) :
    ∑ b, (#(S.load b) : ℝ) * pathMass μ path b ^ 2 / S.condOf b z ≤ ∑ p, μ p := by
  have hm : ∀ b, 0 ≤ pathMass μ path b := fun b =>
    sum_nonneg fun p _ => by split_ifs <;> simp [hμ p]
  calc ∑ b, (#(S.load b) : ℝ) * pathMass μ path b ^ 2 / S.condOf b z
      ≤ ∑ b, pathMass μ path b * τ b := by
        refine sum_le_sum fun b _ => ?_
        by_cases h0 : pathMass μ path b = 0
        · simp [h0]
        · have hc := hsupp b h0
          rw [div_le_iff₀ hc]
          have := mul_le_mul_of_nonneg_left (hτ b) (hm b)
          nlinarith
    _ = ∑ p, μ p * ((path p).map τ).sum := sum_pathMass_mul μ path hnd τ
    _ ≤ ∑ p, μ p := by
        refine sum_le_sum fun p _ => ?_
        by_cases h0 : μ p = 0
        · simp [h0]
        · exact mul_le_of_le_one_right (hμ p) (hbudget p h0)

/-- **A dual adversary solution from certifying block paths.** Every positive input `x` chooses
paths `path x p` with weights `μ x p` of total weight one, no path repeating a block, each path of
nonzero weight telescoping to one against every negative input, and positive conductance on every
block it uses. If every negative input has `∑_b |load b| c_b ≤ N` and every positive input has
`∑_b |load b| m_b² / c_b ≤ Q`, with **`N > 0` and `Q > 0`**, there is a dual solution of cost
`√(N Q)` for `f` observed through `read`. The amplitudes are rescaled by `λ² = √(N/Q)`, which
needs both bounds positive. (Zero budgets are not covered: when `f` takes both values, the cross
sum one forces some block with positive conductance and positive mass, so `N` and `Q` must be
positive anyway.) -/
theorem hasDualOn_of_paths (S : BlockSys ι σ β) (read : X → ι → σ) (f : X → Bool) {P : Type}
    [Fintype P] (μ : X → P → ℝ) (path : X → P → List β)
    (hcond : ∀ b r, 0 ≤ S.cond b r) (hnd : ∀ x p, (path x p).Nodup)
    (hμ : ∀ x, f x = true → ∑ p, μ x p = 1)
    (htel : ∀ x y p, f x = true → f y = false → μ x p ≠ 0 →
      ((path x p).map fun b => agree (S.inn b) (read x) (read y)
        - agree (S.out b) (read x) (read y)).sum = 1)
    (hsupp : ∀ x b, f x = true → pathMass (μ x) (path x) b ≠ 0 → 0 < S.condOf b (read x))
    {N Q : ℝ} (hN : 0 < N) (hQ : 0 < Q)
    (hneg : ∀ y, f y = false → ∑ b, (#(S.load b) : ℝ) * S.condOf b (read y) ≤ N)
    (hpos : ∀ x, f x = true →
      ∑ b, (#(S.load b) : ℝ) * pathMass (μ x) (path x) b ^ 2 / S.condOf b (read x) ≤ Q) :
    HasDualOn read f (Real.sqrt (N * Q)) := by
  set lam := Real.sqrt (Real.sqrt (N / Q)) with hlam_def
  have hNQ : 0 < Real.sqrt (N / Q) := Real.sqrt_pos.2 (div_pos hN hQ)
  have hlampos : (0 : ℝ) < lam := Real.sqrt_pos.2 hNQ
  have hlamsq : lam ^ 2 = Real.sqrt (N / Q) := Real.sq_sqrt hNQ.le
  have hkey1 : Real.sqrt (N / Q) * Q = Real.sqrt (N * Q) := by
    rw [show N * Q = N / Q * Q ^ 2 from by field_simp,
      Real.sqrt_mul (div_nonneg hN.le hQ.le), Real.sqrt_sq hQ.le]
  have hkey2 : N / Real.sqrt (N / Q) = Real.sqrt (N * Q) := by
    rw [div_eq_iff hNQ.ne', ← Real.sqrt_mul (mul_nonneg hN.le hQ.le),
      show N * Q * (N / Q) = N ^ 2 from by field_simp, Real.sqrt_sq hN.le]
  refine (S.arcSys read f (fun x => pathMass (μ x) (path x)) lam).hasDualOn
    (fun x y hx hy => ?_) fun x => ?_
  · rw [S.arcSys_cross hlampos.ne' hx hy (hsupp x · hx), sum_pathMass_mul _ _ (hnd x),
      ← hμ x hx]
    refine sum_congr rfl fun p _ => ?_
    by_cases h0 : μ x p = 0
    · simp [h0]
    · rw [htel x y p hx hy h0, mul_one]
  · cases hfx : f x
    · rw [S.arcSys_cost_neg hcond hfx, hlamsq, ← hkey2]
      exact div_le_div_of_nonneg_right (hneg x hfx) hNQ.le
    · rw [S.arcSys_cost_pos hcond hfx, hlamsq, ← hkey1]
      exact mul_le_mul_of_nonneg_left (hpos x hfx) hNQ.le

end Paths

end QuantumQueryComplexity
