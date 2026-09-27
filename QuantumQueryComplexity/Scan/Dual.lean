import QuantumQueryComplexity.Scan.Defs
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The dual solution attached to a weighted scan

`u` sits at the branch it takes, weighted `1/√W`; `v` spreads over the *other*
colours, weighted `√W`.  At the first differing branch the two square roots
cancel — this is where `black_unique` is used, since it rules out both sides
taking a black branch at the same node, which would leave no common colour.

The resulting costs are

  `∑ i, ‖u x i‖² ≤ 4 ∑ i, 1 / W i (col x i)`,
  `∑ i, ‖v y i‖² ≤ 4 ∑ i, (W i true + if col y i then W i false else 0)`,

so the weights trade one side against the other.  Constant weights give the
first-difference dual back; the maximum scan will make them depend on depth.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {O : Type*} [Fintype O] [DecidableEq O]
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The dimension type: node, colour, branch gadget, output gadget. -/
abbrev ScanDim (ι O Q : Type*) := (ι → Option Q) × Bool × Option Q × Option O

namespace Scan

variable (S : Scan ι σ O Q) (W : ι → Bool → ℝ)

/-- Splitting a sum over the four dimension components.  Stated with the
component functions explicit, so no higher-order unification is needed. -/
private lemma sum_four (a a' : (ι → Option Q) → ℝ) (b b' : Bool → ℝ)
    (c c' : Option Q → ℝ) (d d' : Option O → ℝ) :
    (∑ k : ScanDim ι O Q,
        (a k.1 * (b k.2.1 * (c k.2.2.1 * d k.2.2.2)))
          * (a' k.1 * (b' k.2.1 * (c' k.2.2.1 * d' k.2.2.2))))
      = (∑ p, a p * a' p) * ((∑ t, b t * b' t)
          * ((∑ q, c q * c' q) * (∑ o, d o * d' o))) := by
  have h : ∀ p t q o, (a p * (b t * (c q * d o))) * (a' p * (b' t * (c' q * d' o)))
      = (a p * a' p) * ((b t * b' t) * ((c q * c' q) * (d o * d' o))) := by
    intros; ring
  simp only [Fintype.sum_prod_type, h, ← Finset.mul_sum, ← Finset.sum_mul]

/-- The node component of `u` and of `v`. -/
def ndVec (x : ι → σ) (i : ι) (p : ι → Option Q) : ℝ :=
  if p = S.node x i then 1 else 0

/-- The colour component of `u`: mass at the colour actually taken. -/
noncomputable def colU (x : ι → σ) (i : ι) (c : Bool) : ℝ :=
  if c = S.col x i then (Real.sqrt (W i (S.col x i)))⁻¹ else 0

/-- The colour component of `v`: mass on every *other* colour. -/
noncomputable def colV (y : ι → σ) (i : ι) (c : Bool) : ℝ :=
  if S.col y i || c then Real.sqrt (W i c) else 0

lemma sum_ndVec (x y : ι → σ) (i : ι) :
    (∑ p : ι → Option Q, S.ndVec x i p * S.ndVec y i p)
      = if S.node x i = S.node y i then 1 else 0 := by
  classical
  simp only [ndVec]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) =>
    show ((if p = S.node x i then (1 : ℝ) else 0) * if p = S.node y i then 1 else 0)
      = (if p = S.node x i then (if S.node x i = S.node y i then (1 : ℝ) else 0)
          else 0) from by
      by_cases h1 : p = S.node x i <;> by_cases h2 : p = S.node y i <;>
        simp [h1, h2] <;> grind]
  rw [Finset.sum_ite_eq' Finset.univ (S.node x i)
    fun _ => (if S.node x i = S.node y i then (1 : ℝ) else 0),
    if_pos (Finset.mem_univ _)]

lemma sum_col (hW : ∀ i c, 0 < W i c) (x y : ι → σ) (i : ι) :
    (∑ c : Bool, S.colU W x i c * S.colV W y i c)
      = if S.col y i || S.col x i then 1 else 0 := by
  have hne : Real.sqrt (W i (S.col x i)) ≠ 0 := (Real.sqrt_pos.mpr (hW _ _)).ne'
  simp only [colU, colV]
  rw [Fintype.sum_bool]
  cases hx : S.col x i <;> cases hy : S.col y i <;>
    simp only [hx, hy, Bool.false_or, Bool.true_or, Bool.or_false, Bool.or_true,
      if_true, if_false, ite_true, ite_false] <;> norm_num <;>
    rw [hx] at hne <;> field_simp

lemma sum_ndVec_sq (x : ι → σ) (i : ι) :
    (∑ p : ι → Option Q, S.ndVec x i p * S.ndVec x i p) = 1 := by
  classical
  simp only [ndVec]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) =>
    show ((if p = S.node x i then (1 : ℝ) else 0) * if p = S.node x i then 1 else 0)
      = (if p = S.node x i then (1 : ℝ) else 0) from by
      by_cases h1 : p = S.node x i <;> simp [h1]]
  rw [Finset.sum_ite_eq' Finset.univ (S.node x i) fun _ => (1 : ℝ),
    if_pos (Finset.mem_univ _)]

lemma sum_colU_sq (hW : ∀ i c, 0 < W i c) (x : ι → σ) (i : ι) :
    (∑ c : Bool, S.colU W x i c * S.colU W x i c) = (W i (S.col x i))⁻¹ := by
  have hpos := hW i (S.col x i)
  simp only [colU]
  rw [Fintype.sum_bool]
  cases hx : S.col x i <;>
    simp only [hx, if_true, if_false, ite_true, ite_false] <;> norm_num <;>
    rw [hx] at hpos <;>
    rw [← Real.sqrt_inv, Real.mul_self_sqrt (by positivity)]

lemma sum_colV_sq (hW : ∀ i c, 0 < W i c) (y : ι → σ) (i : ι) :
    (∑ c : Bool, S.colV W y i c * S.colV W y i c)
      = W i true + (if S.col y i then W i false else 0) := by
  simp only [colV]
  rw [Fintype.sum_bool]
  cases hy : S.col y i <;>
    simp only [hy, Bool.false_or, Bool.true_or, if_true, if_false, ite_true,
      ite_false] <;> norm_num <;>
    rw [Real.mul_self_sqrt (hW _ _).le] <;>
    try rw [Real.mul_self_sqrt (hW _ _).le] <;> ring

/-! ## The dual solution -/

/-- **The dual solution attached to a weighted scan.** -/
noncomputable def dual (hW : ∀ i c, 0 < W i c) :
    DualPair (ScanDim ι O Q) S.out where
  u x i := fun k => S.ndVec x i k.1 *
    (S.colU W x i k.2.1 * (phiVec (S.br x i) k.2.2.1 * phiVec (S.out x) k.2.2.2))
  v y i := fun k => S.ndVec y i k.1 *
    (S.colV W y i k.2.1 * (psiVec (S.br y i) k.2.2.1 * psiVec (S.out y) k.2.2.2))
  constraint x y := by
    classical
    have hpt : ∀ i : ι,
        (∑ k : ScanDim ι O Q,
          (S.ndVec x i k.1 * (S.colU W x i k.2.1 *
            (phiVec (S.br x i) k.2.2.1 * phiVec (S.out x) k.2.2.2))) *
          (S.ndVec y i k.1 * (S.colV W y i k.2.1 *
            (psiVec (S.br y i) k.2.2.1 * psiVec (S.out y) k.2.2.2))))
        = (if S.node x i = S.node y i then (1 : ℝ) else 0)
          * ((if S.col y i || S.col x i then (1 : ℝ) else 0)
            * ((if S.br x i = S.br y i then (0 : ℝ) else 1)
              * (if S.out x = S.out y then (0 : ℝ) else 1))) := by
      intro i
      rw [sum_four (S.ndVec x i) (S.ndVec y i) (S.colU W x i) (S.colV W y i)
        (phiVec (S.br x i)) (psiVec (S.br y i))
        (phiVec (S.out x)) (psiVec (S.out y)),
        S.sum_ndVec x y i, S.sum_col W hW x y i,
        sum_phiVec_mul_psiVec, sum_phiVec_mul_psiVec]
    simp only [hpt]
    -- each term is the indicator of the first divergence, times the output test
    have hterm : ∀ i : ι,
        (if x i = y i then (0 : ℝ)
          else (if S.node x i = S.node y i then (1 : ℝ) else 0)
            * ((if S.col y i || S.col x i then (1 : ℝ) else 0)
              * ((if S.br x i = S.br y i then (0 : ℝ) else 1)
                * (if S.out x = S.out y then (0 : ℝ) else 1))))
        = (if i ∈ S.divSet x y then (1 : ℝ) else 0)
          * (if S.out x = S.out y then (0 : ℝ) else 1) := by
      intro i
      have hmem : i ∈ S.divSet x y
          ↔ (S.br x i ≠ S.br y i ∧ S.node x i = S.node y i) := by
        simp [Scan.divSet]
      by_cases hnd : S.node x i = S.node y i
      · by_cases hbr : S.br x i = S.br y i
        · have h1 : i ∉ S.divSet x y := fun hc => (hmem.1 hc).1 hbr
          rw [if_neg h1, zero_mul]
          by_cases hxy : x i = y i
          · rw [if_pos hxy]
          · rw [if_neg hxy, if_pos hbr]
            ring
        · have hxy : x i ≠ y i := S.br_ne x y i (S.node_eq_iff.1 hnd) hbr
          have hcol : (S.col y i || S.col x i) = true := by
            by_contra hc
            simp only [Bool.or_eq_true, not_or] at hc
            exact hbr (S.black_unique x y i (by simpa using hc.2)
              (by simpa using hc.1) (S.node_eq_iff.1 hnd))
          have h2 : i ∈ S.divSet x y := hmem.2 ⟨hbr, hnd⟩
          rw [if_neg hxy, if_neg hbr, if_pos hnd, if_pos hcol, if_pos h2]
          ring
      · have h1 : i ∉ S.divSet x y := fun hc => hnd (hmem.1 hc).2
        rw [if_neg h1, zero_mul]
        by_cases hxy : x i = y i
        · rw [if_pos hxy]
        · rw [if_neg hxy, if_neg hnd]
          ring
    simp only [hterm]
    rw [← Finset.sum_mul]
    by_cases hout : S.out x = S.out y
    · rw [if_pos hout, mul_zero]
    · rw [if_neg hout, mul_one, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul, S.card_divSet_of_out_ne hout,
        Nat.cast_one, mul_one]

/-- The exact `ℓ²` mass of `u` at one coordinate: the reciprocal weight of the
branch taken there.

Stated per coordinate, not just summed, because a *weighted* cost inserts a
different factor at each one. -/
lemma sum_dual_u_sq_coord (hW : ∀ i c, 0 < W i c) (x : ι → σ) (i : ι) :
    (∑ k : ScanDim ι O Q, (S.dual W hW).u x i k * (S.dual W hW).u x i k)
      = 4 * (W i (S.col x i))⁻¹ := by
  show (∑ k : ScanDim ι O Q,
    (S.ndVec x i k.1 * (S.colU W x i k.2.1 *
      (phiVec (S.br x i) k.2.2.1 * phiVec (S.out x) k.2.2.2))) *
    (S.ndVec x i k.1 * (S.colU W x i k.2.1 *
      (phiVec (S.br x i) k.2.2.1 * phiVec (S.out x) k.2.2.2)))) = _
  rw [sum_four (S.ndVec x i) (S.ndVec x i) (S.colU W x i) (S.colU W x i)
    (phiVec (S.br x i)) (phiVec (S.br x i)) (phiVec (S.out x)) (phiVec (S.out x)),
    S.sum_ndVec_sq x i, S.sum_colU_sq W hW x i, sum_phiVec_sq, sum_phiVec_sq]
  ring

/-- The exact `ℓ²` mass of `u` at an input: the reciprocal weights of the
branches taken. -/
lemma sum_dual_u_sq (hW : ∀ i c, 0 < W i c) (x : ι → σ) :
    (∑ i : ι, ∑ k : ScanDim ι O Q, (S.dual W hW).u x i k * (S.dual W hW).u x i k)
      = 4 * ∑ i : ι, (W i (S.col x i))⁻¹ := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => S.sum_dual_u_sq_coord W hW x i

/-- The exact `ℓ²` mass of `v` at one coordinate: the weights of the other
colours. -/
lemma sum_dual_v_sq_coord (hW : ∀ i c, 0 < W i c) (y : ι → σ) (i : ι) :
    (∑ k : ScanDim ι O Q, (S.dual W hW).v y i k * (S.dual W hW).v y i k)
      = 4 * (W i true + if S.col y i then W i false else 0) := by
  show (∑ k : ScanDim ι O Q,
    (S.ndVec y i k.1 * (S.colV W y i k.2.1 *
      (psiVec (S.br y i) k.2.2.1 * psiVec (S.out y) k.2.2.2))) *
    (S.ndVec y i k.1 * (S.colV W y i k.2.1 *
      (psiVec (S.br y i) k.2.2.1 * psiVec (S.out y) k.2.2.2)))) = _
  rw [sum_four (S.ndVec y i) (S.ndVec y i) (S.colV W y i) (S.colV W y i)
    (psiVec (S.br y i)) (psiVec (S.br y i)) (psiVec (S.out y)) (psiVec (S.out y)),
    S.sum_ndVec_sq y i, S.sum_colV_sq W hW y i, sum_psiVec_sq, sum_psiVec_sq]
  ring

/-- The exact `ℓ²` mass of `v` at an input: the weights of the other colours. -/
lemma sum_dual_v_sq (hW : ∀ i c, 0 < W i c) (y : ι → σ) :
    (∑ i : ι, ∑ k : ScanDim ι O Q, (S.dual W hW).v y i k * (S.dual W hW).v y i k)
      = 4 * ∑ i : ι, (W i true + if S.col y i then W i false else 0) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => S.sum_dual_v_sq_coord W hW y i

/-- **The weighted cost of the scan dual.**  Each coordinate contributes its own
factor `c i`, which is what a composition with subproblems of differing costs
consumes. -/
theorem dual_isWeightedCostLe (hW : ∀ i c, 0 < W i c) {c : ι → ℝ} {V : ℝ}
    (hu : ∀ x : ι → σ, (4 : ℝ) * ∑ i, c i * (W i (S.col x i))⁻¹ ≤ V)
    (hv : ∀ y : ι → σ, (4 : ℝ) * ∑ i, c i *
      (W i true + if S.col y i then W i false else 0) ≤ V) :
    (S.dual W hW).IsWeightedCostLe c V := by
  constructor
  · intro x
    refine le_trans (le_of_eq ?_) (hu x)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [S.sum_dual_u_sq_coord W hW x i]; ring
  · intro y
    refine le_trans (le_of_eq ?_) (hv y)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [S.sum_dual_v_sq_coord W hW y i]; ring

/-- The cost of the scan dual: `u` pays the reciprocal weight of the branch it
takes, `v` pays the weights of the other colours. -/
theorem dual_isCostLe (hW : ∀ i c, 0 < W i c) {c : ℝ}
    (hu : ∀ x : ι → σ, (4 : ℝ) * ∑ i, (W i (S.col x i))⁻¹ ≤ c)
    (hv : ∀ y : ι → σ, (4 : ℝ) *
      ∑ i, (W i true + if S.col y i then W i false else 0) ≤ c) :
    (S.dual W hW).IsCostLe c :=
  ⟨fun x => (S.sum_dual_u_sq W hW x).trans_le (hu x),
   fun y => (S.sum_dual_v_sq W hW y).trans_le (hv y)⟩

end Scan

end QuantumQueryComplexity
