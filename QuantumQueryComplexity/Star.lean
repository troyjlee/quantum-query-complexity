import QuantumQueryComplexity.DualCompose
set_option linter.style.header false

/-!
# Star adversary matrices

A *star matrix* with centre `c` and leaf set `S` is `∑ z ∈ S, pairMatrix z c`:
the symmetric matrix whose only nonzero entries are the unit weights joining
`c` to each leaf.  Its spectral norm is `√|S|` (`norm_starMatrix`), and
masking it by a difference matrix restricts the leaf set to those leaves
differing from the centre in that coordinate
(`starMatrix_hadamard_advD`).

These are the optimal primal witnesses for `OR` and `AND`, and specialise to
the two-bit case of `QuantumQueryComplexity/AndOr.lean`.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-! ## Generic sum manipulations -/

lemma isHermitian_sum {α : Type*} {S : Finset α}
    {M : α → Matrix (ι → σ) (ι → σ) ℝ}
    (h : ∀ a ∈ S, (M a).IsHermitian) : (∑ a ∈ S, M a).IsHermitian := by
  show (∑ a ∈ S, M a)ᴴ = _
  ext x y
  simp only [Matrix.conjTranspose_apply, Matrix.sum_apply, star_trivial]
  exact Finset.sum_congr rfl fun a ha => (isHermitian_apply_symm (h a ha) y x)

lemma sum_mulVec {α : Type*} (S : Finset α)
    (M : α → Matrix (ι → σ) (ι → σ) ℝ) (y : (ι → σ) → ℝ) :
    (∑ a ∈ S, M a) *ᵥ y = ∑ a ∈ S, (M a *ᵥ y) := by
  funext w
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun v _ => Finset.sum_mul _ _ _

lemma sum_hadamard {α : Type*} (S : Finset α)
    (M : α → Matrix (ι → σ) (ι → σ) ℝ)
    (D : Matrix (ι → σ) (ι → σ) ℝ) :
    (∑ a ∈ S, M a) ⊙ D = ∑ a ∈ S, (M a ⊙ D) := by
  ext x y
  simp [Matrix.hadamard_apply, Matrix.sum_apply, Finset.sum_mul]

lemma sum_ite_const {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (C : ℝ) :
    (∑ a : α, if p a then C else 0)
      = ((Finset.univ.filter p).card : ℝ) * C := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-! ## The star matrix -/

/-- The star matrix with centre `c` and leaves `S`. -/
noncomputable def starMatrix (S : Finset (ι → σ)) (c : ι → σ) :
    Matrix (ι → σ) (ι → σ) ℝ := ∑ z ∈ S, pairMatrix z c

lemma starMatrix_isHermitian (S : Finset (ι → σ)) (c : ι → σ) :
    (starMatrix S c).IsHermitian :=
  isHermitian_sum fun z _ => pairMatrix_isHermitian z c

lemma starMatrix_mulVec_apply (S : Finset (ι → σ)) (c : ι → σ)
    (y : (ι → σ) → ℝ) (w : ι → σ) :
    (starMatrix S c *ᵥ y) w
      = (if w ∈ S then y c else 0) + (if c = w then ∑ z ∈ S, y z else 0) := by
  rw [starMatrix, sum_mulVec]
  simp only [Finset.sum_apply, pairMatrix_mulVec]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' S w fun _ => y c]
  congr 1
  by_cases hc : c = w
  · simp [hc]
  · simp [hc]

lemma starMatrix_bilinear {S : Finset (ι → σ)} {c : ι → σ} (hc : c ∉ S)
    (x y : (ι → σ) → ℝ) :
    x ⬝ᵥ starMatrix S c *ᵥ y
      = (∑ w ∈ S, x w) * y c + x c * ∑ z ∈ S, y z := by
  show (∑ w, x w * (starMatrix S c *ᵥ y) w) = _
  simp only [starMatrix_mulVec_apply, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [show (∑ w : ι → σ, x w * if w ∈ S then y c else 0)
        = ∑ w : ι → σ, if w ∈ S then x w * y c else 0 from
      Finset.sum_congr rfl fun w _ => by by_cases h : w ∈ S <;> simp [h]]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      ← Finset.sum_mul]
  · rw [show (∑ w : ι → σ, x w * if c = w then ∑ z ∈ S, y z else 0)
        = ∑ w : ι → σ, if c = w then x w * ∑ z ∈ S, y z else 0 from
      Finset.sum_congr rfl fun w _ => by by_cases h : c = w <;> simp [h]]
    rw [Finset.sum_ite_eq Finset.univ c fun w => x w * ∑ z ∈ S, y z]
    simp

/-- Splitting off the centre and the leaves from a sum over all inputs. -/
lemma sum_sq_ge {S : Finset (ι → σ)} {c : ι → σ} (hc : c ∉ S)
    (x : (ι → σ) → ℝ) :
    (∑ w ∈ S, x w * x w) + x c * x c ≤ x ⬝ᵥ x := by
  have hsub : (∑ w ∈ insert c S, x w * x w) ≤ ∑ w : ι → σ, x w * x w :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun w _ _ => mul_self_nonneg _
  rw [Finset.sum_insert hc] at hsub
  calc (∑ w ∈ S, x w * x w) + x c * x c
      = x c * x c + ∑ w ∈ S, x w * x w := by ring
    _ ≤ x ⬝ᵥ x := hsub

lemma norm_starMatrix_le {S : Finset (ι → σ)} {c : ι → σ} (hc : c ∉ S) :
    ‖starMatrix S c‖ ≤ Real.sqrt (S.card : ℝ) := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [starMatrix]
  refine l2_opNorm_le_of_forall_dotProduct _ (Real.sqrt_nonneg _) fun x y => ?_
  rw [starMatrix_bilinear hc]
  have hkpos : (0:ℝ) < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  have hCSx : (∑ w ∈ S, x w) ^ 2 ≤ (S.card : ℝ) * ∑ w ∈ S, x w * x w := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) x
    simpa [Finset.sum_const, sq] using h
  have hCSy : (∑ z ∈ S, y z) ^ 2 ≤ (S.card : ℝ) * ∑ z ∈ S, y z * y z := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) y
    simpa [Finset.sum_const, sq] using h
  have hx := sum_sq_ge hc x
  have hy := sum_sq_ge hc y
  have h2 : (∑ w ∈ S, x w) ^ 2 + (S.card : ℝ) * (x c) ^ 2
      ≤ (S.card : ℝ) * (x ⬝ᵥ x) := by nlinarith [hCSx, hx, hkpos.le]
  have h3 : (S.card : ℝ) * (y c) ^ 2 + (∑ z ∈ S, y z) ^ 2
      ≤ (S.card : ℝ) * (y ⬝ᵥ y) := by nlinarith [hCSy, hy, hkpos.le]
  have h1 : (S.card : ℝ) *
        ((∑ w ∈ S, x w) * y c + x c * ∑ z ∈ S, y z) ^ 2
      ≤ ((∑ w ∈ S, x w) ^ 2 + (S.card : ℝ) * (x c) ^ 2) *
        ((S.card : ℝ) * (y c) ^ 2 + (∑ z ∈ S, y z) ^ 2) := by
    nlinarith [sq_nonneg ((∑ w ∈ S, x w) * (∑ z ∈ S, y z)
      - (S.card : ℝ) * (x c * y c))]
  have hprod : ((∑ w ∈ S, x w) ^ 2 + (S.card : ℝ) * (x c) ^ 2) *
        ((S.card : ℝ) * (y c) ^ 2 + (∑ z ∈ S, y z) ^ 2)
      ≤ ((S.card : ℝ) * (x ⬝ᵥ x)) * ((S.card : ℝ) * (y ⬝ᵥ y)) :=
    mul_le_mul h2 h3 (by positivity)
      (mul_nonneg hkpos.le (dotProduct_self_nonneg x))
  have hchain : (S.card : ℝ) *
        ((∑ w ∈ S, x w) * y c + x c * ∑ z ∈ S, y z) ^ 2
      ≤ (S.card : ℝ) * ((S.card : ℝ) * (x ⬝ᵥ x) * (y ⬝ᵥ y)) :=
    h1.trans (hprod.trans (le_of_eq (by ring)))
  have hsq : ((∑ w ∈ S, x w) * y c + x c * ∑ z ∈ S, y z) ^ 2
      ≤ (S.card : ℝ) * (x ⬝ᵥ x) * (y ⬝ᵥ y) :=
    le_of_mul_le_mul_left hchain hkpos
  calc |(∑ w ∈ S, x w) * y c + x c * ∑ z ∈ S, y z|
      = Real.sqrt (((∑ w ∈ S, x w) * y c + x c * ∑ z ∈ S, y z) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((S.card : ℝ) * (x ⬝ᵥ x) * (y ⬝ᵥ y)) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (S.card : ℝ) * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
        rw [Real.sqrt_mul
            (mul_nonneg hkpos.le (dotProduct_self_nonneg x)),
          Real.sqrt_mul hkpos.le]

/-- The top eigenvector of a star matrix. -/
noncomputable def starVec (S : Finset (ι → σ)) (c : ι → σ) :
    (ι → σ) → ℝ :=
  fun w => if w ∈ S then 1 else if w = c then Real.sqrt (S.card : ℝ) else 0

lemma sqrt_card_le_norm_starMatrix {S : Finset (ι → σ)} {c : ι → σ}
    (hc : c ∉ S) (hS : S.Nonempty) :
    Real.sqrt (S.card : ℝ) ≤ ‖starMatrix S c‖ := by
  set k : ℝ := (S.card : ℝ) with hk
  have hkpos : 0 < k := by
    rw [hk]
    exact_mod_cast Finset.card_pos.mpr hS
  have hsk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hkpos.le
  set v := starVec S c with hv
  have hvc : v c = Real.sqrt k := by
    rw [hv, starVec, if_neg hc, if_pos rfl]
  have hvS : ∀ w ∈ S, v w = 1 := fun w hw => by rw [hv, starVec, if_pos hw]
  have hsum : (∑ w ∈ S, v w) = k := by
    rw [Finset.sum_congr rfl hvS, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hvv : v ⬝ᵥ v = 2 * k := by
    have hzero : ∀ w, w ∉ insert c S → v w * v w = 0 := by
      intro w hw
      rw [Finset.mem_insert] at hw
      push_neg at hw
      rw [hv, starVec, if_neg hw.2, if_neg hw.1, mul_zero]
    have h1 : v ⬝ᵥ v = ∑ w ∈ insert c S, v w * v w :=
      (Finset.sum_subset (Finset.subset_univ _) fun w _ hw => hzero w hw).symm
    rw [h1, Finset.sum_insert hc, hvc, hsk,
      Finset.sum_congr rfl (fun w hw => by rw [hvS w hw, mul_one]),
      Finset.sum_const, nsmul_eq_mul, mul_one, ← hk]
    ring
  have h := abs_dotProduct_mulVec_le (starMatrix S c) v v
  rw [starMatrix_bilinear hc, hsum, hvc, hvv] at h
  have habs : |k * Real.sqrt k + Real.sqrt k * k| = 2 * k * Real.sqrt k := by
    rw [abs_of_nonneg (by positivity)]
    ring
  have h2k : Real.sqrt (2 * k) * Real.sqrt (2 * k) = 2 * k :=
    Real.mul_self_sqrt (by positivity)
  rw [habs] at h
  nlinarith [h, h2k, hkpos, Real.sqrt_nonneg k]

theorem norm_starMatrix {S : Finset (ι → σ)} {c : ι → σ} (hc : c ∉ S)
    (hS : S.Nonempty) : ‖starMatrix S c‖ = Real.sqrt (S.card : ℝ) :=
  le_antisymm (norm_starMatrix_le hc) (sqrt_card_le_norm_starMatrix hc hS)

lemma starMatrix_hadamard_advD (S : Finset (ι → σ)) (c : ι → σ)
    (i : ι) :
    starMatrix S c ⊙ advD i
      = starMatrix (S.filter fun z => ¬(z i = c i)) c := by
  rw [starMatrix, sum_hadamard,
    Finset.sum_congr rfl fun z (_ : z ∈ S) => pairMatrix_hadamard_advD z c i,
    starMatrix, Finset.sum_filter]
  exact Finset.sum_congr rfl fun z _ => by
    by_cases h : z i = c i <;> simp [h]

/-! ## Weighted star matrices

Giving the edges weights `w` replaces the leaf count `|S|` by the total
squared weight `∑ w²`.  This is what the *cost* version of the adversary
bound needs: for `OR_k` with costs `c`, the weighted star with `w = c`
certifies the value `√(∑ cᵢ²)` with masked norms `cᵢ`.
-/

/-- The star matrix with centre `c`, leaves `S` and edge weights `w`. -/
noncomputable def wStarMatrix (S : Finset (ι → σ)) (c : ι → σ)
    (w : (ι → σ) → ℝ) : Matrix (ι → σ) (ι → σ) ℝ :=
  ∑ z ∈ S, w z • pairMatrix z c

/-- The total squared weight of a star. -/
def starWeight (S : Finset (ι → σ)) (w : (ι → σ) → ℝ) : ℝ :=
  ∑ z ∈ S, w z * w z

lemma starWeight_nonneg (S : Finset (ι → σ)) (w : (ι → σ) → ℝ) :
    0 ≤ starWeight S w :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

lemma wStarMatrix_isHermitian (S : Finset (ι → σ)) (c : ι → σ)
    (w : (ι → σ) → ℝ) : (wStarMatrix S c w).IsHermitian :=
  isHermitian_sum fun z _ =>
    (pairMatrix_isHermitian z c).smul (star_trivial (w z))

lemma wStarMatrix_mulVec_apply (S : Finset (ι → σ)) (c : ι → σ)
    (w : (ι → σ) → ℝ) (y : (ι → σ) → ℝ) (v : ι → σ) :
    (wStarMatrix S c w *ᵥ y) v
      = (if v ∈ S then w v * y c else 0)
        + (if c = v then ∑ z ∈ S, w z * y z else 0) := by
  rw [wStarMatrix, sum_mulVec]
  simp only [Finset.sum_apply, Matrix.smul_mulVec, pairMatrix_mulVec,
    Pi.smul_apply, smul_eq_mul]
  rw [show (∑ z ∈ S, w z * ((if z = v then y c else 0)
        + (if c = v then y z else 0)))
      = (∑ z ∈ S, if z = v then w z * y c else 0)
        + ∑ z ∈ S, (if c = v then w z * y z else 0) from by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => by
      by_cases h1 : z = v <;> by_cases h2 : c = v <;> simp [h1, h2] <;> ring]
  rw [Finset.sum_ite_eq' S v fun z => w z * y c]
  congr 1
  by_cases hcv : c = v
  · simp [hcv]
  · simp [hcv]

lemma wStarMatrix_bilinear {S : Finset (ι → σ)} {c : ι → σ}
    (hc : c ∉ S) (w : (ι → σ) → ℝ) (x y : (ι → σ) → ℝ) :
    x ⬝ᵥ wStarMatrix S c w *ᵥ y
      = (∑ z ∈ S, w z * x z) * y c + x c * ∑ z ∈ S, w z * y z := by
  show (∑ v, x v * (wStarMatrix S c w *ᵥ y) v) = _
  simp only [wStarMatrix_mulVec_apply, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [show (∑ v : ι → σ, x v * if v ∈ S then w v * y c else 0)
        = ∑ v : ι → σ, if v ∈ S then (w v * x v) * y c else 0 from
      Finset.sum_congr rfl fun v _ => by
        by_cases h : v ∈ S <;> simp [h] <;> ring]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      ← Finset.sum_mul]
  · rw [show (∑ v : ι → σ, x v * if c = v then ∑ z ∈ S, w z * y z else 0)
        = ∑ v : ι → σ, if c = v then x v * ∑ z ∈ S, w z * y z else 0 from
      Finset.sum_congr rfl fun v _ => by by_cases h : c = v <;> simp [h]]
    rw [Finset.sum_ite_eq Finset.univ c fun v => x v * ∑ z ∈ S, w z * y z]
    simp

lemma norm_wStarMatrix_le {S : Finset (ι → σ)} {c : ι → σ} (hc : c ∉ S)
    (w : (ι → σ) → ℝ) :
    ‖wStarMatrix S c w‖ ≤ Real.sqrt (starWeight S w) := by
  rcases eq_or_lt_of_le (starWeight_nonneg S w) with hW | hWpos
  · have hzero : ∀ z ∈ S, w z = 0 := by
      intro z hz
      have h := (Finset.sum_eq_zero_iff_of_nonneg
        (fun z _ => mul_self_nonneg (w z))).mp hW.symm z hz
      exact mul_self_eq_zero.mp h
    have h0 : wStarMatrix S c w = 0 :=
      Finset.sum_eq_zero fun z hz => by rw [hzero z hz, zero_smul]
    rw [h0, norm_zero, ← hW, Real.sqrt_zero]
  refine l2_opNorm_le_of_forall_dotProduct _ (Real.sqrt_nonneg _) fun x y => ?_
  rw [wStarMatrix_bilinear hc]
  have hCSx : (∑ z ∈ S, w z * x z) ^ 2
      ≤ starWeight S w * ∑ z ∈ S, x z * x z := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S w x
    simpa [starWeight, sq] using h
  have hCSy : (∑ z ∈ S, w z * y z) ^ 2
      ≤ starWeight S w * ∑ z ∈ S, y z * y z := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S w y
    simpa [starWeight, sq] using h
  have hx := sum_sq_ge hc x
  have hy := sum_sq_ge hc y
  have h2 : (∑ z ∈ S, w z * x z) ^ 2 + starWeight S w * (x c) ^ 2
      ≤ starWeight S w * (x ⬝ᵥ x) := by nlinarith [hCSx, hx, hWpos.le]
  have h3 : starWeight S w * (y c) ^ 2 + (∑ z ∈ S, w z * y z) ^ 2
      ≤ starWeight S w * (y ⬝ᵥ y) := by nlinarith [hCSy, hy, hWpos.le]
  have h1 : starWeight S w *
        ((∑ z ∈ S, w z * x z) * y c + x c * ∑ z ∈ S, w z * y z) ^ 2
      ≤ ((∑ z ∈ S, w z * x z) ^ 2 + starWeight S w * (x c) ^ 2) *
        (starWeight S w * (y c) ^ 2 + (∑ z ∈ S, w z * y z) ^ 2) := by
    nlinarith [sq_nonneg ((∑ z ∈ S, w z * x z) * (∑ z ∈ S, w z * y z)
      - starWeight S w * (x c * y c))]
  have hprod : ((∑ z ∈ S, w z * x z) ^ 2 + starWeight S w * (x c) ^ 2) *
        (starWeight S w * (y c) ^ 2 + (∑ z ∈ S, w z * y z) ^ 2)
      ≤ (starWeight S w * (x ⬝ᵥ x)) * (starWeight S w * (y ⬝ᵥ y)) :=
    mul_le_mul h2 h3 (by positivity)
      (mul_nonneg hWpos.le (dotProduct_self_nonneg x))
  have hchain : starWeight S w *
        ((∑ z ∈ S, w z * x z) * y c + x c * ∑ z ∈ S, w z * y z) ^ 2
      ≤ starWeight S w * (starWeight S w * (x ⬝ᵥ x) * (y ⬝ᵥ y)) :=
    h1.trans (hprod.trans (le_of_eq (by ring)))
  have hsq : ((∑ z ∈ S, w z * x z) * y c + x c * ∑ z ∈ S, w z * y z) ^ 2
      ≤ starWeight S w * (x ⬝ᵥ x) * (y ⬝ᵥ y) :=
    le_of_mul_le_mul_left hchain hWpos
  calc |(∑ z ∈ S, w z * x z) * y c + x c * ∑ z ∈ S, w z * y z|
      = Real.sqrt (((∑ z ∈ S, w z * x z) * y c
          + x c * ∑ z ∈ S, w z * y z) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (starWeight S w * (x ⬝ᵥ x) * (y ⬝ᵥ y)) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (starWeight S w) * Real.sqrt (x ⬝ᵥ x) *
          Real.sqrt (y ⬝ᵥ y) := by
        rw [Real.sqrt_mul
            (mul_nonneg hWpos.le (dotProduct_self_nonneg x)),
          Real.sqrt_mul hWpos.le]

/-- The top eigenvector of a weighted star matrix. -/
noncomputable def wStarVec (S : Finset (ι → σ)) (c : ι → σ)
    (w : (ι → σ) → ℝ) : (ι → σ) → ℝ :=
  fun v => if v ∈ S then w v
    else if v = c then Real.sqrt (starWeight S w) else 0

lemma sqrt_starWeight_le_norm_wStarMatrix {S : Finset (ι → σ)}
    {c : ι → σ} (hc : c ∉ S) {w : (ι → σ) → ℝ}
    (hW : 0 < starWeight S w) :
    Real.sqrt (starWeight S w) ≤ ‖wStarMatrix S c w‖ := by
  set W : ℝ := starWeight S w with hWdef
  have hsW : Real.sqrt W * Real.sqrt W = W := Real.mul_self_sqrt hW.le
  set v := wStarVec S c w with hv
  have hvc : v c = Real.sqrt W := by
    rw [hv, wStarVec, if_neg hc, if_pos rfl]
  have hvS : ∀ z ∈ S, v z = w z := fun z hz => by rw [hv, wStarVec, if_pos hz]
  have hsum : (∑ z ∈ S, w z * v z) = W := by
    rw [Finset.sum_congr rfl fun z hz => by rw [hvS z hz]]
    exact hWdef.symm
  have hvv : v ⬝ᵥ v = 2 * W := by
    have hzero : ∀ u, u ∉ insert c S → v u * v u = 0 := by
      intro u hu
      rw [Finset.mem_insert] at hu
      push_neg at hu
      rw [hv, wStarVec, if_neg hu.2, if_neg hu.1, mul_zero]
    have h1 : v ⬝ᵥ v = ∑ u ∈ insert c S, v u * v u :=
      (Finset.sum_subset (Finset.subset_univ _) fun u _ hu => hzero u hu).symm
    rw [h1, Finset.sum_insert hc, hvc, hsW,
      Finset.sum_congr rfl (fun z hz => by rw [hvS z hz]),
      show (∑ z ∈ S, w z * w z) = W from hWdef.symm]
    ring
  have h := abs_dotProduct_mulVec_le (wStarMatrix S c w) v v
  rw [wStarMatrix_bilinear hc, hsum, hvc, hvv] at h
  have habs : |W * Real.sqrt W + Real.sqrt W * W| = 2 * W * Real.sqrt W := by
    rw [abs_of_nonneg (by positivity)]
    ring
  have h2W : Real.sqrt (2 * W) * Real.sqrt (2 * W) = 2 * W :=
    Real.mul_self_sqrt (by positivity)
  rw [habs] at h
  nlinarith [h, h2W, hW, Real.sqrt_nonneg W]

theorem norm_wStarMatrix {S : Finset (ι → σ)} {c : ι → σ} (hc : c ∉ S)
    {w : (ι → σ) → ℝ} (hW : 0 < starWeight S w) :
    ‖wStarMatrix S c w‖ = Real.sqrt (starWeight S w) :=
  le_antisymm (norm_wStarMatrix_le hc w) (sqrt_starWeight_le_norm_wStarMatrix hc hW)

lemma wStarMatrix_hadamard_advD (S : Finset (ι → σ)) (c : ι → σ)
    (w : (ι → σ) → ℝ) (i : ι) :
    wStarMatrix S c w ⊙ advD i
      = wStarMatrix (S.filter fun z => ¬(z i = c i)) c w := by
  rw [wStarMatrix, sum_hadamard]
  rw [Finset.sum_congr rfl fun z (_ : z ∈ S) => by
    rw [Matrix.smul_hadamard, pairMatrix_hadamard_advD z c i]]
  rw [wStarMatrix, Finset.sum_filter]
  exact Finset.sum_congr rfl fun z _ => by
    by_cases h : z i = c i <;> simp [h]

end QuantumQueryComplexity
