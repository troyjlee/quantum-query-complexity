import QuantumQueryComplexity.Duality.Gram
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Analysis.Convex.Basic

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The two convex sets of the separation argument

The dual program is separated from its target inside the finite-dimensional
coordinate space `DualOmega ι σ → ℝ`, whose coordinates are indexed by a pair
of inputs (the constraint `gramR`) or by an input together with a side tag (the
two costs `gramCost`).  The map assembling those coordinates from a Gram matrix
is `gramL`.

Two sets live there:

* `gramImage T`, the image of the positive semidefinite matrices of trace at
  most `T` — convex because the positive semidefinite cone is, and **compact**
  because that truncated cone is closed and bounded in a finite-dimensional
  space (`‖G‖ ≤ G.trace` for positive semidefinite `G`);
* `dualBox g c`, the points whose constraint block is the dual target and whose
  cost block lies in `[0, c]` — convex and closed.

Truncating the cone at a finite trace is what makes `gramImage` compact, and
hence what lets `geometric_hahn_banach_compact_closed` apply without any
closedness-of-image argument; the truncation is harmless because a dual
solution of cost at most `c` has trace at most `2 c · card (ι → σ)`.

This file also records `apply_eq_sum_single`, which reads the coefficients of a
continuous linear functional off its values on the standard basis.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-! ## Positive semidefinite matrices of bounded trace -/

section PsdNorm

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For a positive semidefinite matrix the spectral norm is at most the trace:
the eigenvalues are nonnegative, so the largest is at most their sum. -/
lemma norm_le_trace_of_posSemidef {G : Matrix n n ℝ} (hG : G.PosSemidef) :
    ‖G‖ ≤ G.trace := by
  have htr : G.trace = ∑ i, hG.1.eigenvalues i := by
    simpa using hG.1.trace_eq_sum_eigenvalues
  refine norm_le_of_forall_abs_eigenvalues_le hG.1 ?_ fun j => ?_
  · rw [htr]
    exact Finset.sum_nonneg fun i _ => hG.eigenvalues_nonneg i
  · rw [abs_of_nonneg (hG.eigenvalues_nonneg j), htr]
    exact Finset.single_le_sum (fun i _ => hG.eigenvalues_nonneg i) (Finset.mem_univ j)

end PsdNorm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The coordinate index of the ambient space of the separation argument: a
pair of inputs for each constraint, and an input with a side tag for each cost
variable. -/
abbrev DualOmega (ι σ : Type*) : Type _ := ((ι → σ) × (ι → σ)) ⊕ ((ι → σ) × Bool)

/-- The affine data of the dual program, read off a Gram matrix. -/
def gramL (G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ) : DualOmega ι σ → ℝ :=
  Sum.elim (fun q => gramR G q.1 q.2) (fun q => gramCost G q.2 q.1)

@[simp] lemma gramL_inl (G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ)
    (x y : ι → σ) : gramL G (Sum.inl (x, y)) = gramR G x y := rfl

@[simp] lemma gramL_inr (G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ)
    (x : ι → σ) (b : Bool) : gramL G (Sum.inr (x, b)) = gramCost G b x := rfl

/-- `gramL` as a linear map. -/
def gramLₗ : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ →ₗ[ℝ] (DualOmega ι σ → ℝ) where
  toFun := gramL
  map_add' G H := by
    funext z
    rcases z with ⟨x, y⟩ | ⟨x, b⟩
    · simpa using congrFun₂ (gramR_add G H) x y
    · simpa using gramCost_add G H b x
  map_smul' c G := by
    funext z
    rcases z with ⟨x, y⟩ | ⟨x, b⟩
    · simpa using congrFun₂ (gramR_smul c G) x y
    · simpa using gramCost_smul c G b x

@[simp] lemma gramLₗ_apply (G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ) :
    gramLₗ G = gramL G := rfl

/-- Entry evaluation, as a linear map (hence continuous, the space being
finite-dimensional). -/
private def entryₗ (z z' : GramIdx ι σ) :
    Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ →ₗ[ℝ] ℝ where
  toFun G := G z z'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma continuous_matrixEntry (z z' : GramIdx ι σ) :
    Continuous fun G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ => G z z' :=
  (entryₗ z z').continuous_of_finiteDimensional

/-- The trace, as a linear map. -/
private def traceₗ : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ →ₗ[ℝ] ℝ where
  toFun G := G.trace
  map_add' := Matrix.trace_add
  map_smul' c G := by simpa using Matrix.trace_smul c G

lemma continuous_matrixTrace :
    Continuous fun G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ => G.trace :=
  traceₗ.continuous_of_finiteDimensional

lemma continuous_gramL :
    Continuous (gramL : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ → DualOmega ι σ → ℝ) :=
  gramLₗ.continuous_of_finiteDimensional

/-- Positive semidefinite matrices of trace at most `T`. -/
def psdBall (ι σ : Type*) [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (T : ℝ) : Set (Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ) :=
  {G | G.PosSemidef ∧ G.trace ≤ T}

lemma convex_psdBall (T : ℝ) : Convex ℝ (psdBall ι σ T) := by
  rintro G ⟨hG, hGT⟩ H ⟨hH, hHT⟩ a b ha hb hab
  refine ⟨(hG.smul ha).add (hH.smul hb), ?_⟩
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  have h1 : a * G.trace ≤ a * T := mul_le_mul_of_nonneg_left hGT ha
  have h2 : b * H.trace ≤ b * T := mul_le_mul_of_nonneg_left hHT hb
  have h3 : a * T + b * T = T := by rw [← add_mul, hab, one_mul]
  linarith

lemma isClosed_psdBall (T : ℝ) : IsClosed (psdBall ι σ T) := by
  have hset : psdBall ι σ T =
      (⋂ (z : GramIdx ι σ) (z' : GramIdx ι σ), {G | G z' z = G z z'}) ∩
        ((⋂ v : GramIdx ι σ → ℝ, {G | 0 ≤ v ⬝ᵥ G *ᵥ v}) ∩
          {G | G.trace ≤ T}) := by
    ext G
    simp only [psdBall, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hG, hT⟩
      refine ⟨fun z z' => ?_, fun v => ?_, hT⟩
      · simpa using congrFun₂ hG.1 z z'
      · simpa using hG.dotProduct_mulVec_nonneg v
    · rintro ⟨hherm, hquad, hT⟩
      have hH : G.IsHermitian := by
        show Gᴴ = G
        ext z z'
        simpa [Matrix.conjTranspose_apply] using hherm z z'
      refine ⟨Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun v => ?_, hT⟩
      · simpa using hquad v
  rw [hset]
  refine IsClosed.inter (isClosed_iInter fun z => isClosed_iInter fun z' => ?_)
    (IsClosed.inter (isClosed_iInter fun v => ?_) ?_)
  · exact isClosed_eq (continuous_matrixEntry z' z) (continuous_matrixEntry z z')
  · refine isClosed_le continuous_const ?_
    have : (fun G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ => v ⬝ᵥ G *ᵥ v)
        = fun G => ∑ z, ∑ z', v z * G z z' * v z' := by
      funext G; exact dotProduct_mulVec_eq_sum G v v
    rw [this]
    exact continuous_finset_sum _ fun z _ => continuous_finset_sum _ fun z' _ =>
      ((continuous_const.mul (continuous_matrixEntry z z')).mul continuous_const)
  · exact isClosed_le continuous_matrixTrace continuous_const

lemma isCompact_psdBall (T : ℝ) : IsCompact (psdBall ι σ T) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_psdBall T) ?_
  have hsub : psdBall ι σ T ⊆
      Metric.closedBall (0 : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ) T := by
    rintro G ⟨hG, hGT⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_trace_of_posSemidef hG).trans hGT
  exact Metric.isBounded_closedBall.subset hsub

/-! ## The two sets -/

/-- The image of the truncated positive semidefinite cone: the affine data
achievable by dual solutions of total weight at most `T`. -/
def gramImage (ι σ : Type*) [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (T : ℝ) : Set (DualOmega ι σ → ℝ) := gramL '' psdBall ι σ T

lemma convex_gramImage (T : ℝ) : Convex ℝ (gramImage ι σ T) :=
  (convex_psdBall T).linear_image gramLₗ

lemma isCompact_gramImage (T : ℝ) : IsCompact (gramImage ι σ T) :=
  (isCompact_psdBall T).image continuous_gramL

lemma zero_mem_gramImage {T : ℝ} (hT : 0 ≤ T) : (0 : DualOmega ι σ → ℝ) ∈ gramImage ι σ T := by
  refine ⟨0, ⟨Matrix.PosSemidef.zero, by simpa using hT⟩, ?_⟩
  funext z
  rcases z with ⟨x, y⟩ | ⟨x, b⟩
  · simp [gramR]
  · simp [gramCost]

lemma mem_gramImage_vecMulVec {T : ℝ} (w : GramIdx ι σ → ℝ)
    (hw : ∑ z, w z * w z ≤ T) : gramL (vecMulVec w w) ∈ gramImage ι σ T :=
  ⟨vecMulVec w w, ⟨posSemidef_vecMulVec_self w, by rwa [trace_vecMulVec]⟩, rfl⟩

/-- The target of the dual program: constraint block equal to `dualTarget g`,
cost block in `[0, c]`. -/
def dualBox (g : (ι → σ) → Bool) (c : ℝ) : Set (DualOmega ι σ → ℝ) :=
  {z | (∀ x y, z (Sum.inl (x, y)) = dualTarget g x y) ∧
    ∀ q : (ι → σ) × Bool, 0 ≤ z (Sum.inr q) ∧ z (Sum.inr q) ≤ c}

lemma convex_dualBox (g : (ι → σ) → Bool) (c : ℝ) : Convex ℝ (dualBox g c) := by
  rintro z ⟨hz1, hz2⟩ z' ⟨hz1', hz2'⟩ a b ha hb hab
  constructor
  · intro x y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz1 x y, hz1' x y]
    rw [← add_mul, hab, one_mul]
  · intro q
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · have := (hz2 q).1
      have := (hz2' q).1
      positivity
    · nlinarith [(hz2 q).2, (hz2' q).2, (hz2 q).1, (hz2' q).1]

lemma isClosed_dualBox (g : (ι → σ) → Bool) (c : ℝ) : IsClosed (dualBox g c) := by
  have hset : dualBox g c =
      (⋂ (x : ι → σ) (y : ι → σ), {z : DualOmega ι σ → ℝ |
          z (Sum.inl (x, y)) = dualTarget g x y}) ∩
        ⋂ q : (ι → σ) × Bool,
          ({z : DualOmega ι σ → ℝ | 0 ≤ z (Sum.inr q)} ∩
            {z : DualOmega ι σ → ℝ | z (Sum.inr q) ≤ c}) := by
    ext z
    simp only [dualBox, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  refine IsClosed.inter (isClosed_iInter fun x => isClosed_iInter fun y => ?_)
    (isClosed_iInter fun q => IsClosed.inter ?_ ?_)
  · exact isClosed_eq (continuous_apply _) continuous_const
  · exact isClosed_le continuous_const (continuous_apply _)
  · exact isClosed_le (continuous_apply _) continuous_const

/-- The corner of the box: the dual target with every cost variable at `c`. -/
def dualCorner (g : (ι → σ) → Bool) (c : ℝ) : DualOmega ι σ → ℝ :=
  Sum.elim (fun q => dualTarget g q.1 q.2) (fun _ => c)

lemma dualCorner_mem {g : (ι → σ) → Bool} {c : ℝ} (hc : 0 ≤ c) :
    dualCorner g c ∈ dualBox g c :=
  ⟨fun _ _ => rfl, fun _ => ⟨hc, le_refl c⟩⟩

/-! ## Reading off the coefficients of a functional -/

/-- A linear functional on a finite coordinate space is the pairing with its
values on the standard basis. -/
lemma apply_eq_sum_single {α : Type*} [Fintype α] [DecidableEq α]
    (φ : (α → ℝ) →L[ℝ] ℝ) (z : α → ℝ) : φ z = ∑ a, z a * φ (Pi.single a 1) := by
  have hz : z = ∑ a, z a • (Pi.single a 1 : α → ℝ) := by
    rw [← Finset.univ_sum_single z]
    exact Finset.sum_congr rfl fun a _ => by
      funext b
      by_cases h : a = b <;> simp [Pi.single_apply, h]
  conv_lhs => rw [hz]
  rw [map_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [map_smul, smul_eq_mul]

end QuantumQueryComplexity
