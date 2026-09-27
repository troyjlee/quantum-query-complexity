import QuantumQueryComplexity.Duality.Compact
import QuantumQueryComplexity.Duality.GramOn
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The two convex sets of the separation argument, on a promise domain

The promise mirror of `Duality/Compact.lean`: the ambient coordinate space is
`DualOmegaOn X → ℝ`, the compact set is the image of the truncated positive
semidefinite cone over `GramIdxOn X ι`, and the closed set is the box around
the promise dual target.  `norm_le_trace_of_posSemidef` and
`apply_eq_sum_single` are generic and imported, not re-proved.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The coordinate index of the ambient space: a pair of promise inputs for
each constraint, and an input with a side tag for each cost variable. -/
abbrev DualOmegaOn (X : Type*) : Type _ := (X × X) ⊕ (X × Bool)

/-- The affine data of the promise dual program, read off a Gram matrix. -/
def gramLOn (read : X → ι → σ)
    (G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) : DualOmegaOn X → ℝ :=
  Sum.elim (fun q => gramROn read G q.1 q.2) (fun q => gramCostOn G q.2 q.1)

@[simp] lemma gramLOn_inl (read : X → ι → σ)
    (G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) (x y : X) :
    gramLOn read G (Sum.inl (x, y)) = gramROn read G x y := rfl

@[simp] lemma gramLOn_inr (read : X → ι → σ)
    (G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) (x : X) (b : Bool) :
    gramLOn read G (Sum.inr (x, b)) = gramCostOn G b x := rfl

/-- `gramLOn` as a linear map. -/
def gramLOnₗ (read : X → ι → σ) :
    Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ →ₗ[ℝ] (DualOmegaOn X → ℝ) where
  toFun := gramLOn read
  map_add' G H := by
    funext z
    rcases z with ⟨x, y⟩ | ⟨x, b⟩
    · simpa using congrFun₂ (gramROn_add read G H) x y
    · simpa using gramCostOn_add G H b x
  map_smul' c G := by
    funext z
    rcases z with ⟨x, y⟩ | ⟨x, b⟩
    · simpa using congrFun₂ (gramROn_smul read c G) x y
    · simpa using gramCostOn_smul c G b x

@[simp] lemma gramLOnₗ_apply (read : X → ι → σ)
    (G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) :
    gramLOnₗ read G = gramLOn read G := rfl

private def entryOnₗ (z z' : GramIdxOn X ι) :
    Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ →ₗ[ℝ] ℝ where
  toFun G := G z z'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma continuous_matrixEntryOn (z z' : GramIdxOn X ι) :
    Continuous fun G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ => G z z' :=
  (entryOnₗ z z').continuous_of_finiteDimensional

private def traceOnₗ :
    Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ →ₗ[ℝ] ℝ where
  toFun G := G.trace
  map_add' := Matrix.trace_add
  map_smul' c G := by simpa using Matrix.trace_smul c G

lemma continuous_matrixTraceOn :
    Continuous fun G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ => G.trace :=
  traceOnₗ.continuous_of_finiteDimensional

lemma continuous_gramLOn (read : X → ι → σ) :
    Continuous
      (gramLOn read :
        Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ → DualOmegaOn X → ℝ) :=
  (gramLOnₗ read).continuous_of_finiteDimensional

/-- Positive semidefinite matrices of trace at most `T`. -/
def psdBallOn (X ι : Type*) [Fintype X] [DecidableEq X] [Fintype ι]
    [DecidableEq ι] (T : ℝ) : Set (Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) :=
  {G | G.PosSemidef ∧ G.trace ≤ T}

lemma convex_psdBallOn (T : ℝ) : Convex ℝ (psdBallOn X ι T) := by
  rintro G ⟨hG, hGT⟩ H ⟨hH, hHT⟩ a b ha hb hab
  refine ⟨(hG.smul ha).add (hH.smul hb), ?_⟩
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul,
    smul_eq_mul]
  have h1 : a * G.trace ≤ a * T := mul_le_mul_of_nonneg_left hGT ha
  have h2 : b * H.trace ≤ b * T := mul_le_mul_of_nonneg_left hHT hb
  have h3 : a * T + b * T = T := by rw [← add_mul, hab, one_mul]
  linarith

lemma isClosed_psdBallOn (T : ℝ) : IsClosed (psdBallOn X ι T) := by
  have hset : psdBallOn X ι T =
      (⋂ (z : GramIdxOn X ι) (z' : GramIdxOn X ι), {G | G z' z = G z z'}) ∩
        ((⋂ v : GramIdxOn X ι → ℝ, {G | 0 ≤ v ⬝ᵥ G *ᵥ v}) ∩
          {G | G.trace ≤ T}) := by
    ext G
    simp only [psdBallOn, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
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
  · exact isClosed_eq (continuous_matrixEntryOn z' z) (continuous_matrixEntryOn z z')
  · refine isClosed_le continuous_const ?_
    have : (fun G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ => v ⬝ᵥ G *ᵥ v)
        = fun G => ∑ z, ∑ z', v z * G z z' * v z' := by
      funext G; exact dotProduct_mulVec_eq_sum G v v
    rw [this]
    exact continuous_finset_sum _ fun z _ => continuous_finset_sum _ fun z' _ =>
      ((continuous_const.mul (continuous_matrixEntryOn z z')).mul
        continuous_const)
  · exact isClosed_le continuous_matrixTraceOn continuous_const

lemma isCompact_psdBallOn (T : ℝ) : IsCompact (psdBallOn X ι T) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_psdBallOn T) ?_
  have hsub : psdBallOn X ι T ⊆
      Metric.closedBall (0 : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) T := by
    rintro G ⟨hG, hGT⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_trace_of_posSemidef hG).trans hGT
  exact Metric.isBounded_closedBall.subset hsub

/-! ## The two sets -/

/-- The image of the truncated positive semidefinite cone. -/
def gramImageOn (read : X → ι → σ) (T : ℝ) : Set (DualOmegaOn X → ℝ) :=
  gramLOn read '' psdBallOn X ι T

lemma convex_gramImageOn (read : X → ι → σ) (T : ℝ) :
    Convex ℝ (gramImageOn read T) :=
  (convex_psdBallOn T).linear_image (gramLOnₗ read)

lemma isCompact_gramImageOn (read : X → ι → σ) (T : ℝ) :
    IsCompact (gramImageOn read T) :=
  (isCompact_psdBallOn T).image (continuous_gramLOn read)

lemma zero_mem_gramImageOn {read : X → ι → σ} {T : ℝ} (hT : 0 ≤ T) :
    (0 : DualOmegaOn X → ℝ) ∈ gramImageOn read T := by
  refine ⟨0, ⟨Matrix.PosSemidef.zero, by simpa using hT⟩, ?_⟩
  funext z
  rcases z with ⟨x, y⟩ | ⟨x, b⟩
  · simp [gramROn]
  · simp [gramCostOn]

lemma mem_gramImageOn_vecMulVec {read : X → ι → σ} {T : ℝ}
    (w : GramIdxOn X ι → ℝ) (hw : ∑ z, w z * w z ≤ T) :
    gramLOn read (vecMulVec w w) ∈ gramImageOn read T :=
  ⟨vecMulVec w w, ⟨posSemidef_vecMulVec_self_on w,
    by rwa [trace_vecMulVec_on]⟩, rfl⟩

/-- The target of the promise dual program: constraint block equal to
`dualTargetOn f`, cost block in `[0, c]`. -/
def dualBoxOn (f : X → Bool) (c : ℝ) : Set (DualOmegaOn X → ℝ) :=
  {z | (∀ x y, z (Sum.inl (x, y)) = dualTargetOn f x y) ∧
    ∀ q : X × Bool, 0 ≤ z (Sum.inr q) ∧ z (Sum.inr q) ≤ c}

lemma convex_dualBoxOn (f : X → Bool) (c : ℝ) : Convex ℝ (dualBoxOn f c) := by
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

lemma isClosed_dualBoxOn (f : X → Bool) (c : ℝ) : IsClosed (dualBoxOn f c) := by
  have hset : dualBoxOn f c =
      (⋂ (x : X) (y : X), {z : DualOmegaOn X → ℝ |
          z (Sum.inl (x, y)) = dualTargetOn f x y}) ∩
        ⋂ q : X × Bool,
          ({z : DualOmegaOn X → ℝ | 0 ≤ z (Sum.inr q)} ∩
            {z : DualOmegaOn X → ℝ | z (Sum.inr q) ≤ c}) := by
    ext z
    simp only [dualBoxOn, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  refine IsClosed.inter (isClosed_iInter fun x => isClosed_iInter fun y => ?_)
    (isClosed_iInter fun q => IsClosed.inter ?_ ?_)
  · exact isClosed_eq (continuous_apply _) continuous_const
  · exact isClosed_le continuous_const (continuous_apply _)
  · exact isClosed_le (continuous_apply _) continuous_const

/-- The corner of the box. -/
def dualCornerOn (f : X → Bool) (c : ℝ) : DualOmegaOn X → ℝ :=
  Sum.elim (fun q => dualTargetOn f q.1 q.2) (fun _ => c)

lemma dualCornerOn_mem {f : X → Bool} {c : ℝ} (hc : 0 ≤ c) :
    dualCornerOn f c ∈ dualBoxOn f c :=
  ⟨fun _ _ => rfl, fun _ => ⟨hc, le_refl c⟩⟩

end QuantumQueryComplexity
