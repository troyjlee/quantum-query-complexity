import QuantumQueryComplexity.Quantum.FiniteHilbert
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Orthogonal projectors and reflections, as raw matrices

**A spike, to fix the representation before the witness construction.**

The upper bound reflects about the span of a finite family of vectors coming
from a `DualPair`.  Rather than build projectors by hand, construct the subspace
in `EuclideanSpace ℂ H`, take Mathlib's `Submodule.starProjection`, and carry it
back to a raw `Matrix H H ℂ`.

The transport is `Matrix.toEuclideanCLM`, which is a **star-algebra
equivalence** — not merely a linear one.  That single fact is what makes this
representation the right one: idempotence and self-adjointness of the projector
come from `map_mul` and `map_star`, with no matrix computation at all, and
`IsQProjector` (hence `qRefl`, already proved unitary and involutive) follows
immediately.

## What the spike establishes

* `subProj_mulVec` — the raw action: `subProj K *ᵥ ψ` is `K.starProjection`
  applied to `ψ`, read back through `WithLp`.
* `subProj_mulVec_of_mem` / `subProj_mulVec_of_mem_orthogonal` — the **fixed
  space** and the **killed space**, the two characterizations a reflection
  argument actually uses.
* `isQProjector_subProj`, and hence `subRefl` with `subRefl_mul_self`,
  `subRefl_mem_unitaryGroup`, `subRefl_mulVec_of_mem` (`+ψ`) and
  `subRefl_mulVec_of_mem_orthogonal` (`-ψ`).
* `spanProj` / `spanRefl` — the finite-span case, which is the one the witness
  construction needs.

The membership side conditions are stated in `EuclideanSpace` (`WithLp.toLp 2 ψ ∈ K`)
rather than raw, deliberately: that is where the span of a family of vectors is
easy to reason about, and `WithLp.toLp` is an equivalence, so nothing is lost.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H : Type} [Fintype H] [DecidableEq H]

/-! ## The projector -/

/-- The orthogonal projector onto `K`, as a raw matrix. -/
noncomputable def subProj (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] : Matrix H H ℂ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := H)).symm K.starProjection

lemma toEuclideanCLM_subProj (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (subProj K) = K.starProjection :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := H)).apply_symm_apply _

/-- **The raw action of the projector.** -/
theorem subProj_mulVec (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] (ψ : H → ℂ) :
    (WithLp.toLp 2 (subProj K *ᵥ ψ) : EuclideanSpace ℂ H)
      = K.starProjection (WithLp.toLp 2 ψ) := by
  rw [← Matrix.toEuclideanCLM_toLp, toEuclideanCLM_subProj]

/-- **It is an orthogonal projector.**  Both halves come from
`Matrix.toEuclideanCLM` being a star-algebra equivalence. -/
theorem isQProjector_subProj (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] : IsQProjector (subProj K) := by
  constructor
  · have h : star (subProj K) = subProj K := by
      rw [subProj, ← map_star]
      congr 1
      exact isSelfAdjoint_starProjection K
    rwa [Matrix.star_eq_conjTranspose] at h
  · rw [subProj, ← map_mul]
    congr 1
    exact K.isIdempotentElem_starProjection

/-- **The fixed space.** -/
theorem subProj_mulVec_of_mem (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] {ψ : H → ℂ}
    (h : (WithLp.toLp 2 ψ : EuclideanSpace ℂ H) ∈ K) : subProj K *ᵥ ψ = ψ := by
  have h1 := subProj_mulVec K ψ
  rw [Submodule.starProjection_eq_self_iff.mpr h] at h1
  exact WithLp.toLp_injective 2 h1

/-- **The fixed space, as an iff.**  What a witness construction has to hit:
being fixed by the projector *is* membership. -/
theorem subProj_mulVec_eq_self_iff (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] (ψ : H → ℂ) :
    subProj K *ᵥ ψ = ψ ↔ (WithLp.toLp 2 ψ : EuclideanSpace ℂ H) ∈ K := by
  constructor
  · intro h
    have h1 := subProj_mulVec K ψ
    rw [h] at h1
    exact Submodule.starProjection_eq_self_iff.mp h1.symm
  · exact subProj_mulVec_of_mem K

/-- **The killed space.** -/
theorem subProj_mulVec_of_mem_orthogonal (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] {ψ : H → ℂ}
    (h : (WithLp.toLp 2 ψ : EuclideanSpace ℂ H) ∈ Kᗮ) : subProj K *ᵥ ψ = 0 := by
  have h1 := subProj_mulVec K ψ
  rw [(Submodule.starProjection_apply_eq_zero_iff K).mpr h] at h1
  have h2 : (WithLp.toLp 2 (subProj K *ᵥ ψ) : EuclideanSpace ℂ H)
      = WithLp.toLp 2 (0 : H → ℂ) := by
    rw [h1]
    rfl
  exact WithLp.toLp_injective 2 h2

/-! ## The reflection -/

/-- The reflection about `K`. -/
noncomputable def subRefl (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] : Matrix H H ℂ := qRefl (subProj K)

theorem subRefl_mem_unitaryGroup (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] :
    subRefl K ∈ Matrix.unitaryGroup H ℂ :=
  qRefl_mem_unitaryGroup (isQProjector_subProj K)

theorem subRefl_mul_self (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] : subRefl K * subRefl K = 1 :=
  qRefl_mul_self (isQProjector_subProj K)

lemma subRefl_mulVec (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] (ψ : H → ℂ) :
    subRefl K *ᵥ ψ = (2 : ℂ) • (subProj K *ᵥ ψ) - ψ := by
  rw [subRefl, qRefl, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- **The reflection fixes `K`.** -/
theorem subRefl_mulVec_of_mem (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] {ψ : H → ℂ}
    (h : (WithLp.toLp 2 ψ : EuclideanSpace ℂ H) ∈ K) : subRefl K *ᵥ ψ = ψ := by
  rw [subRefl_mulVec, subProj_mulVec_of_mem K h]
  module

/-- **The reflection negates `Kᗮ`.** -/
theorem subRefl_mulVec_of_mem_orthogonal (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] {ψ : H → ℂ}
    (h : (WithLp.toLp 2 ψ : EuclideanSpace ℂ H) ∈ Kᗮ) : subRefl K *ᵥ ψ = -ψ := by
  rw [subRefl_mulVec, subProj_mulVec_of_mem_orthogonal K h]
  module

/-! ## The orthogonal complement

**The sign matters.**  The plan's `Λ` is the projector onto `span{ψₓ}ᗮ`, and its
reflection is *minus* the reflection about the span.  A global sign shifts every
eigenphase by `π`, so it cannot be dropped when the operator is fed to
controlled phase detection. -/

/-- **The projector onto the orthogonal complement.** -/
theorem subProj_orthogonal (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] : subProj Kᗮ = 1 - subProj K := by
  rw [subProj, subProj, Submodule.starProjection_orthogonal', map_sub, map_one]

/-- **The reflection about the complement is minus the reflection about the
subspace.**  This is the sign that must not be dropped. -/
theorem subRefl_orthogonal (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] : subRefl Kᗮ = - subRefl K := by
  rw [subRefl, subRefl, qRefl, qRefl, subProj_orthogonal]
  module

/-! ## Finite spans

The case the witness construction needs: reflect about the span of a finite
family of raw vectors. -/

/-- The subspace spanned by a finite family of raw vectors. -/
noncomputable def rawSpan {ι' : Type} (v : ι' → (H → ℂ)) :
    Submodule ℂ (EuclideanSpace ℂ H) :=
  Submodule.span ℂ (Set.range fun i => (WithLp.toLp 2 (v i) : EuclideanSpace ℂ H))

/-- **Orthogonality to a span is orthogonality to its generators.**  This is the
form a witness construction can actually verify: one inner product per
generator, no spans. -/
theorem mem_rawSpan_orthogonal_iff {ι' : Type} (v : ι' → (H → ℂ)) (ψ : H → ℂ) :
    (WithLp.toLp 2 ψ : EuclideanSpace ℂ H) ∈ (rawSpan v)ᗮ ↔ ∀ i, qInner (v i) ψ = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h i
    rw [qInner_eq_euclidean]
    exact h _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro h u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        rw [← qInner_eq_euclidean]
        exact h i
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]

/-- The projector onto the span of a finite family. -/
noncomputable def spanProj {ι' : Type} (v : ι' → (H → ℂ)) : Matrix H H ℂ :=
  subProj (rawSpan v)

/-- The reflection about the span of a finite family. -/
noncomputable def spanRefl {ι' : Type} (v : ι' → (H → ℂ)) : Matrix H H ℂ :=
  subRefl (rawSpan v)

theorem isQProjector_spanProj {ι' : Type} (v : ι' → (H → ℂ)) :
    IsQProjector (spanProj v) := isQProjector_subProj _

theorem spanRefl_mem_unitaryGroup {ι' : Type} (v : ι' → (H → ℂ)) :
    spanRefl v ∈ Matrix.unitaryGroup H ℂ := subRefl_mem_unitaryGroup _

theorem spanRefl_mul_self {ι' : Type} (v : ι' → (H → ℂ)) :
    spanRefl v * spanRefl v = 1 := subRefl_mul_self _

/-- The projector onto the complement of a span. -/
theorem spanProj_orthogonal {ι' : Type} (v : ι' → (H → ℂ)) :
    subProj (rawSpan v)ᗮ = 1 - spanProj v := subProj_orthogonal _

/-- **The reflection about the complement of a span**, with its sign. -/
theorem spanRefl_orthogonal {ι' : Type} (v : ι' → (H → ℂ)) :
    subRefl (rawSpan v)ᗮ = - spanRefl v := subRefl_orthogonal _

/-- Each spanning vector is fixed by the projector. -/
theorem spanProj_mulVec_self {ι' : Type} (v : ι' → (H → ℂ)) (i : ι') :
    spanProj v *ᵥ v i = v i :=
  subProj_mulVec_of_mem _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Each spanning vector is fixed by the reflection. -/
theorem spanRefl_mulVec_self {ι' : Type} (v : ι' → (H → ℂ)) (i : ι') :
    spanRefl v *ᵥ v i = v i :=
  subRefl_mulVec_of_mem _ (Submodule.subset_span ⟨i, rfl⟩)

end QuantumQueryComplexity
