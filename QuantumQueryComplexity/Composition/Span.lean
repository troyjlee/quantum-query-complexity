import QuantumQueryComplexity.Composition.Eigen
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Spanning by tensor eigenvectors (HLŠ Lemma 16, Item 3)

The family of tensor vectors `tensorVecE e g (v' · (c ·)) (ofLp (W c j))` — over
all eigen-index assignments `c : α → Y` and all members `j` of an orthonormal
basis `W c` of the outer space — spans the whole composed space.

Route: pure tensors of orthonormal families are orthonormal
(`tensor_orthonormalE`, via the `sum_prod_sliceE` interchange), hence linearly
independent; their cardinality equals the dimension, so they span; and each
pure tensor lies in the span of the family because `tensorVecE` is linear in
its outer argument and `W c` is a basis.

As in `Hat.lean` the block decomposition is abstract: everything is proved for
`e : Z ≃ (α → Y)` with `Y` an arbitrary finite type, and the cube statements are
the `cubeBlocks` instance.  The only cube-specific step was the dimension count
`Fintype.card ((α × β) → Bool) = Fintype.card (α → (β → Bool))`, which is now
just `Fintype.card_congr e.symm`.

This file is the second (and last) `WithLp`/`EuclideanSpace` quarantine zone.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix

/-- **S2**: transporting a spanning statement from `EuclideanSpace` to the
plain Pi module. -/
lemma span_top_of_toLp {n κ : Type*} [Fintype n] (T : κ → (n → ℝ))
    (h : Submodule.span ℝ (Set.range fun k =>
      (WithLp.toLp 2 (T k) : EuclideanSpace ℝ n)) = ⊤) :
    Submodule.span ℝ (Set.range T) = ⊤ := by
  have himg : Set.range T
      = ⇑(WithLp.linearEquiv 2 ℝ (n → ℝ)).toLinearMap ''
        Set.range (fun k => (WithLp.toLp 2 (T k) : EuclideanSpace ℝ n)) := by
    rw [← Set.range_comp]
    rfl
  rw [himg, Submodule.span_image, h, Submodule.map_top, LinearMap.range_eq_top]
  exact (WithLp.linearEquiv 2 ℝ (n → ℝ)).surjective

/-! ## Spanning over an abstract block decomposition -/

section General

variable {α Y Z : Type*} [Fintype α] [DecidableEq α]
variable [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

/-- **S1**: pure tensors of orthonormal families are orthonormal. -/
lemma tensor_orthonormalE (e : Z ≃ (α → Y)) {v' : α → Y → Y → ℝ}
    (hON : ∀ i, Orthonormal ℝ fun d =>
      (WithLp.toLp 2 (v' i d) : EuclideanSpace ℝ Y)) :
    Orthonormal ℝ fun c : α → Y =>
      (WithLp.toLp 2 (fun x => ∏ i, v' i (c i) (sliceE e x i)) :
        EuclideanSpace ℝ Z) := by
  rw [orthonormal_iff_ite]
  intro c c'
  rw [inner_toLp]
  have hstep : (fun x : Z => ∏ i, v' i (c i) (sliceE e x i)) ⬝ᵥ
      (fun x => ∏ i, v' i (c' i) (sliceE e x i))
      = ∏ i, (v' i (c i) ⬝ᵥ v' i (c' i)) := by
    calc (fun x : Z => ∏ i, v' i (c i) (sliceE e x i)) ⬝ᵥ
        (fun x => ∏ i, v' i (c' i) (sliceE e x i))
        = ∑ x : Z,
            (∏ i, v' i (c i) (sliceE e x i)) *
              ∏ i, v' i (c' i) (sliceE e x i) := rfl
      _ = ∑ x : Z,
            ∏ i, (v' i (c i) (sliceE e x i) * v' i (c' i) (sliceE e x i)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.prod_mul_distrib]
      _ = ∏ i, ∑ u, v' i (c i) u * v' i (c' i) u :=
          sum_prod_sliceE e fun i u => v' i (c i) u * v' i (c' i) u
      _ = ∏ i, (v' i (c i) ⬝ᵥ v' i (c' i)) := rfl
  rw [hstep]
  have hij : ∀ i, v' i (c i) ⬝ᵥ v' i (c' i) = if c i = c' i then 1 else 0 := by
    intro i
    have h := orthonormal_iff_ite.mp (hON i) (c i) (c' i)
    rwa [inner_toLp] at h
  rw [Finset.prod_congr rfl fun i _ => hij i]
  by_cases hcc : c = c'
  · rw [if_pos hcc, hcc]
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hcc
    rw [if_neg hcc, Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)]

/-- **S3**: the tensor eigenvector family spans everything. -/
lemma span_tensorVecE_top (e : Z ≃ (α → Y)) {g : α → Y → Bool}
    (v' : α → Y → Y → ℝ)
    (hON : ∀ i, Orthonormal ℝ fun d =>
      (WithLp.toLp 2 (v' i d) : EuclideanSpace ℝ Y))
    (W : (α → Y) → OrthonormalBasis (α → Bool) ℝ
      (EuclideanSpace ℝ (α → Bool))) :
    Submodule.span ℝ (Set.range fun p : (α → Y) × (α → Bool) =>
      tensorVecE e g (fun i => v' i (p.1 i)) (WithLp.ofLp (W p.1 p.2))) = ⊤ := by
  classical
  -- The eigen-index type `α → Y` can be empty when `Y` is; then so is `Z`, and
  -- the whole space is trivial.  (At a cube this branch never fires.)
  rcases isEmpty_or_nonempty (α → Y) with hE | hE
  · haveI : IsEmpty Z := Function.isEmpty e
    rw [eq_top_iff]
    intro v _
    rw [show v = 0 from funext fun z => isEmptyElim z]
    exact Submodule.zero_mem _
  rw [eq_top_iff]
  have hPT : Submodule.span ℝ (Set.range fun c : α → Y =>
      fun x : Z => ∏ i, v' i (c i) (sliceE e x i)) = ⊤ := by
    apply span_top_of_toLp
    refine LinearIndependent.span_eq_top_of_card_eq_finrank
      (tensor_orthonormalE e hON).linearIndependent ?_
    rw [finrank_euclideanSpace]
    exact Fintype.card_congr e.symm
  rw [← hPT]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨c, rfl⟩
  show (fun x : Z => ∏ i, v' i (c i) (sliceE e x i)) ∈ _
  let φ : ((α → Bool) → ℝ) →ₗ[ℝ] (Z → ℝ) :=
    { toFun := fun w => tensorVecE e g (fun i => v' i (c i)) w
      map_add' := fun a b => by
        funext x
        simp only [tensorVecE_apply, Pi.add_apply]
        ring
      map_smul' := fun m a => by
        funext x
        simp only [tensorVecE_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  have hWspan : Submodule.span ℝ
      (Set.range fun j => WithLp.ofLp (W c j)) = ⊤ := by
    apply span_top_of_toLp
    have heq : (fun j => (WithLp.toLp 2 (WithLp.ofLp (W c j)) :
        EuclideanSpace ℝ (α → Bool))) = fun j => W c j := rfl
    rw [heq]
    have hcoe : (fun j => W c j) = ⇑(W c).toBasis := by
      funext j
      rw [OrthonormalBasis.coe_toBasis]
    rw [hcoe]
    exact (W c).toBasis.span_eq
  have h1 : (fun _ : α → Bool => (1 : ℝ)) ∈
      Submodule.span ℝ (Set.range fun j => WithLp.ofLp (W c j)) := by
    rw [hWspan]
    exact Submodule.mem_top
  have h2 : φ (fun _ => 1) ∈
      Submodule.map φ (Submodule.span ℝ
        (Set.range fun j => WithLp.ofLp (W c j))) :=
    Submodule.mem_map_of_mem h1
  rw [← Submodule.span_image] at h2
  have hPTeq : (fun x : Z => ∏ i, v' i (c i) (sliceE e x i))
      = φ (fun _ => 1) := by
    funext x
    show _ = tensorVecE e g (fun i => v' i (c i)) (fun _ => 1) x
    simp [tensorVecE_apply]
  rw [hPTeq]
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  exact ⟨(c, j), rfl⟩

end General

/-! ## The cube instance -/

section Cube

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- **S1**, cube form. -/
lemma tensor_orthonormal {v' : α → (β → Bool) → (β → Bool) → ℝ}
    (hON : ∀ i, Orthonormal ℝ fun d =>
      (WithLp.toLp 2 (v' i d) : EuclideanSpace ℝ (β → Bool))) :
    Orthonormal ℝ fun c : α → (β → Bool) =>
      (WithLp.toLp 2 (fun x => ∏ i, v' i (c i) (slice x i)) :
        EuclideanSpace ℝ ((α × β) → Bool)) :=
  tensor_orthonormalE (cubeBlocks α β) hON

/-- **S3**, cube form. -/
lemma span_tensorVec_top {g : α → (β → Bool) → Bool}
    (v' : α → (β → Bool) → (β → Bool) → ℝ)
    (hON : ∀ i, Orthonormal ℝ fun d =>
      (WithLp.toLp 2 (v' i d) : EuclideanSpace ℝ (β → Bool)))
    (W : (α → (β → Bool)) → OrthonormalBasis (α → Bool) ℝ
      (EuclideanSpace ℝ (α → Bool))) :
    Submodule.span ℝ (Set.range fun p : (α → (β → Bool)) × (α → Bool) =>
      tensorVec g (fun i => v' i (p.1 i)) (WithLp.ofLp (W p.1 p.2))) = ⊤ :=
  span_tensorVecE_top (cubeBlocks α β) v' hON W

end Cube

end QuantumQueryComplexity
