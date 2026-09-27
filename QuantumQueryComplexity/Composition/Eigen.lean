import QuantumQueryComplexity.Composition.Compose
import QuantumQueryComplexity.Composition.SchurPSD
set_option linter.style.header false

/-!
# The eigen-computation for composed matrices (HLŠ Lemma 16, Items 1–2)

The crux of the composition theorem: for eigenvectors `v i` of the inner
matrices `M i` (eigenvalues `lamv i`) and an eigenvector `w` of the outer
auxiliary matrix `Γf ⊙ Emat (‖M ·‖) lamv` (eigenvalue `μ`), the tensor
vector

  `tensorVec g v w x = w (tilde g x) * ∏ i, v i (slice x i)`

is an eigenvector of `compose g Γf M` with eigenvalue `μ`
(`compose_mulVec_tensorVec`).

The two supporting identities:
* `hat_guarded_row_sum` (K1) — the per-block action, replacing HLŠ Eq. (3)
  and all restriction-vector bookkeeping by a scalar computation;
* `sum_prod_slice` (K2) — the sum/product interchange along
  `(α × β) → Bool ≃ α → β → Bool`.

As in `Hat.lean` everything is proved over an **abstract** block decomposition
`e : Z ≃ (α → Y)`; the cube statements are the `cubeBlocks` instance.
This includes promise problems whose inner inputs form a subtype. Nothing in the
spectral argument sees the difference: K1 uses only that the colouring is
`Bool`-valued, and K2 is `Fintype.prod_sum` transported along `e`.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-! ## An adversary matrix for a colouring of an arbitrary type

`IsAdvMatrix` is tied to a cube of inputs.  The inner inputs of a composition
range over an arbitrary finite type, so the same notion is
needed there; at a cube the two are definitionally equal. -/

/-- A symmetric matrix supported on pairs of differently-coloured points. -/
def IsAdvCol {Y : Type*} (g : Y → Bool) (N : Matrix Y Y ℝ) : Prop :=
  N.IsHermitian ∧ ∀ u v, g u = g v → N u v = 0

namespace IsAdvCol
variable {Y : Type*} {g : Y → Bool} {N : Matrix Y Y ℝ}

lemma isHermitian (h : IsAdvCol g N) : N.IsHermitian := h.1

lemma apply_eq_zero (h : IsAdvCol g N) {u v : Y} (huv : g u = g v) : N u v = 0 :=
  h.2 u v huv

end IsAdvCol

/-- The bipartite-support lemma for a colouring of an arbitrary type: an
eigenvector with nonzero eigenvalue of an adversary matrix for `g` has support
in every colour class of `g`.  (`Bipartite.lean` proves this over an arbitrary
index type already; only the `IsAdvMatrix` wrapper was cube-tied.) -/
theorem IsAdvCol.exists_eigenvector_support {Y : Type*} [Fintype Y]
    {g : Y → Bool} {N : Matrix Y Y ℝ} (hN : IsAdvCol g N)
    {v : Y → ℝ} {θ : ℝ} (hv : N *ᵥ v = θ • v) (hθ : θ ≠ 0) (hv0 : v ≠ 0)
    (a : Bool) : ∃ u, g u = a ∧ v u ≠ 0 := by
  have h := brestrict_ne_zero (fun u w' huw => hN.2 u w' huw) hv hθ hv0 a
  obtain ⟨u, hu⟩ := Function.ne_iff.mp h
  simp only [brestrict_apply, Pi.zero_apply] at hu
  by_cases hgu : g u = a
  · rw [if_pos hgu] at hu
    exact ⟨u, hgu, hu⟩
  · rw [if_neg hgu] at hu
    exact absurd rfl hu

lemma IsAdvMatrix.isAdvCol {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq σ] {f : (ι → σ) → Bool} {Γ : Matrix (ι → σ) (ι → σ) ℝ}
    (h : IsAdvMatrix f Γ) : IsAdvCol f Γ := h

/-! ## The spectral core over an abstract block decomposition -/

section General

variable {α Y Z : Type*} [Fintype α] [DecidableEq α]
variable [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
variable (e : Z ≃ (α → Y))

/-- **K1**: the guarded row sum of `hat N` against an eigenvector. -/
lemma hat_guarded_row_sumGen {g : (Y) → Bool}
    {N : Matrix (Y) (Y) ℝ} (hN : IsAdvCol g N)
    {v : (Y) → ℝ} {θ : ℝ} (hv : N *ᵥ v = θ • v) (u₀ : Y)
    (b : Bool) :
    ∑ u, (if g u = b then hat N u₀ u * v u else 0)
      = (if g u₀ = b then ‖N‖ else θ) * v u₀ := by
  have hsplit : ∀ u, (if g u = b then hat N u₀ u * v u else 0)
      = (if g u = b then N u₀ u * v u else 0)
      + (if g u = b then ‖N‖ * (if u₀ = u then 1 else 0) * v u else 0) := by
    intro u
    by_cases h : g u = b
    · rw [if_pos h, if_pos h, if_pos h, hat_apply]
      ring
    · rw [if_neg h, if_neg h, if_neg h, add_zero]
  rw [Finset.sum_congr rfl fun u _ => hsplit u, Finset.sum_add_distrib]
  have hid : ∑ u, (if g u = b then ‖N‖ * (if u₀ = u then 1 else 0) * v u else 0)
      = (if g u₀ = b then ‖N‖ else 0) * v u₀ := by
    rw [Finset.sum_eq_single u₀]
    · by_cases h : g u₀ = b <;> simp [h]
    · intro u _ hu
      have hne : u₀ ≠ u := fun hh => hu hh.symm
      by_cases h : g u = b
      · rw [if_pos h, if_neg hne, mul_zero, zero_mul]
      · rw [if_neg h]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hNpart : ∑ u, (if g u = b then N u₀ u * v u else 0)
      = (if g u₀ = b then 0 else θ * v u₀) := by
    by_cases h0 : g u₀ = b
    · rw [if_pos h0]
      refine Finset.sum_eq_zero fun u _ => ?_
      by_cases h : g u = b
      · rw [if_pos h, hN.apply_eq_zero (h0.trans h.symm), zero_mul]
      · rw [if_neg h]
    · rw [if_neg h0]
      have hall : ∀ u, (if g u = b then N u₀ u * v u else 0) = N u₀ u * v u := by
        intro u
        by_cases h : g u = b
        · rw [if_pos h]
        · rw [if_neg h]
          have hgg : g u = g u₀ := by
            cases hgu : g u <;> cases hgu0 : g u₀ <;> cases b <;> simp_all
          rw [hN.apply_eq_zero hgg.symm, zero_mul]
      rw [Finset.sum_congr rfl fun u _ => hall u]
      have hcf := congrFun hv u₀
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hcf
      exact hcf
  rw [hid, hNpart]
  by_cases h : g u₀ = b <;> simp [h]

/-- **K2**: the sum/product interchange along slices. -/
lemma sum_prod_sliceE (F : α → (Y) → ℝ) :
    ∑ y : Z, ∏ i, F i (sliceE e y i)
      = ∏ i, ∑ u : Y, F i u := by
  rw [Fintype.prod_sum]
  exact Fintype.sum_equiv e
    (fun y => ∏ i, F i (sliceE e y i)) (fun p => ∏ i, F i (p i)) fun y => rfl

/-- The tensor eigenvector of the composed matrix. -/
noncomputable def tensorVecE (g : α → (Y) → Bool)
    (v : α → (Y) → ℝ) (w : (α → Bool) → ℝ) :
    (Z) → ℝ :=
  fun x => w (tildeE e g x) * ∏ i, v i (sliceE e x i)

@[simp] lemma tensorVecE_apply (g : α → Y → Bool) (v : α → Y → ℝ)
    (w : (α → Bool) → ℝ) (z : Z) :
    tensorVecE e g v w z = w (tildeE e g z) * ∏ i, v i (sliceE e z i) := rfl

/-- **K3', the crux in general form**: applying the composed matrix to a
tensor vector amounts to applying the outer auxiliary matrix `Γf ⊙ Emat` to
the outer factor.  (HLŠ Lemma 16, Items 1–2, for an arbitrary outer
vector.) -/
theorem composeE_mulVec_tensorVec' {g : α → (Y) → Bool}
    {Γf : Matrix (α → Bool) (α → Bool) ℝ}
    {M : α → Matrix (Y) (Y) ℝ}
    (hM : ∀ i, IsAdvCol (g i) (M i))
    {v : α → (Y) → ℝ} {lamv : α → ℝ}
    (hv : ∀ i, M i *ᵥ v i = lamv i • v i)
    (w : (α → Bool) → ℝ) :
    composeE e g Γf M *ᵥ tensorVecE e g v w
      = tensorVecE e g v ((Γf ⊙ Emat (fun i => ‖M i‖) lamv) *ᵥ w) := by
  funext x
  calc (composeE e g Γf M *ᵥ tensorVecE e g v w) x
      = ∑ y, composeE e g Γf M x y * tensorVecE e g v w y := rfl
    _ = ∑ y, (∑ b, Γf (tildeE e g x) b *
          ∏ i, (if g i (sliceE e y i) = b i
            then hat (M i) (sliceE e x i) (sliceE e y i) else 0))
          * tensorVecE e g v w y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [composeE_apply_sum]
    _ = ∑ y, ∑ b, Γf (tildeE e g x) b * w b *
          ∏ i, ((if g i (sliceE e y i) = b i
            then hat (M i) (sliceE e x i) (sliceE e y i) else 0) * v i (sliceE e y i)) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hby : tildeE e g y = b
        · subst hby
          simp only [tensorVecE]
          rw [Finset.prod_mul_distrib]
          ring
        · obtain ⟨i, hi⟩ := Function.ne_iff.mp hby
          have hzero : (if g i (sliceE e y i) = b i
              then hat (M i) (sliceE e x i) (sliceE e y i) else 0) = 0 := if_neg hi
          have hzero2 : (if g i (sliceE e y i) = b i
              then hat (M i) (sliceE e x i) (sliceE e y i) else 0) * v i (sliceE e y i)
              = 0 := by
            rw [hzero, zero_mul]
          rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero,
            Finset.prod_eq_zero (Finset.mem_univ i) hzero2]
          ring
    _ = ∑ b, Γf (tildeE e g x) b * w b *
          ∏ i, ∑ u, (if g i u = b i
            then hat (M i) (sliceE e x i) u * v i u else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        have hfact : ∀ (y : Z) (i : α),
            (if g i (sliceE e y i) = b i
              then hat (M i) (sliceE e x i) (sliceE e y i) else 0) * v i (sliceE e y i)
            = (if g i (sliceE e y i) = b i
              then hat (M i) (sliceE e x i) (sliceE e y i) * v i (sliceE e y i) else 0) := by
          intro y i
          by_cases h : g i (sliceE e y i) = b i
          · rw [if_pos h, if_pos h]
          · rw [if_neg h, if_neg h, zero_mul]
        rw [Finset.sum_congr rfl fun y _ => Finset.prod_congr rfl fun i _ => hfact y i]
        exact sum_prod_sliceE e fun i u =>
          if g i u = b i then hat (M i) (sliceE e x i) u * v i u else 0
    _ = ∑ b, Γf (tildeE e g x) b * w b *
          ∏ i, ((if tildeE e g x i = b i then ‖M i‖ else lamv i) * v i (sliceE e x i)) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        congr 1
        exact Finset.prod_congr rfl fun i _ =>
          hat_guarded_row_sumGen (hM i) (hv i) (sliceE e x i) (b i)
    _ = (∏ i, v i (sliceE e x i)) *
          ∑ b, (Γf (tildeE e g x) b * Emat (fun i => ‖M i‖) lamv (tildeE e g x) b) * w b := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.prod_mul_distrib, Emat_apply]
        ring
    _ = (∏ i, v i (sliceE e x i)) *
          ((Γf ⊙ Emat (fun i => ‖M i‖) lamv) *ᵥ w) (tildeE e g x) := by
        rfl
    _ = tensorVecE e g v ((Γf ⊙ Emat (fun i => ‖M i‖) lamv) *ᵥ w) x := by
        simp only [tensorVecE]
        ring

/-- **K3**: tensor vectors built from inner eigenvectors and an eigenvector
of the outer auxiliary matrix are eigenvectors of the composed matrix, with
the outer eigenvalue. -/
theorem composeE_mulVec_tensorVec {g : α → (Y) → Bool}
    {Γf : Matrix (α → Bool) (α → Bool) ℝ}
    {M : α → Matrix (Y) (Y) ℝ}
    (hM : ∀ i, IsAdvCol (g i) (M i))
    {v : α → (Y) → ℝ} {lamv : α → ℝ}
    (hv : ∀ i, M i *ᵥ v i = lamv i • v i)
    {w : (α → Bool) → ℝ} {μ : ℝ}
    (hw : (Γf ⊙ Emat (fun i => ‖M i‖) lamv) *ᵥ w = μ • w) :
    composeE e g Γf M *ᵥ tensorVecE e g v w = μ • tensorVecE e g v w := by
  rw [composeE_mulVec_tensorVec' e hM hv, hw]
  funext x
  simp only [tensorVecE, Pi.smul_apply, smul_eq_mul]
  ring


end General

/-! ## The cube instance -/

section Cube
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

lemma hat_guarded_row_sum {g : (β → Bool) → Bool}
    {N : Matrix (β → Bool) (β → Bool) ℝ} (hN : IsAdvMatrix g N)
    {v : (β → Bool) → ℝ} {θ : ℝ} (hv : N *ᵥ v = θ • v) (u₀ : β → Bool)
    (b : Bool) :
    ∑ u, (if g u = b then hat N u₀ u * v u else 0)
      = (if g u₀ = b then ‖N‖ else θ) * v u₀ :=
  hat_guarded_row_sumGen hN.isAdvCol hv u₀ b

lemma sum_prod_slice (F : α → (β → Bool) → ℝ) :
    ∑ y : (α × β) → Bool, ∏ i, F i (slice y i)
      = ∏ i, ∑ u : β → Bool, F i u :=
  sum_prod_sliceE (cubeBlocks α β) F

/-- The tensor eigenvector of the composed matrix. -/
noncomputable def tensorVec (g : α → (β → Bool) → Bool)
    (v : α → (β → Bool) → ℝ) (w : (α → Bool) → ℝ) :
    ((α × β) → Bool) → ℝ :=
  tensorVecE (cubeBlocks α β) g v w

@[simp] lemma tensorVec_apply (g : α → (β → Bool) → Bool)
    (v : α → (β → Bool) → ℝ) (w : (α → Bool) → ℝ) (x : (α × β) → Bool) :
    tensorVec g v w x = w (tilde g x) * ∏ i, v i (slice x i) := rfl

theorem compose_mulVec_tensorVec' {g : α → (β → Bool) → Bool}
    {Γf : Matrix (α → Bool) (α → Bool) ℝ}
    {M : α → Matrix (β → Bool) (β → Bool) ℝ}
    (hM : ∀ i, IsAdvMatrix (g i) (M i))
    {v : α → (β → Bool) → ℝ} {lamv : α → ℝ}
    (hv : ∀ i, M i *ᵥ v i = lamv i • v i) (w : (α → Bool) → ℝ) :
    compose g Γf M *ᵥ tensorVec g v w
      = tensorVec g v ((Γf ⊙ Emat (fun i => ‖M i‖) lamv) *ᵥ w) :=
  composeE_mulVec_tensorVec' (cubeBlocks α β) (fun i => (hM i).isAdvCol) hv w

theorem compose_mulVec_tensorVec {g : α → (β → Bool) → Bool}
    {Γf : Matrix (α → Bool) (α → Bool) ℝ}
    {M : α → Matrix (β → Bool) (β → Bool) ℝ}
    (hM : ∀ i, IsAdvMatrix (g i) (M i))
    {v : α → (β → Bool) → ℝ} {lamv : α → ℝ}
    (hv : ∀ i, M i *ᵥ v i = lamv i • v i)
    {w : (α → Bool) → ℝ} {μ : ℝ}
    (hw : (Γf ⊙ Emat (fun i => ‖M i‖) lamv) *ᵥ w = μ • w) :
    compose g Γf M *ᵥ tensorVec g v w = μ • tensorVec g v w :=
  composeE_mulVec_tensorVec (cubeBlocks α β) (fun i => (hM i).isAdvCol) hv hw

end Cube

end QuantumQueryComplexity
