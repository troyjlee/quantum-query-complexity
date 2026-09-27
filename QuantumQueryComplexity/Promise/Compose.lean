import QuantumQueryComplexity.Composition.Mask
import QuantumQueryComplexity.Promise.Transport
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Composition lower bounds for promise problems

**Main result** (`advPMOn_mul_le_advPMOn_compose`): for an outer promise
`f : X → O` observed by an injective `outerRead : X → α → Bool` and an inner
promise `g : Y → Bool` observed by an injective `innerRead : Y → β → σ`,

  `ADV±(f) * ADV±(g) ≤ ADV±(f ∘ gᵅ)`

on the composite promise domain `ComposeDom` of block tuples whose vector of
inner outputs is a legal outer input.

The proof is the total argument of `Composition/Main.lean` run over the
generalized block decomposition of `Composition/{Hat,Eigen,Span,NormCompose,
Mask}.lean`, with two promise-specific steps:

* the outer witness is zero-extended along `outerRead` to the full cube
  `α → Bool` (`Promise/Transport.lean`), which preserves its norm and its
  masked norms;
* the composed matrix is built on *all* block tuples `α → Y` and then
  restricted to `ComposeDom`.  Rows outside the promise vanish, because the
  zero-extended outer matrix does, so `norm_submatrix_of_support` says the
  restriction changes neither the norm nor any masked norm.

Only the composition lower bound is asserted here.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-! ## Restricting a matrix to its support -/

section Restrict

variable {S Z : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z]

lemma submatrix_hadamard (A B : Matrix Z Z ℝ) (inc : S → Z) :
    (A ⊙ B).submatrix inc inc
      = A.submatrix inc inc ⊙ B.submatrix inc inc := rfl

/-- A matrix supported on the image of an injection has the norm of its
restriction to that image. -/
theorem norm_submatrix_of_support {inc : S → Z} (hinj : Function.Injective inc)
    {Γ : Matrix Z Z ℝ}
    (hsupp : ∀ a b : Z, ((∀ s, inc s ≠ a) ∨ (∀ s, inc s ≠ b)) → Γ a b = 0) :
    ‖Γ.submatrix inc inc‖ = ‖Γ‖ := by
  have hz : zextMat inc (Γ.submatrix inc inc) = Γ := by
    ext a b
    by_cases ha : ∃ s, inc s = a
    · obtain ⟨s, rfl⟩ := ha
      by_cases hb : ∃ t, inc t = b
      · obtain ⟨t, rfl⟩ := hb
        rw [zextMat_apply_encode hinj]
        rfl
      · push_neg at hb
        rw [zextMat_apply_of_not_mem_range _ _ (Or.inr hb)]
        exact (hsupp _ _ (Or.inr hb)).symm
    · push_neg at ha
      rw [zextMat_apply_of_not_mem_range _ _ (Or.inl ha)]
      exact (hsupp _ _ (Or.inl ha)).symm
  calc ‖Γ.submatrix inc inc‖ = ‖zextMat inc (Γ.submatrix inc inc)‖ :=
      (norm_zextMat hinj _).symm
    _ = ‖Γ‖ := by rw [hz]

end Restrict

/-! ## The composite promise domain -/

section Compose

variable {α β σ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [DecidableEq σ]
variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
variable {O : Type*}

/-- The composite promise domain — block tuples whose vector
of inner outputs is a legal outer input. -/
abbrev ComposeDom (outerRead : X → α → Bool) (g : Y → Bool) : Type _ :=
  {ys : α → Y // ∃ x, outerRead x = fun i => g (ys i)}

/-- The composite observation map: query `(p, q)` reads coordinate `q` of
block `p`. -/
def composeReadOn (outerRead : X → α → Bool) (g : Y → Bool)
    (innerRead : Y → β → σ) : ComposeDom outerRead g → (α × β) → σ :=
  fun ys pq => innerRead (ys.1 pq.1) pq.2

/-- The composite output.  Well defined because `outerRead` is injective
(`composeOutOn_eq`). -/
noncomputable def composeOutOn (outerRead : X → α → Bool) (g : Y → Bool)
    (f : X → O) : ComposeDom outerRead g → O :=
  fun ys => f ys.2.choose

lemma composeOutOn_eq {outerRead : X → α → Bool} {g : Y → Bool}
    (hOuter : Function.Injective outerRead) (f : X → O)
    (ys : ComposeDom outerRead g) {x : X}
    (hx : outerRead x = fun i => g (ys.1 i)) :
    composeOutOn outerRead g f ys = f x := by
  have h := ys.2.choose_spec
  change f ys.2.choose = f x
  rw [hOuter (h.trans hx.symm)]

lemma composeReadOn_injective {outerRead : X → α → Bool} {g : Y → Bool}
    {innerRead : Y → β → σ} (hInner : Function.Injective innerRead) :
    Function.Injective (composeReadOn outerRead g innerRead) := fun _ _ hab =>
  Subtype.ext (funext fun p => hInner (funext fun q => congrFun hab (p, q)))

/-! ## The composed witness

The block decomposition is the identity on `α → Y`; these two `rfl`s record
that `sliceE`/`tildeE` really do reduce to coordinate access there. -/

lemma sliceE_refl (z : α → Y) (i : α) :
    sliceE (Equiv.refl (α → Y)) z i = z i := rfl

lemma tildeE_refl (g : Y → Bool) (z : α → Y) :
    tildeE (Equiv.refl (α → Y)) (fun _ : α => g) z = fun i => g (z i) := rfl

/-- The composed matrix on all block tuples, before restricting to the
promise. -/
noncomputable def composeGammaFull (outerRead : X → α → Bool) (g : Y → Bool)
    (Γf : Matrix X X ℝ) (Γg : Matrix Y Y ℝ) : Matrix (α → Y) (α → Y) ℝ :=
  composeE (Equiv.refl (α → Y)) (fun _ : α => g) (zextMat outerRead Γf)
    (fun _ : α => Γg)

/-- The composed witness on the composite promise domain. -/
noncomputable def composeGammaOn (outerRead : X → α → Bool) (g : Y → Bool)
    (Γf : Matrix X X ℝ) (Γg : Matrix Y Y ℝ) :
    Matrix (ComposeDom outerRead g) (ComposeDom outerRead g) ℝ :=
  (composeGammaFull outerRead g Γf Γg).submatrix Subtype.val Subtype.val

/-- Rows and columns of the composed matrix outside the promise vanish. -/
lemma composeGammaFull_apply_eq_zero {outerRead : X → α → Bool} {g : Y → Bool}
    (Γf : Matrix X X ℝ) (Γg : Matrix Y Y ℝ) {a b : α → Y}
    (h : (∀ s : ComposeDom outerRead g, (s : α → Y) ≠ a) ∨
      (∀ s : ComposeDom outerRead g, (s : α → Y) ≠ b)) :
    composeGammaFull outerRead g Γf Γg a b = 0 := by
  change composeE (Equiv.refl (α → Y)) (fun _ : α => g) (zextMat outerRead Γf)
    (fun _ : α => Γg) a b = 0
  rw [composeE_apply, tildeE_refl, tildeE_refl]
  have hz : zextMat outerRead Γf (fun i => g (a i)) (fun i => g (b i)) = 0 := by
    refine zextMat_apply_of_not_mem_range outerRead Γf ?_
    rcases h with h | h
    · exact Or.inl fun x hx => h ⟨a, ⟨x, hx⟩⟩ rfl
    · exact Or.inr fun x hx => h ⟨b, ⟨x, hx⟩⟩ rfl
  rw [hz, zero_mul]

lemma norm_composeGammaOn {outerRead : X → α → Bool} {g : Y → Bool}
    (Γf : Matrix X X ℝ) (Γg : Matrix Y Y ℝ) :
    ‖composeGammaOn outerRead g Γf Γg‖ = ‖composeGammaFull outerRead g Γf Γg‖ := by
  change ‖(composeGammaFull outerRead g Γf Γg).submatrix Subtype.val Subtype.val‖
    = ‖composeGammaFull outerRead g Γf Γg‖
  exact norm_submatrix_of_support Subtype.val_injective fun _ _ h =>
    composeGammaFull_apply_eq_zero Γf Γg h

lemma norm_composeGammaOn_hadamard {outerRead : X → α → Bool} {g : Y → Bool}
    {innerRead : Y → β → σ} (Γf : Matrix X X ℝ) (Γg : Matrix Y Y ℝ)
    (pq : α × β) :
    ‖composeGammaOn outerRead g Γf Γg
        ⊙ advDOn (composeReadOn outerRead g innerRead) pq‖
      = ‖composeGammaFull outerRead g Γf Γg
          ⊙ advDOn (composeReadE (Equiv.refl (α → Y)) innerRead) pq‖ := by
  have heq : composeGammaOn outerRead g Γf Γg
      ⊙ advDOn (composeReadOn outerRead g innerRead) pq
      = (composeGammaFull outerRead g Γf Γg
          ⊙ advDOn (composeReadE (Equiv.refl (α → Y)) innerRead) pq).submatrix
        Subtype.val Subtype.val := rfl
  rw [heq]
  exact norm_submatrix_of_support Subtype.val_injective fun a b h => by
    rw [Matrix.hadamard_apply, composeGammaFull_apply_eq_zero Γf Γg h, zero_mul]

lemma composeGammaOn_isAdvMatrixOn {outerRead : X → α → Bool} {g : Y → Bool}
    {f : X → O} {Γf : Matrix X X ℝ} {Γg : Matrix Y Y ℝ}
    (hOuter : Function.Injective outerRead) (hf1 : IsAdvMatrixOn f Γf)
    (hg1 : IsAdvMatrixOn g Γg) :
    IsAdvMatrixOn (composeOutOn outerRead g f) (composeGammaOn outerRead g Γf Γg) := by
  refine ⟨(composeE_isHermitian (Equiv.refl (α → Y)) (fun _ : α => g)
    (zextMat_isHermitian hf1.1) fun _ => hg1.1).submatrix Subtype.val,
    fun a b hab => ?_⟩
  have hab' : f a.2.choose = f b.2.choose := hab
  change composeE (Equiv.refl (α → Y)) (fun _ : α => g) (zextMat outerRead Γf)
    (fun _ : α => Γg) (a : α → Y) (b : α → Y) = 0
  rw [composeE_apply, tildeE_refl, tildeE_refl]
  have ha := a.2.choose_spec
  have hb := b.2.choose_spec
  rw [← ha, ← hb, zextMat_apply_encode hOuter, hf1.2 _ _ hab', zero_mul]

/-! ## The composition theorem -/

/-- **Composition lower bound on promise domains.**  Only the
lower-bound direction is proved. -/
theorem advPMOn_mul_le_advPMOn_compose {outerRead : X → α → Bool}
    {innerRead : Y → β → σ} {f : X → O} {g : Y → Bool}
    (hOuter : Function.Injective outerRead)
    (hInner : Function.Injective innerRead) :
    advPMOn outerRead f * advPMOn innerRead g
      ≤ advPMOn (composeReadOn outerRead g innerRead)
          (composeOutOn outerRead g f) := by
  classical
  have hRinj : Function.Injective (composeReadOn outerRead g innerRead) :=
    composeReadOn_injective hInner
  have hdet := separates_of_injective hRinj (composeOutOn outerRead g f)
  have hkey : ∀ Γf, IsAdvMatrixOn f Γf → (∀ i, ‖Γf ⊙ advDOn outerRead i‖ ≤ 1) →
      ∀ Γg, IsAdvMatrixOn g Γg → (∀ j, ‖Γg ⊙ advDOn innerRead j‖ ≤ 1) →
      ‖Γf‖ * ‖Γg‖ ≤ advPMOn (composeReadOn outerRead g innerRead)
        (composeOutOn outerRead g f) := by
    intro Γf hf1 hf2 Γg hg1 hg2
    rcases eq_or_lt_of_le (norm_nonneg Γf) with hfz | hΓfpos
    · rw [← hfz, zero_mul]
      exact advPMOn_nonneg hdet
    rcases eq_or_lt_of_le (norm_nonneg Γg) with hgz | hΓgpos
    · rw [← hgz, mul_zero]
      exact advPMOn_nonneg hdet
    -- a nonzero inner witness forces `Y` inhabited
    have hY : Nonempty Y := by
      rcases isEmpty_or_nonempty Y with hE | hE
      · have h0 : Γg = 0 := by
          ext u _
          exact hE.elim u
        rw [h0, norm_zero] at hΓgpos
        exact absurd hΓgpos (lt_irrefl 0)
      · exact hE
    -- a nonzero outer witness forces `α` inhabited
    have hα : Nonempty α := by
      have hΓf0 : Γf ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hΓfpos
        exact lt_irrefl 0 hΓfpos
      obtain ⟨x, y, hxy⟩ : ∃ x y, Γf x y ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hΓf0 (Matrix.ext fun x y => by rw [hc x y, Matrix.zero_apply])
      have hfxy : f x ≠ f y := fun h => hxy (hf1.2 x y h)
      have hne : outerRead x ≠ outerRead y := fun h => hfxy (by rw [hOuter h])
      obtain ⟨i, -⟩ := Function.ne_iff.mp hne
      exact ⟨i⟩
    haveI := hY
    haveI := hα
    have hk : Fintype.card α - 1 + 1 = Fintype.card α :=
      Nat.succ_pred_eq_of_pos Fintype.card_pos
    have hgcol : IsAdvCol g Γg := hg1
    have hZf : (zextMat outerRead Γf).IsHermitian := zextMat_isHermitian hf1.1
    have hnormZ : ‖zextMat outerRead Γf‖ = ‖Γf‖ := norm_zextMat hOuter Γf
    have hmaskZ : ∀ p : α, ‖zextMat outerRead Γf ⊙ advD p‖ ≤ 1 := by
      intro p
      rw [zextMat_hadamard, submatrix_advD_eq_advDOn, norm_zextMat hOuter]
      exact hf2 p
    -- the composed witness is feasible with masked norms `‖Γg‖ ^ (|α| - 1)`
    have hadv : IsAdvMatrixOn (composeOutOn outerRead g f)
        (composeGammaOn outerRead g Γf Γg) :=
      composeGammaOn_isAdvMatrixOn hOuter hf1 hg1
    have hmask : ∀ pq : α × β,
        ‖composeGammaOn outerRead g Γf Γg
            ⊙ advDOn (composeReadOn outerRead g innerRead) pq‖
          ≤ ‖Γg‖ ^ (Fintype.card α - 1) := by
      rintro ⟨p, q⟩
      rw [norm_composeGammaOn_hadamard]
      change ‖composeE (Equiv.refl (α → Y)) (fun _ : α => g)
          (zextMat outerRead Γf) (fun _ : α => Γg)
        ⊙ advDOn (composeReadE (Equiv.refl (α → Y)) innerRead) (p, q)‖ ≤ _
      rw [composeE_hadamard_advDOn (Equiv.refl (α → Y)) innerRead
          (fun _ : α => g) (zextMat outerRead Γf) (fun _ : α => Γg)
          (fun _ => hgcol) p q]
      have hshape : ∀ i : α, IsAdvCol ((fun _ : α => g) i)
          (Function.update (fun _ : α => Γg) p (Γg ⊙ advDOn innerRead q) i) := by
        intro i
        by_cases hip : i = p
        · rw [hip, Function.update_self]
          exact IsAdvCol.hadamard_advDOn hgcol innerRead q
        · rw [Function.update_of_ne hip]
          exact hgcol
      refine (normE_compose_le (Equiv.refl (α → Y))
        (hZf.hadamard (advD_isHermitian p)) hshape).trans ?_
      have hprod : ∏ i : α, ‖Function.update (fun _ : α => Γg) p
            (Γg ⊙ advDOn innerRead q) i‖
          = ‖Γg ⊙ advDOn innerRead q‖ * ‖Γg‖ ^ (Fintype.card α - 1) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p), Function.update_self]
        congr 1
        rw [Finset.prod_congr rfl fun i hi => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)],
          Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ p),
          Finset.card_univ]
      rw [hprod]
      calc ‖zextMat outerRead Γf ⊙ advD p‖ *
            (‖Γg ⊙ advDOn innerRead q‖ * ‖Γg‖ ^ (Fintype.card α - 1))
          ≤ 1 * (1 * ‖Γg‖ ^ (Fintype.card α - 1)) :=
            mul_le_mul (hmaskZ p)
              (mul_le_mul (hg2 q) le_rfl (by positivity) zero_le_one)
              (by positivity) zero_le_one
        _ = ‖Γg‖ ^ (Fintype.card α - 1) := by ring
    have hfinal := norm_div_le_advPMOn hdet hadv hmask (pow_pos hΓgpos _)
    refine le_trans ?_ hfinal
    rw [le_div_iff₀ (pow_pos hΓgpos _), norm_composeGammaOn]
    calc ‖Γf‖ * ‖Γg‖ * ‖Γg‖ ^ (Fintype.card α - 1)
        = ‖Γf‖ * (‖Γg‖ * ‖Γg‖ ^ (Fintype.card α - 1)) := mul_assoc _ _ _
      _ = ‖Γf‖ * ‖Γg‖ ^ (Fintype.card α - 1 + 1) := by rw [← pow_succ']
      _ = ‖Γf‖ * ‖Γg‖ ^ Fintype.card α := by rw [hk]
      _ ≤ ‖composeGammaFull outerRead g Γf Γg‖ := by
          have h := le_normE_compose (Equiv.refl (α → Y))
            (g := fun _ : α => g) (Γf := zextMat outerRead Γf)
            (M := fun _ : α => Γg) hZf fun _ => hgcol
          rw [Finset.prod_const, Finset.card_univ, hnormZ] at h
          exact h
  -- two supremum passes
  rcases eq_or_lt_of_le
    (advPMOn_nonneg (separates_of_injective hInner g)) with hg0 | hg0
  · rw [← hg0, mul_zero]
    exact advPMOn_nonneg hdet
  rw [← le_div_iff₀ hg0]
  refine advPMOn_le fun Γf hf1 hf2 => ?_
  rw [le_div_iff₀ hg0]
  rcases eq_or_lt_of_le (norm_nonneg Γf) with hf0 | hf0
  · rw [← hf0, zero_mul]
    exact advPMOn_nonneg hdet
  rw [mul_comm, ← le_div_iff₀ hf0]
  refine advPMOn_le fun Γg hg1 hg2 => ?_
  rw [le_div_iff₀ hf0, mul_comm]
  exact hkey Γf hf1 hf2 Γg hg1 hg2

end Compose

end QuantumQueryComplexity
