import QuantumQueryComplexity.Composition.Span
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The norm of a composed matrix (HLŠ Lemma 16 / BL Lemma 21)

`‖composeE e g Γf M‖ = ‖Γf‖ * ∏ i, ‖M i‖` for symmetric `Γf` and g-shaped
inner matrices `M i`.

* `≤` (`normE_compose_le`): every tensor eigenvector's eigenvalue is an
  eigenvalue of some `Γf ⊙ Emat`, bounded via the Schur-multiplier estimate;
  the tensor eigenvectors span, so the spanning-eigenvector bound applies.
  No sign-flipping analysis is needed (this replaces HLŠ's Item 4 — and
  repairs the gap in BL Lemma 21's Eq. (4), whose orthogonality claim fails
  for ±-paired eigenvalues of the dilation).
* `≥` (`le_normE_compose`): at the sign vertex `Emat` degenerates to a
  `±1`-diagonal conjugate of `(∏ ‖M i‖) • Γf`, producing an explicit tensor
  eigenvector with eigenvalue `± ‖Γf‖ * ∏ ‖M i‖`; it is nonvanishing by the
  bipartite-support lemma.

As in `Hat.lean` the block decomposition is abstract, and the cube statements
`norm_compose_le` / `le_norm_compose` / `norm_compose` are the `cubeBlocks`
instance.  Two side conditions appear in the general form and are automatic at
a cube: the `≤` direction is stated for a possibly empty composed type `Z`
(the spanning-eigenvector bound wants `Nonempty`), and the `≥` direction needs
`Nonempty Y` to select an inner eigenvalue of maximal modulus.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

lemma div_self_sq {a R : ℝ} (hR : 0 < R) (h : |a| = R) :
    a / R * (a / R) = 1 := by
  have h1 : a * a = R * R := by
    have h2 := sq_abs a
    rw [h, pow_two, pow_two] at h2
    exact h2.symm
  rw [div_mul_div_comm, h1]
  exact div_self (by positivity)

/-- The vertex eigen-computation: at a sign vertex, an eigenvector of `Γf`
conjugated by the `±1` diagonal is an eigenvector of `Γf ⊙ Emat R lam` with
eigenvalue `(∏ R) * θ`. -/
lemma vertex_eigen {α : Type*} [Fintype α] [DecidableEq α]
    {Γf : Matrix (α → Bool) (α → Bool) ℝ} (hΓf : Γf.IsHermitian)
    {R lam ε : α → ℝ}
    (hε : ∀ i, ε i * ε i = 1) (hlam_eq : ∀ i, ε i * R i = lam i)
    {θ : ℝ} {w : (α → Bool) → ℝ} (hw : Γf *ᵥ w = θ • w) :
    (Γf ⊙ Emat R lam) *ᵥ (Matrix.diagonal (chiSign ε) *ᵥ w)
      = ((∏ i, R i) * θ) • (Matrix.diagonal (chiSign ε) *ᵥ w) := by
  have hlam_fun : (fun i => ε i * R i) = lam := funext hlam_eq
  rw [← hlam_fun, hadamard_Emat_vertex Γf hε, Matrix.smul_mulVec]
  have hcore : (Matrix.diagonal (chiSign ε) * Γf * Matrix.diagonal (chiSign ε))
      *ᵥ (Matrix.diagonal (chiSign ε) *ᵥ w)
      = θ • (Matrix.diagonal (chiSign ε) *ᵥ w) := by
    rw [Matrix.mulVec_mulVec,
      mul_assoc (Matrix.diagonal (chiSign ε) * Γf),
      diagonal_chiSign_mul_self hε, mul_one,
      ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
  rw [hcore, smul_smul]

/-! ## The norm formula over an abstract block decomposition -/

section General

variable {α Y Z : Type*} [Fintype α] [DecidableEq α]
variable [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
variable {g : α → Y → Bool} {Γf : Matrix (α → Bool) (α → Bool) ℝ}
  {M : α → Matrix Y Y ℝ}

/-- The `≤` direction of HLŠ Lemma 16. -/
theorem normE_compose_le (e : Z ≃ (α → Y)) (hΓf : Γf.IsHermitian)
    (hM : ∀ i, IsAdvCol (g i) (M i)) :
    ‖composeE e g Γf M‖ ≤ ‖Γf‖ * ∏ i, ‖M i‖ := by
  classical
  have hRHS : 0 ≤ ‖Γf‖ * ∏ i, ‖M i‖ :=
    mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · have h0 : composeE e g Γf M = 0 := by
      ext x y
      exact hZ.elim x
    rw [h0, norm_zero]
    exact hRHS
  haveI : Nonempty Z := hZ
  have hAH : ∀ c : α → Y,
      (Γf ⊙ Emat (fun i => ‖M i‖)
        fun i => (hM i).isHermitian.eigenvalues (c i)).IsHermitian :=
    fun c => hΓf.hadamard (Emat_isHermitian _ _)
  refine norm_le_of_eigenvector_family
    (composeE_isHermitian e g hΓf fun i => (hM i).isHermitian)
    (fun p : (α → Y) × (α → Bool) =>
      tensorVecE e g
        (fun i => WithLp.ofLp ((hM i).isHermitian.eigenvectorBasis (p.1 i)))
        (WithLp.ofLp ((hAH p.1).eigenvectorBasis p.2)))
    (fun p => (hAH p.1).eigenvalues p.2) hRHS ?_ ?_ ?_
  · rintro ⟨c, j⟩
    exact composeE_mulVec_tensorVec e hM
      (fun i => (hM i).isHermitian.mulVec_eigenvectorBasis (c i))
      ((hAH c).mulVec_eigenvectorBasis j)
  · exact span_tensorVecE_top e
      (fun i d => WithLp.ofLp ((hM i).isHermitian.eigenvectorBasis d))
      (fun i => (hM i).isHermitian.eigenvectorBasis.orthonormal)
      (fun c => (hAH c).eigenvectorBasis)
  · rintro ⟨c, j⟩
    calc |(hAH c).eigenvalues j|
        ≤ ‖Γf ⊙ Emat (fun i => ‖M i‖)
            fun i => (hM i).isHermitian.eigenvalues (c i)‖ :=
          abs_eigenvalues_le_norm (hAH c) j
      _ ≤ (∏ i, ‖M i‖) * ‖Γf‖ :=
          norm_hadamard_Emat_le Γf (fun i => norm_nonneg (M i))
            (fun i => abs_eigenvalues_le_norm (hM i).isHermitian (c i))
      _ = ‖Γf‖ * ∏ i, ‖M i‖ := mul_comm _ _

/-- The `≥` direction of HLŠ Lemma 16. -/
theorem le_normE_compose [Nonempty Y] (e : Z ≃ (α → Y)) (hΓf : Γf.IsHermitian)
    (hM : ∀ i, IsAdvCol (g i) (M i)) :
    ‖Γf‖ * ∏ i, ‖M i‖ ≤ ‖composeE e g Γf M‖ := by
  classical
  by_cases hz : ∃ i, ‖M i‖ = 0
  · obtain ⟨i₀, hi₀⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ i₀) hi₀, mul_zero]
    exact norm_nonneg _
  push_neg at hz
  have hMpos : ∀ i, 0 < ‖M i‖ := fun i =>
    (norm_nonneg (M i)).lt_of_ne (Ne.symm (hz i))
  have hpick : ∀ i, ∃ d, |(hM i).isHermitian.eigenvalues d| = ‖M i‖ := fun i =>
    exists_abs_eigenvalues_eq_norm (hM i).isHermitian
  choose d hd using hpick
  have hlam0 : ∀ i, (hM i).isHermitian.eigenvalues (d i) ≠ 0 := by
    intro i h
    have h2 := hd i
    rw [h, abs_zero] at h2
    exact (hMpos i).ne' h2.symm
  have hε : ∀ i, ((hM i).isHermitian.eigenvalues (d i) / ‖M i‖) *
      ((hM i).isHermitian.eigenvalues (d i) / ‖M i‖) = 1 := fun i =>
    div_self_sq (hMpos i) (hd i)
  have hlam_eq : ∀ i, ((hM i).isHermitian.eigenvalues (d i) / ‖M i‖) * ‖M i‖
      = (hM i).isHermitian.eigenvalues (d i) := fun i =>
    div_mul_cancel₀ _ (hMpos i).ne'
  -- the outer eigen-pair with |θ| = ‖Γf‖
  obtain ⟨j₀, hj₀⟩ := exists_abs_eigenvalues_eq_norm hΓf
  have hw : Γf *ᵥ WithLp.ofLp (hΓf.eigenvectorBasis j₀)
      = hΓf.eigenvalues j₀ • WithLp.ofLp (hΓf.eigenvectorBasis j₀) :=
    hΓf.mulVec_eigenvectorBasis j₀
  have hw0 : WithLp.ofLp (hΓf.eigenvectorBasis j₀) ≠ 0 := fun h0 =>
    hΓf.eigenvectorBasis.orthonormal.ne_zero j₀ (by
      have hb : hΓf.eigenvectorBasis j₀
          = WithLp.toLp 2 (WithLp.ofLp (hΓf.eigenvectorBasis j₀)) := rfl
      rw [hb, h0]
      rfl)
  have hvert := vertex_eigen (ε := fun i =>
      (hM i).isHermitian.eigenvalues (d i) / ‖M i‖)
    (lam := fun i => (hM i).isHermitian.eigenvalues (d i))
    (R := fun i => ‖M i‖) hΓf hε hlam_eq hw
  have hvv : ∀ i, M i *ᵥ
      WithLp.ofLp ((hM i).isHermitian.eigenvectorBasis (d i))
      = (hM i).isHermitian.eigenvalues (d i) •
        WithLp.ofLp ((hM i).isHermitian.eigenvectorBasis (d i)) := fun i =>
    (hM i).isHermitian.mulVec_eigenvectorBasis (d i)
  have hbig := composeE_mulVec_tensorVec e hM hvv hvert
  -- nonvanishing of the tensor witness
  have hvv0 : ∀ i,
      WithLp.ofLp ((hM i).isHermitian.eigenvectorBasis (d i)) ≠ 0 := fun i h0 =>
    (hM i).isHermitian.eigenvectorBasis.orthonormal.ne_zero (d i) (by
      have hb : (hM i).isHermitian.eigenvectorBasis (d i)
          = WithLp.toLp 2
            (WithLp.ofLp ((hM i).isHermitian.eigenvectorBasis (d i))) := rfl
      rw [hb, h0]
      rfl)
  have hwstar0 : Matrix.diagonal (chiSign fun i =>
      (hM i).isHermitian.eigenvalues (d i) / ‖M i‖) *ᵥ
      WithLp.ofLp (hΓf.eigenvectorBasis j₀) ≠ 0 :=
    chiSign_diagonal_mulVec_ne_zero hε hw0
  have hT0 : tensorVecE e g
      (fun i => WithLp.ofLp ((hM i).isHermitian.eigenvectorBasis (d i)))
      (Matrix.diagonal (chiSign fun i =>
        (hM i).isHermitian.eigenvalues (d i) / ‖M i‖) *ᵥ
        WithLp.ofLp (hΓf.eigenvectorBasis j₀)) ≠ 0 := by
    obtain ⟨a₀, ha₀⟩ := Function.ne_iff.mp hwstar0
    have hsupp : ∀ i, ∃ u, g i u = a₀ i ∧
        WithLp.ofLp ((hM i).isHermitian.eigenvectorBasis (d i)) u ≠ 0 :=
      fun i => (hM i).exists_eigenvector_support (hvv i) (hlam0 i) (hvv0 i)
        (a₀ i)
    choose u hu1 hu2 using hsupp
    have hslice : ∀ i, sliceE e (e.symm u) i = u i := fun i =>
      congrFun (e.apply_symm_apply u) i
    intro h0
    have hx := congrFun h0 (e.symm u)
    simp only [tensorVecE_apply, Pi.zero_apply] at hx
    have htilde : tildeE e g (e.symm u) = a₀ := by
      funext i
      rw [tildeE_apply, hslice i]
      exact hu1 i
    rw [htilde] at hx
    rcases mul_eq_zero.mp hx with h | h
    · exact ha₀ h
    · obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp h
      rw [hslice i] at hi
      exact hu2 i hi
  have habs := abs_eigenvalue_le_norm hbig hT0
  calc ‖Γf‖ * ∏ i, ‖M i‖
      = |(∏ i, ‖M i‖) * hΓf.eigenvalues j₀| := by
        rw [abs_mul, abs_of_nonneg (Finset.prod_nonneg fun i _ =>
          norm_nonneg (M i)), hj₀]
        ring
    _ ≤ ‖composeE e g Γf M‖ := habs

/-- HLŠ Lemma 16 / BL Lemma 21, over an abstract block decomposition. -/
theorem normE_compose [Nonempty Y] (e : Z ≃ (α → Y)) (hΓf : Γf.IsHermitian)
    (hM : ∀ i, IsAdvCol (g i) (M i)) :
    ‖composeE e g Γf M‖ = ‖Γf‖ * ∏ i, ‖M i‖ :=
  le_antisymm (normE_compose_le e hΓf hM) (le_normE_compose e hΓf hM)

end General

/-! ## The cube instance -/

section Cube

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  {g : α → (β → Bool) → Bool} {Γf : Matrix (α → Bool) (α → Bool) ℝ}
  {M : α → Matrix (β → Bool) (β → Bool) ℝ}

/-- The `≤` direction of HLŠ Lemma 16. -/
theorem norm_compose_le (hΓf : Γf.IsHermitian)
    (hM : ∀ i, IsAdvMatrix (g i) (M i)) :
    ‖compose g Γf M‖ ≤ ‖Γf‖ * ∏ i, ‖M i‖ :=
  normE_compose_le (cubeBlocks α β) hΓf fun i => (hM i).isAdvCol

/-- The `≥` direction of HLŠ Lemma 16. -/
theorem le_norm_compose (hΓf : Γf.IsHermitian)
    (hM : ∀ i, IsAdvMatrix (g i) (M i)) :
    ‖Γf‖ * ∏ i, ‖M i‖ ≤ ‖compose g Γf M‖ :=
  le_normE_compose (cubeBlocks α β) hΓf fun i => (hM i).isAdvCol

/-- HLŠ Lemma 16 / BL Lemma 21: the norm of the composed matrix. -/
theorem norm_compose (hΓf : Γf.IsHermitian)
    (hM : ∀ i, IsAdvMatrix (g i) (M i)) :
    ‖compose g Γf M‖ = ‖Γf‖ * ∏ i, ‖M i‖ :=
  le_antisymm (norm_compose_le hΓf hM) (le_norm_compose hΓf hM)

end Cube

end QuantumQueryComplexity
