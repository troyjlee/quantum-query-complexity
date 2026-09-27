import QuantumQueryComplexity.Quantum.ChordGap
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The chord-distance spectral windows

The near and far windows of a unitary `U` at **threshold `Δ²`** — equivalently
chord radius `|Δ|`, since `Δ` is not assumed nonnegative anywhere — as the
spectral projectors of the **Hermitian** matrix `chordSq U = (1-U)ᴴ(1-U)`:

  `chordNearProj U Δ = cfc (fun l => if l ≤ Δ² then 1 else 0) (chordSq U)`,
  `chordFarProj  U Δ = 1 - chordNearProj U Δ`.

Two things make this work where diagonalizing a general unitary would not:

* **The discontinuous mask is legitimate.**  Mathlib's `cfc` needs the function
  continuous only *on the spectrum*, and a matrix has finite real spectrum
  (`Matrix.finite_real_spectrum`), which is discrete — so
  `Set.Finite.continuousOn` discharges every side condition.  Nothing here is an
  approximation of an indicator; it *is* the indicator.
* **`U` preserves the windows.**  `chordSq_commute` says `U` commutes with
  `chordSq U`, and `Commute.cfc_real` upgrades that to commuting with any `cfc`
  of it.  No simultaneous diagonalization, and no eigenbasis for `U`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H : Type} [Fintype H] [DecidableEq H]

/-- The complement of a projector is a projector.  (Belongs in
`FiniteHilbert.lean`; kept here to avoid a tree-wide rebuild.) -/
lemma IsQProjector.one_sub {P : Matrix H H ℂ} (hP : IsQProjector P) :
    IsQProjector (1 - P) := by
  constructor
  · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.1]
  · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP.2]
    abel

lemma isSelfAdjoint_chordSq (U : Matrix H H ℂ) : IsSelfAdjoint (chordSq U) := by
  show star (chordSq U) = chordSq U
  rw [Matrix.star_eq_conjTranspose]
  exact chordSq_conjTranspose U

/-- The near-window mask.  Discontinuous on `ℝ`, but that is irrelevant: it is
only ever restricted to a finite spectrum. -/
noncomputable def chordMask (Δ : ℝ) : ℝ → ℝ := fun l => if l ≤ Δ ^ 2 then 1 else 0

lemma continuousOn_chordMask (A : Matrix H H ℂ) (Δ : ℝ) :
    ContinuousOn (chordMask Δ) (spectrum ℝ A) :=
  Matrix.finite_real_spectrum.continuousOn _

lemma chordMask_mul_self (Δ : ℝ) (l : ℝ) :
    chordMask Δ l * chordMask Δ l = chordMask Δ l := by
  unfold chordMask
  by_cases h : l ≤ Δ ^ 2 <;> simp [h]

/-- **The near window**: the spectral projector of `chordSq U` for eigenvalues
at most `Δ²`, i.e. chord distance at most `|Δ|`. -/
noncomputable def chordNearProj (U : Matrix H H ℂ) (Δ : ℝ) : Matrix H H ℂ :=
  cfc (chordMask Δ) (chordSq U)

/-- **The far window.** -/
noncomputable def chordFarProj (U : Matrix H H ℂ) (Δ : ℝ) : Matrix H H ℂ :=
  1 - chordNearProj U Δ

theorem isQProjector_chordNearProj (U : Matrix H H ℂ) (Δ : ℝ) :
    IsQProjector (chordNearProj U Δ) := by
  constructor
  · have h : IsSelfAdjoint (chordNearProj U Δ) := cfc_predicate _ _
    have h2 : star (chordNearProj U Δ) = chordNearProj U Δ := h
    rwa [Matrix.star_eq_conjTranspose] at h2
  · rw [chordNearProj, ← cfc_mul (chordMask Δ) (chordMask Δ) (chordSq U)
      (continuousOn_chordMask _ Δ) (continuousOn_chordMask _ Δ)]
    congr 1
    funext l
    exact chordMask_mul_self Δ l

theorem isQProjector_chordFarProj (U : Matrix H H ℂ) (Δ : ℝ) :
    IsQProjector (chordFarProj U Δ) :=
  (isQProjector_chordNearProj U Δ).one_sub

/-- **`U` preserves the near window.** -/
theorem chordNearProj_commute {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (Δ : ℝ) :
    chordNearProj U Δ * U = U * chordNearProj U Δ := by
  have hc : Commute (chordSq U) U := chordSq_commute hU
  exact hc.cfc_real (chordMask Δ)

/-- **`U` preserves the far window.** -/
theorem chordFarProj_commute {U : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (Δ : ℝ) :
    chordFarProj U Δ * U = U * chordFarProj U Δ := by
  rw [chordFarProj, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    chordNearProj_commute hU]

/-! ## Quadratic forms

The bound below is an inequality between quadratic forms, so these are the
manipulations it needs.  Nothing here is specific to the chord form. -/

lemma qInner_add_mulVec (M M' : Matrix H H ℂ) (x : H → ℂ) :
    qInner x ((M + M') *ᵥ x) = qInner x (M *ᵥ x) + qInner x (M' *ᵥ x) := by
  rw [Matrix.add_mulVec, qInner_add_right]

lemma qInner_smul_mulVec (r : ℝ) (M : Matrix H H ℂ) (x : H → ℂ) :
    qInner x ((r • M) *ᵥ x) = (r : ℂ) * qInner x (M *ᵥ x) := by
  have hsm : (r • (M *ᵥ x) : H → ℂ) = ((r : ℂ)) • (M *ᵥ x) := by
    funext i
    simp [Complex.real_smul]
  rw [Matrix.smul_mulVec, hsm, qInner_smul_right]

/-- On a projector the quadratic form is the squared norm of the image. -/
lemma qInner_proj_self {P : Matrix H H ℂ} (hP : IsQProjector P) (x : H → ℂ) :
    qInner x (P *ᵥ x) = (qNormSq (P *ᵥ x) : ℂ) := by
  have h2 : qInner (P *ᵥ x) (P *ᵥ x) = qInner x (Pᴴ *ᵥ (P *ᵥ x)) :=
    qInner_mulVec_left P x (P *ᵥ x)
  rw [hP.1, Matrix.mulVec_mulVec, hP.2] at h2
  rw [← h2, qInner_self]

/-- For an operator commuting with a projector, the quadratic form restricts to
the projector's range. -/
lemma qInner_mul_proj {A P : Matrix H H ℂ} (hP : IsQProjector P)
    (hc : A * P = P * A) (x : H → ℂ) :
    qInner x ((A * P) *ᵥ x) = qInner (P *ᵥ x) (A *ᵥ (P *ᵥ x)) := by
  have h : qInner (P *ᵥ x) (A *ᵥ (P *ᵥ x)) = qInner x (Pᴴ *ᵥ (A *ᵥ (P *ᵥ x))) :=
    qInner_mulVec_left P x (A *ᵥ (P *ᵥ x))
  rw [hP.1] at h
  rw [h]
  congr 1
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hc, Matrix.mul_assoc, hP.2]

/-- **A `cfc` of a nonnegative function has nonnegative quadratic form.**  Proved
by writing `g = √g · √g`, so the matrix is `MᴴM`; no order theory is needed. -/
lemma qInner_cfc_nonneg (a : Matrix H H ℂ) (g : ℝ → ℝ) (hg : ∀ l, 0 ≤ g l)
    (x : H → ℂ) : 0 ≤ (qInner x (cfc g a *ᵥ x)).re := by
  set h : ℝ → ℝ := fun l => Real.sqrt (g l) with hhdef
  have hfun : (fun l => h l * h l) = g := funext fun l => Real.mul_self_sqrt (hg l)
  have hcfc : cfc g a = cfc h a * cfc h a := by
    rw [← hfun, cfc_mul h h a (Matrix.finite_real_spectrum.continuousOn _)
      (Matrix.finite_real_spectrum.continuousOn _)]
  have hsa : (cfc h a)ᴴ = cfc h a := by
    have hp : IsSelfAdjoint (cfc h a) := cfc_predicate h a
    have hst : star (cfc h a) = cfc h a := hp
    rwa [Matrix.star_eq_conjTranspose] at hst
  have hkey : qInner x (cfc g a *ᵥ x) = (qNormSq (cfc h a *ᵥ x) : ℂ) := by
    have e1 : qInner (cfc h a *ᵥ x) (cfc h a *ᵥ x)
        = qInner x (cfc h a *ᵥ (cfc h a *ᵥ x)) := by
      rw [qInner_mulVec_left, hsa]
    rw [hcfc, ← Matrix.mulVec_mulVec, ← e1, qInner_self]
  rw [hkey, Complex.ofReal_re]
  exact qNormSq_nonneg _

/-! ## The near-window bound -/

/-- The gap function `(Δ² - l)·mask l`, nonnegative everywhere. -/
noncomputable def chordGapFun (Δ : ℝ) : ℝ → ℝ :=
  fun l => (Δ ^ 2 - l) * chordMask Δ l

lemma chordGapFun_nonneg (Δ : ℝ) (l : ℝ) : 0 ≤ chordGapFun Δ l := by
  unfold chordGapFun chordMask
  by_cases h : l ≤ Δ ^ 2
  · rw [if_pos h, mul_one]
    linarith
  · rw [if_neg h, mul_zero]

lemma chordSq_mul_chordNearProj (U : Matrix H H ℂ) (Δ : ℝ) :
    chordSq U * chordNearProj U Δ + cfc (chordGapFun Δ) (chordSq U)
      = (Δ ^ 2 : ℝ) • chordNearProj U Δ := by
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ (chordSq U)) :=
    fun f => Matrix.finite_real_spectrum.continuousOn f
  have h1 : cfc (fun l : ℝ => id l * chordMask Δ l) (chordSq U)
      = chordSq U * chordNearProj U Δ := by
    rw [cfc_mul _ _ _ (hcont _) (hcont _), cfc_id ℝ (chordSq U) (isSelfAdjoint_chordSq U)]
    rfl
  have h2 : cfc (fun l : ℝ => Δ ^ 2 * chordMask Δ l) (chordSq U)
      = (Δ ^ 2 : ℝ) • chordNearProj U Δ := cfc_const_mul _ _ _ (hcont _)
  have h3 : chordGapFun Δ
      = fun l : ℝ => Δ ^ 2 * chordMask Δ l - id l * chordMask Δ l := by
    funext l
    unfold chordGapFun
    simp only [id]
    ring
  rw [h3, cfc_sub _ _ _ (hcont _) (hcont _), h1, h2]
  abel

/-- **The near-window bound**: on the near window the chord distance is at most
`|Δ|` (stated squared, so no absolute value appears). -/
theorem chordNear_bound_sq (U : Matrix H H ℂ) (Δ : ℝ) (x : H → ℂ) :
    qNormSq ((1 - U) *ᵥ (chordNearProj U Δ *ᵥ x))
      ≤ Δ ^ 2 * qNormSq (chordNearProj U Δ *ᵥ x) := by
  have hN := isQProjector_chordNearProj U Δ
  have hcomm : chordSq U * chordNearProj U Δ = chordNearProj U Δ * chordSq U := by
    have hc : Commute (chordSq U) (chordSq U) := Commute.refl _
    exact ((hc.cfc_real (chordMask Δ)) : Commute (chordNearProj U Δ) (chordSq U)).symm
  -- the left side, as a quadratic form at `x`
  have hL : qNormSq ((1 - U) *ᵥ (chordNearProj U Δ *ᵥ x))
      = (qInner x ((chordSq U * chordNearProj U Δ) *ᵥ x)).re := by
    rw [qNormSq_sub_mulVec, qInner_mul_proj hN hcomm x]
  -- the right side, likewise
  have hR : qNormSq (chordNearProj U Δ *ᵥ x)
      = (qInner x (chordNearProj U Δ *ᵥ x)).re := by
    rw [qInner_proj_self hN, Complex.ofReal_re]
  -- the gap term is nonnegative
  have hgap : 0 ≤ (qInner x (cfc (chordGapFun Δ) (chordSq U) *ᵥ x)).re :=
    qInner_cfc_nonneg _ _ (chordGapFun_nonneg Δ) x
  -- and the three add up
  have hsum := congrArg (fun M : Matrix H H ℂ => (qInner x (M *ᵥ x)).re)
    (chordSq_mul_chordNearProj U Δ)
  simp only [qInner_add_mulVec, qInner_smul_mulVec, Complex.add_re] at hsum
  rw [Complex.re_ofReal_mul] at hsum
  rw [hL, hR]
  linarith

/-! ## Decomposition, and the fixed space

The two windows are complementary orthogonal projectors, so every state splits
into a near part and a far part with no cross term.  And the **fixed space of
`U` sits entirely in the near window**, for every `Δ`: a vector with `U x = x`
has chord distance `0`, and `0 ≤ Δ²` always.  That is the statement a phase
detector needs in order to conclude that it never mistakes a fixed vector for a
rotating one. -/

@[simp] theorem chordNearProj_add_chordFarProj (U : Matrix H H ℂ) (Δ : ℝ) :
    chordNearProj U Δ + chordFarProj U Δ = 1 := by
  rw [chordFarProj]
  abel

theorem chordNearProj_mul_chordFarProj (U : Matrix H H ℂ) (Δ : ℝ) :
    chordNearProj U Δ * chordFarProj U Δ = 0 := by
  rw [chordFarProj, Matrix.mul_sub, Matrix.mul_one,
    (isQProjector_chordNearProj U Δ).2, sub_self]

theorem chordFarProj_mul_chordNearProj (U : Matrix H H ℂ) (Δ : ℝ) :
    chordFarProj U Δ * chordNearProj U Δ = 0 := by
  rw [chordFarProj, Matrix.sub_mul, Matrix.one_mul,
    (isQProjector_chordNearProj U Δ).2, sub_self]

/-- **The Pythagorean decomposition** across the two windows. -/
theorem qNormSq_chord_decomp (U : Matrix H H ℂ) (Δ : ℝ) (x : H → ℂ) :
    qNormSq x = qNormSq (chordNearProj U Δ *ᵥ x) + qNormSq (chordFarProj U Δ *ᵥ x) := by
  have hsplit : chordNearProj U Δ *ᵥ x + chordFarProj U Δ *ᵥ x = x := by
    rw [← Matrix.add_mulVec, chordNearProj_add_chordFarProj, Matrix.one_mulVec]
  have horth : (qInner (chordNearProj U Δ *ᵥ x) (chordFarProj U Δ *ᵥ x)).re = 0 := by
    rw [qInner_mulVec_left, (isQProjector_chordNearProj U Δ).1, Matrix.mulVec_mulVec,
      chordNearProj_mul_chordFarProj, Matrix.zero_mulVec, qInner_zero_right,
      Complex.zero_re]
  have hadd := qNormSq_add (chordNearProj U Δ *ᵥ x) (chordFarProj U Δ *ᵥ x)
  rw [hsplit, horth] at hadd
  linarith

/-- If `g` vanishes at `0` then `cfc g a` kills the kernel of `a`.  Proved by
factoring `g l = l · h l` — legitimate for *any* `g` here, since `h` need only
be continuous on a finite spectrum. -/
lemma cfc_mulVec_eq_zero_of_mulVec_eq_zero {a : Matrix H H ℂ} (ha : IsSelfAdjoint a)
    (g : ℝ → ℝ) (hg0 : g 0 = 0) {x : H → ℂ} (hx : a *ᵥ x = 0) : cfc g a *ᵥ x = 0 := by
  classical
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ a) :=
    fun f => Matrix.finite_real_spectrum.continuousOn f
  set h : ℝ → ℝ := fun l => if l = 0 then 0 else g l / l with hhdef
  have hfun : (fun l : ℝ => id l * h l) = g := by
    funext l
    by_cases hl : l = 0
    · rw [hl]
      simp [hhdef, hg0]
    · simp only [hhdef, id, if_neg hl]
      field_simp
  have hcomm : cfc h a * a = a * cfc h a := (Commute.refl a).cfc_real h
  have hsplit : cfc g a = cfc h a * a := by
    have h1 : cfc (fun l : ℝ => id l * h l) a = a * cfc h a := by
      rw [cfc_mul _ _ _ (hcont _) (hcont _), cfc_id ℝ a ha]
    rw [← hfun, h1, ← hcomm]
  rw [hsplit, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

/-- **The fixed space of `U` lies in the near window**, for every `Δ`. -/
theorem chordNearProj_mulVec_of_fixed (U : Matrix H H ℂ) (Δ : ℝ) {x : H → ℂ}
    (hx : U *ᵥ x = x) : chordNearProj U Δ *ᵥ x = x := by
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ (chordSq U)) :=
    fun f => Matrix.finite_real_spectrum.continuousOn f
  have h0 : chordSq U *ᵥ x = 0 := by
    rw [chordSq_mulVec_eq_zero_iff, Matrix.sub_mulVec, Matrix.one_mulVec, hx, sub_self]
  have hg : cfc (fun l : ℝ => chordMask Δ l - 1) (chordSq U)
      = chordNearProj U Δ - 1 := by
    rw [show (fun l : ℝ => chordMask Δ l - 1)
        = (fun l : ℝ => chordMask Δ l - (1 : ℝ → ℝ) l) from rfl,
      cfc_sub _ _ _ (hcont _) (hcont _), cfc_one ℝ (chordSq U) (isSelfAdjoint_chordSq U)]
    rfl
  have hmask0 : chordMask Δ 0 - 1 = 0 := by
    unfold chordMask
    rw [if_pos (sq_nonneg Δ), sub_self]
  have hz := cfc_mulVec_eq_zero_of_mulVec_eq_zero (isSelfAdjoint_chordSq U)
    (fun l => chordMask Δ l - 1) hmask0 h0
  rw [hg, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hz
  exact hz

/-- **The far window misses the fixed space.** -/
theorem chordFarProj_mulVec_of_fixed (U : Matrix H H ℂ) (Δ : ℝ) {x : H → ℂ}
    (hx : U *ᵥ x = x) : chordFarProj U Δ *ᵥ x = 0 := by
  rw [chordFarProj, Matrix.sub_mulVec, Matrix.one_mulVec,
    chordNearProj_mulVec_of_fixed U Δ hx, sub_self]

/-! ## The far-window bound

The companion to `chordNear_bound_sq`, and the coercivity estimate the
uniform-clock argument consumes: off the near window the chord distance is at
least `|Δ|`.  Same proof shape, with the gap function's sign reversed. -/

lemma chordFarProj_eq_cfc (U : Matrix H H ℂ) (Δ : ℝ) :
    chordFarProj U Δ = cfc (fun l : ℝ => 1 - chordMask Δ l) (chordSq U) := by
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ (chordSq U)) :=
    fun f => Matrix.finite_real_spectrum.continuousOn f
  rw [show (fun l : ℝ => 1 - chordMask Δ l)
      = (fun l : ℝ => (1 : ℝ → ℝ) l - chordMask Δ l) from rfl,
    cfc_sub _ _ _ (hcont _) (hcont _), cfc_one ℝ (chordSq U) (isSelfAdjoint_chordSq U)]
  rfl

/-- The far gap function `(l - Δ²)·(1 - mask l)`, nonnegative everywhere. -/
noncomputable def chordFarGapFun (Δ : ℝ) : ℝ → ℝ :=
  fun l => (l - Δ ^ 2) * (1 - chordMask Δ l)

lemma chordFarGapFun_nonneg (Δ : ℝ) (l : ℝ) : 0 ≤ chordFarGapFun Δ l := by
  unfold chordFarGapFun chordMask
  by_cases h : l ≤ Δ ^ 2
  · rw [if_pos h]
    simp
  · rw [if_neg h]
    have hlt : Δ ^ 2 < l := not_le.mp h
    have : (0 : ℝ) ≤ l - Δ ^ 2 := by linarith
    simpa using this

lemma chordSq_mul_chordFarProj (U : Matrix H H ℂ) (Δ : ℝ) :
    (Δ ^ 2 : ℝ) • chordFarProj U Δ + cfc (chordFarGapFun Δ) (chordSq U)
      = chordSq U * chordFarProj U Δ := by
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ (chordSq U)) :=
    fun f => Matrix.finite_real_spectrum.continuousOn f
  have h1 : cfc (fun l : ℝ => id l * (1 - chordMask Δ l)) (chordSq U)
      = chordSq U * chordFarProj U Δ := by
    rw [cfc_mul _ _ _ (hcont _) (hcont _), cfc_id ℝ (chordSq U) (isSelfAdjoint_chordSq U),
      chordFarProj_eq_cfc]
  have h2 : cfc (fun l : ℝ => Δ ^ 2 * (1 - chordMask Δ l)) (chordSq U)
      = (Δ ^ 2 : ℝ) • chordFarProj U Δ := by
    rw [cfc_const_mul _ _ _ (hcont _), chordFarProj_eq_cfc]
  have h3 : chordFarGapFun Δ
      = fun l : ℝ => id l * (1 - chordMask Δ l) - Δ ^ 2 * (1 - chordMask Δ l) := by
    funext l
    unfold chordFarGapFun
    simp only [id]
    ring
  rw [h3, cfc_sub _ _ _ (hcont _) (hcont _), h1, h2]
  abel

/-- **The far-window bound (coercivity)**: off the near window the chord
distance is at least `|Δ|`. -/
theorem chordFar_bound_sq (U : Matrix H H ℂ) (Δ : ℝ) (x : H → ℂ) :
    Δ ^ 2 * qNormSq (chordFarProj U Δ *ᵥ x)
      ≤ qNormSq ((1 - U) *ᵥ (chordFarProj U Δ *ᵥ x)) := by
  have hF := isQProjector_chordFarProj U Δ
  have hNc : chordSq U * chordNearProj U Δ = chordNearProj U Δ * chordSq U := by
    have hc : Commute (chordSq U) (chordSq U) := Commute.refl _
    exact ((hc.cfc_real (chordMask Δ)) : Commute (chordNearProj U Δ) (chordSq U)).symm
  have hcomm : chordSq U * chordFarProj U Δ = chordFarProj U Δ * chordSq U := by
    rw [chordFarProj, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hNc]
  have hR : qNormSq ((1 - U) *ᵥ (chordFarProj U Δ *ᵥ x))
      = (qInner x ((chordSq U * chordFarProj U Δ) *ᵥ x)).re := by
    rw [qNormSq_sub_mulVec, qInner_mul_proj hF hcomm x]
  have hL : qNormSq (chordFarProj U Δ *ᵥ x)
      = (qInner x (chordFarProj U Δ *ᵥ x)).re := by
    rw [qInner_proj_self hF, Complex.ofReal_re]
  have hgap : 0 ≤ (qInner x (cfc (chordFarGapFun Δ) (chordSq U) *ᵥ x)).re :=
    qInner_cfc_nonneg _ _ (chordFarGapFun_nonneg Δ) x
  have hsum := congrArg (fun M : Matrix H H ℂ => (qInner x (M *ᵥ x)).re)
    (chordSq_mul_chordFarProj U Δ)
  simp only [qInner_add_mulVec, qInner_smul_mulVec, Complex.add_re] at hsum
  rw [Complex.re_ofReal_mul] at hsum
  rw [hL, hR]
  linarith

/-! ## The effective spectral gap

The statement is naturally *squared*: everything in sight is a squared norm, and
squaring avoids square roots entirely.  The core is the elementary identity
`(1 - R_P R_L) w = 2 P w` of `ChordGap.lean`; the spectral content is only that
the near window contracts `1 - U` by `Δ` and that a projector does not expand. -/

/-- **The effective spectral gap.**  If `L` annihilates `w`, then the part of
`P w` lying in the chord-distance window of threshold `Δ²` (radius `|Δ|`) of
`R_P R_L` has squared norm at most `(Δ²/4)‖w‖²`.

No sign hypothesis on `Δ` is needed: the squared formulation makes `0 ≤ Δ`
vacuous, since only `Δ²` ever appears. -/
theorem effective_chord_gap_sq {P L : Matrix H H ℂ} (hP : IsQProjector P)
    (hL : IsQProjector L) {w : H → ℂ} (hw : L *ᵥ w = 0) (Δ : ℝ) :
    qNormSq (chordNearProj (qRefl P * qRefl L) Δ *ᵥ (P *ᵥ w))
      ≤ (Δ ^ 2 / 4) * qNormSq w := by
  set U := qRefl P * qRefl L with hUdef
  have hUu : U ∈ Matrix.unitaryGroup H ℂ :=
    mul_mem (qRefl_mem_unitaryGroup hP) (qRefl_mem_unitaryGroup hL)
  set N := chordNearProj U Δ with hNdef
  have hNcomm : N * (1 - U) = (1 - U) * N := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      chordNearProj_commute hUu]
  have hcore : (1 - U) *ᵥ w = (2 : ℂ) • (P *ᵥ w) := one_sub_qRefl_mul_qRefl_mulVec hw
  have key : (2 : ℂ) • (N *ᵥ (P *ᵥ w)) = (1 - U) *ᵥ (N *ᵥ w) := by
    calc (2 : ℂ) • (N *ᵥ (P *ᵥ w))
        = N *ᵥ ((2 : ℂ) • (P *ᵥ w)) := by rw [Matrix.mulVec_smul]
      _ = N *ᵥ ((1 - U) *ᵥ w) := by rw [hcore]
      _ = (N * (1 - U)) *ᵥ w := by rw [Matrix.mulVec_mulVec]
      _ = ((1 - U) * N) *ᵥ w := by rw [hNcomm]
      _ = (1 - U) *ᵥ (N *ᵥ w) := by rw [Matrix.mulVec_mulVec]
  have h4 : (4 : ℝ) * qNormSq (N *ᵥ (P *ᵥ w)) = qNormSq ((1 - U) *ᵥ (N *ᵥ w)) := by
    rw [← key, qNormSq_smul]
    norm_num
  have hbound := chordNear_bound_sq U Δ w
  have hproj := (isQProjector_chordNearProj U Δ).qNormSq_mulVec_le w
  nlinarith [sq_nonneg Δ, qNormSq_nonneg (N *ᵥ (P *ᵥ w)), qNormSq_nonneg w]

end QuantumQueryComplexity
