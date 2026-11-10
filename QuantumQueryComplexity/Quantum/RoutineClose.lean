import QuantumQueryComplexity.Quantum.KronLift
import QuantumQueryComplexity.Quantum.Approximation

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Approximate preparations inside larger routines

A routine `R` **prepares `t` from `ψ` up to the phase `c` and the error `η`** on the input `a`
when `‖R ψ − c·t‖ ≤ η`, with `‖c‖ = 1`. The phase is allowed because amplitude-amplification
preparations (for example `exists_coherentPrep`) end in `c·t` with an input-dependent `c`. Such a
phase is harmless wherever every use of the preparation on the same input carries the same `c`:
the rows of a walk update, for instance (`ApproxWalkOK` takes one common phase for all rows).

This file is the bridge from a preparation to the routines that use it.
* `QRoutine.run_comp_close`: in a composition, errors add and phases multiply.
* `QRoutine.run_close_kronLift`: lifting along an oracle-compatible split `W' ≃ W × D`, with the
  environment in a state `ξ`, keeps the error (times `‖ξ‖`) and the phase.
* `QRoutine.run_close_sandwich`: a routine made of a query-free unitary, one lifted preparation,
  and a query-free unitary (the shape of a walk update that prepares one fresh label) maps any
  `φ` with `B₁ φ = splitVec e ψ ξ` to within `η‖ξ‖` of `c · B₂ (splitVec e t ξ)`. The phase `c`
  depends only on the preparation and the input, not on `φ`: every row of such an update carries
  the same phase.
-/

namespace QuantumQueryComplexity

open scoped Matrix

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-- **Errors add and phases multiply under composition** (`R₁` first, then `R₂`). -/
theorem QRoutine.run_comp_close (R₁ R₂ : QRoutine ι σ W) (a : ι → σ)
    {φ₀ φ₁ φ₂ : QBasis ι σ W → ℂ} {c₁ c₂ : ℂ} {η₁ η₂ : ℝ} (hc₁ : ‖c₁‖ = 1)
    (h₁ : qNorm (R₁.run a *ᵥ φ₀ - c₁ • φ₁) ≤ η₁)
    (h₂ : qNorm (R₂.run a *ᵥ φ₁ - c₂ • φ₂) ≤ η₂) :
    qNorm ((R₁.comp R₂).run a *ᵥ φ₀ - (c₁ * c₂) • φ₂) ≤ η₁ + η₂ := by
  have key : (R₁.comp R₂).run a *ᵥ φ₀ - (c₁ * c₂) • φ₂
      = R₂.run a *ᵥ (R₁.run a *ᵥ φ₀ - c₁ • φ₁) + c₁ • (R₂.run a *ᵥ φ₁ - c₂ • φ₂) := by
    rw [QRoutine.comp_run, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul,
      smul_sub, mul_smul]
    abel
  rw [key]
  calc qNorm (R₂.run a *ᵥ (R₁.run a *ᵥ φ₀ - c₁ • φ₁) + c₁ • (R₂.run a *ᵥ φ₁ - c₂ • φ₂))
      ≤ qNorm (R₂.run a *ᵥ (R₁.run a *ᵥ φ₀ - c₁ • φ₁))
          + qNorm (c₁ • (R₂.run a *ᵥ φ₁ - c₂ • φ₂)) := qNorm_add_le _ _
    _ = qNorm (R₁.run a *ᵥ φ₀ - c₁ • φ₁) + qNorm (R₂.run a *ᵥ φ₁ - c₂ • φ₂) := by
        rw [qNorm_mulVec (R₂.run_mem_unitaryGroup a), qNorm_smul, hc₁, one_mul]
    _ ≤ η₁ + η₂ := add_le_add h₁ h₂

variable {W' D : Type} [Fintype W'] [DecidableEq W'] [Fintype D] [DecidableEq D]

/-- `splitVec` is linear in its system factor: differences and scalars pass through. -/
private lemma rcl_splitVec_sub_smul {β γ δ : Type} (e : β ≃ γ × δ) (v t : γ → ℂ)
    (ξ : δ → ℂ) (c : ℂ) :
    splitVec e v ξ - c • splitVec e t ξ = splitVec e (v - c • t) ξ := by
  funext b
  simp only [Pi.sub_apply, Pi.smul_apply, splitVec_apply, smul_eq_mul]
  ring

/-- The norm of a split state is the product of the factors' norms. -/
private lemma rcl_qNorm_splitVec {β γ δ : Type} [Fintype β] [DecidableEq β] [Fintype γ]
    [DecidableEq γ] [Fintype δ] [DecidableEq δ] (e : β ≃ γ × δ) (v : γ → ℂ) (ξ : δ → ℂ) :
    qNorm (splitVec e v ξ) = qNorm v * qNorm ξ := by
  rw [qNorm, qNormSq_splitVec, Real.sqrt_mul (qNormSq_nonneg v), qNorm, qNorm]

/-- **A lifted preparation keeps its error and its phase**: along an oracle-compatible split,
with the environment in `ξ`. -/
theorem QRoutine.run_close_kronLift {e : QBasis ι σ W' ≃ QBasis ι σ W × D} (he : OracleCompat e)
    (R : QRoutine ι σ W) (a : ι → σ) (ψ t : QBasis ι σ W → ℂ) (ξ : D → ℂ) (c : ℂ) :
    qNorm ((R.kronLift e).run a *ᵥ splitVec e ψ ξ - c • splitVec e t ξ)
      = qNorm (R.run a *ᵥ ψ - c • t) * qNorm ξ := by
  have hrun : (R.kronLift e).run a *ᵥ splitVec e ψ ξ = splitVec e (R.run a *ᵥ ψ) ξ :=
    QRoutine.kronLift_runUpto_splitVec he R a R.len ψ ξ
  rw [hrun, rcl_splitVec_sub_smul, rcl_qNorm_splitVec]

/-- **An update built around one lifted preparation inherits its precision and phase**: a
query-free unitary `B₁`, the preparation lifted along `e`, a query-free unitary `B₂`. -/
theorem QRoutine.run_close_sandwich {e : QBasis ι σ W' ≃ QBasis ι σ W × D} (he : OracleCompat e)
    (R : QRoutine ι σ W) (B₁ B₂ : Matrix (QBasis ι σ W') (QBasis ι σ W') ℂ)
    (hB₁ : B₁ ∈ Matrix.unitaryGroup (QBasis ι σ W') ℂ)
    (hB₂ : B₂ ∈ Matrix.unitaryGroup (QBasis ι σ W') ℂ) (a : ι → σ) {φ : QBasis ι σ W' → ℂ}
    {ψ t : QBasis ι σ W → ℂ} {ξ : D → ℂ} (c : ℂ) (h₁ : B₁ *ᵥ φ = splitVec e ψ ξ) :
    qNorm ((((QRoutine.ofUnitary B₁ hB₁).comp (R.kronLift e)).comp
        (QRoutine.ofUnitary B₂ hB₂)).run a *ᵥ φ - c • (B₂ *ᵥ splitVec e t ξ))
      = qNorm (R.run a *ᵥ ψ - c • t) * qNorm ξ := by
  have hrun : (((QRoutine.ofUnitary B₁ hB₁).comp (R.kronLift e)).comp
        (QRoutine.ofUnitary B₂ hB₂)).run a *ᵥ φ
      = B₂ *ᵥ ((R.kronLift e).run a *ᵥ splitVec e ψ ξ) := by
    rw [QRoutine.comp_run, QRoutine.comp_run, QRoutine.ofUnitary_run, QRoutine.ofUnitary_run,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h₁]
  rw [hrun, ← Matrix.mulVec_smul, ← Matrix.mulVec_sub, qNorm_mulVec hB₂,
    QRoutine.run_close_kronLift he]

end QuantumQueryComplexity
