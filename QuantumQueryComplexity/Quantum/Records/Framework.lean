import QuantumQueryComplexity.Quantum.Records.Knowledge
import QuantumQueryComplexity.Quantum.Transfer.Endpoint

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The lower-bound framework

[Bel26, Lemma 3.18]. Run the algorithm on a product reference distribution `ρ` and transfer the
final joint state to the hidden problem `ν`: by Proposition 3.6 (`xferOp_mul_jointXorState`),
`Ψ^ν_T = ΥΨ_T = Υ⁺Ψ_T + Υ⁻Ψ_T`. After `T` queries `Ψ_T` has at most `T` records
(`recLe_mul_jointXorState`), so `Υ⁻Ψ_T` has every column in the range of `Υ⁻ ∘ (⊕_{|S| ≤ T} P_S)`.
If that subspace is `γ`-anti-concentrated and the knowledge is `‖Υ⁺Ψ_T‖ ≤ δ`, the success
probability `σ` satisfies

    √σ ≤ γ + δ    (`sqrt_avgXorSuccessProb_le_of_knowledge`).

The proof rescales `Υ⁻Ψ_T` to the multiple closest to `Ψ^ν_T`, which has norm at most `1`, as in
[Bel26, Lemma 3.12], and applies the library's anti-concentration endpoint
(`sqrt_avgXorSuccessProb_le_of_stronglyAntiConc`). The transfer operator need not be an isometry.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Ω M : Type} [Fintype Ω] [DecidableEq Ω]

namespace FinDist

/-- Some multiple of `g` is no longer than `Φ` and at least as close to `Φ` as `g` is: the
orthogonal projection of `Φ` onto the line through `g`. -/
private lemma exists_smul_norm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (Φ g : E) :
    ∃ c : ℂ, ‖c • g‖ ≤ ‖Φ‖ ∧ ‖Φ - c • g‖ ≤ ‖Φ - g‖ := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((ℂ ∙ g).starProjection_apply_mem Φ)
  refine ⟨c, hc ▸ (ℂ ∙ g).norm_starProjection_apply_le Φ, ?_⟩
  rw [hc, Submodule.starProjection_minimal]
  refine ciInf_le ?_ (⟨g, Submodule.mem_span_singleton_self g⟩ : ℂ ∙ g)
  exact ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩

/-- The norm of a joint vector is the Euclidean norm of its flattening. -/
private lemma jNorm_eq_norm {X B : Type} [Fintype X] [Fintype B] (f : JVec X B) :
    jNorm f = ‖(WithLp.toLp 2 (fun p : X × B => f p.1 p.2) : EuclideanSpace ℂ (X × B))‖ := by
  classical
  rw [jNorm, ← Real.sqrt_sq (norm_nonneg _), ← qNormSq_eq_euclidean]
  simp only [jNormSq, qNormSq_def, Fintype.sum_prod_type]

/-- Some multiple of `g` is no longer than `Φ` and at least as close to `Φ` as `g` is. -/
private lemma exists_smul_jNorm_le {X B : Type} [Fintype X] [Fintype B] (Φ g : JVec X B) :
    ∃ c : ℂ, jNorm (c • g) ≤ jNorm Φ ∧ jNorm (Φ - c • g) ≤ jNorm (Φ - g) := by
  obtain ⟨c, h1, h2⟩ := exists_smul_norm_le
    (WithLp.toLp 2 (fun p : X × B => Φ p.1 p.2) : EuclideanSpace ℂ (X × B))
    (WithLp.toLp 2 (fun p : X × B => g p.1 p.2))
  refine ⟨c, ?_, ?_⟩
  · rw [jNorm_eq_norm, jNorm_eq_norm]
    exact h1
  · rw [jNorm_eq_norm, jNorm_eq_norm]
    exact h2

/-- **The lower-bound framework** [Bel26, Lemma 3.18], XOR model: if the transferred
no-knowledge part of the records of size at most `T` is `γ`-anti-concentrated (`0 ≤ γ`) and the
final knowledge is at most `δ`, then `√σ ≤ γ + δ`. -/
theorem sqrt_avgXorSuccessProb_le_of_knowledge {ρ : FinDist (ι → Bool)} (h : ρ.IsFullProduct)
    {ν : FinDist Ω} {read : Ω → ι → Bool} (type : Ω → M) (L : M → Set (Finset ι))
    {O W : Type} [Fintype W] [DecidableEq W] (Good : Ω → O → Prop)
    [∀ ω, DecidablePred (Good ω)] (A : QAlg ι Bool O W) (T : ℕ) {γ δ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : ν.IsAntiConc Good γ
      (LinearMap.range (Matrix.toLin' (knowOp ρ ν read type (fun μ => (L μ)ᶜ) * ρ.recLe T))))
    (hδ : jNorm (knowOp ρ ν read type L * ρ.jointXorState id A T) ≤ δ) :
    Real.sqrt (ν.avgXorSuccessProb A T read Good) ≤ γ + δ := by
  set Ψ := ρ.jointXorState id A T
  set Φ := ν.jointXorState read A T
  set Kp := knowOp ρ ν read type L
  set Km := knowOp ρ ν read type (fun μ => (L μ)ᶜ)
  have hΦ : Φ = Kp * Ψ + Km * Ψ := by
    rw [← Matrix.add_mul, knowOp_add_knowOp_compl h, xferOp_mul_jointXorState h]
  have hΦ1 : jNorm Φ = 1 := by rw [jNorm, jNormSq_jointXorState, Real.sqrt_one]
  obtain ⟨c, hc1, hc2⟩ := exists_smul_jNorm_le Φ (Km * Ψ)
  have hsac : ν.StronglyAntiConc Good γ (c • (Km * Ψ)) := by
    refine ⟨_, hγ, fun b => ?_⟩
    have hR : ρ.recLe T * Ψ = Ψ := recLe_mul_jointXorState h A T
    have hΨ : Km * Ψ = Km * ρ.recLe T * Ψ := by rw [Matrix.mul_assoc, hR]
    have hcol : (fun x => (c • (Km * Ψ)) x b)
        = c • Matrix.toLin' (Km * ρ.recLe T) (fun x => Ψ x b) := by
      rw [hΨ]
      funext x
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [hcol]
    exact Submodule.smul_mem _ c (LinearMap.mem_range_self _ _)
  have h3 : Φ - Km * Ψ = Kp * Ψ := by rw [hΦ]; abel
  calc Real.sqrt (ν.avgXorSuccessProb A T read Good)
      ≤ γ * jNorm (c • (Km * Ψ)) + jNorm (Φ - c • (Km * Ψ)) :=
        ν.sqrt_avgXorSuccessProb_le_of_stronglyAntiConc read Good A T hsac
    _ ≤ γ * 1 + δ := by
        gcongr
        · exact hc1.trans hΦ1.le
        · exact hc2.trans (h3 ▸ hδ)
    _ = γ + δ := by ring

end FinDist

end QuantumQueryComplexity
