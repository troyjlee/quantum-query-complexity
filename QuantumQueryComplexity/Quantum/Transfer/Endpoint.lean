import QuantumQueryComplexity.Quantum.Transfer.Lemma
import QuantumQueryComplexity.Quantum.JointState.Success

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Endpoint lemmas

The average relational success of an algorithm is `σ = ‖ΠΦ‖²`, where `Φ` is its final joint
state and `Π` masks each input's row to the basis states whose readout is valid for that input
(`FinDist.goodMask`).  For any comparison vector `g`, typically `g = KΨ⁻` for a run `Ψ⁻` on
another input register,

  `√σ ≤ ‖Πg‖ + ‖Φ − g‖`   (`FinDist.jNorm_goodMask_le_add`).

The first term is bounded in one of two ways:

* **Exact verification** [CGZ, proof of Theorem 4.1].  When validity does not depend on the
  input, `Π` acts on the workspace only (`wsMask`) and commutes with every input-register map.
  If the computation never accepts on the negative distribution, then `ΠKΨ⁻ = KΠΨ⁻ = 0`
  (`FinDist.goodMask_const_mul_eq_zero`).
* **Strong anti-concentration** [Bel26, Definitions 3.8–3.9, Proposition 3.11, Lemma 3.12].
  If every column of `g` lies in a subspace `H` of the input register on which no output is
  valid for more than a `γ` fraction of the norm, then `‖Πg‖ ≤ γ ‖g‖`
  (`FinDist.jNorm_goodMask_le_of_stronglyAntiConc`).

## Main definitions

* `wsMask P` — the projector onto the workspace basis states satisfying `P`.
* `FinDist.IsAntiConc`, `FinDist.StronglyAntiConc` — Belovs's anti-concentration notions.

## Main results

* `FinDist.jNorm_goodMask_le_add`, `FinDist.sqrt_avgXorSuccessProb_le`,
  `FinDist.sqrt_avgSuccessProb_le` — **the endpoint lemma**.
* `FinDist.goodMask_const_mul_eq_zero`, `FinDist.wsMask_jointXorState_eq_zero` — exact
  verification.
* `FinDist.jNorm_goodMask_le_of_stronglyAntiConc`,
  `FinDist.sqrt_avgXorSuccessProb_le_of_stronglyAntiConc` — anti-concentration.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {Ω O B X Y : Type} [Fintype Ω] [DecidableEq Ω] [Fintype B] [DecidableEq B]
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-! ## Workspace masks -/

/-- **A workspace mask**: the projector onto the workspace basis states satisfying `P`, acting
as the identity on the input register. -/
def wsMask (P : B → Prop) [DecidablePred P] (f : JVec X B) : JVec X B :=
  fun x b => if P b then f x b else 0

/-- Workspace masks commute with input-register operators. -/
theorem mul_wsMask (K : Matrix Y X ℂ) (P : B → Prop) [DecidablePred P] (f : JVec X B) :
    K * wsMask P f = wsMask P (K * f) := by
  funext y b
  simp only [wsMask, Matrix.mul_apply]
  split_ifs <;> simp

namespace FinDist

variable (ρ : FinDist Ω)

/-! ## The endpoint lemma -/

lemma goodMask_sub (rd : B → O) (Good : Ω → O → Prop) [∀ ω, DecidablePred (Good ω)]
    (f g : JVec ρ.Supp B) :
    ρ.goodMask rd Good (f - g) = ρ.goodMask rd Good f - ρ.goodMask rd Good g := by
  funext x b
  simp only [goodMask, Matrix.sub_apply]
  split_ifs <;> simp

/-- `Π` is a projector, so it does not increase the norm. -/
theorem jNorm_goodMask_le (rd : B → O) (Good : Ω → O → Prop) [∀ ω, DecidablePred (Good ω)]
    (f : JVec ρ.Supp B) : jNorm (ρ.goodMask rd Good f) ≤ jNorm f := by
  refine Real.sqrt_le_sqrt ?_
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun b _ => ?_
  simp only [goodMask]
  split_ifs
  · exact le_rfl
  · simpa using Complex.normSq_nonneg (f x b)

/-- **The endpoint lemma**: `‖ΠΦ‖ ≤ ‖Πg‖ + ‖Φ − g‖` for every comparison vector `g`. -/
theorem jNorm_goodMask_le_add (rd : B → O) (Good : Ω → O → Prop)
    [∀ ω, DecidablePred (Good ω)] (Φ g : JVec ρ.Supp B) :
    jNorm (ρ.goodMask rd Good Φ) ≤ jNorm (ρ.goodMask rd Good g) + jNorm (Φ - g) := by
  have h : ρ.goodMask rd Good Φ = ρ.goodMask rd Good g + ρ.goodMask rd Good (Φ - g) := by
    rw [goodMask_sub]; abel
  rw [h]
  exact (jNorm_add_le _ _).trans (add_le_add le_rfl (ρ.jNorm_goodMask_le rd Good _))

section Algorithm

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype W]
  [DecidableEq W]

/-- **The endpoint lemma for an algorithm** (XOR model): `√σ ≤ ‖Πg‖ + ‖Ψ_T − g‖`. -/
theorem sqrt_avgXorSuccessProb_le (read : Ω → ι → Bool) (Good : Ω → O → Prop)
    [∀ ω, DecidablePred (Good ω)] (A : QAlg ι Bool O W) (T : ℕ)
    (g : JVec ρ.Supp (QBasis ι Bool W)) :
    Real.sqrt (ρ.avgXorSuccessProb A T read Good)
      ≤ jNorm (ρ.goodMask A.readout Good g) + jNorm (ρ.jointXorState read A T - g) := by
  rw [avgXorSuccessProb_eq_jNormSq_goodMask]
  exact ρ.jNorm_goodMask_le_add A.readout Good _ g

/-- **The endpoint lemma for an algorithm** (value oracle): `√σ ≤ ‖Πg‖ + ‖Ψ_T − g‖`. -/
theorem sqrt_avgSuccessProb_le (read : Ω → ι → σ) (Good : Ω → O → Prop)
    [∀ ω, DecidablePred (Good ω)] (A : QAlg ι σ O W) (T : ℕ)
    (g : JVec ρ.Supp (QBasis ι σ W)) :
    Real.sqrt (ρ.avgSuccessProb A T read Good)
      ≤ jNorm (ρ.goodMask A.readout Good g) + jNorm (ρ.jointState read A T - g) := by
  rw [avgSuccessProb_eq_jNormSq_goodMask]
  exact ρ.jNorm_goodMask_le_add A.readout Good _ g

end Algorithm

/-! ## Exact verification -/

/-- An input-independent relation masks the workspace only. -/
theorem goodMask_const (rd : B → O) (acc : O → Prop) [DecidablePred acc] (f : JVec ρ.Supp B) :
    ρ.goodMask rd (fun _ => acc) f = wsMask (fun b => acc (rd b)) f := rfl

/-- **Exact verification kills the comparison term**: if the acceptance mask annihilates `Ψ`,
it annihilates `KΨ` for every input-register map `K`. -/
theorem goodMask_const_mul_eq_zero (rd : B → O) (acc : O → Prop) [DecidablePred acc]
    (K : Matrix ρ.Supp X ℂ) (Ψ : JVec X B) (h : wsMask (fun b => acc (rd b)) Ψ = 0) :
    ρ.goodMask rd (fun _ => acc) (K * Ψ) = 0 := by
  rw [goodMask_const, ← mul_wsMask, h, Matrix.mul_zero]

/-- An algorithm that never accepts on the support of `ρ` has acceptance-masked joint state
zero. -/
theorem wsMask_jointXorState_eq_zero {ι W : Type} [Fintype ι] [DecidableEq ι] [Fintype W]
    [DecidableEq W] (read : Ω → ι → Bool) (A : QAlg ι Bool O W) (T : ℕ) (acc : O → Prop)
    [DecidablePred acc] (h : ∀ x : ρ.Supp, xorSuccessProbOn A T read (fun _ => acc) x = 0) :
    wsMask (fun b => acc (A.readout b)) (ρ.jointXorState read A T) = 0 := by
  funext x b
  simp only [wsMask, Matrix.zero_apply]
  split_ifs with hb
  · have hx := h x
    rw [xorSuccessProbOn, goodProb_eq_sum_ite] at hx
    have hb0 := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => by
      split_ifs <;> simp [Complex.normSq_nonneg])).mp hx b (Finset.mem_univ _)
    simp only [hb, ite_true, Complex.normSq_eq_zero] at hb0
    simp [jointXorState, ofWvec, hb0]
  · rfl

/-! ## Anti-concentration -/

/-- `‖f‖²` as a sum of the squared norms of the columns of `f`. -/
private lemma jNormSq_eq_sum_col {Z : Type} [Fintype Z] (f : JVec Z B) :
    jNormSq f = ∑ b, qNormSq (fun x => f x b) := by
  unfold jNormSq qNormSq
  exact Finset.sum_comm

/-- **Anti-concentration** [Bel26, Definition 3.8]: the subspace `H` of the input register is
`γ`-anti-concentrated for the relation `Good` if, for every `φ ∈ H` and every output `r`, the
part of `φ` on the inputs for which `r` is valid has norm at most `γ ‖φ‖`. -/
def IsAntiConc (Good : Ω → O → Prop) [∀ ω, DecidablePred (Good ω)] (γ : ℝ)
    (H : Submodule ℂ (ρ.Supp → ℂ)) : Prop :=
  ∀ φ ∈ H, ∀ r : O,
    Real.sqrt (qNormSq fun x : ρ.Supp => if Good x r then φ x else 0)
      ≤ γ * Real.sqrt (qNormSq φ)

/-- **Strong anti-concentration** [Bel26, Definition 3.9]: `g ∈ H ⊗ A` for a
`γ`-anti-concentrated subspace `H`, that is, every column of `g` lies in `H`. -/
def StronglyAntiConc (Good : Ω → O → Prop) [∀ ω, DecidablePred (Good ω)] (γ : ℝ)
    (g : JVec ρ.Supp B) : Prop :=
  ∃ H : Submodule ℂ (ρ.Supp → ℂ), ρ.IsAntiConc Good γ H ∧ ∀ b, (fun x => g x b) ∈ H

/-- **A strongly anti-concentrated vector has small success** [Bel26, Proposition 3.11]:
`‖Πg‖ ≤ γ ‖g‖` for every readout. -/
theorem jNorm_goodMask_le_of_stronglyAntiConc (rd : B → O) (Good : Ω → O → Prop)
    [∀ ω, DecidablePred (Good ω)] {γ : ℝ} {g : JVec ρ.Supp B}
    (hg : ρ.StronglyAntiConc Good γ g) : jNorm (ρ.goodMask rd Good g) ≤ γ * jNorm g := by
  obtain ⟨H, hH, hcol⟩ := hg
  have hb : ∀ b, Real.sqrt (qNormSq fun x => ρ.goodMask rd Good g x b)
      ≤ γ * Real.sqrt (qNormSq fun x => g x b) := fun b => hH _ (hcol b) (rd b)
  rcases le_or_gt 0 γ with hγ | hγ
  · have key : jNormSq (ρ.goodMask rd Good g) ≤ γ ^ 2 * jNormSq g := by
      rw [jNormSq_eq_sum_col, jNormSq_eq_sum_col, Finset.mul_sum]
      refine Finset.sum_le_sum fun b _ => ?_
      have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hb b) 2
      rwa [mul_pow, Real.sq_sqrt (qNormSq_nonneg _), Real.sq_sqrt (qNormSq_nonneg _)] at h2
    rw [jNorm, jNorm, ← Real.sqrt_sq hγ, ← Real.sqrt_mul (sq_nonneg γ)]
    exact Real.sqrt_le_sqrt key
  · have hcol0 : ∀ b, qNormSq (fun x => g x b) = 0 := fun b => by
      have h1 := (Real.sqrt_nonneg _).trans (hb b)
      have h2 : Real.sqrt (qNormSq fun x => g x b) ≤ 0 := by
        nlinarith [Real.sqrt_nonneg (qNormSq fun x => g x b)]
      exact (Real.sqrt_eq_zero (qNormSq_nonneg _)).mp (le_antisymm h2 (Real.sqrt_nonneg _))
    have hg0 : jNorm g = 0 := by
      rw [jNorm, jNormSq_eq_sum_col, Finset.sum_eq_zero fun b _ => hcol0 b, Real.sqrt_zero]
    rw [hg0, mul_zero]
    exact (ρ.jNorm_goodMask_le rd Good g).trans hg0.le

/-- **The anti-concentration endpoint** [Bel26, Lemma 3.12]: if the final state is within
`‖Ψ_T − g‖` of a strongly `γ`-anti-concentrated `g`, then `√σ ≤ γ ‖g‖ + ‖Ψ_T − g‖`. -/
theorem sqrt_avgXorSuccessProb_le_of_stronglyAntiConc {ι W : Type} [Fintype ι] [DecidableEq ι]
    [Fintype W] [DecidableEq W] (read : Ω → ι → Bool) (Good : Ω → O → Prop)
    [∀ ω, DecidablePred (Good ω)] (A : QAlg ι Bool O W) (T : ℕ) {γ : ℝ}
    {g : JVec ρ.Supp (QBasis ι Bool W)} (hg : ρ.StronglyAntiConc Good γ g) :
    Real.sqrt (ρ.avgXorSuccessProb A T read Good)
      ≤ γ * jNorm g + jNorm (ρ.jointXorState read A T - g) :=
  (ρ.sqrt_avgXorSuccessProb_le read Good A T g).trans
    (add_le_add (ρ.jNorm_goodMask_le_of_stronglyAntiConc A.readout Good hg) le_rfl)

end FinDist

end QuantumQueryComplexity
