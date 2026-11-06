import QuantumQueryComplexity.Quantum.Records.ZqRecords

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Fourier analysis on `Z_qⁿ` and the records of the uniform distribution

For the uniform reference distribution on `Z_qⁿ`, Belovs works in the basis of Fourier characters
`|σ̂⟩ = ∏ᵢ ω_q^{σᵢxᵢ}/√q` (`FinDist.fourierVec`) [Bel26, Section 3, (3.16)]. This module provides:

* orthogonality of the characters of `Z_q^κ` and Parseval's identity for character sums
  (`sum_prod_zqChar_mul_star`, `sum_normSq_sum_mul_prod_zqChar`);
* the Fourier coefficients `α_σ = ⟨σ̂|ϕ⟩` of a vector `ϕ` of the input register
  (`FinDist.fourierCoeff`), Fourier inversion `ϕ = ∑_σ α_σ |σ̂⟩`
  (`FinDist.eq_sum_fourierCoeff_smul`) and Parseval's identity `‖ϕ‖² = ∑_σ |α_σ|²`
  (`FinDist.qNormSq_eq_sum_fourierCoeff`);
* the record projections in the Fourier basis: the projection `Π_G` onto the records in `G` keeps
  the characters whose support `zsupp σ = {i | σᵢ ≠ 0}` lies in `G` and kills the others
  (`FinDist.recIn_mulVec_fourierVec`, [Bel26, (3.20)]); hence the value of a knowledge operator
  in the Fourier basis (`FinDist.knowOp_mulVec_apply`), and a vector with at most `t` records has
  no Fourier weight on supports of more than `t` elements
  (`FinDist.fourierCoeff_eq_zero_of_recLe`).
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {q : ℕ} [NeZero q]

/-! ## Characters of `Z_q^κ` -/

section Characters

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A product of characters at the same point is the character of the summed frequency. -/
theorem prod_zqChar_left {ι : Type*} (s : Finset ι) (f : ι → ZMod q) (x : ZMod q) :
    ∏ i ∈ s, zqChar (f i) x = zqChar (∑ i ∈ s, f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zqChar_add_left]

/-- **Orthogonality of the characters of `Z_q^κ`**:
`∑_z χ_τ(z) χ_τ'(z)^* = q^|κ| [τ = τ']`. -/
theorem sum_prod_zqChar_mul_star (τ τ' : κ → ZMod q) :
    ∑ z : κ → ZMod q, (∏ i, zqChar (τ i) (z i)) * star (∏ i, zqChar (τ' i) (z i))
      = if τ = τ' then (q : ℂ) ^ Fintype.card κ else 0 := by
  have h : ∀ z : κ → ZMod q, (∏ i, zqChar (τ i) (z i)) * star (∏ i, zqChar (τ' i) (z i))
      = ∏ i, zqChar (τ i - τ' i) (z i) := by
    intro z
    rw [star_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [star_zqChar, ← zqChar_add_left, sub_eq_add_neg]
  rw [Finset.sum_congr rfl fun z _ => h z,
    ← Fintype.prod_sum (f := fun i a => zqChar (τ i - τ' i) a)]
  simp_rw [sum_zqChar, sub_eq_zero]
  rw [Fintype.prod_ite_zero, Finset.prod_const, Finset.card_univ]
  simp [funext_iff]

/-- **Parseval's identity for character sums** on `Z_q^κ`:
`∑_z |∑_τ β_τ χ_τ(z)|² = q^|κ| ∑_τ |β_τ|²`. -/
theorem sum_normSq_sum_mul_prod_zqChar (β : (κ → ZMod q) → ℂ) :
    ∑ z : κ → ZMod q, Complex.normSq (∑ τ, β τ * ∏ i, zqChar (τ i) (z i))
      = (q : ℝ) ^ Fintype.card κ * ∑ τ, Complex.normSq (β τ) := by
  have key : ∀ τ τ' : κ → ZMod q, ∑ z : κ → ZMod q,
      (β τ * ∏ i, zqChar (τ i) (z i)) * star (β τ' * ∏ i, zqChar (τ' i) (z i))
        = if τ = τ' then (q : ℂ) ^ Fintype.card κ * (β τ * star (β τ)) else 0 := by
    intro τ τ'
    have hz : ∀ z : κ → ZMod q,
        (β τ * ∏ i, zqChar (τ i) (z i)) * star (β τ' * ∏ i, zqChar (τ' i) (z i))
          = (β τ * star (β τ'))
            * ((∏ i, zqChar (τ i) (z i)) * star (∏ i, zqChar (τ' i) (z i))) := by
      intro z
      rw [star_mul']
      ring
    rw [Finset.sum_congr rfl fun z _ => hz z, ← Finset.mul_sum, sum_prod_zqChar_mul_star]
    split_ifs with hττ
    · subst hττ
      ring
    · rw [mul_zero]
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast,
    ← Complex.mul_conj, starRingEnd_apply, star_sum, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun τ _ => Finset.sum_comm]
  simp only [key, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.mul_sum]

end Characters

/-- The support `{i | σᵢ ≠ 0}` of `σ ∈ Z_qⁿ`. -/
def zsupp {ι : Type*} [Fintype ι] (σ : ι → ZMod q) : Finset ι :=
  Finset.univ.filter fun i => σ i ≠ 0

namespace FinDist

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The Fourier basis of `Z_qⁿ` -/

/-- The character `|σ̂⟩` in product form: `∏ᵢ ω_q^{σᵢxᵢ} / √q^n`. -/
theorem fourierVec_eq (σ x : ι → ZMod q) :
    fourierVec σ x = (∏ i, zqChar (σ i) (x i)) / ((Real.sqrt q : ℝ) : ℂ) ^ Fintype.card ι := by
  rw [fourierVec, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]

/-- **Completeness of the characters**: `∑_σ ⟨σ̂|y⟩ ⟨x|σ̂⟩ = [x = y]`. -/
theorem sum_star_fourierVec_mul (x y : ι → ZMod q) :
    ∑ σ, star (fourierVec σ y) * fourierVec σ x = if x = y then 1 else 0 := by
  have hs : star (((Real.sqrt q : ℝ) : ℂ) ^ Fintype.card ι)
      * ((Real.sqrt q : ℝ) : ℂ) ^ Fintype.card ι = (q : ℂ) ^ Fintype.card ι := by
    rw [star_pow, Complex.star_def, Complex.conj_ofReal, ← mul_pow, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have hq : (q : ℂ) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne q))
  have h : ∀ σ : ι → ZMod q, star (fourierVec σ y) * fourierVec σ x
      = (∏ i, zqChar (x i) (σ i)) * star (∏ i, zqChar (y i) (σ i))
        / (q : ℂ) ^ Fintype.card ι := by
    intro σ
    rw [fourierVec_eq, fourierVec_eq, star_div₀, ← hs]
    simp only [zqChar_comm (σ _)]
    ring
  rw [Finset.sum_congr rfl fun σ _ => h σ, ← Finset.sum_div, sum_prod_zqChar_mul_star]
  split_ifs
  · exact div_self hq
  · exact zero_div _

/-- **The Fourier coefficient** `α_σ = ⟨σ̂|ϕ⟩` of a vector `ϕ` of the input register, for the
uniform distribution on `Z_qⁿ` [Bel26, (3.16)]. -/
noncomputable def fourierCoeff (ϕ : (uniform (ι → ZMod q)).Supp → ℂ) (σ : ι → ZMod q) : ℂ :=
  ∑ x : (uniform (ι → ZMod q)).Supp, star (fourierVec σ x.1) * ϕ x

/-- `fourierCoeff ϕ σ` is the dot product `⟨σ̂|ϕ⟩`. -/
theorem fourierCoeff_eq_dotProduct (ϕ : (uniform (ι → ZMod q)).Supp → ℂ) (σ : ι → ZMod q) :
    fourierCoeff ϕ σ = star (fun x : (uniform (ι → ZMod q)).Supp => fourierVec σ x.1) ⬝ᵥ ϕ :=
  rfl

/-- **Fourier inversion** on `Z_qⁿ`: `ϕ(x) = ∑_σ α_σ ⟨x|σ̂⟩`. -/
theorem sum_fourierCoeff_mul_fourierVec (ϕ : (uniform (ι → ZMod q)).Supp → ℂ)
    (x : (uniform (ι → ZMod q)).Supp) :
    ∑ σ, fourierCoeff ϕ σ * fourierVec σ x.1 = ϕ x := by
  have hy : ∀ y : (uniform (ι → ZMod q)).Supp,
      ∑ σ, star (fourierVec σ y.1) * ϕ y * fourierVec σ x.1 = if x = y then ϕ y else 0 := by
    intro y
    have h1 : ∑ σ, star (fourierVec σ y.1) * ϕ y * fourierVec σ x.1
        = ϕ y * ∑ σ, star (fourierVec σ y.1) * fourierVec σ x.1 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by ring
    rw [h1, sum_star_fourierVec_mul]
    by_cases hxy : x = y
    · subst hxy
      simp
    · have hxy' : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
      simp [hxy, hxy']
  simp only [fourierCoeff, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun y _ => hy y]
  simp

/-- **Fourier inversion** as an identity of vectors: `ϕ = ∑_σ α_σ |σ̂⟩`. -/
theorem eq_sum_fourierCoeff_smul (ϕ : (uniform (ι → ZMod q)).Supp → ℂ) :
    ϕ = ∑ σ, fourierCoeff ϕ σ • (fun y : (uniform (ι → ZMod q)).Supp => fourierVec σ y.1) := by
  funext y
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact (sum_fourierCoeff_mul_fourierVec ϕ y).symm

/-- **Parseval's identity** on `Z_qⁿ`: `‖ϕ‖² = ∑_σ |α_σ|²`. -/
theorem qNormSq_eq_sum_fourierCoeff (ϕ : (uniform (ι → ZMod q)).Supp → ℂ) :
    qNormSq ϕ = ∑ σ, Complex.normSq (fourierCoeff ϕ σ) := by
  have hq : (q : ℝ) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne q))
  have h : ∀ x : (uniform (ι → ZMod q)).Supp, Complex.normSq (ϕ x)
      = Complex.normSq (∑ σ, fourierCoeff ϕ σ * ∏ i, zqChar (σ i) (x.1 i))
        / (q : ℝ) ^ Fintype.card ι := by
    intro x
    have hx : ϕ x = (∑ σ, fourierCoeff ϕ σ * ∏ i, zqChar (σ i) (x.1 i))
        / ((Real.sqrt q : ℝ) : ℂ) ^ Fintype.card ι := by
      rw [← sum_fourierCoeff_mul_fourierVec ϕ x, Finset.sum_div]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [fourierVec_eq, mul_div_assoc]
    rw [hx, Complex.normSq_div, map_pow, Complex.normSq_ofReal,
      Real.mul_self_sqrt (Nat.cast_nonneg _)]
  rw [qNormSq_def, Finset.sum_congr rfl fun x _ => h x, ← Finset.sum_div,
    sum_supp_uniform_zq (fun x => Complex.normSq (∑ σ, fourierCoeff ϕ σ * ∏ i, zqChar (σ i) (x i))),
    sum_normSq_sum_mul_prod_zqChar, mul_div_cancel_left₀ _ hq]

/-! ## Records in the Fourier basis -/

/-- The projection onto at most `t` records kills the characters with more than `t` records. -/
theorem recLe_mulVec_fourierVec {t : ℕ} {σ : ι → ZMod q} (hσ : t < (zsupp σ).card) :
    (uniform (ι → ZMod q)).recLe t
        *ᵥ (fun x : (uniform (ι → ZMod q)).Supp => fourierVec σ x.1) = 0 := by
  rw [recLe, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun S hS => ?_
  rw [recProj_uniform_mulVec_fourier]
  have hne : ¬ (Finset.univ.filter fun i => σ i ≠ 0) = S := by
    rintro rfl
    exact absurd (Finset.mem_filter.mp hS).2 (not_le.mpr hσ)
  rw [ite_eq_right hne]

/-- A vector with at most `t` records has no Fourier weight on supports of more than `t`
elements. -/
theorem fourierCoeff_eq_zero_of_recLe {t : ℕ} {ϕ : (uniform (ι → ZMod q)).Supp → ℂ}
    (hϕ : (uniform (ι → ZMod q)).recLe t *ᵥ ϕ = ϕ) {σ : ι → ZMod q} (hσ : t < (zsupp σ).card) :
    fourierCoeff ϕ σ = 0 := by
  rw [fourierCoeff_eq_dotProduct, ← hϕ, Matrix.dotProduct_mulVec,
    ← (recLe_isHermitian (ρ := uniform (ι → ZMod q)) t).eq, ← Matrix.star_mulVec,
    recLe_mulVec_fourierVec hσ, star_zero, zero_dotProduct]

/-- The projection onto the records in `G` keeps the characters whose support lies in `G` and
kills the others [Bel26, (3.20)]. -/
theorem recIn_mulVec_fourierVec (G : Set (Finset ι)) [DecidablePred (· ∈ G)]
    (σ : ι → ZMod q) :
    (uniform (ι → ZMod q)).recIn G *ᵥ (fun x : (uniform (ι → ZMod q)).Supp => fourierVec σ x.1)
      = if zsupp σ ∈ G then (fun x : (uniform (ι → ZMod q)).Supp => fourierVec σ x.1)
        else 0 := by
  rw [recIn, Matrix.sum_mulVec]
  simp_rw [recProj_uniform_mulVec_fourier]
  rw [Finset.sum_ite_eq]
  by_cases h : zsupp σ ∈ G
  · rw [ite_eq_left h]
    exact ite_eq_left (by simpa [zsupp] using h)
  · rw [ite_eq_right h]
    exact ite_eq_right (by simpa [zsupp] using h)

/-- **The projection onto the records in `G`** in the Fourier basis:
`Π_G ϕ = ∑_{σ : supp σ ∈ G} α_σ |σ̂⟩` [Bel26, (3.20)]. -/
theorem recIn_mulVec_apply (G : Set (Finset ι)) [DecidablePred (· ∈ G)]
    (ϕ : (uniform (ι → ZMod q)).Supp → ℂ) (x : (uniform (ι → ZMod q)).Supp) :
    ((uniform (ι → ZMod q)).recIn G *ᵥ ϕ) x
      = ∑ σ, if zsupp σ ∈ G then fourierCoeff ϕ σ * fourierVec σ x.1 else 0 := by
  conv_lhs => rw [eq_sum_fourierCoeff_smul ϕ]
  rw [Matrix.mulVec_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Matrix.mulVec_smul, recIn_mulVec_fourierVec]
  by_cases h : zsupp σ ∈ G <;> simp [h]

/-- **The value of a knowledge operator** in the Fourier basis [Bel26, Proposition 4.5]: row `ω`
of `Υ^L ϕ` is `√(ν(ω)/ρ(x)) ∑_{σ : supp σ ∈ L(type ω)} α_σ ⟨x|σ̂⟩` at `x = read ω`. -/
theorem knowOp_mulVec_apply {Ω M : Type} [Fintype Ω] [DecidableEq Ω] (ν : FinDist Ω)
    (read : Ω → ι → ZMod q) (type : Ω → M) (L : M → Set (Finset ι))
    (ϕ : (uniform (ι → ZMod q)).Supp → ℂ) (ω : ν.Supp) [DecidablePred (· ∈ L (type ω))] :
    (knowOp (uniform (ι → ZMod q)) ν read type L *ᵥ ϕ) ω
      = ((Real.sqrt (ν.mass ω / (uniform (ι → ZMod q)).mass (read ω)) : ℝ) : ℂ)
        * ∑ σ, if zsupp σ ∈ L (type ω) then fourierCoeff ϕ σ * fourierVec σ (read ω)
          else 0 := by
  change ((xferOp (uniform (ι → ZMod q)) ν read * (uniform (ι → ZMod q)).recIn (L (type ω)))
    *ᵥ ϕ) ω = _
  rw [← Matrix.mulVec_mulVec]
  change ∑ x, xferOp (uniform (ι → ZMod q)) ν read ω x
    * ((uniform (ι → ZMod q)).recIn (L (type ω)) *ᵥ ϕ) x = _
  rw [xferOp_sum_mul isFullProduct_uniform, recIn_mulVec_apply]

end FinDist

end QuantumQueryComplexity
