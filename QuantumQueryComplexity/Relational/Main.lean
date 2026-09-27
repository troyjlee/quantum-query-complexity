import QuantumQueryComplexity.Relational.Tensor
import QuantumQueryComplexity.Composition.Main
set_option linter.style.header false

/-!
# The relational composition theorem (BL Theorem 22)

**Main result** (`relAdvPM_mul_le_relAdvPM_composeRel`): for a total relation
with indicator family `χ : κ → (α → Bool) → Bool` and a Boolean function
`g : (β → Bool) → Bool`,

  `ADV±_rel(χ) * ADV±(g) ≤ ADV±_rel(χ ∘ gᵏ)`

— the lower-bound direction of Belovs–Lee (arXiv:2004.06439, Theorem 22).

Proof: for a feasible pair `(Γf, v)` of the relational program and a feasible
`Γg` of the functional program, the composed matrix
`Γh = compose (constFam g) Γf (fun _ => Γg)` is a relational adversary matrix for the
composed relation (`isRelAdvMatrix_compose`), its `advD`-masked norms are at
most `‖Γg‖^(k-1)` (mask identity + Lemma 16 `≤`), and the normalized tensor
vector `(√2)^k • tensorVec g (fun _ => z) (D *ᵥ v)` — built from a maximal
eigenvector `z` of `Γg` and the `±1`-diagonal `D` — is a unit vector whose
Rayleigh quotient is `‖Γg‖^k * (v ⬝ᵥ Γf *ᵥ v)` (general tensor identity,
half-mass property, vertex identity).  The un-normalized relational witness
lemma then yields `ADV±_rel(χ ∘ gᵏ) ≥ (v ⬝ᵥ Γf *ᵥ v) * ‖Γg‖`, and two
supremum passes finish the proof.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {α β κ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The composed relation `χ ∘ gᵏ`. -/
def composeRel (χ : κ → (α → Bool) → Bool) (g : (β → Bool) → Bool) :
    κ → ((α × β) → Bool) → Bool :=
  fun a x => χ a (tilde (constFam g) x)

/-- **The relational composition theorem** (BL Theorem 22, `≥` direction):
`ADV±_rel(χ) * ADV±(g) ≤ ADV±_rel(χ ∘ gᵏ)` for a total relation `χ`. -/
theorem relAdvPM_mul_le_relAdvPM_composeRel
    (χ : κ → (α → Bool) → Bool) (g : (β → Bool) → Bool)
    (htot : ∀ x, ∃ a, χ a x) :
    relAdvPM χ * advPM g ≤ relAdvPM (composeRel χ g) := by
  classical
  have htot' : ∀ x : (α × β) → Bool, ∃ a, composeRel χ g a x :=
    fun x => htot (tilde (constFam g) x)
  have hkey : ∀ (Γf : Matrix (α → Bool) (α → Bool) ℝ) (v : (α → Bool) → ℝ),
      IsRelAdvMatrix χ Γf → (∀ i, ‖Γf ⊙ advD i‖ ≤ 1) → v ⬝ᵥ v = 1 →
      ∀ Γg : Matrix (β → Bool) (β → Bool) ℝ, IsAdvMatrix g Γg →
      (∀ j, ‖Γg ⊙ advD j‖ ≤ 1) →
      (v ⬝ᵥ Γf *ᵥ v) * ‖Γg‖ ≤ relAdvPM (composeRel χ g) := by
    intro Γf v hf1 hf2 hv Γg hg1 hg2
    rcases le_or_gt (v ⬝ᵥ Γf *ᵥ v) 0 with hr0 | hrpos
    · have h1 : (v ⬝ᵥ Γf *ᵥ v) * ‖Γg‖ ≤ 0 := by
        simpa using mul_le_mul_of_nonneg_right hr0 (norm_nonneg Γg)
      exact h1.trans (relAdvPM_nonneg htot')
    rcases eq_or_lt_of_le (norm_nonneg Γg) with hg0 | hgpos
    · rw [← hg0, mul_zero]
      exact relAdvPM_nonneg htot'
    -- a positive Rayleigh quotient forces α to be inhabited
    have hα : Nonempty α := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      have hray : v ⬝ᵥ Γf *ᵥ v ≤ 0 := by
        rw [dotProduct_mulVec_eq_sum]
        refine Finset.sum_nonpos fun x _ => Finset.sum_nonpos fun y _ => ?_
        have hxy : x = y := funext fun i => (hne.false i).elim
        subst hxy
        obtain ⟨a, ha⟩ := htot x
        have hd := hf1.diag_nonpos ha
        nlinarith [mul_self_nonneg (v x)]
      linarith
    haveI := hα
    have hk : Fintype.card α - 1 + 1 = Fintype.card α :=
      Nat.succ_pred_eq_of_pos Fintype.card_pos
    -- maximal eigen-data of Γg
    obtain ⟨d₀, hd₀⟩ := exists_abs_eigenvalues_eq_norm hg1.isHermitian
    set lam0 : ℝ := hg1.isHermitian.eigenvalues d₀ with hlam0def
    set z : (β → Bool) → ℝ :=
      WithLp.ofLp (hg1.isHermitian.eigenvectorBasis d₀) with hzdef
    have hz : Γg *ᵥ z = lam0 • z := hg1.isHermitian.mulVec_eigenvectorBasis d₀
    have hlam0 : lam0 ≠ 0 := by
      intro h
      rw [h, abs_zero] at hd₀
      exact hgpos.ne' hd₀.symm
    have hzunit : z ⬝ᵥ z = 1 := by
      have h := orthonormal_iff_ite.mp
        (hg1.isHermitian.eigenvectorBasis.orthonormal) d₀ d₀
      rw [if_pos rfl] at h
      have hb : hg1.isHermitian.eigenvectorBasis d₀ = WithLp.toLp 2 z := rfl
      rw [hb, inner_toLp] at h
      exact h
    have hmass : ∀ bb : Bool,
        (∑ u, if g u = bb then z u * z u else 0) = 1 / 2 := by
      intro bb
      rw [sum_ite_sq_eq_brestrict]
      exact brestrict_mass_eq_half hg1.isHermitian
        (fun u w huw => hg1.2 u w huw) hz hlam0 hzunit bb
    -- sign data
    set ε : α → ℝ := fun _ => lam0 / ‖Γg‖ with hεdef
    have hε : ∀ i, ε i * ε i = 1 := fun _ => div_self_sq hgpos hd₀
    have hlam_eq : (fun i : α => ε i * ‖Γg‖) = fun _ : α => lam0 :=
      funext fun _ => div_mul_cancel₀ _ hgpos.ne'
    -- inner products of tensor vectors
    have hTdot : ∀ w₁ w₂ : (α → Bool) → ℝ,
        tensorVec (constFam g) (fun _ : α => z) w₁ ⬝ᵥ tensorVec (constFam g) (fun _ : α => z) w₂
          = (1 / 2 : ℝ) ^ Fintype.card α * (w₁ ⬝ᵥ w₂) := by
      intro w₁ w₂
      rw [tensorVec_dotProduct]
      have hprod : ∀ b : α → Bool,
          (∏ i, ∑ u, if g u = b i then z u * z u else 0)
            = (1 / 2 : ℝ) ^ Fintype.card α := by
        intro b
        rw [Finset.prod_congr rfl fun i _ => hmass (b i), Finset.prod_const,
          Finset.card_univ]
      rw [Finset.sum_congr rfl fun b _ => by rw [hprod b]]
      rw [show ∑ b, w₁ b * w₂ b * (1 / 2 : ℝ) ^ Fintype.card α
          = (∑ b, w₁ b * w₂ b) * (1 / 2 : ℝ) ^ Fintype.card α
        from (Finset.sum_mul _ _ _).symm]
      rw [mul_comm]
      rfl
    -- the vertex form of the outer auxiliary matrix
    have hED : Γf ⊙ Emat (fun _ : α => ‖Γg‖) (fun _ : α => lam0)
        = (∏ _i : α, ‖Γg‖) •
          (Matrix.diagonal (chiSign ε) * Γf * Matrix.diagonal (chiSign ε)) := by
      rw [← hlam_eq]
      exact hadamard_Emat_vertex Γf hε
    have hDGD : (Matrix.diagonal (chiSign ε) * Γf * Matrix.diagonal (chiSign ε))
        *ᵥ (Matrix.diagonal (chiSign ε) *ᵥ v)
        = Matrix.diagonal (chiSign ε) *ᵥ (Γf *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, mul_assoc (Matrix.diagonal (chiSign ε) * Γf),
        diagonal_chiSign_mul_self hε, mul_one, ← Matrix.mulVec_mulVec]
    -- the Rayleigh quotient of the tensor witness
    have hray : tensorVec (constFam g) (fun _ : α => z) (Matrix.diagonal (chiSign ε) *ᵥ v)
        ⬝ᵥ (compose (constFam g) Γf (fun _ : α => Γg) *ᵥ
          tensorVec (constFam g) (fun _ : α => z) (Matrix.diagonal (chiSign ε) *ᵥ v))
        = (1 / 2 : ℝ) ^ Fintype.card α *
          (‖Γg‖ ^ Fintype.card α * (v ⬝ᵥ Γf *ᵥ v)) := by
      rw [compose_mulVec_tensorVec' (g := constFam g) (fun _ => hg1) (fun _ => hz), hTdot, hED,
        Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hDGD,
        diagonal_chiSign_mulVec_dotProduct hε, Finset.prod_const,
        Finset.card_univ]
    -- normalization
    set cc : ℝ := Real.sqrt 2 ^ Fintype.card α with hccdef
    have hcc2 : cc * cc = 2 ^ Fintype.card α := by
      rw [hccdef, ← mul_pow, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    have hVunit : (cc • tensorVec (constFam g) (fun _ : α => z)
          (Matrix.diagonal (chiSign ε) *ᵥ v)) ⬝ᵥ
        (cc • tensorVec (constFam g) (fun _ : α => z)
          (Matrix.diagonal (chiSign ε) *ᵥ v)) = 1 := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hTdot,
        diagonal_chiSign_mulVec_dotProduct hε, hv, mul_one]
      rw [show cc * (cc * (1 / 2 : ℝ) ^ Fintype.card α)
          = cc * cc * (1 / 2 : ℝ) ^ Fintype.card α from by ring, hcc2,
        ← mul_pow]
      norm_num
    have hVray : (cc • tensorVec (constFam g) (fun _ : α => z)
          (Matrix.diagonal (chiSign ε) *ᵥ v)) ⬝ᵥ
        (compose (constFam g) Γf (fun _ : α => Γg) *ᵥ
          (cc • tensorVec (constFam g) (fun _ : α => z)
            (Matrix.diagonal (chiSign ε) *ᵥ v)))
        = ‖Γg‖ ^ Fintype.card α * (v ⬝ᵥ Γf *ᵥ v) := by
      rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        smul_eq_mul, hray]
      calc cc * (cc * ((1 / 2 : ℝ) ^ Fintype.card α *
              (‖Γg‖ ^ Fintype.card α * (v ⬝ᵥ Γf *ᵥ v))))
          = cc * cc * (1 / 2 : ℝ) ^ Fintype.card α *
              (‖Γg‖ ^ Fintype.card α * (v ⬝ᵥ Γf *ᵥ v)) := by ring
        _ = (2 : ℝ) ^ Fintype.card α * (1 / 2 : ℝ) ^ Fintype.card α *
              (‖Γg‖ ^ Fintype.card α * (v ⬝ᵥ Γf *ᵥ v)) := by rw [hcc2]
        _ = ((2 : ℝ) * (1 / 2)) ^ Fintype.card α *
              (‖Γg‖ ^ Fintype.card α * (v ⬝ᵥ Γf *ᵥ v)) := by rw [mul_pow]
        _ = ‖Γg‖ ^ Fintype.card α * (v ⬝ᵥ Γf *ᵥ v) := by norm_num
    -- feasibility of the composed witness
    have hrel : IsRelAdvMatrix (composeRel χ g)
        (compose (constFam g) Γf (fun _ : α => Γg)) :=
      isRelAdvMatrix_compose (g := constFam g) hf1 fun _ => hg1
    have hmask : ∀ ℓ : α × β, ‖compose (constFam g) Γf (fun _ : α => Γg) ⊙ advD ℓ‖
        ≤ ‖Γg‖ ^ (Fintype.card α - 1) := by
      rintro ⟨p, q⟩
      refine (norm_compose_mask hf1.isHermitian hg1 p q).trans ?_
      calc ‖Γf ⊙ advD p‖ * (‖Γg ⊙ advD q‖ * ‖Γg‖ ^ (Fintype.card α - 1))
          ≤ 1 * (1 * ‖Γg‖ ^ (Fintype.card α - 1)) :=
            mul_le_mul (hf2 p)
              (mul_le_mul (hg2 q) le_rfl (by positivity) zero_le_one)
              (by positivity) zero_le_one
        _ = ‖Γg‖ ^ (Fintype.card α - 1) := by ring
    have hfinal := rayleigh_div_le_relAdvPM htot' hrel hmask
      (pow_pos hgpos _) hVunit
    rw [hVray] at hfinal
    have hle : (v ⬝ᵥ Γf *ᵥ v) * ‖Γg‖
        ≤ ‖Γg‖ ^ Fintype.card α * (v ⬝ᵥ Γf *ᵥ v)
          / ‖Γg‖ ^ (Fintype.card α - 1) := by
      rw [le_div_iff₀ (pow_pos hgpos _)]
      refine le_of_eq ?_
      calc (v ⬝ᵥ Γf *ᵥ v) * ‖Γg‖ * ‖Γg‖ ^ (Fintype.card α - 1)
          = (v ⬝ᵥ Γf *ᵥ v) * (‖Γg‖ * ‖Γg‖ ^ (Fintype.card α - 1)) :=
            mul_assoc _ _ _
        _ = (v ⬝ᵥ Γf *ᵥ v) * ‖Γg‖ ^ (Fintype.card α - 1 + 1) := by
            rw [← pow_succ']
        _ = (v ⬝ᵥ Γf *ᵥ v) * ‖Γg‖ ^ Fintype.card α := by rw [hk]
        _ = ‖Γg‖ ^ Fintype.card α * (v ⬝ᵥ Γf *ᵥ v) := mul_comm _ _
    exact hle.trans hfinal
  -- two supremum passes
  rcases eq_or_lt_of_le (advPM_nonneg g) with hg0 | hg0
  · rw [← hg0, mul_zero]
    exact relAdvPM_nonneg htot'
  rw [← le_div_iff₀ hg0]
  refine relAdvPM_le fun Γf v hf1 hf2 hv => ?_
  rw [le_div_iff₀ hg0]
  rcases le_or_gt (v ⬝ᵥ Γf *ᵥ v) 0 with hr0 | hrpos
  · have h1 : (v ⬝ᵥ Γf *ᵥ v) * advPM g ≤ 0 := by
      simpa using mul_le_mul_of_nonneg_right hr0 hg0.le
    exact h1.trans (relAdvPM_nonneg htot')
  rw [mul_comm, ← le_div_iff₀ hrpos]
  refine advPM_le fun Γg hg1 hg2 => ?_
  rw [le_div_iff₀ hrpos, mul_comm]
  exact hkey Γf v hf1 hf2 hv Γg hg1 hg2

end QuantumQueryComplexity
