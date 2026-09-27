import QuantumQueryComplexity.Quantum.Amplitude.SearchInvUpTo
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# A reflection with a genuine error

`noisyRefl s t t' = (2|s⟩⟨s| − 1)·(2|t⟩⟨t| − 1)·(2|t'⟩⟨t'| − 1)` for unit vectors `t, t'`
orthogonal to `s`.  The last two factors are a small rotation in the plane of `t, t'`, which
fixes `s`; so `noisyRefl` **fixes `s` exactly** and differs from the exact reflection about
`s` by at most `4·‖t' − t‖` times the component orthogonal to `s`
(`isApproxRefl_noisyRefl`) — and the difference is not zero.  When `t` has a blank ancilla and
`t'` a slightly rotated one, the error is precisely amplitude leaking into a *dirty* ancilla:
the situation the clean-history convention exists for.

Also: the adjoint (`noisyRefl_conjTranspose`), preservation of any support containing the
three vectors, and commutation with any flag that holds on the three vectors.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H : Type} [Fintype H] [DecidableEq H]

/-- Three reflections. -/
noncomputable def noisyRefl (s t t' : H → ℂ) : Matrix H H ℂ :=
  stateRefl s * (stateRefl t * stateRefl t')

variable {s t t' : H → ℂ}

lemma noisyRefl_mem_unitaryGroup (hs : IsQState s) (ht : IsQState t) (ht' : IsQState t') :
    noisyRefl s t t' ∈ Matrix.unitaryGroup H ℂ :=
  mul_mem_qUnitary (stateRefl_mem_unitaryGroup hs)
    (mul_mem_qUnitary (stateRefl_mem_unitaryGroup ht) (stateRefl_mem_unitaryGroup ht'))

lemma noisyRefl_conjTranspose (hs : IsQState s) (ht : IsQState t) (ht' : IsQState t') :
    (noisyRefl s t t')ᴴ = stateRefl t' * (stateRefl t * stateRefl s) := by
  rw [noisyRefl, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, stateRefl_conjTranspose hs,
    stateRefl_conjTranspose ht, stateRefl_conjTranspose ht', Matrix.mul_assoc]

lemma stateRefl_mulVec_of_orth {v w : H → ℂ} (h : qInner v w = 0) : stateRefl v *ᵥ w = -w := by
  rw [stateRefl_mulVec, h, mul_zero, zero_smul, zero_sub]

lemma stateRefl_mulVec_self {v : H → ℂ} (hv : IsQState v) : stateRefl v *ᵥ v = v :=
  (isApproxRefl_stateRefl hv).fix

lemma stateRefl_stateRefl_mulVec {v : H → ℂ} (hv : IsQState v) (w : H → ℂ) :
    stateRefl v *ᵥ (stateRefl v *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, stateRefl, qRefl_mul_self (isQProjector_ketbra hv),
    Matrix.one_mulVec]

/-- **A `4‖t' − t‖`-approximate reflection about `s`, on every vector.** -/
theorem isApproxRefl_noisyRefl (hs : IsQState s) (ht : IsQState t) (ht' : IsQState t')
    (hts : qInner t s = 0) (ht's : qInner t' s = 0) {d : ℝ} (hd : qNorm (t' - t) ≤ d) :
    IsApproxRefl (noisyRefl s t t') s Set.univ (4 * d) where
  fix := by
    rw [noisyRefl, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      stateRefl_mulVec_of_orth ht's, Matrix.mulVec_neg, stateRefl_mulVec_of_orth hts, neg_neg,
      stateRefl_mulVec_self hs]
  near := fun w _ => by
    set wp := w - qInner s w • s with hwp
    have hd0 : 0 ≤ d := (qNorm_nonneg _).trans hd
    have horth : ∀ v : H → ℂ, qInner v s = 0 → qInner v w = qInner v wp := fun v hv => by
      rw [hwp, qInner_sub_right, qInner_smul_right, hv, mul_zero, sub_zero]
    -- strip the outer reflections
    have h1 : noisyRefl s t t' *ᵥ w - stateRefl s *ᵥ w
        = stateRefl s *ᵥ (stateRefl t *ᵥ (stateRefl t' *ᵥ w - stateRefl t *ᵥ w)) := by
      rw [noisyRefl, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub,
        Matrix.mulVec_sub, stateRefl_stateRefl_mulVec ht]
    have h2 : stateRefl t' *ᵥ w - stateRefl t *ᵥ w
        = (2 * qInner (t' - t) wp) • t' + (2 * qInner t wp) • (t' - t) := by
      rw [stateRefl_mulVec, stateRefl_mulVec, horth t' ht's, horth t hts, qInner_sub_left]
      module
    rw [h1, qNorm_mulVec (stateRefl_mem_unitaryGroup hs),
      qNorm_mulVec (stateRefl_mem_unitaryGroup ht), h2]
    refine (qNorm_add_le _ _).trans ?_
    rw [qNorm_smul, qNorm_smul, norm_mul, norm_mul, Complex.norm_ofNat, qNorm_eq_one ht',
      mul_one]
    have e1 : ‖qInner (t' - t) wp‖ ≤ d * qNorm wp :=
      (norm_qInner_le _ _).trans (mul_le_mul_of_nonneg_right hd (qNorm_nonneg _))
    have e2 : ‖qInner t wp‖ ≤ qNorm wp := by
      refine (norm_qInner_le _ _).trans ?_
      rw [qNorm_eq_one ht, one_mul]
    have e3 : ‖qInner t wp‖ * qNorm (t' - t) ≤ qNorm wp * d :=
      mul_le_mul e2 hd (qNorm_nonneg _) (qNorm_nonneg _)
    nlinarith

/-- The contract weakens in the precision and in the allowed set. -/
lemma IsApproxRefl.mono {R : Matrix H H ℂ} {D D' : Set (H → ℂ)} {β β' : ℝ}
    (h : IsApproxRefl R s D β) (hD : D' ⊆ D) (hβ : β ≤ β') : IsApproxRefl R s D' β' :=
  ⟨h.fix, fun w hw => (h.near w (hD hw)).trans
    (mul_le_mul_of_nonneg_right hβ (qNorm_nonneg _))⟩

section Supp

lemma preserves_noisyRefl {F : Set H} (hs : SuppIn F s) (ht : SuppIn F t) (ht' : SuppIn F t') :
    Preserves (noisyRefl s t t') F :=
  (preserves_stateRefl hs).mul ((preserves_stateRefl ht).mul (preserves_stateRefl ht'))

lemma preserves_noisyRefl_adj {F : Set H} (hsu : IsQState s) (htu : IsQState t)
    (ht'u : IsQState t') (hs : SuppIn F s) (ht : SuppIn F t) (ht' : SuppIn F t') :
    Preserves (noisyRefl s t t')ᴴ F := by
  rw [noisyRefl_conjTranspose hsu htu ht'u]
  exact (preserves_stateRefl ht').mul ((preserves_stateRefl ht).mul (preserves_stateRefl hs))

lemma qInner_goodPart_left {O : Type} (rd : H → O) (G : O → Prop) [DecidablePred G]
    (ψ φ : H → ℂ) : qInner (goodPart rd G ψ) φ = qInner (goodPart rd G ψ) (goodPart rd G φ) := by
  rw [qInner_def, qInner_def]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [goodPart_apply, goodPart_apply]
  split_ifs <;> simp

/-- A reflection about a flagged vector commutes with the flag. -/
lemma stateRefl_comm_flagProj {c : H → Bool} {v : H → ℂ}
    (hv : goodPart c (· = true) v = v) :
    stateRefl v * flagProj c = flagProj c * stateRefl v := by
  refine matrix_ext_of_mulVec_qBasis fun r => ?_
  have hin : ∀ w, qInner v (goodPart c (· = true) w) = qInner v w := fun w => by
    have h1 := qInner_goodPart_right c (· = true) v w
    have h2 := qInner_goodPart_left c (· = true) v w
    rw [hv] at h1 h2
    rw [h1, ← h2]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, flagProj_mulVec, flagProj_mulVec,
    stateRefl_mulVec, stateRefl_mulVec, hin, goodPart_sub, goodPart_smul, hv]

lemma noisyRefl_comm_flagProj {c : H → Bool} (hs : goodPart c (· = true) s = s)
    (ht : goodPart c (· = true) t = t) (ht' : goodPart c (· = true) t' = t') :
    noisyRefl s t t' * flagProj c = flagProj c * noisyRefl s t t' := by
  rw [noisyRefl, Matrix.mul_assoc, Matrix.mul_assoc, stateRefl_comm_flagProj ht',
    ← Matrix.mul_assoc (stateRefl t), stateRefl_comm_flagProj ht, Matrix.mul_assoc,
    ← Matrix.mul_assoc (stateRefl s), stateRefl_comm_flagProj hs, Matrix.mul_assoc]

end Supp

end QuantumQueryComplexity
