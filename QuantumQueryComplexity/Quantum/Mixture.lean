import QuantumQueryComplexity.Quantum.Blocks
import QuantumQueryComplexity.Quantum.Padding
import QuantumQueryComplexity.Quantum.Complexity

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Finite mixtures of query algorithms

A finite family of algorithms `A ω`, one per seed `ω : Ω`, with seed-dependent
workspaces `W ω`, is run as **one** algorithm on the workspace `Σ ω, W ω`: the
initial state puts `√(p ω)·init_ω` in the sector of seed `ω`, every step is the
block-diagonal family of the components' steps, and the oracle — which ignores
the workspace — is itself such a family.  The sectors never interact, so

`(mixAlg p A).prob a t o = ∑ ω, p ω * (A ω).prob a t o`

exactly (`mixAlg_prob`).  With `padAlg` this handles components of different
query counts (`exists_mixture`). The construction realizes a classical
mixture through orthogonal workspace sectors.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {W : Ω → Type} [∀ ω, Fintype (W ω)]
  [∀ ω, DecidableEq (W ω)]

/-! ## The seed-indexed block family -/

/-- The basis of the seeded workspace, split by seed. -/
def sigEquiv : QBasis ι σ (Σ ω, W ω) ≃ Σ ω, QBasis ι σ (W ω) where
  toFun p := ⟨p.2.2.1, (p.1, p.2.1, p.2.2.2)⟩
  invFun x := (x.2.1, x.2.2.1, ⟨x.1, x.2.2.2⟩)
  left_inv := by rintro ⟨k, t, ω, w⟩; rfl
  right_inv := by rintro ⟨ω, k, t, w⟩; rfl

@[simp] lemma sigEquiv_symm_apply (x : Σ ω, QBasis ι σ (W ω)) :
    (sigEquiv (ι := ι) (σ := σ) (W := W)).symm x = (x.2.1, x.2.2.1, ⟨x.1, x.2.2.2⟩) := rfl

/-- A seed-indexed family of operators, acting block-diagonally on the seed. -/
def sigFam (fam : ∀ ω, Matrix (QBasis ι σ (W ω)) (QBasis ι σ (W ω)) ℂ) :
    Matrix (QBasis ι σ (Σ ω, W ω)) (QBasis ι σ (Σ ω, W ω)) ℂ :=
  (Matrix.blockDiagonal' fam).submatrix sigEquiv sigEquiv

theorem sigFam_mul (f g : ∀ ω, Matrix (QBasis ι σ (W ω)) (QBasis ι σ (W ω)) ℂ) :
    sigFam f * sigFam g = sigFam (fun ω => f ω * g ω) := by
  rw [sigFam, sigFam, sigFam, Matrix.submatrix_mul_equiv, Matrix.blockDiagonal'_mul]

theorem sigFam_one :
    sigFam (fun ω => (1 : Matrix (QBasis ι σ (W ω)) (QBasis ι σ (W ω)) ℂ)) = 1 := by
  rw [sigFam, show (fun ω => (1 : Matrix (QBasis ι σ (W ω)) (QBasis ι σ (W ω)) ℂ))
    = (1 : ∀ ω, Matrix (QBasis ι σ (W ω)) (QBasis ι σ (W ω)) ℂ) from rfl,
    Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]

theorem sigFam_conjTranspose (f : ∀ ω, Matrix (QBasis ι σ (W ω)) (QBasis ι σ (W ω)) ℂ) :
    (sigFam f)ᴴ = sigFam (fun ω => (f ω)ᴴ) := by
  rw [sigFam, sigFam, Matrix.conjTranspose_submatrix, Matrix.blockDiagonal'_conjTranspose]

theorem sigFam_mem_unitaryGroup {f : ∀ ω, Matrix (QBasis ι σ (W ω)) (QBasis ι σ (W ω)) ℂ}
    (hf : ∀ ω, f ω ∈ Matrix.unitaryGroup (QBasis ι σ (W ω)) ℂ) :
    sigFam f ∈ Matrix.unitaryGroup (QBasis ι σ (Σ ω, W ω)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, sigFam_conjTranspose,
    sigFam_mul]
  rw [show (fun ω => (f ω)ᴴ * f ω)
      = (fun ω => (1 : Matrix (QBasis ι σ (W ω)) (QBasis ι σ (W ω)) ℂ))
    from funext fun ω => conjTranspose_mul_self_of_unitary (hf ω)]
  exact sigFam_one

/-! ## The seed sectors -/

/-- A state placed in the sector of seed `ω`, on the split basis. -/
def embedSig' (ω : Ω) (ψ : QBasis ι σ (W ω) → ℂ) : (Σ ω, QBasis ι σ (W ω)) → ℂ :=
  fun x => if h : x.1 = ω then ψ (h ▸ x.2) else 0

/-- A state placed in the sector of seed `ω`. -/
def embedSig (ω : Ω) (ψ : QBasis ι σ (W ω) → ℂ) : QBasis ι σ (Σ ω, W ω) → ℂ :=
  fun p => embedSig' ω ψ (sigEquiv p)

lemma embedSig'_mk_self (ω : Ω) (ψ : QBasis ι σ (W ω) → ℂ) (q : QBasis ι σ (W ω)) :
    embedSig' ω ψ ⟨ω, q⟩ = ψ q := by
  simp [embedSig']

lemma embedSig'_mk_ne (ω ω' : Ω) (ψ : QBasis ι σ (W ω) → ℂ) (q : QBasis ι σ (W ω'))
    (h : ω' ≠ ω) : embedSig' ω ψ ⟨ω', q⟩ = 0 := by
  simp [embedSig', h]

lemma embedSig_symm (ω : Ω) (ψ : QBasis ι σ (W ω) → ℂ) (x : Σ ω, QBasis ι σ (W ω)) :
    embedSig ω ψ (sigEquiv.symm x) = embedSig' ω ψ x := by
  rw [embedSig, Equiv.apply_symm_apply]

/-- Split a sum over the seeded basis by seed. -/
lemma sum_sig {M : Type*} [AddCommMonoid M] (F : QBasis ι σ (Σ ω, W ω) → M) :
    ∑ r, F r = ∑ ω, ∑ q : QBasis ι σ (W ω), F (sigEquiv.symm ⟨ω, q⟩) := by
  rw [← Equiv.sum_comp (sigEquiv (ι := ι) (σ := σ) (W := W)).symm F, Fintype.sum_sigma]

/-- The block family acts on a sector through its own block. -/
theorem sigFam_mulVec_embed (fam : ∀ ω, Matrix (QBasis ι σ (W ω)) (QBasis ι σ (W ω)) ℂ)
    (ω : Ω) (ψ : QBasis ι σ (W ω) → ℂ) :
    sigFam fam *ᵥ embedSig ω ψ = embedSig ω (fam ω *ᵥ ψ) := by
  rw [sigFam, Matrix.submatrix_mulVec_equiv]
  have hcomp : embedSig ω ψ ∘ (sigEquiv (ι := ι) (σ := σ) (W := W)).symm = embedSig' ω ψ := by
    funext x; exact embedSig_symm ω ψ x
  rw [hcomp]
  funext p
  simp only [Function.comp_apply, embedSig]
  obtain ⟨ω', q⟩ := sigEquiv p
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  by_cases h : ω' = ω
  · subst h
    rw [embedSig'_mk_self, Matrix.mulVec, dotProduct, Finset.sum_eq_single ω']
    · refine Finset.sum_congr rfl fun q' _ => ?_
      rw [Matrix.blockDiagonal'_apply_eq, embedSig'_mk_self]
    · intro ω'' _ hne
      refine Finset.sum_eq_zero fun q' _ => ?_
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hne), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [embedSig'_mk_ne _ _ _ _ h]
    refine Finset.sum_eq_zero fun ω'' _ => Finset.sum_eq_zero fun q' _ => ?_
    by_cases h2 : ω'' = ω
    · subst h2
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ h, zero_mul]
    · rw [embedSig'_mk_ne _ _ _ _ h2, mul_zero]

/-- The oracle ignores the workspace. -/
lemma oracleMap_sig_snd (a : ι → σ) (p : QBasis ι σ (Σ ω, W ω)) :
    (oracleMap a p).2.2 = p.2.2 := by
  obtain ⟨k, t, w⟩ := p
  cases k <;> rfl

lemma oracleMap_sig_drop (a : ι → σ) (p : QBasis ι σ (Σ ω, W ω)) :
    sigEquiv (oracleMap a p) = ⟨p.2.2.1, oracleMap a (p.1, p.2.1, p.2.2.2)⟩ := by
  obtain ⟨k, t, w⟩ := p
  cases k <;> rfl

lemma qBasis_eq_embedSig (r : QBasis ι σ (Σ ω, W ω)) :
    qBasis r = embedSig r.2.2.1 (qBasis (r.1, r.2.1, r.2.2.2)) := by
  funext p
  rw [embedSig]
  obtain ⟨k, t, ω, w⟩ := p
  obtain ⟨k', t', ω', w'⟩ := r
  simp only [qBasis_apply, Prod.mk.injEq, sigEquiv, Equiv.coe_fn_mk]
  by_cases h : ω = ω'
  · subst h
    rw [embedSig'_mk_self]
    simp only [qBasis_apply, Prod.mk.injEq]
    by_cases hk : k = k' <;> by_cases ht : t = t' <;> by_cases hw : w = w' <;> simp [hk, ht, hw]
  · rw [embedSig'_mk_ne _ _ _ _ h]
    simp [h]

/-- **The oracle is a seed-indexed block family.** -/
theorem sigFam_oracle (a : ι → σ) :
    oracleMat (W := Σ ω, W ω) a = sigFam (fun ω => oracleMat (W := W ω) a) := by
  refine matrix_ext_of_mulVec_qBasis fun r => ?_
  rw [oracleMat_mulVec_qBasis, qBasis_eq_embedSig r, sigFam_mulVec_embed, oracleMat_mulVec_qBasis,
    qBasis_eq_embedSig (oracleMap a r)]
  obtain ⟨k, t, ω, w⟩ := r
  cases k <;> rfl

/-! ## Norms and probabilities of a superposition over the seeds -/

lemma embedSig_symm_mk (ω ω' : Ω) (ψ : QBasis ι σ (W ω) → ℂ) (q : QBasis ι σ (W ω')) :
    embedSig ω ψ (sigEquiv.symm ⟨ω', q⟩) = if h : ω' = ω then ψ (h ▸ q) else 0 := by
  rw [embedSig_symm]; rfl

/-- A superposition over the seeds, evaluated at a point of seed `ω'`, is its own
`ω'`-component. -/
lemma sum_embedSig_symm_mk (φ : ∀ ω, QBasis ι σ (W ω) → ℂ) (ω' : Ω) (q : QBasis ι σ (W ω')) :
    (∑ ω, embedSig ω (φ ω)) (sigEquiv.symm ⟨ω', q⟩) = φ ω' q := by
  rw [Finset.sum_apply, Finset.sum_eq_single ω']
  · rw [embedSig_symm_mk, dif_pos rfl]
  · intro ω _ hne
    rw [embedSig_symm_mk, dif_neg (Ne.symm hne)]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma qNormSq_sum_embedSig (φ : ∀ ω, QBasis ι σ (W ω) → ℂ) :
    qNormSq (∑ ω, embedSig ω (φ ω)) = ∑ ω, qNormSq (φ ω) := by
  rw [qNormSq_def, sum_sig]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [qNormSq_def]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [sum_embedSig_symm_mk]

/-- The readout of a seeded algorithm: the component's readout in its sector. -/
def sigReadout {O : Type} (rd : ∀ ω, QBasis ι σ (W ω) → O) : QBasis ι σ (Σ ω, W ω) → O :=
  fun r => rd r.2.2.1 (r.1, r.2.1, r.2.2.2)

lemma sigReadout_symm_mk {O : Type} (rd : ∀ ω, QBasis ι σ (W ω) → O) (ω : Ω)
    (q : QBasis ι σ (W ω)) : sigReadout rd (sigEquiv.symm ⟨ω, q⟩) = rd ω q := rfl

lemma qProb_sum_embedSig {O : Type} [DecidableEq O] (rd : ∀ ω, QBasis ι σ (W ω) → O)
    (φ : ∀ ω, QBasis ι σ (W ω) → ℂ) (o : O) :
    qProb (sigReadout rd) (∑ ω, embedSig ω (φ ω)) o = ∑ ω, qProb (rd ω) (φ ω) o := by
  rw [qProb, sum_sig]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [qProb]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [sigReadout_symm_mk, sum_embedSig_symm_mk]

/-! ## The mixture algorithm -/

variable {O : Type} [DecidableEq O]

/-- **The mixture** of the algorithms `A ω` with weights `p ω`. -/
noncomputable def mixAlg (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1)
    (A : ∀ ω, QAlg ι σ O (W ω)) : QAlg ι σ O (Σ ω, W ω) where
  init := ∑ ω, embedSig ω (((Real.sqrt (p ω) : ℝ) : ℂ) • (A ω).init)
  init_isQState := by
    rw [IsQState, qNormSq_sum_embedSig]
    refine (Finset.sum_congr rfl fun ω _ => ?_).trans hsum
    rw [qNormSq_smul, (A ω).init_isQState, mul_one, Complex.normSq_ofReal,
      Real.mul_self_sqrt (hp ω)]
  step t := sigFam (fun ω => (A ω).step t)
  step_unitary t := sigFam_mem_unitaryGroup fun ω => (A ω).step_unitary t
  readout := sigReadout fun ω => (A ω).readout

/-- The state of the mixture is the superposition of the component states. -/
theorem mixAlg_state (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1)
    (A : ∀ ω, QAlg ι σ O (W ω)) (a : ι → σ) (t : ℕ) :
    (mixAlg p hp hsum A).state a t
      = ∑ ω, embedSig ω (((Real.sqrt (p ω) : ℝ) : ℂ) • (A ω).state a t) := by
  induction t with
  | zero =>
    simp only [QAlg.state_zero, mixAlg, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [sigFam_mulVec_embed, Matrix.mulVec_smul]
  | succ t ih =>
    rw [QAlg.state_succ, ih]
    simp only [mixAlg, sigFam_oracle, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [sigFam_mulVec_embed, Matrix.mulVec_smul, sigFam_mulVec_embed, Matrix.mulVec_smul,
      QAlg.state_succ]

lemma qProb_smul {H : Type} [Fintype H] (rd : H → O) (c : ℂ) (ψ : H → ℂ) (o : O) :
    qProb rd (c • ψ) o = Complex.normSq c * qProb rd ψ o := by
  rw [qProb, qProb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  split_ifs
  · rw [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]
  · rw [mul_zero]

/-- **The outcome law of a mixture is the mixture of the outcome laws.** -/
theorem mixAlg_prob (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1)
    (A : ∀ ω, QAlg ι σ O (W ω)) (a : ι → σ) (t : ℕ) (o : O) :
    (mixAlg p hp hsum A).prob a t o = ∑ ω, p ω * (A ω).prob a t o := by
  rw [QAlg.prob, mixAlg_state]
  show qProb (sigReadout fun ω => (A ω).readout) _ o = _
  rw [qProb_sum_embedSig]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [QAlg.prob, qProb_smul, Complex.normSq_ofReal, Real.mul_self_sqrt (hp ω)]

/-- **A mixture of algorithms of different query counts**, padded to a common count
`Q`: an algorithm whose outcome law at `Q` queries is the weighted mixture of the
components' laws at their own counts. -/
theorem exists_mixture (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1)
    (q : Ω → ℕ) (Q : ℕ) (hQ : ∀ ω, q ω ≤ Q) (A : ∀ ω, QAlg ι σ O (W ω)) :
    ∃ (W' : Type) (_ : Fintype W') (_ : DecidableEq W') (B : QAlg ι σ O W'),
      ∀ (a : ι → σ) (o : O), B.prob a Q o = ∑ ω, p ω * (A ω).prob a (q ω) o := by
  refine ⟨Σ ω, CtrlWork ι (W ω), inferInstance, inferInstance,
    mixAlg p hp hsum (fun ω => padAlg (A ω) (q ω) (Q - q ω)), fun a o => ?_⟩
  rw [mixAlg_prob]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have h := padAlg_prob (A ω) (q ω) (Q - q ω) a o
  rw [show q ω + (Q - q ω) = Q by have := hQ ω; omega] at h
  rw [h]

end QuantumQueryComplexity
