import QuantumQueryComplexity.Quantum.Oracle
import Mathlib.LinearAlgebra.Matrix.Kronecker

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Workspace extension and register-indexed families

Extending a workspace by a register `V` and acting **block-diagonally** on it is
the single primitive behind two things the circuit layer needs: *lifting* an
operator to a larger workspace (a constant family) and *controlling* it on a
register value (a family that is the identity elsewhere).

  `blockFam fam` applies `fam v` on the sector where the extra register holds `v`.

It is defined as Mathlib's `Matrix.blockDiagonal` read through the reindexing
`regEquiv : QBasis ι σ (V × W) ≃ QBasis ι σ W × V`, so the algebra —
multiplicativity, unit, adjoint — is inherited rather than re-proved.

## Acceptance contracts

* `blockFam_mul`, `blockFam_one`, `blockFam_conjTranspose`,
  `blockFam_mem_unitaryGroup` — it is a monoid map into the unitaries.
* `blockFam_mulVec_embed` — its action on the **encoded subspace**
  `embedReg v ψ`, the sector where the register holds `v`.  This is the only
  form in which `blockFam` gets used: statements about a controlled operator are
  statements about encoded states, never global matrix identities.
* `blockFam_oracle` — the oracle ignores the workspace, so on an extended
  workspace it *is* a constant block family.  This is what lets a query pass
  through a workspace extension unchanged.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ V W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Two matrices agreeing on every basis vector are equal. -/
lemma matrix_ext_of_mulVec_qBasis {H : Type} [Fintype H] [DecidableEq H]
    {M N : Matrix H H ℂ} (h : ∀ r, M *ᵥ qBasis r = N *ᵥ qBasis r) : M = N := by
  ext p q
  have hpq := congrFun (h q) p
  simpa [Matrix.mulVec, dotProduct, qBasis_apply, Finset.sum_ite_eq'] using hpq

/-- The extended basis, split as (rest, extra register). -/
def regEquiv : QBasis ι σ (V × W) ≃ QBasis ι σ W × V where
  toFun p := ((p.1, p.2.1, p.2.2.2), p.2.2.1)
  invFun x := (x.1.1, x.1.2.1, (x.2, x.1.2.2))
  left_inv := by rintro ⟨k, t, v, w⟩; rfl
  right_inv := by rintro ⟨⟨k, t, w⟩, v⟩; rfl

@[simp] lemma regEquiv_apply (p : QBasis ι σ (V × W)) :
    regEquiv p = ((p.1, p.2.1, p.2.2.2), p.2.2.1) := rfl

@[simp] lemma regEquiv_symm_apply (x : QBasis ι σ W × V) :
    (regEquiv (ι := ι) (σ := σ) (V := V) (W := W)).symm x
      = (x.1.1, x.1.2.1, (x.2, x.1.2.2)) := rfl

/-- **A register-indexed family of operators**, acting block-diagonally on the
extra register. -/
def blockFam (fam : V → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) :
    Matrix (QBasis ι σ (V × W)) (QBasis ι σ (V × W)) ℂ :=
  (Matrix.blockDiagonal fam).submatrix regEquiv regEquiv

/-- Lift an operator to an extended workspace: the constant family. -/
def liftReg (V : Type) [Fintype V] [DecidableEq V]
    (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) :
    Matrix (QBasis ι σ (V × W)) (QBasis ι σ (V × W)) ℂ :=
  blockFam (fun _ : V => U)

/-! ## The algebra -/

theorem blockFam_mul (f g : V → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) :
    blockFam f * blockFam g = blockFam (fun v => f v * g v) := by
  rw [blockFam, blockFam, blockFam, Matrix.submatrix_mul_equiv, Matrix.blockDiagonal_mul]

theorem blockFam_one :
    blockFam (fun _ : V => (1 : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)) = 1 := by
  rw [blockFam, show (fun _ : V => (1 : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ))
    = (1 : V → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) from rfl,
    Matrix.blockDiagonal_one, Matrix.submatrix_one_equiv]

theorem blockFam_conjTranspose (f : V → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) :
    (blockFam f)ᴴ = blockFam (fun v => (f v)ᴴ) := by
  rw [blockFam, blockFam, Matrix.conjTranspose_submatrix, Matrix.blockDiagonal_conjTranspose]

theorem blockFam_mem_unitaryGroup {f : V → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
    (hf : ∀ v, f v ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) :
    blockFam f ∈ Matrix.unitaryGroup (QBasis ι σ (V × W)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    blockFam_conjTranspose, blockFam_mul]
  rw [show (fun v => (f v)ᴴ * f v) = (fun _ : V => (1 : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ))
    from funext fun v => conjTranspose_mul_self_of_unitary (hf v)]
  exact blockFam_one

lemma liftReg_mem_unitaryGroup {U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) :
    liftReg V U ∈ Matrix.unitaryGroup (QBasis ι σ (V × W)) ℂ :=
  blockFam_mem_unitaryGroup fun _ => hU

/-! ## The encoded subspace -/

/-- **The encoded subspace**: `ψ`, placed in the sector where the extra register
holds `v`. -/
def embedReg (v : V) (ψ : QBasis ι σ W → ℂ) : QBasis ι σ (V × W) → ℂ :=
  fun p => if p.2.2.1 = v then ψ (p.1, p.2.1, p.2.2.2) else 0

lemma embedReg_apply (v : V) (ψ : QBasis ι σ W → ℂ) (p : QBasis ι σ (V × W)) :
    embedReg v ψ p = if p.2.2.1 = v then ψ (p.1, p.2.1, p.2.2.2) else 0 := rfl

private lemma blockDiagonal_mulVec_embed
    (fam : V → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (v : V)
    (ψ : QBasis ι σ W → ℂ) :
    Matrix.blockDiagonal fam *ᵥ (fun x : QBasis ι σ W × V => if x.2 = v then ψ x.1 else 0)
      = fun x : QBasis ι σ W × V => if x.2 = v then (fam v *ᵥ ψ) x.1 else 0 := by
  funext x
  obtain ⟨s', u'⟩ := x
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  have hterm : ∀ (s : QBasis ι σ W) (u : V),
      Matrix.blockDiagonal fam (s', u') (s, u) * (if u = v then ψ s else 0)
        = if u = u' then (if u' = v then fam u' s' s * ψ s else 0) else 0 := by
    intro s u
    rw [Matrix.blockDiagonal_apply]
    by_cases h : u' = u
    · subst h
      by_cases h2 : u' = v <;> simp [h2]
    · simp [h, Ne.symm h]
  simp only [hterm]
  rw [show (∑ s : QBasis ι σ W, ∑ u : V,
      (if u = u' then (if u' = v then fam u' s' s * ψ s else 0) else 0))
      = ∑ s : QBasis ι σ W, (if u' = v then fam u' s' s * ψ s else 0) from
    Finset.sum_congr rfl fun s _ => by
      rw [Finset.sum_ite_eq' Finset.univ u' (fun _ => (if u' = v then fam u' s' s * ψ s else 0))]
      simp]
  by_cases h : u' = v
  · subst h
    simp [Matrix.mulVec, dotProduct]
  · simp [h]

/-- **The action on the encoded subspace.** -/
theorem blockFam_mulVec_embed (fam : V → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (v : V) (ψ : QBasis ι σ W → ℂ) :
    blockFam fam *ᵥ embedReg v ψ = embedReg v (fam v *ᵥ ψ) := by
  rw [blockFam, Matrix.submatrix_mulVec_equiv]
  have hcomp : embedReg v ψ ∘ (regEquiv (ι := ι) (σ := σ) (V := V) (W := W)).symm
      = fun x : QBasis ι σ W × V => if x.2 = v then ψ x.1 else 0 := by
    funext x
    obtain ⟨⟨k, t, w⟩, u⟩ := x
    rfl
  rw [hcomp, blockDiagonal_mulVec_embed]
  funext p
  rfl

lemma liftReg_mul (U U' : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) :
    liftReg V U * liftReg V U' = liftReg V (U * U') := blockFam_mul _ _

lemma liftReg_mulVec_embed (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (v : V)
    (ψ : QBasis ι σ W → ℂ) :
    liftReg V U *ᵥ embedReg v ψ = embedReg v (U *ᵥ ψ) :=
  blockFam_mulVec_embed _ v ψ

lemma liftReg_conjTranspose (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) :
    (liftReg V U)ᴴ = liftReg V Uᴴ := blockFam_conjTranspose _

lemma isQProjector_liftReg {P : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
    (hP : IsQProjector P) : IsQProjector (liftReg V P) :=
  ⟨by rw [liftReg_conjTranspose, hP.1], by rw [liftReg_mul, hP.2]⟩

/-! ## The sectors are orthogonal

The embedding is linear and isometric onto its own sector, and distinct register
values give orthogonal sectors.  Everything a superposition over the register
needs — Pythagoras for a packed family, in particular — comes from these. -/

/-- Split a sum over the extended basis as (rest, extra register). -/
lemma sum_reg {M : Type*} [AddCommMonoid M] (F : QBasis ι σ (V × W) → M) :
    ∑ r, F r = ∑ s : QBasis ι σ W, ∑ u : V, F (regEquiv.symm (s, u)) := by
  rw [← Equiv.sum_comp (regEquiv (ι := ι) (σ := σ) (V := V) (W := W)).symm F,
    Fintype.sum_prod_type]

lemma embedReg_regEquiv_symm (v : V) (ψ : QBasis ι σ W → ℂ)
    (s : QBasis ι σ W) (u : V) :
    embedReg v ψ (regEquiv.symm (s, u)) = if u = v then ψ s else 0 := rfl

lemma embedReg_smul (v : V) (a : ℂ) (ψ : QBasis ι σ W → ℂ) :
    embedReg v (a • ψ) = a • embedReg v ψ := by
  funext p
  by_cases h : p.2.2.1 = v <;> simp [embedReg_apply, h]

lemma embedReg_sum {α : Type*} (v : V) (s : Finset α)
    (f : α → (QBasis ι σ W → ℂ)) :
    embedReg v (∑ i ∈ s, f i) = ∑ i ∈ s, embedReg v (f i) := by
  funext p
  rw [embedReg_apply, Finset.sum_apply, Finset.sum_apply]
  by_cases h : p.2.2.1 = v
  · simp only [if_pos h]
    exact Finset.sum_congr rfl fun i _ => by rw [embedReg_apply, if_pos h]
  · simp [h, embedReg_apply]

/-- **Distinct register values give orthogonal sectors**, and the embedding
preserves the inner product on its own. -/
theorem qInner_embedReg (v v' : V) (ψ φ : QBasis ι σ W → ℂ) :
    qInner (embedReg v ψ) (embedReg v' φ) = if v = v' then qInner ψ φ else 0 := by
  rw [qInner_def, sum_reg]
  by_cases h : v = v'
  · subst h
    rw [if_pos rfl, qInner_def]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single v]
    · rw [embedReg_regEquiv_symm, embedReg_regEquiv_symm, if_pos rfl, if_pos rfl]
    · intro u _ hu
      rw [embedReg_regEquiv_symm, if_neg hu, star_zero, zero_mul]
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun u _ => ?_
    rw [embedReg_regEquiv_symm, embedReg_regEquiv_symm]
    by_cases hu : u = v'
    · rw [if_neg fun hc => h (hc.symm.trans hu), star_zero, zero_mul]
    · rw [if_neg hu, mul_zero]

lemma qNormSq_embedReg (v : V) (ψ : QBasis ι σ W → ℂ) :
    qNormSq (embedReg v ψ) = qNormSq ψ := by
  have h := qInner_embedReg v v ψ ψ
  rw [if_pos rfl, qInner_self, qInner_self] at h
  exact_mod_cast h

/-! ## Operators on the extra register itself

`blockFam` acts on the *workspace*, indexed by the register.  Its transpose —
acting on the **register**, trivially on the workspace — is the other primitive a
clocked construction needs, and it is Mathlib's Kronecker product with the
identity, so again the algebra is inherited rather than re-proved. -/

/-- An operator acting on the **extra register alone**, as the identity
elsewhere. -/
def regOp (A : Matrix V V ℂ) :
    Matrix (QBasis ι σ (V × W)) (QBasis ι σ (V × W)) ℂ :=
  Matrix.kroneckerMap (· * ·) (1 : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) A
    |>.submatrix regEquiv regEquiv

theorem regOp_mul (A B : Matrix V V ℂ) :
    regOp (ι := ι) (σ := σ) (W := W) A * regOp B = regOp (A * B) := by
  rw [regOp, regOp, regOp, Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, one_mul]

theorem regOp_one :
    regOp (ι := ι) (σ := σ) (W := W) (1 : Matrix V V ℂ) = 1 := by
  rw [regOp, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

theorem regOp_conjTranspose (A : Matrix V V ℂ) :
    (regOp (ι := ι) (σ := σ) (W := W) A)ᴴ = regOp Aᴴ := by
  rw [regOp, regOp, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]

theorem isQProjector_regOp {A : Matrix V V ℂ} (hA : IsQProjector A) :
    IsQProjector (regOp (ι := ι) (σ := σ) (W := W) A) :=
  ⟨by rw [regOp_conjTranspose, hA.1], by rw [regOp_mul, hA.2]⟩

/-- **The action on the encoded subspace**: `A` moves the register, leaving the
workspace vector alone. -/
theorem regOp_mulVec_embedReg (A : Matrix V V ℂ) (v : V) (ψ : QBasis ι σ W → ℂ) :
    regOp A *ᵥ embedReg v ψ = ∑ v' : V, A v' v • embedReg v' ψ := by
  have key : ∀ (s' : QBasis ι σ W) (u : V),
      (Matrix.kroneckerMap (· * ·) (1 : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) A
          *ᵥ (embedReg v ψ ∘ (regEquiv (ι := ι) (σ := σ) (V := V) (W := W)).symm))
          (s', u) = A u v * ψ s' := by
    intro s' u
    rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    have hterm : ∀ (s : QBasis ι σ W) (u' : V),
        Matrix.kroneckerMap (· * ·) (1 : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) A
            (s', u) (s, u')
          * (embedReg v ψ ∘ (regEquiv (ι := ι) (σ := σ) (V := V) (W := W)).symm) (s, u')
        = if u' = v then (if s = s' then A u v * ψ s else 0) else 0 := by
      intro s u'
      rw [Function.comp_apply, embedReg_regEquiv_symm]
      by_cases h : u' = v
      · subst h
        rw [if_pos rfl, if_pos rfl]
        -- the Kronecker entry, unfolded: `(1 ⊗ₖ A) (s',u) (s,u') = 1 s' s * A u u'`
        change ((1 : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) s' s * A u u') * ψ s
          = if s = s' then A u u' * ψ s else 0
        rw [Matrix.one_apply]
        by_cases hs : s' = s
        · rw [if_pos hs, if_pos hs.symm, one_mul]
        · rw [if_neg hs, if_neg fun hc => hs hc.symm, zero_mul, zero_mul]
      · rw [if_neg h, if_neg h, mul_zero]
    simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [regOp, Matrix.submatrix_mulVec_equiv]
  funext p
  rw [Function.comp_apply,
    show (regEquiv (ι := ι) (σ := σ) (V := V) (W := W)) p
      = ((p.1, p.2.1, p.2.2.2), p.2.2.1) from rfl, key, Finset.sum_apply,
    Finset.sum_eq_single p.2.2.1]
  · rw [Pi.smul_apply, embedReg_apply, if_pos rfl, smul_eq_mul]
  · intro v' _ hv'
    rw [Pi.smul_apply, embedReg_apply, if_neg fun hc => hv' hc.symm, smul_zero]
  · simp

/-! ## The oracle passes through a workspace extension -/

/-- The oracle leaves the extra register alone. -/
lemma oracleMap_reg_fst (a : ι → σ) (p : QBasis ι σ (V × W)) :
    (oracleMap a p).2.2.1 = p.2.2.1 := by
  obtain ⟨k, t, v, w⟩ := p
  cases k <;> rfl

/-- The oracle commutes with dropping the extra register. -/
lemma oracleMap_reg_drop (a : ι → σ) (p : QBasis ι σ (V × W)) :
    ((oracleMap a p).1, (oracleMap a p).2.1, (oracleMap a p).2.2.2)
      = oracleMap a (p.1, p.2.1, p.2.2.2) := by
  obtain ⟨k, t, v, w⟩ := p
  cases k <;> rfl

lemma qBasis_eq_embedReg (r : QBasis ι σ (V × W)) :
    qBasis r = embedReg r.2.2.1 (qBasis (r.1, r.2.1, r.2.2.2)) := by
  funext p
  obtain ⟨k, t, v, w⟩ := p
  obtain ⟨k', t', v', w'⟩ := r
  simp only [qBasis_apply, embedReg_apply, Prod.mk.injEq]
  by_cases h : v = v'
  · subst h
    by_cases hk : k = k' <;> by_cases ht : t = t' <;> by_cases hw : w = w' <;>
      simp [hk, ht, hw]
  · simp [h]

/-- **The oracle ignores the workspace**, so on an extended workspace it is a
constant block family. -/
theorem blockFam_oracle (a : ι → σ) :
    oracleMat (W := V × W) a = liftReg V (oracleMat a) := by
  refine matrix_ext_of_mulVec_qBasis fun r => ?_
  rw [oracleMat_mulVec_qBasis, qBasis_eq_embedReg r, liftReg_mulVec_embed,
    oracleMat_mulVec_qBasis, qBasis_eq_embedReg (oracleMap a r), oracleMap_reg_fst,
    oracleMap_reg_drop]

end QuantumQueryComplexity
