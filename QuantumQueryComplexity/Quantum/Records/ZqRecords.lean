import QuantumQueryComplexity.Quantum.Records.Framework
import QuantumQueryComplexity.Quantum.ZqOracle
import QuantumQueryComplexity.Quantum.JointState.Conditioning
import Mathlib.RingTheory.RootsOfUnity.Complex

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Records and knowledge in the phase-oracle model over `Z_q`

Belovs states his framework for the phase oracle over `Z_q` and the uniform reference distribution
on `Z_qⁿ` [Bel26, Section 3]. This module places that setting inside the general one of
`Product.lean`–`Framework.lean`:

* the phase and additive oracles over `Z_q` are sector local (`isSectorLocal_phaseZqOracleMat`,
  `isSectorLocal_addOracleMat`);
* joint states in the phase model (`FinDist.jointZqState`) satisfy the record-count bound
  (`recLe_mul_jointZqState`, [Bel26, Proposition 3.2]) and are transferred exactly
  (`xferOp_mul_jointZqState`, [Bel26, Proposition 3.6]);
* the knowledge bound [Bel26, Corollary 3.24] and the lower-bound framework [Bel26, Lemma 3.18]
  hold in the phase model (`jNorm_knowOp_jointZqState_le`, `sqrt_avgZqSuccessProb_le_of_knowledge`);
* for the uniform distribution on `Z_qⁿ`, the record subspace `P_S` is spanned by the Fourier
  characters `|τ̂⟩ = ∏ᵢ ω_q^{τᵢxᵢ}/√q` with support `S` (`recProj_uniform_mulVec_fourier`): the
  records are Belovs's Fourier supports [Bel26, (3.16), (3.20)].
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι O W : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
variable {q : ℕ} [NeZero q]
variable {Ω M : Type} [Fintype Ω] [DecidableEq Ω]

/-- The phase oracle over `Z_q` is sector local for its index register. -/
theorem isSectorLocal_phaseZqOracleMat :
    IsSectorLocal (fun p : QBasis ι (ZMod q) W => p.1) phaseZqOracleMat := by
  refine ⟨fun a p p' hpp => ?_, fun a b p p' hab => ?_⟩
  · have hne : p ≠ p' := fun h => hpp (by rw [h])
    rw [phaseZqOracleMat, Matrix.diagonal_apply_ne _ hne]
  · simp only [phaseZqOracleMat, Matrix.diagonal_apply]
    split_ifs with hpp
    · subst hpp
      obtain ⟨_ | i, _ | c, w⟩ := p
      · rfl
      · rfl
      · rfl
      · change zqChar c (a i) = zqChar c (b i)
        rw [hab i rfl]
    · rfl

/-- The entries of the additive oracle: `1` at `(addOracleMap a p', p')`, `0` elsewhere. -/
private lemma addOracleMat_apply (a : ι → ZMod q) (p p' : QBasis ι (ZMod q) W) :
    addOracleMat a p p' = if p = addOracleMap a p' then 1 else 0 := by
  have h := qPerm_mulVec_apply (addOraclePerm (W := W) a) (Pi.single p' 1) p
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
  rw [addOracleMat, h, Pi.single_apply]
  simp only [Equiv.symm_apply_eq]
  rfl

/-- The additive oracle over `Z_q` is sector local for its index register. -/
theorem isSectorLocal_addOracleMat :
    IsSectorLocal (fun p : QBasis ι (ZMod q) W => p.1) addOracleMat := by
  refine ⟨fun a p p' hpp => ?_, fun a b p p' hab => ?_⟩
  · rw [addOracleMat_apply, ite_eq_right_iff]
    intro hp
    obtain ⟨_ | i, t, w⟩ := p' <;> exact absurd (by rw [hp]; rfl) hpp
  · rw [addOracleMat_apply, addOracleMat_apply]
    obtain ⟨_ | i, t, w⟩ := p'
    · rfl
    · have hab' : addOracleMap a ((some i, t, w) : QBasis ι (ZMod q) W)
          = addOracleMap b (some i, t, w) := by
        simp only [addOracleMap, hab i rfl]
      rw [hab']

namespace FinDist

/-- **The joint state in the phase-oracle model**: `∑ₓ √ρ(x) |x⟩ ⊗ ψᶻᑫₓ,ₜ`. -/
noncomputable def jointZqState (ρ : FinDist Ω) (read : Ω → ι → ZMod q)
    (A : QAlg ι (ZMod q) O W) (t : ℕ) : JVec ρ.Supp (QBasis ι (ZMod q) W) :=
  ρ.ofWvec fun x => zqState A (read x) t

/-- **The average success probability in the phase-oracle model.** -/
noncomputable def avgZqSuccessProb (ρ : FinDist Ω) (A : QAlg ι (ZMod q) O W) (t : ℕ)
    (read : Ω → ι → ZMod q) (Good : Ω → O → Prop) [∀ ω, DecidablePred (Good ω)] : ℝ :=
  ∑ ω, ρ.mass ω * zqSuccessProbOn A t read Good ω

section PhaseModel

variable (ρ : FinDist Ω)

/-- The workspace vectors of the phase-model joint state are the phase-model states. -/
theorem wvec_jointZqState (read : Ω → ι → ZMod q) (A : QAlg ι (ZMod q) O W) (t : ℕ)
    (x : ρ.Supp) : ρ.wvec (ρ.jointZqState read A t) x = zqState A (read x) t := by
  rw [jointZqState, wvec_ofWvec]

/-- The initial phase-model joint state is `|ρ⟩ ⊗ U₀|init⟩`. -/
theorem jointZqState_zero (read : Ω → ι → ZMod q) (A : QAlg ι (ZMod q) O W) :
    ρ.jointZqState read A 0 = fun x => ρ.ket x • (A.step 0 *ᵥ A.init) := by
  rfl

/-- **The joint state recursion** (phase oracle): `Ψ_{t+1} = U_{t+1} O Ψₜ`. -/
theorem jointZqState_succ (read : Ω → ι → ZMod q) (A : QAlg ι (ZMod q) O W) (t : ℕ) :
    ρ.jointZqState read A (t + 1)
      = wsOp (A.step (t + 1)) (jOracle phaseZqOracleMat (fun x : ρ.Supp => read x)
          (ρ.jointZqState read A t)) := by
  funext x
  simp only [jointZqState, ofWvec, wsOp, jOracle, zqState_succ, Matrix.mulVec_smul]

/-- An actual phase-model joint state is a unit vector. -/
theorem jNormSq_jointZqState (read : Ω → ι → ZMod q) (A : QAlg ι (ZMod q) O W) (t : ℕ) :
    jNormSq (ρ.jointZqState read A t) = 1 := by
  rw [jNormSq_eq_sum_wvec, ← ρ.sum_mass_supp]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [wvec_jointZqState, (zqState_isQState _ _ _ : qNormSq _ = 1), mul_one]



/-- **Average success is the squared norm of the masked joint state** (phase model). -/
theorem avgZqSuccessProb_eq_jNormSq_goodMask (A : QAlg ι (ZMod q) O W) (t : ℕ)
    (read : Ω → ι → ZMod q) (Good : Ω → O → Prop) [∀ ω, DecidablePred (Good ω)] :
    ρ.avgZqSuccessProb A t read Good
      = jNormSq (ρ.goodMask A.readout Good (ρ.jointZqState read A t)) := by
  rw [avgZqSuccessProb, jNormSq_eq_sum_wvec, sum_mass_mul_eq_sum_supp]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [qNormSq_wvec_goodMask, wvec_jointZqState, zqSuccessProbOn]

end PhaseModel

variable {ρ : FinDist (ι → ZMod q)}






/-- **The record-count bound in the phase model** [Bel26, Proposition 3.2]. -/
theorem recLe_mul_jointZqState (h : ρ.IsFullProduct) (A : QAlg ι (ZMod q) O W) (t : ℕ) :
    ρ.recLe t * ρ.jointZqState id A t = ρ.jointZqState id A t := by
  induction t with
  | zero =>
    exact recLe_mul_ket_smul h 0 _ _ fun x => by rw [jointZqState_zero ρ id A]
  | succ t ih =>
    rw [jointZqState_succ, mul_wsOp]
    congr 1
    exact recLe_mul_jOracle h (fun p => p.1) isSectorLocal_phaseZqOracleMat ih

/-- **The transferred joint state in the phase model** [Bel26, Proposition 3.6]. -/
theorem xferOp_mul_jointZqState (h : ρ.IsFullProduct) {ν : FinDist Ω}
    {read : Ω → ι → ZMod q} (A : QAlg ι (ZMod q) O W) (t : ℕ) :
    xferOp ρ ν read * ρ.jointZqState id A t = ν.jointZqState read A t := by
  exact xferOp_mul_ofWvec h (fun x => zqState A x t)

/-- **The knowledge bound in the phase model** [Bel26, Corollary 3.24]. -/
theorem jNorm_knowOp_jointZqState_le (h : ρ.IsFullProduct) {ν : FinDist Ω}
    {read : Ω → ι → ZMod q} {type : Ω → M} {L : M → Set (Finset ι)}
    (hL : IsKnowledgeSystem L) (A : QAlg ι (ZMod q) O W) (t : ℕ) :
    jNorm (knowOp ρ ν read type L * ρ.jointZqState id A t)
      ≤ ∑ j ∈ Finset.range t,
          (jNorm (gainOp ρ ν read type L (ρ.jointZqState id A j))
            + jNorm (gainOp ρ ν read type L
                (jOracle phaseZqOracleMat (fun x : ρ.Supp => (x : ι → ZMod q))
                  (ρ.jointZqState id A j)))) := by
  induction t with
  | zero =>
    rw [knowOp_mul_ket_smul h hL (A.step 0 *ᵥ A.init) _ fun x => by
      rw [jointZqState_zero ρ id A]]
    simp
  | succ t ih =>
    have hs : ρ.jointZqState id A (t + 1) = wsOp (A.step (t + 1))
        (jOracle phaseZqOracleMat (fun x : ρ.Supp => (x : ι → ZMod q))
          (ρ.jointZqState id A t)) :=
      jointZqState_succ ρ id A t
    rw [hs, mul_wsOp, jNorm_wsOp_of_mem_unitaryGroup (A.step_unitary _), Finset.sum_range_succ]
    linarith [jNorm_knowOp_jOracle_sub_le (ν := ν) (read := read) (type := type) h hL
      isSectorLocal_phaseZqOracleMat phaseZqOracleMat_mem_unitaryGroup (ρ.jointZqState id A t)]




/-- **The lower-bound framework in the phase model** [Bel26, Lemma 3.18]: anti-concentration of
the transferred no-knowledge part of the records of size at most `T` and final knowledge at most
`δ` give `√σ ≤ γ + δ`. -/
theorem sqrt_avgZqSuccessProb_le_of_knowledge (h : ρ.IsFullProduct) {ν : FinDist Ω}
    {read : Ω → ι → ZMod q} (type : Ω → M) (L : M → Set (Finset ι)) (Good : Ω → O → Prop)
    [∀ ω, DecidablePred (Good ω)] (A : QAlg ι (ZMod q) O W) (T : ℕ) {γ δ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : ν.IsAntiConc Good γ
      (LinearMap.range (Matrix.toLin' (knowOp ρ ν read type (fun μ => (L μ)ᶜ) * ρ.recLe T))))
    (hδ : jNorm (knowOp ρ ν read type L * ρ.jointZqState id A T) ≤ δ) :
    Real.sqrt (ν.avgZqSuccessProb A T read Good) ≤ γ + δ := by
  set Ψ := ρ.jointZqState id A T
  set Φ := ν.jointZqState read A T
  set Kp := knowOp ρ ν read type L
  set Km := knowOp ρ ν read type (fun μ => (L μ)ᶜ)
  have hΦ : Φ = Kp * Ψ + Km * Ψ := by
    rw [← Matrix.add_mul, knowOp_add_knowOp_compl h, xferOp_mul_jointZqState h]
  have hΦ1 : jNorm Φ = 1 := by rw [jNorm, jNormSq_jointZqState, Real.sqrt_one]
  obtain ⟨c, hc1, hc2⟩ := exists_smul_jNorm_le Φ (Km * Ψ)
  have hsac : ν.StronglyAntiConc Good γ (c • (Km * Ψ)) := by
    refine ⟨_, hγ, fun b => ?_⟩
    have hR : ρ.recLe T * Ψ = Ψ := recLe_mul_jointZqState h A T
    have hΨ : Km * Ψ = Km * ρ.recLe T * Ψ := by rw [Matrix.mul_assoc, hR]
    have hcol : (fun x => (c • (Km * Ψ)) x b)
        = c • Matrix.toLin' (Km * ρ.recLe T) (fun x => Ψ x b) := by
      rw [hΨ]
      funext x
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [hcol]
    exact Submodule.smul_mem _ c (LinearMap.mem_range_self _ _)
  have h3 : Φ - Km * Ψ = Kp * Ψ := by rw [hΦ]; abel
  calc Real.sqrt (ν.avgZqSuccessProb A T read Good)
      ≤ γ * jNorm (c • (Km * Ψ)) + jNorm (Φ - c • (Km * Ψ)) := by
        rw [avgZqSuccessProb_eq_jNormSq_goodMask]
        exact (ν.jNorm_goodMask_le_add A.readout Good Φ _).trans
          (add_le_add (ν.jNorm_goodMask_le_of_stronglyAntiConc A.readout Good hsac) le_rfl)
    _ ≤ γ * 1 + δ := by
        gcongr
        · exact hc1.trans hΦ1.le
        · exact hc2.trans (h3 ▸ hδ)
    _ = γ + δ := by ring

/-- The Fourier character `|τ̂⟩ = ∏ᵢ ω_q^{τᵢxᵢ}/√q` of `Z_qⁿ`. -/
noncomputable def fourierVec (τ : ι → ZMod q) : (ι → ZMod q) → ℂ := fun x =>
  ∏ i, zqChar (τ i) (x i) / ((Real.sqrt q : ℝ) : ℂ)

/-- The marginals of the uniform distribution on `Z_qⁿ` are `1/q`. -/
theorem marg_uniform_zq (i : ι) (a : ZMod q) :
    (uniform (ι → ZMod q)).marg i a = 1 / q := by
  have hshift : ∀ a, (uniform (ι → ZMod q)).marg i a = (uniform (ι → ZMod q)).marg i 0 := by
    intro a
    refine Fintype.sum_equiv (Equiv.subRight (Pi.single i a)) _ _ fun x => ?_
    simp [sub_eq_zero]
  have hsum := sum_marg (ρ := uniform (ι → ZMod q)) i
  rw [Finset.sum_congr rfl fun b _ => hshift b, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul] at hsum
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  rw [hshift a, eq_div_iff hq, mul_comm]
  exact hsum

/-- The record factor of the uniform distribution on `Z_qⁿ`. -/
private lemma recFactor_uniform_zq (S : Finset ι) (i : ι) (a b : ZMod q) :
    (uniform (ι → ZMod q)).recFactor S i a b
      = if i ∈ S then (if a = b then 1 else 0) - (q : ℂ)⁻¹ else (q : ℂ)⁻¹ := by
  have h : ((Real.sqrt ((uniform (ι → ZMod q)).marg i a * (uniform (ι → ZMod q)).marg i b) : ℝ)
      : ℂ) = (q : ℂ)⁻¹ := by
    rw [marg_uniform_zq, marg_uniform_zq, Real.sqrt_mul_self (by positivity)]
    simp
  simp only [recFactor, h]

/-- One coordinate of `P_S` applied to a character: `ω_q^{c·a}` if `i ∈ S ↔ c ≠ 0`, else `0`. -/
private lemma sum_recFactor_uniform_mul_zqChar (S : Finset ι) (i : ι) (c a : ZMod q) :
    ∑ b, (uniform (ι → ZMod q)).recFactor S i a b * zqChar c b
      = if (i ∈ S ↔ c ≠ 0) then zqChar c a else 0 := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  simp only [recFactor_uniform_zq]
  by_cases hi : i ∈ S
  · simp only [hi, ↓reduceIte, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ← Finset.mul_sum, sum_zqChar]
    by_cases hc : c = 0 <;> simp [hc, hq]
  · simp only [hi, ↓reduceIte, ← Finset.mul_sum, sum_zqChar]
    by_cases hc : c = 0 <;> simp [hc, hq]

/-- A sum over the support of the uniform distribution is a sum over all strings. -/
theorem sum_supp_uniform_zq {N : Type*} [AddCommMonoid N] (g : (ι → ZMod q) → N) :
    ∑ z : (uniform (ι → ZMod q)).Supp, g z.1 = ∑ z, g z :=
  (Finset.sum_subtype Finset.univ (fun z => by
    simp only [Finset.mem_univ, true_iff, uniform_mass]
    positivity) g).symm

/-- **The records of the uniform distribution are the Fourier supports** [Bel26, (3.20)]: `P_S`
fixes the character `|τ̂⟩` if its support `{i | τᵢ ≠ 0}` is `S`, and kills it otherwise. -/
theorem recProj_uniform_mulVec_fourier (S : Finset ι) (τ : ι → ZMod q) :
    (uniform (ι → ZMod q)).recProj S
        *ᵥ (fun x : (uniform (ι → ZMod q)).Supp => fourierVec τ x.1)
      = if Finset.univ.filter (fun i => τ i ≠ 0) = S then
          (fun x : (uniform (ι → ZMod q)).Supp => fourierVec τ x.1)
        else 0 := by
  have key : ∀ x : (uniform (ι → ZMod q)).Supp, ((uniform (ι → ZMod q)).recProj S
        *ᵥ (fun x : (uniform (ι → ZMod q)).Supp => fourierVec τ x.1)) x
      = ∏ i, (if (i ∈ S ↔ τ i ≠ 0) then zqChar (τ i) (x.1 i) else 0)
          / ((Real.sqrt q : ℝ) : ℂ) := by
    intro x
    have hG : ∀ i, (if (i ∈ S ↔ τ i ≠ 0) then zqChar (τ i) (x.1 i) else 0)
          / ((Real.sqrt q : ℝ) : ℂ)
        = ∑ b, (uniform (ι → ZMod q)).recFactor S i (x.1 i) b
            * (zqChar (τ i) b / ((Real.sqrt q : ℝ) : ℂ)) := by
      intro i
      rw [← sum_recFactor_uniform_mul_zqChar, Finset.sum_div]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [Finset.prod_congr rfl fun i _ => hG i, Fintype.prod_sum]
    simp only [Matrix.mulVec, dotProduct, recProj, fourierVec, ← Finset.prod_mul_distrib]
    exact sum_supp_uniform_zq (fun y => ∏ i, (uniform (ι → ZMod q)).recFactor S i (x.1 i) (y i)
      * (zqChar (τ i) (y i) / ((Real.sqrt q : ℝ) : ℂ)))
  by_cases hS : Finset.univ.filter (fun i => τ i ≠ 0) = S
  · rw [ite_eq_left hS]
    funext x
    rw [key x]
    simp only [fourierVec]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : (i ∈ S ↔ τ i ≠ 0) := by
      rw [← hS]
      simp
    rw [ite_eq_left hi]
  · rw [ite_eq_right hS]
    funext x
    rw [key x, Pi.zero_apply]
    obtain ⟨i, hi⟩ : ∃ i, ¬(i ∈ S ↔ τ i ≠ 0) := by
      by_contra hc
      push Not at hc
      exact hS (Finset.ext fun i => by simp [hc i])
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

end FinDist

end QuantumQueryComplexity
