import QuantumQueryComplexity.Quantum.ProductRun

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Copied input bits cost one query each

[CGKLPZ26, Lemma 2.3 and the proof of Lemma 2.9]. A map `φ : κ → ι`, not necessarily injective,
lets an input `x : ι → σ` be read as `x ∘ φ : κ → σ`: index `k` holds a copy of the bit `x (φ k)`.
An algorithm on the copied input is simulated on the original input with **the same number of
value-oracle queries** (`Realizes.reindex`): before each query it writes `φ k` into the query
register, keeping `k` in its workspace, and after the query it uncomputes `φ k`. The library's
`xorQQueryOn_le_of_padRead` is the XOR-oracle counterpart with known zeros; this is the native
value-oracle form, which the bipartite double cover (Lemma 2.3) and the cover copy of Lemma 2.9
need.
-/

namespace QuantumQueryComplexity

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

open scoped Matrix
open Matrix

/-! ## The workspace lift and the embedded sector -/

section IdxLift

variable {R : Type} [Fintype R] [DecidableEq R]

/-- The simulation's basis, split as (workspace, simulation registers). -/
private def idx_wEquiv : QBasis ι σ R ≃ R × (Option ι × Option σ) where
  toFun p := (p.2.2, (p.1, p.2.1))
  invFun x := (x.2.1, x.2.2, x.1)
  left_inv := by rintro ⟨k, c, r⟩; rfl
  right_inv := by rintro ⟨r, k, c⟩; rfl

/-- An operator on the workspace, acting as the identity on the simulation's registers. -/
private noncomputable def idx_wLift (M : Matrix R R ℂ) :
    Matrix (QBasis ι σ R) (QBasis ι σ R) ℂ :=
  (Matrix.blockDiagonal fun _ : Option ι × Option σ => M).submatrix idx_wEquiv idx_wEquiv

private lemma idx_wLift_mem_unitaryGroup {M : Matrix R R ℂ}
    (hM : M ∈ Matrix.unitaryGroup R ℂ) :
    idx_wLift (ι := ι) (σ := σ) M ∈ Matrix.unitaryGroup (QBasis ι σ R) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, idx_wLift,
    Matrix.conjTranspose_submatrix, Matrix.blockDiagonal_conjTranspose,
    Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]
  rw [show (fun _ : Option ι × Option σ => Mᴴ * M)
    = (1 : Option ι × Option σ → Matrix R R ℂ) from
      funext fun _ => conjTranspose_mul_self_of_unitary hM,
    Matrix.blockDiagonal_one, Matrix.submatrix_one_equiv]

private lemma idx_wLift_mulVec_apply (M : Matrix R R ℂ) (v : QBasis ι σ R → ℂ)
    (p : QBasis ι σ R) :
    (idx_wLift M *ᵥ v) p = (M *ᵥ fun r => v (p.1, p.2.1, r)) p.2.2 := by
  obtain ⟨k, c, r⟩ := p
  simp only [Matrix.mulVec, dotProduct, idx_wLift, Matrix.submatrix_apply]
  rw [← Equiv.sum_comp idx_wEquiv.symm, Fintype.sum_prod_type]
  simp [Matrix.blockDiagonal_apply, idx_wEquiv]

/-- A workspace state, with the simulation's index and answer registers idle and blank. -/
private def idx_rEmbed (ψ : R → ℂ) : QBasis ι σ R → ℂ :=
  fun p => if p.1 = none ∧ p.2.1 = none then ψ p.2.2 else 0

private lemma idx_wLift_mulVec_rEmbed (M : Matrix R R ℂ) (ψ : R → ℂ) :
    idx_wLift (ι := ι) (σ := σ) M *ᵥ idx_rEmbed ψ = idx_rEmbed (M *ᵥ ψ) := by
  funext p
  rw [idx_wLift_mulVec_apply]
  by_cases h : p.1 = none ∧ p.2.1 = none
  · have hψ : (fun r => idx_rEmbed (ι := ι) (σ := σ) ψ (p.1, p.2.1, r)) = ψ :=
      funext fun r => by simp [idx_rEmbed, h]
    rw [hψ]
    simp [idx_rEmbed, h]
  · have hψ : (fun r => idx_rEmbed (ι := ι) (σ := σ) ψ (p.1, p.2.1, r)) = 0 :=
      funext fun r => by simp only [idx_rEmbed, h, ↓reduceIte, Pi.zero_apply]
    rw [hψ, Matrix.mulVec_zero]
    simp only [idx_rEmbed, h, ↓reduceIte, Pi.zero_apply]

/-- Sums over the embedded sector. -/
private lemma idx_sum_sector (f : R → ℝ) :
    ∑ p : QBasis ι σ R, (if p.1 = none ∧ p.2.1 = none then f p.2.2 else 0)
      = ∑ r, f r := by
  simp [Fintype.sum_prod_type, ite_and]

private lemma idx_isQState_rEmbed {ψ : R → ℂ} (hψ : IsQState ψ) :
    IsQState (idx_rEmbed (ι := ι) (σ := σ) ψ) := by
  rw [IsQState] at hψ ⊢
  rw [← hψ, qNormSq_def, qNormSq_def,
    ← idx_sum_sector (ι := ι) (σ := σ) (fun r => Complex.normSq (ψ r))]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : p.1 = none ∧ p.2.1 = none <;> simp [idx_rEmbed, h]

end IdxLift

/-! ## The basis permutation around each query -/

section IdxPerm

variable {κ W : Type} [Fintype κ] [DecidableEq κ] [Fintype W] [DecidableEq W] (φ : κ → ι)

/-- **The basis permutation around each query**, controlled on the simulated index `k`:
exchange the simulation's index between idle and `φ k`, and swap the two answer registers. -/
private def idx_rMap (p : QBasis ι σ (QBasis κ σ W)) : QBasis ι σ (QBasis κ σ W) :=
  (Equiv.swap none (p.2.2.1.map φ) p.1, p.2.2.2.1, (p.2.2.1, p.2.1, p.2.2.2.2))

private lemma idx_rMap_involutive : Function.Involutive (idx_rMap (σ := σ) (W := W) φ) := by
  rintro ⟨j, c, k, b, w⟩
  simp [idx_rMap]

/-- The permutation as an `Equiv.Perm`. -/
private def idx_rPerm : Equiv.Perm (QBasis ι σ (QBasis κ σ W)) :=
  Function.Involutive.toPerm _ (idx_rMap_involutive (σ := σ) (W := W) φ)

private lemma idx_rPerm_mulVec_apply (ψ : QBasis ι σ (QBasis κ σ W) → ℂ)
    (p : QBasis ι σ (QBasis κ σ W)) :
    (qPerm (idx_rPerm φ) *ᵥ ψ) p = ψ (idx_rMap φ p) := by
  rw [qPerm_mulVec_apply]
  rfl

/-- The oracle moves neither the index register nor the workspace. -/
private lemma idx_oracleMap_fst_work {ι' W' : Type} [Fintype ι'] [DecidableEq ι']
    [Fintype W'] [DecidableEq W'] (a : ι' → σ) (q : QBasis ι' σ W') :
    (oracleMap a q).1 = q.1 ∧ (oracleMap a q).2.2 = q.2.2 := by
  rcases q with ⟨_ | j, t, r⟩ <;> exact ⟨rfl, rfl⟩

/-- **One simulated query**: the permutation, the `ι`-oracle on `x`, and the permutation again
act on the embedded sector as the `κ`-oracle on `x ∘ φ`. -/
private lemma idx_rPerm_oracle_rPerm (x : ι → σ) (ψ : QBasis κ σ W → ℂ) :
    qPerm (idx_rPerm φ) *ᵥ (oracleMat x *ᵥ (qPerm (idx_rPerm φ) *ᵥ idx_rEmbed ψ))
      = idx_rEmbed (oracleMat (x ∘ φ) *ᵥ ψ) := by
  funext p
  rw [idx_rPerm_mulVec_apply, oracleMat_mulVec_apply, idx_rPerm_mulVec_apply]
  obtain ⟨j, c, k, b, w⟩ := p
  by_cases h : j = none ∧ c = none
  · obtain ⟨rfl, rfl⟩ := h
    rcases k with _ | k
    · simp [idx_rMap, idx_rEmbed, oracleMat_mulVec_apply]
    · simp [idx_rMap, idx_rEmbed, oracleMat_mulVec_apply]
  · obtain ⟨h1, h2⟩ :=
      idx_oracleMap_fst_work x (idx_rMap φ ((j, c, k, b, w) : QBasis ι σ (QBasis κ σ W)))
    generalize oracleMap x (idx_rMap φ ((j, c, k, b, w) : QBasis ι σ (QBasis κ σ W))) = q
      at h1 h2
    have hj : (idx_rMap φ q).1 = j := by
      simp [idx_rMap, h1, h2]
    have hc : (idx_rMap φ q).2.1 = c := by
      simp [idx_rMap, h2]
    simp only [idx_rEmbed, hj, hc, h, ↓reduceIte]

end IdxPerm

/-! ## The simulation -/

section IdxAlg

variable {κ W O : Type} [Fintype κ] [DecidableEq κ] [Fintype W] [DecidableEq W]

/-- The steps of the simulation: the simulated step on the workspace, conjugated by the
permutation around each query. -/
private noncomputable def idx_rStep (A : QAlg κ σ O W) (φ : κ → ι) :
    ℕ → Matrix (QBasis ι σ (QBasis κ σ W)) (QBasis ι σ (QBasis κ σ W)) ℂ
  | 0 => qPerm (idx_rPerm φ) * idx_wLift (A.step 0)
  | s + 1 => qPerm (idx_rPerm φ) * idx_wLift (A.step (s + 1)) * qPerm (idx_rPerm φ)

private lemma idx_rStep_mem_unitaryGroup (A : QAlg κ σ O W) (φ : κ → ι) (s : ℕ) :
    idx_rStep A φ s ∈ Matrix.unitaryGroup (QBasis ι σ (QBasis κ σ W)) ℂ := by
  cases s with
  | zero =>
      exact (Matrix.unitaryGroup _ ℂ).mul_mem (qPerm_mem_unitaryGroup _)
        (idx_wLift_mem_unitaryGroup (A.step_unitary 0))
  | succ s =>
      exact (Matrix.unitaryGroup _ ℂ).mul_mem ((Matrix.unitaryGroup _ ℂ).mul_mem
        (qPerm_mem_unitaryGroup _) (idx_wLift_mem_unitaryGroup (A.step_unitary (s + 1))))
        (qPerm_mem_unitaryGroup _)

/-- **The simulation** of an algorithm on `κ` by one on `ι`, through `φ : κ → ι`, with the same
number of queries.  Its workspace holds the simulated algorithm's whole basis. -/
private noncomputable def idx_alg (A : QAlg κ σ O W) (φ : κ → ι) :
    QAlg ι σ O (QBasis κ σ W) where
  init := idx_rEmbed A.init
  init_isQState := idx_isQState_rEmbed A.init_isQState
  step := idx_rStep A φ
  step_unitary := idx_rStep_mem_unitaryGroup A φ
  readout p := A.readout (p.2.2.1, p.2.1, p.2.2.2.2)

/-- The simulation's state is the simulated state on `x ∘ φ`, embedded and permuted. -/
private lemma idx_alg_state (A : QAlg κ σ O W) (φ : κ → ι) (x : ι → σ) (t : ℕ) :
    (idx_alg A φ).state x t = qPerm (idx_rPerm φ) *ᵥ idx_rEmbed (A.state (x ∘ φ) t) := by
  induction t with
  | zero =>
      rw [QAlg.state_zero, QAlg.state_zero]
      change (qPerm (idx_rPerm φ) * idx_wLift (A.step 0)) *ᵥ idx_rEmbed A.init = _
      rw [← Matrix.mulVec_mulVec, idx_wLift_mulVec_rEmbed]
  | succ t ih =>
      rw [QAlg.state_succ, QAlg.state_succ, ih]
      change (qPerm (idx_rPerm φ) * idx_wLift (A.step (t + 1)) * qPerm (idx_rPerm φ)) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, idx_rPerm_oracle_rPerm,
        idx_wLift_mulVec_rEmbed]

/-- The simulation's readout sees the simulated readout on the embedded, permuted state. -/
private lemma idx_alg_qProb [DecidableEq O] (A : QAlg κ σ O W) (φ : κ → ι)
    (ψ : QBasis κ σ W → ℂ) (o : O) :
    qProb (idx_alg A φ).readout (qPerm (idx_rPerm φ) *ᵥ idx_rEmbed ψ) o
      = qProb A.readout ψ o := by
  rw [qProb, qProb]
  conv_lhs => rw [← Equiv.sum_comp (idx_rPerm φ)]
  conv_rhs => rw [← idx_sum_sector (ι := ι) (σ := σ)
    (fun r => if A.readout r = o then Complex.normSq (ψ r) else 0)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [idx_rPerm_mulVec_apply, show idx_rPerm φ p = idx_rMap φ p from rfl,
    idx_rMap_involutive φ p]
  obtain ⟨j, c, k, b, w⟩ := p
  rw [show (idx_alg A φ).readout (idx_rMap φ (j, c, k, b, w)) = A.readout (k, b, w) from rfl]
  by_cases h : j = none ∧ c = none <;> by_cases hr : A.readout (k, b, w) = o <;>
    simp [idx_rEmbed, h, hr]

end IdxAlg

/-- **Copied indices cost one query each** [CGKLPZ26, Lemma 2.3]: an outcome law realized on
inputs indexed by `κ` with `q` queries is realized on `x : ι → σ`, read as `x ∘ φ`, with `q`
queries. -/
theorem Realizes.reindex {κ : Type} [Fintype κ] [DecidableEq κ] (φ : κ → ι) {O : Type}
    [DecidableEq O] {q : ℕ} {P : (κ → σ) → O → ℝ}
    (h : Realizes (id : (κ → σ) → κ → σ) q P) :
    Realizes (id : (ι → σ) → ι → σ) q fun x o => P (x ∘ φ) o := by
  obtain ⟨W, _, _, A, hA⟩ := h
  refine ⟨QBasis κ σ W, inferInstance, inferInstance, idx_alg A φ, fun x o => ?_⟩
  rw [QAlg.prob, idx_alg_state, idx_alg_qProb]
  exact hA (x ∘ φ) o

end QuantumQueryComplexity
