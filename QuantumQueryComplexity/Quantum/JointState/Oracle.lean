import QuantumQueryComplexity.Quantum.JointState.Basic
import QuantumQueryComplexity.Quantum.XorOracle

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Joint oracles, query sectors, and the phase/XOR bridge

With the input register in superposition, a query acts on the component labelled by `x` with the
oracle of the observed input `read x` (`jOracle`).  Input-independent unitaries act on every row
(`wsOp`) and commute with every input-register operator (`mul_wsOp`).  This gives the
recursions `jointState_succ` (value oracle) and `jointXorState_succ` (XOR oracle).

## Phase form

For Boolean inputs, the controlled phase oracle `phaseOracleMat a` multiplies `|i, some true, w⟩`
by `(−1)^{aᵢ}` and fixes everything else, including the idle index and the blank answer
(Cornelissen–Gilani–Zhou (3.1), where the answer `some true` is the phase register `|1⟩`).  The
XOR oracle is its conjugate by the Hadamard gate on the answer register's `some`-part
(`hadAns`): `xorOracleMat a = hadAns * phaseOracleMat a * hadAns`
(`xorOracleMat_eq_hadAns_phase`), at the joint level `jOracle_xor_eq_hadAns_phase`.  The query
counts of the two models therefore agree exactly.

## Query sectors

`sector f e` is the component of a joint vector with query index `e` and answer `some true`.
In phase form the joint oracle acts on it by the input-register operator
`readPhase read e = diagonal ((−1)^{(read x)ₑ})` (`sector_jOracle_phase`) and fixes every other
component (`jOracle_phase_apply_of_not_sector`).  The sectors are orthogonal pieces of the joint
vector: `∑ₑ ‖sector f e‖² ≤ ‖f‖²` and `‖sector f e‖∞ ≤ ‖f‖∞` (`sum_jNormSq_sector_le`,
`FinDist.infNormSq_sector_le`).  For an actual joint state, after the Hadamard conjugation, both
sides are at most one.
-/

namespace QuantumQueryComplexity

open scoped Matrix MatrixOrder ComplexOrder
open Matrix

variable {X Y A : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype A]
  [DecidableEq A]

/-! ## Workspace operators -/

/-- An operator on the workspace, applied to every row of a joint vector. -/
def wsOp (U : Matrix A A ℂ) (f : JVec X A) : JVec X A := fun x => U *ᵥ f x

/-- A workspace operator acts on a joint vector by right multiplication with its transpose. -/
lemma wsOp_eq_mul_transpose (U : Matrix A A ℂ) (f : JVec X A) : wsOp U f = f * Uᵀ := by
  ext x a
  simp only [wsOp, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

/-- Input-register operators and workspace operators commute. -/
theorem mul_wsOp (B : Matrix Y X ℂ) (U : Matrix A A ℂ) (f : JVec X A) :
    B * wsOp U f = wsOp U (B * f) := by
  rw [wsOp_eq_mul_transpose, wsOp_eq_mul_transpose, Matrix.mul_assoc]

theorem wsOp_wsOp (U V : Matrix A A ℂ) (f : JVec X A) : wsOp U (wsOp V f) = wsOp (U * V) f := by
  funext x
  simp only [wsOp, Matrix.mulVec_mulVec]

theorem jNormSq_wsOp_of_mem_unitaryGroup {U : Matrix A A ℂ} (hU : U ∈ Matrix.unitaryGroup A ℂ)
    (f : JVec X A) : jNormSq (wsOp U f) = jNormSq f := by
  exact Finset.sum_congr rfl fun x _ => qNormSq_mulVec hU (f x)

theorem jInner_wsOp_of_mem_unitaryGroup {U : Matrix A A ℂ} (hU : U ∈ Matrix.unitaryGroup A ℂ)
    (f g : JVec X A) : jInner (wsOp U f) (wsOp U g) = jInner f g := by
  exact Finset.sum_congr rfl fun x _ => qInner_mulVec_mulVec hU (f x) (g x)

namespace FinDist

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] (ρ : FinDist Ω)

theorem wvec_wsOp (U : Matrix A A ℂ) (f : JVec ρ.Supp A) (x : ρ.Supp) :
    ρ.wvec (wsOp U f) x = U *ᵥ ρ.wvec f x := by
  rw [wvec, wvec, wsOp, Matrix.mulVec_smul]

theorem infNormSq_wsOp_of_mem_unitaryGroup {U : Matrix A A ℂ}
    (hU : U ∈ Matrix.unitaryGroup A ℂ) (f : JVec ρ.Supp A) :
    ρ.infNormSq (wsOp U f) = ρ.infNormSq f := by
  simp only [infNormSq, wvec_wsOp, qNormSq_mulVec hU]

end FinDist

/-! ## Joint oracles and joint states -/

section JointOracle

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

/-- **The joint oracle**: on the row labelled `x`, the oracle of the observed input `read x`. -/
def jOracle (O : (ι → σ) → Matrix A A ℂ) (read : X → ι → σ) (f : JVec X A) : JVec X A :=
  fun x => O (read x) *ᵥ f x

end JointOracle

namespace FinDist

variable {Ω ι σ O W : Type} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]
  [Fintype σ] [DecidableEq σ] [Fintype W] [DecidableEq W] (ρ : FinDist Ω)

/-- The initial joint state is `|ρ⟩ ⊗ U₀|init⟩`. -/
theorem jointState_zero (read : Ω → ι → σ) (A : QAlg ι σ O W) :
    ρ.jointState read A 0 = fun x => ρ.ket x • (A.step 0 *ᵥ A.init) := by
  rfl

/-- **The joint state recursion** (value oracle): `Ψ_{t+1} = U_{t+1} O Ψₜ`. -/
theorem jointState_succ (read : Ω → ι → σ) (A : QAlg ι σ O W) (t : ℕ) :
    ρ.jointState read A (t + 1)
      = wsOp (A.step (t + 1)) (jOracle oracleMat (fun x : ρ.Supp => read x)
          (ρ.jointState read A t)) := by
  funext x
  simp only [jointState, ofWvec, wsOp, jOracle, QAlg.state_succ, Matrix.mulVec_smul]

/-- **The joint state in the XOR model**: `∑ₓ √ρ(x) |x⟩ ⊗ ψˣᵒʳₓ,ₜ`. -/
noncomputable def jointXorState (read : Ω → ι → Bool) (A : QAlg ι Bool O W) (t : ℕ) :
    JVec ρ.Supp (QBasis ι Bool W) :=
  ρ.ofWvec fun x => xorState A (read x) t

@[simp] lemma wvec_jointXorState (read : Ω → ι → Bool) (A : QAlg ι Bool O W) (t : ℕ)
    (x : ρ.Supp) : ρ.wvec (ρ.jointXorState read A t) x = xorState A (read x) t := by
  rw [jointXorState, wvec_ofWvec]

theorem jointXorState_zero (read : Ω → ι → Bool) (A : QAlg ι Bool O W) :
    ρ.jointXorState read A 0 = fun x => ρ.ket x • (A.step 0 *ᵥ A.init) := by
  rfl

/-- **The joint state recursion** (XOR oracle). -/
theorem jointXorState_succ (read : Ω → ι → Bool) (A : QAlg ι Bool O W) (t : ℕ) :
    ρ.jointXorState read A (t + 1)
      = wsOp (A.step (t + 1)) (jOracle xorOracleMat (fun x : ρ.Supp => read x)
          (ρ.jointXorState read A t)) := by
  funext x
  simp only [jointXorState, ofWvec, wsOp, jOracle, xorState_succ, Matrix.mulVec_smul]

/-- An actual XOR-model joint state is a unit vector. -/
theorem jNormSq_jointXorState (read : Ω → ι → Bool) (A : QAlg ι Bool O W) (t : ℕ) :
    jNormSq (ρ.jointXorState read A t) = 1 := by
  classical
  rw [jNormSq_eq_sum_wvec, ← ρ.sum_mass_supp]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [wvec_jointXorState, (xorState_isQState _ _ _ : qNormSq _ = 1), mul_one]

/-- Every workspace vector of an actual XOR-model joint state is a unit vector. -/
theorem infNormSq_jointXorState (read : Ω → ι → Bool) (A : QAlg ι Bool O W) (t : ℕ) :
    ρ.infNormSq (ρ.jointXorState read A t) = 1 := by
  classical
  refine le_antisymm (ρ.infNormSq_le fun x => ?_) ?_
  · rw [wvec_jointXorState, (xorState_isQState _ _ _ : qNormSq _ = 1)]
  · have := ρ.qNormSq_wvec_le_infNormSq (ρ.jointXorState read A t)
      (Classical.arbitrary ρ.Supp)
    rwa [wvec_jointXorState, (xorState_isQState _ _ _ : qNormSq _ = 1)] at this

end FinDist

/-! ## The phase oracle and the Hadamard bridge -/

section Phase

variable {ι W : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]

/-- The phase of the controlled phase oracle at a basis state: `(−1)^{aᵢ}` at
`(some i, some true, w)`, and `1` elsewhere. -/
def phaseSign (a : ι → Bool) : QBasis ι Bool W → ℂ
  | (some i, some true, _) => if a i then -1 else 1
  | _ => 1

/-- **The controlled phase oracle** `|i, b, w⟩ ↦ (−1)^{b·aᵢ} |i, b, w⟩` on the answer's
`some`-part, the identity on the idle index and the blank answer (CGZ (3.1)). -/
def phaseOracleMat (a : ι → Bool) : Matrix (QBasis ι Bool W) (QBasis ι Bool W) ℂ :=
  Matrix.diagonal (phaseSign a)

theorem phaseOracleMat_mem_unitaryGroup (a : ι → Bool) :
    phaseOracleMat (W := W) a ∈ Matrix.unitaryGroup (QBasis ι Bool W) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, phaseOracleMat, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext p
  rcases p with ⟨_ | i, _ | _ | _, w⟩ <;> simp only [phaseSign, Pi.star_apply, star_one,
    mul_one]
  split_ifs <;> simp

/-- The Hadamard gate on `Option Bool`: Hadamard on `{some false, some true}`, fixing `none`. -/
noncomputable def ansHad : Matrix (Option Bool) (Option Bool) ℂ
  | none, none => 1
  | some b, some c => (if b && c then -1 else 1) / (Real.sqrt 2 : ℂ)
  | _, _ => 0

/-- The Hadamard gate on the answer register of the query basis; index and workspace untouched. -/
noncomputable def hadAns : Matrix (QBasis ι Bool W) (QBasis ι Bool W) ℂ := fun p q =>
  if p.1 = q.1 ∧ p.2.2 = q.2.2 then ansHad p.2.1 q.2.1 else 0

private lemma sqrt_two_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

private lemma sqrt_two_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (by positivity)

private lemma star_ansHad (t s : Option Bool) : star (ansHad t s) = ansHad s t := by
  rcases t with _ | _ | _ <;> rcases s with _ | _ | _ <;>
    simp [ansHad, star_div₀, Complex.conj_ofReal]

/-- Entries of a Hadamard conjugate of a diagonal operator: only the answer coordinate mixes. -/
private lemma hadAns_mul_diagonal_mul_hadAns_apply (d : QBasis ι Bool W → ℂ) (i : Option ι)
    (t : Option Bool) (w : W) (q : QBasis ι Bool W) :
    (hadAns * Matrix.diagonal d * hadAns : Matrix (QBasis ι Bool W) _ ℂ) (i, t, w) q =
      if i = q.1 ∧ w = q.2.2 then ∑ c, ansHad t c * d (i, c, w) * ansHad c q.2.1 else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, hadAns, Fintype.sum_prod_type, ite_and, ite_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  split_ifs with h1 h2
  · rw [h1, h2]
  · rfl
  · rfl

private lemma sum_ansHad_mul_ansHad (t s : Option Bool) :
    ∑ c, ansHad t c * ansHad c s = if t = s then 1 else 0 := by
  have h2 := sqrt_two_sq
  have h0 := sqrt_two_ne_zero
  simp only [Fintype.sum_option, Fintype.sum_bool]
  rcases t with _ | _ | _ <;> rcases s with _ | _ | _ <;> simp [ansHad] <;> field_simp <;>
    norm_num [h2]

private lemma sum_ansHad_mul_phaseSign_mul_ansHad (a : ι → Bool) (i : ι) (w : W)
    (t s : Option Bool) :
    ∑ c, ansHad t c * phaseSign a (some i, c, w) * ansHad c s
      = if optXor t (some (a i)) = s then 1 else 0 := by
  have h2 := sqrt_two_sq
  have h0 := sqrt_two_ne_zero
  simp only [Fintype.sum_option, Fintype.sum_bool]
  cases h : a i <;>
  rcases t with _ | _ | _ <;> rcases s with _ | _ | _ <;> simp [ansHad, phaseSign, h] <;>
    field_simp <;> norm_num [h2]

private lemma ite_and_and_eq {P Q R : Prop} [Decidable P] [Decidable Q] [Decidable R] :
    (if P ∧ Q ∧ R then (1 : ℂ) else 0) = if P ∧ R then (if Q then 1 else 0) else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP, hQ, hR]

theorem hadAns_isHermitian : (hadAns (ι := ι) (W := W)).IsHermitian := by
  ext p q
  rw [Matrix.conjTranspose_apply]
  simp only [hadAns]
  split_ifs with h1 h2 h2
  · exact star_ansHad _ _
  · exact absurd ⟨h1.1.symm, h1.2.symm⟩ h2
  · exact absurd ⟨h2.1.symm, h2.2.symm⟩ h1
  · exact star_zero _

theorem hadAns_mul_self : hadAns (ι := ι) (W := W) * hadAns = 1 := by
  have h := hadAns_mul_diagonal_mul_hadAns_apply (ι := ι) (W := W) (fun _ => 1)
  rw [Matrix.diagonal_one, Matrix.mul_one] at h
  ext ⟨i, t, w⟩ ⟨j, s, v⟩
  rw [h, Matrix.one_apply]
  simp only [mul_one, sum_ansHad_mul_ansHad, Prod.mk.injEq]
  exact ite_and_and_eq.symm

theorem hadAns_mem_unitaryGroup :
    hadAns (ι := ι) (W := W) ∈ Matrix.unitaryGroup (QBasis ι Bool W) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hadAns_isHermitian.eq,
    hadAns_mul_self]

/-- The entries of the XOR oracle: `1` at `(p, xorOracleMap a p)`, `0` elsewhere. -/
lemma xorOracleMat_apply (a : ι → Bool) (p q : QBasis ι Bool W) :
    xorOracleMat a p q = if xorOracleMap a p = q then 1 else 0 := by
  have h := xorOracleMat_mulVec_apply a (Pi.single q 1) p
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
  rw [h, Pi.single_apply]

/-- **The phase/XOR bridge**: the XOR oracle is the Hadamard conjugate of the controlled phase
oracle, with the idle index and the blank answer fixed by both. -/
theorem xorOracleMat_eq_hadAns_phase (a : ι → Bool) :
    xorOracleMat (W := W) a = hadAns * phaseOracleMat a * hadAns := by
  ext ⟨i, t, w⟩ ⟨j, s, v⟩
  rw [phaseOracleMat, hadAns_mul_diagonal_mul_hadAns_apply, xorOracleMat_apply]
  rcases i with _ | i
  · have hd : ∀ c, phaseSign a ((none, c, w) : QBasis ι Bool W) = 1 := fun c => rfl
    simp only [xorOracleMap_none, hd, mul_one, sum_ansHad_mul_ansHad, Prod.mk.injEq]
    exact ite_and_and_eq
  · simp only [xorOracleMap_some, sum_ansHad_mul_phaseSign_mul_ansHad, Prod.mk.injEq]
    exact ite_and_and_eq

/-- **The phase/XOR bridge for joint vectors.** -/
theorem jOracle_xor_eq_hadAns_phase (read : X → ι → Bool) (f : JVec X (QBasis ι Bool W)) :
    jOracle xorOracleMat read f = wsOp hadAns (jOracle phaseOracleMat read (wsOp hadAns f)) := by
  funext x
  simp only [jOracle, wsOp]
  rw [xorOracleMat_eq_hadAns_phase, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-! ## Query sectors -/

/-- **The query sector** of index `e`: the workspace component of a joint vector with query
index `some e` and answer `some true` (the phase register `|1⟩`). -/
def sector (f : JVec X (QBasis ι Bool W)) (e : ι) : JVec X W :=
  fun x w => f x (some e, some true, w)

/-- The phase query `Qₑ` on the input register, for an observation map:
`(Qₑ g)ˣ = (−1)^{(read x)ₑ} gˣ`. -/
def readPhase (read : X → ι → Bool) (e : ι) : Matrix X X ℂ :=
  Matrix.diagonal fun x => if read x e then -1 else 1

/-- Input-register operators act on each sector separately. -/
theorem sector_mul (B : Matrix Y X ℂ) (f : JVec X (QBasis ι Bool W)) (e : ι) :
    sector (B * f) e = B * sector f e := by
  rfl

/-- **The phase oracle on a sector** is the input-register operator `Qₑ`. -/
theorem sector_jOracle_phase (read : X → ι → Bool) (f : JVec X (QBasis ι Bool W)) (e : ι) :
    sector (jOracle phaseOracleMat read f) e = readPhase read e * sector f e := by
  ext x w
  simp only [sector, jOracle, phaseOracleMat, readPhase, Matrix.mulVec_diagonal,
    Matrix.diagonal_mul]
  rfl

/-- **The phase oracle fixes every basis state outside the sectors**: the idle index, the blank
answer, and the answer `some false`. -/
theorem jOracle_phase_apply_of_not_sector (read : X → ι → Bool) (f : JVec X (QBasis ι Bool W))
    (x : X) (p : QBasis ι Bool W) (hp : ∀ e w, p ≠ (some e, some true, w)) :
    jOracle phaseOracleMat read f x p = f x p := by
  simp only [jOracle, phaseOracleMat, Matrix.mulVec_diagonal]
  rcases p with ⟨_ | i, _ | _ | _, w⟩
  · simp [phaseSign]
  · simp [phaseSign]
  · simp [phaseSign]
  · simp [phaseSign]
  · simp [phaseSign]
  · exact absurd rfl (hp i w)

/-- The sector coordinates `(e, w) ↦ (some e, some true, w)` are distinct basis states, so a
nonnegative function sums over them to at most its full sum. -/
private lemma sum_sector_le (g : QBasis ι Bool W → ℝ) (hg : ∀ p, 0 ≤ g p) :
    ∑ e, ∑ w, g (some e, some true, w) ≤ ∑ p, g p := by
  calc ∑ e, ∑ w, g (some e, some true, w)
      ≤ ∑ e, ∑ t, ∑ w, g (some e, t, w) :=
        Finset.sum_le_sum fun e _ =>
          Finset.single_le_sum (f := fun t => ∑ w, g (some e, t, w))
            (fun t _ => Finset.sum_nonneg fun w _ => hg _) (Finset.mem_univ (some true))
    _ ≤ ∑ i : Option ι, ∑ t, ∑ w, g (i, t, w) := by
        rw [Fintype.sum_option]
        exact le_add_of_nonneg_left (Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun w _ => hg _)
    _ = ∑ p, g p := by simp only [Fintype.sum_prod_type]

/-- The sectors are orthogonal pieces: `∑ₑ ‖sector f e‖² ≤ ‖f‖²`. -/
theorem sum_jNormSq_sector_le (f : JVec X (QBasis ι Bool W)) :
    ∑ e, jNormSq (sector f e) ≤ jNormSq f := by
  simp only [jNormSq, qNormSq_def]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun x _ =>
    sum_sector_le (fun p => Complex.normSq (f x p)) fun p => Complex.normSq_nonneg _

/-- `‖sector f e‖∞ ≤ ‖f‖∞`. -/
theorem FinDist.infNormSq_sector_le {Ω : Type} [Fintype Ω] [DecidableEq Ω] (ρ : FinDist Ω)
    (f : JVec ρ.Supp (QBasis ι Bool W)) (e : ι) :
    ρ.infNormSq (sector f e) ≤ ρ.infNormSq f := by
  refine ρ.infNormSq_le fun x => le_trans ?_ (ρ.qNormSq_wvec_le_infNormSq f x)
  have hw : ρ.wvec (sector f e) x = fun w => ρ.wvec f x (some e, some true, w) := rfl
  rw [hw, qNormSq_def, qNormSq_def]
  have hnn : ∀ p, 0 ≤ Complex.normSq (ρ.wvec f x p) := fun p => Complex.normSq_nonneg _
  refine le_trans ?_ (sum_sector_le _ hnn)
  exact Finset.single_le_sum (f := fun e => ∑ w, Complex.normSq (ρ.wvec f x (some e, some true, w)))
    (fun e _ => Finset.sum_nonneg fun w _ => hnn _) (Finset.mem_univ e)

end Phase

end QuantumQueryComplexity
