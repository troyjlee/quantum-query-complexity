import QuantumQueryComplexity.Quantum.Simulation
import QuantumQueryComplexity.Quantum.Relation
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.RootsOfUnity.Complex

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Oracles over `Z_q`: additive and phase

For inputs `a : ι → ZMod q`, two oracles act on the library's basis `QBasis ι (ZMod q) W` (index
register `Option ι`, answer register `Option (ZMod q)`, workspace `W`); both fix the idle index
and the blank answer:

* the **additive oracle** `|i, c⟩ ↦ |i, c + aᵢ⟩` (`addOracleMat`), a basis permutation;
* the **phase oracle** `|i, c⟩ ↦ ω_q^{c·aᵢ}|i, c⟩` with `ω_q = e^{2πi/q}` (`phaseZqOracleMat`),
  the oracle of [Bel26, (3.3)].

They are conjugate by the Fourier transform on the `some`-part of the answer register
(`ansFourierZq`, entries `ω_q^{−bc}/√q`): `addOracleMat a = F · phaseZqOracleMat a · F†`
(`addOracleMat_eq_fourier_phase`). For `q = 2` these are the library's XOR and phase oracles.

The **phase-oracle model** runs a `QAlg` with the phase oracle in place of the value oracle
(`zqState`), and `zqSuccessProbOn` is its relational success probability. The library's value
oracle is simulated in the phase model at **two phase queries per value query**, with exactly the
same success on every input and for every relation (`zqSuccessProbOn_simStdToZq`,
`ZqSimulation.lean`).
-/

namespace QuantumQueryComplexity

open scoped Matrix Kronecker
open Matrix

variable {ι O W : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
variable {q : ℕ} [NeZero q]

/-! ## The additive oracle -/

/-- The additive oracle on a basis state: add `aᵢ` to the `some`-part of the answer register of a
query to `i`. -/
def addOracleMap (a : ι → ZMod q) : QBasis ι (ZMod q) W → QBasis ι (ZMod q) W
  | (some i, t, w) => (some i, t.map (· + a i), w)
  | p => p

/-- The additive oracle as a permutation (its inverse adds `−aᵢ`). -/
def addOraclePerm (a : ι → ZMod q) : Equiv.Perm (QBasis ι (ZMod q) W) where
  toFun := addOracleMap a
  invFun := addOracleMap (-a)
  left_inv := by
    rintro ⟨_ | i, _ | c, w⟩ <;> simp [addOracleMap]
  right_inv := by
    rintro ⟨_ | i, _ | c, w⟩ <;> simp [addOracleMap]

/-- **The additive oracle over `Z_q`.** -/
def addOracleMat (a : ι → ZMod q) : Matrix (QBasis ι (ZMod q) W) (QBasis ι (ZMod q) W) ℂ :=
  qPerm (addOraclePerm a)

theorem addOracleMat_mem_unitaryGroup (a : ι → ZMod q) :
    addOracleMat (W := W) a ∈ Matrix.unitaryGroup (QBasis ι (ZMod q) W) ℂ := by
  exact qPerm_mem_unitaryGroup _

/-! ## The phase oracle -/

/-- The primitive `q`-th root of unity `ω_q = e^{2πi/q}`. -/
noncomputable def zqRoot (q : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)

/-- The character `ω_q^{c·x}` of `Z_q`. -/
noncomputable def zqChar (c x : ZMod q) : ℂ := zqRoot q ^ (c * x).val

/-- `ω_q` is a primitive `q`-th root of unity. -/
theorem zqRoot_isPrimitiveRoot : IsPrimitiveRoot (zqRoot q) q :=
  Complex.isPrimitiveRoot_exp q (NeZero.ne q)

/-- `ω_q^q = 1`. -/
theorem zqRoot_pow_q : zqRoot q ^ q = 1 :=
  zqRoot_isPrimitiveRoot.pow_eq_one

/-- `|ω_q| = 1`. -/
theorem norm_zqRoot : ‖zqRoot q‖ = 1 :=
  zqRoot_isPrimitiveRoot.norm'_eq_one (NeZero.ne q)

/-- `k ↦ ω_q^{k.val}` is additive on `ZMod q`. -/
private lemma zqRoot_pow_val_add (k l : ZMod q) :
    zqRoot q ^ (k + l).val = zqRoot q ^ k.val * zqRoot q ^ l.val := by
  rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ zqRoot_pow_q]

/-- Conjugation inverts `ω_q^{k.val}`. -/
private lemma star_zqRoot_pow_val (k : ZMod q) :
    star (zqRoot q ^ k.val) = zqRoot q ^ (-k).val := by
  have h : zqRoot q ^ (-k).val * zqRoot q ^ k.val = 1 := by
    rw [← zqRoot_pow_val_add, neg_add_cancel, ZMod.val_zero, pow_zero]
  rw [eq_inv_of_mul_eq_one_left h, star_pow, ← inv_pow, Complex.inv_eq_conj norm_zqRoot,
    starRingEnd_apply]

/-- `ω_q^{c·x}` is symmetric in `c` and `x`. -/
theorem zqChar_comm (c x : ZMod q) : zqChar c x = zqChar x c := by
  rw [zqChar, zqChar, mul_comm]

/-- `zqChar` is additive in its first argument. -/
theorem zqChar_add_left (c c' x : ZMod q) : zqChar (c + c') x = zqChar c x * zqChar c' x := by
  rw [zqChar, zqChar, zqChar, add_mul, zqRoot_pow_val_add]

/-- `zqChar` is additive in its second argument. -/
theorem zqChar_add_right (c x x' : ZMod q) : zqChar c (x + x') = zqChar c x * zqChar c x' := by
  rw [zqChar_comm, zqChar_add_left, zqChar_comm x, zqChar_comm x']

/-- The trivial character. -/
@[simp] theorem zqChar_zero_left (x : ZMod q) : zqChar 0 x = 1 := by
  rw [zqChar, zero_mul, ZMod.val_zero, pow_zero]

/-- Conjugating a character negates its frequency. -/
theorem star_zqChar (c x : ZMod q) : star (zqChar c x) = zqChar (-c) x := by
  rw [zqChar, zqChar, star_zqRoot_pow_val, neg_mul]

/-- Characters have modulus one. -/
theorem zqChar_mul_star (c x : ZMod q) : zqChar c x * star (zqChar c x) = 1 := by
  rw [star_zqChar, ← zqChar_add_left, add_neg_cancel, zqChar_zero_left]

/-- **Character orthogonality over `Z_q`**: `∑ₓ ω_q^{c·x} = q·[c = 0]`. -/
theorem sum_zqChar (c : ZMod q) : ∑ x, zqChar c x = if c = 0 then (q : ℂ) else 0 := by
  split_ifs with hc
  · simp [hc, ZMod.card]
  · have h1 : zqChar c 1 ≠ 1 := by
      rw [zqChar, mul_one]
      exact zqRoot_isPrimitiveRoot.pow_ne_one_of_pos_of_lt ((ZMod.val_ne_zero c).mpr hc)
        (ZMod.val_lt c)
    have hS : zqChar c 1 * ∑ x, zqChar c x = ∑ x, zqChar c x := by
      rw [Finset.mul_sum]
      simp_rw [← zqChar_add_right]
      exact Equiv.sum_comp (Equiv.addLeft 1) (zqChar c)
    have h0 : (zqChar c 1 - 1) * ∑ x, zqChar c x = 0 := by rw [sub_mul, hS, one_mul, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr h1)

/-- The phase of the phase oracle at a basis state: `ω_q^{c·aᵢ}` at `(some i, some c, w)`, and
`1` elsewhere. -/
noncomputable def phaseZqSign (a : ι → ZMod q) : QBasis ι (ZMod q) W → ℂ
  | (some i, some c, _) => zqChar c (a i)
  | _ => 1

/-- **The phase oracle over `Z_q`** [Bel26, (3.3)]. -/
noncomputable def phaseZqOracleMat (a : ι → ZMod q) :
    Matrix (QBasis ι (ZMod q) W) (QBasis ι (ZMod q) W) ℂ :=
  Matrix.diagonal (phaseZqSign a)

theorem phaseZqOracleMat_mem_unitaryGroup (a : ι → ZMod q) :
    phaseZqOracleMat (W := W) a ∈ Matrix.unitaryGroup (QBasis ι (ZMod q) W) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, phaseZqOracleMat, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext p
  rcases p with ⟨_ | i, _ | c, w⟩ <;>
    simp only [phaseZqSign, Pi.star_apply, star_one, mul_one, zqChar_mul_star]

/-! ## The Fourier bridge -/

/-- **The Fourier transform on the answer register**: `|b⟩ ↦ ∑_c ω_q^{−bc}/√q |c⟩` on the
`some`-part, the identity on the blank answer, the identity on the index and the workspace. -/
noncomputable def ansFourierZq : Matrix (QBasis ι (ZMod q) W) (QBasis ι (ZMod q) W) ℂ :=
  fun p p' =>
    if p.1 = p'.1 ∧ p.2.2 = p'.2.2 then
      match p.2.1, p'.2.1 with
      | none, none => 1
      | some b, some c => zqChar (-b) c / ((Real.sqrt q : ℝ) : ℂ)
      | _, _ => 0
    else 0

/-- The Fourier transform on `Option (ZMod q)`: the DFT on the `some`-part, fixing `none`. -/
private noncomputable def ansFourierBlock : Matrix (Option (ZMod q)) (Option (ZMod q)) ℂ
  | none, none => 1
  | some b, some c => zqChar (-b) c / ((Real.sqrt q : ℝ) : ℂ)
  | _, _ => 0

/-- `ansFourierZq` is `1 ⊗ F ⊗ 1` for the answer-register block `F`. -/
private lemma ansFourierZq_eq_kronecker :
    ansFourierZq (ι := ι) (W := W) (q := q) =
      (1 : Matrix (Option ι) (Option ι) ℂ) ⊗ₖ (ansFourierBlock ⊗ₖ (1 : Matrix W W ℂ)) := by
  ext ⟨i, t, w⟩ ⟨j, s, v⟩
  rcases t with _ | b <;> rcases s with _ | c <;>
    by_cases hij : i = j <;> by_cases hwv : w = v <;>
    simp [ansFourierZq, ansFourierBlock, hij, hwv]

/-- The answer-register block of the Fourier transform is unitary. -/
private lemma ansFourierBlock_mul_conjTranspose :
    ansFourierBlock (q := q) * ansFourierBlockᴴ = 1 := by
  have hq : ((Real.sqrt q : ℝ) : ℂ) ^ 2 = q := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  ext t s
  rw [Matrix.mul_apply, Fintype.sum_option]
  rcases t with _ | b <;> rcases s with _ | b'
  · simp [ansFourierBlock]
  · simp [ansFourierBlock]
  · simp [ansFourierBlock]
  · have key : ∀ c, ansFourierBlock (some b) (some c) * ansFourierBlockᴴ (some c) (some b')
        = zqChar (b' + -b) c / q := by
      intro c
      simp only [ansFourierBlock, Matrix.conjTranspose_apply, star_div₀, star_zqChar, neg_neg,
        Complex.star_def, Complex.conj_ofReal, div_mul_div_comm, ← sq, hq]
      rw [zqChar_add_left, mul_comm]
    simp only [key, ← Finset.sum_div, sum_zqChar, add_neg_eq_zero]
    simp only [ansFourierBlock, Matrix.conjTranspose_apply, star_zero, mul_zero, zero_add,
      Matrix.one_apply, Option.some.injEq]
    by_cases h : b = b'
    · simp [h, hq0]
    · simp [h, Ne.symm h]

theorem ansFourierZq_mem_unitaryGroup :
    ansFourierZq (ι := ι) (W := W) (q := q) ∈ Matrix.unitaryGroup (QBasis ι (ZMod q) W) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ansFourierZq_eq_kronecker,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ansFourierBlock_mul_conjTranspose, Matrix.mul_one, Matrix.mul_one, Matrix.one_kronecker_one,
    Matrix.one_kronecker_one]

/-- Left multiplication by a permutation unitary permutes the rows. -/
private lemma qPerm_mul_apply {H : Type*} [Fintype H] [DecidableEq H] (e : Equiv.Perm H)
    (M : Matrix H H ℂ) (p p' : H) : (qPerm e * M) p p' = M (e.symm p) p' :=
  qPerm_mulVec_apply e (fun r => M r p') p

/-- **The intertwining relation** `T_a F = F P_a`. -/
private lemma addOracleMat_mul_ansFourierZq (a : ι → ZMod q) :
    addOracleMat (W := W) a * ansFourierZq = ansFourierZq * phaseZqOracleMat a := by
  ext ⟨i, t, w⟩ ⟨j, s, v⟩
  rw [addOracleMat, qPerm_mul_apply, phaseZqOracleMat, Matrix.mul_diagonal]
  rcases i with _ | i
  · rcases t with _ | b <;> rcases j with _ | j <;> rcases s with _ | c <;>
      simp [ansFourierZq, addOraclePerm, addOracleMap, phaseZqSign]
  rcases t with _ | b
  · rcases j with _ | j <;> rcases s with _ | c <;>
      simp [ansFourierZq, addOraclePerm, addOracleMap, phaseZqSign]
  rcases j with _ | j
  · rcases s with _ | c <;> simp [ansFourierZq, addOraclePerm, addOracleMap, phaseZqSign]
  rcases s with _ | c
  · simp [ansFourierZq, addOraclePerm, addOracleMap, phaseZqSign]
  simp only [ansFourierZq, addOraclePerm, Equiv.symm_mk, Equiv.coe_fn_mk, addOracleMap,
    Pi.neg_apply, Option.map_some, Option.some.injEq, neg_add_rev, neg_neg, phaseZqSign, ite_mul,
    zero_mul]
  by_cases h : i = j ∧ w = v
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, ↓reduceIte]
    rw [div_mul_eq_mul_div, zqChar_comm c (a i), ← zqChar_add_left, add_comm]
  · simp only [h, ↓reduceIte]

/-- **The additive oracle is the Fourier conjugate of the phase oracle.** -/
theorem addOracleMat_eq_fourier_phase (a : ι → ZMod q) :
    addOracleMat (W := W) a = ansFourierZq * phaseZqOracleMat a * ansFourierZqᴴ := by
  have hF := ansFourierZq_mem_unitaryGroup (ι := ι) (W := W) (q := q)
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hF
  rw [← addOracleMat_mul_ansFourierZq, Matrix.mul_assoc, hF, Matrix.mul_one]

/-! ## The phase-oracle model -/

/-- **The state of `A` on input `a` after `t` phase queries over `Z_q`.** -/
noncomputable def zqState (A : QAlg ι (ZMod q) O W) (a : ι → ZMod q) :
    ℕ → (QBasis ι (ZMod q) W → ℂ)
  | 0 => A.step 0 *ᵥ A.init
  | t + 1 => A.step (t + 1) *ᵥ (phaseZqOracleMat a *ᵥ zqState A a t)

@[simp] lemma zqState_zero (A : QAlg ι (ZMod q) O W) (a : ι → ZMod q) :
    zqState A a 0 = A.step 0 *ᵥ A.init := rfl

@[simp] lemma zqState_succ (A : QAlg ι (ZMod q) O W) (a : ι → ZMod q) (t : ℕ) :
    zqState A a (t + 1) = A.step (t + 1) *ᵥ (phaseZqOracleMat a *ᵥ zqState A a t) := rfl

variable {X : Type} [Fintype X]

/-- **Relational success in the phase-oracle model**: the probability that `A`, after `t` phase
queries on `read x`, outputs a value valid for `x`. -/
noncomputable def zqSuccessProbOn (A : QAlg ι (ZMod q) O W) (t : ℕ) (read : X → ι → ZMod q)
    (Good : X → O → Prop) [∀ x, DecidablePred (Good x)] (x : X) : ℝ :=
  goodProb A.readout (Good x) (zqState A (read x) t)

end QuantumQueryComplexity
