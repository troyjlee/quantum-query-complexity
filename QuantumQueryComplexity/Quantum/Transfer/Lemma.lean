import QuantumQueryComplexity.Quantum.JointState.Oracle

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The transfer lemma

Run one circuit, with workspace unitaries `U₀, U₁, …`, on two input registers `X` and `Y`
with oracles `O_X` and `O_Y`.  Started from `f₀` on `X` the run is `Ψₜ`; started from `g₀` on
`Y` it is `Φₜ` (`jRun`).  For any linear map `K : X → Y` acting on the input register,

  `‖Φₜ − KΨₜ‖ ≤ ‖g₀ − K f₀‖ + ∑_{j<t} ‖(O_Y K − K O_X) Ψⱼ‖`

(`jNorm_jRun_sub_mul_le`).  The proof is one line per step: `K` commutes with the workspace
unitary, and `O_Y` does not increase distances.  The per-step errors are arbitrary, so the
lemma serves both the uniform sector accounting of Cornelissen–Gilani–Zhou [CGZ, Theorem 4.1]
and the knowledge-operator recursion of Belovs [Bel26, Corollary 3.24], which starts the
target run from `g₀ = 0`.

## Main definitions

* `jNorm` — the norm of a joint vector, `√(jNormSq f)`.
* `jRun O U f₀` — the run of the steps `U` interleaved with the oracle `O`, started from `f₀`.

## Main results

* `jNorm_add_le` — the triangle inequality.
* `jNorm_jRun_sub_mul_le` — **the transfer lemma**.
* `FinDist.jointState_eq_jRun`, `FinDist.jointXorState_eq_jRun` — actual joint states are runs
  started from `|ρ⟩ ⊗ init`.
* `jNorm_jointXorState_sub_le` — the transfer lemma for an algorithm in the XOR model, with
  an arbitrary initial mismatch `‖|ρ⁺⟩ − K|ρ⁻⟩‖`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {X Y A : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype A]
  [DecidableEq A]

/-! ## The norm of a joint vector -/

/-- The norm `‖f‖` of a joint vector. -/
noncomputable def jNorm (f : JVec X A) : ℝ := Real.sqrt (jNormSq f)

lemma jNorm_nonneg (f : JVec X A) : 0 ≤ jNorm f := Real.sqrt_nonneg _

lemma jNorm_sq (f : JVec X A) : jNorm f ^ 2 = jNormSq f := Real.sq_sqrt (jNormSq_nonneg f)

/-- The squared norm of a joint vector is the squared norm of its flattening. -/
private lemma jNormSq_eq_qNormSq (f : JVec X A) :
    jNormSq f = qNormSq (fun p : X × A => f p.1 p.2) := by
  simp only [jNormSq, qNormSq_def, Fintype.sum_prod_type]

/-- An isometry `Mᴴ M = I` between input registers preserves the norm of joint vectors. -/
theorem jNorm_mul_of_isometry {M : Matrix Y X ℂ} (hM : Mᴴ * M = 1) (f : JVec X A) :
    jNorm (M * f) = jNorm f := by
  rw [jNorm, jNorm, jNormSq_mul_of_isometry hM]

@[simp] lemma jNorm_zero : jNorm (0 : JVec X A) = 0 := by
  rw [jNorm, jNormSq_eq_qNormSq]
  simp [qNormSq_def]

lemma jNorm_neg (f : JVec X A) : jNorm (-f) = jNorm f := by
  simp only [jNorm, jNormSq_eq_qNormSq, qNormSq_def, Matrix.neg_apply, Complex.normSq_neg]

lemma jNorm_sub_comm (f g : JVec X A) : jNorm (f - g) = jNorm (g - f) := by
  rw [← jNorm_neg, neg_sub]

/-- **The triangle inequality.** -/
theorem jNorm_add_le (f g : JVec X A) : jNorm (f + g) ≤ jNorm f + jNorm g := by
  simp only [jNorm, jNormSq_eq_qNormSq]
  exact sqrt_qNormSq_add_le (fun p : X × A => f p.1 p.2) (fun p : X × A => g p.1 p.2)

theorem jNorm_sub_le (f g h : JVec X A) : jNorm (f - h) ≤ jNorm (f - g) + jNorm (g - h) := by
  simpa only [sub_add_sub_cancel] using jNorm_add_le (f - g) (g - h)

lemma wsOp_sub (U : Matrix A A ℂ) (f g : JVec X A) : wsOp U (f - g) = wsOp U f - wsOp U g := by
  simp only [wsOp_eq_mul_transpose, Matrix.sub_mul]

/-- Workspace unitaries preserve the norm. -/
theorem jNorm_wsOp_of_mem_unitaryGroup {U : Matrix A A ℂ} (hU : U ∈ Matrix.unitaryGroup A ℂ)
    (f : JVec X A) : jNorm (wsOp U f) = jNorm f := by
  rw [jNorm, jNorm, jNormSq_wsOp_of_mem_unitaryGroup hU]

section JointOracle

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

lemma jOracle_sub (O : (ι → σ) → Matrix A A ℂ) (read : X → ι → σ) (f g : JVec X A) :
    jOracle O read (f - g) = jOracle O read f - jOracle O read g := by
  funext x
  exact Matrix.mulVec_sub _ _ _

/-- A joint oracle made of unitaries preserves the norm. -/
theorem jNorm_jOracle_of_mem_unitaryGroup {O : (ι → σ) → Matrix A A ℂ}
    (hO : ∀ a, O a ∈ Matrix.unitaryGroup A ℂ) (read : X → ι → σ) (f : JVec X A) :
    jNorm (jOracle O read f) = jNorm f := by
  simp only [jNorm, jNormSq, jOracle, qNormSq_mulVec (hO _)]

/-- A joint oracle made of unitaries does not increase distances. -/
theorem jNorm_jOracle_sub_jOracle {O : (ι → σ) → Matrix A A ℂ}
    (hO : ∀ a, O a ∈ Matrix.unitaryGroup A ℂ) (read : X → ι → σ) (f g : JVec X A) :
    jNorm (jOracle O read f - jOracle O read g) = jNorm (f - g) := by
  rw [← jOracle_sub, jNorm_jOracle_of_mem_unitaryGroup hO]

end JointOracle

/-! ## Product vectors -/

/-! Input-register operators act on the first factor of a product vector `k ⊗ ψ`: this is
Mathlib's `Matrix.mul_vecMulVec`. -/

/-- `‖k ⊗ ψ‖ = ‖k‖ ‖ψ‖`. -/
theorem jNorm_vecMulVec (k : X → ℂ) (ψ : A → ℂ) :
    jNorm (vecMulVec k ψ) = Real.sqrt (qNormSq k) * Real.sqrt (qNormSq ψ) := by
  have h : jNormSq (vecMulVec k ψ) = qNormSq k * qNormSq ψ := by
    simp only [jNormSq, qNormSq_def, vecMulVec_apply, Complex.normSq_mul, Finset.sum_mul_sum]
  rw [jNorm, h, Real.sqrt_mul (qNormSq_nonneg k)]

/-! ## Runs and the transfer lemma -/

/-- **The run** of the workspace steps `U` interleaved with the oracle `O`, started from the
joint vector `f₀`: `jRun O U f₀ 0 = U₀ f₀` and `jRun O U f₀ (t + 1) = U_{t+1} (O (jRun O U f₀ t))`.
This is the `QAlg.state` recursion with the input register kept in superposition. -/
def jRun (O : JVec X A → JVec X A) (U : ℕ → Matrix A A ℂ) (f₀ : JVec X A) : ℕ → JVec X A
  | 0 => wsOp (U 0) f₀
  | t + 1 => wsOp (U (t + 1)) (O (jRun O U f₀ t))

@[simp] lemma jRun_zero (O : JVec X A → JVec X A) (U : ℕ → Matrix A A ℂ) (f₀ : JVec X A) :
    jRun O U f₀ 0 = wsOp (U 0) f₀ := rfl

@[simp] lemma jRun_succ (O : JVec X A → JVec X A) (U : ℕ → Matrix A A ℂ) (f₀ : JVec X A)
    (t : ℕ) : jRun O U f₀ (t + 1) = wsOp (U (t + 1)) (O (jRun O U f₀ t)) := rfl

/-- **The transfer lemma.**  Run the same unitary steps `U` with oracle `OX` from `f₀` and with
oracle `OY` from `g₀`.  If `OY` does not increase distances and the error of the map `K`
under the `j`-th query is at most `ε j` on the states the first run actually visits, then

  `‖Φₜ − KΨₜ‖ ≤ ‖g₀ − K f₀‖ + ∑_{j<t} ε j`.

`K` need not be a contraction, and `OX`, `OY` need not be linear. -/
theorem jNorm_jRun_sub_mul_le (K : Matrix Y X ℂ) (OX : JVec X A → JVec X A)
    (OY : JVec Y A → JVec Y A) (hOY : ∀ g h, jNorm (OY g - OY h) ≤ jNorm (g - h))
    {U : ℕ → Matrix A A ℂ} (hU : ∀ t, U t ∈ Matrix.unitaryGroup A ℂ) (f₀ : JVec X A)
    (g₀ : JVec Y A) (ε : ℕ → ℝ) (t : ℕ)
    (hε : ∀ j < t, jNorm (OY (K * jRun OX U f₀ j) - K * OX (jRun OX U f₀ j)) ≤ ε j) :
    jNorm (jRun OY U g₀ t - K * jRun OX U f₀ t)
      ≤ jNorm (g₀ - K * f₀) + ∑ j ∈ Finset.range t, ε j := by
  induction t with
  | zero =>
    rw [jRun_zero, jRun_zero, mul_wsOp, ← wsOp_sub, jNorm_wsOp_of_mem_unitaryGroup (hU 0),
      Finset.sum_range_zero, add_zero]
  | succ t ih =>
    rw [jRun_succ, jRun_succ, mul_wsOp, ← wsOp_sub, jNorm_wsOp_of_mem_unitaryGroup (hU _),
      Finset.sum_range_succ]
    have h1 := ih fun j hj => hε j (Nat.lt_succ_of_lt hj)
    have h2 := hε t (Nat.lt_succ_self t)
    have h3 := hOY (jRun OY U g₀ t) (K * jRun OX U f₀ t)
    have h4 := jNorm_sub_le (OY (jRun OY U g₀ t)) (OY (K * jRun OX U f₀ t))
      (K * OX (jRun OX U f₀ t))
    linarith

/-! ## Joint states of algorithms are runs -/

/-- Row `x` of the product vector `k ⊗ ψ` is `k x • ψ`. -/
theorem vecMulVec_row (k : X → ℂ) (ψ : A → ℂ) (x : X) : vecMulVec k ψ x = k x • ψ := by
  funext a
  rw [vecMulVec_apply, Pi.smul_apply, smul_eq_mul]

section Algorithm

variable {ι σ O W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

namespace FinDist

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] (ρ : FinDist Ω)

/-- The joint state (value oracle) is the run started from `|ρ⟩ ⊗ init`. -/
theorem jointState_eq_jRun (read : Ω → ι → σ) (A : QAlg ι σ O W) (t : ℕ) :
    ρ.jointState read A t
      = jRun (jOracle oracleMat (fun x : ρ.Supp => read x)) A.step (vecMulVec ρ.ket A.init) t := by
  induction t with
  | zero =>
    rw [jointState_zero, jRun_zero]
    funext x
    rw [wsOp, vecMulVec_row, Matrix.mulVec_smul]
  | succ t ih => rw [jointState_succ, jRun_succ, ih]

/-- The joint state (XOR oracle) is the run started from `|ρ⟩ ⊗ init`. -/
theorem jointXorState_eq_jRun (read : Ω → ι → Bool) (A : QAlg ι Bool O W) (t : ℕ) :
    ρ.jointXorState read A t
      = jRun (jOracle xorOracleMat (fun x : ρ.Supp => read x)) A.step
          (vecMulVec ρ.ket A.init) t := by
  induction t with
  | zero =>
    rw [jointXorState_zero, jRun_zero]
    funext x
    rw [wsOp, vecMulVec_row, Matrix.mulVec_smul]
  | succ t ih => rw [jointXorState_succ, jRun_succ, ih]

end FinDist

/-- **The transfer lemma for an algorithm** (XOR model).  Run `A` on inputs drawn from `ρm`
(read through `readM`) and from `ρp` (read through `readP`).  For any map `K` between the two
input registers,

  `‖Ψ⁺ₜ − KΨ⁻ₜ‖ ≤ ‖|ρp⟩ − K|ρm⟩‖ + ∑_{j<t} ε j`

whenever `ε j` bounds the error `‖(O⁺K − KO⁻)Ψ⁻ⱼ‖` of the `j`-th query. -/
theorem jNorm_jointXorState_sub_le {Ωm Ωp : Type} [Fintype Ωm] [DecidableEq Ωm] [Fintype Ωp]
    [DecidableEq Ωp] (ρm : FinDist Ωm) (readM : Ωm → ι → Bool) (ρp : FinDist Ωp)
    (readP : Ωp → ι → Bool) (K : Matrix ρp.Supp ρm.Supp ℂ) (A : QAlg ι Bool O W) (ε : ℕ → ℝ)
    (t : ℕ)
    (hε : ∀ j < t,
      jNorm (jOracle xorOracleMat (fun y : ρp.Supp => readP y) (K * ρm.jointXorState readM A j)
        - K * jOracle xorOracleMat (fun x : ρm.Supp => readM x) (ρm.jointXorState readM A j))
        ≤ ε j) :
    jNorm (ρp.jointXorState readP A t - K * ρm.jointXorState readM A t)
      ≤ Real.sqrt (qNormSq (ρp.ket - K *ᵥ ρm.ket)) + ∑ j ∈ Finset.range t, ε j := by
  simp only [FinDist.jointXorState_eq_jRun] at hε ⊢
  refine (jNorm_jRun_sub_mul_le K _ _ (fun g h => (jNorm_jOracle_sub_jOracle
    (fun a => xorOracleMat_mem_unitaryGroup a) _ g h).le) A.step_unitary _ _ ε t hε).trans_eq ?_
  rw [Matrix.mul_vecMulVec, ← Matrix.sub_vecMulVec, jNorm_vecMulVec,
    (A.init_isQState : qNormSq A.init = 1), Real.sqrt_one, mul_one]

end Algorithm

end QuantumQueryComplexity
