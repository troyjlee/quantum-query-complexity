import QuantumQueryComplexity.Quantum.Records.Interaction

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Phase queries and conditional differences

For Boolean inputs, the phase operator `Qₑ` multiplies the workspace vector at `x` by
`(−1)^{xₑ}` (Cornelissen–Gilani–Zhou (3.3)); a controlled query applies it on the components
with query index `e`.  Its commutator with the conditional difference at `e` is
`Kₑ = [Dₑ, Qₑ]` (CGZ (4.13), `FinDist.recordComm`): it creates or removes a record at `e`.

* For every distribution, queries commute with the conditional differences at other
  coordinates, so `[H, Qₑ] = wₑ Kₑ` for `H = ∑ⱼ wⱼ Dⱼ`, and Lemma 4.2's commutator identity
  gives `[Qₑ, F] = (wₑ/R) F Kₑ F` (CGZ (4.15)).
* For conditioned Bernoulli bits, `‖Kₑ‖ ≤ 2√p` and `‖Kₑ f‖∞ ≤ 2‖f‖∞` (CGZ (4.14)), hence
  `‖[Qₑ, F]‖ ≤ 2wₑ√p / R`.
* For `i ≠ e`, the Jacobi identity gives `[Dᵢ, Kₑ] = [[Dᵢ, Dₑ], Qₑ]`, so `‖[Dᵢ, Kₑ]‖ ≤ 2p` by
  (4.17) (CGZ (5.33); the statement is general, though the paper uses it only in Section 5).

Norm bounds are stated as operator inequalities `X†X ≤ c I`, which give `‖X f‖² ≤ c ‖f‖²` on
every workspace by `jNormSq_mul_le_smul`.
-/

namespace QuantumQueryComplexity

open scoped Matrix MatrixOrder ComplexOrder
open Matrix

variable {ι A : Type} [Fintype ι] [DecidableEq ι] [Fintype A]

/-! ### Order helpers -/

section OrderHelpers

variable {X : Type} [Fintype X] [DecidableEq X]

/-- Conjugation preserves the Loewner order. -/
private lemma conj_le_conj {B C : Matrix X X ℂ} (h : B ≤ C) (M : Matrix X X ℂ) :
    Mᴴ * B * M ≤ Mᴴ * C * M := by
  rw [Matrix.le_iff] at h ⊢
  have := h.conjTranspose_mul_mul_same M
  rwa [Matrix.mul_sub, Matrix.sub_mul] at this

/-- Nonnegative real scaling preserves the Loewner order. -/
private lemma real_smul_le_smul {B C : Matrix X X ℂ} (h : B ≤ C) {r : ℝ} (hr : 0 ≤ r) :
    (r : ℂ) • B ≤ (r : ℂ) • C := by
  rw [Matrix.le_iff] at h ⊢
  rw [← smul_sub]
  exact h.smul (Complex.zero_le_real.mpr hr)

/-- `(a − b)†(a − b) ≤ 2 a†a + 2 b†b`: the difference is `(a + b)†(a + b)`. -/
private lemma sub_sq_le_two_smul (a b : Matrix X X ℂ) :
    (a - b)ᴴ * (a - b) ≤ ((2 : ℝ) : ℂ) • (aᴴ * a) + ((2 : ℝ) : ℂ) • (bᴴ * b) := by
  rw [Matrix.le_iff]
  have h : ((2 : ℝ) : ℂ) • (aᴴ * a) + ((2 : ℝ) : ℂ) • (bᴴ * b) - (a - b)ᴴ * (a - b)
      = (a + b)ᴴ * (a + b) := by
    simp only [conjTranspose_add, conjTranspose_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_mul, Matrix.mul_sub]
    push_cast
    module
  rw [h]
  exact posSemidef_conjTranspose_mul_self _

/-- An operator-norm bound from the norm bound on one-dimensional workspaces. -/
private lemma conjTranspose_mul_self_le_of_jNormSq {B : Matrix X X ℂ} {c : ℝ}
    (h : ∀ f : JVec X Unit, jNormSq (B * f) ≤ c * jNormSq f) :
    Bᴴ * B ≤ (c : ℂ) • (1 : Matrix X X ℂ) := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
  · set f : JVec X Unit := Matrix.of fun x _ => v x with hf
    have hq : ∀ M : Matrix X X ℂ, star v ⬝ᵥ (M *ᵥ v) = jInner f (M * f) := by
      intro M
      simp [hf, jInner, qInner_def, dotProduct, Matrix.mul_apply, Matrix.mulVec]
    have h2 : jInner f (((c : ℂ) • (1 : Matrix X X ℂ) - Bᴴ * B) * f)
        = (c : ℂ) * jInner f f - jInner (B * f) (B * f) := by
      rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, jInner_eq_trace,
        jInner_eq_trace, jInner_eq_trace, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub,
        Matrix.trace_smul, smul_eq_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [hq, h2, jInner_self, jInner_self, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    exact Complex.zero_le_real.mpr (by linarith [h f])

end OrderHelpers

namespace FinDist

variable (ρ : FinDist (ι → Bool))

/-- **The phase operator** `Qₑ`: `(Qₑ f)ˣ = (−1)^{xₑ} fˣ` on the input register. -/
noncomputable def phaseOp (e : ι) : Matrix ρ.Supp ρ.Supp ℂ :=
  ρ.coordDiag e fun b => if b then -1 else 1

theorem phaseOp_isHermitian (e : ι) : (ρ.phaseOp e).IsHermitian := by
  unfold phaseOp coordDiag
  refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
  funext x
  cases h : x.1 e <;> simp [h]

theorem phaseOp_mul_self (e : ι) : ρ.phaseOp e * ρ.phaseOp e = 1 := by
  unfold phaseOp coordDiag
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext x
  cases x.1 e <;> simp

/-- **`Kₑ = [Dₑ, Qₑ]`** (CGZ (4.13)). -/
noncomputable def recordComm (e : ι) : Matrix ρ.Supp ρ.Supp ℂ :=
  ρ.condDiff e * ρ.phaseOp e - ρ.phaseOp e * ρ.condDiff e

/-- `[H, Qₑ] = wₑ Kₑ` for `H = ∑ⱼ wⱼ Dⱼ`, for every distribution. -/
theorem varOp_comm_phaseOp (w : ι → ℝ) (e : ι) :
    ρ.varOp w * ρ.phaseOp e - ρ.phaseOp e * ρ.varOp w = ((w e : ℝ) : ℂ) • ρ.recordComm e := by
  unfold varOp
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single_of_mem e (Finset.mem_univ e)]
  · rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, recordComm]
  · intro j _ hj
    have hc := (ρ.commute_condDiff_coordDiag hj (fun b : Bool => if b then (-1 : ℂ) else 1)).eq
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, phaseOp, hc, sub_self, smul_zero]

/-- **(4.15), the identity** `[Qₑ, F] = (wₑ/R) F Kₑ F`, for every distribution. -/
theorem phaseOp_comm_resolvent {R : ℝ} {w : ι → ℝ} (hR : 0 < R) (hw : ∀ i, 0 ≤ w i) (e : ι) :
    ρ.phaseOp e * resolvent R (ρ.varOp w) - resolvent R (ρ.varOp w) * ρ.phaseOp e
      = ((w e / R : ℝ) : ℂ) •
          (resolvent R (ρ.varOp w) * ρ.recordComm e * resolvent R (ρ.varOp w)) := by
  rw [commutator_resolvent hR (varOp_posSemidef (ρ := ρ) hw), ρ.varOp_comm_phaseOp w e,
    mul_smul_comm, smul_mul_assoc, smul_smul]
  congr 1
  push_cast
  ring

/-! ### Workspace forms of the phase operator -/

private lemma wvec_sub' (f g : JVec ρ.Supp A) (x : ρ.Supp) :
    ρ.wvec (f - g) x = ρ.wvec f x - ρ.wvec g x := by
  funext a
  simp [wvec, mul_sub]

private lemma wvec_phaseOp_mul (e : ι) (f : JVec ρ.Supp A) (x : ρ.Supp) :
    ρ.wvec (ρ.phaseOp e * f) x = (if x.1 e then (-1 : ℂ) else 1) • ρ.wvec f x := by
  funext a
  simp only [wvec, phaseOp, coordDiag, Matrix.diagonal_mul, Pi.smul_apply, smul_eq_mul]
  ring

private lemma wvecAt_phaseOp_mul (e : ι) (f : JVec ρ.Supp A) (y : ι → Bool) :
    ρ.wvecAt (ρ.phaseOp e * f) y = (if y e then (-1 : ℂ) else 1) • ρ.wvecAt f y := by
  by_cases h : 0 < ρ.mass y
  · simp only [wvecAt, h, dite_true, wvec_phaseOp_mul]
  · simp [wvecAt, h]

private lemma qNormSq_wvecAt_le (f : JVec ρ.Supp A) (y : ι → Bool) :
    qNormSq (ρ.wvecAt f y) ≤ ρ.infNormSq f := by
  classical
  unfold wvecAt
  split_ifs with h
  · exact ρ.qNormSq_wvec_le_infNormSq f _
  · rw [qNormSq_zero]
    exact ρ.infNormSq_nonneg f

end FinDist

namespace CondBern

variable (μ : CondBern ι)

/-! ### Workspace form of `Kₑ` -/

/-- The coefficient of `Kₑ` at a free coordinate: `2p` at `xₑ = 0`, `−2(1 − p)` at `xₑ = 1`. -/
private noncomputable def kCoef (b : Bool) : ℝ := if b then -(2 * (1 - μ.p)) else 2 * μ.p

private lemma kCoef_sq_le (b : Bool) : μ.kCoef b * μ.kCoef b ≤ 4 := by
  have h0 := μ.p_pos
  have h1 := μ.p_le_half
  cases b <;> simp only [kCoef, Bool.false_eq_true, ite_true, ite_false] <;> nlinarith

/-- Flipping a free coordinate stays in the support. -/
private lemma flip_mass_pos (e : ι) (x : μ.dist.Supp) (h : μ.Free e x.1) :
    0 < μ.dist.mass (Function.update x.1 e (!x.1 e)) := by
  rw [μ.mass_pos_iff]
  cases hx : x.1 e
  · simpa [Free] using h
  · refine Avoids.mono ((μ.mass_pos_iff x.1).mp x.2) fun k hk => ?_
    by_cases hke : k = e
    · subst hke
      simp at hk
    · rwa [Function.update_of_ne hke] at hk

/-- **(4.14), workspace form**: at a free coordinate `(Kₑ f)⁰ = 2p f¹` and
`(Kₑ f)¹ = −2(1 − p) f⁰`; at a forced coordinate `Kₑ f = 0`. -/
private lemma wvec_recordComm_mul (e : ι) (f : JVec μ.dist.Supp A) (x : μ.dist.Supp) :
    μ.dist.wvec (μ.dist.recordComm e * f) x =
      if μ.Free e x.1 then
        ((μ.kCoef (x.1 e) : ℝ) : ℂ) • μ.dist.wvecAt f (Function.update x.1 e (!x.1 e))
      else 0 := by
  rw [FinDist.recordComm, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    FinDist.wvec_sub']
  simp only [μ.wvec_condDiff_mul, FinDist.wvec_phaseOp_mul, FinDist.wvecAt_phaseOp_mul]
  by_cases hfree : μ.Free e x.1
  · simp only [hfree, ite_true, Function.update_self]
    cases hx : x.1 e <;> simp only [kCoef, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      ite_true, ite_false] <;> push_cast <;> module
  · simp [hfree]

/-! ### The free-pair involution -/

/-- Flip coordinate `e` where it is free; fix the point where it is forced. -/
private noncomputable def flipAt (e : ι) (x : μ.dist.Supp) : μ.dist.Supp :=
  if h : μ.Free e x.1 then ⟨Function.update x.1 e (!x.1 e), μ.flip_mass_pos e x h⟩ else x

private lemma flipAt_val (e : ι) {x : μ.dist.Supp} (h : μ.Free e x.1) :
    (μ.flipAt e x).1 = Function.update x.1 e (!x.1 e) := by
  simp [flipAt, h]

private lemma agreeOff_flipAt (e : ι) (x : μ.dist.Supp) : AgreeOff e x.1 (μ.flipAt e x).1 := by
  intro j hj
  by_cases h : μ.Free e x.1
  · rw [μ.flipAt_val e h, Function.update_of_ne hj]
  · simp [flipAt, h]

private lemma flipAt_flipAt (e : ι) (x : μ.dist.Supp) : μ.flipAt e (μ.flipAt e x) = x := by
  by_cases h : μ.Free e x.1
  · have h' : μ.Free e (μ.flipAt e x).1 := (μ.free_congr (μ.agreeOff_flipAt e x)).mp h
    apply Subtype.ext
    rw [μ.flipAt_val e h', μ.flipAt_val e h]
    simp
  · simp [flipAt, h]

/-- On a free pair the masses are in the ratio `(1 − p) : p`, so the squared coefficient of
`Kₑ`, weighted by the mass at `x`, is `4p(1 − p)` times the mass at the flipped point. -/
private lemma mass_mul_kCoef_sq (e : ι) (x : μ.dist.Supp) (h : μ.Free e x.1) :
    μ.dist.mass x.1 * (μ.kCoef (x.1 e) * μ.kCoef (x.1 e))
      = 4 * μ.p * (1 - μ.p) * μ.dist.mass (μ.flipAt e x).1 := by
  have h1 := μ.condWeight_eq e x x
  have h2 := μ.condWeight_eq e x (μ.flipAt e x)
  simp only [FinDist.condWeight, AgreeOff.refl, μ.agreeOff_flipAt e x, h, ite_true] at h1 h2
  have hfm := μ.dist.fiberMass_pos e x
  rw [div_eq_iff hfm.ne'] at h1 h2
  rw [μ.flipAt_val e h, Function.update_self] at h2
  rw [μ.flipAt_val e h, h2, h1]
  cases x.1 e <;> simp only [kCoef, bitWeight, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, ite_true, ite_false] <;> ring

/-- **(4.14), the norm form** `‖Kₑ f‖² ≤ 4p ‖f‖²`. -/
private lemma jNormSq_recordComm_mul_le (e : ι) (f : JVec μ.dist.Supp A) :
    jNormSq (μ.dist.recordComm e * f) ≤ 4 * μ.p * jNormSq f := by
  classical
  rw [μ.dist.jNormSq_eq_sum_wvec, μ.dist.jNormSq_eq_sum_wvec, Finset.mul_sum]
  have hperm : ∑ x : μ.dist.Supp, 4 * μ.p * (μ.dist.mass (μ.flipAt e x).1
        * qNormSq (μ.dist.wvec f (μ.flipAt e x)))
      = ∑ x : μ.dist.Supp, 4 * μ.p * (μ.dist.mass x.1 * qNormSq (μ.dist.wvec f x)) :=
    Equiv.sum_comp (Function.Involutive.toPerm _ fun x => μ.flipAt_flipAt e x)
      fun x => 4 * μ.p * (μ.dist.mass x.1 * qNormSq (μ.dist.wvec f x))
  rw [← hperm]
  refine Finset.sum_le_sum fun x _ => ?_
  have hmW : 0 ≤ μ.dist.mass (μ.flipAt e x).1 * qNormSq (μ.dist.wvec f (μ.flipAt e x)) :=
    mul_nonneg (μ.dist.mass_nonneg _) (qNormSq_nonneg _)
  have hp := μ.p_pos
  rw [μ.wvec_recordComm_mul]
  by_cases h : μ.Free e x.1
  · simp only [h, ite_true]
    rw [qNormSq_smul, Complex.normSq_ofReal]
    have hW : μ.dist.wvecAt f (Function.update x.1 e (!x.1 e))
        = μ.dist.wvec f (μ.flipAt e x) := by
      rw [← FinDist.wvecAt_coe, μ.flipAt_val e h]
    rw [hW]
    have hm := μ.mass_mul_kCoef_sq e x h
    calc μ.dist.mass x.1 * (μ.kCoef (x.1 e) * μ.kCoef (x.1 e)
            * qNormSq (μ.dist.wvec f (μ.flipAt e x)))
        = μ.dist.mass x.1 * (μ.kCoef (x.1 e) * μ.kCoef (x.1 e))
            * qNormSq (μ.dist.wvec f (μ.flipAt e x)) := by ring
      _ = 4 * μ.p * (1 - μ.p) * (μ.dist.mass (μ.flipAt e x).1
            * qNormSq (μ.dist.wvec f (μ.flipAt e x))) := by rw [hm]; ring
      _ ≤ 4 * μ.p * (μ.dist.mass (μ.flipAt e x).1
            * qNormSq (μ.dist.wvec f (μ.flipAt e x))) := by
          nlinarith [mul_nonneg (mul_nonneg hp.le hp.le) hmW]
  · simp only [h, ite_false]
    rw [qNormSq_zero, mul_zero]
    positivity

/-- **(4.14)** `‖Kₑ‖ ≤ 2√p`. -/
theorem recordComm_sq_le (e : ι) :
    (μ.dist.recordComm e)ᴴ * μ.dist.recordComm e ≤ ((4 * μ.p : ℝ) : ℂ) • (1 : Matrix _ _ ℂ) := by
  exact conjTranspose_mul_self_le_of_jNormSq fun f => μ.jNormSq_recordComm_mul_le e f

/-- **(4.14)** `‖Kₑ f‖∞ ≤ 2‖f‖∞`, on every finite workspace. -/
theorem infNormSq_recordComm_mul_le (e : ι) (f : JVec μ.dist.Supp A) :
    μ.dist.infNormSq (μ.dist.recordComm e * f) ≤ 4 * μ.dist.infNormSq f := by
  classical
  refine μ.dist.infNormSq_le fun x => ?_
  rw [μ.wvec_recordComm_mul]
  by_cases h : μ.Free e x.1
  · simp only [h, ite_true]
    rw [qNormSq_smul, Complex.normSq_ofReal]
    have hk := μ.kCoef_sq_le (x.1 e)
    have hW := μ.dist.qNormSq_wvecAt_le f (Function.update x.1 e (!x.1 e))
    have hW0 := qNormSq_nonneg (μ.dist.wvecAt f (Function.update x.1 e (!x.1 e)))
    have hk0 := mul_self_nonneg (μ.kCoef (x.1 e))
    nlinarith
  · simp only [h, ite_false]
    rw [qNormSq_zero]
    have := μ.dist.infNormSq_nonneg f
    linarith

/-- **(4.15), the bound** `‖[Qₑ, F]‖ ≤ 2wₑ√p / R`. -/
theorem phaseOp_comm_resolvent_sq_le {R : ℝ} {w : ι → ℝ} (hR : 0 < R) (hw : ∀ i, 0 ≤ w i)
    (e : ι) :
    (μ.dist.phaseOp e * resolvent R (μ.dist.varOp w)
        - resolvent R (μ.dist.varOp w) * μ.dist.phaseOp e)ᴴ
      * (μ.dist.phaseOp e * resolvent R (μ.dist.varOp w)
        - resolvent R (μ.dist.varOp w) * μ.dist.phaseOp e)
      ≤ ((4 * w e ^ 2 * μ.p / R ^ 2 : ℝ) : ℂ) • (1 : Matrix _ _ ℂ) := by
  rw [μ.dist.phaseOp_comm_resolvent hR hw e]
  have hH := FinDist.varOp_posSemidef (ρ := μ.dist) hw
  set F := resolvent R (μ.dist.varOp w) with hFdef
  set K := μ.dist.recordComm e with hKdef
  have hF : Fᴴ = F := resolvent_isHermitian hR hH
  have hFF : F * F ≤ 1 := (resolvent_sq_le hR hH).trans (resolvent_le_one hR hH)
  have hp : 0 ≤ 4 * μ.p := by linarith [μ.p_pos]
  have hc : 0 ≤ (w e / R) ^ 2 := sq_nonneg _
  have h1 : (((w e / R : ℝ) : ℂ) • (F * K * F))ᴴ * (((w e / R : ℝ) : ℂ) • (F * K * F))
      = (((w e / R) ^ 2 : ℝ) : ℂ) • ((K * F)ᴴ * (F * F) * (K * F)) := by
    simp only [conjTranspose_smul, conjTranspose_mul, hF, Complex.star_def, Complex.conj_ofReal,
      smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.mul_assoc]
    congr 1
    push_cast
    ring
  have h2 : (K * F)ᴴ * (F * F) * (K * F) ≤ ((4 * μ.p : ℝ) : ℂ) • (1 : Matrix _ _ ℂ) := by
    calc (K * F)ᴴ * (F * F) * (K * F) ≤ (K * F)ᴴ * 1 * (K * F) := conj_le_conj hFF _
      _ = Fᴴ * (Kᴴ * K) * F := by
          rw [conjTranspose_mul, Matrix.mul_one, Matrix.mul_assoc, Matrix.mul_assoc,
            Matrix.mul_assoc]
      _ ≤ Fᴴ * (((4 * μ.p : ℝ) : ℂ) • 1) * F := conj_le_conj (μ.recordComm_sq_le e) _
      _ = ((4 * μ.p : ℝ) : ℂ) • (F * F) := by
          rw [hF, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ ≤ ((4 * μ.p : ℝ) : ℂ) • 1 := real_smul_le_smul hFF hp
  rw [h1]
  calc _ ≤ (((w e / R) ^ 2 : ℝ) : ℂ) • (((4 * μ.p : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)) :=
        real_smul_le_smul h2 hc
    _ = _ := by
        rw [smul_smul]
        congr 1
        push_cast
        ring

/-- **The Jacobi identity** `[Dᵢ, Kₑ] = [[Dᵢ, Dₑ], Qₑ]` for `i ≠ e` (CGZ (5.33)). -/
theorem condDiff_comm_recordComm {i e : ι} (hie : i ≠ e) :
    μ.dist.condDiff i * μ.dist.recordComm e - μ.dist.recordComm e * μ.dist.condDiff i
      = μ.diffComm i e * μ.dist.phaseOp e - μ.dist.phaseOp e * μ.diffComm i e := by
  have hc : μ.dist.condDiff i * μ.dist.phaseOp e = μ.dist.phaseOp e * μ.dist.condDiff i :=
    (μ.dist.commute_condDiff_coordDiag hie _).eq
  have h1 : μ.dist.condDiff i * (μ.dist.phaseOp e * μ.dist.condDiff e)
      = μ.dist.phaseOp e * (μ.dist.condDiff i * μ.dist.condDiff e) := by
    rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc]
  unfold FinDist.recordComm diffComm
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  rw [h1, ← hc]
  abel

/-- **(5.33)** `‖[Dᵢ, Kₑ]‖ ≤ 2p` for `i ≠ e`. -/
theorem condDiff_comm_recordComm_sq_le {i e : ι} (hie : i ≠ e) :
    (μ.dist.condDiff i * μ.dist.recordComm e - μ.dist.recordComm e * μ.dist.condDiff i)ᴴ
      * (μ.dist.condDiff i * μ.dist.recordComm e - μ.dist.recordComm e * μ.dist.condDiff i)
      ≤ ((4 * μ.p ^ 2 : ℝ) : ℂ) • (1 : Matrix _ _ ℂ) := by
  rw [μ.condDiff_comm_recordComm hie]
  set X := μ.diffComm i e with hXdef
  set Q := μ.dist.phaseOp e with hQdef
  have hQ : Qᴴ = Q := μ.dist.phaseOp_isHermitian e
  have hQQ : Q * Q = 1 := μ.dist.phaseOp_mul_self e
  have hp2 : 0 ≤ μ.p ^ 2 := sq_nonneg _
  have hX : Xᴴ * X ≤ ((μ.p ^ 2 : ℝ) : ℂ) • (1 : Matrix _ _ ℂ) :=
    (μ.diffComm_sq_le_interactOp hie).trans (real_smul_le_smul (μ.interactOp_le_one i e) hp2)
  have ha : (X * Q)ᴴ * (X * Q) ≤ ((μ.p ^ 2 : ℝ) : ℂ) • (1 : Matrix _ _ ℂ) := by
    have e1 : (X * Q)ᴴ * (X * Q) = Qᴴ * (Xᴴ * X) * Q := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    have e2 : Qᴴ * (((μ.p ^ 2 : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)) * Q
        = ((μ.p ^ 2 : ℝ) : ℂ) • (1 : Matrix _ _ ℂ) := by
      rw [hQ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hQQ]
    exact e1.trans_le ((conj_le_conj hX Q).trans_eq e2)
  have hb : (Q * X)ᴴ * (Q * X) ≤ ((μ.p ^ 2 : ℝ) : ℂ) • (1 : Matrix _ _ ℂ) := by
    have e1 : (Q * X)ᴴ * (Q * X) = Xᴴ * X := by
      rw [conjTranspose_mul, hQ, Matrix.mul_assoc, ← Matrix.mul_assoc Q Q X, hQQ,
        Matrix.one_mul]
    exact e1.trans_le hX
  calc _ ≤ ((2 : ℝ) : ℂ) • ((X * Q)ᴴ * (X * Q)) + ((2 : ℝ) : ℂ) • ((Q * X)ᴴ * (Q * X)) :=
        sub_sq_le_two_smul _ _
    _ ≤ ((2 : ℝ) : ℂ) • (((μ.p ^ 2 : ℝ) : ℂ) • (1 : Matrix _ _ ℂ))
          + ((2 : ℝ) : ℂ) • (((μ.p ^ 2 : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)) :=
        add_le_add (real_smul_le_smul ha (by norm_num)) (real_smul_le_smul hb (by norm_num))
    _ = _ := by
        rw [smul_smul, ← add_smul]
        congr 1
        push_cast
        ring

end CondBern

end QuantumQueryComplexity
