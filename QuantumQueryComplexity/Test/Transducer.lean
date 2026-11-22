import QuantumQueryComplexity.Quantum.Transducer
import QuantumQueryComplexity.Quantum.KronLift

set_option linter.style.header false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Acceptance: transducers

Checks of `Quantum/Transducer.lean` ([BJY23, Theorem 5.5]) on small explicit instances.

1. **[BJY23, Example 5.3].** On `Fin 3`, `|0⟩` is public and `|1⟩`, `|2⟩` are private; `S` is
   the reflection of `|0⟩ − |1⟩ − |2⟩` (it negates that vector and fixes its orthogonal
   complement). `S` transduces `|0⟩` into itself with the catalyst `(|1⟩ + |2⟩)/2` of squared
   norm `1/2`, and also with the catalysts `|1⟩` and `|2⟩`. The algorithm `Transducer.circuit`
   then returns `|0⟩ ⊗ |0⟩` within `√2/√K`. For `K = 1` and `K = 2` the output is computed
   exactly: errors `2/√3` and `2/3`, below the bounds `√2` and `1`. These two sizes cannot see
   the direction of the clock advance (`finRotate` is its own inverse on `Fin 1` and `Fin 2`).
2. **The direction of the advance and the order of the operations**, at `K = 3`: `tick` moves a
   private basis state from clock `0` to `1` and from `2` to `0`, and one round with the swap of
   `|0⟩` and `|1⟩` sends `(clock 0, |0⟩)` to `(clock 1, |1⟩)`. A reversed advance would give
   clock `2`; advancing before applying `S` would give clock `0`.
3. **A transducer with a query.** One swap query on `QBasis Unit Bool Unit` exchanges the blank
   answer `|(), ⊥⟩` with `|(), a ()⟩`. With the non-blank answers private, it transduces
   `|(), ⊥⟩` into itself with the input-dependent catalyst `|(), a ()⟩`, so the routine form
   gives a fixed `K`-query routine that returns the clocked `|(), ⊥⟩` within `2/√K` on every
   input. (An idle routine also meets this conclusion; item 5 is the positive control.)
4. **A realized transducer.** The matrix of Example 5.3 acting on the workspace `Fin 3` of
   `QBasis Unit Bool (Fin 3)`, as a zero-query routine, realizes `S` along the embedding
   `x ↦ (none, none, x)`, and `exists_transducerRoutine_of_realizes` applies. (Here too the
   identity routine meets the conclusion.)
5. **The routine must read the oracle.** On the answer register of a live query, embedded by
   `z ↦ (some (), z, ())`, one query realizes the swap of `⊥` and `a ()`. With every basis state
   public and the catalyst `0` it transduces `|⊥⟩` into `|a ()⟩` exactly, so the realized form
   gives one fixed `K`-query routine that maps the clocked `|(), ⊥⟩` to the clocked
   `|(), a ()⟩` exactly: its output differs between the two oracle tables.
-/

namespace QuantumQueryComplexity
namespace TransducerAcceptance

open scoped Matrix
open Matrix

/-! ## 1. [BJY23, Example 5.3] -/

/-- The privacy predicate of [BJY23, Example 5.3] on `Fin 3`: `|0⟩` is public, `|1⟩` and `|2⟩`
are private. -/
def priv53 : Fin 3 → Prop := fun i => i ≠ 0

instance : DecidablePred priv53 := fun i => inferInstanceAs (Decidable (i ≠ 0))

/-- The vector `|0⟩ − |1⟩ − |2⟩` of [BJY23, Example 5.3]. -/
def u53 : Fin 3 → ℂ := ![1, -1, -1]

/-- The transducer of [BJY23, Example 5.3], written out: the reflection
`1 − (2/3) u uᵀ` of `u = |0⟩ − |1⟩ − |2⟩` (`S53_eq`). -/
noncomputable def S53 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1 / 3, 2 / 3, 2 / 3; 2 / 3, 1 / 3, -2 / 3; 2 / 3, -2 / 3, 1 / 3]

/-- `S53` is the reflection of `u53`: `1 − (2/3) u uᵀ`, where `‖u‖² = 3`. -/
theorem S53_eq : S53 = 1 - (2 / 3 : ℂ) • Matrix.vecMulVec u53 u53 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [S53, u53, Matrix.one_apply, Matrix.vecMulVec]

/-- `S53` negates `u53` ... -/
theorem S53_mulVec_u53 : S53 *ᵥ u53 = -u53 := by
  funext i
  fin_cases i <;> norm_num [S53, u53, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- ... and fixes every vector orthogonal to it. -/
theorem S53_mulVec_of_orth (w : Fin 3 → ℂ) (hw : u53 ⬝ᵥ w = 0) : S53 *ᵥ w = w := by
  rw [S53_eq, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, hw]
  simp

/-- `S53` is unitary. -/
theorem S53_mem_unitaryGroup : S53 ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, S53,
      Fin.sum_univ_succ, map_ofNat]

/-- A vector `v` with `v 0 = 0` is a catalyst for `S53` transducing `|0⟩` into itself as soon
as `|0⟩ + v` is orthogonal to `u53` (then `S53` fixes it). -/
theorem transduces53_of_orth (v : Fin 3 → ℂ) (hv : v 0 = 0)
    (horth : u53 ⬝ᵥ (qBasis 0 + v) = 0) :
    Transduces priv53 S53 (qBasis 0) (qBasis 0) v := by
  have hpub (i : Fin 3) (h : priv53 i) : qBasis 0 i = 0 := by
    simp [qBasis_apply, show i ≠ 0 from h]
  refine ⟨hpub, hpub, ?_, S53_mulVec_of_orth _ horth⟩
  intro i hi
  simpa [show i = 0 from (by simpa [priv53] using hi)] using hv

/-- The catalyst `(|1⟩ + |2⟩)/2` of [BJY23, Example 5.3]. -/
noncomputable def v53 : Fin 3 → ℂ := ![0, 1 / 2, 1 / 2]

/-- **[BJY23, Example 5.3]**: `S (|0⟩ + (|1⟩ + |2⟩)/2) = |0⟩ + (|1⟩ + |2⟩)/2`, so `S53`
transduces `|0⟩` into itself with the catalyst `v53`. -/
theorem transduces53 : Transduces priv53 S53 (qBasis 0) (qBasis 0) v53 := by
  apply transduces53_of_orth
  · rfl
  · norm_num [u53, v53, dotProduct, Fin.sum_univ_succ, qBasis_apply]

/-- The other catalysts named in [BJY23, Example 5.3]: `|1⟩` and `|2⟩`. -/
theorem transduces53_basis :
    Transduces priv53 S53 (qBasis 0) (qBasis 0) (qBasis 1) ∧
      Transduces priv53 S53 (qBasis 0) (qBasis 0) (qBasis 2) := by
  constructor <;> apply transduces53_of_orth <;>
    norm_num [u53, dotProduct, Fin.sum_univ_succ, qBasis_apply]

/-- `‖v53‖² = 1/2`, the value used in `circuit53_close`. (That `v53` is the minimal catalyst,
so that `W(S, |0⟩) = 1/2`, is shown in [BJY23, Example 5.3] and not formalized here; the
catalysts `|1⟩` and `|2⟩` have squared norm `1`.) -/
theorem qNormSq_v53 : qNormSq v53 = 1 / 2 := by
  norm_num [qNormSq_def, v53, Fin.sum_univ_succ, Complex.normSq_div]

/-- The error numerator of `circuit53_close`: `2‖v53‖ = √2`. -/
theorem two_mul_qNorm_v53 : 2 * qNorm v53 = Real.sqrt 2 := by
  apply (sq_eq_sq₀ (mul_nonneg (by norm_num) (qNorm_nonneg _)) (Real.sqrt_nonneg _)).mp
  have h := qNorm_sq v53
  rw [qNormSq_v53] at h
  rw [Real.sq_sqrt (by norm_num)]
  nlinarith

/-- **The theorem on the example**: for every `K ≥ 1` the algorithm returns `|0⟩ ⊗ |0⟩` within
`2‖v53‖/√K = √2/√K`. -/
theorem circuit53_close {K : ℕ} (hK : 0 < K) :
    qNorm (Transducer.circuit K S53 priv53 *ᵥ Transducer.clockVec ⟨0, hK⟩ (qBasis 0)
      - Transducer.clockVec ⟨0, hK⟩ (qBasis 0)) ≤ Real.sqrt 2 / Real.sqrt K := by
  simpa only [two_mul_qNorm_v53] using
    Transducer.circuit_close hK S53_mem_unitaryGroup priv53 transduces53

/-! ### Exact outputs for `K = 1` and `K = 2` -/

/-- `A ⊗ 1` acts on the clock branches only. -/
theorem kron_one_mulVec_apply {K : ℕ} (A : Matrix (Fin K) (Fin K) ℂ) (f : Fin K × Fin 3 → ℂ)
    (c : Fin K) (h : Fin 3) :
    (Matrix.kroneckerMap (· * ·) A (1 : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ f) (c, h) =
      ∑ d, A c d * f (d, h) := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [Matrix.one_apply, mul_ite]

/-- The clock preparation acts as `fourierMat K` on the clock branches. -/
theorem prep_mulVec_apply {K : ℕ} (f : Fin K × Fin 3 → ℂ) (c : Fin K) (h : Fin 3) :
    (Transducer.prep K *ᵥ f) (c, h) = ∑ d, fourierMat K c d * f (d, h) :=
  kron_one_mulVec_apply _ _ _ _

/-- Its adjoint acts as `(fourierMat K)ᴴ` on the clock branches. -/
theorem prep_conjTranspose_mulVec_apply {K : ℕ} (f : Fin K × Fin 3 → ℂ) (c : Fin K)
    (h : Fin 3) :
    ((Transducer.prep K)ᴴ *ᵥ f) (c, h) = ∑ d, (fourierMat K)ᴴ c d * f (d, h) := by
  rw [Transducer.prep, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  exact kron_one_mulVec_apply _ _ _ _

/-- For `K = 1` the clock preparation is the identity. -/
theorem prep_one_mulVec (f : Fin 1 × Fin 3 → ℂ) : Transducer.prep 1 *ᵥ f = f := by
  funext ⟨c, h⟩
  fin_cases c
  norm_num [prep_mulVec_apply, fourierMat_apply]

/-- For `K = 1` its adjoint is the identity too. -/
theorem prep_one_conjTranspose_mulVec (f : Fin 1 × Fin 3 → ℂ) :
    (Transducer.prep 1)ᴴ *ᵥ f = f := by
  funext ⟨c, h⟩
  fin_cases c
  norm_num [prep_conjTranspose_mulVec_apply, fourierMat_apply]

/-- `K = 1`: the algorithm is one application of `S53`, which maps `|0⟩` to
`(1/3, 2/3, 2/3)`; the error is `2/√3 ≤ √2`. -/
theorem circuit53_one :
    Transducer.circuit 1 S53 priv53 *ᵥ Transducer.clockVec 0 (qBasis 0)
      = Transducer.clockVec 0 ![1 / 3, 2 / 3, 2 / 3] := by
  rw [Transducer.circuit, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, prep_one_mulVec,
    prep_one_conjTranspose_mulVec]
  change (qPerm _ * (Transducer.ctrlAt 1 0 S53 * 1)) *ᵥ _ = _
  rw [Matrix.mul_one, ← Matrix.mulVec_mulVec]
  funext ⟨c, h⟩
  have hp : (Transducer.tick 1 priv53).symm (c, h) = (c, h) := by
    fin_cases c
    fin_cases h <;> rfl
  rw [qPerm_mulVec_apply, hp, Transducer.ctrlAt_mulVec_apply]
  fin_cases c
  fin_cases h <;>
    norm_num [S53, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Transducer.clockVec,
      qBasis_apply]

/-- The factor `1/√2` shared by both clock branches after the clock preparation at `K = 2`. -/
noncomputable def invSqrtTwo : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

/-- `(1/√2)² = 1/2`. -/
theorem invSqrtTwo_sq : invSqrtTwo ^ 2 = (1 / 2 : ℂ) := by
  have h : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num), one_div]
  unfold invSqrtTwo
  rw [← Complex.ofReal_pow, h]
  norm_num

/-- `e^{2πi/2} = −1`. -/
theorem cexp1_half : cexp1 (1 / 2) = -1 := by
  rw [cexp1, ← Complex.exp_pi_mul_I]
  congr 1
  push_cast
  ring

/-- `fourierMat 2` is the Hadamard matrix. -/
theorem fourierMat_two (c d : Fin 2) :
    fourierMat 2 c d = if c = 1 ∧ d = 1 then -invSqrtTwo else invSqrtTwo := by
  fin_cases c <;> fin_cases d <;> norm_num [fourierMat_apply, invSqrtTwo, cexp1_half]

/-- The adjoint of `fourierMat 2`, entrywise. -/
theorem fourierMat_two_conjTranspose (c d : Fin 2) :
    (fourierMat 2)ᴴ c d = if d = 1 ∧ c = 1 then -invSqrtTwo else invSqrtTwo := by
  rw [Matrix.conjTranspose_apply, fourierMat_two]
  split <;> simp [invSqrtTwo]

/-- The vector with branch vectors `x` on clock `0` and `y` on clock `1`. -/
def branches2 (x y : Fin 3 → ℂ) (p : Fin 2 × Fin 3) : ℂ := ![x, y] p.1 p.2

/-- The inverse of the advance at `K = 2`: it swaps the clocks of private basis states. -/
theorem tick_two_symm (c : Fin 2) (h : Fin 3) :
    (Transducer.tick 2 priv53).symm (c, h) = (if h = 0 then c else ![(1 : Fin 2), 0] c, h) := by
  fin_cases c <;> fin_cases h <;> rfl

/-- The prepared clock at `K = 2`: `|0⟩` on both branches, with the factor `1/√2`. -/
theorem prep_two_mulVec_clockVec :
    Transducer.prep 2 *ᵥ Transducer.clockVec 0 (qBasis (0 : Fin 3))
      = invSqrtTwo • branches2 (qBasis 0) (qBasis 0) := by
  funext ⟨c, h⟩
  rw [prep_mulVec_apply, Fin.sum_univ_two]
  fin_cases c <;> simp [fourierMat_two, Transducer.clockVec, branches2]

/-- Round `0` at `K = 2`, without the factor `1/√2`. -/
theorem loop_two_one :
    Transducer.loop 2 S53 priv53 1 *ᵥ branches2 (qBasis 0) (qBasis 0) =
      branches2 ![1 / 3, 0, 0] ![1, 2 / 3, 2 / 3] := by
  change (qPerm _ * (Transducer.ctrlAt 2 0 S53 * 1)) *ᵥ _ = _
  rw [Matrix.mul_one, ← Matrix.mulVec_mulVec]
  funext ⟨c, h⟩
  rw [qPerm_mulVec_apply, tick_two_symm, Transducer.ctrlAt_mulVec_apply]
  fin_cases c <;> fin_cases h <;>
    norm_num [S53, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, branches2, qBasis_apply]

/-- Rounds `0` and `1` at `K = 2`, without the factor `1/√2`. -/
theorem loop_two_two :
    Transducer.loop 2 S53 priv53 2 *ᵥ branches2 (qBasis 0) (qBasis 0) =
      branches2 ![1 / 3, 4 / 9, 4 / 9] ![11 / 9, 0, 0] := by
  change (qPerm _ * (Transducer.ctrlAt 2 1 S53 * Transducer.loop 2 S53 priv53 1)) *ᵥ _ = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, loop_two_one]
  funext ⟨c, h⟩
  rw [qPerm_mulVec_apply, tick_two_symm, Transducer.ctrlAt_mulVec_apply]
  fin_cases c <;> fin_cases h <;>
    norm_num [S53, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, branches2]

/-- `K = 2`, computed by hand. After the clock preparation the state is
`(|0⟩ + |1⟩)|0⟩/√2`; the branch vectors below omit this common factor `1/√2` during the rounds.
Round `0` applies `S53` on branch `0` and moves its private part to branch `1`; round `1`
applies `S53` to `(1, 2/3, 2/3)` on branch `1`, giving `(11/9, 4/9, 4/9)`, and moves its private
part back to branch `0`. Undoing the preparation (which supplies a second factor `1/√2`) gives
`(7/9, 2/9, 2/9)` on branch `0` and `(−4/9, 2/9, 2/9)` on branch `1`: the error is
`2/3 ≤ 1`. -/
theorem circuit53_two :
    Transducer.circuit 2 S53 priv53 *ᵥ Transducer.clockVec 0 (qBasis 0)
      = Transducer.clockVec 0 ![7 / 9, 2 / 9, 2 / 9]
        + Transducer.clockVec 1 ![-4 / 9, 2 / 9, 2 / 9] := by
  rw [Transducer.circuit, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    prep_two_mulVec_clockVec, Matrix.mulVec_smul, loop_two_two, Matrix.mulVec_smul]
  funext ⟨c, h⟩
  simp only [Pi.smul_apply, smul_eq_mul, prep_conjTranspose_mulVec_apply, Fin.sum_univ_two,
    fourierMat_two_conjTranspose]
  fin_cases c <;> fin_cases h <;> norm_num [Transducer.clockVec, branches2] <;>
    ring_nf <;> norm_num [invSqrtTwo_sq]

/-! ## 2. The direction of the advance and the order of the operations -/

/-- At `K = 3`, `tick` advances a private basis state from clock `0` to `1` and from clock `2`
to `0`, and leaves a public basis state alone. -/
theorem tick_three :
    Transducer.tick 3 priv53 (0, 1) = (1, 1) ∧ Transducer.tick 3 priv53 (2, 1) = (0, 1) ∧
      Transducer.tick 3 priv53 (0, 0) = (0, 0) :=
  ⟨rfl, rfl, rfl⟩

/-- **One round at `K = 3`**, with `S` the swap of `|0⟩` (public) and `|1⟩` (private): `S`
moves `(clock 0, |0⟩)` to `(clock 0, |1⟩)`, and the advance then moves it to `(clock 1, |1⟩)`.
A reversed advance would give clock `2`; advancing before applying `S` would give clock `0`. -/
theorem first_round_three :
    Transducer.loop 3 (qPerm (Equiv.swap (0 : Fin 3) 1)) priv53 1 *ᵥ qBasis (0, 0)
      = qBasis (1, 1) := by
  let S := qPerm (Equiv.swap (0 : Fin 3) 1)
  have hswap : S *ᵥ qBasis 0 = qBasis 1 := by simp [S, qPerm_mulVec_qBasis]
  have hcol : S.col 0 = qBasis 1 := by
    simpa only [qBasis, Matrix.mulVec_single_one] using hswap
  have hbranch : Transducer.ctrlAt 3 0 S *ᵥ qBasis (0, 0) = qBasis (0, 1) := by
    rw [qBasis, Matrix.mulVec_single_one]
    funext ⟨c, h⟩
    by_cases hc : c = 0
    · subst c
      simpa [Matrix.col, Transducer.ctrlAt, qBasis_apply] using congrFun hcol h
    · simp [Matrix.col, Transducer.ctrlAt, hc, qBasis_apply]
  change (qPerm (Transducer.tick 3 priv53) * (Transducer.ctrlAt 3 0 S * 1)) *ᵥ _ = _
  rw [Matrix.mul_one, ← Matrix.mulVec_mulVec, hbranch, qPerm_mulVec_qBasis]
  rfl

/-! ## 3. A transducer with a query -/

/-- The privacy predicate on `QBasis Unit Bool Unit`: a basis state is private exactly when its
answer register is not blank. -/
def privAnswer : QBasis Unit Bool Unit → Prop := fun p => p.2.1 ≠ none

instance : DecidablePred privAnswer := fun p => inferInstanceAs (Decidable (p.2.1 ≠ none))

/-- The basis state that queries `()` with a blank answer. -/
def blank1 : QBasis Unit Bool Unit := (some (), none, ())

/-- **One query is a transducer.** The swap oracle exchanges `|(), ⊥⟩` and `|(), a ()⟩`, so it
transduces `|(), ⊥⟩` into itself with the catalyst `|(), a ()⟩`, which depends on the input. -/
theorem transduces_query (a : Unit → Bool) :
    Transduces privAnswer ((QRoutine.query : QRoutine Unit Bool Unit).run a)
      (qBasis blank1) (qBasis blank1) (qBasis (some (), some (a ()), ())) := by
  have hpub (p : QBasis Unit Bool Unit) (hp : privAnswer p) : qBasis blank1 p = 0 := by
    have hne : p ≠ blank1 := fun he => hp (by rw [he]; rfl)
    simp [hne]
  refine ⟨hpub, hpub, ?_, ?_⟩
  · intro p hp
    have hne : p ≠ (some (), some (a ()), ()) := by
      intro he
      exact hp (he ▸ Option.some_ne_none _)
    simp [hne]
  · simp [QRoutine.query_run, Matrix.mulVec_add, oracleMat_mulVec_qBasis, blank1, add_comm]

/-- **The routine form on the one-query transducer**: one fixed routine with `K` queries returns
the clocked `|(), ⊥⟩` within `2/√K` on every input. (A routine that parks every query also
meets this conclusion; `query_reads_answer` is the positive control.) -/
theorem query_transducer {K : ℕ} (hK : 0 < K) :
    ∃ T : QRoutine Unit Bool (ClockWork Unit K Unit), T.len = K ∧
      ∀ a : Unit → Bool,
        qNorm (T.run a *ᵥ embedClock ⟨0, hK⟩ false (qBasis blank1)
          - embedClock ⟨0, hK⟩ false (qBasis blank1)) ≤ 2 / Real.sqrt K := by
  obtain ⟨T, hlen, hT⟩ := exists_transducerRoutine (QRoutine.query : QRoutine Unit Bool Unit)
    privAnswer hK
  refine ⟨T, by simpa using hlen, fun a => ?_⟩
  have h := hT a _ _ _ (transduces_query a)
  have hv : qNorm (qBasis ((some (), some (a ()), ()) : QBasis Unit Bool Unit)) = 1 := by
    rw [qNorm, qNormSq_qBasis, Real.sqrt_one]
  rwa [hv, mul_one] at h

/-! ## 4. A realized transducer -/

/-- The basis of `QBasis Unit Bool (Fin 3)` split as (workspace, query registers). -/
def split3 : QBasis Unit Bool (Fin 3) ≃ Fin 3 × (Option Unit × Option Bool) where
  toFun p := (p.2.2, (p.1, p.2.1))
  invFun x := (x.2.1, x.2.2, x.1)
  left_inv := by rintro ⟨k, t, w⟩; rfl
  right_inv := by rintro ⟨w, k, t⟩; rfl

/-- `S53` acting on the workspace `Fin 3`, as a zero-query routine. -/
noncomputable def R53 : QRoutine Unit Bool (Fin 3) :=
  QRoutine.ofUnitary (kronLift split3 S53) (kronLift_mem_unitaryGroup split3 S53_mem_unitaryGroup)

/-- The embedding of `Fin 3` as the workspace, with idle query index and blank answer. -/
def emb3 : Fin 3 → QBasis Unit Bool (Fin 3) := fun x => (none, none, x)

/-- `R53` realizes `S53` along `emb3`, on every input. -/
theorem realizes53 (a : Unit → Bool) (ψ : Fin 3 → ℂ) :
    R53.run a *ᵥ Transducer.embedVia emb3 ψ = Transducer.embedVia emb3 (S53 *ᵥ ψ) := by
  have hsplit (φ : Fin 3 → ℂ) :
      Transducer.embedVia emb3 φ = splitVec split3 φ (qBasis (none, none)) := by
    funext ⟨k, t, w⟩
    by_cases hk : k = none <;> by_cases ht : t = none <;>
      simp [Transducer.embedVia, splitVec, split3, emb3, Finset.sum_apply, qBasis_apply, hk, ht,
        mul_ite]
  change kronLift split3 S53 *ᵥ Transducer.embedVia emb3 ψ = _
  rw [hsplit, kronLift_mulVec_splitVec, hsplit]

/-- **The realized form on Example 5.3**: one fixed zero-query routine returns the clocked
embedding of `|0⟩` within `√2/√K`. (The identity routine also meets this conclusion.) -/
theorem realized53_transducer {K : ℕ} (hK : 0 < K) :
    ∃ T : QRoutine Unit Bool (ClockWork Unit K (Fin 3)), T.len = 0 ∧
      ∀ a : Unit → Bool,
        qNorm (T.run a *ᵥ embedClock ⟨0, hK⟩ false (Transducer.embedVia emb3 (qBasis 0))
          - embedClock ⟨0, hK⟩ false (Transducer.embedVia emb3 (qBasis 0)))
          ≤ Real.sqrt 2 / Real.sqrt K := by
  have he : Function.Injective emb3 := fun _ _ h => congrArg (fun p => p.2.2) h
  obtain ⟨T, hlen, hT⟩ := exists_transducerRoutine_of_realizes R53 emb3 he priv53 hK
  refine ⟨T, by simpa [R53] using hlen, fun a => ?_⟩
  rw [← two_mul_qNorm_v53]
  exact hT a S53 (realizes53 a) _ _ _ transduces53

/-! ## 5. The routine must read the oracle -/

/-- The answer register of a live query to `()`, as a register of `QBasis Unit Bool Unit`. -/
def liveAnswer (z : Option Bool) : QBasis Unit Bool Unit := (some (), z, ())

/-- On the answer register of a live query, one query realizes the swap of `⊥` and `a ()`. -/
theorem realizes_answer (a : Unit → Bool) (ψ : Option Bool → ℂ) :
    (QRoutine.query : QRoutine Unit Bool Unit).run a *ᵥ Transducer.embedVia liveAnswer ψ
      = Transducer.embedVia liveAnswer (qPerm (Equiv.swap none (some (a ()))) *ᵥ ψ) := by
  have hembed (φ : Option Bool → ℂ) (k : Option Unit) (z : Option Bool) :
      Transducer.embedVia liveAnswer φ (k, z, ()) = if k = some () then φ z else 0 := by
    by_cases h : k = some () <;>
      simp [Transducer.embedVia, liveAnswer, Finset.sum_apply, qBasis_apply, h, mul_ite]
  funext ⟨k, z, w⟩
  cases w
  cases k with
  | none => simp [oracleMat_mulVec_apply, hembed]
  | some i =>
    cases i
    simp [oracleMat_mulVec_apply, hembed, qPerm_mulVec_apply]

/-- **The positive control**: one fixed routine with `K` queries maps the clocked `|(), ⊥⟩` to
the clocked `|(), a ()⟩` exactly, on every input `a`. It follows from
`exists_transducerRoutine_of_realizes` with every basis state public and the catalyst `0`
(error `0`). The two oracle tables give different outputs, so no idle routine satisfies it. -/
theorem query_reads_answer {K : ℕ} (hK : 0 < K) :
    ∃ T : QRoutine Unit Bool (ClockWork Unit K Unit), T.len = K ∧
      ∀ a : Unit → Bool,
        T.run a *ᵥ embedClock ⟨0, hK⟩ false (qBasis blank1)
          = embedClock ⟨0, hK⟩ false (qBasis (some (), some (a ()), ())) := by
  have he : Function.Injective liveAnswer := fun _ _ h => congrArg (fun p => p.2.1) h
  obtain ⟨T, hlen, hT⟩ := exists_transducerRoutine_of_realizes
    (QRoutine.query : QRoutine Unit Bool Unit) liveAnswer he (fun _ => False) hK
  refine ⟨T, by simpa using hlen, fun a => ?_⟩
  have ht : Transduces (fun _ => False) (qPerm (Equiv.swap none (some (a ()))))
      (qBasis none) (qBasis (some (a ()))) 0 := by
    refine ⟨fun _ h => h.elim, fun _ h => h.elim, by simp, ?_⟩
    simp [qPerm_mulVec_qBasis]
  have herr := hT a _ (realizes_answer a) _ _ _ ht
  rw [Transducer.embedVia_qBasis, Transducer.embedVia_qBasis, qNorm_zero, mul_zero,
    zero_div] at herr
  change T.run a *ᵥ embedClock ⟨0, hK⟩ false (qBasis (liveAnswer none)) =
    embedClock ⟨0, hK⟩ false (qBasis (liveAnswer (some (a ()))))
  apply sub_eq_zero.mp
  apply qNormSq_eq_zero_iff.mp
  rw [← qNorm_sq, le_antisymm herr (qNorm_nonneg _)]
  norm_num

end TransducerAcceptance
end QuantumQueryComplexity
