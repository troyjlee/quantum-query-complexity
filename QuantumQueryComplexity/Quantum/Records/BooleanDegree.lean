import QuantumQueryComplexity.Quantum.Records.RecordCount
import QuantumQueryComplexity.Quantum.PolynomialMethod
import QuantumQueryComplexity.Quantum.JointState.Conditioning

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Records and the polynomial method

For the uniform distribution on the Boolean cube `ι → Bool`, the record subspace `P_S` is spanned
by the character `x ↦ ∏_{i ∈ S} (−1)^{xᵢ}`, a multilinear polynomial of degree `|S|`. So a joint
vector with at most `t` records has, at every workspace basis state, an amplitude that is a
polynomial of degree at most `t` in the input bits (`hasAmpPoly_of_recLe`) [Bel26, Section 3.6].

Combined with the record-count bound (`recLe_mul_jointState`), this re-derives the amplitude half
of the polynomial method of Beals–Buhrman–Cleve–Mosca–de Wolf (`QAlg.hasAmpPoly_state`, proved in
`PolynomialMethod.lean` by a direct induction) from records (`QAlg.hasAmpPoly_state_of_records`).
The two developments are consistent.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

namespace FinDist

/-- The marginals of the uniform distribution on the cube are `1/2`. -/
private lemma marg_uniform_cube (i : ι) (a : Bool) : (uniform (ι → Bool)).marg i a = 1 / 2 := by
  have hflip : (uniform (ι → Bool)).marg i true = (uniform (ι → Bool)).marg i false := by
    let e : (ι → Bool) ≃ (ι → Bool) :=
      ⟨fun x => Function.update x i (!x i), fun x => Function.update x i (!x i),
        fun x => by simp, fun x => by simp⟩
    refine Fintype.sum_equiv e _ _ fun x => ?_
    simp [e]
  have hsum := sum_marg (ρ := uniform (ι → Bool)) i
  rw [Fintype.sum_bool] at hsum
  cases a <;> linarith

/-- The record factor `I − |√μᵢ⟩⟨√μᵢ|` or `|√μᵢ⟩⟨√μᵢ|` of the uniform cube, as a real number. -/
private noncomputable def cubeFactor (S : Finset ι) (i : ι) (a b : Bool) : ℝ :=
  if i ∈ S then (if a = b then 1 else 0) - 1 / 2 else 1 / 2

/-- The record factor of the uniform cube is the real number `cubeFactor`. -/
private lemma recFactor_uniform_cube (S : Finset ι) (i : ι) (a b : Bool) :
    (uniform (ι → Bool)).recFactor S i a b = (cubeFactor S i a b : ℂ) := by
  have h : Real.sqrt ((uniform (ι → Bool)).marg i a * (uniform (ι → Bool)).marg i b) = 1 / 2 := by
    rw [marg_uniform_cube, marg_uniform_cube]
    exact Real.sqrt_mul_self (by norm_num)
  rw [recFactor, cubeFactor, h]
  split_ifs <;> push_cast <;> ring

/-- A real polynomial of degree at most `|S|` giving the column `b` of `P_S` on the cube. -/
private noncomputable def cubePoly (S : Finset ι) (b : ι → Bool) : MvPolynomial ι ℝ :=
  ∏ i, if i ∈ S then QuantumQueryComplexity.select i (MvPolynomial.C (cubeFactor S i false (b i)))
    (MvPolynomial.C (cubeFactor S i true (b i))) else MvPolynomial.C (1 / 2)

/-- Evaluation on the cube is multiplicative over finite products. -/
private lemma evalBool_prod' (s : Finset ι) (q : ι → MvPolynomial ι ℝ) (a : ι → Bool) :
    evalBool (∏ i ∈ s, q i) a = ∏ i ∈ s, evalBool (q i) a :=
  map_prod (MvPolynomial.eval fun i => bit (a i)) q s

/-- `cubePoly S b` evaluates to the product of the record factors. -/
private lemma evalBool_cubePoly (S : Finset ι) (a b : ι → Bool) :
    evalBool (cubePoly S b) a = ∏ i, cubeFactor S i (a i) (b i) := by
  rw [cubePoly, evalBool_prod']
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [evalBool_select, evalBool_C, evalBool_C]
    cases a i <;> rfl
  · rw [evalBool_C]
    simp [cubeFactor, hi]

/-- `cubePoly S b` has total degree at most `|S|`. -/
private lemma totalDegree_cubePoly_le (S : Finset ι) (b : ι → Bool) :
    (cubePoly S b).totalDegree ≤ S.card := by
  rw [cubePoly]
  refine ((MvPolynomial.totalDegree_finsetProd _ _).trans
    (Finset.sum_le_sum (g := fun i => if i ∈ S then 1 else 0) fun i _ => ?_)).trans ?_
  · split_ifs
    · exact totalDegree_select_le (t := 0) i (by simp) (by simp)
    · simp
  · simp

/-- The complex value of a real polynomial, as an amplitude polynomial. -/
private lemma evalC_mk_zero (p : MvPolynomial ι ℝ) (a : ι → Bool) :
    (⟨p, 0⟩ : AmpPoly ι).evalC a = (evalBool p a : ℂ) := by
  apply Complex.ext <;> simp

/-- A point of the Boolean cube, as a point of the support of the uniform distribution. -/
def cubePt (a : ι → Bool) : (uniform (ι → Bool)).Supp :=
  ⟨a, by rw [uniform_mass]; exact one_div_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)⟩

/-- **At most `t` records means degree at most `t`**: for the uniform distribution on the cube,
the workspace amplitudes of a joint vector in `⊕_{|S| ≤ t} P_S` are polynomials of degree at most
`t` in the input bits. -/
theorem hasAmpPoly_of_recLe {B : Type} [Fintype B] {t : ℕ}
    (f : JVec (uniform (ι → Bool)).Supp B) (hf : (uniform (ι → Bool)).recLe t * f = f) :
    HasAmpPoly (fun a b => (uniform (ι → Bool)).wvec f (cubePt a) b) t := by
  have key : ∀ (x : (uniform (ι → Bool)).Supp) (c : B), f x c =
      ∑ S ∈ Finset.univ.filter (fun S : Finset ι => S.card ≤ t),
        ∑ y : (uniform (ι → Bool)).Supp, ((evalBool (cubePoly S y.1) x.1 : ℝ) : ℂ) * f y c := by
    intro x c
    conv_lhs => rw [← hf]
    simp only [recLe, Matrix.mul_apply, Matrix.sum_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun y _ => ?_
    rw [evalBool_cubePoly, Complex.ofReal_prod, recProj]
    exact congrArg (· * f y c) (Finset.prod_congr rfl fun i _ => recFactor_uniform_cube S i _ _)
  refine ⟨fun c => AmpPoly.cmul ((Real.sqrt (1 / (Fintype.card (ι → Bool) : ℝ)))⁻¹ : ℂ)
      (AmpPoly.sum (Finset.univ.filter (fun S : Finset ι => S.card ≤ t)) fun S =>
        AmpPoly.sum Finset.univ fun y : (uniform (ι → Bool)).Supp =>
          AmpPoly.cmul (f y c) ⟨cubePoly S y.1, 0⟩), fun c => ?_, fun a c => ?_⟩
  · refine AmpPoly.degLe_cmul _ _ (AmpPoly.degLe_sum _ _ fun S hS =>
      AmpPoly.degLe_sum _ _ fun y _ => AmpPoly.degLe_cmul _ _ ⟨?_, by simp⟩)
    exact (totalDegree_cubePoly_le S y.1).trans (Finset.mem_filter.mp hS).2
  · beta_reduce
    rw [AmpPoly.evalC_cmul, AmpPoly.evalC_sum, wvec, Pi.smul_apply, smul_eq_mul,
      key (cubePt a) c, uniform_mass]
    refine congrArg _ (Finset.sum_congr rfl fun S _ => ?_)
    rw [AmpPoly.evalC_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [AmpPoly.evalC_cmul, evalC_mk_zero, mul_comm]
    rfl

end FinDist

/-- **The amplitude half of the polynomial method, from records**: after `t` queries the
amplitudes are polynomials of degree at most `t` (`QAlg.hasAmpPoly_state`), derived from the
record-count bound. -/
theorem QAlg.hasAmpPoly_state_of_records {O W : Type} [Fintype W] [DecidableEq W]
    (A : QAlg ι Bool O W) (t : ℕ) : HasAmpPoly (fun a => A.state a t) t := by
  have h := FinDist.hasAmpPoly_of_recLe _
    (FinDist.recLe_mul_jointState (FinDist.isFullProduct_uniform (ι := ι) (σ := Bool)) A t)
  simp only [FinDist.wvec_jointState] at h
  exact h

end QuantumQueryComplexity
