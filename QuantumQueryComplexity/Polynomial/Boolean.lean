import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.Complex.Basic
set_option linter.style.header false

/-!
# Real polynomials on the Boolean cube

The small algebra API behind the polynomial method (`Quantum/PolynomialMethod.lean`):

* `bit b`, the `0/1` real value of a Boolean, and `evalBool p a`, the evaluation of a real
  multivariate polynomial at a Boolean point of the cube (any finite index type `ι`);
* `select i P₀ P₁ = (1 − Xᵢ)·P₀ + Xᵢ·P₁`, which on the cube evaluates to the polynomial
  selected by the `i`-th bit and raises the degree bound by one — the one operation an
  oracle query performs on an amplitude;
* `AmpPoly ι`, a pair of real polynomials representing the real and imaginary parts of a
  complex amplitude, with the complex-scalar action and sums needed to push an
  input-independent unitary through a representation.  Working with two real
  polynomials avoids any coefficient-ring map: `Complex.re` is not a ring homomorphism.

Everything is stated for arbitrary finite `ι`, including `Fin n`.
-/

namespace QuantumQueryComplexity

open MvPolynomial

/-! ## Bits and evaluation -/

/-- The real value of a Boolean: `1` for `true`, `0` for `false`. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

@[simp] lemma bit_true : bit true = 1 := rfl
@[simp] lemma bit_false : bit false = 0 := rfl

lemma bit_nonneg (b : Bool) : 0 ≤ bit b := by cases b <;> simp
lemma bit_le_one (b : Bool) : bit b ≤ 1 := by cases b <;> simp
lemma one_sub_bit (b : Bool) : 1 - bit b = bit (!b) := by cases b <;> simp

variable {ι : Type*}

/-- Evaluating a real multivariate polynomial at a Boolean point of the cube. -/
noncomputable def evalBool (p : MvPolynomial ι ℝ) (a : ι → Bool) : ℝ :=
  MvPolynomial.eval (fun i => bit (a i)) p

@[simp] lemma evalBool_C (c : ℝ) (a : ι → Bool) : evalBool (C c) a = c := by
  simp [evalBool]

@[simp] lemma evalBool_X (i : ι) (a : ι → Bool) : evalBool (X i) a = bit (a i) := by
  simp [evalBool]

@[simp] lemma evalBool_add (p q : MvPolynomial ι ℝ) (a : ι → Bool) :
    evalBool (p + q) a = evalBool p a + evalBool q a := by
  simp [evalBool]

@[simp] lemma evalBool_sub (p q : MvPolynomial ι ℝ) (a : ι → Bool) :
    evalBool (p - q) a = evalBool p a - evalBool q a := by
  simp [evalBool]

@[simp] lemma evalBool_neg (p : MvPolynomial ι ℝ) (a : ι → Bool) :
    evalBool (-p) a = -evalBool p a := by
  simp [evalBool]

@[simp] lemma evalBool_mul (p q : MvPolynomial ι ℝ) (a : ι → Bool) :
    evalBool (p * q) a = evalBool p a * evalBool q a := by
  simp [evalBool]

@[simp] lemma evalBool_pow (p : MvPolynomial ι ℝ) (k : ℕ) (a : ι → Bool) :
    evalBool (p ^ k) a = evalBool p a ^ k := by
  simp [evalBool]

@[simp] lemma evalBool_zero (a : ι → Bool) : evalBool (0 : MvPolynomial ι ℝ) a = 0 := by
  simp [evalBool]

@[simp] lemma evalBool_one (a : ι → Bool) : evalBool (1 : MvPolynomial ι ℝ) a = 1 := by
  simp [evalBool]

lemma evalBool_sum {κ : Type*} (s : Finset κ) (p : κ → MvPolynomial ι ℝ) (a : ι → Bool) :
    evalBool (∑ k ∈ s, p k) a = ∑ k ∈ s, evalBool (p k) a := by
  simp [evalBool]

/-! ## Total-degree conveniences -/

lemma totalDegree_finsetSum_le {κ : Type*} (s : Finset κ) (p : κ → MvPolynomial ι ℝ)
    {d : ℕ} (h : ∀ k ∈ s, (p k).totalDegree ≤ d) : (∑ k ∈ s, p k).totalDegree ≤ d :=
  (MvPolynomial.totalDegree_finsetSum s p).trans (Finset.sup_le h)

lemma totalDegree_C_mul_le (c : ℝ) (p : MvPolynomial ι ℝ) :
    (C c * p).totalDegree ≤ p.totalDegree :=
  (MvPolynomial.totalDegree_mul _ _).trans (by simp)

lemma totalDegree_sq_le (p : MvPolynomial ι ℝ) {d : ℕ} (h : p.totalDegree ≤ d) :
    (p ^ 2).totalDegree ≤ 2 * d :=
  (MvPolynomial.totalDegree_pow _ _).trans (by omega)

/-! ## The selector -/

/-- `select i P₀ P₁ = (1 − Xᵢ)·P₀ + Xᵢ·P₁`: on the cube, `P₁` where the `i`-th bit is set
and `P₀` where it is not. -/
noncomputable def select (i : ι) (P₀ P₁ : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  (1 - X i) * P₀ + X i * P₁

lemma evalBool_select (i : ι) (P₀ P₁ : MvPolynomial ι ℝ) (a : ι → Bool) :
    evalBool (select i P₀ P₁) a = if a i then evalBool P₁ a else evalBool P₀ a := by
  simp only [select, evalBool_add, evalBool_mul, evalBool_sub, evalBool_one, evalBool_X]
  cases a i <;> simp

lemma totalDegree_select_le (i : ι) {P₀ P₁ : MvPolynomial ι ℝ} {t : ℕ}
    (h₀ : P₀.totalDegree ≤ t) (h₁ : P₁.totalDegree ≤ t) :
    (select i P₀ P₁).totalDegree ≤ t + 1 := by
  have hX : (X i : MvPolynomial ι ℝ).totalDegree ≤ 1 := le_of_eq (totalDegree_X i)
  have h1X : ((1 : MvPolynomial ι ℝ) - X i).totalDegree ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · simp
    · rw [totalDegree_neg]; exact hX
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_mul _ _).trans (by omega)
  · exact (totalDegree_mul _ _).trans (by omega)

/-! ## Amplitude polynomials

A complex amplitude, as a function of the input, is represented by two real polynomials:
its real and its imaginary part. -/

/-- A pair of real polynomials, standing for `re + im·I`. -/
structure AmpPoly (ι : Type*) where
  /-- The real part. -/
  re : MvPolynomial ι ℝ
  /-- The imaginary part. -/
  im : MvPolynomial ι ℝ

namespace AmpPoly

variable (P : AmpPoly ι)

/-- The complex value at a Boolean point. -/
noncomputable def evalC (P : AmpPoly ι) (a : ι → Bool) : ℂ :=
  ⟨evalBool P.re a, evalBool P.im a⟩

@[simp] lemma evalC_re (a : ι → Bool) : (P.evalC a).re = evalBool P.re a := rfl
@[simp] lemma evalC_im (a : ι → Bool) : (P.evalC a).im = evalBool P.im a := rfl

/-- Both parts have total degree at most `t`. -/
def DegLe (P : AmpPoly ι) (t : ℕ) : Prop := P.re.totalDegree ≤ t ∧ P.im.totalDegree ≤ t

lemma DegLe.mono {P : AmpPoly ι} {s t : ℕ} (h : P.DegLe s) (hst : s ≤ t) : P.DegLe t :=
  ⟨h.1.trans hst, h.2.trans hst⟩

/-- The constant amplitude `z`. -/
noncomputable def const (z : ℂ) : AmpPoly ι := ⟨C z.re, C z.im⟩

@[simp] lemma evalC_const (z : ℂ) (a : ι → Bool) : (const (ι := ι) z).evalC a = z := by
  apply Complex.ext <;> simp [const, evalC]

lemma degLe_const (z : ℂ) (t : ℕ) : (const (ι := ι) z).DegLe t := by
  constructor <;> simp [const]

/-- Multiplication by a fixed complex scalar `z`:
`(x + y I)(re + im I) = (x·re − y·im) + (y·re + x·im) I`. -/
noncomputable def cmul (z : ℂ) (P : AmpPoly ι) : AmpPoly ι :=
  ⟨C z.re * P.re - C z.im * P.im, C z.im * P.re + C z.re * P.im⟩

@[simp] lemma evalC_cmul (z : ℂ) (a : ι → Bool) : (cmul z P).evalC a = z * P.evalC a := by
  apply Complex.ext <;> simp [cmul, evalC, Complex.mul_re, Complex.mul_im] <;> ring

lemma degLe_cmul (z : ℂ) {t : ℕ} (h : P.DegLe t) : (cmul z P).DegLe t := by
  constructor
  · rw [cmul, sub_eq_add_neg]
    refine (totalDegree_add _ _).trans (max_le ((totalDegree_C_mul_le _ _).trans h.1) ?_)
    rw [totalDegree_neg]
    exact (totalDegree_C_mul_le _ _).trans h.2
  · exact (totalDegree_add _ _).trans
      (max_le ((totalDegree_C_mul_le _ _).trans h.1) ((totalDegree_C_mul_le _ _).trans h.2))

/-- The sum of a finite family. -/
noncomputable def sum {κ : Type*} (s : Finset κ) (P : κ → AmpPoly ι) : AmpPoly ι :=
  ⟨∑ k ∈ s, (P k).re, ∑ k ∈ s, (P k).im⟩

@[simp] lemma evalC_sum {κ : Type*} (s : Finset κ) (P : κ → AmpPoly ι) (a : ι → Bool) :
    (sum s P).evalC a = ∑ k ∈ s, (P k).evalC a := by
  apply Complex.ext <;> simp [sum, evalC, evalBool_sum, Complex.re_sum, Complex.im_sum]

lemma degLe_sum {κ : Type*} (s : Finset κ) (P : κ → AmpPoly ι) {t : ℕ}
    (h : ∀ k ∈ s, (P k).DegLe t) : (sum s P).DegLe t :=
  ⟨totalDegree_finsetSum_le _ _ fun k hk => (h k hk).1,
   totalDegree_finsetSum_le _ _ fun k hk => (h k hk).2⟩

/-- The selector, applied to both parts. -/
noncomputable def select (i : ι) (P₀ P₁ : AmpPoly ι) : AmpPoly ι :=
  ⟨QuantumQueryComplexity.select i P₀.re P₁.re, QuantumQueryComplexity.select i P₀.im P₁.im⟩

lemma evalC_select (i : ι) (P₀ P₁ : AmpPoly ι) (a : ι → Bool) :
    (select i P₀ P₁).evalC a = if a i then P₁.evalC a else P₀.evalC a := by
  apply Complex.ext
  · simp only [select, evalC_re, evalBool_select]; split_ifs <;> rfl
  · simp only [select, evalC_im, evalBool_select]; split_ifs <;> rfl

lemma degLe_select (i : ι) {P₀ P₁ : AmpPoly ι} {t : ℕ} (h₀ : P₀.DegLe t) (h₁ : P₁.DegLe t) :
    (select i P₀ P₁).DegLe (t + 1) :=
  ⟨totalDegree_select_le i h₀.1 h₁.1, totalDegree_select_le i h₀.2 h₁.2⟩

/-- The squared modulus `re² + im²`, a real polynomial of twice the degree. -/
noncomputable def normSqPoly (P : AmpPoly ι) : MvPolynomial ι ℝ := P.re ^ 2 + P.im ^ 2

lemma evalBool_normSqPoly (a : ι → Bool) :
    evalBool P.normSqPoly a = Complex.normSq (P.evalC a) := by
  simp [normSqPoly, Complex.normSq_apply, sq]

lemma totalDegree_normSqPoly_le {t : ℕ} (h : P.DegLe t) : P.normSqPoly.totalDegree ≤ 2 * t :=
  (totalDegree_add _ _).trans (max_le (totalDegree_sq_le _ h.1) (totalDegree_sq_le _ h.2))

end AmpPoly

end QuantumQueryComplexity
