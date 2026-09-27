import QuantumQueryComplexity.Polynomial.Boolean
import QuantumQueryComplexity.Quantum.Algorithm
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The polynomial method (Beals–Buhrman–Cleve–Mosca–de Wolf)

A quantum algorithm making `t` queries to a Boolean input has, at every basis state, an
amplitude whose real and imaginary parts are real polynomials of total degree at most `t`
in the input bits; its acceptance probabilities are therefore polynomials of degree at most
`2·t`.  This is Lemmas 4.1 and 4.2 of *Quantum Lower Bounds by Polynomials*
(arXiv:quant-ph/9802049), proved here from the operational model of `Quantum/Algorithm.lean`.

The induction is stated once, for an arbitrary finite basis `B` and any oracle whose
action on a basis state is either input-independent or selected by one input bit
(`HasAmpPoly.selector`); the native value oracle (`oracleMap`) and the XOR oracle
(`XorPolynomialMethod.lean`) are two instances.  No query simulation between the models
is used, so both get the degree bound `2·t`, never `4·t`.

Main statements:

* `QAlg.hasAmpPoly_state`: the amplitudes after `t` queries have degree `≤ t`;
* `QAlg.exists_probability_polynomial`: `∃ p, p.totalDegree ≤ 2·t ∧ ∀ a, evalBool p a = A.prob a t o`;
* `QAlg.exists_event_polynomial`: the same for the probability of a set of outputs;
* `ComputesWithErrorOn.exists_approx_polynomial`: a `t`-query algorithm computing a
  Boolean `f` on a promise with error `ε` yields a degree-`≤ 2t` polynomial within `ε` of
  `bit ∘ f` on the promise, with values in `[0, 1]` on the whole cube.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Representations of input-dependent vectors -/

/-- `Represents Φ φ t`: the amplitude polynomials `Φ b` represent the input-dependent vector
`φ`, with both parts of degree at most `t`. -/
def Represents {B : Type} (Φ : B → AmpPoly ι) (φ : (ι → Bool) → B → ℂ) (t : ℕ) : Prop :=
  (∀ b, (Φ b).DegLe t) ∧ ∀ a b, (Φ b).evalC a = φ a b

/-- `φ` has a representation of degree at most `t`. -/
def HasAmpPoly {B : Type} (φ : (ι → Bool) → B → ℂ) (t : ℕ) : Prop :=
  ∃ Φ : B → AmpPoly ι, Represents Φ φ t

variable {B : Type} {φ : (ι → Bool) → B → ℂ} {t : ℕ}

lemma hasAmpPoly_const (v : B → ℂ) : HasAmpPoly (fun _ : ι → Bool => v) 0 :=
  ⟨fun b => AmpPoly.const (v b), fun _ => AmpPoly.degLe_const _ _,
    fun _ _ => AmpPoly.evalC_const _ _⟩

lemma HasAmpPoly.mono (h : HasAmpPoly φ t) {t' : ℕ} (htt : t ≤ t') : HasAmpPoly φ t' := by
  obtain ⟨Φ, hdeg, heval⟩ := h
  exact ⟨Φ, fun b => (hdeg b).mono htt, heval⟩

/-- **An input-independent linear map preserves the degree bound.** -/
lemma HasAmpPoly.mulVec [Fintype B] (U : Matrix B B ℂ) (h : HasAmpPoly φ t) :
    HasAmpPoly (fun a => U *ᵥ φ a) t := by
  obtain ⟨Φ, hdeg, heval⟩ := h
  refine ⟨fun b => AmpPoly.sum Finset.univ fun c => AmpPoly.cmul (U b c) (Φ c),
    fun b => AmpPoly.degLe_sum _ _ fun c _ => AmpPoly.degLe_cmul _ _ (hdeg c), fun a b => ?_⟩
  simp [AmpPoly.evalC_sum, AmpPoly.evalC_cmul, heval, Matrix.mulVec, dotProduct]

/-- **A selector oracle raises the degree bound by one.**  An oracle whose action on each
basis state is either input-independent or the choice between two fixed basis states made
by one input bit. -/
lemma HasAmpPoly.selector (orc : (ι → Bool) → B → B)
    (horc : ∀ p, (∀ a, orc a p = p) ∨ ∃ i p₀ p₁, ∀ a, orc a p = if a i then p₁ else p₀)
    (h : HasAmpPoly φ t) : HasAmpPoly (fun a p => φ a (orc a p)) (t + 1) := by
  obtain ⟨Φ, hdeg, heval⟩ := h
  have key : ∀ p, ∃ Q : AmpPoly ι, Q.DegLe (t + 1) ∧ ∀ a, Q.evalC a = φ a (orc a p) := by
    intro p
    rcases horc p with hid | ⟨i, p₀, p₁, hsel⟩
    · exact ⟨Φ p, (hdeg p).mono (Nat.le_succ t), fun a => by rw [heval, hid]⟩
    · refine ⟨AmpPoly.select i (Φ p₀) (Φ p₁), AmpPoly.degLe_select i (hdeg p₀) (hdeg p₁),
        fun a => ?_⟩
      rw [AmpPoly.evalC_select, hsel a]
      split_ifs <;> rw [heval]
  choose Φ' hΦ' using key
  exact ⟨Φ', fun p => (hΦ' p).1, fun a p => (hΦ' p).2 a⟩

/-! ## From amplitudes to probabilities -/

variable {O : Type} [DecidableEq O]

/-- **The probability polynomial**: the measured probability of an output is a real
polynomial of degree at most `2·t`. -/
theorem HasAmpPoly.exists_qProb_polynomial [Fintype B] (h : HasAmpPoly φ t) (rd : B → O)
    (o : O) : ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧
      ∀ a, evalBool p a = qProb rd (φ a) o := by
  obtain ⟨Φ, hdeg, heval⟩ := h
  refine ⟨∑ b ∈ Finset.univ.filter (fun b => rd b = o), (Φ b).normSqPoly,
    totalDegree_finsetSum_le _ _ fun b _ => AmpPoly.totalDegree_normSqPoly_le _ (hdeg b),
    fun a => ?_⟩
  rw [evalBool_sum, qProb, Finset.sum_filter]
  exact Finset.sum_congr rfl fun b _ => by
    split_ifs
    · rw [AmpPoly.evalBool_normSqPoly, heval]
    · rfl

/-- The probability of an event (a finite set of outputs). -/
theorem HasAmpPoly.exists_event_polynomial [Fintype B] (h : HasAmpPoly φ t) (rd : B → O)
    (E : Finset O) : ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧
      ∀ a, evalBool p a = ∑ o ∈ E, qProb rd (φ a) o := by
  have key : ∀ o : O, ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧
      ∀ a, evalBool p a = qProb rd (φ a) o := fun o => h.exists_qProb_polynomial rd o
  choose P hP using key
  refine ⟨∑ o ∈ E, P o, totalDegree_finsetSum_le _ _ fun o _ => (hP o).1, fun a => ?_⟩
  rw [evalBool_sum]
  exact Finset.sum_congr rfl fun o _ => (hP o).2 a

/-! ## The native value oracle -/

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The native oracle is a selector oracle: idle on index `none`, and at index `some i` a
swap determined by the bit `a i`. -/
lemma oracleMap_selector (p : QBasis ι Bool W) :
    (∀ a : ι → Bool, oracleMap a p = p) ∨
      ∃ i p₀ p₁, ∀ a : ι → Bool, oracleMap a p = if a i then p₁ else p₀ := by
  obtain ⟨(_ | i), s, w⟩ := p
  · exact Or.inl fun a => rfl
  · refine Or.inr ⟨i, (some i, Equiv.swap none (some false) s, w),
      (some i, Equiv.swap none (some true) s, w), fun a => ?_⟩
    rw [oracleMap_some]
    cases a i <;> simp

/-- **Amplitudes after `t` queries have degree at most `t`** (BBCMW Lemma 4.1). -/
theorem QAlg.hasAmpPoly_state (A : QAlg ι Bool O W) (t : ℕ) :
    HasAmpPoly (fun a => A.state a t) t := by
  induction t with
  | zero => exact (hasAmpPoly_const A.init).mulVec (A.step 0)
  | succ t ih =>
      have h1 := ih.selector (fun a => oracleMap a) oracleMap_selector
      have h2 : (fun a (p : QBasis ι Bool W) => A.state a t (oracleMap a p))
          = fun a => oracleMat a *ᵥ A.state a t := by
        funext a p
        exact (oracleMat_mulVec_apply a _ p).symm
      rw [h2] at h1
      exact h1.mulVec (A.step (t + 1))

/-- **The polynomial method** (BBCMW Lemma 4.2): the probability that a `t`-query
algorithm announces `o` is a real polynomial of total degree at most `2·t` in the input
bits, exactly, on the whole Boolean cube. -/
theorem QAlg.exists_probability_polynomial (A : QAlg ι Bool O W) (t : ℕ) (o : O) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧ ∀ a, evalBool p a = A.prob a t o :=
  (A.hasAmpPoly_state t).exists_qProb_polynomial A.readout o

/-- The probability of announcing an output in `E`. -/
theorem QAlg.exists_event_polynomial (A : QAlg ι Bool O W) (t : ℕ) (E : Finset O) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧
      ∀ a, evalBool p a = ∑ o ∈ E, A.prob a t o :=
  (A.hasAmpPoly_state t).exists_event_polynomial A.readout E

/-! ## Probability bounds on the whole cube -/

/-- A measured probability never exceeds the squared norm (no finiteness of the output
type needed). -/
lemma qProb_le_one_of_isQState {H : Type} [Fintype H] [DecidableEq H] {rd : H → O} {ψ : H → ℂ}
    (hψ : IsQState ψ) (o : O) : qProb rd ψ o ≤ 1 := by
  rw [← hψ, qProb, qNormSq_def]
  exact Finset.sum_le_sum fun h _ => by
    split_ifs
    · exact le_rfl
    · exact Complex.normSq_nonneg _

lemma QAlg.prob_le_one' (A : QAlg ι Bool O W) (a : ι → Bool) (t : ℕ) (o : O) :
    A.prob a t o ≤ 1 :=
  qProb_le_one_of_isQState (A.state_isQState a t) o

/-- With finitely many outputs the output polynomials sum to `1` on the cube. -/
theorem QAlg.sum_prob_eq_one [Fintype O] (A : QAlg ι Bool O W) (a : ι → Bool) (t : ℕ) :
    ∑ o, A.prob a t o = 1 :=
  sum_qProb_eq_one (A.state_isQState a t) A.readout

/-! ## Correctness: the acceptance polynomial approximates the function -/

variable {X : Type} [Fintype X]

/-- `p` approximates the Boolean function `f` on the promise `read` within `ε`. -/
def ApproximatesOn (p : MvPolynomial ι ℝ) (read : X → ι → Bool) (f : X → Bool) (ε : ℝ) :
    Prop :=
  ∀ x, |evalBool p (read x) - bit (f x)| ≤ ε

/-- Two probabilities of a Boolean-output algorithm: correctness on `true` and on
`false`, translated into a two-sided bound on the acceptance probability. -/
lemma abs_qProb_true_sub_bit_le {H : Type} [Fintype H] [DecidableEq H] {rd : H → Bool} {ψ : H → ℂ}
    (hψ : IsQState ψ) {b : Bool} {ε : ℝ} (h : 1 - ε ≤ qProb rd ψ b) :
    |qProb rd ψ true - bit b| ≤ ε := by
  have h0 : 0 ≤ qProb rd ψ true := qProb_nonneg _ _ _
  have h1 : qProb rd ψ true ≤ 1 := qProb_le_one_of_isQState hψ true
  cases b with
  | true =>
      rw [bit_true, abs_le]
      constructor <;> linarith
  | false =>
      have hsum : qProb rd ψ true + qProb rd ψ false ≤ 1 :=
        qProb_add_qProb_le_one hψ rd (by decide)
      rw [bit_false, sub_zero, abs_le]
      constructor <;> linarith

/-- **Correctness transfers to the polynomial.** -/
theorem ComputesWithErrorOn.abs_prob_sub_bit_le {A : QAlg ι Bool Bool W} {t : ℕ}
    {read : X → ι → Bool} {f : X → Bool} {ε : ℝ} (h : ComputesWithErrorOn A t read f ε)
    (x : X) : |A.prob (read x) t true - bit (f x)| ≤ ε :=
  abs_qProb_true_sub_bit_le (A.state_isQState _ t) (h x)

/-- **The approximating polynomial of a bounded-error algorithm**: degree at most `2·t`,
within `ε` of `bit ∘ f` on the promise, and with values in `[0, 1]` on the entire cube. -/
theorem ComputesWithErrorOn.exists_approx_polynomial {A : QAlg ι Bool Bool W} {t : ℕ}
    {read : X → ι → Bool} {f : X → Bool} {ε : ℝ} (h : ComputesWithErrorOn A t read f ε) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧ ApproximatesOn p read f ε ∧
      ∀ a, 0 ≤ evalBool p a ∧ evalBool p a ≤ 1 := by
  obtain ⟨p, hdeg, heval⟩ := A.exists_probability_polynomial t true
  refine ⟨p, hdeg, fun x => ?_, fun a => ?_⟩
  · rw [heval]
    exact h.abs_prob_sub_bit_le x
  · rw [heval]
    exact ⟨A.prob_nonneg _ _ _, A.prob_le_one' _ _ _⟩

end QuantumQueryComplexity
