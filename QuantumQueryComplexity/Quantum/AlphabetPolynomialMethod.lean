import QuantumQueryComplexity.Quantum.PolynomialLowerBound

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The polynomial method for inputs over a finite alphabet

For inputs `a : ι → σ` the natural polynomial variables are the indicators
`δ_{i,j}(a) = [a i = j]`, one for each pair `(i, j) : ι × σ` (S. Aaronson, *Quantum lower bound
for the collision problem*, STOC 2002; used by Kutin, Theory of Computing 1 (2005), §2.1). The
input is then the Boolean point `oneHot a : ι × σ → Bool`, and polynomials are elements of
`MvPolynomial (ι × σ) ℝ` evaluated at it (`evalBool p (oneHot a)`).

A native query (`oracleMap`) sends the basis state `(some i, s, w)` to
`(some i, swap none (some (a i)) s, w)`: the new basis state is selected by the **value** `a i`,
one of `|σ|` options, not by one bit. The new amplitude is therefore
`∑_j δ_{i,j} · Φ(p_j)` — one degree higher — and this agrees with the amplitude at the one-hot
points, where exactly one `δ_{i,j}` equals `1`. So the representation is required only at the
one-hot points (`HasOneHotAmpPoly`), and the Boolean API (`HasAmpPoly`, which represents at every
point of the cube) is left unchanged.

Main statements:

* `QAlg.hasOneHotAmpPoly_state`: after `t` queries the amplitudes have degree `≤ t` in the
  `δ_{i,j}`;
* `QAlg.exists_probability_polynomial_oneHot`, `QAlg.exists_event_polynomial_oneHot`: output
  probabilities are polynomials of degree `≤ 2·t`, exactly, at every input `a : ι → σ`;
* `ComputesWithErrorOn.exists_approx_polynomial_oneHot`: a `t`-query algorithm with error `ε`
  on a promise gives a degree-`≤ 2t` polynomial within `ε` of `bit ∘ f` on the promise, with
  values in `[0, 1]` at **every** input `a : ι → σ` (not only on the promise);
* the lower-bound interface `OneHotPolyObstructionOn`, `lt_two_mul_of_computes_oneHot`,
  `lt_two_mul_qQueryOn_oneHot`, `lt_two_mul_qQueryOn_oneHot_of_det`, mirroring
  `Quantum/PolynomialLowerBound.lean`. The obstruction only has to rule out polynomials that are
  bounded in `[0, 1]` at every input, which is what symmetrization arguments need.
-/

namespace QuantumQueryComplexity

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

/-- **The one-hot encoding** of an input: `oneHot a (i, j)` says whether `a i = j`. -/
def oneHot (a : ι → σ) : ι × σ → Bool := fun q => decide (a q.1 = q.2)

@[simp] lemma oneHot_apply (a : ι → σ) (i : ι) (j : σ) :
    oneHot a (i, j) = decide (a i = j) := rfl

/-- `φ` has a representation of degree at most `t` **at the one-hot points**: amplitude
polynomials in the variables `δ_{i,j}` of degree at most `t` whose values at `oneHot a` are
`φ a`. -/
def HasOneHotAmpPoly {B : Type} (φ : (ι → σ) → B → ℂ) (t : ℕ) : Prop :=
  ∃ Φ : B → AmpPoly (ι × σ), (∀ b, (Φ b).DegLe t) ∧ ∀ a b, (Φ b).evalC (oneHot a) = φ a b

variable {O : Type} [DecidableEq O]
variable {W : Type} [Fintype W] [DecidableEq W]

open scoped Matrix

/-! ## Closure properties of one-hot representations -/

section Closure

variable {B : Type} {φ : (ι → σ) → B → ℂ} {t : ℕ}

/-- Multiplication of both parts of an amplitude polynomial by the variable `X q`. -/
private noncomputable def mulVar {κ : Type} (q : κ) (P : AmpPoly κ) : AmpPoly κ :=
  ⟨MvPolynomial.X q * P.re, MvPolynomial.X q * P.im⟩

private lemma evalC_mulVar {κ : Type} (q : κ) (P : AmpPoly κ) (c : κ → Bool) :
    (mulVar q P).evalC c = (bit (c q) : ℂ) * P.evalC c := by
  apply Complex.ext <;> simp [mulVar, AmpPoly.evalC]

private lemma degLe_mulVar {κ : Type} (q : κ) {P : AmpPoly κ} (h : P.DegLe t) :
    (mulVar q P).DegLe (t + 1) := by
  have hX : (MvPolynomial.X q : MvPolynomial κ ℝ).totalDegree = 1 :=
    MvPolynomial.totalDegree_X q
  have h1 := h.1
  have h2 := h.2
  constructor
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)

private lemma hasOneHotAmpPoly_const (v : B → ℂ) :
    HasOneHotAmpPoly (fun _ : ι → σ => v) 0 :=
  ⟨fun b => AmpPoly.const (v b), fun _ => AmpPoly.degLe_const _ _,
    fun _ _ => AmpPoly.evalC_const _ _⟩

/-- An input-independent linear map preserves the degree bound. -/
private lemma HasOneHotAmpPoly.mulVec [Fintype B] (U : Matrix B B ℂ)
    (h : HasOneHotAmpPoly φ t) : HasOneHotAmpPoly (fun a => U *ᵥ φ a) t := by
  obtain ⟨Φ, hdeg, heval⟩ := h
  refine ⟨fun b => AmpPoly.sum Finset.univ fun c => AmpPoly.cmul (U b c) (Φ c),
    fun b => AmpPoly.degLe_sum _ _ fun c _ => AmpPoly.degLe_cmul _ _ (hdeg c), fun a b => ?_⟩
  simp [AmpPoly.evalC_sum, AmpPoly.evalC_cmul, heval, Matrix.mulVec, dotProduct]

/-- **A value-selector oracle raises the degree bound by one.** Every basis state is either
fixed or sent to a basis state selected by the value `a i` of one input coordinate. -/
private lemma HasOneHotAmpPoly.valueSelector (orc : (ι → σ) → B → B)
    (horc : ∀ p, (∀ a, orc a p = p) ∨ ∃ (i : ι) (g : σ → B), ∀ a, orc a p = g (a i))
    (h : HasOneHotAmpPoly φ t) : HasOneHotAmpPoly (fun a p => φ a (orc a p)) (t + 1) := by
  obtain ⟨Φ, hdeg, heval⟩ := h
  have key : ∀ p, ∃ Q : AmpPoly (ι × σ), Q.DegLe (t + 1) ∧
      ∀ a, Q.evalC (oneHot a) = φ a (orc a p) := by
    intro p
    rcases horc p with hid | ⟨i, g, hsel⟩
    · exact ⟨Φ p, (hdeg p).mono (Nat.le_succ t), fun a => by rw [heval, hid]⟩
    · refine ⟨AmpPoly.sum Finset.univ fun j => mulVar (i, j) (Φ (g j)),
        AmpPoly.degLe_sum _ _ fun j _ => degLe_mulVar _ (hdeg (g j)), fun a => ?_⟩
      rw [AmpPoly.evalC_sum, Finset.sum_eq_single (a i)]
      · simp [evalC_mulVar, heval, hsel]
      · intro j _ hj
        simp [evalC_mulVar, Ne.symm hj]
      · intro hi
        exact absurd (Finset.mem_univ _) hi
  choose Φ' hΦ' using key
  exact ⟨Φ', fun p => (hΦ' p).1, fun a p => (hΦ' p).2 a⟩

/-- The probability polynomial of a one-hot representation. -/
private theorem HasOneHotAmpPoly.exists_qProb_polynomial [Fintype B] [DecidableEq B]
    (h : HasOneHotAmpPoly φ t) (rd : B → O) (o : O) :
    ∃ p : MvPolynomial (ι × σ) ℝ, p.totalDegree ≤ 2 * t ∧
      ∀ a : ι → σ, evalBool p (oneHot a) = qProb rd (φ a) o := by
  obtain ⟨Φ, hdeg, heval⟩ := h
  obtain ⟨p, hp, hev⟩ := HasAmpPoly.exists_qProb_polynomial
    (φ := fun c b => (Φ b).evalC c) ⟨Φ, hdeg, fun _ _ => rfl⟩ rd o
  refine ⟨p, hp, fun a => ?_⟩
  rw [hev]
  congr 1
  funext b
  exact heval a b

/-- The event polynomial of a one-hot representation. -/
private theorem HasOneHotAmpPoly.exists_event_polynomial [Fintype B] [DecidableEq B]
    (h : HasOneHotAmpPoly φ t) (rd : B → O) (E : Finset O) :
    ∃ p : MvPolynomial (ι × σ) ℝ, p.totalDegree ≤ 2 * t ∧
      ∀ a : ι → σ, evalBool p (oneHot a) = ∑ o ∈ E, qProb rd (φ a) o := by
  obtain ⟨Φ, hdeg, heval⟩ := h
  obtain ⟨p, hp, hev⟩ := HasAmpPoly.exists_event_polynomial
    (φ := fun c b => (Φ b).evalC c) ⟨Φ, hdeg, fun _ _ => rfl⟩ rd E
  refine ⟨p, hp, fun a => ?_⟩
  rw [hev]
  refine Finset.sum_congr rfl fun o _ => ?_
  congr 1
  funext b
  exact heval a b

end Closure

/-- The native oracle is a value selector: idle on index `none`, and at index `some i` a
swap determined by the value `a i`. -/
private lemma oracleMap_valueSelector (p : QBasis ι σ W) :
    (∀ a : ι → σ, oracleMap a p = p) ∨
      ∃ (i : ι) (g : σ → QBasis ι σ W), ∀ a : ι → σ, oracleMap a p = g (a i) := by
  obtain ⟨(_ | i), s, w⟩ := p
  · exact Or.inl fun _ => rfl
  · exact Or.inr ⟨i, fun j => (some i, Equiv.swap none (some j) s, w), fun _ => rfl⟩

/-- **Amplitudes after `t` queries have degree at most `t`** in the one-hot variables. -/
theorem QAlg.hasOneHotAmpPoly_state (A : QAlg ι σ O W) (t : ℕ) :
    HasOneHotAmpPoly (fun a => A.state a t) t := by
  induction t with
  | zero => exact HasOneHotAmpPoly.mulVec (A.step 0) (hasOneHotAmpPoly_const A.init)
  | succ t ih =>
      have h1 := HasOneHotAmpPoly.valueSelector (fun a => oracleMap a) oracleMap_valueSelector ih
      have h2 : (fun a (p : QBasis ι σ W) => A.state a t (oracleMap a p))
          = fun a => oracleMat a *ᵥ A.state a t := by
        funext a p
        exact (oracleMat_mulVec_apply a _ p).symm
      rw [h2] at h1
      exact HasOneHotAmpPoly.mulVec (A.step (t + 1)) h1

/-- **The polynomial method over an alphabet**: the probability that a `t`-query algorithm
announces `o` is a real polynomial of total degree at most `2·t` in the one-hot variables,
exactly, at every input. -/
theorem QAlg.exists_probability_polynomial_oneHot (A : QAlg ι σ O W) (t : ℕ) (o : O) :
    ∃ p : MvPolynomial (ι × σ) ℝ, p.totalDegree ≤ 2 * t ∧
      ∀ a : ι → σ, evalBool p (oneHot a) = A.prob a t o :=
  HasOneHotAmpPoly.exists_qProb_polynomial (A.hasOneHotAmpPoly_state t) A.readout o

/-- The probability of announcing an output in `E`. -/
theorem QAlg.exists_event_polynomial_oneHot (A : QAlg ι σ O W) (t : ℕ) (E : Finset O) :
    ∃ p : MvPolynomial (ι × σ) ℝ, p.totalDegree ≤ 2 * t ∧
      ∀ a : ι → σ, evalBool p (oneHot a) = ∑ o ∈ E, A.prob a t o :=
  HasOneHotAmpPoly.exists_event_polynomial (A.hasOneHotAmpPoly_state t) A.readout E

variable {X : Type} [Fintype X]

/-- `p` approximates the Boolean function `f` on the promise observed through `read` within
`ε`, in the one-hot variables. -/
def OneHotApproximatesOn (p : MvPolynomial (ι × σ) ℝ) (read : X → ι → σ) (f : X → Bool)
    (ε : ℝ) : Prop :=
  ∀ x, |evalBool p (oneHot (read x)) - bit (f x)| ≤ ε

/-- **The approximating polynomial of a bounded-error algorithm over an alphabet**: degree at
most `2·t`, within `ε` of `bit ∘ f` on the promise, and with values in `[0, 1]` at every input
`a : ι → σ`. -/
theorem ComputesWithErrorOn.exists_approx_polynomial_oneHot {A : QAlg ι σ Bool W} {t : ℕ}
    {read : X → ι → σ} {f : X → Bool} {ε : ℝ} (h : ComputesWithErrorOn A t read f ε) :
    ∃ p : MvPolynomial (ι × σ) ℝ, p.totalDegree ≤ 2 * t ∧ OneHotApproximatesOn p read f ε ∧
      ∀ a : ι → σ, 0 ≤ evalBool p (oneHot a) ∧ evalBool p (oneHot a) ≤ 1 := by
  obtain ⟨p, hdeg, heval⟩ := A.exists_probability_polynomial_oneHot t true
  refine ⟨p, hdeg, fun x => ?_, fun a => ?_⟩
  · rw [heval]
    exact abs_qProb_true_sub_bit_le (A.state_isQState _ t) (h x)
  · rw [heval]
    exact ⟨A.prob_nonneg _ _ _, qProb_le_one_of_isQState (A.state_isQState a t) true⟩

/-- A degree-`d` obstruction over an alphabet: no polynomial of total degree at most `d` in the
one-hot variables that is bounded in `[0, 1]` at every input approximates `f` on the promise
within `ε`. -/
def OneHotPolyObstructionOn (read : X → ι → σ) (f : X → Bool) (ε : ℝ) (d : ℕ) : Prop :=
  ∀ p : MvPolynomial (ι × σ) ℝ, p.totalDegree ≤ d →
    (∀ a : ι → σ, 0 ≤ evalBool p (oneHot a) ∧ evalBool p (oneHot a) ≤ 1) →
    ¬ OneHotApproximatesOn p read f ε

variable {read : X → ι → σ} {f : X → Bool} {ε : ℝ} {d : ℕ}

/-- **Algorithm-level obstruction over an alphabet.** -/
theorem lt_two_mul_of_computes_oneHot (hobs : OneHotPolyObstructionOn read f ε d)
    {A : QAlg ι σ Bool W} {t : ℕ} (hA : ComputesWithErrorOn A t read f ε) : d < 2 * t := by
  obtain ⟨p, hdeg, happ, hbd⟩ := hA.exists_approx_polynomial_oneHot
  by_contra hle
  push Not at hle
  exact hobs p (hdeg.trans hle) hbd happ

/-- **Complexity-level obstruction over an alphabet**, with the achievable set assumed
nonempty. -/
theorem lt_two_mul_qQueryOn_oneHot (hne : (QueryCounts read f ε).Nonempty)
    (hobs : OneHotPolyObstructionOn read f ε d) : d < 2 * qQueryOn read f ε := by
  obtain ⟨W, hW, hWd, A, hA⟩ := exists_computes_qQueryOn hne
  exact lt_two_mul_of_computes_oneHot hobs hA

/-- The convenient form: read-determinacy and `0 ≤ ε` supply nonemptiness. -/
theorem lt_two_mul_qQueryOn_oneHot_of_det (hdet : ∀ x y, read x = read y → f x = f y)
    (hε : 0 ≤ ε) (hobs : OneHotPolyObstructionOn read f ε d) : d < 2 * qQueryOn read f ε :=
  lt_two_mul_qQueryOn_oneHot (queryCounts_nonempty hdet hε) hobs

end QuantumQueryComplexity
