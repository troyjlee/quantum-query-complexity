import QuantumQueryComplexity.Quantum.PolynomialMethod
import QuantumQueryComplexity.Quantum.XorOracle
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The polynomial method for the XOR oracle

The same induction as `PolynomialMethod.lean`, run on the XOR-oracle semantics `xorState`
of `Quantum/XorOracle.lean`.  The XOR oracle is again a selector oracle (idle at index
`none`; at index `some i` the answer register is XORed with the bit `a i`), so the shared
lemma `HasAmpPoly.selector` applies directly and the degree bound is `2·t` — the model
simulation of `Quantum/Simulation.lean` is not used, which would have cost a factor two.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {W : Type} [Fintype W] [DecidableEq W]
variable {O : Type} [DecidableEq O]

/-- The XOR oracle is a selector oracle. -/
lemma xorOracleMap_selector (p : QBasis ι Bool W) :
    (∀ a : ι → Bool, xorOracleMap a p = p) ∨
      ∃ i p₀ p₁, ∀ a : ι → Bool, xorOracleMap a p = if a i then p₁ else p₀ := by
  obtain ⟨(_ | i), s, w⟩ := p
  · exact Or.inl fun a => rfl
  · refine Or.inr ⟨i, (some i, optXor s (some false), w), (some i, optXor s (some true), w),
      fun a => ?_⟩
    rw [xorOracleMap_some]
    cases a i <;> simp

/-- **XOR amplitudes after `t` queries have degree at most `t`.** -/
theorem hasAmpPoly_xorState (A : QAlg ι Bool O W) (t : ℕ) :
    HasAmpPoly (fun a => xorState A a t) t := by
  induction t with
  | zero => exact (hasAmpPoly_const A.init).mulVec (A.step 0)
  | succ t ih =>
      have h1 := ih.selector (fun a => xorOracleMap a) xorOracleMap_selector
      have h2 : (fun a (p : QBasis ι Bool W) => xorState A a t (xorOracleMap a p))
          = fun a => xorOracleMat a *ᵥ xorState A a t := by
        funext a p
        exact (xorOracleMat_mulVec_apply a _ p).symm
      rw [h2] at h1
      exact h1.mulVec (A.step (t + 1))

/-- **The polynomial method, XOR oracle**: the acceptance probability after `t` XOR
queries is a real polynomial of total degree at most `2·t`. -/
theorem exists_xor_probability_polynomial (A : QAlg ι Bool O W) (t : ℕ) (o : O) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧
      ∀ a, evalBool p a = qProb A.readout (xorState A a t) o :=
  (hasAmpPoly_xorState A t).exists_qProb_polynomial A.readout o

/-- The probability of an event, XOR oracle. -/
theorem exists_xor_event_polynomial (A : QAlg ι Bool O W) (t : ℕ) (E : Finset O) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧
      ∀ a, evalBool p a = ∑ o ∈ E, qProb A.readout (xorState A a t) o :=
  (hasAmpPoly_xorState A t).exists_event_polynomial A.readout E

variable {X : Type} [Fintype X]

/-- **Correctness transfers to the polynomial**, XOR oracle. -/
theorem XorComputesWithErrorOn.abs_prob_sub_bit_le {A : QAlg ι Bool Bool W} {t : ℕ}
    {read : X → ι → Bool} {f : X → Bool} {ε : ℝ}
    (h : XorComputesWithErrorOn A t read f ε) (x : X) :
    |qProb A.readout (xorState A (read x) t) true - bit (f x)| ≤ ε :=
  abs_qProb_true_sub_bit_le (xorState_isQState A _ t) (h x)

/-- **The approximating polynomial of a bounded-error XOR algorithm.** -/
theorem XorComputesWithErrorOn.exists_approx_polynomial {A : QAlg ι Bool Bool W} {t : ℕ}
    {read : X → ι → Bool} {f : X → Bool} {ε : ℝ}
    (h : XorComputesWithErrorOn A t read f ε) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧ ApproximatesOn p read f ε ∧
      ∀ a, 0 ≤ evalBool p a ∧ evalBool p a ≤ 1 := by
  obtain ⟨p, hdeg, heval⟩ := exists_xor_probability_polynomial A t true
  refine ⟨p, hdeg, fun x => ?_, fun a => ?_⟩
  · rw [heval]
    exact h.abs_prob_sub_bit_le x
  · rw [heval]
    exact ⟨qProb_nonneg _ _ _, qProb_le_one_of_isQState (xorState_isQState A a t) true⟩

end QuantumQueryComplexity
