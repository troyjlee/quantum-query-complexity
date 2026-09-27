import QuantumQueryComplexity.Quantum.Algorithm
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Relations: the probability of a valid output

For `read : X → ι → σ` and a relation `Good : X → O → Prop`, the **success probability** of
an algorithm is the squared mass of the basis states whose readout is valid.  This is a
semantic definition: the Boolean readout `fun h => decide (Good x (A.readout h))` names an
*event*; it is never installed as an input-dependent readout of an algorithm.  A compiled
algorithm learns validity only through a query routine (`Amplitude/Marker.lean`).

* `goodProb rd Good ψ`, `successProbOn A q read Good x`;
* `SolvesWithErrorOn A q read Good ε`, monotone in `ε`;
* `solvesWithErrorOn_eq_iff`: for `Good x y ↔ y = f x` this is `ComputesWithErrorOn`;
* `goodProb_eq_sum`: with finitely many outputs, the sum of the valid outputs' probabilities.
-/

namespace QuantumQueryComplexity

variable {H : Type} [Fintype H] [DecidableEq H] {O : Type}

/-- The squared mass of `ψ` on the basis states whose readout satisfies `G`. -/
def goodProb (rd : H → O) (G : O → Prop) [DecidablePred G] (ψ : H → ℂ) : ℝ :=
  qProb (fun h => decide (G (rd h))) ψ true

lemma goodProb_eq_sum_ite (rd : H → O) (G : O → Prop) [DecidablePred G] (ψ : H → ℂ) :
    goodProb rd G ψ = ∑ h, if G (rd h) then Complex.normSq (ψ h) else 0 := by
  rw [goodProb, qProb]
  exact Finset.sum_congr rfl fun h _ => by simp only [decide_eq_true_eq]

lemma goodProb_nonneg (rd : H → O) (G : O → Prop) [DecidablePred G] (ψ : H → ℂ) :
    0 ≤ goodProb rd G ψ := qProb_nonneg _ _ _

lemma goodProb_le_qNormSq (rd : H → O) (G : O → Prop) [DecidablePred G] (ψ : H → ℂ) :
    goodProb rd G ψ ≤ qNormSq ψ := by
  rw [goodProb_eq_sum_ite, qNormSq_def]
  exact Finset.sum_le_sum fun h _ => by
    split_ifs
    · exact le_rfl
    · exact Complex.normSq_nonneg _

lemma goodProb_le_one (rd : H → O) (G : O → Prop) [DecidablePred G] {ψ : H → ℂ}
    (hψ : IsQState ψ) : goodProb rd G ψ ≤ 1 :=
  (goodProb_le_qNormSq rd G ψ).trans_eq hψ

omit [DecidableEq H] in
/-- With decidable equality on outputs: the valid outputs' probabilities, summed.  (No
`DecidableEq H`: rewriting with this lemma must not re-synthesize that instance on very
large workspaces.) -/
lemma goodProb_eq_sum [Fintype O] [DecidableEq O] (rd : H → O) (G : O → Prop)
    [DecidablePred G] (ψ : H → ℂ) :
    goodProb rd G ψ = ∑ y, if G y then qProb rd ψ y else 0 := by
  classical
  rw [goodProb_eq_sum_ite]
  simp only [qProb]
  rw [show (∑ y, if G y then ∑ h, (if rd h = y then Complex.normSq (ψ h) else 0) else 0)
      = ∑ y, ∑ h, if rd h = y then (if G y then Complex.normSq (ψ h) else 0) else 0 from
    Finset.sum_congr rfl fun y _ => by
      split_ifs
      · exact Finset.sum_congr rfl fun h _ => by split_ifs <;> rfl
      · exact (Finset.sum_eq_zero fun h _ => by split_ifs <;> rfl).symm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_ite_eq Finset.univ (rd h), if_pos (Finset.mem_univ _)]

/-- The equality relation: the valid mass is the probability of the right answer. -/
lemma goodProb_eq (rd : H → O) [DecidableEq O] (o : O) (ψ : H → ℂ) :
    goodProb rd (fun y => y = o) ψ = qProb rd ψ o := by
  rw [goodProb_eq_sum_ite, qProb]

variable {ι σ W X : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] [Fintype X]

/-- **The probability that `A`, after `q` queries on the promise input `x`, outputs a
value valid for `x`.** -/
def successProbOn (A : QAlg ι σ O W) (q : ℕ) (read : X → ι → σ) (Good : X → O → Prop)
    [∀ x, DecidablePred (Good x)] (x : X) : ℝ :=
  goodProb A.readout (Good x) (A.state (read x) q)

/-- **`A` solves the relation `Good` on the promise with error at most `ε`.** -/
def SolvesWithErrorOn (A : QAlg ι σ O W) (q : ℕ) (read : X → ι → σ) (Good : X → O → Prop)
    [∀ x, DecidablePred (Good x)] (ε : ℝ) : Prop :=
  ∀ x, 1 - ε ≤ successProbOn A q read Good x

section

variable {A : QAlg ι σ O W} {q : ℕ} {read : X → ι → σ} {Good : X → O → Prop}
  [∀ x, DecidablePred (Good x)]

lemma successProbOn_nonneg (x : X) : 0 ≤ successProbOn A q read Good x :=
  goodProb_nonneg _ _ _

lemma successProbOn_le_one (x : X) : successProbOn A q read Good x ≤ 1 :=
  goodProb_le_one _ _ (A.state_isQState _ _)

lemma SolvesWithErrorOn.mono {ε ε' : ℝ} (h : SolvesWithErrorOn A q read Good ε)
    (hε : ε ≤ ε') : SolvesWithErrorOn A q read Good ε' :=
  fun x => le_trans (by linarith) (h x)

end

/-- **Functions are relations**: for `Good x y ↔ y = f x`, solving is computing. -/
theorem solvesWithErrorOn_eq_iff [DecidableEq O] {A : QAlg ι σ O W} {q : ℕ}
    {read : X → ι → σ} {f : X → O} {ε : ℝ} :
    SolvesWithErrorOn A q read (fun x y => y = f x) ε ↔ ComputesWithErrorOn A q read f ε := by
  refine forall_congr' fun x => ?_
  rw [successProbOn, goodProb_eq]
  rfl

end QuantumQueryComplexity
