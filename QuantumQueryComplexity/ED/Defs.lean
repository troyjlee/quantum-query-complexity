import QuantumQueryComplexity.LearningGraph.Defs
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Element distinctness

`edFun x` asks whether the input word `x : ι → σ` repeats a value.  A
positive input owns a collision pair, a negative input is injective.  The
sink predicate of the learning-graph flow is "the loaded set contains *some*
collision": it is deliberately weaker than "contains the chosen pair", so
that no choice function appears in the structure, and it certifies
positivity — an injective input cannot agree with `x` on a collision pair.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [DecidableEq σ]

/-- Element distinctness: `true` iff some value is repeated.  (The pair form
of the quantifier is what `Classical.choose` extracts a collision from.) -/
def edFun (x : ι → σ) : Bool :=
  decide (∃ q : ι × ι, q.1 ≠ q.2 ∧ x q.1 = x q.2)

lemma edFun_eq_true_iff {x : ι → σ} :
    edFun x = true ↔ ∃ q : ι × ι, q.1 ≠ q.2 ∧ x q.1 = x q.2 := by
  rw [edFun, decide_eq_true_eq]

lemma edFun_eq_false_iff {x : ι → σ} :
    edFun x = false ↔ ∀ i j : ι, x i = x j → i = j := by
  rw [edFun, decide_eq_false_iff_not]
  constructor
  · intro h i j hxy
    by_contra hne
    exact h ⟨(i, j), hne, hxy⟩
  · rintro h ⟨q, hne, hxy⟩
    exact hne (h q.1 q.2 hxy)

/-- The sink predicate: the loaded set contains a collision of `x`. -/
def edSink (x : ι → σ) (S : Finset ι) : Prop :=
  ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ x i = x j

/-- A collision-containing set certifies positivity: every negative
(injective) input differs from `x` somewhere on it. -/
lemma edSink_cert {x y : ι → σ} (hy : edFun y = false) {S : Finset ι}
    (h : edSink x S) : ∃ i ∈ S, x i ≠ y i := by
  obtain ⟨i, hiS, j, hjS, hij, hxx⟩ := h
  by_contra hall
  push_neg at hall
  have h1 : x i = y i := hall i hiS
  have h2 : x j = y j := hall j hjS
  refine hij (edFun_eq_false_iff.mp hy i j ?_)
  rw [← h1, ← h2]
  exact hxx

end QuantumQueryComplexity
