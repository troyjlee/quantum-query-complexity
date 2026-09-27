import QuantumQueryComplexity.LearningGraph.Defs
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# k-distinctness

`kdFun k x` asks whether some value appears at least `k` times in the input
word `x : ι → σ`: positively certified by an injective tuple
`a : Fin k → ι` on which `x` is constant.  As for element distinctness, the
sink predicate of the learning-graph flow is "the loaded set contains *some*
`k`-collision of `x`" — choice-free, and it certifies positivity: a negative
input agreeing with `x` on such a set would own the same `k`-collision.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [DecidableEq σ]

/-- k-distinctness: `true` iff some value is taken by `k` distinct
coordinates.  (The tuple form is what `Classical.choose` extracts a
collision from.) -/
def kdFun (k : ℕ) (x : ι → σ) : Bool :=
  decide (∃ a : Fin k → ι, Function.Injective a ∧
    ∀ i j : Fin k, x (a i) = x (a j))

lemma kdFun_eq_true_iff {k : ℕ} {x : ι → σ} :
    kdFun k x = true ↔ ∃ a : Fin k → ι, Function.Injective a ∧
      ∀ i j : Fin k, x (a i) = x (a j) := by
  rw [kdFun, decide_eq_true_eq]

lemma kdFun_eq_false_iff {k : ℕ} {x : ι → σ} :
    kdFun k x = false ↔ ∀ a : Fin k → ι, Function.Injective a →
      ∃ i j : Fin k, x (a i) ≠ x (a j) := by
  rw [kdFun, decide_eq_false_iff_not]
  constructor
  · intro h a hinj
    by_contra hno
    push_neg at hno
    exact h ⟨a, hinj, hno⟩
  · rintro h ⟨a, hinj, hconst⟩
    obtain ⟨i, j, hne⟩ := h a hinj
    exact hne (hconst i j)

/-- The sink predicate: the loaded set contains a `k`-collision of `x`. -/
def kdSink (k : ℕ) (x : ι → σ) (S : Finset ι) : Prop :=
  ∃ a : Fin k → ι, Function.Injective a ∧ (∀ i, a i ∈ S) ∧
    ∀ i j : Fin k, x (a i) = x (a j)

/-- A `k`-collision-containing set certifies positivity: every negative
input differs from `x` somewhere on it. -/
lemma kdSink_cert {k : ℕ} {x y : ι → σ} (hy : kdFun k y = false)
    {S : Finset ι} (h : kdSink k x S) : ∃ i ∈ S, x i ≠ y i := by
  obtain ⟨a, hinj, hmem, hconst⟩ := h
  by_contra hall
  push_neg at hall
  obtain ⟨i, j, hne⟩ := kdFun_eq_false_iff.mp hy a hinj
  refine hne ?_
  rw [← hall (a i) (hmem i), ← hall (a j) (hmem j)]
  exact hconst i j

end QuantumQueryComplexity
