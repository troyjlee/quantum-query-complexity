import QuantumQueryComplexity.Quantum.Complexity

set_option linter.style.header false

/-!
# Readings that factor through another reading

An algorithm for the problem `(read', g)` also solves `(read' ∘ e, g ∘ e)`, for
any map `e` into the promise domain of `read'`: run it on the observations
`read' (e x)`.  This is the general form of `qQueryOn_comp_read_le_qQuery`
(there `read' = id` on the total cube); it is what turns an adversary bound
read through an encoding into a lower bound for a *promise* problem whose
domain contains the encoded inputs.
-/

namespace QuantumQueryComplexity

variable {ι σ O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [DecidableEq O]
variable {X X' : Type} [Fintype X] [Fintype X']

/-- An algorithm for `(read', g)`, run on observations that factor through `read'`. -/
theorem computesWithErrorOn_comp {W : Type} [Fintype W] [DecidableEq W]
    {A : QAlg ι σ O W} {q : ℕ} {read' : X' → ι → σ} {g : X' → O} {ε : ℝ}
    (h : ComputesWithErrorOn A q read' g ε) (e : X → X') :
    ComputesWithErrorOn A q (fun x => read' (e x)) (fun x => g (e x)) ε :=
  fun x => h (e x)

theorem queryCounts_subset_comp (e : X → X') (read' : X' → ι → σ) (g : X' → O) (ε : ℝ) :
    QueryCounts read' g ε ⊆ QueryCounts (fun x => read' (e x)) (fun x => g (e x)) ε := by
  rintro q ⟨W, hW, hW', A, hA⟩
  exact ⟨W, hW, hW', A, computesWithErrorOn_comp hA e⟩

/-- **Factoring bound**: `Q_ε(g ∘ e, read through read' ∘ e) ≤ Q_ε(g, read through read')`. -/
theorem qQueryOn_comp_le (e : X → X') (read' : X' → ι → σ) (g : X' → O) {ε : ℝ}
    (hne : (QueryCounts read' g ε).Nonempty) :
    qQueryOn (fun x => read' (e x)) (fun x => g (e x)) ε ≤ qQueryOn read' g ε :=
  Nat.sInf_le (queryCounts_subset_comp e read' g ε (Nat.sInf_mem hne))

end QuantumQueryComplexity
