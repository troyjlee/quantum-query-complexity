import QuantumQueryComplexity.Quantum.Complexity
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Classical postprocessing of the readout

Relabelling an algorithm's measurement outcome costs nothing: `QAlg.postcomp`
changes only the `readout` field, so the state — which is built from `init`
and `step` alone — is *literally unchanged*, and the fibre sum can only grow
the correct outcome's probability (`qProb_comp_ge`).

At the complexity level this is `qQueryOn_postcomp_le : Q_ε(g ∘ f) ≤ Q_ε(f)`,
the workhorse for reading a Boolean test off a large-valued output: it is how
a lower bound proved for a Boolean postprocessing transfers to the function
itself, and it is what makes lower bounds available for outputs whose type is
too big (or infinite) for the `Fintype`-output machinery.
-/

namespace QuantumQueryComplexity

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {X : Type}

/-- Post-composing the readout can only increase the probability of the
image outcome. -/
lemma qProb_comp_ge {H O O' : Type} [Fintype H]
    [DecidableEq O] [DecidableEq O'] (g : O → O') (r : H → O) (ψ : H → ℂ)
    (o : O) :
    qProb r ψ o ≤ qProb (fun h => g (r h)) ψ (g o) := by
  rw [qProb, qProb]
  refine Finset.sum_le_sum fun h _ => ?_
  by_cases hr : r h = o
  · rw [if_pos hr, if_pos (by rw [hr])]
  · rw [if_neg hr]
    by_cases hg : g (r h) = g o
    · rw [if_pos hg]
      exact Complex.normSq_nonneg _
    · rw [if_neg hg]

/-- **Relabelling the readout**: same initial state, same steps, composed
output map. -/
def QAlg.postcomp {O O' W : Type} [Fintype W] [DecidableEq W]
    (A : QAlg ι σ O W) (g : O → O') : QAlg ι σ O' W :=
  { A with readout := fun p => g (A.readout p) }

@[simp] lemma QAlg.postcomp_step {O O' W : Type} [Fintype W] [DecidableEq W]
    (A : QAlg ι σ O W) (g : O → O') : (A.postcomp g).step = A.step := rfl

@[simp] lemma QAlg.postcomp_init {O O' W : Type} [Fintype W] [DecidableEq W]
    (A : QAlg ι σ O W) (g : O → O') : (A.postcomp g).init = A.init := rfl

@[simp] lemma QAlg.postcomp_state {O O' W : Type} [Fintype W] [DecidableEq W]
    (A : QAlg ι σ O W) (g : O → O') (a : ι → σ) (t : ℕ) :
    (A.postcomp g).state a t = A.state a t := by
  induction t with
  | zero =>
      rw [QAlg.state_zero, QAlg.state_zero, QAlg.postcomp_step,
        QAlg.postcomp_init]
  | succ t ih =>
      rw [QAlg.state_succ, QAlg.state_succ, ih, QAlg.postcomp_step]

@[simp] lemma QAlg.postcomp_readout {O O' W : Type} [Fintype W] [DecidableEq W]
    (A : QAlg ι σ O W) (g : O → O') :
    (A.postcomp g).readout = fun p => g (A.readout p) := rfl

/-- **Post-composition at the algorithm level**: same cost, same error, the
composed function. -/
theorem ComputesWithErrorOn.postcomp {O O' W : Type} [DecidableEq O]
    [DecidableEq O'] [Fintype W] [DecidableEq W]
    {A : QAlg ι σ O W} {q : ℕ} {read : X → ι → σ} {F : X → O} {ε : ℝ}
    (h : ComputesWithErrorOn A q read F ε) (g : O → O') :
    ComputesWithErrorOn (A.postcomp g) q read (fun x => g (F x)) ε := by
  intro x
  refine (h x).trans ?_
  rw [QAlg.prob, QAlg.prob, QAlg.postcomp_state, QAlg.postcomp_readout]
  exact qProb_comp_ge g A.readout (A.state (read x) q) (F x)

/-- The workspace-existential form, for callers that quantify it away. -/
theorem ComputesWithErrorOn.exists_postcomp {O O' W : Type} [DecidableEq O]
    [DecidableEq O'] [Fintype W] [DecidableEq W]
    {A : QAlg ι σ O W} {q : ℕ} {read : X → ι → σ} {F : X → O} {ε : ℝ}
    (h : ComputesWithErrorOn A q read F ε) (g : O → O') :
    ∃ (W' : Type) (_ : Fintype W') (_ : DecidableEq W')
      (A' : QAlg ι σ O' W'),
      ComputesWithErrorOn A' q read (fun x => g (F x)) ε :=
  ⟨W, inferInstance, inferInstance, A.postcomp g, h.postcomp g⟩

/-- Every achievable query count survives postprocessing — the mirror of
`queryCounts_subset_of_read`. -/
theorem queryCounts_postcomp [Fintype X] {O O' : Type} [DecidableEq O]
    [DecidableEq O'] (g : O → O') (read : X → ι → σ) (f : X → O) (ε : ℝ) :
    QueryCounts read f ε ⊆ QueryCounts read (fun x => g (f x)) ε := by
  rintro q ⟨W, hW, hW', A, hA⟩
  exact ⟨W, hW, hW', A.postcomp g, hA.postcomp g⟩

/-- **Classical postprocessing of the readout is free**: post-composing the
output function can only lower the quantum query complexity. -/
theorem qQueryOn_postcomp_le [Fintype X] {O O' : Type} [DecidableEq O]
    [DecidableEq O'] {read : X → ι → σ} {f : X → O} {ε : ℝ} (g : O → O')
    (hne : (QueryCounts read f ε).Nonempty) :
    qQueryOn read (fun x => g (f x)) ε ≤ qQueryOn read f ε :=
  Nat.sInf_le (queryCounts_postcomp g read f ε (Nat.sInf_mem hne))

end QuantumQueryComplexity
