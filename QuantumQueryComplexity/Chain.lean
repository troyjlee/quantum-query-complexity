import QuantumQueryComplexity.Adaptive

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Chains of adaptive steps

A *chain* runs `ρ` steps, each a function of the input that may depend on the transcript
of the previous steps; the transcript of all steps is the output.  If every step has a
dual of cost `c i` uniformly in the transcript it sees, the chain has a dual of cost
`∑ c i` (`hasDual_chain`), by `HasDual.adaptiveCall` at every step.  Keeping the whole
transcript as the output is what makes the adaptive composition clean: a projection to a
final answer is taken once, at the very end, by `HasDual.postcomp_of_determined` or
`HasDual.ofKer`.
-/

namespace QuantumQueryComplexity

/-- Transcripts of `ρ` steps with values in `S`. -/
def Trans (S : Type) : ℕ → Type
  | 0 => Unit
  | ρ + 1 => Trans S ρ × S

def decEqTrans (S : Type) [DecidableEq S] : ∀ ρ, DecidableEq (Trans S ρ)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | ρ + 1 => letI := decEqTrans S ρ; inferInstanceAs (DecidableEq (Trans S ρ × S))

@[instance_reducible] def fintypeTrans (S : Type) [Fintype S] : ∀ ρ, Fintype (Trans S ρ)
  | 0 => inferInstanceAs (Fintype Unit)
  | ρ + 1 => letI := fintypeTrans S ρ; inferInstanceAs (Fintype (Trans S ρ × S))

instance instDecidableEqTrans {S : Type} [DecidableEq S] {ρ : ℕ} : DecidableEq (Trans S ρ) :=
  decEqTrans S ρ

instance instFintypeTrans {S : Type} [Fintype S] {ρ : ℕ} : Fintype (Trans S ρ) :=
  fintypeTrans S ρ

/-- The last value of a nonempty transcript. -/
def Trans.last {S : Type} : ∀ {ρ : ℕ}, Trans S (ρ + 1) → S
  | _, t => t.2

/-- The value at step `i` of a transcript. -/
def Trans.get {S : Type} : ∀ {ρ : ℕ}, Trans S ρ → ∀ i, i < ρ → S
  | ρ + 1, t, i, _ => if h : i < ρ then Trans.get t.1 i h else t.2

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- **The chain**: step `ρ` sees the transcript of the previous steps. -/
def chain (step : ∀ ρ, Trans S ρ → (ι → σ) → S) : ∀ ρ, (ι → σ) → Trans S ρ
  | 0 => fun _ => ()
  | ρ + 1 => fun x => (chain step ρ x, step ρ (chain step ρ x) x)

lemma chain_succ (step : ∀ ρ, Trans S ρ → (ι → σ) → S) (ρ : ℕ) (x : ι → σ) :
    chain step (ρ + 1) x = (chain step ρ x, step ρ (chain step ρ x) x) := rfl

/-- **A chain of adaptive steps has a dual of the summed cost.** -/
theorem hasDual_chain (step : ∀ ρ, Trans S ρ → (ι → σ) → S) (c : ℕ → ℝ)
    (hstep : ∀ ρ (prev : Trans S ρ), HasDual (step ρ prev) (c ρ)) :
    ∀ ρ, HasDual (chain step ρ) (∑ i ∈ Finset.range ρ, c i)
  | 0 => by
    rw [Finset.range_zero, Finset.sum_empty]
    exact hasDual_const fun _ _ => rfl
  | ρ + 1 => by
    rw [Finset.sum_range_succ]
    exact HasDual.adaptiveCall (hasDual_chain step c hstep ρ) (fun d => hstep ρ d)

/-- The uniform-cost form. -/
theorem hasDual_chain_const (step : ∀ ρ, Trans S ρ → (ι → σ) → S) {c : ℝ}
    (hstep : ∀ ρ (prev : Trans S ρ), HasDual (step ρ prev) c) (ρ : ℕ) :
    HasDual (chain step ρ) (ρ * c) := by
  have h := hasDual_chain step (fun _ => c) hstep ρ
  rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h

end QuantumQueryComplexity
