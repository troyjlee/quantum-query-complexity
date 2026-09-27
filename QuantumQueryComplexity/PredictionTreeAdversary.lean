import QuantumQueryComplexity.Promise.PredictionTreeCompose
import QuantumQueryComplexity.Duality.FiniteOutputOn
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Prediction trees over subroutine calls: the worst-case adversary form

If every subroutine `g p` is read-determined with
`advPMOn read (g p) ≤ T`, then the composite procedure has an all-pairs
certificate of cost

    24 · T · √(q·G)

and hence `advPMOn read F ≤ 24·T·√(q·G)`.  The constant `24 = 8 · 3` is the
prediction-tree constant `8` times the inner certificate cost `3T` supplied
by the finite-output bridge (`hasDualOn_three_mul_advPMOn`: every
read-determined finite-output promise problem has a certificate of cost
`3·advPMOn`, the bridge's factor two plus room to avoid assuming the infimum
is attained).  `T = 0` needs no separate treatment: the bridge already covers
constant subroutines with the zero certificate.

For a nonempty family the budget may be taken to be the maximum of the
subroutines' adversary bounds (`hasDualOn_compose_of_advPMOn_sup`).
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X] [DecidableEq X]
variable {P : Type} [Fintype P] [DecidableEq P]
variable {V : Type} [DecidableEq V]
variable {α : Type} [Fintype α] [DecidableEq α]
variable {O : Type} [DecidableEq O]

namespace PredTree

/-- **Compositional Beigi–Taghavi, worst-case adversary form.**  Read-determined
subroutines with `advPMOn read (g p) ≤ T` (`T ≥ 0`), at most `q` calls and `G`
unpredicted answers on every realizable table: the composite has an all-pairs
certificate of cost `24·T·√(q·G)` on the promise. -/
theorem hasDualOn_compose_of_advPMOn (Tr : PredTree P V α Unit O) (read : X → ι → σ)
    (g : P → X → V) (hdet : ∀ p x y, read x = read y → g p x = g p y)
    {T : ℝ} (hT : 0 ≤ T) (hadv : ∀ p, advPMOn read (g p) ≤ T) {q G : ℕ}
    (hvis : ∀ x, Tr.visits () (fun p => g p x) ≤ q)
    (hunp : ∀ x, Tr.unpreds () (fun p => g p x) ≤ G) :
    HasDualOn read (fun x => Tr.eval (fun p => g p x))
      (24 * T * Real.sqrt ((q : ℝ) * (G : ℝ))) := by
  have hg : ∀ p, HasDualOn read (g p) (3 * T) := fun p =>
    hasDualOn_of_advPMOn_le (hdet p) (hadv p)
  exact (hasDualOn_compose Tr read g (by positivity) hg hvis hunp).mono (le_of_eq (by ring))

/-- **Weak duality**: the composite's adversary bound is at most
`24·T·√(q·G)`. -/
theorem advPMOn_compose_le (Tr : PredTree P V α Unit O) (read : X → ι → σ)
    (g : P → X → V) (hdet : ∀ p x y, read x = read y → g p x = g p y)
    {T : ℝ} (hT : 0 ≤ T) (hadv : ∀ p, advPMOn read (g p) ≤ T) {q G : ℕ}
    (hvis : ∀ x, Tr.visits () (fun p => g p x) ≤ q)
    (hunp : ∀ x, Tr.unpreds () (fun p => g p x) ≤ G) :
    advPMOn read (fun x => Tr.eval (fun p => g p x))
      ≤ 24 * T * Real.sqrt ((q : ℝ) * (G : ℝ)) :=
  advPMOn_le_of_hasDualOn (by positivity)
    (hasDualOn_compose_of_advPMOn Tr read g hdet hT hadv hvis hunp)

/-- The budget may be the maximum of the subroutines' adversary bounds
(nonempty family). -/
theorem hasDualOn_compose_of_advPMOn_sup [Nonempty P] (Tr : PredTree P V α Unit O)
    (read : X → ι → σ) (g : P → X → V) (hdet : ∀ p x y, read x = read y → g p x = g p y)
    {q G : ℕ} (hvis : ∀ x, Tr.visits () (fun p => g p x) ≤ q)
    (hunp : ∀ x, Tr.unpreds () (fun p => g p x) ≤ G) :
    HasDualOn read (fun x => Tr.eval (fun p => g p x))
      (24 * (Finset.univ.sup' Finset.univ_nonempty fun p => advPMOn read (g p))
        * Real.sqrt ((q : ℝ) * (G : ℝ))) := by
  have hT : 0 ≤ Finset.univ.sup' Finset.univ_nonempty fun p => advPMOn read (g p) :=
    (advPMOn_nonneg (hdet (Classical.arbitrary P))).trans
      (Finset.le_sup' (fun p => advPMOn read (g p)) (Finset.mem_univ _))
  exact hasDualOn_compose_of_advPMOn Tr read g hdet hT
    (fun p => Finset.le_sup' (fun p => advPMOn read (g p)) (Finset.mem_univ p)) hvis hunp

/-- **The total-input form**: subroutines on the full cube with
`advPM (g p) ≤ T`. -/
theorem hasDual_compose_of_advPM (Tr : PredTree P V α Unit O) (g : P → (ι → σ) → V)
    {T : ℝ} (hT : 0 ≤ T) (hadv : ∀ p, advPM (g p) ≤ T) {q G : ℕ}
    (hvis : ∀ x : ι → σ, Tr.visits () (fun p => g p x) ≤ q)
    (hunp : ∀ x : ι → σ, Tr.unpreds () (fun p => g p x) ≤ G) :
    HasDual (fun x => Tr.eval (fun p => g p x)) (24 * T * Real.sqrt ((q : ℝ) * (G : ℝ))) :=
  HasDual.of_hasDualOn_id (hasDualOn_compose_of_advPMOn Tr id g
    (fun p x y h => by simpa using congrArg (g p) h) hT hadv hvis hunp)

/-- Weak duality, total form. -/
theorem advPM_compose_le (Tr : PredTree P V α Unit O) (g : P → (ι → σ) → V)
    {T : ℝ} (hT : 0 ≤ T) (hadv : ∀ p, advPM (g p) ≤ T) {q G : ℕ}
    (hvis : ∀ x : ι → σ, Tr.visits () (fun p => g p x) ≤ q)
    (hunp : ∀ x : ι → σ, Tr.unpreds () (fun p => g p x) ≤ G) :
    advPM (fun x => Tr.eval (fun p => g p x)) ≤ 24 * T * Real.sqrt ((q : ℝ) * (G : ℝ)) :=
  advPM_le_of_hasDual (by positivity) (hasDual_compose_of_advPM Tr g hT hadv hvis hunp)

end PredTree

end QuantumQueryComplexity
