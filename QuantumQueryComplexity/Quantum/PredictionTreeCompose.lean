import QuantumQueryComplexity.PredictionTreeAdversary
import QuantumQueryComplexity.Quantum.UniformHasDual
import QuantumQueryComplexity.Quantum.ReadAll
import QuantumQueryComplexity.Quantum.Mixture
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Prediction trees over subroutine calls: quantum query bounds

The operational endpoints of prediction-tree composition, obtained from the
certificates of `Promise/PredictionTreeCompose.lean` and
`PredictionTreeAdversary.lean` by the cardinality-free extraction
`qQueryOn_third_le_of_hasDualOn_uniform`:

    Q_{1/3}(F) ≤ 8192 · (1 + 8·A·√(q·G))        (certificate form)
    Q_{1/3}(F) ≤ 8192 · (1 + 24·T·√(q·G))       (worst-case adversary form)

together with exact zero-query statements for the constant cases (`q = 0`,
`G = 0`, zero inner cost), realised by a genuine constant algorithm.

**Fixed seeds.**  A randomized procedure is handled by fixing all of its
random choices in one seed `ω`, proving the certificate bound above for the
deterministic tree `Tr ω` of every seed, and analysing the classical
success probability of the seeded output separately; no quantum error
reduction is introduced at recursive calls.  `qQueryOn_third_le_of_seeds`
packages this: seeds drawn from a fixed distribution independent of the
input, fixed-seed outputs correct with probability at least `9/10`, each
fixed-seed output evaluated with quantum error `1/16` within the uniform
certificate budget, and the mixture (`Quantum/Mixture.lean`) succeeds with
probability at least `(9/10)(15/16) > 2/3`.
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X] [DecidableEq X]
variable {P : Type} [Fintype P] [DecidableEq P]
variable {V : Type} [DecidableEq V]
variable {α : Type} [Fintype α] [DecidableEq α]
variable {O : Type} [DecidableEq O]

/-- A function constant on the promise costs no queries (any error `ε ≥ 0`),
without choosing a default value when the promise is nonempty. -/
theorem qQueryOn_eq_zero_of_forall_eq [Nonempty O] (read : X → ι → σ) {f : X → O}
    (hf : ∀ x y, f x = f y) {ε : ℝ} (hε : 0 ≤ ε) : qQueryOn read f ε = 0 := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact qQueryOn_const_eq_zero read (c := Classical.arbitrary O)
      (fun x => (hX.false x).elim) hε
  · exact qQueryOn_const_eq_zero read (c := f x₀) (fun x => hf x x₀) hε

namespace PredTree

/-- **Quantum query bound, certificate form**:
`Q_{1/3}(F) ≤ 8192·(1 + 8·A·√(q·G))`. -/
theorem qQueryOn_third_compose_le [Nonempty O] (Tr : PredTree P V α Unit O)
    (read : X → ι → σ) (g : P → X → V) {A : ℝ} (hA : 0 ≤ A)
    (hg : ∀ p, HasDualOn read (g p) A) {q G : ℕ}
    (hvis : ∀ x, Tr.visits () (fun p => g p x) ≤ q)
    (hunp : ∀ x, Tr.unpreds () (fun p => g p x) ≤ G) :
    (qQueryOn read (fun x => Tr.eval (fun p => g p x)) (1 / 3) : ℝ)
      ≤ 8192 * (1 + 8 * A * Real.sqrt ((q : ℝ) * (G : ℝ))) := by
  have h := qQueryOn_third_le_of_hasDualOn_uniform
    (hasDualOn_compose Tr read g hA hg hvis hunp) (by positivity)
  rwa [uniformExtractionConstant] at h

/-- **Quantum query bound, worst-case adversary form**:
`Q_{1/3}(F) ≤ 8192·(1 + 24·T·√(q·G))`. -/
theorem qQueryOn_third_compose_le_of_advPMOn [Nonempty O] (Tr : PredTree P V α Unit O)
    (read : X → ι → σ) (g : P → X → V) (hdet : ∀ p x y, read x = read y → g p x = g p y)
    {T : ℝ} (hT : 0 ≤ T) (hadv : ∀ p, advPMOn read (g p) ≤ T) {q G : ℕ}
    (hvis : ∀ x, Tr.visits () (fun p => g p x) ≤ q)
    (hunp : ∀ x, Tr.unpreds () (fun p => g p x) ≤ G) :
    (qQueryOn read (fun x => Tr.eval (fun p => g p x)) (1 / 3) : ℝ)
      ≤ 8192 * (1 + 24 * T * Real.sqrt ((q : ℝ) * (G : ℝ))) := by
  have h := qQueryOn_third_le_of_hasDualOn_uniform
    (hasDualOn_compose_of_advPMOn Tr read g hdet hT hadv hvis hunp) (by positivity)
  rwa [uniformExtractionConstant] at h

/-- The total-input form of the certificate bound. -/
theorem qQuery_third_compose_le [Nonempty O] (Tr : PredTree P V α Unit O)
    (g : P → (ι → σ) → V) {A : ℝ} (hA : 0 ≤ A) (hg : ∀ p, HasDual (g p) A) {q G : ℕ}
    (hvis : ∀ x : ι → σ, Tr.visits () (fun p => g p x) ≤ q)
    (hunp : ∀ x : ι → σ, Tr.unpreds () (fun p => g p x) ≤ G) :
    (qQuery (fun x => Tr.eval (fun p => g p x)) (1 / 3) : ℝ)
      ≤ 8192 * (1 + 8 * A * Real.sqrt ((q : ℝ) * (G : ℝ))) :=
  qQueryOn_third_compose_le Tr id g hA (fun p => (hg p).hasDualOn) hvis hunp

/-! ## Exact zero-query cases -/

/-- **No call**: zero queries, at every error `ε ≥ 0`. -/
theorem qQueryOn_compose_eq_zero_of_visits [Nonempty O] (Tr : PredTree P V α Unit O)
    (read : X → ι → σ) (g : P → X → V)
    (hvis : ∀ x, Tr.visits () (fun p => g p x) ≤ 0) {ε : ℝ} (hε : 0 ≤ ε) :
    qQueryOn read (fun x => Tr.eval (fun p => g p x)) ε = 0 :=
  qQueryOn_eq_zero_of_forall_eq read
    (fun x _ => eval_eq_of_visits_eq_zero Tr (fun _ => Nat.le_zero.mp (hvis x)) _) hε

/-- **No unpredicted answer**: zero queries, at every error `ε ≥ 0`. -/
theorem qQueryOn_compose_eq_zero_of_unpreds [Nonempty O] (Tr : PredTree P V α Unit O)
    (read : X → ι → σ) (g : P → X → V)
    (hunp : ∀ x, Tr.unpreds () (fun p => g p x) ≤ 0) {ε : ℝ} (hε : 0 ≤ ε) :
    qQueryOn read (fun x => Tr.eval (fun p => g p x)) ε = 0 :=
  qQueryOn_eq_zero_of_forall_eq read
    (fun x y => eval_eq_of_unpreds_eq_zero Tr
      (fun _ => Nat.le_zero.mp (hunp x)) (fun _ => Nat.le_zero.mp (hunp y))) hε

/-- **Zero inner cost**: zero queries, at every error `ε ≥ 0`. -/
theorem qQueryOn_compose_eq_zero_of_cost_zero [Nonempty O] (Tr : PredTree P V α Unit O)
    (read : X → ι → σ) (g : P → X → V) (hg : ∀ p, HasDualOn read (g p) 0) {ε : ℝ}
    (hε : 0 ≤ ε) : qQueryOn read (fun x => Tr.eval (fun p => g p x)) ε = 0 :=
  qQueryOn_eq_zero_of_forall_eq read (eval_eq_of_cost_zero Tr read g hg) hε

end PredTree

/-! ## Fixed seeds and the classical mixture -/

section Seeds

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- **The fixed-seed mixture wrapper.**  Seeds `ω : Ω` are drawn from a fixed
distribution `p` independent of the input; each fixed-seed output
`F ω : X → O` is read-determined and has quantum query complexity at most
`B` at error `1/16`; and for every promise input the seeded output is the
desired answer `f x` with probability at least `9/10`.  Then
`Q_{1/3}(f) ≤ B`: the mixture of the fixed-seed algorithms (padded to a
common query count) succeeds with probability at least
`(9/10)(15/16) = 27/32 > 2/3`. -/
theorem qQueryOn_third_le_of_seeds [Nonempty O] (read : X → ι → σ) (f : X → O)
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1) (F : Ω → X → O)
    (hdet : ∀ ω x y, read x = read y → F ω x = F ω y) {B : ℕ}
    (hB : ∀ ω, qQueryOn read (F ω) (1 / 16) ≤ B)
    (hgood : ∀ x, (9 / 10 : ℝ) ≤ ∑ ω, if F ω x = f x then p ω else 0) :
    qQueryOn read f (1 / 3) ≤ B := by
  classical
  -- a fixed-seed algorithm for every seed, at its own query count
  have hmem : ∀ ω, qQueryOn read (F ω) (1 / 16) ∈ QueryCounts read (F ω) (1 / 16) :=
    fun ω => Nat.sInf_mem (queryCounts_nonempty (hdet ω) (by norm_num))
  choose W hW hWd A hA using hmem
  let _ := hW
  let _ := hWd
  obtain ⟨W', hW', hW'd, Bmix, hBmix⟩ := exists_mixture p hp hsum
    (fun ω => qQueryOn read (F ω) (1 / 16)) B hB A
  let _ := hW'
  let _ := hW'd
  refine qQueryOn_le (A := Bmix) (q := B) fun x => ?_
  rw [hBmix]
  -- the good seeds contribute at least `15/16 · p ω` each
  have hterm : ∀ ω, (if F ω x = f x then p ω else 0) * (15 / 16)
      ≤ p ω * (A ω).prob (read x) (qQueryOn read (F ω) (1 / 16)) (f x) := by
    intro ω
    by_cases h : F ω x = f x
    · rw [if_pos h]
      have := hA ω x
      rw [h] at this
      have hpn := hp ω
      nlinarith
    · rw [if_neg h, zero_mul]
      exact mul_nonneg (hp ω) (QAlg.prob_nonneg _ _ _ _)
  have hsumle := Finset.sum_le_sum fun ω (_ : ω ∈ Finset.univ) => hterm ω
  rw [← Finset.sum_mul] at hsumle
  have hg := hgood x
  nlinarith

end Seeds

end QuantumQueryComplexity
