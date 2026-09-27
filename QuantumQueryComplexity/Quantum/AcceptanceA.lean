import QuantumQueryComplexity.Quantum.LowerBound.Main
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Adversary lower bound: statement tests

This file restates the lower-bound results in full, so a refactor that weakens
a statement fails the build. The `QuantumQueryComplexity.Quantum` aggregate
imports it, and the default library build checks it.

A statement alone is not enough: a lower bound on `qQueryOn` stays *true* if
`ComputesWithErrorOn` is accidentally made vacuous, or if the oracle stops being
a query.  So the pins come in three groups:

1. **The theorem** — `acceptance`, the headline bound, written out with no
   abbreviations, and `acceptance_concrete`, the `7/32` instance at `ε = 1/16`.
2. **The model is a query model** — the oracle is unitary and self-inverse, it
   is the identity on the idle sector, and on an active index it depends on the
   input only through the letter at that index.  These are what make the bound
   about *queries*.
3. **The model is not degenerate** — measurement probabilities sum to one, one
   query really does read one coordinate exactly, and `qQueryOn` is a genuine
   minimum (bounded by `|ι|`, so the achievable set is nonempty and
   `sInf ∅ = 0` is not what the theorem is about).

Group 3 is the one that would catch a vacuous refactor: if `ComputesWithErrorOn`
were weakened, `computesWithErrorOn_proj_pinned` would still hold, but if it were
*strengthened* past the point of achievability `qQueryOn_le_card_pinned` would
fail; if the measurement rule broke, `sum_qProb_pinned` would fail.

To inspect the headline theorem's axioms interactively:

    #print axioms QuantumQueryComplexity.mul_advPMOn_le_qQueryOn
      → [propext, Classical.choice, Quot.sound]
-/

namespace QuantumQueryComplexity
namespace MilestoneA

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-! ## 1. The theorem -/

/-- **The Milestone A statement, pinned.**  Every quantum algorithm computing an
observationally determined `f` on the promise `read` with error `ε` makes at
least `(1 - (2√ε + ε))/2 · advPMOn read f` queries. -/
theorem acceptance
    {ι σ O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    [Fintype O] [DecidableEq O] [Nonempty O]
    {X : Type} [Fintype X] [DecidableEq X]
    {read : X → ι → σ} {f : X → O} {ε : ℝ}
    (hdet : ∀ x y, read x = read y → f x = f y)
    (hε0 : 0 ≤ ε) (hlt : 2 * Real.sqrt ε + ε < 1) :
    (1 - (2 * Real.sqrt ε + ε)) / 2 * advPMOn read f ≤ (qQueryOn read f ε : ℝ) :=
  mul_advPMOn_le_qQueryOn hdet hε0 hlt

/-- The concrete instance, so the threshold is on the record as satisfiable. -/
theorem acceptance_concrete
    {ι σ O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    [Fintype O] [DecidableEq O] [Nonempty O]
    {X : Type} [Fintype X] [DecidableEq X]
    {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (7 / 32 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 16) : ℝ) :=
  mul_advPMOn_le_qQueryOn_of_error_sixteenth hdet

/-- The per-algorithm form, which is what a `Milestone B` refactor is most
likely to touch. -/
theorem acceptance_alg
    {ι σ O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    [Fintype O] [DecidableEq O]
    {X : Type} [Fintype X] [DecidableEq X] {W : Type} [Fintype W] [DecidableEq W]
    {A : QAlg ι σ O W} {q : ℕ} {read : X → ι → σ} {f : X → O} {ε : ℝ}
    (hε0 : 0 ≤ ε) (hlt : 2 * Real.sqrt ε + ε < 1)
    (hcomp : ComputesWithErrorOn A q read f ε) :
    (1 - (2 * Real.sqrt ε + ε)) * advPMOn read f ≤ 2 * q :=
  advPMOn_le_of_computes hε0 hlt hcomp

/-! ## 2. The model is a query model -/

section Model

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-- The oracle is unitary. -/
theorem oracle_unitary_pinned (a : ι → σ) :
    oracleMat (W := W) a ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ :=
  oracleMat_mem_unitaryGroup a

/-- Query = unquery. -/
theorem oracle_involutive_pinned (a : ι → σ) :
    oracleMat (W := W) a * oracleMat a = 1 :=
  oracleMat_mul_self a

/-- The oracle does nothing on the idle sector: queries are controlled. -/
theorem oracle_idle_pinned (a : ι → σ) (ψ : QBasis ι σ W → ℂ) (t : Option σ)
    (w : W) : (oracleMat a *ᵥ ψ) ((none, t, w) : QBasis ι σ W) = ψ (none, t, w) :=
  oracleMat_mulVec_apply_none a ψ t w

/-- **The query decomposition**: at an active index the oracle depends on the
input only through the letter at that index.  This is the fact the whole lower
bound rests on. -/
theorem oracle_local_pinned {a b : ι → σ} (ψ : QBasis ι σ W → ℂ)
    {p : QBasis ι σ W} (hp : ∀ i, p.1 = some i → a i = b i) :
    (oracleMat a *ᵥ ψ) p = (oracleMat b *ᵥ ψ) p :=
  oracleMat_mulVec_congr ψ hp

end Model

/-! ## 3. The model is not degenerate -/

section NonDegenerate

variable {ι σ O W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype O] [DecidableEq O] [Fintype W] [DecidableEq W]
variable {X : Type} [Fintype X]

/-- Measurement is a probability distribution on a state. -/
theorem sum_qProb_pinned {H : Type} [Fintype H] [DecidableEq H] {ψ : H → ℂ}
    (hψ : IsQState ψ) (p : H → O) : ∑ o, qProb p ψ o = 1 :=
  sum_qProb_eq_one hψ p

/-- An algorithm's state is a unit vector at every time. -/
theorem state_isQState_pinned (A : QAlg ι σ O W) (a : ι → σ) (t : ℕ) :
    IsQState (A.state a t) :=
  A.state_isQState a t

/-- **One query reads one coordinate, exactly** — the model can actually query. -/
theorem computesWithErrorOn_proj_pinned (read : X → ι → σ) (i : ι) {ε : ℝ}
    (hε : 0 ≤ ε) :
    ComputesWithErrorOn (projAlg σ i) 1 read (fun x => some (read x i)) ε :=
  computesWithErrorOn_proj read i hε

/-- **`qQueryOn` is a genuine minimum**, not `sInf ∅ = 0`: reading every
coordinate solves any observationally determined problem. -/
theorem qQueryOn_le_card_pinned [Nonempty O] {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y) {ε : ℝ} (hε : 0 ≤ ε) :
    qQueryOn read f ε ≤ Fintype.card ι :=
  qQueryOn_le_card hdet hε

end NonDegenerate

end MilestoneA
end QuantumQueryComplexity
