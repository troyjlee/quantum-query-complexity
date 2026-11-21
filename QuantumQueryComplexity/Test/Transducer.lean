import QuantumQueryComplexity.Quantum.Transducer
import QuantumQueryComplexity.Quantum.KronLift

set_option linter.style.header false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Acceptance: transducers

Checks of `Quantum/Transducer.lean` ([BJY23, Theorem 5.5]) on small explicit instances.

1. **[BJY23, Example 5.3].** On `Fin 3`, `|0⟩` is public and `|1⟩`, `|2⟩` are private; `S` is
   the reflection of `|0⟩ − |1⟩ − |2⟩` (it negates that vector and fixes its orthogonal
   complement). `S` transduces `|0⟩` into itself with the catalyst `(|1⟩ + |2⟩)/2` of squared
   norm `1/2`, and also with the catalysts `|1⟩` and `|2⟩`. The algorithm `Transducer.circuit`
   then returns `|0⟩ ⊗ |0⟩` within `√2/√K`. For `K = 1` and `K = 2` the output is computed
   exactly: errors `2/√3` and `2/3`, below the bounds `√2` and `1`. These two sizes cannot see
   the direction of the clock advance (`finRotate` is its own inverse on `Fin 1` and `Fin 2`).
2. **The direction of the advance and the order of the operations**, at `K = 3`: `tick` moves a
   private basis state from clock `0` to `1` and from `2` to `0`, and one round with the swap of
   `|0⟩` and `|1⟩` sends `(clock 0, |0⟩)` to `(clock 1, |1⟩)`. A reversed advance would give
   clock `2`; advancing before applying `S` would give clock `0`.
3. **A transducer with a query.** One swap query on `QBasis Unit Bool Unit` exchanges the blank
   answer `|(), ⊥⟩` with `|(), a ()⟩`. With the non-blank answers private, it transduces
   `|(), ⊥⟩` into itself with the input-dependent catalyst `|(), a ()⟩`, so the routine form
   gives a fixed `K`-query routine that returns the clocked `|(), ⊥⟩` within `2/√K` on every
   input. (An idle routine also meets this conclusion; item 5 is the positive control.)
4. **A realized transducer.** The matrix of Example 5.3 acting on the workspace `Fin 3` of
   `QBasis Unit Bool (Fin 3)`, as a zero-query routine, realizes `S` along the embedding
   `x ↦ (none, none, x)`, and `exists_transducerRoutine_of_realizes` applies. (Here too the
   identity routine meets the conclusion.)
5. **The routine must read the oracle.** On the answer register of a live query, embedded by
   `z ↦ (some (), z, ())`, one query realizes the swap of `⊥` and `a ()`. With every basis state
   public and the catalyst `0` it transduces `|⊥⟩` into `|a ()⟩` exactly, so the realized form
   gives one fixed `K`-query routine that maps the clocked `|(), ⊥⟩` to the clocked
   `|(), a ()⟩` exactly: its output differs between the two oracle tables.
-/

namespace QuantumQueryComplexity
namespace TransducerAcceptance

open scoped Matrix
open Matrix

/-! ## 1. [BJY23, Example 5.3] -/

/-- The privacy predicate of [BJY23, Example 5.3] on `Fin 3`: `|0⟩` is public, `|1⟩` and `|2⟩`
are private. -/
def priv53 : Fin 3 → Prop := fun i => i ≠ 0

instance : DecidablePred priv53 := fun i => inferInstanceAs (Decidable (i ≠ 0))

/-- The vector `|0⟩ − |1⟩ − |2⟩` of [BJY23, Example 5.3]. -/
def u53 : Fin 3 → ℂ := ![1, -1, -1]

/-- The transducer of [BJY23, Example 5.3], written out: the reflection
`1 − (2/3) u uᵀ` of `u = |0⟩ − |1⟩ − |2⟩` (`S53_eq`). -/
noncomputable def S53 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1 / 3, 2 / 3, 2 / 3; 2 / 3, 1 / 3, -2 / 3; 2 / 3, -2 / 3, 1 / 3]

/-- `S53` is the reflection of `u53`: `1 − (2/3) u uᵀ`, where `‖u‖² = 3`. -/
theorem S53_eq : S53 = 1 - (2 / 3 : ℂ) • Matrix.vecMulVec u53 u53 := by
  sorry

/-- `S53` negates `u53` ... -/
theorem S53_mulVec_u53 : S53 *ᵥ u53 = -u53 := by
  sorry

/-- ... and fixes every vector orthogonal to it. -/
theorem S53_mulVec_of_orth (w : Fin 3 → ℂ) (hw : u53 ⬝ᵥ w = 0) : S53 *ᵥ w = w := by
  sorry

/-- `S53` is unitary. -/
theorem S53_mem_unitaryGroup : S53 ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  sorry

/-- The catalyst `(|1⟩ + |2⟩)/2` of [BJY23, Example 5.3]. -/
noncomputable def v53 : Fin 3 → ℂ := ![0, 1 / 2, 1 / 2]

/-- **[BJY23, Example 5.3]**: `S (|0⟩ + (|1⟩ + |2⟩)/2) = |0⟩ + (|1⟩ + |2⟩)/2`, so `S53`
transduces `|0⟩` into itself with the catalyst `v53`. -/
theorem transduces53 : Transduces priv53 S53 (qBasis 0) (qBasis 0) v53 := by
  sorry

/-- The other catalysts named in [BJY23, Example 5.3]: `|1⟩` and `|2⟩`. -/
theorem transduces53_basis :
    Transduces priv53 S53 (qBasis 0) (qBasis 0) (qBasis 1) ∧
      Transduces priv53 S53 (qBasis 0) (qBasis 0) (qBasis 2) := by
  sorry

/-- `‖v53‖² = 1/2`, the value used in `circuit53_close`. (That `v53` is the minimal catalyst,
so that `W(S, |0⟩) = 1/2`, is shown in [BJY23, Example 5.3] and not formalized here; the
catalysts `|1⟩` and `|2⟩` have squared norm `1`.) -/
theorem qNormSq_v53 : qNormSq v53 = 1 / 2 := by
  sorry

/-- **The theorem on the example**: for every `K ≥ 1` the algorithm returns `|0⟩ ⊗ |0⟩` within
`2‖v53‖/√K = √2/√K`. -/
theorem circuit53_close {K : ℕ} (hK : 0 < K) :
    qNorm (Transducer.circuit K S53 priv53 *ᵥ Transducer.clockVec ⟨0, hK⟩ (qBasis 0)
      - Transducer.clockVec ⟨0, hK⟩ (qBasis 0)) ≤ Real.sqrt 2 / Real.sqrt K := by
  sorry

/-- `K = 1`: the algorithm is one application of `S53`, which maps `|0⟩` to
`(1/3, 2/3, 2/3)`; the error is `2/√3 ≤ √2`. -/
theorem circuit53_one :
    Transducer.circuit 1 S53 priv53 *ᵥ Transducer.clockVec 0 (qBasis 0)
      = Transducer.clockVec 0 ![1 / 3, 2 / 3, 2 / 3] := by
  sorry

/-- `K = 2`, computed by hand. After the clock preparation the state is
`(|0⟩ + |1⟩)|0⟩/√2`; the branch vectors below omit this common factor `1/√2` during the rounds.
Round `0` applies `S53` on branch `0` and moves its private part to branch `1`; round `1`
applies `S53` to `(1, 2/3, 2/3)` on branch `1`, giving `(11/9, 4/9, 4/9)`, and moves its private
part back to branch `0`. Undoing the preparation (which supplies a second factor `1/√2`) gives
`(7/9, 2/9, 2/9)` on branch `0` and `(−4/9, 2/9, 2/9)` on branch `1`: the error is
`2/3 ≤ 1`. -/
theorem circuit53_two :
    Transducer.circuit 2 S53 priv53 *ᵥ Transducer.clockVec 0 (qBasis 0)
      = Transducer.clockVec 0 ![7 / 9, 2 / 9, 2 / 9]
        + Transducer.clockVec 1 ![-4 / 9, 2 / 9, 2 / 9] := by
  sorry

/-! ## 2. The direction of the advance and the order of the operations -/

/-- At `K = 3`, `tick` advances a private basis state from clock `0` to `1` and from clock `2`
to `0`, and leaves a public basis state alone. -/
theorem tick_three :
    Transducer.tick 3 priv53 (0, 1) = (1, 1) ∧ Transducer.tick 3 priv53 (2, 1) = (0, 1) ∧
      Transducer.tick 3 priv53 (0, 0) = (0, 0) := by
  sorry

/-- **One round at `K = 3`**, with `S` the swap of `|0⟩` (public) and `|1⟩` (private): `S`
moves `(clock 0, |0⟩)` to `(clock 0, |1⟩)`, and the advance then moves it to `(clock 1, |1⟩)`.
A reversed advance would give clock `2`; advancing before applying `S` would give clock `0`. -/
theorem first_round_three :
    Transducer.loop 3 (qPerm (Equiv.swap (0 : Fin 3) 1)) priv53 1 *ᵥ qBasis (0, 0)
      = qBasis (1, 1) := by
  sorry

/-! ## 3. A transducer with a query -/

/-- The privacy predicate on `QBasis Unit Bool Unit`: a basis state is private exactly when its
answer register is not blank. -/
def privAnswer : QBasis Unit Bool Unit → Prop := fun p => p.2.1 ≠ none

instance : DecidablePred privAnswer := fun p => inferInstanceAs (Decidable (p.2.1 ≠ none))

/-- The basis state that queries `()` with a blank answer. -/
def blank1 : QBasis Unit Bool Unit := (some (), none, ())

/-- **One query is a transducer.** The swap oracle exchanges `|(), ⊥⟩` and `|(), a ()⟩`, so it
transduces `|(), ⊥⟩` into itself with the catalyst `|(), a ()⟩`, which depends on the input. -/
theorem transduces_query (a : Unit → Bool) :
    Transduces privAnswer ((QRoutine.query : QRoutine Unit Bool Unit).run a)
      (qBasis blank1) (qBasis blank1) (qBasis (some (), some (a ()), ())) := by
  sorry

/-- **The routine form on the one-query transducer**: one fixed routine with `K` queries returns
the clocked `|(), ⊥⟩` within `2/√K` on every input. (A routine that parks every query also
meets this conclusion; `query_reads_answer` is the positive control.) -/
theorem query_transducer {K : ℕ} (hK : 0 < K) :
    ∃ T : QRoutine Unit Bool (ClockWork Unit K Unit), T.len = K ∧
      ∀ a : Unit → Bool,
        qNorm (T.run a *ᵥ embedClock ⟨0, hK⟩ false (qBasis blank1)
          - embedClock ⟨0, hK⟩ false (qBasis blank1)) ≤ 2 / Real.sqrt K := by
  sorry

/-! ## 4. A realized transducer -/

/-- The basis of `QBasis Unit Bool (Fin 3)` split as (workspace, query registers). -/
def split3 : QBasis Unit Bool (Fin 3) ≃ Fin 3 × (Option Unit × Option Bool) where
  toFun p := (p.2.2, (p.1, p.2.1))
  invFun x := (x.2.1, x.2.2, x.1)
  left_inv := by rintro ⟨k, t, w⟩; rfl
  right_inv := by rintro ⟨w, k, t⟩; rfl

/-- `S53` acting on the workspace `Fin 3`, as a zero-query routine. -/
noncomputable def R53 : QRoutine Unit Bool (Fin 3) :=
  QRoutine.ofUnitary (kronLift split3 S53) (kronLift_mem_unitaryGroup split3 S53_mem_unitaryGroup)

/-- The embedding of `Fin 3` as the workspace, with idle query index and blank answer. -/
def emb3 : Fin 3 → QBasis Unit Bool (Fin 3) := fun x => (none, none, x)

/-- `R53` realizes `S53` along `emb3`, on every input. -/
theorem realizes53 (a : Unit → Bool) (ψ : Fin 3 → ℂ) :
    R53.run a *ᵥ Transducer.embedVia emb3 ψ = Transducer.embedVia emb3 (S53 *ᵥ ψ) := by
  sorry

/-- **The realized form on Example 5.3**: one fixed zero-query routine returns the clocked
embedding of `|0⟩` within `√2/√K`. (The identity routine also meets this conclusion.) -/
theorem realized53_transducer {K : ℕ} (hK : 0 < K) :
    ∃ T : QRoutine Unit Bool (ClockWork Unit K (Fin 3)), T.len = 0 ∧
      ∀ a : Unit → Bool,
        qNorm (T.run a *ᵥ embedClock ⟨0, hK⟩ false (Transducer.embedVia emb3 (qBasis 0))
          - embedClock ⟨0, hK⟩ false (Transducer.embedVia emb3 (qBasis 0)))
          ≤ Real.sqrt 2 / Real.sqrt K := by
  sorry

/-! ## 5. The routine must read the oracle -/

/-- The answer register of a live query to `()`, as a register of `QBasis Unit Bool Unit`. -/
def liveAnswer (z : Option Bool) : QBasis Unit Bool Unit := (some (), z, ())

/-- On the answer register of a live query, one query realizes the swap of `⊥` and `a ()`. -/
theorem realizes_answer (a : Unit → Bool) (ψ : Option Bool → ℂ) :
    (QRoutine.query : QRoutine Unit Bool Unit).run a *ᵥ Transducer.embedVia liveAnswer ψ
      = Transducer.embedVia liveAnswer (qPerm (Equiv.swap none (some (a ()))) *ᵥ ψ) := by
  sorry

/-- **The positive control**: one fixed routine with `K` queries maps the clocked `|(), ⊥⟩` to
the clocked `|(), a ()⟩` exactly, on every input `a`. It follows from
`exists_transducerRoutine_of_realizes` with every basis state public and the catalyst `0`
(error `0`). The two oracle tables give different outputs, so no idle routine satisfies it. -/
theorem query_reads_answer {K : ℕ} (hK : 0 < K) :
    ∃ T : QRoutine Unit Bool (ClockWork Unit K Unit), T.len = K ∧
      ∀ a : Unit → Bool,
        T.run a *ᵥ embedClock ⟨0, hK⟩ false (qBasis blank1)
          = embedClock ⟨0, hK⟩ false (qBasis (some (), some (a ()), ())) := by
  sorry

end TransducerAcceptance
end QuantumQueryComplexity
