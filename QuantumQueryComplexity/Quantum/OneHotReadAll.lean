import QuantumQueryComplexity.Quantum.OneHot
import QuantumQueryComplexity.Quantum.OneHotSimulation
import QuantumQueryComplexity.Quantum.ReadAll
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Reading the whole input exactly, in the one-hot model

The direct one-hot analogue of `ReadAll.lean`: every observationally
determined problem has an **exact** `|ι|`-query algorithm in the canonical
one-hot XOR oracle model, so `oneHotQQueryOn ≤ |ι|` with the exact cap —
transporting the native read-all through the factor-two simulation would
only give `2|ι|`.

The construction reuses the native algorithm's *steps* verbatim, over the
record type `QRec ι (Hot σ)`: the index-register transpositions and the
answer–slot swaps of `ReadAll.lean` are alphabet-generic.  Only the initial
state and the invariant change.  Under one-hot semantics a query on a blank
register does nothing, so the register must be **clean** (`some hotZero`)
rather than blank before each query; the slot it is swapped with must
therefore hold `some hotZero` too, so that the swap returns a clean register
for the next query.  Hence every slot starts at `some hotZero`, and the
invariant is

  `oneHotState a t = |idxAt t⟩ |some 0⟩ |hotRecAt a t⟩`,

with `hotRecAt a t` holding `some (hotCode (a i))` at the first `t` indices
and `some hotZero` elsewhere.  The readout decodes the one-hot record
slot-wise with `decodeHot`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X]

/-! ## The one-hot record -/

/-- The workspace after `t` one-hot queries: the codes of the first `t`
answers, and the clean answer elsewhere. -/
noncomputable def hotRecAt (a : ι → σ) (t : ℕ) : QRec ι (Hot σ) :=
  fun i => some ((recAt a t i).elim hotZero hotCode)

lemma hotRecAt_apply (a : ι → σ) (t : ℕ) (i : ι) :
    hotRecAt a t i = some ((recAt a t i).elim hotZero hotCode) := rfl

lemma hotRecAt_zero (a : ι → σ) : hotRecAt a 0 = fun _ => some hotZero := by
  funext i
  rw [hotRecAt_apply, recAt_zero]
  rfl

/-- Once every index has been read the record holds every code. -/
lemma hotRecAt_of_card_le (a : ι → σ) {t : ℕ} (h : Fintype.card ι ≤ t) :
    hotRecAt a t = fun i => some (hotCode (a i)) := by
  funext i
  rw [hotRecAt_apply, recAt_of_card_le a h]
  rfl

/-- Storing the code at the index read at time `t` advances the record. -/
lemma update_hotRecAt (a : ι → σ) {t : ℕ} {j : ι}
    (hj : (Fintype.equivFin ι j : ℕ) = t) :
    Function.update (hotRecAt a t) j (some (hotCode (a j))) = hotRecAt a (t + 1) := by
  funext i
  by_cases hij : i = j
  · subst hij
    rw [Function.update_self, hotRecAt_apply, ← update_recAt a hj, Function.update_self]
    rfl
  · rw [Function.update_of_ne hij, hotRecAt_apply, hotRecAt_apply, ← update_recAt a hj,
      Function.update_of_ne hij]

/-- The slot the algorithm is about to write to is clean. -/
lemma hotRecAt_self (a : ι → σ) {t : ℕ} {j : ι}
    (hj : (Fintype.equivFin ι j : ℕ) = t) : hotRecAt a t j = some hotZero := by
  rw [hotRecAt_apply, recAt_self_eq_none a hj]
  rfl

/-! ## The algorithm -/

/-- **The one-hot algorithm that reads every coordinate**: the native
read-all steps over one-hot records, started with every register clean. -/
noncomputable def oneHotReadAllAlg (dec : QRec ι (Hot σ) → O) :
    QAlg ι (Hot σ) O (QRec ι (Hot σ)) :=
  { readAllAlg dec with
    init := qBasis (none, some hotZero, fun _ => some hotZero)
    init_isQState := isQState_qBasis _ }

@[simp] lemma oneHotReadAllAlg_readout (dec : QRec ι (Hot σ) → O)
    (p : QBasis ι (Hot σ) (QRec ι (Hot σ))) :
    (oneHotReadAllAlg dec).readout p = dec p.2.2 := rfl

lemma oneHotReadAllAlg_step_qBasis (dec : QRec ι (Hot σ) → O) (t : ℕ)
    (p : QBasis ι (Hot σ) (QRec ι (Hot σ))) :
    (oneHotReadAllAlg dec).step t *ᵥ qBasis p
      = qBasis (idxSwapPerm (prevIdx ι t) (idxAt ι t)
          (slotSwapPerm (prevIdx ι t) p)) :=
  readAllAlg_step_qBasis dec t p

/-- **The invariant.**  After `t` one-hot queries the algorithm holds the
codes of the first `t` answers, with the index register pointing at the next
index and the answer register clean. -/
theorem oneHotReadAllAlg_state (dec : QRec ι (Hot σ) → O) (a : ι → σ) (t : ℕ) :
    oneHotState (oneHotReadAllAlg dec) a t
      = qBasis (idxAt ι t, some hotZero, hotRecAt a t) := by
  induction t with
  | zero =>
      change (oneHotReadAllAlg dec).step 0
          *ᵥ qBasis ((none, some hotZero, fun _ => some hotZero)) = _
      rw [oneHotReadAllAlg_step_qBasis, hotRecAt_zero]
      congr 1
  | succ t ih =>
      rw [oneHotState_succ, ih, oneHotOracleMat_mulVec_qBasis,
        oneHotReadAllAlg_step_qBasis]
      congr 1
      change idxSwapPerm (idxAt ι t) (idxAt ι (t + 1))
          (slotSwapPerm (idxAt ι t)
            (oneHotOracleMap a (idxAt ι t, some hotZero, hotRecAt a t))) = _
      cases hidx : idxAt ι t with
      | none =>
          have hcard : Fintype.card ι ≤ t := (idxAt_eq_none_iff t).mp hidx
          have h1 : hotRecAt a t = hotRecAt a (t + 1) := by
            rw [hotRecAt_of_card_le a hcard, hotRecAt_of_card_le a (by omega)]
          rw [oneHotOracleMap_none, slotSwapPerm_none]
          change (Equiv.swap none (idxAt ι (t + 1)) none, some hotZero, hotRecAt a t) = _
          rw [Equiv.swap_apply_left, h1]
      | some j =>
          have hj : (Fintype.equivFin ι j : ℕ) = t := equivFin_of_idxAt hidx
          rw [oneHotOracleMap_clean, slotSwapPerm_some]
          change (Equiv.swap (some j) (idxAt ι (t + 1)) (some j), hotRecAt a t j,
            Function.update (hotRecAt a t) j (some (hotCode (a j)))) = _
          rw [Equiv.swap_apply_left, hotRecAt_self a hj, update_hotRecAt a hj]

/-- **The algorithm announces `dec` of the full one-hot record after `|ι|`
queries.** -/
theorem oneHotReadAllAlg_prob (dec : QRec ι (Hot σ) → O) [DecidableEq O]
    (a : ι → σ) :
    qProb (oneHotReadAllAlg dec).readout
      (oneHotState (oneHotReadAllAlg dec) a (Fintype.card ι))
      (dec fun i => some (hotCode (a i))) = 1 := by
  rw [oneHotReadAllAlg_state, hotRecAt_of_card_le a le_rfl, qProb_qBasis]
  simp

/-! ## Every observationally determined problem is exactly solvable -/

/-- The readout: decode the one-hot record slot-wise, then decode the logical
record into the value of `f`. -/
noncomputable def hotRecDecode [Nonempty O] (read : X → ι → σ) (f : X → O)
    (r : QRec ι (Hot σ)) : O :=
  recDecode read f fun i => (r i).bind decodeHot

lemma hotRecDecode_apply [Nonempty O] {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y) (x : X) :
    hotRecDecode read f (fun i => some (hotCode (read x i))) = f x := by
  change recDecode read f (fun i => decodeHot (hotCode (read x i))) = f x
  simp only [decodeHot_hotCode]
  exact recDecode_apply hdet x

/-- **Every observationally determined problem has an exact `|ι|`-query
one-hot algorithm.** -/
theorem exists_oneHotComputesWithErrorOn [DecidableEq O] [Nonempty O]
    {read : X → ι → σ} {f : X → O} (hdet : ∀ x y, read x = read y → f x = f y)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ A : QAlg ι (Hot σ) O (QRec ι (Hot σ)),
      OneHotComputesWithErrorOn A (Fintype.card ι) read f ε := by
  refine ⟨oneHotReadAllAlg (hotRecDecode read f), fun x => ?_⟩
  have h : qProb (oneHotReadAllAlg (hotRecDecode read f)).readout
      (oneHotState (oneHotReadAllAlg (hotRecDecode read f)) (read x)
        (Fintype.card ι)) (f x) = 1 := by
    rw [← hotRecDecode_apply hdet x]
    exact oneHotReadAllAlg_prob _ _
  rw [h]
  linarith

/-- **Reading everything is enough, with the exact cap**:
`oneHotQQueryOn ≤ |ι|`. -/
theorem oneHotQQueryOn_le_card [DecidableEq O] [Nonempty O] {read : X → ι → σ}
    {f : X → O} (hdet : ∀ x y, read x = read y → f x = f y) {ε : ℝ} (hε : 0 ≤ ε) :
    oneHotQQueryOn read f ε ≤ Fintype.card ι := by
  obtain ⟨A, hA⟩ := exists_oneHotComputesWithErrorOn hdet hε
  exact oneHotQQueryOn_le hA

end QuantumQueryComplexity
