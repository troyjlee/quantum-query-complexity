import QuantumQueryComplexity.Quantum.Complexity
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Reading the whole input exactly

Every observationally determined problem has an **exact** algorithm making
`|ι|` queries.  This is the theorem that makes `qQueryOn` a genuine minimum
rather than `sInf ∅ = 0`, and it is the base case of the query model: it says
the model can do at least what a classical algorithm can.

The construction records the answers in a workspace `QRec ι σ = ι → Option σ`
and never leaves the computational basis.  Two families of basis permutations
do all the work:

* `idxSwapPerm u v` — transpose the two index-register values `u` and `v`.
  Since the index register's content is *known* at each time (it is `idxAt t`),
  a transposition suffices to move it to the next index; "assign the index
  register" would not be unitary, but "transpose the value it holds with the one
  it should hold next" is.
* `slotSwapPerm j` — swap the answer register with the workspace slot `j`.
  A *swap*, not a copy: copying is not injective, but the slot is blank when the
  swap happens, so the swap has the effect of a copy and clears the answer
  register for the next query.

The step unitary at time `t` is `idxSwapPerm (prevIdx t) (idxAt t)` after
`slotSwapPerm (prevIdx t)`, and the invariant carried by the induction is

  `state a t = |idxAt t⟩ |⊥⟩ |recAt a t⟩`,

with `recAt a t` the record holding the answers of the first `t` indices.  It
holds for **every** `t`, with no side condition: past `|ι|` the index register is
idle, the oracle acts trivially and the state stops moving, so the algorithm
pads for free.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X]

/-! ## Two families of basis permutations -/

section IdxSwap

variable {W : Type} [Fintype W] [DecidableEq W]

/-- Transpose two values of the query-index register. -/
def idxSwapMap (u v : Option ι) : QBasis ι σ W → QBasis ι σ W :=
  fun p => (Equiv.swap u v p.1, p.2)

lemma idxSwapMap_involutive (u v : Option ι) :
    Function.Involutive (idxSwapMap (σ := σ) (W := W) u v) := by
  rintro ⟨k, r⟩
  simp [idxSwapMap]

/-- The index-register transposition, as a permutation of the basis. -/
def idxSwapPerm (u v : Option ι) : Equiv.Perm (QBasis ι σ W) :=
  Function.Involutive.toPerm _ (idxSwapMap_involutive u v)

@[simp] lemma idxSwapPerm_apply (u v : Option ι) (p : QBasis ι σ W) :
    idxSwapPerm u v p = (Equiv.swap u v p.1, p.2) := rfl

end IdxSwap

/-- The workspace of the exact algorithm: a record of the answers seen so far. -/
abbrev QRec (ι σ : Type) : Type := ι → Option σ

/-- Swap the answer register with the workspace slot `j`. -/
def slotSwapMap (j : ι) : QBasis ι σ (QRec ι σ) → QBasis ι σ (QRec ι σ) :=
  fun p => (p.1, p.2.2 j, Function.update p.2.2 j p.2.1)

lemma slotSwapMap_involutive (j : ι) :
    Function.Involutive (slotSwapMap (ι := ι) (σ := σ) j) := by
  rintro ⟨k, t, w⟩
  simp [slotSwapMap, Function.update_idem]

/-- The slot swap at an *optional* index: at `none` there is nothing to store, so
the algorithm idles.  This is what lets one formula describe every step. -/
def slotSwapPerm : Option ι → Equiv.Perm (QBasis ι σ (QRec ι σ))
  | none => 1
  | some j => Function.Involutive.toPerm _ (slotSwapMap_involutive j)

@[simp] lemma slotSwapPerm_none :
    slotSwapPerm (ι := ι) (σ := σ) none = 1 := rfl

@[simp] lemma slotSwapPerm_some (j : ι) (p : QBasis ι σ (QRec ι σ)) :
    slotSwapPerm (some j) p = (p.1, p.2.2 j, Function.update p.2.2 j p.2.1) := rfl

/-! ## The schedule -/

/-- The index queried at time `t`; `none` once every index has been read. -/
noncomputable def idxAt (ι : Type) [Fintype ι] (t : ℕ) : Option ι :=
  if h : t < Fintype.card ι then some ((Fintype.equivFin ι).symm ⟨t, h⟩) else none

/-- The index queried at time `t - 1`, i.e. the one whose answer the step at time
`t` has to store. -/
noncomputable def prevIdx (ι : Type) [Fintype ι] : ℕ → Option ι
  | 0 => none
  | t + 1 => idxAt ι t

lemma idxAt_of_lt {t : ℕ} (h : t < Fintype.card ι) :
    idxAt ι t = some ((Fintype.equivFin ι).symm ⟨t, h⟩) := dif_pos h

lemma idxAt_eq_none_iff (t : ℕ) : idxAt ι t = none ↔ Fintype.card ι ≤ t := by
  unfold idxAt
  by_cases h : t < Fintype.card ι
  · simp only [h, dif_pos, reduceCtorEq, false_iff, not_le]
  · simp only [h, dif_neg, not_false_iff, true_iff]
    omega

lemma equivFin_of_idxAt {t : ℕ} {j : ι} (h : idxAt ι t = some j) :
    (Fintype.equivFin ι j : ℕ) = t := by
  by_cases ht : t < Fintype.card ι
  · rw [idxAt_of_lt ht] at h
    have hj : j = (Fintype.equivFin ι).symm ⟨t, ht⟩ := (Option.some_injective _ h).symm
    rw [hj, Equiv.apply_symm_apply]
  · rw [idxAt, dif_neg ht] at h
    exact absurd h (by simp)

/-! ## The record -/

/-- The workspace after `t` queries: the answers at the first `t` indices. -/
noncomputable def recAt (a : ι → σ) (t : ℕ) : QRec ι σ :=
  fun i => if (Fintype.equivFin ι i : ℕ) < t then some (a i) else none

lemma recAt_apply (a : ι → σ) (t : ℕ) (i : ι) :
    recAt a t i = if (Fintype.equivFin ι i : ℕ) < t then some (a i) else none := rfl

lemma recAt_zero (a : ι → σ) : recAt a 0 = fun _ => none := by
  funext i
  simp [recAt_apply]

/-- Once every index has been read the record is complete. -/
lemma recAt_of_card_le (a : ι → σ) {t : ℕ} (h : Fintype.card ι ≤ t) :
    recAt a t = fun i => some (a i) := by
  funext i
  rw [recAt_apply, if_pos]
  exact lt_of_lt_of_le (Fintype.equivFin ι i).isLt h

/-- Storing the answer at the index read at time `t` advances the record. -/
lemma update_recAt (a : ι → σ) {t : ℕ} {j : ι} (hj : (Fintype.equivFin ι j : ℕ) = t) :
    Function.update (recAt a t) j (some (a j)) = recAt a (t + 1) := by
  funext i
  by_cases hij : i = j
  · subst hij
    rw [Function.update_self, recAt_apply, if_pos (by omega)]
  · rw [Function.update_of_ne hij, recAt_apply, recAt_apply]
    have hne : (Fintype.equivFin ι i : ℕ) ≠ t := by
      intro hc
      exact hij ((Fintype.equivFin ι).injective (Fin.ext (by rw [hc, hj])))
    by_cases hlt : (Fintype.equivFin ι i : ℕ) < t
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]

/-- The slot the algorithm is about to write to is blank. -/
lemma recAt_self_eq_none (a : ι → σ) {t : ℕ} {j : ι}
    (hj : (Fintype.equivFin ι j : ℕ) = t) : recAt a t j = none := by
  rw [recAt_apply, if_neg (by omega)]

/-! ## The algorithm -/

/-- **The algorithm that reads every coordinate**, announcing `dec` of the
completed record. -/
noncomputable def readAllAlg (dec : QRec ι σ → O) : QAlg ι σ O (QRec ι σ) where
  init := qBasis (none, none, fun _ => none)
  init_isQState := isQState_qBasis _
  step := fun t =>
    qPerm (idxSwapPerm (prevIdx ι t) (idxAt ι t)) * qPerm (slotSwapPerm (prevIdx ι t))
  step_unitary := fun _ =>
    mul_mem_qUnitary (qPerm_mem_unitaryGroup _) (qPerm_mem_unitaryGroup _)
  readout := fun p => dec p.2.2

@[simp] lemma readAllAlg_readout (dec : QRec ι σ → O) (p : QBasis ι σ (QRec ι σ)) :
    (readAllAlg dec).readout p = dec p.2.2 := rfl

lemma readAllAlg_step_qBasis (dec : QRec ι σ → O) (t : ℕ)
    (p : QBasis ι σ (QRec ι σ)) :
    (readAllAlg dec).step t *ᵥ qBasis p
      = qBasis (idxSwapPerm (prevIdx ι t) (idxAt ι t) (slotSwapPerm (prevIdx ι t) p)) := by
  show (qPerm (idxSwapPerm (prevIdx ι t) (idxAt ι t))
      * qPerm (slotSwapPerm (prevIdx ι t))) *ᵥ qBasis p = _
  rw [← Matrix.mulVec_mulVec, qPerm_mulVec_qBasis, qPerm_mulVec_qBasis]

/-- **The invariant.**  After `t` queries the algorithm holds the record of the
first `t` answers, with the index register pointing at the next index and the
answer register blank. -/
theorem readAllAlg_state (dec : QRec ι σ → O) (a : ι → σ) (t : ℕ) :
    (readAllAlg dec).state a t = qBasis (idxAt ι t, none, recAt a t) := by
  induction t with
  | zero =>
      show (readAllAlg dec).step 0 *ᵥ qBasis ((none, none, fun _ => none)) = _
      rw [readAllAlg_step_qBasis, recAt_zero]
      congr 1
  | succ t ih =>
      rw [QAlg.state_succ, ih, oracleMat_mulVec_qBasis, readAllAlg_step_qBasis]
      congr 1
      show idxSwapPerm (idxAt ι t) (idxAt ι (t + 1))
          (slotSwapPerm (idxAt ι t) (oracleMap a (idxAt ι t, none, recAt a t))) = _
      cases hidx : idxAt ι t with
      | none =>
          have hcard : Fintype.card ι ≤ t := (idxAt_eq_none_iff t).mp hidx
          have h1 : recAt a t = recAt a (t + 1) := by
            rw [recAt_of_card_le a hcard, recAt_of_card_le a (by omega)]
          rw [oracleMap_none, slotSwapPerm_none]
          show (Equiv.swap none (idxAt ι (t + 1)) none, none, recAt a t) = _
          rw [Equiv.swap_apply_left, h1]
      | some j =>
          have hj : (Fintype.equivFin ι j : ℕ) = t := equivFin_of_idxAt hidx
          rw [oracleMap_blank, slotSwapPerm_some]
          show (Equiv.swap (some j) (idxAt ι (t + 1)) (some j), recAt a t j,
            Function.update (recAt a t) j (some (a j))) = _
          rw [Equiv.swap_apply_left, recAt_self_eq_none a hj, update_recAt a hj]

/-- **The algorithm announces `dec` of the full input after `|ι|` queries.** -/
theorem readAllAlg_prob (dec : QRec ι σ → O) [DecidableEq O] (a : ι → σ) :
    (readAllAlg dec).prob a (Fintype.card ι) (dec fun i => some (a i)) = 1 := by
  rw [QAlg.prob, readAllAlg_state, recAt_of_card_le a le_rfl, qProb_qBasis]
  simp

/-! ## Every observationally determined problem is exactly solvable -/

/-- The readout: decode a completed record into the value of `f`.  Well defined
by observational determinacy — two promise inputs with the same record are
indistinguishable, hence have the same `f`-value. -/
noncomputable def recDecode [Nonempty O] (read : X → ι → σ) (f : X → O)
    (w : QRec ι σ) : O := by
  classical
  exact if h : ∃ x : X, ∀ i, w i = some (read x i) then f h.choose
    else Classical.arbitrary O

lemma recDecode_apply [Nonempty O] {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y) (x : X) :
    recDecode read f (fun i => some (read x i)) = f x := by
  classical
  have hex : ∃ y : X, ∀ i, (fun i => some (read x i)) i = some (read y i) :=
    ⟨x, fun _ => rfl⟩
  rw [recDecode, dif_pos hex]
  refine (hdet x hex.choose (funext fun i => ?_)).symm
  exact Option.some_injective _ (hex.choose_spec i)

/-- **Every observationally determined problem has an exact `|ι|`-query
algorithm.**  In particular the set of achievable query counts is nonempty, so
`qQueryOn` is a genuine minimum. -/
theorem exists_computesWithErrorOn [DecidableEq O] [Nonempty O] {read : X → ι → σ}
    {f : X → O} (hdet : ∀ x y, read x = read y → f x = f y) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ A : QAlg ι σ O (QRec ι σ),
      ComputesWithErrorOn A (Fintype.card ι) read f ε := by
  refine ⟨readAllAlg (recDecode read f), fun x => ?_⟩
  have h : (readAllAlg (recDecode read f)).prob (read x) (Fintype.card ι) (f x) = 1 := by
    rw [← recDecode_apply hdet x]
    exact readAllAlg_prob _ _
  rw [h]
  linarith

/-- **The achievable set is nonempty**, which is the hypothesis every lower
bound in `Complexity.lean` carries. -/
theorem queryCounts_nonempty [DecidableEq O] [Nonempty O] {read : X → ι → σ}
    {f : X → O} (hdet : ∀ x y, read x = read y → f x = f y) {ε : ℝ} (hε : 0 ≤ ε) :
    (QueryCounts read f ε).Nonempty := by
  obtain ⟨A, hA⟩ := exists_computesWithErrorOn hdet hε
  exact ⟨Fintype.card ι, mem_queryCounts hA⟩

/-- **Reading everything is enough**: `qQueryOn ≤ |ι|`. -/
theorem qQueryOn_le_card [DecidableEq O] [Nonempty O] {read : X → ι → σ}
    {f : X → O} (hdet : ∀ x y, read x = read y → f x = f y) {ε : ℝ} (hε : 0 ≤ ε) :
    qQueryOn read f ε ≤ Fintype.card ι := by
  obtain ⟨A, hA⟩ := exists_computesWithErrorOn hdet hε
  exact qQueryOn_le hA

end QuantumQueryComplexity
