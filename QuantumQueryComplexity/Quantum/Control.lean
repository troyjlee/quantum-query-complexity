import QuantumQueryComplexity.Quantum.Blocks
import QuantumQueryComplexity.Quantum.Routine
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The controlled query, and idling

The value oracle has an **idle index** `none`, and `Oracle.lean` records that it
does nothing there.  That is only half of what a circuit needs: to *use* the
idle sector one must be able to move the query index into it and back, and
"assign `none` to the index register" is not injective, hence not unitary.

The fix is the same one `ReadAll.lean` used for copying: **swap, don't assign**.
Extend the workspace with a control bit and a parking slot,

  `CtrlWork ι W = Bool × Option ι × W`,

and let `parkMat` swap the index register with the parking slot exactly when the
control bit is `false`.  Then

  `ctrlQuery a = parkMat · O_a · parkMat`

contains **exactly one** oracle factor and satisfies

* `ctrlQuery_qBasis_true`  — on control `true` it *is* the query;
* `ctrlQuery_qBasis_false` — on control `false` with a blank slot it is the
  identity: the physical query is spent on the idle index.

So one physical query implements the controlled logical query, which is what
phase detection will need, and what makes an idle query available for padding a
schedule by one (`padOne`; padding by two needs no workspace at all, see
`QRoutine.padTwo`).

`IsParked` names the sector this all happens in — control `false`, slot blank —
and `ctrlQuery_mulVec_of_parked` upgrades the basis-state statement to states
supported there, which is the form a padding argument consumes.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-- The workspace of a controlled routine: a control bit, a parking slot for the
query index, and the original workspace. -/
abbrev CtrlWork (ι W : Type) : Type := Bool × Option ι × W

/-! ## Parking -/

/-- Swap the query-index register with the parking slot, unless the control bit
says otherwise. -/
def parkMap : QBasis ι σ (CtrlWork ι W) → QBasis ι σ (CtrlWork ι W)
  | (k, t, (true, s, w)) => (k, t, (true, s, w))
  | (k, t, (false, s, w)) => (s, t, (false, k, w))

@[simp] lemma parkMap_true (k : Option ι) (t : Option σ) (s : Option ι) (w : W) :
    parkMap ((k, t, (true, s, w)) : QBasis ι σ (CtrlWork ι W))
      = (k, t, (true, s, w)) := rfl

@[simp] lemma parkMap_false (k : Option ι) (t : Option σ) (s : Option ι) (w : W) :
    parkMap ((k, t, (false, s, w)) : QBasis ι σ (CtrlWork ι W))
      = (s, t, (false, k, w)) := rfl

lemma parkMap_involutive :
    Function.Involutive (parkMap (ι := ι) (σ := σ) (W := W)) := by
  rintro ⟨k, t, b, s, w⟩
  cases b <;> rfl

/-- Parking, as a permutation of the basis. -/
def parkPerm : Equiv.Perm (QBasis ι σ (CtrlWork ι W)) :=
  Function.Involutive.toPerm _ parkMap_involutive

/-- Parking, as a unitary. -/
def parkMat : Matrix (QBasis ι σ (CtrlWork ι W)) (QBasis ι σ (CtrlWork ι W)) ℂ :=
  qPerm parkPerm

lemma parkMat_mem_unitaryGroup :
    parkMat (ι := ι) (σ := σ) (W := W)
      ∈ Matrix.unitaryGroup (QBasis ι σ (CtrlWork ι W)) ℂ :=
  qPerm_mem_unitaryGroup _

lemma parkMat_mulVec_apply (ψ : QBasis ι σ (CtrlWork ι W) → ℂ)
    (p : QBasis ι σ (CtrlWork ι W)) : (parkMat *ᵥ ψ) p = ψ (parkMap p) := by
  rw [parkMat, qPerm_mulVec_apply]
  rfl

/-! ## The controlled query -/

/-- **The controlled query**: park, query, unpark.  Note the single `oracleMat`
factor — this costs exactly one physical query. -/
def ctrlQuery (a : ι → σ) :
    Matrix (QBasis ι σ (CtrlWork ι W)) (QBasis ι σ (CtrlWork ι W)) ℂ :=
  parkMat * (oracleMat a * parkMat)

lemma ctrlQuery_mem_unitaryGroup (a : ι → σ) :
    ctrlQuery (W := W) a ∈ Matrix.unitaryGroup (QBasis ι σ (CtrlWork ι W)) ℂ :=
  mul_mem parkMat_mem_unitaryGroup
    (mul_mem (oracleMat_mem_unitaryGroup a) parkMat_mem_unitaryGroup)

/-- The basis action of the controlled query. -/
def ctrlMap (a : ι → σ) :
    QBasis ι σ (CtrlWork ι W) → QBasis ι σ (CtrlWork ι W) :=
  fun p => parkMap (oracleMap a (parkMap p))

lemma ctrlQuery_mulVec_apply (a : ι → σ) (ψ : QBasis ι σ (CtrlWork ι W) → ℂ)
    (p : QBasis ι σ (CtrlWork ι W)) :
    (ctrlQuery a *ᵥ ψ) p = ψ (ctrlMap a p) := by
  rw [ctrlQuery, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    parkMat_mulVec_apply, oracleMat_mulVec_apply, parkMat_mulVec_apply]
  rfl

lemma ctrlMap_involutive (a : ι → σ) :
    Function.Involutive (ctrlMap (σ := σ) (W := W) a) := by
  intro p
  show parkMap (oracleMap a (parkMap (parkMap (oracleMap a (parkMap p))))) = p
  rw [parkMap_involutive, oracleMap_involutive, parkMap_involutive]

lemma ctrlQuery_mulVec_qBasis (a : ι → σ) (r : QBasis ι σ (CtrlWork ι W)) :
    ctrlQuery a *ᵥ qBasis r = qBasis (ctrlMap a r) := by
  funext p
  rw [ctrlQuery_mulVec_apply, qBasis_apply, qBasis_apply]
  by_cases h : ctrlMap a p = r
  · rw [if_pos h, if_pos (by rw [← h, ctrlMap_involutive a p])]
  · rw [if_neg h, if_neg (fun hc => h (by rw [hc, ctrlMap_involutive a r]))]

lemma ctrlMap_true (a : ι → σ) (k : Option ι) (t : Option σ) (s : Option ι)
    (w : W) :
    ctrlMap a ((k, t, (true, s, w)) : QBasis ι σ (CtrlWork ι W))
      = oracleMap a (k, t, (true, s, w)) := by
  cases k <;> rfl

lemma ctrlMap_false_blank (a : ι → σ) (k : Option ι) (t : Option σ) (w : W) :
    ctrlMap a ((k, t, (false, none, w)) : QBasis ι σ (CtrlWork ι W))
      = (k, t, (false, none, w)) := rfl

/-- **On the control-true sector the controlled query is the query.** -/
theorem ctrlQuery_qBasis_true (a : ι → σ) (k : Option ι) (t : Option σ)
    (s : Option ι) (w : W) :
    ctrlQuery a *ᵥ qBasis ((k, t, (true, s, w)) : QBasis ι σ (CtrlWork ι W))
      = oracleMat a *ᵥ qBasis (k, t, (true, s, w)) := by
  rw [ctrlQuery_mulVec_qBasis, oracleMat_mulVec_qBasis, ctrlMap_true]

/-- **On the control-false sector with a blank slot the controlled query is the
identity**: the physical query is spent on the idle index. -/
theorem ctrlQuery_qBasis_false (a : ι → σ) (k : Option ι) (t : Option σ) (w : W) :
    ctrlQuery a *ᵥ qBasis ((k, t, (false, none, w)) : QBasis ι σ (CtrlWork ι W))
      = qBasis (k, t, (false, none, w)) := by
  rw [ctrlQuery_mulVec_qBasis, ctrlMap_false_blank]

/-! ## The parked sector -/

/-- A state is **parked** if it lives where the control bit is `false` and the
parking slot is blank — the sector on which a query idles. -/
def IsParked (ψ : QBasis ι σ (CtrlWork ι W) → ℂ) : Prop :=
  ∀ p, ψ p ≠ 0 → p.2.2.1 = false ∧ p.2.2.2.1 = none

lemma ctrlMap_eq_self {a : ι → σ} {p : QBasis ι σ (CtrlWork ι W)}
    (h1 : p.2.2.1 = false) (h2 : p.2.2.2.1 = none) : ctrlMap a p = p := by
  obtain ⟨k, t, b, s, w⟩ := p
  simp only at h1 h2
  subst h1
  subst h2
  rfl

lemma ctrlMap_not_parked {a : ι → σ} {p : QBasis ι σ (CtrlWork ι W)}
    (h : ¬ (p.2.2.1 = false ∧ p.2.2.2.1 = none)) :
    ¬ ((ctrlMap a p).2.2.1 = false ∧ (ctrlMap a p).2.2.2.1 = none) := by
  intro hc
  apply h
  have hfix : ctrlMap a (ctrlMap a p) = ctrlMap a p := ctrlMap_eq_self hc.1 hc.2
  rw [ctrlMap_involutive a p] at hfix
  rw [hfix]
  exact hc

/-- **A parked state does not notice a query.**  This is the form a padding
argument consumes. -/
theorem ctrlQuery_mulVec_of_parked (a : ι → σ)
    {ψ : QBasis ι σ (CtrlWork ι W) → ℂ} (hψ : IsParked ψ) :
    ctrlQuery a *ᵥ ψ = ψ := by
  funext p
  rw [ctrlQuery_mulVec_apply]
  by_cases hp : p.2.2.1 = false ∧ p.2.2.2.1 = none
  · rw [ctrlMap_eq_self hp.1 hp.2]
  · have h1 : ψ p = 0 := by
      by_contra h
      exact hp (hψ p h)
    have h2 : ψ (ctrlMap a p) = 0 := by
      by_contra h
      exact ctrlMap_not_parked hp (hψ _ h)
    rw [h1, h2]

/-! ## Idling and padding by one -/

/-- The controlled query as a **one-query routine**. -/
def ctrlQueryRoutine : QRoutine ι σ (CtrlWork ι W) where
  len := 1
  step := fun _ => parkMat
  step_unitary := fun _ => parkMat_mem_unitaryGroup

@[simp] lemma ctrlQueryRoutine_len :
    (ctrlQueryRoutine (ι := ι) (σ := σ) (W := W)).len = 1 := rfl

lemma ctrlQueryRoutine_run (a : ι → σ) :
    (ctrlQueryRoutine (ι := ι) (σ := σ) (W := W)).run a = ctrlQuery a := rfl

/-- **Padding by one query.** -/
def padOne (R : QRoutine ι σ (CtrlWork ι W)) : QRoutine ι σ (CtrlWork ι W) :=
  R.comp ctrlQueryRoutine

@[simp] lemma padOne_len (R : QRoutine ι σ (CtrlWork ι W)) :
    (padOne R).len = R.len + 1 := rfl

lemma padOne_run (R : QRoutine ι σ (CtrlWork ι W)) (a : ι → σ) :
    (padOne R).run a = ctrlQuery a * R.run a := by
  rw [padOne, QRoutine.comp_run, ctrlQueryRoutine_run]

/-- **Padding by one is free on the parked sector.** -/
theorem padOne_run_mulVec (R : QRoutine ι σ (CtrlWork ι W)) (a : ι → σ)
    (ψ : QBasis ι σ (CtrlWork ι W) → ℂ) (h : IsParked (R.run a *ᵥ ψ)) :
    (padOne R).run a *ᵥ ψ = R.run a *ᵥ ψ := by
  rw [padOne_run, ← Matrix.mulVec_mulVec, ctrlQuery_mulVec_of_parked a h]

/-! ## Controlled execution of a whole routine

A fixed step is controlled by lifting it to the parked workspace and
conditioning on the control bit — both instances of `blockFam`.  A query is
controlled by `ctrlQuery`.  Neither adds a query, so `control_len` is an
equality.

The statements are about the **encoded subspace** `embedCtrl b ψ` — control bit
`b`, parking slot blank — and not global matrix identities, which would be
false: off that subspace `ctrlQuery` swaps a parked index back in and queries
it. -/

/-- The blank-slot embedding: `ψ` in the sector with control bit `b` and an
empty parking slot. -/
def embedCtrl (b : Bool) (ψ : QBasis ι σ W → ℂ) : QBasis ι σ (CtrlWork ι W) → ℂ :=
  embedReg b (embedReg none ψ)

lemma embedCtrl_apply (b : Bool) (ψ : QBasis ι σ W → ℂ)
    (p : QBasis ι σ (CtrlWork ι W)) :
    embedCtrl b ψ p =
      if p.2.2.1 = b ∧ p.2.2.2.1 = none then ψ (p.1, p.2.1, p.2.2.2.2) else 0 := by
  rw [embedCtrl, embedReg_apply, embedReg_apply]
  by_cases h1 : p.2.2.1 = b <;> by_cases h2 : p.2.2.2.1 = none <;> simp [h1, h2]

lemma isParked_embedCtrl_false (ψ : QBasis ι σ W → ℂ) :
    IsParked (embedCtrl false ψ) := by
  intro p hp
  by_contra h
  exact hp (by rw [embedCtrl_apply, if_neg h])

/-- A fixed step, lifted to the parked workspace and conditioned on the control
bit. -/
def ctrlStep (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) :
    Matrix (QBasis ι σ (CtrlWork ι W)) (QBasis ι σ (CtrlWork ι W)) ℂ :=
  blockFam (fun b : Bool => bif b then liftReg (Option ι) U else 1)

lemma ctrlStep_mem_unitaryGroup {U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) :
    ctrlStep U ∈ Matrix.unitaryGroup (QBasis ι σ (CtrlWork ι W)) ℂ := by
  refine blockFam_mem_unitaryGroup fun b => ?_
  cases b
  · exact one_mem_qUnitary
  · exact liftReg_mem_unitaryGroup hU

lemma ctrlStep_mulVec_embed_true (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (ψ : QBasis ι σ W → ℂ) :
    ctrlStep U *ᵥ embedCtrl true ψ = embedCtrl true (U *ᵥ ψ) := by
  rw [ctrlStep, embedCtrl, blockFam_mulVec_embed]
  show embedReg true (liftReg (Option ι) U *ᵥ embedReg none ψ) = _
  rw [liftReg_mulVec_embed]
  rfl

lemma ctrlStep_mulVec_embed_false (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (ψ : QBasis ι σ W → ℂ) :
    ctrlStep U *ᵥ embedCtrl false ψ = embedCtrl false ψ := by
  rw [ctrlStep, embedCtrl, blockFam_mulVec_embed]
  show embedReg false ((1 : Matrix (QBasis ι σ (Option ι × W))
    (QBasis ι σ (Option ι × W)) ℂ) *ᵥ embedReg none ψ) = _
  rw [Matrix.one_mulVec]

lemma parkMat_mulVec_embed_true (ψ : QBasis ι σ W → ℂ) :
    parkMat *ᵥ embedCtrl true ψ = embedCtrl true ψ := by
  funext p
  rw [parkMat_mulVec_apply]
  obtain ⟨k, t, b, s, w⟩ := p
  cases b
  · rw [parkMap_false, embedCtrl_apply, embedCtrl_apply]
    simp
  · rw [parkMap_true]

lemma oracleMat_mulVec_embedCtrl (a : ι → σ) (b : Bool) (ψ : QBasis ι σ W → ℂ) :
    oracleMat a *ᵥ embedCtrl b ψ = embedCtrl b (oracleMat a *ᵥ ψ) := by
  rw [embedCtrl, blockFam_oracle (V := Bool), liftReg_mulVec_embed,
    blockFam_oracle (V := Option ι), liftReg_mulVec_embed]
  rfl

lemma ctrlQuery_mulVec_embed_true (a : ι → σ) (ψ : QBasis ι σ W → ℂ) :
    ctrlQuery a *ᵥ embedCtrl true ψ = embedCtrl true (oracleMat a *ᵥ ψ) := by
  rw [ctrlQuery, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    parkMat_mulVec_embed_true, oracleMat_mulVec_embedCtrl,
    parkMat_mulVec_embed_true]

lemma ctrlQuery_mulVec_embed_false (a : ι → σ) (ψ : QBasis ι σ W → ℂ) :
    ctrlQuery a *ᵥ embedCtrl false ψ = embedCtrl false ψ :=
  ctrlQuery_mulVec_of_parked a (isParked_embedCtrl_false ψ)

/-- The controlled routine, built one query at a time. -/
def controlUpto (R : QRoutine ι σ W) : ℕ → QRoutine ι σ (CtrlWork ι W)
  | 0 => QRoutine.ofUnitary (ctrlStep (R.step 0))
      (ctrlStep_mem_unitaryGroup (R.step_unitary 0))
  | t + 1 => (controlUpto R t).comp
      (ctrlQueryRoutine.comp (QRoutine.ofUnitary (ctrlStep (R.step (t + 1)))
        (ctrlStep_mem_unitaryGroup (R.step_unitary (t + 1)))))

/-- **Controlled execution** of a routine. -/
def QRoutine.control (R : QRoutine ι σ W) : QRoutine ι σ (CtrlWork ι W) :=
  controlUpto R R.len

lemma controlUpto_len (R : QRoutine ι σ W) (t : ℕ) : (controlUpto R t).len = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      show (controlUpto R t).len + (1 + 0) = t + 1
      rw [ih]

/-- **Controlling a routine costs no extra queries.** -/
theorem control_len (R : QRoutine ι σ W) : R.control.len = R.len :=
  controlUpto_len R R.len

lemma controlUpto_run_true (R : QRoutine ι σ W) (a : ι → σ) (t : ℕ)
    (ψ : QBasis ι σ W → ℂ) :
    (controlUpto R t).run a *ᵥ embedCtrl true ψ
      = embedCtrl true (R.runUpto a t *ᵥ ψ) := by
  induction t with
  | zero =>
      show ctrlStep (R.step 0) *ᵥ embedCtrl true ψ = _
      rw [ctrlStep_mulVec_embed_true]
      rfl
  | succ t ih =>
      show ((controlUpto R t).comp _).run a *ᵥ embedCtrl true ψ = _
      rw [QRoutine.comp_run, QRoutine.comp_run, QRoutine.ofUnitary_run,
        ctrlQueryRoutine_run, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
        ctrlQuery_mulVec_embed_true, ctrlStep_mulVec_embed_true,
        QRoutine.runUpto_succ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc]

lemma controlUpto_run_false (R : QRoutine ι σ W) (a : ι → σ) (t : ℕ)
    (ψ : QBasis ι σ W → ℂ) :
    (controlUpto R t).run a *ᵥ embedCtrl false ψ = embedCtrl false ψ := by
  induction t with
  | zero =>
      show ctrlStep (R.step 0) *ᵥ embedCtrl false ψ = _
      rw [ctrlStep_mulVec_embed_false]
  | succ t ih =>
      show ((controlUpto R t).comp _).run a *ᵥ embedCtrl false ψ = _
      rw [QRoutine.comp_run, QRoutine.comp_run, QRoutine.ofUnitary_run,
        ctrlQueryRoutine_run, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
        ctrlQuery_mulVec_embed_false, ctrlStep_mulVec_embed_false]

/-- **On the control-true sector the controlled routine runs.** -/
theorem control_run_true (R : QRoutine ι σ W) (a : ι → σ) (ψ : QBasis ι σ W → ℂ) :
    R.control.run a *ᵥ embedCtrl true ψ = embedCtrl true (R.run a *ᵥ ψ) :=
  controlUpto_run_true R a R.len ψ

/-- **On the control-false sector it does nothing** — and still spends exactly
`R.len` physical queries. -/
theorem control_run_false (R : QRoutine ι σ W) (a : ι → σ) (ψ : QBasis ι σ W → ℂ) :
    R.control.run a *ᵥ embedCtrl false ψ = embedCtrl false ψ :=
  controlUpto_run_false R a R.len ψ

end QuantumQueryComplexity
