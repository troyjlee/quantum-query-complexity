import QuantumQueryComplexity.Quantum.SelectRoutine
import QuantumQueryComplexity.Quantum.Simulation
import QuantumQueryComplexity.Quantum.RoutineLift

set_option linter.style.header false
set_option synthInstance.maxSize 3200
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Adaptive composition: running the algorithm that an outcome selects

`Realizes.pair` (`ProductRun.lean`) runs two algorithms independently. Here the second
algorithm depends on the first one's outcome: after `A` produces `o`, run `B o`. The outcome
law is exact,

    Pr[(o, o')] = P₁(o) · P₂(o)(o'),

and the costs add, `q₁ + q₂`, as for a classical procedure that measures `o` and then chooses
`B o`. The construction keeps `o` coherent. It runs all the algorithms `B o` in one bank,
selected by the first bank's basis state (`bankCtrl`), with the selected algorithm's initial
state prepared by an outcome-controlled free unitary (`swapRefl`), as in robust search. The
selected algorithms may have different workspaces. They share the query count `q₂`; callers
pad shorter ones first.

## Main result

* `Realizes.bind` — the adaptive composition, with the exact law and cost `q₁ + q₂`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X] {O O' : Type} [DecidableEq O] [DecidableEq O']

/-! ## Reading a sum of outcome-restricted product states -/

section Joint

variable {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]

/-- On the event "first bank reads `o`, second bank reads `o'`", a sum of product states whose
first factor is restricted to the outcomes `o₁` keeps only the term `o₁ = o`. -/
lemma qRestrict_pairReadout_sum_prodState [Fintype O] (r₁ : QBasis ι σ W₁ → O)
    (r₂ : QBasis ι σ W₂ → O') (χ : Option ι × Option σ → ℂ) (θ : QBasis ι σ W₁ → ℂ)
    (w : O → QBasis ι σ W₂ → ℂ) (o : O) (o' : O') :
    qRestrict (pairReadout r₁ r₂) (o, o') (∑ o₁, prodState χ (qRestrict r₁ o₁ θ) (w o₁))
      = prodState χ (qRestrict r₁ o θ) (qRestrict r₂ o' (w o)) := by
  funext q
  obtain ⟨k, t, y, b⟩ := q
  have hsum : (∑ o₁, prodState χ (qRestrict r₁ o₁ θ) (w o₁)) (k, t, y, b)
      = χ (k, t) * θ y * w (r₁ y) b := by
    rw [Finset.sum_apply, Finset.sum_eq_single (r₁ y)]
    · change χ (k, t) * qRestrict r₁ (r₁ y) θ y * w (r₁ y) b = _
      simp [qRestrict]
    · intro o₁ _ ho₁
      change χ (k, t) * qRestrict r₁ o₁ θ y * w o₁ b = 0
      simp [qRestrict, Ne.symm ho₁]
    · intro h; exact absurd (Finset.mem_univ _) h
  change (if (r₁ y, r₂ b) = (o, o') then _ else 0)
    = χ (k, t) * qRestrict r₁ o θ y * qRestrict r₂ o' (w o) b
  rw [hsum]
  simp only [qRestrict, Prod.mk.injEq]
  by_cases h1 : r₁ y = o <;> by_cases h2 : r₂ b = o' <;> simp [h1, h2]

end Joint

/-! ## The adaptive composition -/

/-- **Adaptive composition.** If `P₁` is realized with `q₁` queries and, for each outcome `o`,
`P₂ o` is realized with `q₂` queries, then the two-stage procedure "run the first, then the
algorithm selected by its outcome `o`" is realized with `q₁ + q₂` queries, with outcome law
`(o, o') ↦ P₁ x o · P₂ o x o'`.

The construction uses the bank layout of `pairRoutine`. The first bank runs the first algorithm
`A₁`. The second bank, `Bool × (Σ o, V₂ o)`, starts in a blank vector (flag `true`); the free
unitary `bankCtrl A₁.readout (swapRefl blank ∘ start)` carries it, on the component where the
first bank reads `o`, to the initial vector of `A₂ o` (flag `false`, sector `o`). The second bank
then runs the coherent selection `QRoutine.sig` of all the second-stage algorithms. -/
theorem Realizes.bind [Fintype O] {read : X → ι → σ} {q₁ q₂ : ℕ} {P₁ : X → O → ℝ}
    {P₂ : O → X → O' → ℝ} (h₁ : Realizes read q₁ P₁) (h₂ : ∀ o, Realizes read q₂ (P₂ o)) :
    Realizes read (q₁ + q₂) (fun x p => P₁ x p.1 * P₂ p.1 x p.2 : X → O × O' → ℝ) := by
  obtain ⟨V₁, _, _, A₁, hA₁⟩ := h₁
  choose V₂ hV₂ hV₂' A₂ hA₂ using h₂
  let _ : ∀ o, Fintype (V₂ o) := hV₂
  let _ : ∀ o, DecidableEq (V₂ o) := hV₂'
  -- an outcome, to label the blank vector
  have hne : Nonempty (QBasis ι σ V₁) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := A₁.init_isQState
    rw [IsQState, qNormSq_def, Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact zero_ne_one h1
  obtain ⟨p₀⟩ := hne
  -- the second bank
  let start : O → QBasis ι σ (Bool × (Σ o, V₂ o)) → ℂ := fun o =>
    embedReg false (embedSig o (A₂ o).init)
  let blank : QBasis ι σ (Bool × (Σ o, V₂ o)) → ℂ :=
    embedReg true (embedSig (A₁.readout p₀) (A₂ (A₁.readout p₀)).init)
  have hstart : ∀ o, IsQState (start o) := fun o =>
    isQState_embedReg false (by rw [IsQState, qNormSq_embedSig]; exact (A₂ o).init_isQState)
  have hblank : IsQState blank :=
    isQState_embedReg true (by
      rw [IsQState, qNormSq_embedSig]; exact (A₂ (A₁.readout p₀)).init_isQState)
  have horth : ∀ o, qInner blank (start o) = 0 := fun o => by
    rw [qInner_embedReg]
    simp
  let prep : O → Matrix (QBasis ι σ (Bool × (Σ o, V₂ o))) (QBasis ι σ (Bool × (Σ o, V₂ o))) ℂ :=
    fun o => swapRefl blank (start o)
  have hprep : ∀ o, prep o ∈ Matrix.unitaryGroup _ ℂ := fun o =>
    swapRefl_mem_unitaryGroup hblank (hstart o) (horth o)
  have hprep_blank : ∀ o, prep o *ᵥ blank = start o := fun o => swapRefl_mulVec hblank (horth o)
  -- the routines
  let R₁ : QRoutine ι σ V₁ := QRoutine.mk q₁ A₁.step A₁.step_unitary
  let R₂ : QRoutine ι σ (Σ o, V₂ o) :=
    QRoutine.sig q₂ fun o => QRoutine.mk q₂ (A₂ o).step (A₂ o).step_unitary
  let R : QRoutine ι σ (QBasis ι σ V₁ × QBasis ι σ (Bool × (Σ o, V₂ o))) :=
    (pairRoutine R₁ QRoutine.identity).comp
      ((QRoutine.ofUnitary (bankCtrl A₁.readout prep)
          (bankCtrl_mem_unitaryGroup A₁.readout hprep)).comp
        (pairRoutine QRoutine.identity (R₂.liftReg Bool)))
  let r₂ : QBasis ι σ (Bool × (Σ o, V₂ o)) → O' :=
    stripReadout (V := Bool) (sigReadout fun o => (A₂ o).readout)
  refine ⟨_, inferInstance, inferInstance,
    R.toAlg (prodState blankReg A₁.init blank) (isQState_prodState A₁.init_isQState hblank)
      (pairReadout A₁.readout r₂), ?_⟩
  intro x ⟨o, o'⟩
  have hlen : R.len = q₁ + q₂ := by
    simp only [R, QRoutine.comp_len, pairRoutine_len, QRoutine.ofUnitary_len,
      QRoutine.identity_len, QRoutine.liftReg_len]
    change q₁ + 0 + (0 + (0 + q₂)) = q₁ + q₂
    omega
  -- the final state
  have hrun : R.run (read x)
      = (pairRoutine (ι := ι) (σ := σ) (QRoutine.identity (W := V₁)) (R₂.liftReg Bool)).run
          (read x)
        * (bankCtrl A₁.readout prep
          * (pairRoutine R₁ (QRoutine.identity (W := Bool × (Σ o, V₂ o)))).run (read x)) := by
    simp only [R]
    rw [QRoutine.comp_run, QRoutine.comp_run, QRoutine.ofUnitary_run, Matrix.mul_assoc]
  have hR₁ : R₁.run (read x) *ᵥ A₁.init = A₁.state (read x) q₁ := by
    rw [state_eq_runUpto2 A₁ q₁]; rfl
  have hR₂ : ∀ o, R₂.run (read x) *ᵥ embedSig o (A₂ o).init
      = embedSig o ((A₂ o).state (read x) q₂) := fun o => by
    simp only [R₂]
    rw [QRoutine.sig_run_mulVec_embed (L := q₂)
      (R := fun o => QRoutine.mk q₂ (A₂ o).step (A₂ o).step_unitary) (fun _ => rfl),
      state_eq_runUpto2 (A₂ o) q₂]
    rfl
  have hstate : R.run (read x) *ᵥ prodState blankReg A₁.init blank
      = ∑ o₁, prodState blankReg (qRestrict A₁.readout o₁ (A₁.state (read x) q₁))
          (embedReg false (embedSig o₁ ((A₂ o₁).state (read x) q₂))) := by
    rw [hrun, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, pairRoutine_run_prodState,
      QRoutine.identity_run, Matrix.one_mulVec, hR₁, bankCtrl_mulVec_prodState,
      Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun o₁ _ => ?_
    rw [pairRoutine_run_prodState, QRoutine.identity_run, Matrix.one_mulVec, hprep_blank,
      QRoutine.liftReg_run_embed, hR₂]
  rw [QAlg.prob, ← hlen, QRoutine.toAlg_state_len, hstate]
  change qProb (pairReadout A₁.readout r₂) _ (o, o') = _
  rw [qProb_eq_qNormSq_qRestrict, qRestrict_pairReadout_sum_prodState, qNormSq_prodState,
    sum_normSq_blankReg, one_mul, ← qProb_eq_qNormSq_qRestrict, ← qProb_eq_qNormSq_qRestrict]
  simp only [r₂]
  rw [qProb_stripReadout_embedReg, qProb_sigReadout_embedSig]
  rw [show qProb A₁.readout (A₁.state (read x) q₁) o = A₁.prob (read x) q₁ o from rfl,
    show qProb (A₂ o).readout ((A₂ o).state (read x) q₂) o' = (A₂ o).prob (read x) q₂ o'
      from rfl, hA₁, hA₂]

end QuantumQueryComplexity
