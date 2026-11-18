import QuantumQueryComplexity.Quantum.AddOracle
import QuantumQueryComplexity.Quantum.OneHotSimulation
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The additive and value-oracle models agree within a factor of two

For a finite abelian group `G`, the native (transposition) oracle on inputs `a : ι → G` and the
additive oracle `|i, c⟩ ↦ |i, c + aᵢ⟩` of `AddOracle.lean` simulate each other at **two queries
per query**, with exactly the same output distribution on every input, hence the same success
for every function and every relation. As in `OneHotSimulation.lean`, the foreign answer register
moves into the workspace (`crossLift`, `crossEmbed`, `crossStrip`), and each simulated query is
one two-query gadget around an input-independent permutation:

* **Transposition simulates the additive oracle** (`addGadget`; the direction lower bounds
  need). The physical native register is kept blank. One additive query becomes

      query, add-into, query:

  the first query writes `aᵢ` into the blank register, a fixed permutation adds it to the
  logical register (`addIntoMat`), and the second query erases it.

* **The additive oracle simulates transposition** (`addTransGadget`). The physical additive
  register is kept clean at `some 0`. One native query becomes

      query, controlled swap and negation, query:

  the first query turns `0` into `aᵢ`, a fixed permutation swaps `⊥ ↔ some aᵢ` in the logical
  register (`addCtrlSwapMat`) and negates the physical register (`addNegMat`), and the second
  query turns `−aᵢ` back into `0`.

**Headlines.** For an additive-model algorithm `A` and `q` queries, `simAddAlg A q` is a native
algorithm on the workspace `Option G × W` whose output distribution after `2q` queries equals
that of `A` after `q` additive queries (`prob_simAddAlg`), so it computes every function and
solves every relation that `A` does (`AddComputesWithErrorOn.simAddAlg`,
`AddSolvesWithErrorOn.simAddAlg`); conversely `simTransAddAlg`
(`ComputesWithErrorOn.simTransAddAlg`, `SolvesWithErrorOn.simTransAddAlg`). The complexities
satisfy

    qQueryOn read f ε ≤ 2 · addQQueryOn read f ε,    addQQueryOn read f ε ≤ 2 · qQueryOn read f ε.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι W G : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
  [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## The run against the additive oracle, packaged -/

namespace QRoutine

/-- The operator implemented by `R` against the additive oracle. -/
def addRun (R : QRoutine ι G W) (a : ι → G) : Matrix (QBasis ι G W) (QBasis ι G W) ℂ :=
  R.runWith (addOracleMat a) R.len

theorem comp_addRun (R S : QRoutine ι G W) (a : ι → G) :
    (R.comp S).addRun a = S.addRun a * R.addRun a :=
  comp_runWith_full (addOracleMat a) R S

@[simp] lemma ofUnitary_addRun (U : Matrix (QBasis ι G W) (QBasis ι G W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι G W) ℂ) (a : ι → G) :
    (ofUnitary U hU).addRun a = U := rfl

end QRoutine

/-! ## The gadget permutations

All on `QBasis ι G (Option G × W)`: index, physical answer, logical answer, workspace. -/

/-- Add the physical answer to the logical register; blank sectors on either side are fixed. -/
def addIntoMap : QBasis ι G (Option G × W) → QBasis ι G (Option G × W)
  | (idx, some v, (t, w)) => (idx, some v, (t.map (· + v), w))
  | p => p

/-- Subtract the physical answer from the logical register (the inverse of `addIntoMap`). -/
def subIntoMap : QBasis ι G (Option G × W) → QBasis ι G (Option G × W)
  | (idx, some v, (t, w)) => (idx, some v, (t.map (· - v), w))
  | p => p

/-- The add-into permutation. -/
def addIntoPerm : Equiv.Perm (QBasis ι G (Option G × W)) where
  toFun := addIntoMap
  invFun := subIntoMap
  left_inv := by
    rintro ⟨idx, _ | v, _ | t, w⟩ <;> simp [addIntoMap, subIntoMap]
  right_inv := by
    rintro ⟨idx, _ | v, _ | t, w⟩ <;> simp [addIntoMap, subIntoMap]

/-- On an active index with physical answer `some v`: swap `⊥ ↔ some v` in the logical
register. -/
def addCtrlSwapMap : QBasis ι G (Option G × W) → QBasis ι G (Option G × W)
  | (some i, some v, (t, w)) => (some i, some v, (Equiv.swap none (some v) t, w))
  | p => p

lemma addCtrlSwapMap_involutive :
    Function.Involutive (addCtrlSwapMap (ι := ι) (G := G) (W := W)) := by
  rintro ⟨(_ | i), (_ | v), t, w⟩ <;> simp [addCtrlSwapMap]

/-- Negate the `some`-part of the physical answer register. -/
def addNegMap : QBasis ι G (Option G × W) → QBasis ι G (Option G × W)
  | (idx, t, x) => (idx, t.map Neg.neg, x)

lemma addNegMap_involutive : Function.Involutive (addNegMap (ι := ι) (G := G) (W := W)) := by
  rintro ⟨idx, (_ | c), x⟩ <;> simp [addNegMap]

/-! ## The gadget unitaries -/

/-- The add-into unitary. -/
def addIntoMat : Matrix (QBasis ι G (Option G × W)) (QBasis ι G (Option G × W)) ℂ :=
  qPerm addIntoPerm

lemma addIntoMat_mem_unitaryGroup :
    addIntoMat (ι := ι) (G := G) (W := W) ∈ Matrix.unitaryGroup (QBasis ι G (Option G × W)) ℂ :=
  qPerm_mem_unitaryGroup _

/-- The controlled-swap unitary. -/
def addCtrlSwapMat : Matrix (QBasis ι G (Option G × W)) (QBasis ι G (Option G × W)) ℂ :=
  qPerm (Function.Involutive.toPerm _ addCtrlSwapMap_involutive)

lemma addCtrlSwapMat_mem_unitaryGroup :
    addCtrlSwapMat (ι := ι) (G := G) (W := W)
      ∈ Matrix.unitaryGroup (QBasis ι G (Option G × W)) ℂ :=
  qPerm_mem_unitaryGroup _

/-- The negation unitary on the physical answer register. -/
def addNegMat : Matrix (QBasis ι G (Option G × W)) (QBasis ι G (Option G × W)) ℂ :=
  qPerm (Function.Involutive.toPerm _ addNegMap_involutive)

lemma addNegMat_mem_unitaryGroup :
    addNegMat (ι := ι) (G := G) (W := W) ∈ Matrix.unitaryGroup (QBasis ι G (Option G × W)) ℂ :=
  qPerm_mem_unitaryGroup _

lemma addIntoMat_mulVec_apply (ψ : QBasis ι G (Option G × W) → ℂ)
    (p : QBasis ι G (Option G × W)) : (addIntoMat *ᵥ ψ) p = ψ (subIntoMap p) := by
  rw [addIntoMat, qPerm_mulVec_apply]
  rfl

lemma addCtrlSwapMat_mulVec_apply (ψ : QBasis ι G (Option G × W) → ℂ)
    (p : QBasis ι G (Option G × W)) : (addCtrlSwapMat *ᵥ ψ) p = ψ (addCtrlSwapMap p) := by
  rw [addCtrlSwapMat, qPerm_mulVec_apply]
  rfl

lemma addNegMat_mulVec_apply (ψ : QBasis ι G (Option G × W) → ℂ)
    (p : QBasis ι G (Option G × W)) : (addNegMat *ᵥ ψ) p = ψ (addNegMap p) := by
  rw [addNegMat, qPerm_mulVec_apply]
  rfl

/-! ## The two gadgets -/

/-- **Transposition simulates the additive oracle**: two native queries around the add-into. -/
def addGadget : QRoutine ι G (Option G × W) where
  len := 2
  step := fun t => if t = 1 then addIntoMat else 1
  step_unitary := by
    intro t
    split_ifs
    · exact addIntoMat_mem_unitaryGroup
    · exact one_mem_qUnitary

@[simp] lemma addGadget_len : (addGadget (ι := ι) (G := G) (W := W)).len = 2 := rfl

/-- **The additive oracle simulates transposition**: two additive queries around the controlled
swap followed by the negation. -/
def addTransGadget : QRoutine ι G (Option G × W) where
  len := 2
  step := fun t => if t = 1 then addNegMat * addCtrlSwapMat else 1
  step_unitary := by
    intro t
    split_ifs
    · exact Submonoid.mul_mem _ addNegMat_mem_unitaryGroup addCtrlSwapMat_mem_unitaryGroup
    · exact one_mem_qUnitary

@[simp] lemma addTransGadget_len : (addTransGadget (ι := ι) (G := G) (W := W)).len = 2 := rfl

/-- **The add-into gadget on the blank sector** is exactly one additive query, under native
semantics. -/
theorem addGadget_run (a : ι → G) (ψ : QBasis ι G W → ℂ) :
    (addGadget (ι := ι) (G := G) (W := W)).run a *ᵥ crossEmbed none ψ
      = crossEmbed none (addOracleMat a *ᵥ ψ) := by
  have hrun : (addGadget (ι := ι) (G := G) (W := W)).run a
      = 1 * (oracleMat a * (addIntoMat * (oracleMat a * 1))) := rfl
  rw [hrun, Matrix.one_mul, Matrix.mul_one]
  funext p
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, oracleMat_mulVec_apply,
    addIntoMat_mulVec_apply, oracleMat_mulVec_apply]
  obtain ⟨idx, s, t, w⟩ := p
  rcases idx with _ | i
  · rcases s with _ | v
    · simp [subIntoMap, addOracleMat_mulVec_apply, addOracleMap]
    · simp [subIntoMap]
  · rcases s with _ | v
    · -- blank native register: the simulated additive query
      simp [subIntoMap, addOracleMat_mulVec_apply, addOracleMap, sub_eq_add_neg]
    · -- dirty native register: stays dirty, both sides vanish
      by_cases hv : v = a i
      · subst hv
        simp [subIntoMap]
      · simp [subIntoMap, Equiv.swap_apply_def, hv]

/-- **The swap gadget on the clean sector** is exactly one native query, under additive
semantics. -/
theorem addTransGadget_addRun (a : ι → G) (ψ : QBasis ι G W → ℂ) :
    (addTransGadget (ι := ι) (G := G) (W := W)).addRun a *ᵥ crossEmbed (some 0) ψ
      = crossEmbed (some 0) (oracleMat a *ᵥ ψ) := by
  have hrun : (addTransGadget (ι := ι) (G := G) (W := W)).addRun a
      = 1 * (addOracleMat a * ((addNegMat * addCtrlSwapMat) * (addOracleMat a * 1))) := rfl
  rw [hrun, Matrix.one_mul, Matrix.mul_one]
  funext p
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    addOracleMat_mulVec_apply, addNegMat_mulVec_apply, addCtrlSwapMat_mulVec_apply,
    addOracleMat_mulVec_apply]
  obtain ⟨idx, s, t, w⟩ := p
  rcases idx with _ | i
  · rcases s with _ | c
    · simp [addOracleMap, addNegMap, addCtrlSwapMap]
    · simp [addOracleMap, addNegMap, addCtrlSwapMap]
  · rcases s with _ | c
    · -- blank additive register: both sides vanish
      simp [addOracleMap, addNegMap, addCtrlSwapMap]
    · by_cases hc : c = 0
      · -- clean register, active index: the simulated transposition
        subst hc
        simp [addOracleMap, addNegMap, addCtrlSwapMap]
      · -- dirty register: the register ends at `−c ≠ 0`, both sides vanish
        simp [addOracleMap, addNegMap, addCtrlSwapMap, hc]

/-! ## The compilers -/

/-- Compile the first `t` additive queries of a schedule into the native model: cross-lifted
steps, one `addGadget` per query. -/
def simAddUpto (R : QRoutine ι G W) : ℕ → QRoutine ι G (Option G × W)
  | 0 => QRoutine.ofUnitary (crossLift G (R.step 0))
      (crossLift_mem_unitaryGroup (R.step_unitary 0))
  | t + 1 => (simAddUpto R t).comp (addGadget.comp
      (QRoutine.ofUnitary (crossLift G (R.step (t + 1)))
        (crossLift_mem_unitaryGroup (R.step_unitary (t + 1)))))

@[simp] lemma simAddUpto_len (R : QRoutine ι G W) (t : ℕ) :
    (simAddUpto R t).len = 2 * t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change ((simAddUpto R t).comp _).len = _
      rw [QRoutine.comp_len, QRoutine.comp_len, ih, addGadget_len, QRoutine.ofUnitary_len]
      omega

theorem simAddUpto_run (R : QRoutine ι G W) (a : ι → G) (t : ℕ) (ψ : QBasis ι G W → ℂ) :
    (simAddUpto R t).run a *ᵥ crossEmbed none ψ
      = crossEmbed none (R.runWith (addOracleMat a) t *ᵥ ψ) := by
  induction t with
  | zero =>
      change (QRoutine.ofUnitary _ _).run a *ᵥ _ = _
      rw [QRoutine.ofUnitary_run, crossLift_mulVec_embed]
      rfl
  | succ t ih =>
      have hrun : (simAddUpto R (t + 1)).run a
          = crossLift G (R.step (t + 1)) * (addGadget.run a * (simAddUpto R t).run a) := by
        change ((simAddUpto R t).comp _).run a = _
        rw [QRoutine.comp_run, QRoutine.comp_run, QRoutine.ofUnitary_run, Matrix.mul_assoc]
      rw [hrun, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih, addGadget_run,
        crossLift_mulVec_embed, QRoutine.runWith_succ, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec]

/-- **The compiled additive schedule**: `2·R.len` native queries. -/
def simAdd (R : QRoutine ι G W) : QRoutine ι G (Option G × W) :=
  simAddUpto R R.len

@[simp] lemma simAdd_len (R : QRoutine ι G W) : (simAdd R).len = 2 * R.len :=
  simAddUpto_len R R.len

theorem simAdd_run (R : QRoutine ι G W) (a : ι → G) (ψ : QBasis ι G W → ℂ) :
    (simAdd R).run a *ᵥ crossEmbed none ψ = crossEmbed none (R.addRun a *ᵥ ψ) :=
  simAddUpto_run R a R.len ψ

/-- Compile the first `t` native queries of a schedule into the additive model: cross-lifted
steps, one `addTransGadget` per query. -/
def simTransAddUpto (R : QRoutine ι G W) : ℕ → QRoutine ι G (Option G × W)
  | 0 => QRoutine.ofUnitary (crossLift G (R.step 0))
      (crossLift_mem_unitaryGroup (R.step_unitary 0))
  | t + 1 => (simTransAddUpto R t).comp (addTransGadget.comp
      (QRoutine.ofUnitary (crossLift G (R.step (t + 1)))
        (crossLift_mem_unitaryGroup (R.step_unitary (t + 1)))))

@[simp] lemma simTransAddUpto_len (R : QRoutine ι G W) (t : ℕ) :
    (simTransAddUpto R t).len = 2 * t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change ((simTransAddUpto R t).comp _).len = _
      rw [QRoutine.comp_len, QRoutine.comp_len, ih, addTransGadget_len, QRoutine.ofUnitary_len]
      omega

theorem simTransAddUpto_addRun (R : QRoutine ι G W) (a : ι → G) (t : ℕ)
    (ψ : QBasis ι G W → ℂ) :
    (simTransAddUpto R t).addRun a *ᵥ crossEmbed (some 0) ψ
      = crossEmbed (some 0) (R.runUpto a t *ᵥ ψ) := by
  induction t with
  | zero =>
      change (QRoutine.ofUnitary _ _).addRun a *ᵥ _ = _
      rw [QRoutine.ofUnitary_addRun, crossLift_mulVec_embed]
      rfl
  | succ t ih =>
      have hrun : (simTransAddUpto R (t + 1)).addRun a
          = crossLift G (R.step (t + 1))
              * (addTransGadget.addRun a * (simTransAddUpto R t).addRun a) := by
        change ((simTransAddUpto R t).comp _).addRun a = _
        rw [QRoutine.comp_addRun, QRoutine.comp_addRun, QRoutine.ofUnitary_addRun,
          Matrix.mul_assoc]
      rw [hrun, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih, addTransGadget_addRun,
        crossLift_mulVec_embed, QRoutine.runUpto_succ, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec]

/-- **The compiled native schedule**: `2·R.len` additive queries. -/
def simTransAdd (R : QRoutine ι G W) : QRoutine ι G (Option G × W) :=
  simTransAddUpto R R.len

@[simp] lemma simTransAdd_len (R : QRoutine ι G W) : (simTransAdd R).len = 2 * R.len :=
  simTransAddUpto_len R R.len

theorem simTransAdd_addRun (R : QRoutine ι G W) (a : ι → G) (ψ : QBasis ι G W → ℂ) :
    (simTransAdd R).addRun a *ᵥ crossEmbed (some 0) ψ = crossEmbed (some 0) (R.run a *ᵥ ψ) :=
  simTransAddUpto_addRun R a R.len ψ

/-! ## The simulating algorithms -/

section Algorithms

variable {O : Type}

/-- The additive state of a packaged routine is its parametric run. -/
private lemma addState_toAlg (R : QRoutine ι G W) (init : QBasis ι G W → ℂ)
    (hinit : IsQState init) (r : QBasis ι G W → O) (a : ι → G) (t : ℕ) :
    addState (R.toAlg init hinit r) a t = R.runWith (addOracleMat a) t *ᵥ init :=
  addState_eq_runWith (R.toAlg init hinit r) R.len a t

/-- Valid-output mass through the moved register. -/
private lemma goodProb_crossStrip_crossEmbed (r : QBasis ι G W → O) (P : O → Prop)
    [DecidablePred P] (v : Option G) (χ : QBasis ι G W → ℂ) :
    goodProb (crossStrip G r) P (crossEmbed v χ) = goodProb r P χ :=
  qProb_crossStrip_crossEmbed (fun h => decide (P (r h))) v true χ

/-- **The native simulation of an additive-model algorithm** for `q` queries: the compiled
schedule, started on `A`'s initial state with the physical answer register blank, read through
`A`'s readout on the logical registers. It makes `2q` native queries. -/
def simAddAlg (A : QAlg ι G O W) (q : ℕ) : QAlg ι G O (Option G × W) :=
  (simAdd (QRoutine.mk q A.step A.step_unitary)).toAlg (crossEmbed none A.init)
    (isQState_crossEmbed none A.init_isQState) (crossStrip G A.readout)

/-- **The additive simulation of a native algorithm** for `q` queries: the compiled schedule,
started on `A`'s initial state with the physical answer register at `some 0`. It makes `2q`
additive queries. -/
def simTransAddAlg (A : QAlg ι G O W) (q : ℕ) : QAlg ι G O (Option G × W) :=
  (simTransAdd (QRoutine.mk q A.step A.step_unitary)).toAlg (crossEmbed (some 0) A.init)
    (isQState_crossEmbed (some 0) A.init_isQState) (crossStrip G A.readout)

/-- **The native simulation reproduces the additive state**: after `2q` native queries, the state
of `simAddAlg A q` is that of `A` after `q` additive queries, with the physical register blank. -/
theorem simAddAlg_state (A : QAlg ι G O W) (q : ℕ) (a : ι → G) :
    (simAddAlg A q).state a (2 * q) = crossEmbed none (addState A a q) := by
  classical
  have hlen : (simAdd (QRoutine.mk q A.step A.step_unitary)).len = 2 * q := by
    rw [simAdd_len]
  rw [simAddAlg, ← hlen, QRoutine.toAlg_state_len, addState_eq_runWith A q]
  exact simAdd_run (QRoutine.mk q A.step A.step_unitary) a A.init

/-- **The native simulation has the same output distribution.** -/
theorem prob_simAddAlg [DecidableEq O] (A : QAlg ι G O W) (q : ℕ) (a : ι → G) (o : O) :
    (simAddAlg A q).prob a (2 * q) o = qProb A.readout (addState A a q) o := by
  rw [QAlg.prob, simAddAlg_state]
  exact qProb_crossStrip_crossEmbed A.readout none o _

/-- **The additive simulation reproduces the native state**: after `2q` additive queries, the
state of `simTransAddAlg A q` is that of `A` after `q` native queries, with the physical register
at `some 0`. -/
theorem addState_simTransAddAlg (A : QAlg ι G O W) (q : ℕ) (a : ι → G) :
    addState (simTransAddAlg A q) a (2 * q) = crossEmbed (some 0) (A.state a q) := by
  classical
  have hlen : (simTransAdd (QRoutine.mk q A.step A.step_unitary)).len = 2 * q := by
    rw [simTransAdd_len]
  rw [simTransAddAlg, ← hlen, addState_toAlg, state_eq_runUpto2 A q]
  exact simTransAdd_addRun (QRoutine.mk q A.step A.step_unitary) a A.init

/-- **The additive simulation has the same output distribution.** -/
theorem prob_simTransAddAlg [DecidableEq O] (A : QAlg ι G O W) (q : ℕ) (a : ι → G) (o : O) :
    qProb (simTransAddAlg A q).readout (addState (simTransAddAlg A q) a (2 * q)) o
      = A.prob a q o := by
  rw [addState_simTransAddAlg, QAlg.prob]
  exact qProb_crossStrip_crossEmbed A.readout (some 0) o _

variable {X : Type}

/-- **Relations transfer to the native model**: the native simulation succeeds with exactly the
additive algorithm's probability, for every relation. -/
theorem successProbOn_simAddAlg (A : QAlg ι G O W) (q : ℕ) (read : X → ι → G)
    (Good : X → O → Prop) [∀ x, DecidablePred (Good x)] (x : X) :
    successProbOn (simAddAlg A q) (2 * q) read Good x = addSuccessProbOn A q read Good x := by
  rw [successProbOn, addSuccessProbOn, simAddAlg_state]
  exact goodProb_crossStrip_crossEmbed A.readout (Good x) none _

/-- **Relations transfer to the additive model.** -/
theorem addSuccessProbOn_simTransAddAlg (A : QAlg ι G O W) (q : ℕ) (read : X → ι → G)
    (Good : X → O → Prop) [∀ x, DecidablePred (Good x)] (x : X) :
    addSuccessProbOn (simTransAddAlg A q) (2 * q) read Good x = successProbOn A q read Good x := by
  rw [addSuccessProbOn, successProbOn, addState_simTransAddAlg]
  exact goodProb_crossStrip_crossEmbed A.readout (Good x) (some 0) _

/-- **An additive-model algorithm gives a native one with twice the queries**, for functions. -/
theorem AddComputesWithErrorOn.simAddAlg [DecidableEq O] {A : QAlg ι G O W} {q : ℕ}
    {read : X → ι → G} {f : X → O} {ε : ℝ} (h : AddComputesWithErrorOn A q read f ε) :
    ComputesWithErrorOn (simAddAlg A q) (2 * q) read f ε := by
  intro x
  rw [prob_simAddAlg]
  exact h x

/-- **An additive-model algorithm gives a native one with twice the queries**, for relations. -/
theorem AddSolvesWithErrorOn.simAddAlg {A : QAlg ι G O W} {q : ℕ} {read : X → ι → G}
    {Good : X → O → Prop} [∀ x, DecidablePred (Good x)] {ε : ℝ}
    (h : AddSolvesWithErrorOn A q read Good ε) :
    SolvesWithErrorOn (simAddAlg A q) (2 * q) read Good ε := by
  intro x
  rw [successProbOn_simAddAlg]
  exact h x

/-- **A native algorithm gives an additive-model one with twice the queries**, for functions. -/
theorem ComputesWithErrorOn.simTransAddAlg [DecidableEq O] {A : QAlg ι G O W} {q : ℕ}
    {read : X → ι → G} {f : X → O} {ε : ℝ} (h : ComputesWithErrorOn A q read f ε) :
    AddComputesWithErrorOn (simTransAddAlg A q) (2 * q) read f ε := by
  intro x
  rw [prob_simTransAddAlg]
  exact h x

/-- **A native algorithm gives an additive-model one with twice the queries**, for relations. -/
theorem SolvesWithErrorOn.simTransAddAlg {A : QAlg ι G O W} {q : ℕ} {read : X → ι → G}
    {Good : X → O → Prop} [∀ x, DecidablePred (Good x)] {ε : ℝ}
    (h : SolvesWithErrorOn A q read Good ε) :
    AddSolvesWithErrorOn (simTransAddAlg A q) (2 * q) read Good ε := by
  intro x
  rw [addSuccessProbOn_simTransAddAlg]
  exact h x

end Algorithms

/-! ## The `QueryCounts` translations and the complexity comparison -/

section Translations

variable {O : Type} [DecidableEq O] {X : Type}

/-- **The native model simulates the additive model** at a factor of two. -/
theorem two_mul_mem_queryCounts_of_add {read : X → ι → G} {f : X → O} {ε : ℝ} {q : ℕ}
    (hq : q ∈ AddQueryCounts read f ε) : 2 * q ∈ QueryCounts read f ε := by
  obtain ⟨W', _, _, A, hA⟩ := hq
  -- (`mem_queryCounts` carries a `Fintype X` section instance; the set is unfolded directly)
  exact ⟨Option G × W', inferInstance, inferInstance, _, hA.simAddAlg⟩

/-- **The additive model simulates the native model** at a factor of two. -/
theorem two_mul_mem_addQueryCounts_of_std {read : X → ι → G} {f : X → O} {ε : ℝ} {q : ℕ}
    (hq : q ∈ QueryCounts read f ε) : 2 * q ∈ AddQueryCounts read f ε := by
  obtain ⟨W', _, _, A, hA⟩ := hq
  exact mem_addQueryCounts hA.simTransAddAlg

/-- **Solvable problems are solvable in the additive model**: if the reading determines the
value, some additive-model algorithm computes it with error `ε ≥ 0`. -/
theorem addQueryCounts_nonempty [Fintype X] [Nonempty O] {read : X → ι → G} {f : X → O} {ε : ℝ}
    (hdet : ∀ x y, read x = read y → f x = f y) (hε0 : 0 ≤ ε) :
    (AddQueryCounts read f ε).Nonempty := by
  obtain ⟨q, hq⟩ := queryCounts_nonempty hdet hε0
  exact ⟨2 * q, two_mul_mem_addQueryCounts_of_std hq⟩

/-- **Model equivalence, one direction**: native complexity is at most twice the additive
complexity. No hypothesis is needed: by the two translations the achievable sets are empty
together, and then both infima are `0`. -/
theorem qQueryOn_le_two_mul_addQQueryOn {read : X → ι → G} {f : X → O} {ε : ℝ} :
    qQueryOn read f ε ≤ 2 * addQQueryOn read f ε := by
  rcases (AddQueryCounts read f ε).eq_empty_or_nonempty with h | h
  · have hstd : QueryCounts read f ε = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun q hq => ?_
      have h2 := two_mul_mem_addQueryCounts_of_std hq
      rw [h] at h2
      exact h2
    rw [qQueryOn, hstd, Nat.sInf_empty]
    exact Nat.zero_le _
  · exact Nat.sInf_le (two_mul_mem_queryCounts_of_add (Nat.sInf_mem h))

/-- **Model equivalence, the other direction**: additive complexity is at most twice the native
complexity, again with no hypothesis. -/
theorem addQQueryOn_le_two_mul_qQueryOn {read : X → ι → G} {f : X → O} {ε : ℝ} :
    addQQueryOn read f ε ≤ 2 * qQueryOn read f ε := by
  rcases (QueryCounts read f ε).eq_empty_or_nonempty with h | h
  · have hadd : AddQueryCounts read f ε = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun q hq => ?_
      have h2 := two_mul_mem_queryCounts_of_add hq
      rw [h] at h2
      exact h2
    rw [addQQueryOn, hadd, Nat.sInf_empty]
    exact Nat.zero_le _
  · exact Nat.sInf_le (two_mul_mem_addQueryCounts_of_std (Nat.sInf_mem h))

end Translations

end QuantumQueryComplexity
