import QuantumQueryComplexity.Quantum.OneHot
import QuantumQueryComplexity.Quantum.Simulation
import QuantumQueryComplexity.Quantum.Relabel
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The one-hot XOR model and the native model agree within a factor of two

The native transposition oracle acts on the answer register `Option σ`; the
canonical one-hot XOR oracle of `OneHot.lean` acts on `Option (Hot σ)`.  The
two models therefore live on **different bases**, and simulating one in the
other means carrying the foreign answer register in the workspace.  The
comparison here is direct — it does *not* pass through the Boolean XOR model
of `Simulation.lean` and `AlphabetSimulation.lean`, which would inflate the
constant to four — and both directions cost exactly two physical queries per
simulated query:

* **One-hot simulates transposition.**  The native algorithm's answer
  register `Option σ` moves into the workspace; the physical one-hot register
  is kept clean at `some hotZero`.  One native query becomes

      query, controlled swap, query:

  the first query writes `hotCode (x i)` into the clean register, a fixed
  permutation decodes it and swaps `⊥ ↔ some (x i)` in the logical register,
  and the second query erases the code again.

* **Transposition simulates one-hot.**  The one-hot algorithm's register
  `Option (Hot σ)` moves into the workspace; the physical native register is
  kept blank.  One one-hot query becomes

      query, XOR-into, query:

  the first query writes `x i` into the blank register, a fixed permutation
  XORs `hotCode (x i)` into the logical register, and the second query erases
  the letter.

The register move is the equivalence `regSwap`; `crossLift` and `crossEmbed`
are `liftReg` and `embedReg` transported along it, so unitarity, the action on
the encoded sector, and the norm identities are inherited from `Blocks.lean`
rather than re-proved.  The compilers and the `QueryCounts` translations then
follow `Simulation.lean` line by line.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-! ## The run in the one-hot model, packaged -/

namespace QRoutine

/-- The operator implemented by `R` against the one-hot XOR oracle. -/
def oneHotRun (R : QRoutine ι (Hot σ) W) (a : ι → σ) :
    Matrix (QBasis ι (Hot σ) W) (QBasis ι (Hot σ) W) ℂ :=
  R.runWith (oneHotOracleMat a) R.len

theorem comp_oneHotRun (R S : QRoutine ι (Hot σ) W) (a : ι → σ) :
    (R.comp S).oneHotRun a = S.oneHotRun a * R.oneHotRun a :=
  comp_runWith_full (oneHotOracleMat a) R S

@[simp] lemma ofUnitary_oneHotRun
    (U : Matrix (QBasis ι (Hot σ) W) (QBasis ι (Hot σ) W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι (Hot σ) W) ℂ) (a : ι → σ) :
    (ofUnitary U hU).oneHotRun a = U := rfl

end QRoutine

/-! ## Moving an answer register into the workspace

`regSwap` exchanges the answer register with the first workspace register; it
relates the basis of a `β`-answer machine carrying an `α`-register in its
workspace to that of an `α`-answer machine carrying a `β`-register. -/

section Cross

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Exchange the answer register with the first workspace register. -/
def regSwap : QBasis ι β (Option α × W) ≃ QBasis ι α (Option β × W) where
  toFun p := (p.1, p.2.2.1, (p.2.1, p.2.2.2))
  invFun p := (p.1, p.2.2.1, (p.2.1, p.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma regSwap_apply (idx : Option ι) (s : Option β) (t : Option α) (w : W) :
    regSwap ((idx, s, (t, w)) : QBasis ι β (Option α × W)) = (idx, t, (s, w)) := rfl

/-- **An operator on an `α`-answer machine, acting on a `β`-answer machine**
whose workspace carries the `α`-register: `liftReg` transported along
`regSwap`. -/
def crossLift (β : Type) [Fintype β] [DecidableEq β]
    (U : Matrix (QBasis ι α W) (QBasis ι α W) ℂ) :
    Matrix (QBasis ι β (Option α × W)) (QBasis ι β (Option α × W)) ℂ :=
  (liftReg (Option β) U).submatrix regSwap regSwap

lemma crossLift_mem_unitaryGroup {U : Matrix (QBasis ι α W) (QBasis ι α W) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι α W) ℂ) :
    crossLift β U ∈ Matrix.unitaryGroup (QBasis ι β (Option α × W)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, crossLift,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    ← Matrix.star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff'.mp (liftReg_mem_unitaryGroup hU),
    Matrix.submatrix_one_equiv]

/-- **The encoded sector**: `ψ`, with its answer register moved into the
workspace and the physical answer register holding `v`. -/
def crossEmbed (v : Option β) (ψ : QBasis ι α W → ℂ) :
    QBasis ι β (Option α × W) → ℂ :=
  fun p => embedReg v ψ (regSwap p)

@[simp] lemma crossEmbed_apply (v : Option β) (ψ : QBasis ι α W → ℂ)
    (idx : Option ι) (s : Option β) (t : Option α) (w : W) :
    crossEmbed v ψ ((idx, s, (t, w)) : QBasis ι β (Option α × W))
      = if s = v then ψ (idx, t, w) else 0 := rfl

/-- **The action on the encoded sector.** -/
lemma crossLift_mulVec_embed (U : Matrix (QBasis ι α W) (QBasis ι α W) ℂ)
    (v : Option β) (ψ : QBasis ι α W → ℂ) :
    crossLift β U *ᵥ crossEmbed v ψ = crossEmbed v (U *ᵥ ψ) := by
  rw [crossLift, Matrix.submatrix_mulVec_equiv]
  have h : crossEmbed v ψ ∘ regSwap.symm = embedReg v ψ := by
    funext p
    simp [crossEmbed]
  rw [h, liftReg_mulVec_embed]
  rfl

/-- The norm identity, inherited from `embedReg` along the register move
(`qNormSq_comp_equiv` is `Relabel.lean`'s generic transport). -/
lemma qNormSq_crossEmbed (v : Option β) (ψ : QBasis ι α W → ℂ) :
    qNormSq (crossEmbed v ψ) = qNormSq ψ := by
  rw [← qNormSq_embedReg v ψ]
  exact qNormSq_comp_equiv regSwap (embedReg v ψ)

lemma isQState_crossEmbed (v : Option β) {ψ : QBasis ι α W → ℂ}
    (hψ : IsQState ψ) : IsQState (crossEmbed v ψ) := by
  rw [IsQState, qNormSq_crossEmbed]
  exact hψ

variable {O : Type} [DecidableEq O]

/-- Read the logical registers, ignoring the physical answer register. -/
def crossStrip (β : Type) [Fintype β] [DecidableEq β] (r : QBasis ι α W → O) :
    QBasis ι β (Option α × W) → O :=
  fun p => stripReadout r (regSwap p)

/-- **Measuring through the moved register changes nothing.** -/
lemma qProb_crossStrip_crossEmbed (r : QBasis ι α W → O) (v : Option β) (o : O)
    (χ : QBasis ι α W → ℂ) :
    qProb (crossStrip β r) (crossEmbed v χ) o = qProb r χ o := by
  rw [← qProb_stripReadout_embedReg r v o χ]
  exact qProb_comp_equiv regSwap (stripReadout r) (embedReg v χ) o

end Cross

/-! ## Decoding a one-hot register -/

/-- Decode a one-hot register: the letter it codes, if any. -/
noncomputable def decodeHot (h : Hot σ) : Option σ :=
  if hx : ∃ b, hotCode b = h then some hx.choose else none

lemma decodeHot_hotCode (b : σ) : decodeHot (hotCode b) = some b := by
  have hx : ∃ c, hotCode c = hotCode b := ⟨b, rfl⟩
  rw [decodeHot, dif_pos hx]
  exact congrArg some (hotCode_injective hx.choose_spec)

/-- The transposition `⊥ ↔ some b` of the logical register, controlled on the
one-hot register coding `b`; the identity when it codes nothing. -/
noncomputable def hotSwap (h : Hot σ) : Equiv.Perm (Option σ) :=
  match decodeHot h with
  | some b => Equiv.swap none (some b)
  | none => 1

lemma hotSwap_hotCode (b : σ) : hotSwap (hotCode b) = Equiv.swap none (some b) := by
  simp only [hotSwap, decodeHot_hotCode]

lemma hotSwap_hotSwap (h : Hot σ) (t : Option σ) : hotSwap h (hotSwap h t) = t := by
  simp only [hotSwap]
  rcases decodeHot h with _ | b <;> simp

/-! ## The gadget permutations -/

/-- On an active index with a one-hot answer `some h`: decode `h` and swap
`⊥ ↔ some b` in the logical register.  Controlled on the index being active
and the register not blank, so the idle and blank sectors are exactly
fixed. -/
noncomputable def ctrlHotSwapMap :
    QBasis ι (Hot σ) (Option σ × W) → QBasis ι (Hot σ) (Option σ × W)
  | (some i, some h, (t, w)) => (some i, some h, (hotSwap h t, w))
  | p => p

@[simp] lemma ctrlHotSwapMap_active (i : ι) (h : Hot σ) (t : Option σ) (w : W) :
    ctrlHotSwapMap ((some i, some h, (t, w)) : QBasis ι (Hot σ) (Option σ × W))
      = (some i, some h, (hotSwap h t, w)) := rfl

@[simp] lemma ctrlHotSwapMap_idle (s : Option (Hot σ)) (t : Option σ) (w : W) :
    ctrlHotSwapMap ((none, s, (t, w)) : QBasis ι (Hot σ) (Option σ × W))
      = (none, s, (t, w)) := by
  cases s <;> rfl

@[simp] lemma ctrlHotSwapMap_blank (i : ι) (t : Option σ) (w : W) :
    ctrlHotSwapMap ((some i, none, (t, w)) : QBasis ι (Hot σ) (Option σ × W))
      = (some i, none, (t, w)) := rfl

lemma ctrlHotSwapMap_involutive :
    Function.Involutive (ctrlHotSwapMap (ι := ι) (σ := σ) (W := W)) := by
  rintro ⟨(_ | i), (_ | h), t, w⟩ <;> simp [hotSwap_hotSwap]

/-- XOR the one-hot code of the native answer into the logical one-hot
register; blank sectors on either side are fixed. -/
def hotXorIntoMap :
    QBasis ι σ (Option (Hot σ) × W) → QBasis ι σ (Option (Hot σ) × W)
  | (idx, some b, (g, w)) => (idx, some b, (optHotXor g (hotCode b), w))
  | p => p

@[simp] lemma hotXorIntoMap_some (idx : Option ι) (b : σ) (g : Option (Hot σ))
    (w : W) :
    hotXorIntoMap ((idx, some b, (g, w)) : QBasis ι σ (Option (Hot σ) × W))
      = (idx, some b, (optHotXor g (hotCode b), w)) := rfl

@[simp] lemma hotXorIntoMap_none (idx : Option ι) (g : Option (Hot σ)) (w : W) :
    hotXorIntoMap ((idx, none, (g, w)) : QBasis ι σ (Option (Hot σ) × W))
      = (idx, none, (g, w)) := rfl

lemma hotXorIntoMap_involutive :
    Function.Involutive (hotXorIntoMap (ι := ι) (σ := σ) (W := W)) := by
  rintro ⟨idx, (_ | b), g, w⟩ <;> simp [optHotXor_optHotXor]

/-! ## The gadget unitaries -/

/-- The controlled decode-and-swap unitary. -/
noncomputable def ctrlHotSwapMat : Matrix (QBasis ι (Hot σ) (Option σ × W))
    (QBasis ι (Hot σ) (Option σ × W)) ℂ :=
  qPerm (Function.Involutive.toPerm _ ctrlHotSwapMap_involutive)

lemma ctrlHotSwapMat_mem_unitaryGroup :
    ctrlHotSwapMat (ι := ι) (σ := σ) (W := W)
      ∈ Matrix.unitaryGroup (QBasis ι (Hot σ) (Option σ × W)) ℂ :=
  qPerm_mem_unitaryGroup _

lemma ctrlHotSwapMat_mulVec_apply (ψ : QBasis ι (Hot σ) (Option σ × W) → ℂ)
    (p : QBasis ι (Hot σ) (Option σ × W)) :
    (ctrlHotSwapMat *ᵥ ψ) p = ψ (ctrlHotSwapMap p) := by
  rw [ctrlHotSwapMat, qPerm_mulVec_apply]
  rfl

/-- The XOR-the-code-into-the-register unitary. -/
def hotXorIntoMat : Matrix (QBasis ι σ (Option (Hot σ) × W))
    (QBasis ι σ (Option (Hot σ) × W)) ℂ :=
  qPerm (Function.Involutive.toPerm _ hotXorIntoMap_involutive)

lemma hotXorIntoMat_mem_unitaryGroup :
    hotXorIntoMat (ι := ι) (σ := σ) (W := W)
      ∈ Matrix.unitaryGroup (QBasis ι σ (Option (Hot σ) × W)) ℂ :=
  qPerm_mem_unitaryGroup _

lemma hotXorIntoMat_mulVec_apply (ψ : QBasis ι σ (Option (Hot σ) × W) → ℂ)
    (p : QBasis ι σ (Option (Hot σ) × W)) :
    (hotXorIntoMat *ᵥ ψ) p = ψ (hotXorIntoMap p) := by
  rw [hotXorIntoMat, qPerm_mulVec_apply]
  rfl

/-! ## The two gadgets -/

/-- **One-hot simulates transposition**: two physical one-hot queries around
the controlled decode-and-swap. -/
noncomputable def transHotGadget : QRoutine ι (Hot σ) (Option σ × W) where
  len := 2
  step := fun t => if t = 1 then ctrlHotSwapMat else 1
  step_unitary := by
    intro t
    split_ifs
    · exact ctrlHotSwapMat_mem_unitaryGroup
    · exact one_mem_qUnitary

@[simp] lemma transHotGadget_len :
    (transHotGadget (ι := ι) (σ := σ) (W := W)).len = 2 := rfl

/-- **Transposition simulates one-hot**: two physical native queries around
the XOR-into. -/
def hotXorGadget : QRoutine ι σ (Option (Hot σ) × W) where
  len := 2
  step := fun t => if t = 1 then hotXorIntoMat else 1
  step_unitary := by
    intro t
    split_ifs
    · exact hotXorIntoMat_mem_unitaryGroup
    · exact one_mem_qUnitary

@[simp] lemma hotXorGadget_len :
    (hotXorGadget (ι := ι) (σ := σ) (W := W)).len = 2 := rfl

/-- **The transposition gadget's action on the clean sector** is exactly one
native query, under one-hot semantics. -/
theorem transHotGadget_oneHotRun (a : ι → σ) (ψ : QBasis ι σ W → ℂ) :
    (transHotGadget (ι := ι) (σ := σ) (W := W)).oneHotRun a
        *ᵥ crossEmbed (some hotZero) ψ
      = crossEmbed (some hotZero) (oracleMat a *ᵥ ψ) := by
  have hrun : (transHotGadget (ι := ι) (σ := σ) (W := W)).oneHotRun a
      = 1 * (oneHotOracleMat a * (ctrlHotSwapMat * (oneHotOracleMat a * 1))) :=
    rfl
  rw [hrun, Matrix.one_mul, Matrix.mul_one]
  funext p
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    oneHotOracleMat_mulVec_apply, ctrlHotSwapMat_mulVec_apply,
    oneHotOracleMat_mulVec_apply]
  obtain ⟨idx, s, t, w⟩ := p
  rcases idx with _ | i
  · rcases s with _ | h <;> simp
  · rcases s with _ | h
    · -- blank one-hot register: the oracle fixes it, both sides vanish
      simp
    · by_cases hh : h = hotZero
      · -- clean register, active index: the simulated transposition
        subst hh
        simp [hotXor_self, hotSwap_hotCode]
      · -- dirty register: stays dirty, both sides vanish
        simp [hotXor_hotXor, hh]

/-- **The one-hot gadget's action on the blank sector** is exactly one
one-hot query, under native semantics. -/
theorem hotXorGadget_run (a : ι → σ) (ψ : QBasis ι (Hot σ) W → ℂ) :
    (hotXorGadget (ι := ι) (σ := σ) (W := W)).run a *ᵥ crossEmbed none ψ
      = crossEmbed none (oneHotOracleMat a *ᵥ ψ) := by
  have hrun : (hotXorGadget (ι := ι) (σ := σ) (W := W)).run a
      = 1 * (oracleMat a * (hotXorIntoMat * (oracleMat a * 1))) := rfl
  rw [hrun, Matrix.one_mul, Matrix.mul_one]
  funext p
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    oracleMat_mulVec_apply, hotXorIntoMat_mulVec_apply, oracleMat_mulVec_apply]
  obtain ⟨idx, s, g, w⟩ := p
  rcases idx with _ | i
  · rcases s with _ | b <;> simp [oneHotOracleMat_mulVec_apply]
  · rcases s with _ | b
    · -- blank native register: the simulated one-hot query
      simp [oneHotOracleMat_mulVec_apply]
    · -- dirty native register: stays dirty, both sides vanish
      by_cases hb : b = a i
      · subst hb
        simp
      · simp [Equiv.swap_apply_def, hb]

/-! ## The compilers -/

/-- Compile the first `t` native queries of a schedule into the one-hot
model: cross-lifted steps, one `transHotGadget` per query. -/
noncomputable def simTransHotUpto (R : QRoutine ι σ W) :
    ℕ → QRoutine ι (Hot σ) (Option σ × W)
  | 0 => QRoutine.ofUnitary (crossLift (Hot σ) (R.step 0))
      (crossLift_mem_unitaryGroup (R.step_unitary 0))
  | t + 1 => (simTransHotUpto R t).comp (transHotGadget.comp
      (QRoutine.ofUnitary (crossLift (Hot σ) (R.step (t + 1)))
        (crossLift_mem_unitaryGroup (R.step_unitary (t + 1)))))

@[simp] lemma simTransHotUpto_len (R : QRoutine ι σ W) (t : ℕ) :
    (simTransHotUpto R t).len = 2 * t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change ((simTransHotUpto R t).comp _).len = _
      rw [QRoutine.comp_len, QRoutine.comp_len, ih, transHotGadget_len,
        QRoutine.ofUnitary_len]
      omega

theorem simTransHotUpto_oneHotRun (R : QRoutine ι σ W) (a : ι → σ) (t : ℕ)
    (ψ : QBasis ι σ W → ℂ) :
    (simTransHotUpto R t).oneHotRun a *ᵥ crossEmbed (some hotZero) ψ
      = crossEmbed (some hotZero) (R.runUpto a t *ᵥ ψ) := by
  induction t with
  | zero =>
      change (QRoutine.ofUnitary _ _).oneHotRun a *ᵥ _ = _
      rw [QRoutine.ofUnitary_oneHotRun, crossLift_mulVec_embed]
      rfl
  | succ t ih =>
      have hrun : (simTransHotUpto R (t + 1)).oneHotRun a
          = crossLift (Hot σ) (R.step (t + 1))
              * (transHotGadget.oneHotRun a * (simTransHotUpto R t).oneHotRun a) := by
        change ((simTransHotUpto R t).comp _).oneHotRun a = _
        rw [QRoutine.comp_oneHotRun, QRoutine.comp_oneHotRun,
          QRoutine.ofUnitary_oneHotRun, Matrix.mul_assoc]
      rw [hrun, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
        transHotGadget_oneHotRun, crossLift_mulVec_embed, QRoutine.runUpto_succ,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- **The compiled native schedule**: `2·R.len` one-hot queries. -/
noncomputable def simTransHot (R : QRoutine ι σ W) :
    QRoutine ι (Hot σ) (Option σ × W) :=
  simTransHotUpto R R.len

@[simp] lemma simTransHot_len (R : QRoutine ι σ W) :
    (simTransHot R).len = 2 * R.len := simTransHotUpto_len R R.len

theorem simTransHot_oneHotRun (R : QRoutine ι σ W) (a : ι → σ)
    (ψ : QBasis ι σ W → ℂ) :
    (simTransHot R).oneHotRun a *ᵥ crossEmbed (some hotZero) ψ
      = crossEmbed (some hotZero) (R.run a *ᵥ ψ) :=
  simTransHotUpto_oneHotRun R a R.len ψ

/-- Compile the first `t` one-hot queries of a schedule into the native
model: cross-lifted steps, one `hotXorGadget` per query. -/
def simHotXorUpto (R : QRoutine ι (Hot σ) W) :
    ℕ → QRoutine ι σ (Option (Hot σ) × W)
  | 0 => QRoutine.ofUnitary (crossLift σ (R.step 0))
      (crossLift_mem_unitaryGroup (R.step_unitary 0))
  | t + 1 => (simHotXorUpto R t).comp (hotXorGadget.comp
      (QRoutine.ofUnitary (crossLift σ (R.step (t + 1)))
        (crossLift_mem_unitaryGroup (R.step_unitary (t + 1)))))

@[simp] lemma simHotXorUpto_len (R : QRoutine ι (Hot σ) W) (t : ℕ) :
    (simHotXorUpto R t).len = 2 * t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change ((simHotXorUpto R t).comp _).len = _
      rw [QRoutine.comp_len, QRoutine.comp_len, ih, hotXorGadget_len,
        QRoutine.ofUnitary_len]
      omega

theorem simHotXorUpto_run (R : QRoutine ι (Hot σ) W) (a : ι → σ) (t : ℕ)
    (ψ : QBasis ι (Hot σ) W → ℂ) :
    (simHotXorUpto R t).run a *ᵥ crossEmbed none ψ
      = crossEmbed none (R.runWith (oneHotOracleMat a) t *ᵥ ψ) := by
  induction t with
  | zero =>
      change (QRoutine.ofUnitary _ _).run a *ᵥ _ = _
      rw [QRoutine.ofUnitary_run, crossLift_mulVec_embed]
      rfl
  | succ t ih =>
      have hrun : (simHotXorUpto R (t + 1)).run a
          = crossLift σ (R.step (t + 1))
              * (hotXorGadget.run a * (simHotXorUpto R t).run a) := by
        change ((simHotXorUpto R t).comp _).run a = _
        rw [QRoutine.comp_run, QRoutine.comp_run, QRoutine.ofUnitary_run,
          Matrix.mul_assoc]
      rw [hrun, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
        hotXorGadget_run, crossLift_mulVec_embed, QRoutine.runWith_succ,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- **The compiled one-hot schedule**: `2·R.len` native queries. -/
def simHotXor (R : QRoutine ι (Hot σ) W) : QRoutine ι σ (Option (Hot σ) × W) :=
  simHotXorUpto R R.len

@[simp] lemma simHotXor_len (R : QRoutine ι (Hot σ) W) :
    (simHotXor R).len = 2 * R.len := simHotXorUpto_len R R.len

theorem simHotXor_run (R : QRoutine ι (Hot σ) W) (a : ι → σ)
    (ψ : QBasis ι (Hot σ) W → ℂ) :
    (simHotXor R).run a *ᵥ crossEmbed none ψ
      = crossEmbed none (R.runWith (oneHotOracleMat a) R.len *ᵥ ψ) :=
  simHotXorUpto_run R a R.len ψ

/-! ## The state bridge -/

section Bridges

variable {O : Type} [DecidableEq O]

/-- The one-hot state of a packaged routine is its parametric run. -/
lemma oneHotState_toAlg (R : QRoutine ι (Hot σ) W) (init : QBasis ι (Hot σ) W → ℂ)
    (hinit : IsQState init) (r : QBasis ι (Hot σ) W → O) (a : ι → σ) (t : ℕ) :
    oneHotState (R.toAlg init hinit r) a t
      = R.runWith (oneHotOracleMat a) t *ᵥ init := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [oneHotState_succ, ih, QRoutine.runWith_succ, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rfl

end Bridges

/-! ## The `QueryCounts` translations -/

section Translations

variable {O : Type} [DecidableEq O] {X : Type} [Fintype X]

/-- **The native model simulates the one-hot model** at a factor of two:
every achievable one-hot query count doubles into the native model. -/
theorem two_mul_mem_queryCounts_of_oneHot {read : X → ι → σ} {f : X → O}
    {ε : ℝ} {q : ℕ} (hq : q ∈ OneHotXorQueryCounts read f ε) :
    2 * q ∈ QueryCounts read f ε := by
  obtain ⟨W', _, _, A, hA⟩ := hq
  refine mem_queryCounts
    (A := (simHotXor (QRoutine.mk q A.step A.step_unitary)).toAlg
      (crossEmbed none A.init) (isQState_crossEmbed none A.init_isQState)
      (crossStrip σ A.readout)) ?_
  intro x
  have hlen : (simHotXor (QRoutine.mk q A.step A.step_unitary)).len = 2 * q := by
    rw [simHotXor_len]
  have hstate : ((simHotXor (QRoutine.mk q A.step A.step_unitary)).toAlg
        (crossEmbed none A.init) (isQState_crossEmbed none A.init_isQState)
        (crossStrip σ A.readout)).state (read x) (2 * q)
      = crossEmbed none (oneHotState A (read x) q) := by
    rw [← hlen, QRoutine.toAlg_state_len, simHotXor_run,
      ← oneHotState_eq_runWith A q]
  rw [QAlg.prob, hstate,
    show ((simHotXor (QRoutine.mk q A.step A.step_unitary)).toAlg
        (crossEmbed none A.init) (isQState_crossEmbed none A.init_isQState)
        (crossStrip σ A.readout)).readout = crossStrip σ A.readout from rfl,
    qProb_crossStrip_crossEmbed]
  exact hA x

/-- **The one-hot model simulates the native model** at a factor of two. -/
theorem two_mul_mem_oneHotXorQueryCounts_of_std {read : X → ι → σ} {f : X → O}
    {ε : ℝ} {q : ℕ} (hq : q ∈ QueryCounts read f ε) :
    2 * q ∈ OneHotXorQueryCounts read f ε := by
  obtain ⟨W', _, _, A, hA⟩ := hq
  refine mem_oneHotXorQueryCounts
    (A := (simTransHot (QRoutine.mk q A.step A.step_unitary)).toAlg
      (crossEmbed (some hotZero) A.init)
      (isQState_crossEmbed (some hotZero) A.init_isQState)
      (crossStrip (Hot σ) A.readout)) ?_
  intro x
  have hlen : (simTransHot (QRoutine.mk q A.step A.step_unitary)).len = 2 * q := by
    rw [simTransHot_len]
  have hstate : oneHotState ((simTransHot (QRoutine.mk q A.step A.step_unitary)).toAlg
        (crossEmbed (some hotZero) A.init)
        (isQState_crossEmbed (some hotZero) A.init_isQState)
        (crossStrip (Hot σ) A.readout)) (read x) (2 * q)
      = crossEmbed (some hotZero) (A.state (read x) q) := by
    rw [oneHotState_toAlg, show (2 * q)
        = (simTransHot (QRoutine.mk q A.step A.step_unitary)).len from hlen.symm]
    rw [show (simTransHot (QRoutine.mk q A.step A.step_unitary)).runWith
          (oneHotOracleMat (read x))
          (simTransHot (QRoutine.mk q A.step A.step_unitary)).len
        = (simTransHot (QRoutine.mk q A.step A.step_unitary)).oneHotRun (read x)
        from rfl]
    rw [simTransHot_oneHotRun,
      show (QRoutine.mk q A.step A.step_unitary).run (read x)
          = (QRoutine.mk q A.step A.step_unitary).runUpto (read x) q from rfl,
      ← state_eq_runUpto2 A q]
  rw [hstate,
    show ((simTransHot (QRoutine.mk q A.step A.step_unitary)).toAlg
        (crossEmbed (some hotZero) A.init)
        (isQState_crossEmbed (some hotZero) A.init_isQState)
        (crossStrip (Hot σ) A.readout)).readout = crossStrip (Hot σ) A.readout
      from rfl,
    qProb_crossStrip_crossEmbed]
  exact hA x

/-! ## The complexity comparison -/

variable [Nonempty O]

theorem oneHotXorQueryCounts_nonempty {read : X → ι → σ} {f : X → O} {ε : ℝ}
    (hdet : ∀ x y, read x = read y → f x = f y) (hε0 : 0 ≤ ε) :
    (OneHotXorQueryCounts read f ε).Nonempty := by
  obtain ⟨q, hq⟩ := queryCounts_nonempty hdet hε0
  exact ⟨2 * q, two_mul_mem_oneHotXorQueryCounts_of_std hq⟩

/-- **Model equivalence, one direction**: native complexity is at most twice
the one-hot complexity. -/
theorem qQueryOn_le_two_mul_oneHotQQueryOn {read : X → ι → σ} {f : X → O}
    {ε : ℝ} (hdet : ∀ x y, read x = read y → f x = f y) (hε0 : 0 ≤ ε) :
    qQueryOn read f ε ≤ 2 * oneHotQQueryOn read f ε := by
  have hne := oneHotXorQueryCounts_nonempty hdet hε0
  have hmem : oneHotQQueryOn read f ε ∈ OneHotXorQueryCounts read f ε :=
    Nat.sInf_mem hne
  exact Nat.sInf_le (two_mul_mem_queryCounts_of_oneHot hmem)

/-- **Model equivalence, the other direction**: one-hot complexity is at most
twice the native complexity. -/
theorem oneHotQQueryOn_le_two_mul_qQueryOn {read : X → ι → σ} {f : X → O}
    {ε : ℝ} (hdet : ∀ x y, read x = read y → f x = f y) (hε0 : 0 ≤ ε) :
    oneHotQQueryOn read f ε ≤ 2 * qQueryOn read f ε := by
  have hne := queryCounts_nonempty hdet hε0
  have hmem : qQueryOn read f ε ∈ QueryCounts read f ε := Nat.sInf_mem hne
  exact Nat.sInf_le (two_mul_mem_oneHotXorQueryCounts_of_std hmem)

end Translations

end QuantumQueryComplexity
