import QuantumQueryComplexity.Quantum.KronLift
import QuantumQueryComplexity.Quantum.Postcomp
set_option synthInstance.maxSize 800

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Simulating a coarser alphabet: the two-query section lookup

Let `lift : σ → τ` be **any** map between finite alphabets — no injectivity
is needed.  An algorithm designed for the `τ`-oracle, which answers
`lift (read x i)`, can be run against the `σ`-oracle, which answers
`read x i`, at **two `σ`-queries per `τ`-query**:

    query σ  →  compute `lift` into a τ-register  →  query σ again

The last query is the uncompute that returns the `σ`-answer register to
blank, so the compiled routine acts on the embedded states exactly as the
original acted on its own (`mapAlphabet_run`).  The middle step
(`liftSwapMat`) is input-independent: it reads the `σ`-answer register that
is already there and performs the `τ`-transposition determined by it.

The workspace of the compiled routine is `Option τ × W`, and

    QBasis ι σ (Option τ × W) ≃ QBasis ι τ W × Option σ

(`basisEquiv`) — the index register is shared, the `τ`-answer register moves
into the workspace, and the `σ`-answer register becomes the spectator
factor.  That is exactly the shape `KronLift.lean` handles, so the original
routine's own steps are carried over by `kronLift` and the embedded states
are `splitVec`s with the spectator pinned to blank (`embedAnswer`).

Headline: `qQueryOn_alphabetMap_le`,

    qQueryOn read f ε ≤ 2 * qQueryOn (fun x i => lift (read x i)) f ε.

Scope: this is a statement about **finite** alphabets throughout — `QBasis`
bakes in a `Fintype` answer register — so it delivers uniformity over finite
allowed subalphabets, never a literally infinite value oracle.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ τ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [DecidableEq σ] [Fintype τ] [DecidableEq τ] [Fintype W] [DecidableEq W]

/-! ## The basis reassociation -/

/-- The compiled workspace holds the simulated algorithm's answer register;
reassociating puts the simulated basis first and the `σ`-answer register
last. -/
def basisEquiv : QBasis ι σ (Option τ × W) ≃ QBasis ι τ W × Option σ where
  toFun p := ((p.1, p.2.2.1, p.2.2.2), p.2.1)
  invFun q := (q.1.1, q.2, q.1.2.1, q.1.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma basisEquiv_apply (i : Option ι) (s : Option σ) (t : Option τ)
    (w : W) :
    basisEquiv ((i, s, t, w) : QBasis ι σ (Option τ × W))
      = ((i, t, w), s) := rfl

@[simp] lemma basisEquiv_symm_apply (i : Option ι) (t : Option τ) (w : W)
    (s : Option σ) :
    (basisEquiv (ι := ι) (σ := σ) (τ := τ) (W := W)).symm ((i, t, w), s)
      = (i, s, t, w) := rfl

/-- The blank spectator: the `σ`-answer register is returned unused. -/
def blankAnswer : Option σ → ℂ := fun s => if s = none then 1 else 0

@[simp] lemma blankAnswer_none : blankAnswer (none : Option σ) = 1 :=
  if_pos rfl

@[simp] lemma blankAnswer_some (s : σ) : blankAnswer (some s) = 0 :=
  if_neg (Option.some_ne_none s)

lemma qNormSq_blankAnswer : qNormSq (blankAnswer (σ := σ)) = 1 := by
  classical
  rw [qNormSq_def]
  rw [Finset.sum_eq_single (none : Option σ)]
  · rw [blankAnswer, if_pos rfl]
    simp
  · intro s _ hs
    rw [blankAnswer, if_neg hs]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A simulated state, embedded with the `σ`-answer register blank. -/
noncomputable def embedAnswer (ψ : QBasis ι τ W → ℂ) :
    QBasis ι σ (Option τ × W) → ℂ :=
  splitVec basisEquiv ψ blankAnswer

lemma embedAnswer_apply (ψ : QBasis ι τ W → ℂ) (i : Option ι) (s : Option σ)
    (t : Option τ) (w : W) :
    embedAnswer (σ := σ) ψ (i, s, t, w) = ψ (i, t, w) * blankAnswer s := rfl

lemma embedAnswer_eq (ψ : QBasis ι τ W → ℂ) (p : QBasis ι σ (Option τ × W)) :
    embedAnswer (σ := σ) ψ p
      = ψ (p.1, p.2.2.1, p.2.2.2) * blankAnswer p.2.1 := rfl

lemma qNormSq_embedAnswer (ψ : QBasis ι τ W → ℂ) :
    qNormSq (embedAnswer (σ := σ) ψ) = qNormSq ψ := by
  rw [embedAnswer, qNormSq_splitVec, qNormSq_blankAnswer, mul_one]

lemma isQState_embedAnswer {ψ : QBasis ι τ W → ℂ} (h : IsQState ψ) :
    IsQState (embedAnswer (σ := σ) ψ) := by
  rw [IsQState, qNormSq_embedAnswer]
  exact h

/-! ## The middle step: writing `lift` into the `τ`-register -/

/-- Controlled on the `σ`-answer register holding `some s`, perform the
`τ`-transposition `⊥ ↔ some (lift s)`.  Input-independent: it only reads a
register the oracle has already filled. -/
def liftSwapMap (lift : σ → τ) :
    QBasis ι σ (Option τ × W) → QBasis ι σ (Option τ × W)
  | (i, none, t, w) => (i, none, t, w)
  | (i, some s, t, w) =>
      (i, some s, Equiv.swap none (some (lift s)) t, w)

lemma liftSwapMap_involutive (lift : σ → τ) :
    Function.Involutive (liftSwapMap (ι := ι) (W := W) lift) := by
  rintro ⟨i, s, t, w⟩
  cases s with
  | none => rfl
  | some s =>
      show (i, some s, Equiv.swap none (some (lift s))
        (Equiv.swap none (some (lift s)) t), w) = _
      rw [Equiv.swap_apply_self]

/-- The `σ`-answer register is untouched. -/
lemma liftSwapMap_snd (lift : σ → τ) (p : QBasis ι σ (Option τ × W)) :
    (liftSwapMap lift p).2.1 = p.2.1 := by
  obtain ⟨i, s, t, w⟩ := p
  cases s <;> rfl

/-- The index register is untouched. -/
lemma liftSwapMap_fst (lift : σ → τ) (p : QBasis ι σ (Option τ × W)) :
    (liftSwapMap lift p).1 = p.1 := by
  obtain ⟨i, s, t, w⟩ := p
  cases s <;> rfl

noncomputable def liftSwapMat (lift : σ → τ) :
    Matrix (QBasis ι σ (Option τ × W)) (QBasis ι σ (Option τ × W)) ℂ :=
  qPerm (liftSwapMap_involutive (ι := ι) (W := W) lift).toPerm

lemma liftSwapMat_mulVec_apply (lift : σ → τ)
    (ψ : QBasis ι σ (Option τ × W) → ℂ) (p : QBasis ι σ (Option τ × W)) :
    (liftSwapMat lift *ᵥ ψ) p = ψ (liftSwapMap lift p) := by
  rw [liftSwapMat, qPerm_mulVec_apply]
  rfl

lemma liftSwapMat_mem_unitaryGroup (lift : σ → τ) :
    liftSwapMat (ι := ι) (W := W) lift
      ∈ Matrix.unitaryGroup (QBasis ι σ (Option τ × W)) ℂ :=
  qPerm_mem_unitaryGroup _

/-! ## The gadget -/

/-- **The `σ`-answer register comes back blank**: the two oracle calls cancel
on it, because the middle step does not touch it and the index register is
constant throughout. -/
lemma gadget_snd (lift : σ → τ) (a : ι → σ) (p : QBasis ι σ (Option τ × W)) :
    (oracleMap a (liftSwapMap lift (oracleMap a p))).2.1 = p.2.1 := by
  have hfst : (liftSwapMap lift (oracleMap a p)).1 = p.1 := by
    rw [liftSwapMap_fst, oracleMap_fst]
  have hsnd : (liftSwapMap lift (oracleMap a p)).2.1 = (oracleMap a p).2.1 :=
    liftSwapMap_snd lift _
  cases hi : p.1 with
  | none =>
      rw [oracleMap_snd_of_fst_none (by rw [hfst, hi]), hsnd,
        oracleMap_snd_of_fst_none hi]
  | some i =>
      rw [oracleMap_snd_of_fst_some (show (liftSwapMap lift
          (oracleMap a p)).1 = some i from by rw [hfst, hi]), hsnd,
        oracleMap_snd_of_fst_some hi, Equiv.swap_apply_self]

/-- **On a blank input the gadget performs the simulated query.** -/
lemma gadget_blank (lift : σ → τ) (a : ι → σ) (i : Option ι) (t : Option τ)
    (w : W) :
    oracleMap a (liftSwapMap lift
        (oracleMap a ((i, none, t, w) : QBasis ι σ (Option τ × W))))
      = ((oracleMap (fun j => lift (a j)) ((i, t, w) : QBasis ι τ W)).1,
          none,
          (oracleMap (fun j => lift (a j)) ((i, t, w) : QBasis ι τ W)).2.1,
          (oracleMap (fun j => lift (a j)) ((i, t, w) : QBasis ι τ W)).2.2) := by
  cases i with
  | none => rfl
  | some i =>
      rw [oracleMap_some, Equiv.swap_apply_left]
      show oracleMap a ((some i, some (a i),
          Equiv.swap none (some (lift (a i))) t, w) :
            QBasis ι σ (Option τ × W)) = _
      rw [oracleMap_some, Equiv.swap_apply_right]
      rfl

/-- **The gadget, on embedded states**: two `σ`-queries with the lookup in
between act as one `τ`-query. -/
lemma gadget_mulVec (lift : σ → τ) (a : ι → σ) (ψ : QBasis ι τ W → ℂ) :
    oracleMat a *ᵥ (liftSwapMat lift *ᵥ
        (oracleMat a *ᵥ embedAnswer (σ := σ) ψ))
      = embedAnswer (σ := σ) (oracleMat (fun j => lift (a j)) *ᵥ ψ) := by
  funext p
  rw [oracleMat_mulVec_apply, liftSwapMat_mulVec_apply, oracleMat_mulVec_apply]
  obtain ⟨i, s, t, w⟩ := p
  cases s with
  | some s =>
      -- the spectator is not blank on either side, so both sides vanish
      have hs : (oracleMap a (liftSwapMap lift
          (oracleMap a ((i, some s, t, w) : QBasis ι σ (Option τ × W))))).2.1
          = some s := gadget_snd lift a _
      rw [embedAnswer_eq, embedAnswer_eq, hs, blankAnswer_some, mul_zero]
      exact (mul_zero _).symm
  | none =>
      rw [gadget_blank, embedAnswer_apply, embedAnswer_apply,
        oracleMat_mulVec_apply]

/-! ## The compiled routine -/

/-- The two-query section lookup: query, write `lift` into the `τ`-register,
query again to clean the `σ`-register. -/
noncomputable def sectionQuery (lift : σ → τ) :
    QRoutine ι σ (Option τ × W) where
  len := 2
  step t := if t = 1 then liftSwapMat lift else 1
  step_unitary t := by
    by_cases h : t = 1
    · rw [if_pos h]
      exact liftSwapMat_mem_unitaryGroup lift
    · rw [if_neg h]
      exact Submonoid.one_mem _

@[simp] lemma sectionQuery_len (lift : σ → τ) :
    (sectionQuery (ι := ι) (W := W) lift).len = 2 := rfl

/-- **The compiled routine**: each of `R`'s steps is carried over by
`kronLift`, and each of its queries is replaced by the two-query gadget. -/
noncomputable def mapAlphabet (lift : σ → τ) (R : QRoutine ι τ W) :
    QRoutine ι σ (Option τ × W) where
  len := 2 * R.len
  step t :=
    if t % 2 = 1 then liftSwapMat lift
    else kronLift basisEquiv (R.step (t / 2))
  step_unitary t := by
    by_cases h : t % 2 = 1
    · rw [if_pos h]
      exact liftSwapMat_mem_unitaryGroup lift
    · rw [if_neg h]
      exact kronLift_mem_unitaryGroup _ (R.step_unitary _)

@[simp] lemma mapAlphabet_len (lift : σ → τ) (R : QRoutine ι τ W) :
    (mapAlphabet (ι := ι) lift R).len = 2 * R.len := rfl

lemma mapAlphabet_step_even (lift : σ → τ) (R : QRoutine ι τ W) (j : ℕ) :
    (mapAlphabet (ι := ι) lift R).step (2 * j)
      = kronLift basisEquiv (R.step j) := by
  show (if (2 * j) % 2 = 1 then liftSwapMat lift
      else kronLift basisEquiv (R.step ((2 * j) / 2))) = _
  rw [if_neg (by omega), show 2 * j / 2 = j from by omega]

lemma mapAlphabet_step_odd (lift : σ → τ) (R : QRoutine ι τ W) (j : ℕ) :
    (mapAlphabet (ι := ι) lift R).step (2 * j + 1) = liftSwapMat lift := by
  show (if (2 * j + 1) % 2 = 1 then liftSwapMat lift
      else kronLift basisEquiv (R.step ((2 * j + 1) / 2))) = _
  rw [if_pos (by omega)]

/-- **The compiled routine runs as the original**, on embedded states. -/
theorem mapAlphabet_runUpto (lift : σ → τ) (R : QRoutine ι τ W) (a : ι → σ)
    (ψ : QBasis ι τ W → ℂ) (t : ℕ) :
    (mapAlphabet lift R).runUpto a (2 * t) *ᵥ embedAnswer (σ := σ) ψ
      = embedAnswer (σ := σ) (R.runUpto (fun j => lift (a j)) t *ᵥ ψ) := by
  induction t with
  | zero =>
      rw [Nat.mul_zero, QRoutine.runUpto_zero, QRoutine.runUpto_zero,
        show (mapAlphabet (ι := ι) lift R).step 0
          = kronLift basisEquiv (R.step 0) from by
            simpa using mapAlphabet_step_even lift R 0,
        embedAnswer, embedAnswer, kronLift_mulVec_splitVec]
  | succ t ih =>
      have hstep : 2 * (t + 1) = (2 * t + 1) + 1 := by omega
      rw [hstep, QRoutine.runUpto_succ, QRoutine.runUpto_succ,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
        show (mapAlphabet (ι := ι) lift R).step (2 * t + 1)
          = liftSwapMat lift from mapAlphabet_step_odd lift R t,
        gadget_mulVec,
        show (2 * t + 1) + 1 = 2 * (t + 1) from by omega,
        show (mapAlphabet (ι := ι) lift R).step (2 * (t + 1))
          = kronLift basisEquiv (R.step (t + 1)) from
            mapAlphabet_step_even lift R (t + 1),
        embedAnswer, embedAnswer, kronLift_mulVec_splitVec,
        QRoutine.runUpto_succ, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec]

/-- The contract in `run` form. -/
theorem mapAlphabet_run (lift : σ → τ) (R : QRoutine ι τ W) (a : ι → σ)
    (ψ : QBasis ι τ W → ℂ) :
    (mapAlphabet lift R).run a *ᵥ embedAnswer (σ := σ) ψ
      = embedAnswer (σ := σ) (R.run (fun j => lift (a j)) *ᵥ ψ) := by
  rw [QRoutine.run, QRoutine.run, mapAlphabet_len]
  exact mapAlphabet_runUpto lift R a ψ R.len

/-! ## The algorithm level -/

variable {O : Type} [DecidableEq O]

/-- Reading the simulated algorithm's outcome off the embedded state. -/
lemma qProb_embedAnswer (r : QBasis ι τ W → O) (ψ : QBasis ι τ W → ℂ)
    (o : O) :
    qProb (fun p : QBasis ι σ (Option τ × W) => r (basisEquiv p).1)
        (embedAnswer (σ := σ) ψ) o
      = qProb r ψ o := by
  classical
  rw [qProb, qProb]
  rw [← Equiv.sum_comp (basisEquiv (ι := ι) (σ := σ) (τ := τ) (W := W)).symm
    (fun p => if r (basisEquiv p).1 = o then
      Complex.normSq (embedAnswer (σ := σ) ψ p) else 0)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single (none : Option σ)]
  · rw [Equiv.apply_symm_apply]
    obtain ⟨i, t, w⟩ := b
    rw [show ((basisEquiv (ι := ι) (σ := σ) (τ := τ) (W := W)).symm
        ((i, t, w), none)) = (i, none, t, w) from rfl]
    rw [embedAnswer_apply, blankAnswer, if_pos rfl, mul_one]
  · intro s _ hs
    rw [Equiv.apply_symm_apply]
    obtain ⟨i, t, w⟩ := b
    rw [show ((basisEquiv (ι := ι) (σ := σ) (τ := τ) (W := W)).symm
        ((i, t, w), s)) = (i, s, t, w) from rfl]
    rw [embedAnswer_apply, blankAnswer, if_neg hs, mul_zero]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The simulation at the algorithm level**: a `τ`-algorithm becomes a
`σ`-algorithm of twice the length, same error, same function. -/
theorem computesWithErrorOn_mapAlphabet {X : Type} (lift : σ → τ)
    {A : QAlg ι τ O W} {q : ℕ} {read : X → ι → σ} {f : X → O} {ε : ℝ}
    (h : ComputesWithErrorOn A q (fun x i => lift (read x i)) f ε) :
    ComputesWithErrorOn
      ((mapAlphabet lift (QRoutine.mk q A.step A.step_unitary)).toAlg
        (embedAnswer (σ := σ) A.init) (isQState_embedAnswer A.init_isQState)
        (fun p => A.readout (basisEquiv p).1))
      (2 * q) read f ε := by
  intro x
  have hstate := QRoutine.toAlg_state
    (mapAlphabet lift (QRoutine.mk q A.step A.step_unitary))
    (embedAnswer (σ := σ) A.init) (isQState_embedAnswer A.init_isQState)
    (fun p => A.readout (basisEquiv p).1) (read x) (2 * q)
  rw [QAlg.prob, hstate, mapAlphabet_runUpto]
  show 1 - ε ≤ qProb (fun p : QBasis ι σ (Option τ × W) =>
    A.readout (basisEquiv p).1)
      (embedAnswer (σ := σ)
        ((QRoutine.mk q A.step A.step_unitary).runUpto
          (fun j => lift (read x j)) q *ᵥ A.init)) (f x)
  rw [qProb_embedAnswer, ← state_eq_runUpto2 A q]
  exact h x

/-- **The alphabet-simulation bound**: `Q_ε` against the finer oracle is at
most twice `Q_ε` against the coarser one.  `lift` need not be injective. -/
theorem qQueryOn_alphabetMap_le {X : Type} [Fintype X] (lift : σ → τ)
    (read : X → ι → σ) (f : X → O) {ε : ℝ}
    (hne : (QueryCounts (fun x i => lift (read x i)) f ε).Nonempty) :
    qQueryOn read f ε ≤ 2 * qQueryOn (fun x i => lift (read x i)) f ε := by
  obtain ⟨W', hW1, hW2, A, hA⟩ := exists_computes_qQueryOn hne
  letI := hW1
  letI := hW2
  exact qQueryOn_le (computesWithErrorOn_mapAlphabet lift hA)

end QuantumQueryComplexity
