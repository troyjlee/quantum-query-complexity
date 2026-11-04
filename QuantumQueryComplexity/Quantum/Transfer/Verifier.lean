import QuantumQueryComplexity.Quantum.JointState.Success

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Appending an exact verifier

The comparison theorem [CGZ, Theorem 4.1] bounds the probability that a computation **accepts**,
and needs that computation to reject every negative input.  A search algorithm is made into such
a computation by appending a verifier for its output.

A **nonadaptive classical verifier** with `v` queries (`Verifier`) names, for each output `o`,
`v` coordinates `qry o k` and a decision `dec o` on their values.
`QAlg.appendVerifier A t V` runs `A` for `t` XOR queries, then makes the `v` verification
queries coherently and accepts according to `dec`.  The queried bits **stay** in ancillary
registers: they are not uncomputed, so verification costs exactly `v` queries.  The acceptance
measurement acts on the workspace only, which is what the comparison theorem needs.

## Construction

The workspace is `VerWS ι W v = ((Option ι × Option Bool) × (Fin v → Bool)) × W`: a register
that saves `A`'s index and answer registers, `v` answer bits, and `A`'s workspace.  The saved
register starts at `(none, none)`, and the answer bits start at `false`.  The construction is
free.  Its specification is `xorSuccessProbOn_appendVerifier`, which determines the acceptance
probability after `t + v` queries exactly.

## Main definitions

* `Verifier ι O v`, `Verifier.accepts`.
* `VerWS ι W v`, `QAlg.appendVerifier`.

## Main results

* `xorSuccessProbOn_appendVerifier` — after `t + v` queries, the appended algorithm accepts
  with exactly the probability that `V` accepts `A`'s output after `t` queries.
* `xorSuccessProbOn_le_appendVerifier` — if `V` accepts every valid output, acceptance is at
  least `A`'s success probability.
* `xorSuccessProbOn_appendVerifier_eq_zero` — if `V` rejects every output, the appended
  algorithm never accepts.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

/-- **A nonadaptive classical verifier** with `v` queries for outputs in `O`: on output `o` it
reads the coordinates `qry o k`, `k < v`, and decides by `dec o`. -/
structure Verifier (ι O : Type) (v : ℕ) where
  /-- The coordinates read to check the output `o`. -/
  qry : O → Fin v → ι
  /-- The decision on the output `o`, from the values read. -/
  dec : O → (Fin v → Bool) → Bool

/-- `V` accepts the output `o` on the input `a`. -/
def Verifier.accepts {ι O : Type} {v : ℕ} (V : Verifier ι O v) (a : ι → Bool) (o : O) : Bool :=
  V.dec o fun k => a (V.qry o k)

/-- The workspace of the verified algorithm: a register saving `A`'s index and answer
registers, the `v` answer bits, and `A`'s workspace. -/
abbrev VerWS (ι W : Type) (v : ℕ) : Type := ((Option ι × Option Bool) × (Fin v → Bool)) × W

variable {ι O W X : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W] [Fintype X]
  {v : ℕ}

/-! ## The gates of the verification phase -/

/-- Instance search exceeds its size budget on the basis of the appended algorithm, so the
instance is given in two stages.  It is local to this file. -/
private local instance instDecidableEqVerBasis : DecidableEq (QBasis ι Bool (VerWS ι W v)) :=
  @instDecidableEqProd _ _ _
    (@instDecidableEqProd _ _ _ (inferInstanceAs (DecidableEq (VerWS ι W v))))

/-- The initial value of the extra register: blank saved registers, all answer bits `false`. -/
private def verZero : (Option ι × Option Bool) × (Fin v → Bool) := ((none, none), fun _ => false)

/-- `A`'s basis state, read from the saved register and the workspace. -/
private def verC (p : QBasis ι Bool (VerWS ι W v)) : QBasis ι Bool W :=
  (p.2.2.1.1.1, p.2.2.1.1.2, p.2.2.2)

/-- The index and answer registers for the `k`-th verification query on the output `o`: the
coordinate `V.qry o k` with answer `false`, or blank once all `v` queries are made. -/
private def verIdx (V : Verifier ι O v) (o : O) (k : ℕ) : Option ι × Option Bool :=
  if h : k < v then (some (V.qry o ⟨k, h⟩), some false) else (none, none)

/-- Swap the index and answer registers with the saved register. -/
private def verSaveMap (p : QBasis ι Bool (VerWS ι W v)) : QBasis ι Bool (VerWS ι W v) :=
  (p.2.2.1.1.1, p.2.2.1.1.2, (((p.1, p.2.1), p.2.2.1.2), p.2.2.2))

private lemma verSaveMap_involutive :
    Function.Involutive (verSaveMap (ι := ι) (W := W) (v := v)) := fun _ => rfl

/-- Controlled on `A`'s saved basis state `c`, swap the index and answer registers between
`X o` and `Y o`, where `o` is the readout of `c`. -/
private def verSwapMap (A : QAlg ι Bool O W) (X Y : O → Option ι × Option Bool)
    (p : QBasis ι Bool (VerWS ι W v)) : QBasis ι Bool (VerWS ι W v) :=
  let r := Equiv.swap (X (A.readout (verC p))) (Y (A.readout (verC p))) (p.1, p.2.1)
  (r.1, r.2, p.2.2)

private lemma verSwapMap_involutive (A : QAlg ι Bool O W) (X Y : O → Option ι × Option Bool) :
    Function.Involutive (verSwapMap (v := v) A X Y) := by
  intro p
  simp only [verSwapMap, verC, Prod.mk.eta, Equiv.swap_apply_self]

/-- Exchange the answer bit with the ancillary bit `k`, when the answer is not blank. -/
private def verMvBits (k : Fin v) : Option Bool × (Fin v → Bool) → Option Bool × (Fin v → Bool)
  | (some b, f) => (some (f k), Function.update f k b)
  | (none, f) => (none, f)

private lemma verMvBits_verMvBits (k : Fin v) (x : Option Bool × (Fin v → Bool)) :
    verMvBits k (verMvBits k x) = x := by
  rcases x with ⟨_ | b, f⟩
  · rfl
  · simp [verMvBits]

/-- Move the answer register into the ancillary bit `k` (the identity for `k ≥ v`). -/
private def verMvMap (k : ℕ) (p : QBasis ι Bool (VerWS ι W v)) : QBasis ι Bool (VerWS ι W v) :=
  if h : k < v then
    let r := verMvBits ⟨k, h⟩ (p.2.1, p.2.2.1.2)
    (p.1, r.1, ((p.2.2.1.1, r.2), p.2.2.2))
  else p

private lemma verMvMap_involutive (k : ℕ) :
    Function.Involutive (verMvMap (ι := ι) (W := W) (v := v) k) := by
  intro p
  by_cases h : k < v
  · simp only [verMvMap, dite_eq_left h, Prod.mk.eta, verMvBits_verMvBits]
  · simp only [verMvMap, dite_eq_right h]

/-- The gate after `A`'s last step: save `A`'s index and answer registers, then set the index
register to the first verification query. -/
private def verStartPerm (A : QAlg ι Bool O W) (V : Verifier ι O v) :
    Equiv.Perm (QBasis ι Bool (VerWS ι W v)) :=
  Function.Involutive.toPerm _
      (verSwapMap_involutive A (fun _ => (none, none)) (fun o => verIdx V o 0)) *
    Function.Involutive.toPerm _ verSaveMap_involutive

/-- The gate after the `k`-th verification query: move its answer into the bit `k`, then set
the index register to the next verification query. -/
private def verPhasePerm (A : QAlg ι Bool O W) (V : Verifier ι O v) (k : ℕ) :
    Equiv.Perm (QBasis ι Bool (VerWS ι W v)) :=
  Function.Involutive.toPerm _
      (verSwapMap_involutive A (fun o => verIdx V o k) (fun o => verIdx V o (k + 1))) *
    Function.Involutive.toPerm _ (verMvMap_involutive k)

/-- The steps of the appended algorithm. -/
private def verStep (A : QAlg ι Bool O W) (t : ℕ) (V : Verifier ι O v) (s : ℕ) :
    Matrix (QBasis ι Bool (VerWS ι W v)) (QBasis ι Bool (VerWS ι W v)) ℂ :=
  if s < t then liftReg ((Option ι × Option Bool) × (Fin v → Bool)) (A.step s)
  else if s = t then
    qPerm (verStartPerm A V) * liftReg ((Option ι × Option Bool) × (Fin v → Bool)) (A.step s)
  else qPerm (verPhasePerm A V (s - t - 1))

private lemma verStep_mem_unitaryGroup (A : QAlg ι Bool O W) (t : ℕ) (V : Verifier ι O v)
    (s : ℕ) : verStep A t V s ∈ Matrix.unitaryGroup (QBasis ι Bool (VerWS ι W v)) ℂ := by
  unfold verStep
  split_ifs
  · exact liftReg_mem_unitaryGroup (A.step_unitary s)
  · exact mul_mem_qUnitary (qPerm_mem_unitaryGroup _)
      (liftReg_mem_unitaryGroup (A.step_unitary s))
  · exact qPerm_mem_unitaryGroup _

/-- **`A` followed by the verifier `V`.**  Run `A` for `t` XOR queries.  Then save `A`'s index
and answer registers, make the `v` queries `V.qry o k` on `A`'s output `o` with the answers kept
in ancillary bits, and accept iff `V.dec o` holds on them.  The readout is the acceptance bit.
-/
noncomputable def QAlg.appendVerifier (A : QAlg ι Bool O W) (t : ℕ) (V : Verifier ι O v) :
    QAlg ι Bool Bool (VerWS ι W v) where
  init := embedReg verZero A.init
  init_isQState := by
    rw [IsQState, qNormSq_embedReg]
    exact A.init_isQState
  step := verStep A t V
  step_unitary := verStep_mem_unitaryGroup A t V
  readout p := V.dec (A.readout (verC p)) p.2.2.1.2

/-! ## The run of the appended algorithm -/

/-- The XOR oracle passes through a workspace extension. -/
private lemma xorOracleMat_mulVec_embedReg {R : Type} [Fintype R] [DecidableEq R] (a : ι → Bool)
    (u : R) (φ : QBasis ι Bool W → ℂ) :
    xorOracleMat a *ᵥ embedReg u φ = embedReg u (xorOracleMat a *ᵥ φ) := by
  funext p
  rw [xorOracleMat_mulVec_apply, embedReg_apply, embedReg_apply, xorOracleMat_mulVec_apply]
  rcases p with ⟨_ | i, b, r, w⟩ <;> rfl

/-- `xorState_zero`, without a decidable equality on the outputs. -/
private lemma xorState_zero' {W' : Type} [Fintype W'] [DecidableEq W'] (B : QAlg ι Bool O W')
    (a : ι → Bool) : xorState B a 0 = B.step 0 *ᵥ B.init := rfl

/-- `xorState_succ`, without a decidable equality on the outputs. -/
private lemma xorState_succ' {W' : Type} [Fintype W'] [DecidableEq W'] (B : QAlg ι Bool O W')
    (a : ι → Bool) (s : ℕ) :
    xorState B a (s + 1) = B.step (s + 1) *ᵥ (xorOracleMat a *ᵥ xorState B a s) := rfl

private lemma appendVerifier_step (A : QAlg ι Bool O W) (t : ℕ) (V : Verifier ι O v) (s : ℕ) :
    (A.appendVerifier t V).step s = verStep A t V s := rfl

/-- While `A` runs, the appended algorithm is `A` on the sector of the initial extra register. -/
private lemma xorState_appendVerifier_of_lt (A : QAlg ι Bool O W) (t : ℕ) (V : Verifier ι O v)
    (a : ι → Bool) : ∀ s, s < t →
    xorState (A.appendVerifier t V) a s = embedReg verZero (xorState A a s)
  | 0, h => by
    rw [xorState_zero', xorState_zero', appendVerifier_step, verStep, ite_eq_left h]
    exact liftReg_mulVec_embed _ _ _
  | s + 1, h => by
    rw [xorState_succ', xorState_succ', xorState_appendVerifier_of_lt A t V a s (by omega),
      xorOracleMat_mulVec_embedReg, appendVerifier_step, verStep, ite_eq_left h]
    exact liftReg_mulVec_embed _ _ _

/-- After `t` queries, `A`'s last step is followed by the start gate. -/
private lemma xorState_appendVerifier_self (A : QAlg ι Bool O W) (t : ℕ) (V : Verifier ι O v)
    (a : ι → Bool) :
    xorState (A.appendVerifier t V) a t
      = qPerm (verStartPerm A V) *ᵥ embedReg verZero (xorState A a t) := by
  cases t with
  | zero =>
    rw [xorState_zero', xorState_zero', appendVerifier_step, verStep, ite_eq_right (lt_irrefl 0),
      ite_eq_left rfl, ← Matrix.mulVec_mulVec, ← liftReg_mulVec_embed]
    rfl
  | succ s =>
    rw [xorState_succ', xorState_succ',
      xorState_appendVerifier_of_lt A (s + 1) V a s (Nat.lt_succ_self s),
      xorOracleMat_mulVec_embedReg, appendVerifier_step, verStep, ite_eq_right (lt_irrefl _),
      ite_eq_left rfl, ← Matrix.mulVec_mulVec, liftReg_mulVec_embed]

/-- A state on the sector of `u`, as a superposition of basis states. -/
private lemma embedReg_eq_sum {R : Type} [Fintype R] [DecidableEq R] (u : R)
    (ψ : QBasis ι Bool W → ℂ) :
    embedReg u ψ = ∑ c, ψ c • qBasis ((c.1, c.2.1, (u, c.2.2)) : QBasis ι Bool (R × W)) := by
  funext p
  rw [embedReg_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, qBasis_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rcases p with ⟨i, b, r, w⟩
  by_cases h : r = u
  · subst h
    rw [ite_eq_left rfl, Finset.sum_eq_single (i, b, w)]
    · rw [ite_eq_left rfl]
    · rintro ⟨i', b', w'⟩ _ hc
      refine ite_eq_right fun he => hc ?_
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, -, rfl⟩ := he
      rfl
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [ite_eq_right h]
    refine (Finset.sum_eq_zero fun c _ => ite_eq_right fun he => h ?_).symm
    simp only [Prod.mk.injEq] at he
    exact he.2.2.1

/-- The answer bits after `k` verification queries on the output `o`. -/
private def verBits (V : Verifier ι O v) (a : ι → Bool) (o : O) (k : ℕ) : Fin v → Bool :=
  fun j => if j.val < k then a (V.qry o j) else false

/-- The basis state that `A`'s basis state `c` is carried to after `k` verification queries. -/
private def verPt (A : QAlg ι Bool O W) (V : Verifier ι O v) (a : ι → Bool) (k : ℕ)
    (c : QBasis ι Bool W) : QBasis ι Bool (VerWS ι W v) :=
  ((verIdx V (A.readout c) k).1, (verIdx V (A.readout c) k).2,
    (((c.1, c.2.1), verBits V a (A.readout c) k), c.2.2))

private lemma verPt_injective (A : QAlg ι Bool O W) (V : Verifier ι O v) (a : ι → Bool)
    (k : ℕ) : Function.Injective (verPt A V a k) := fun c c' h => by
  have h' := congrArg verC h
  exact h'

private lemma verStartPerm_apply (A : QAlg ι Bool O W) (V : Verifier ι O v) (a : ι → Bool)
    (c : QBasis ι Bool W) :
    verStartPerm A V ((c.1, c.2.1, (verZero, c.2.2)) : QBasis ι Bool (VerWS ι W v))
      = verPt A V a 0 c := by
  simp only [verStartPerm, Equiv.Perm.mul_apply, Function.Involutive.coe_toPerm, verSaveMap,
    verSwapMap, verC, verZero, verPt, Prod.mk.eta, Equiv.swap_apply_left]
  rfl

private lemma verPhasePerm_apply (A : QAlg ι Bool O W) (V : Verifier ι O v) (a : ι → Bool)
    (c : QBasis ι Bool W) {k : ℕ} (hk : k < v) :
    verPhasePerm A V k (xorOracleMap a (verPt A V a k c)) = verPt A V a (k + 1) c := by
  have hI : verIdx V (A.readout c) k = (some (V.qry (A.readout c) ⟨k, hk⟩), some false) :=
    dite_eq_left hk
  simp only [verPhasePerm, Equiv.Perm.mul_apply, Function.Involutive.coe_toPerm, verPt, hI,
    xorOracleMap_some, optXor_some_some, Bool.false_xor, verMvMap, dite_eq_left hk, verMvBits,
    verSwapMap, verC, Prod.mk.eta]
  have hb : verBits V a (A.readout c) k ⟨k, hk⟩ = false := by simp [verBits]
  have hu : Function.update (verBits V a (A.readout c) k) ⟨k, hk⟩
      (a (V.qry (A.readout c) ⟨k, hk⟩)) = verBits V a (A.readout c) (k + 1) := by
    funext j
    by_cases hj : j = ⟨k, hk⟩
    · subst hj
      simp [verBits]
    · have hjk : j.val ≠ k := fun h => hj (Fin.ext h)
      rw [Function.update_of_ne hj]
      simp only [verBits]
      by_cases h1 : j.val < k
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]
  rw [hb, ← hI, Equiv.swap_apply_left, hu]

/-- **The run of the verification phase**: after `t + k` queries, `k ≤ v`, every basis state
`c` of `A`'s state after `t` queries is carried to `verPt A V a k c`. -/
private lemma xorState_appendVerifier_add (A : QAlg ι Bool O W) (t : ℕ) (V : Verifier ι O v)
    (a : ι → Bool) : ∀ k, k ≤ v →
    xorState (A.appendVerifier t V) a (t + k)
      = ∑ c, xorState A a t c • qBasis (verPt A V a k c)
  | 0, _ => by
    rw [Nat.add_zero, xorState_appendVerifier_self, embedReg_eq_sum, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mulVec_smul, qPerm_mulVec_qBasis, verStartPerm_apply]
  | k + 1, hk => by
    rw [← Nat.add_assoc, xorState_succ', xorState_appendVerifier_add A t V a k (by omega),
      Matrix.mulVec_sum, Matrix.mulVec_sum, appendVerifier_step, verStep, ite_eq_right (by omega),
      ite_eq_right (by omega), show t + k + 1 - t - 1 = k by omega]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, xorOracleMat, qPerm_mulVec_qBasis,
      qPerm_mulVec_qBasis, xorOraclePerm_apply, verPhasePerm_apply A V a c (by omega)]

/-- The good mass of a superposition of distinct basis states. -/
private lemma goodProb_sum_smul_qBasis {H H' : Type} [Fintype H] [DecidableEq H] [Fintype H']
    {O' : Type} (rd : H → O') (G : O' → Prop) [DecidablePred G] (Φ : H' → H)
    (hΦ : Function.Injective Φ) (c : H' → ℂ) :
    goodProb rd G (∑ p, c p • qBasis (Φ p))
      = ∑ p, if G (rd (Φ p)) then Complex.normSq (c p) else 0 := by
  have hvec : ∀ h, (∑ p, c p • qBasis (Φ p)) h = ∑ p, if h = Φ p then c p else 0 := by
    intro h
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [qBasis_apply]
  rw [goodProb_eq_sum_ite]
  symm
  refine Fintype.sum_of_injective Φ hΦ _ _ (fun h hh => ?_) (fun p => ?_)
  · rw [hvec, Finset.sum_eq_zero fun p _ => ite_eq_right fun he => hh ⟨p, he.symm⟩]
    simp
  · rw [hvec, Finset.sum_eq_single p (fun q _ hq => ite_eq_right fun he => hq (hΦ he).symm)
      (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl]

private lemma appendVerifier_readout_verPt (A : QAlg ι Bool O W) (t : ℕ) (V : Verifier ι O v)
    (a : ι → Bool) (c : QBasis ι Bool W) :
    (A.appendVerifier t V).readout (verPt A V a v c) = V.accepts a (A.readout c) := by
  change V.dec (A.readout c) (verBits V a (A.readout c) v)
    = V.dec (A.readout c) fun k => a (V.qry (A.readout c) k)
  congr 1
  funext j
  simp [verBits, j.isLt]

/-- **The appended verifier accepts with exactly the probability that `V` accepts `A`'s
output**: after `t + v` XOR queries on the input `read x`, acceptance has the probability that
`A`'s output after `t` queries is accepted by `V` on `read x`. -/
theorem xorSuccessProbOn_appendVerifier (A : QAlg ι Bool O W) (t : ℕ) (V : Verifier ι O v)
    (read : X → ι → Bool) (x : X) :
    xorSuccessProbOn (A.appendVerifier t V) (t + v) read (fun _ b => b = true) x
      = xorSuccessProbOn A t read (fun x o => V.accepts (read x) o = true) x := by
  rw [xorSuccessProbOn, xorSuccessProbOn, xorState_appendVerifier_add A t V (read x) v le_rfl,
    goodProb_sum_smul_qBasis _ _ _ (verPt_injective A V (read x) v), goodProb_eq_sum_ite]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [appendVerifier_readout_verPt]

/-- **Completeness**: if `V` accepts every output valid for `x`, the appended algorithm accepts
`x` at least as often as `A` succeeds on it. -/
theorem xorSuccessProbOn_le_appendVerifier (A : QAlg ι Bool O W) (t : ℕ) (V : Verifier ι O v)
    (read : X → ι → Bool) (Good : X → O → Prop) [∀ x, DecidablePred (Good x)] (x : X)
    (hV : ∀ o, Good x o → V.accepts (read x) o = true) :
    xorSuccessProbOn A t read Good x
      ≤ xorSuccessProbOn (A.appendVerifier t V) (t + v) read (fun _ b => b = true) x := by
  rw [xorSuccessProbOn_appendVerifier, xorSuccessProbOn, xorSuccessProbOn, goodProb_eq_sum_ite,
    goodProb_eq_sum_ite]
  refine Finset.sum_le_sum fun c _ => ?_
  by_cases hg : Good x (A.readout c)
  · rw [ite_eq_left hg, ite_eq_left (hV _ hg)]
  · rw [ite_eq_right hg]
    split_ifs
    · exact Complex.normSq_nonneg _
    · exact le_rfl

/-- **Soundness**: if `V` rejects every output on `x`, the appended algorithm never accepts
`x`. -/
theorem xorSuccessProbOn_appendVerifier_eq_zero (A : QAlg ι Bool O W) (t : ℕ)
    (V : Verifier ι O v) (read : X → ι → Bool) (x : X)
    (hV : ∀ o, V.accepts (read x) o = false) :
    xorSuccessProbOn (A.appendVerifier t V) (t + v) read (fun _ b => b = true) x = 0 := by
  rw [xorSuccessProbOn_appendVerifier, xorSuccessProbOn, goodProb_eq_sum_ite]
  exact Finset.sum_eq_zero fun c _ => ite_eq_right (by simp [hV])

end QuantumQueryComplexity
