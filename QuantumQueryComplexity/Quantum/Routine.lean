import QuantumQueryComplexity.Quantum.Algorithm
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Query routines: a composable layer above `QAlg`

`QAlg` is a whole algorithm — an initial state, a schedule, and a readout — and
its schedule has an exact length.  Circuit constructions need something smaller
and composable: an **operator** built from queries, which can be sequenced,
inverted, and controlled, and whose query count is tracked exactly.  That is a
`QRoutine`:

  `R.run a = U_len · O_a · U_{len-1} · ⋯ · O_a · U_0`,   exactly `R.len` queries.

A routine carries no initial state and no readout, so it composes; `R.toAlg`
turns one into a `QAlg` at the end, and `toAlg_state` says the algorithm's state
after `R.len` queries is `R.run a` applied to the initial state.  So everything
proved about `QAlg` — in particular the Milestone A lower bound — applies to
whatever the routine layer builds, with no change to the pinned statements.

## Main results

* `run_mem_unitaryGroup` — a routine is a unitary for every input.
* `toAlg_state` — the bridge to `QAlg`.
* `comp_run` — **sequencing**: `(R.comp S).run a = S.run a * R.run a` with
  `(R.comp S).len = R.len + S.len`.  Query counts add exactly; the boundary
  unitaries `S.step 0` and `R.step R.len` are merged into one, which is why no
  query is wasted at the junction.
* `exists_inv` — **inversion**: every routine has an inverse routine of the
  *same* length.  This is where the oracle being an involution pays: `Oᴴ = O`,
  so reversing a schedule costs no extra queries.
* `runUpto_congr` — routines agreeing on steps `0 … len` have the same run,
  which is what lets constructions specify a schedule only where it matters.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ O W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-- **A query routine**: `len` oracle calls interleaved with input-independent
unitaries. -/
structure QRoutine (ι σ W : Type) [Fintype ι] [DecidableEq ι] [Fintype σ]
    [DecidableEq σ] [Fintype W] [DecidableEq W] where
  /-- The number of queries. -/
  len : ℕ
  /-- The input-independent unitaries; `step t` is applied after the `t`-th
  query, and `step 0` before the first. -/
  step : ℕ → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ
  /-- Each step is unitary. -/
  step_unitary : ∀ t, step t ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ

/-- The adjoint of a unitary is unitary.  (Belongs in `FiniteHilbert.lean`; kept
here to avoid a rebuild of the whole layer.) -/
lemma conjTranspose_mem_qUnitary {H : Type} [Fintype H] [DecidableEq H]
    {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    Uᴴ ∈ Matrix.unitaryGroup H ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  have h := Matrix.mem_unitaryGroup_iff.mp hU
  rwa [Matrix.star_eq_conjTranspose] at h

namespace QRoutine

/-- The operator implemented by the first `t` queries of `R`. -/
def runUpto (R : QRoutine ι σ W) (a : ι → σ) :
    ℕ → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ
  | 0 => R.step 0
  | t + 1 => R.step (t + 1) * (oracleMat a * R.runUpto a t)

@[simp] lemma runUpto_zero (R : QRoutine ι σ W) (a : ι → σ) :
    R.runUpto a 0 = R.step 0 := rfl

@[simp] lemma runUpto_succ (R : QRoutine ι σ W) (a : ι → σ) (t : ℕ) :
    R.runUpto a (t + 1) = R.step (t + 1) * (oracleMat a * R.runUpto a t) := rfl

/-- **The operator implemented by `R`**, using exactly `R.len` queries. -/
def run (R : QRoutine ι σ W) (a : ι → σ) : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ :=
  R.runUpto a R.len

lemma runUpto_mem_unitaryGroup (R : QRoutine ι σ W) (a : ι → σ) (t : ℕ) :
    R.runUpto a t ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ := by
  induction t with
  | zero => exact R.step_unitary 0
  | succ t ih =>
      exact mul_mem (R.step_unitary (t + 1))
        (mul_mem (oracleMat_mem_unitaryGroup a) ih)

lemma run_mem_unitaryGroup (R : QRoutine ι σ W) (a : ι → σ) :
    R.run a ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ :=
  R.runUpto_mem_unitaryGroup a R.len

/-- Only the steps up to `t` matter for the first `t` queries. -/
lemma runUpto_congr {R S : QRoutine ι σ W} (a : ι → σ) {t : ℕ}
    (h : ∀ k, k ≤ t → R.step k = S.step k) : R.runUpto a t = S.runUpto a t := by
  induction t with
  | zero => exact h 0 le_rfl
  | succ t ih =>
      rw [runUpto_succ, runUpto_succ, h (t + 1) le_rfl,
        ih (fun k hk => h k (le_trans hk (Nat.le_succ t)))]

/-! ## The bridge to `QAlg` -/

/-- Turn a routine into an algorithm by supplying an initial state and a
readout. -/
def toAlg (R : QRoutine ι σ W) (init : QBasis ι σ W → ℂ) (hinit : IsQState init)
    (readout : QBasis ι σ W → O) : QAlg ι σ O W where
  init := init
  init_isQState := hinit
  step := R.step
  step_unitary := R.step_unitary
  readout := readout

/-- **The bridge.**  The algorithm's state after `t` queries is the routine's
operator applied to the initial state. -/
lemma toAlg_state (R : QRoutine ι σ W) (init : QBasis ι σ W → ℂ)
    (hinit : IsQState init) (readout : QBasis ι σ W → O) (a : ι → σ) (t : ℕ) :
    (R.toAlg init hinit readout).state a t = R.runUpto a t *ᵥ init := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [QAlg.state_succ, ih, runUpto_succ, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rfl

lemma toAlg_state_len (R : QRoutine ι σ W) (init : QBasis ι σ W → ℂ)
    (hinit : IsQState init) (readout : QBasis ι σ W → O) (a : ι → σ) :
    (R.toAlg init hinit readout).state a R.len = R.run a *ᵥ init :=
  R.toAlg_state init hinit readout a R.len

/-! ## Sequencing -/

/-- **Sequencing**: run `R`, then `S`.  The two boundary unitaries are merged,
so the query count is exactly `R.len + S.len`. -/
def comp (R S : QRoutine ι σ W) : QRoutine ι σ W where
  len := R.len + S.len
  step := fun t =>
    if t < R.len then R.step t
    else if t = R.len then S.step 0 * R.step R.len
    else S.step (t - R.len)
  step_unitary := by
    intro t
    split_ifs
    · exact R.step_unitary _
    · exact mul_mem (S.step_unitary 0) (R.step_unitary _)
    · exact S.step_unitary _

@[simp] lemma comp_len (R S : QRoutine ι σ W) : (R.comp S).len = R.len + S.len := rfl

lemma comp_step_of_lt (R S : QRoutine ι σ W) {t : ℕ} (h : t < R.len) :
    (R.comp S).step t = R.step t := by
  show (if t < R.len then _ else _) = _
  rw [if_pos h]

lemma comp_step_self (R S : QRoutine ι σ W) :
    (R.comp S).step R.len = S.step 0 * R.step R.len := by
  show (if R.len < R.len then _ else if R.len = R.len then _ else _) = _
  rw [if_neg (lt_irrefl _), if_pos rfl]

lemma comp_step_of_gt (R S : QRoutine ι σ W) {t : ℕ} (h : R.len < t) :
    (R.comp S).step t = S.step (t - R.len) := by
  show (if t < R.len then _ else if t = R.len then _ else _) = _
  rw [if_neg (by omega), if_neg (by omega)]

lemma comp_runUpto_of_lt (R S : QRoutine ι σ W) (a : ι → σ) {t : ℕ}
    (ht : t < R.len) : (R.comp S).runUpto a t = R.runUpto a t :=
  runUpto_congr a fun _ hk => comp_step_of_lt R S (lt_of_le_of_lt hk ht)

lemma comp_runUpto_len (R S : QRoutine ι σ W) (a : ι → σ) :
    (R.comp S).runUpto a R.len = S.step 0 * R.runUpto a R.len := by
  rcases Nat.eq_zero_or_pos R.len with h0 | hpos
  · calc (R.comp S).runUpto a R.len
        = (R.comp S).step R.len := by rw [h0]; rfl
      _ = S.step 0 * R.step R.len := comp_step_self R S
      _ = S.step 0 * R.runUpto a R.len := by rw [h0]; rfl
  · obtain ⟨m, hm⟩ : ∃ m, R.len = m + 1 := ⟨R.len - 1, by omega⟩
    have hlt : m < R.len := by omega
    calc (R.comp S).runUpto a R.len
        = (R.comp S).step R.len * (oracleMat a * (R.comp S).runUpto a m) := by
          rw [hm]
          rfl
      _ = (S.step 0 * R.step R.len) * (oracleMat a * R.runUpto a m) := by
          rw [comp_step_self, comp_runUpto_of_lt R S a hlt]
      _ = S.step 0 * (R.step R.len * (oracleMat a * R.runUpto a m)) := by
          rw [Matrix.mul_assoc]
      _ = S.step 0 * R.runUpto a R.len := by
          rw [hm]
          rfl

lemma comp_runUpto_add (R S : QRoutine ι σ W) (a : ι → σ) (k : ℕ) :
    (R.comp S).runUpto a (R.len + k) = S.runUpto a k * R.run a := by
  induction k with
  | zero => simpa [run] using comp_runUpto_len R S a
  | succ k ih =>
      have hgt : R.len < R.len + (k + 1) := by omega
      have hsub : R.len + (k + 1) - R.len = k + 1 := by omega
      calc (R.comp S).runUpto a (R.len + (k + 1))
          = (R.comp S).step (R.len + (k + 1))
              * (oracleMat a * (R.comp S).runUpto a (R.len + k)) := by
            rw [show R.len + (k + 1) = (R.len + k) + 1 from by omega]
            rfl
        _ = S.step (k + 1) * (oracleMat a * (S.runUpto a k * R.run a)) := by
            rw [comp_step_of_gt R S hgt, hsub, ih]
        _ = (S.step (k + 1) * (oracleMat a * S.runUpto a k)) * R.run a := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc]
        _ = S.runUpto a (k + 1) * R.run a := by rw [runUpto_succ]

/-- **Sequencing, at the level of operators.** -/
theorem comp_run (R S : QRoutine ι σ W) (a : ι → σ) :
    (R.comp S).run a = S.run a * R.run a :=
  comp_runUpto_add R S a S.len

/-! ## Padding by two

Padding by an *even* number of queries is free and needs no extra workspace: the
oracle is an involution, so a query immediately followed by a query is the
identity.  Padding by *one* is a different matter — it needs somewhere to park
the query index so that the extra query idles — and lives in `Control.lean`. -/

/-- Append two queries that cancel. -/
def padTwo (R : QRoutine ι σ W) : QRoutine ι σ W where
  len := R.len + 2
  step := fun t => if t ≤ R.len then R.step t else 1
  step_unitary := by
    intro t
    split_ifs
    · exact R.step_unitary _
    · exact one_mem_qUnitary

@[simp] lemma padTwo_len (R : QRoutine ι σ W) : R.padTwo.len = R.len + 2 := rfl

/-- **Padding by two changes nothing.** -/
theorem padTwo_run (R : QRoutine ι σ W) (a : ι → σ) : R.padTwo.run a = R.run a := by
  have hbase : R.padTwo.runUpto a R.len = R.runUpto a R.len :=
    runUpto_congr a fun k hk => by
      show (if k ≤ R.len then _ else _) = _
      rw [if_pos hk]
  have h1 : R.padTwo.step (R.len + 1) = 1 := by
    show (if R.len + 1 ≤ R.len then _ else _) = _
    rw [if_neg (by omega)]
  have h2 : R.padTwo.step (R.len + 2) = 1 := by
    show (if R.len + 2 ≤ R.len then _ else _) = _
    rw [if_neg (by omega)]
  calc R.padTwo.run a
      = R.padTwo.step (R.len + 2)
          * (oracleMat a * (R.padTwo.step (R.len + 1)
            * (oracleMat a * R.padTwo.runUpto a R.len))) := rfl
    _ = oracleMat a * (oracleMat a * R.runUpto a R.len) := by
        rw [h1, h2, hbase, Matrix.one_mul, Matrix.one_mul]
    _ = (oracleMat a * oracleMat a) * R.runUpto a R.len := by rw [Matrix.mul_assoc]
    _ = R.run a := by rw [oracleMat_mul_self, Matrix.one_mul]; rfl

/-! ## Inversion

The oracle is an involution with real entries, so it is self-adjoint; reversing
a schedule therefore costs no extra queries.  That is the content of the
`Oᴴ = O` step below, and it is the reason the value oracle was chosen to be a
transposition in the first place. -/

lemma oracleMat_conjTranspose (a : ι → σ) :
    (oracleMat (W := W) a)ᴴ = oracleMat a := by
  have h1 : (oracleMat (W := W) a)ᴴ * oracleMat a = 1 :=
    conjTranspose_mul_self_of_unitary (oracleMat_mem_unitaryGroup a)
  have h2 : oracleMat (W := W) a * oracleMat a = 1 := oracleMat_mul_self a
  calc (oracleMat (W := W) a)ᴴ
      = (oracleMat a)ᴴ * 1 := by rw [Matrix.mul_one]
    _ = (oracleMat a)ᴴ * (oracleMat a * oracleMat a) := by rw [h2]
    _ = ((oracleMat a)ᴴ * oracleMat a) * oracleMat a := by rw [Matrix.mul_assoc]
    _ = oracleMat a := by rw [h1, Matrix.one_mul]

/-- A single-query routine, used to peel the last query off a schedule. -/
private def lastQuery (U V : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) : QRoutine ι σ W where
  len := 1
  step := fun t => if t = 0 then V else U
  step_unitary := by
    intro t
    split_ifs
    · exact hV
    · exact hU

private lemma lastQuery_run (U V) (hU) (hV) (a : ι → σ) :
    (lastQuery (W := W) U V hU hV).run a = U * (oracleMat a * V) := rfl

/-- **Inversion.**  Every routine has an inverse routine of the same length. -/
theorem exists_inv (R : QRoutine ι σ W) :
    ∃ R' : QRoutine ι σ W, R'.len = R.len ∧ ∀ a, R'.run a = (R.run a)ᴴ := by
  obtain ⟨n, hn⟩ : ∃ n, R.len = n := ⟨R.len, rfl⟩
  induction n generalizing R with
  | zero =>
      refine ⟨⟨0, fun _ => (R.step 0)ᴴ, fun _ => ?_⟩, hn.symm, fun a => ?_⟩
      · exact conjTranspose_mem_qUnitary (R.step_unitary 0)
      · rw [run, run, hn]
        rfl
  | succ m ih =>
      -- peel the last query: `R = P` then one query and `R.step (m+1)`
      let P : QRoutine ι σ W := ⟨m, R.step, R.step_unitary⟩
      let Q : QRoutine ι σ W :=
        lastQuery (R.step (m + 1)) 1 (R.step_unitary (m + 1)) one_mem_qUnitary
      have hP : ∀ a : ι → σ, P.run a = R.runUpto a m :=
        fun a => runUpto_congr a fun _ _ => rfl
      have hPQ : ∀ a, R.run a = Q.run a * P.run a := by
        intro a
        rw [hP, lastQuery_run, run, hn, runUpto_succ, Matrix.mul_one,
          Matrix.mul_assoc]
      obtain ⟨P', hP'len, hP'⟩ := ih P rfl
      -- the inverse of one query is one query
      let Q' : QRoutine ι σ W :=
        lastQuery 1 (R.step (m + 1))ᴴ one_mem_qUnitary
          (conjTranspose_mem_qUnitary (R.step_unitary (m + 1)))
      have hQ' : ∀ a, Q'.run a = (Q.run a)ᴴ := by
        intro a
        rw [lastQuery_run, lastQuery_run, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_mul, Matrix.conjTranspose_one, oracleMat_conjTranspose,
          Matrix.one_mul, Matrix.one_mul]
      refine ⟨Q'.comp P', ?_, fun a => ?_⟩
      · have hPm : P'.len = m := hP'len
        show 1 + P'.len = R.len
        rw [hPm, hn]
        omega
      · rw [comp_run, hP', hQ', hPQ a, Matrix.conjTranspose_mul]

/-! ## Zero-query constructors, and an explicit inverse -/

/-- A zero-query routine: just a unitary. -/
def ofUnitary (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) : QRoutine ι σ W where
  len := 0
  step := fun _ => U
  step_unitary := fun _ => hU

@[simp] lemma ofUnitary_len (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) : (ofUnitary U hU).len = 0 := rfl

@[simp] lemma ofUnitary_run (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) (a : ι → σ) :
    (ofUnitary U hU).run a = U := rfl

/-- The zero-query identity routine. -/
def identity : QRoutine ι σ W := ofUnitary 1 one_mem_qUnitary

@[simp] lemma identity_len : (identity : QRoutine ι σ W).len = 0 := rfl

@[simp] lemma identity_run (a : ι → σ) :
    (identity : QRoutine ι σ W).run a = 1 := rfl

/-- **The one-query routine**: a single bare oracle call. -/
def query : QRoutine ι σ W where
  len := 1
  step := fun _ => 1
  step_unitary := fun _ => one_mem_qUnitary

@[simp] lemma query_len : (query : QRoutine ι σ W).len = 1 := rfl

@[simp] lemma query_run (a : ι → σ) :
    (query : QRoutine ι σ W).run a = oracleMat a := by
  show (1 : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) * (oracleMat a * 1) = oracleMat a
  rw [Matrix.one_mul, Matrix.mul_one]

/-- **An explicit inverse routine**, chosen once from `exists_inv`. -/
noncomputable def inv (R : QRoutine ι σ W) : QRoutine ι σ W := R.exists_inv.choose

@[simp] lemma inv_len (R : QRoutine ι σ W) : R.inv.len = R.len :=
  R.exists_inv.choose_spec.1

@[simp] lemma inv_run (R : QRoutine ι σ W) (a : ι → σ) :
    R.inv.run a = (R.run a)ᴴ := R.exists_inv.choose_spec.2 a

/-! ## Conjugation and iteration -/

/-- **Conjugate a fixed unitary by a routine**: run `R`, apply `U`, run `R`
backwards.  Costs `2 · R.len` queries — no more, because inversion is free. -/
noncomputable def conjFixed (R : QRoutine ι σ W)
    (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) : QRoutine ι σ W :=
  (R.comp (ofUnitary U hU)).comp R.inv

@[simp] lemma conjFixed_len (R : QRoutine ι σ W)
    (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) :
    (R.conjFixed U hU).len = 2 * R.len := by
  show R.len + 0 + R.inv.len = 2 * R.len
  rw [inv_len]
  omega

theorem conjFixed_run (R : QRoutine ι σ W)
    (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) (a : ι → σ) :
    (R.conjFixed U hU).run a = (R.run a)ᴴ * (U * R.run a) := by
  rw [conjFixed, comp_run, comp_run, ofUnitary_run, inv_run]

/-- **Run `R` `n` times in sequence.** -/
def iterate (R : QRoutine ι σ W) : ℕ → QRoutine ι σ W
  | 0 => identity
  | n + 1 => (R.iterate n).comp R

@[simp] lemma iterate_len (R : QRoutine ι σ W) (n : ℕ) :
    (R.iterate n).len = n * R.len := by
  induction n with
  | zero =>
      show (0 : ℕ) = 0 * R.len
      omega
  | succ n ih =>
      show (R.iterate n).len + R.len = (n + 1) * R.len
      rw [ih]
      ring

theorem iterate_run (R : QRoutine ι σ W) (a : ι → σ) (n : ℕ) :
    (R.iterate n).run a = (R.run a) ^ n := by
  induction n with
  | zero =>
      show (1 : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) = (R.run a) ^ 0
      rw [pow_zero]
  | succ n ih =>
      show ((R.iterate n).comp R).run a = _
      rw [comp_run, ih, pow_succ']

end QRoutine

section
variable {ι σ O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [DecidableEq O]

/-- The same bridge read backwards: an algorithm's state is the run of the
routine formed from its own steps. -/
lemma state_eq_runUpto2 {W : Type} [Fintype W] [DecidableEq W]
    (A : QAlg ι σ O W) (n : ℕ) (a : ι → σ) (t : ℕ) :
    A.state a t
      = (QRoutine.mk n A.step A.step_unitary).runUpto a t *ᵥ A.init := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [QAlg.state_succ, ih, QRoutine.runUpto_succ, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, Matrix.mul_assoc]

end


end QuantumQueryComplexity
