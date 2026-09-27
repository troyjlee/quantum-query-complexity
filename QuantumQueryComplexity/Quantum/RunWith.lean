import QuantumQueryComplexity.Quantum.Routine
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Running a routine against an arbitrary oracle matrix

`QRoutine.runUpto` interleaves a routine's steps with the transposition
oracle `oracleMat a`; nothing in the interleaving or in sequencing uses any
property of that matrix.  This file states the run **parametrically in the
oracle**: `runWith Q t` interleaves the opaque matrix `Q`, and

    runUpto a t  =  runWith (oracleMat a) t

recovers the standard semantics.  The payoff is the oracle-simulation layer:
the XOR-model run is `runWith (xorOracleMat a)`, and the composition law
`comp_runWith` — the mirror of `comp_run`, proved once here — serves both
models, so the gadget compilers of `Simulation.lean` can be built with
`QRoutine.comp` in either semantics.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

namespace QRoutine

variable (Q : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)

/-- The operator implemented by the first `t` queries of `R`, with the opaque
oracle matrix `Q` in place of the transposition oracle. -/
def runWith (R : QRoutine ι σ W) : ℕ → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ
  | 0 => R.step 0
  | t + 1 => R.step (t + 1) * (Q * R.runWith t)

@[simp] lemma runWith_zero (R : QRoutine ι σ W) : R.runWith Q 0 = R.step 0 := rfl

@[simp] lemma runWith_succ (R : QRoutine ι σ W) (t : ℕ) :
    R.runWith Q (t + 1) = R.step (t + 1) * (Q * R.runWith Q t) := rfl

/-- The standard semantics is the transposition-oracle instance. -/
lemma runUpto_eq_runWith (R : QRoutine ι σ W) (a : ι → σ) (t : ℕ) :
    R.runUpto a t = R.runWith (oracleMat a) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [runUpto_succ, runWith_succ, ih]

lemma run_eq_runWith (R : QRoutine ι σ W) (a : ι → σ) :
    R.run a = R.runWith (oracleMat a) R.len :=
  runUpto_eq_runWith R a R.len

lemma runWith_mem_unitaryGroup (R : QRoutine ι σ W)
    (hQ : Q ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) (t : ℕ) :
    R.runWith Q t ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ := by
  induction t with
  | zero => exact R.step_unitary 0
  | succ t ih => exact mul_mem (R.step_unitary (t + 1)) (mul_mem hQ ih)

/-- Only the steps up to `t` matter. -/
lemma runWith_congr {R S : QRoutine ι σ W} {t : ℕ}
    (h : ∀ k, k ≤ t → R.step k = S.step k) : R.runWith Q t = S.runWith Q t := by
  induction t with
  | zero => exact h 0 le_rfl
  | succ t ih =>
      rw [runWith_succ, runWith_succ, h (t + 1) le_rfl,
        ih (fun k hk => h k (le_trans hk (Nat.le_succ t)))]

/-! ## Sequencing, parametrically -/

lemma comp_runWith_of_lt (R S : QRoutine ι σ W) {t : ℕ}
    (ht : t < R.len) : (R.comp S).runWith Q t = R.runWith Q t :=
  runWith_congr Q fun _ hk => comp_step_of_lt R S (lt_of_le_of_lt hk ht)

lemma comp_runWith_len (R S : QRoutine ι σ W) :
    (R.comp S).runWith Q R.len = S.step 0 * R.runWith Q R.len := by
  rcases Nat.eq_zero_or_pos R.len with h0 | hpos
  · calc (R.comp S).runWith Q R.len
        = (R.comp S).step R.len := by rw [h0]; rfl
      _ = S.step 0 * R.step R.len := comp_step_self R S
      _ = S.step 0 * R.runWith Q R.len := by rw [h0]; rfl
  · obtain ⟨m, hm⟩ : ∃ m, R.len = m + 1 := ⟨R.len - 1, by omega⟩
    have hlt : m < R.len := by omega
    calc (R.comp S).runWith Q R.len
        = (R.comp S).step R.len * (Q * (R.comp S).runWith Q m) := by
          rw [hm]
          rfl
      _ = (S.step 0 * R.step R.len) * (Q * R.runWith Q m) := by
          rw [comp_step_self, comp_runWith_of_lt Q R S hlt]
      _ = S.step 0 * (R.step R.len * (Q * R.runWith Q m)) := by
          rw [Matrix.mul_assoc]
      _ = S.step 0 * R.runWith Q R.len := by
          rw [hm]
          rfl

lemma comp_runWith_add (R S : QRoutine ι σ W) (k : ℕ) :
    (R.comp S).runWith Q (R.len + k)
      = S.runWith Q k * R.runWith Q R.len := by
  induction k with
  | zero => simpa using comp_runWith_len Q R S
  | succ k ih =>
      have hgt : R.len < R.len + (k + 1) := by omega
      have hsub : R.len + (k + 1) - R.len = k + 1 := by omega
      calc (R.comp S).runWith Q (R.len + (k + 1))
          = (R.comp S).step (R.len + (k + 1))
              * (Q * (R.comp S).runWith Q (R.len + k)) := by
            rw [show R.len + (k + 1) = (R.len + k) + 1 from by omega]
            rfl
        _ = S.step (k + 1) * (Q * (S.runWith Q k * R.runWith Q R.len)) := by
            rw [comp_step_of_gt R S hgt, hsub, ih]
        _ = (S.step (k + 1) * (Q * S.runWith Q k)) * R.runWith Q R.len := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc]
        _ = S.runWith Q (k + 1) * R.runWith Q R.len := by rw [runWith_succ]

/-- **Sequencing against any oracle**: the mirror of `comp_run`. -/
theorem comp_runWith_full (R S : QRoutine ι σ W) :
    (R.comp S).runWith Q (R.len + S.len)
      = S.runWith Q S.len * R.runWith Q R.len :=
  comp_runWith_add Q R S S.len

@[simp] lemma ofUnitary_runWith (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) :
    (ofUnitary U hU).runWith Q 0 = U := rfl

end QRoutine

end QuantumQueryComplexity
