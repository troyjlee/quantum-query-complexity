import QuantumQueryComplexity.Quantum.Blocks
import QuantumQueryComplexity.Quantum.Routine
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Lifting a routine along a workspace extension

A routine built on workspace `W` runs unchanged on `V × W`: lift every fixed
step with `liftReg`, and the queries pass through because the oracle ignores the
workspace (`blockFam_oracle`).  The query count is unchanged, and on the encoded
subspace the lifted routine does exactly what the original does.

This is what lets a subroutine written for a small workspace be used inside a
circuit that carries extra registers — a phase register, say.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ V W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

namespace QRoutine

/-- **Lift a routine along a workspace extension.** -/
def liftReg (V : Type) [Fintype V] [DecidableEq V] (R : QRoutine ι σ W) :
    QRoutine ι σ (V × W) where
  len := R.len
  step := fun t => QuantumQueryComplexity.liftReg V (R.step t)
  step_unitary := fun t => liftReg_mem_unitaryGroup (R.step_unitary t)

@[simp] lemma liftReg_len (R : QRoutine ι σ W) : (R.liftReg V).len = R.len := rfl

@[simp] lemma liftReg_step (R : QRoutine ι σ W) (t : ℕ) :
    (R.liftReg V).step t = QuantumQueryComplexity.liftReg V (R.step t) := rfl

theorem liftReg_runUpto (R : QRoutine ι σ W) (a : ι → σ) (t : ℕ) :
    (R.liftReg V).runUpto a t = QuantumQueryComplexity.liftReg V (R.runUpto a t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [runUpto_succ, runUpto_succ, liftReg_step, ih, blockFam_oracle (V := V),
        liftReg_mul, liftReg_mul]

theorem liftReg_run (R : QRoutine ι σ W) (a : ι → σ) :
    (R.liftReg V).run a = QuantumQueryComplexity.liftReg V (R.run a) :=
  liftReg_runUpto R a R.len

/-- **The lifted routine acts as the original on the encoded subspace.** -/
theorem liftReg_run_embed (R : QRoutine ι σ W) (a : ι → σ) (v : V)
    (ψ : QBasis ι σ W → ℂ) :
    (R.liftReg V).run a *ᵥ embedReg v ψ = embedReg v (R.run a *ᵥ ψ) := by
  rw [liftReg_run, liftReg_mulVec_embed]

end QRoutine

end QuantumQueryComplexity
