import QuantumQueryComplexity.Quantum.Postcomp
import QuantumQueryComplexity.Quantum.Characterization
import QuantumQueryComplexity.Quantum.PlainSimulation
import QuantumQueryComplexity.Quantum.Transducer
import QuantumQueryComplexity.Quantum.DecisionTree

/-! A consumer project uses only public imports from its Lake dependency. -/

open QuantumQueryComplexity

example (n : ℕ) :
    qQuery (fun x : Fin (n + 1) → Bool => x 0) 0 ≤ 1 := by
  have h := (computesWithErrorOn_proj
    (id : (Fin (n + 1) → Bool) → Fin (n + 1) → Bool) 0
    (le_refl (0 : ℝ))).postcomp (fun bit : Option Bool => bit.getD false)
  exact qQueryOn_le (by simpa using h)

example {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → Bool)
    (k : ℕ) (h : 36 * (k : ℝ) ≤ advPM f) : k ≤ boundedErrorQQuery f := by
  have hq := mul_advPM_le_boundedErrorQQuery f
  have hk : (k : ℝ) ≤ (boundedErrorQQuery f : ℝ) := by linarith
  exact_mod_cast hk

example {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (f : (ι → Bool) → Bool) :
    Plain.plainQQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3)
      = xorQQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) :=
  Plain.plainQQueryOn_eq _ _ _

example {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype W]
    [DecidableEq W] (R : QRoutine ι σ W) (priv : QBasis ι σ W → Prop) {K : ℕ} (hK : 0 < K) :
    ∃ T : QRoutine ι σ (ClockWork ι K W), T.len = K * R.len := by
  obtain ⟨T, hT, -⟩ := exists_transducerRoutine R priv hK
  exact ⟨T, hT⟩

example (x : Fin 3 → Bool) :
    (ReadTree.reads 2 ![0, 2] fun v : Fin 2 → Bool => v 0 && v 1).eval x = (x 0 && x 2) := by
  rw [ReadTree.eval_reads]
  rfl
