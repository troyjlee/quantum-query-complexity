import QuantumQueryComplexity.Quantum.Postcomp
import QuantumQueryComplexity.Quantum.Characterization

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
