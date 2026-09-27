import QuantumQueryComplexity.Quantum.Postcomp

/-!
# Reading one Boolean input coordinate

The primitive projection algorithm returns an `Option Bool`, since its answer
register includes a blank value. Classical postprocessing gives an ordinary
Boolean output without another query. Correctness then bounds query complexity.
-/

namespace QuantumQueryExamples

open QuantumQueryComplexity

/-- Read the first coordinate of a nonempty Boolean input. -/
noncomputable def firstBit (n : ℕ) : QAlg (Fin (n + 1)) Bool Bool Unit :=
  (projAlg Bool 0).postcomp (fun bit => bit.getD false)

/-- The algorithm returns the first bit exactly, after one query. -/
theorem firstBit_correct (n : ℕ) :
    ComputesWithErrorOn (firstBit n) 1 id (fun x => x 0) 0 := by
  have h := (computesWithErrorOn_proj
    (id : (Fin (n + 1) → Bool) → Fin (n + 1) → Bool) 0
    (le_refl (0 : ℝ))).postcomp (fun bit : Option Bool => bit.getD false)
  simpa [firstBit] using h

/-- A concrete algorithm certifies an upper bound on the minimum query count. -/
theorem firstBit_query_bound (n : ℕ) :
    qQuery (fun x : Fin (n + 1) → Bool => x 0) 0 ≤ 1 :=
  qQueryOn_le (firstBit_correct n)

end QuantumQueryExamples
