import QuantumQueryComplexity.Scan.Weighted
import QuantumQueryComplexity.CoordRecode
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# A maximum with a per-coordinate value map

`QuantumQueryComplexity/Scan/Weighted.lean` maximises `m (x j)` over `j` for one value map
`m : σ → A`.  A divide-and-conquer node needs the coordinates to be read
through *different* maps: slot `ℓ` of the node's maximum reads its own child's
joint output and adds its own constant offset, so the value
map is a family `m : ι → σ → A` and the quantity is

  `max_j m_j (x_j)`.

No new scan analysis is needed.  Tagging each letter with its coordinate,
`Ψ i s = (i, s)`, is a coordinate-wise injection into the enlarged alphabet
`ι × σ`, and under it the family collapses to the single map
`m' (i, s) = m_i s`.  `DualPair.coordRecode` transports the solution back at
the same weighted cost, so the bound is again `16 √(∑ᵢ cᵢ²)`.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Type*} [Fintype A] [DecidableEq A] [LinearOrder A]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- **`ADV±_c(MAX) ≤ 16 √(∑ᵢ cᵢ²)` with a per-coordinate value map.** -/
theorem exists_maxMapFam_dual_isWeightedCostLe (m : ι → σ → A) (c : ι → ℝ)
    (hc : ∀ i, 0 < c i) :
    ∃ P : DualPair (Order ι × ScanDim ι A (WithBot A))
      (fun x : ι → σ => maxFun fun j => m j (x j)),
      P.IsWeightedCostLe c (16 * costNorm c) := by
  classical
  obtain ⟨P, hP⟩ := exists_maxMap_dual_isWeightedCostLe (ι := ι) (A := A)
    (σ := ι × σ) (fun p => m p.1 p.2) c hc
  have hinj : ∀ i : ι, Function.Injective (fun s : σ => (i, s)) :=
    fun i a b h => congrArg Prod.snd h
  exact ⟨P.coordRecode hinj, DualPair.coordRecode_isWeightedCostLe hinj P hP⟩

end QuantumQueryComplexity
