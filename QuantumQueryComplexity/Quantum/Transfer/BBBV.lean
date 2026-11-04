import QuantumQueryComplexity.Quantum.Transfer.Comparison
import QuantumQueryComplexity.Quantum.JointState.Conditioning

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The BBBV search bound from the comparison theorem

A validation of the comparison interface (Theorem 4.1) on unstructured search
[BBBV97].  The negative distribution is the point mass on the all-zeros input `0ᵐ`, and the
positive distribution is uniform over the inputs `δᵢ` with a single one at `i`.  The comparison
map is `Υ|0ᵐ⟩ = m^{-1/2} ∑ᵢ |δᵢ⟩`.  Every negative phase query is the identity, so
`Q⁺ₑΥ − ΥQ⁻ₑ = (Q⁺ₑ − 1)Υ` is `−2 m^{-1/2}` from `0ᵐ` to `δₑ` and zero elsewhere.  This gives
`αₑ = 4/m` and `βₑ = 0` for every workspace.  One query verifies an output `i` by reading bit `i`.
Theorem 4.1 then gives `√σ ≤ (t + 1) · 2/√m` for every `t`-query XOR algorithm, the
`Ω(√m)` search lower bound.

## Main definitions

* `searchInput i` — the input `δᵢ`.
* `bbbvMap` — the comparison map.
* `searchVerifier` — the one-query verifier.

## Main results

* `bbbvMap_mulVec_ket`, `compBound_bbbvMap` — the hypotheses of Theorem 4.1, with
  `αₑ = 4/m` and `βₑ = 0`.
* `sqrt_avgXorSuccessProb_search_le` — `√σ ≤ (t + 1) · 2/√m` (XOR model).
* `sqrt_avgSuccessProb_search_le` — `√σ ≤ (2q + 1) · 2/√m` (value oracle).
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι W : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype W] [DecidableEq W]

/-- The search input `δᵢ`, with a single one at `i`. -/
def searchInput (i : ι) : ι → Bool := fun j => decide (j = i)

/-- **The BBBV comparison map** `Υ|0ᵐ⟩ = m^{-1/2} ∑ᵢ |δᵢ⟩`, from the point mass on `0ᵐ` to the
uniform distribution on the search inputs. -/
noncomputable def bbbvMap :
    Matrix (FinDist.uniform ι).Supp (FinDist.uniform Unit).Supp ℂ :=
  fun _ _ => (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ)

/-- The unique support point of the point mass on `0ᵐ`. -/
private def uPt : (FinDist.uniform Unit).Supp := ⟨(), by simp⟩

/-- The initial states match: `Υ|0ᵐ⟩ = |ρ⁺⟩`. -/
theorem bbbvMap_mulVec_ket :
    bbbvMap *ᵥ (FinDist.uniform Unit).ket = (FinDist.uniform ι).ket := by
  funext i
  rw [Matrix.mulVec, dotProduct, Fintype.sum_subsingleton _ uPt]
  simp [bbbvMap, FinDist.ket, Real.sqrt_inv]

/-- **The BBBV comparison bound**: (4.1) holds with `αₑ = 4/m` and `βₑ = 0` on every finite
workspace. -/
theorem compBound_bbbvMap (W' : Type) [Fintype W'] [DecidableEq W'] :
    CompBound (FinDist.uniform Unit) (fun y : (FinDist.uniform ι).Supp => searchInput y.1)
      (fun _ _ => false) bbbvMap (fun _ => 4 / (Fintype.card ι : ℝ)) (fun _ => 0) W' := by
  intro e f
  have hm : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hrow : ∀ i : (FinDist.uniform ι).Supp,
      (phaseComm (fun y : (FinDist.uniform ι).Supp => searchInput y.1)
        (fun x : (FinDist.uniform Unit).Supp => (fun _ _ => false : Unit → ι → Bool) x)
        bbbvMap e * f) i
      = ((if e = i.1 then -2 * (Real.sqrt (Fintype.card ι : ℝ))⁻¹ else 0 : ℝ) : ℂ) • f uPt := by
    intro i
    funext w
    rw [Matrix.mul_apply, Fintype.sum_subsingleton _ uPt]
    split_ifs with h
    · simp [phaseComm, readPhase, bbbvMap, searchInput, Matrix.diagonal_mul, h]
      ring
    · simp [phaseComm, readPhase, bbbvMap, searchInput, Matrix.diagonal_mul, h]
  have hsq : Real.sqrt (Fintype.card ι : ℝ) ^ 2 = Fintype.card ι := Real.sq_sqrt hm.le
  have hi : 0 < (FinDist.uniform ι).mass e := by simp [hm]
  have hlhs : jNormSq (phaseComm (fun y : (FinDist.uniform ι).Supp => searchInput y.1)
        (fun x : (FinDist.uniform Unit).Supp => (fun _ _ => false : Unit → ι → Bool) x)
        bbbvMap e * f) = 4 / (Fintype.card ι : ℝ) * qNormSq (f uPt) := by
    rw [jNormSq, Finset.sum_eq_single (⟨e, hi⟩ : (FinDist.uniform ι).Supp)]
    · rw [hrow, qNormSq_smul]
      simp only [↓reduceIte, Complex.normSq_ofReal]
      field_simp
      rw [hsq]
      ring
    · intro b _ hb
      have hne : e ≠ b.1 := fun h => hb (Subtype.ext h.symm)
      rw [hrow]
      simp [hne]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hf : jNormSq f = qNormSq (f uPt) := by
    rw [jNormSq, Fintype.sum_subsingleton _ uPt]
  rw [hlhs, hf, zero_mul, add_zero]

/-- The one-query verifier for search: read bit `o` of the input, accept iff it is one. -/
def searchVerifier : Verifier ι ι 1 where
  qry o _ := o
  dec _ b := b 0

/-- The constant of Theorem 4.1 for search: `√(maxₑ 4/m + ∑ₑ 0) = 2/√m`. -/
private lemma sqrt_bbbv_const :
    Real.sqrt ((⨆ _ : ι, 4 / (Fintype.card ι : ℝ)) + ∑ _ : ι, (0 : ℝ))
      = 2 / Real.sqrt (Fintype.card ι : ℝ) := by
  rw [ciSup_const, Finset.sum_const_zero, add_zero, Real.sqrt_div (by norm_num),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- **The BBBV bound** (XOR model): a `t`-query algorithm outputs the marked index of a
uniformly random search input with probability `σ`, where `√σ ≤ (t + 1) · 2/√m`. -/
theorem sqrt_avgXorSuccessProb_search_le (A : QAlg ι Bool ι W) (t : ℕ) :
    Real.sqrt ((FinDist.uniform ι).avgXorSuccessProb A t searchInput (fun i o => o = i))
      ≤ ((t : ℝ) + 1) * (2 / Real.sqrt (Fintype.card ι : ℝ)) := by
  have h := theorem_4_1 (FinDist.uniform Unit) (fun _ _ => false) (FinDist.uniform ι)
    searchInput (fun i o => o = i) bbbvMap bbbvMap_mulVec_ket
    (α := fun _ => 4 / (Fintype.card ι : ℝ)) (β := fun _ => 0) (fun _ => by positivity)
    (fun _ => le_rfl) searchVerifier
    (fun y o ho => by simp [Verifier.accepts, searchVerifier, searchInput, ho])
    (fun x o => by simp [Verifier.accepts, searchVerifier]) A t (compBound_bbbvMap _)
  simpa only [Nat.cast_one, sqrt_bbbv_const] using h

/-- **The BBBV bound** (value oracle): with `q` queries, `√σ ≤ (2q + 1) · 2/√m`. -/
theorem sqrt_avgSuccessProb_search_le (A : QAlg ι Bool ι W) (q : ℕ) :
    Real.sqrt ((FinDist.uniform ι).avgSuccessProb A q searchInput (fun i o => o = i))
      ≤ (2 * (q : ℝ) + 1) * (2 / Real.sqrt (Fintype.card ι : ℝ)) := by
  have h := theorem_4_1_std (FinDist.uniform Unit) (fun _ _ => false) (FinDist.uniform ι)
    searchInput (fun i o => o = i) bbbvMap bbbvMap_mulVec_ket
    (α := fun _ => 4 / (Fintype.card ι : ℝ)) (β := fun _ => 0) (fun _ => by positivity)
    (fun _ => le_rfl) searchVerifier
    (fun y o ho => by simp [Verifier.accepts, searchVerifier, searchInput, ho])
    (fun x o => by simp [Verifier.accepts, searchVerifier]) A q (compBound_bbbvMap _)
  simpa only [Nat.cast_one, sqrt_bbbv_const] using h

end QuantumQueryComplexity
