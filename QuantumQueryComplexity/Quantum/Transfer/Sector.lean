import QuantumQueryComplexity.Quantum.JointState.Oracle

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Sector accounting for one query

The error of a comparison map `K` under one joint query splits over the query sectors
[CGZ, proof of Theorem 4.1].  In the phase model the oracle is the identity off the sectors and
acts by the phase query `Qₑ` on sector `e`.  `K` acts on the input register only, so it preserves
the index and answer registers, and

  `‖(O⁺K − KO⁻) f‖² = ∑ₑ ‖(Q⁺ₑK − KQ⁻ₑ) fₑ‖²`   (`jNormSq_phaseQueryErr`).

In the XOR model the same holds after conjugating by the answer Hadamard
(`jNormSq_xorQueryErr`).  An actual state has `∑ₑ ‖fₑ‖² ≤ 1` and `‖fₑ‖∞ ≤ 1` for every `e`.
So the workspace-uniform bound (4.1), `‖(Q⁺ₑK − KQ⁻ₑ) g‖² ≤ αₑ ‖g‖² + βₑ ‖g‖∞²`, gives the
per-query error `ε² ≤ maxₑ αₑ + ∑ₑ βₑ`, which is CGZ (4.3) (`jNormSq_xorQueryErr_le`).  The
`α`-terms are averaged by the sector weights; the `β`-terms are not, since different inputs may
put their whole amplitude on different query indices.

## Main definitions

* `phaseComm readY readX K e` — the comparison error `Q⁺ₑK − KQ⁻ₑ` of the phase query `e`.
* `CompBound ρ readY readX K α β W` — the bound (4.1) on the workspace `W`.

## Main results

* `jNormSq_phaseQueryErr`, `jNormSq_xorQueryErr` — the sector decomposition.
* `jNormSq_phaseQueryErr_le`, `jNormSq_xorQueryErr_le` — **CGZ (4.3)**.
* `FinDist.jNormSq_xorQueryErr_jointXorState_le` — the same on an actual joint state.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι W X Y : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- **The comparison error of the phase query `e`**, `Q⁺ₑK − KQ⁻ₑ` (CGZ (4.1)). -/
def phaseComm (readY : Y → ι → Bool) (readX : X → ι → Bool) (K : Matrix Y X ℂ) (e : ι) :
    Matrix Y X ℂ :=
  readPhase readY e * K - K * readPhase readX e

/-- A function on the query basis that vanishes off the sectors sums over the sector
coordinates `(e, w) ↦ (some e, some true, w)`. -/
private lemma sum_eq_sum_sector (g : QBasis ι Bool W → ℝ)
    (hg : ∀ p, (∀ e w, p ≠ (some e, some true, w)) → g p = 0) :
    ∑ p, g p = ∑ e, ∑ w, g (some e, some true, w) := by
  have h0 : ∀ t w, g (none, t, w) = 0 := fun t w => hg _ fun e w' h => by simp at h
  have h1 : ∀ e w, g (some e, none, w) = 0 := fun e w => hg _ fun e' w' h => by simp at h
  have h2 : ∀ e w, g (some e, some false, w) = 0 := fun e w => hg _ fun e' w' h => by simp at h
  simp only [Fintype.sum_prod_type, Fintype.sum_option, Fintype.sum_bool, h0, h1, h2,
    Finset.sum_const_zero, zero_add, add_zero]

private lemma sector_sub (f g : JVec X (QBasis ι Bool W)) (e : ι) :
    sector (f - g) e = sector f e - sector g e :=
  rfl

/-- On sector `e`, the phase-query error is `(Q⁺ₑK − KQ⁻ₑ) fₑ`. -/
private lemma sector_phaseQueryErr (readY : Y → ι → Bool) (readX : X → ι → Bool)
    (K : Matrix Y X ℂ) (f : JVec X (QBasis ι Bool W)) (e : ι) :
    sector (jOracle phaseOracleMat readY (K * f) - K * jOracle phaseOracleMat readX f) e
      = phaseComm readY readX K e * sector f e := by
  rw [sector_sub, sector_jOracle_phase, sector_mul, sector_mul, sector_jOracle_phase, phaseComm,
    Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc]

/-- **Sector decomposition of the phase-query error.**  Components outside the sectors
contribute nothing, and errors in distinct sectors are orthogonal. -/
theorem jNormSq_phaseQueryErr (readY : Y → ι → Bool) (readX : X → ι → Bool)
    (K : Matrix Y X ℂ) (f : JVec X (QBasis ι Bool W)) :
    jNormSq (jOracle phaseOracleMat readY (K * f) - K * jOracle phaseOracleMat readX f)
      = ∑ e, jNormSq (phaseComm readY readX K e * sector f e) := by
  set D := jOracle phaseOracleMat readY (K * f) - K * jOracle phaseOracleMat readX f with hD
  have hoff : ∀ y p, (∀ e w, p ≠ (some e, some true, w)) → D y p = 0 := by
    intro y p hp
    rw [hD, Matrix.sub_apply, jOracle_phase_apply_of_not_sector _ _ _ _ hp, Matrix.mul_apply,
      Matrix.mul_apply, sub_eq_zero]
    exact Finset.sum_congr rfl fun x _ => by rw [jOracle_phase_apply_of_not_sector _ _ _ _ hp]
  simp only [jNormSq, qNormSq_def]
  rw [Finset.sum_comm, sum_eq_sum_sector (fun p => ∑ y, Complex.normSq (D y p))
    fun p hp => Finset.sum_eq_zero fun y _ => by rw [hoff y p hp, map_zero]]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm, ← sector_phaseQueryErr]
  rfl

private lemma wsOp_sub {A : Type} [Fintype A] [DecidableEq A] (U : Matrix A A ℂ)
    (f g : JVec X A) : wsOp U (f - g) = wsOp U f - wsOp U g := by
  rw [wsOp_eq_mul_transpose, wsOp_eq_mul_transpose, wsOp_eq_mul_transpose, Matrix.sub_mul]

/-- **The XOR-query error is the phase-query error of the Hadamard-conjugated vector.** -/
theorem jNormSq_xorQueryErr (readY : Y → ι → Bool) (readX : X → ι → Bool)
    (K : Matrix Y X ℂ) (f : JVec X (QBasis ι Bool W)) :
    jNormSq (jOracle xorOracleMat readY (K * f) - K * jOracle xorOracleMat readX f)
      = jNormSq (jOracle phaseOracleMat readY (K * wsOp hadAns f)
          - K * jOracle phaseOracleMat readX (wsOp hadAns f)) := by
  rw [jOracle_xor_eq_hadAns_phase, jOracle_xor_eq_hadAns_phase, mul_wsOp, ← wsOp_sub,
    jNormSq_wsOp_of_mem_unitaryGroup hadAns_mem_unitaryGroup, ← mul_wsOp K hadAns f]

section Bound

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- **The comparison bound (4.1) on the workspace `W`**: for every query index `e` and every
joint vector `f` on `W`, `‖(Q⁺ₑK − KQ⁻ₑ) f‖² ≤ αₑ ‖f‖² + βₑ ‖f‖∞²`, where the infinity norm is
taken over the support of the negative distribution `ρ`. -/
def CompBound (ρ : FinDist Ω) (readY : Y → ι → Bool) (readX : Ω → ι → Bool)
    (K : Matrix Y ρ.Supp ℂ) (α β : ι → ℝ) (W : Type) [Fintype W] [DecidableEq W] : Prop :=
  ∀ (e : ι) (f : JVec ρ.Supp W),
    jNormSq (phaseComm readY (fun x : ρ.Supp => readX x) K e * f)
      ≤ α e * jNormSq f + β e * ρ.infNormSq f

/-- **Error accounting for one phase query.**  Under (4.1), a vector with `‖f‖ ≤ 1` and
`‖f‖∞ ≤ 1` has phase-query error at most `maxₑ αₑ + ∑ₑ βₑ`. -/
theorem jNormSq_phaseQueryErr_le (ρ : FinDist Ω) (readY : Y → ι → Bool)
    (readX : Ω → ι → Bool) (K : Matrix Y ρ.Supp ℂ) {α β : ι → ℝ} (hα : ∀ e, 0 ≤ α e)
    (hβ : ∀ e, 0 ≤ β e) (h41 : CompBound ρ readY readX K α β W)
    (f : JVec ρ.Supp (QBasis ι Bool W)) (hf : jNormSq f ≤ 1) (hf' : ρ.infNormSq f ≤ 1) :
    jNormSq (jOracle phaseOracleMat readY (K * f)
        - K * jOracle phaseOracleMat (fun x : ρ.Supp => readX x) f)
      ≤ (⨆ e, α e) + ∑ e, β e := by
  rw [jNormSq_phaseQueryErr]
  have hbdd : BddAbove (Set.range α) := (Set.finite_range α).bddAbove
  have hM : 0 ≤ ⨆ e, α e := Real.iSup_nonneg hα
  calc ∑ e, jNormSq (phaseComm readY (fun x : ρ.Supp => readX x) K e * sector f e)
      ≤ ∑ e, (α e * jNormSq (sector f e) + β e * ρ.infNormSq (sector f e)) :=
        Finset.sum_le_sum fun e _ => h41 e (sector f e)
    _ ≤ ∑ e, ((⨆ e, α e) * jNormSq (sector f e) + β e) := by
        refine Finset.sum_le_sum fun e _ => add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_right (le_ciSup hbdd e) (jNormSq_nonneg _)
        · exact mul_le_of_le_one_right (hβ e) ((ρ.infNormSq_sector_le f e).trans hf')
    _ = (⨆ e, α e) * ∑ e, jNormSq (sector f e) + ∑ e, β e := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (⨆ e, α e) + ∑ e, β e := by
        gcongr
        exact mul_le_of_le_one_right hM ((sum_jNormSq_sector_le f).trans hf)

/-- **Error accounting for one XOR query (CGZ (4.3)).** -/
theorem jNormSq_xorQueryErr_le (ρ : FinDist Ω) (readY : Y → ι → Bool)
    (readX : Ω → ι → Bool) (K : Matrix Y ρ.Supp ℂ) {α β : ι → ℝ} (hα : ∀ e, 0 ≤ α e)
    (hβ : ∀ e, 0 ≤ β e) (h41 : CompBound ρ readY readX K α β W)
    (f : JVec ρ.Supp (QBasis ι Bool W)) (hf : jNormSq f ≤ 1) (hf' : ρ.infNormSq f ≤ 1) :
    jNormSq (jOracle xorOracleMat readY (K * f)
        - K * jOracle xorOracleMat (fun x : ρ.Supp => readX x) f)
      ≤ (⨆ e, α e) + ∑ e, β e := by
  rw [jNormSq_xorQueryErr]
  exact jNormSq_phaseQueryErr_le ρ readY readX K hα hβ h41 (wsOp hadAns f)
    (by rwa [jNormSq_wsOp_of_mem_unitaryGroup hadAns_mem_unitaryGroup])
    (by rwa [ρ.infNormSq_wsOp_of_mem_unitaryGroup hadAns_mem_unitaryGroup])

/-- **CGZ (4.3) on an actual joint state**: before every query, the comparison error is at most
`maxₑ αₑ + ∑ₑ βₑ`. -/
theorem FinDist.jNormSq_xorQueryErr_jointXorState_le {O : Type} (ρ : FinDist Ω)
    (readY : Y → ι → Bool) (readX : Ω → ι → Bool) (K : Matrix Y ρ.Supp ℂ) {α β : ι → ℝ}
    (hα : ∀ e, 0 ≤ α e) (hβ : ∀ e, 0 ≤ β e) (h41 : CompBound ρ readY readX K α β W)
    (A : QAlg ι Bool O W) (j : ℕ) :
    jNormSq (jOracle xorOracleMat readY (K * ρ.jointXorState readX A j)
        - K * jOracle xorOracleMat (fun x : ρ.Supp => readX x) (ρ.jointXorState readX A j))
      ≤ (⨆ e, α e) + ∑ e, β e :=
  jNormSq_xorQueryErr_le ρ readY readX K hα hβ h41 _ (ρ.jNormSq_jointXorState readX A j).le
    (ρ.infNormSq_jointXorState readX A j).le

end Bound

end QuantumQueryComplexity
