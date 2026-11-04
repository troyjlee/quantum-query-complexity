import QuantumQueryComplexity.Quantum.Transfer.Lemma
import QuantumQueryComplexity.Quantum.Transfer.Sector
import QuantumQueryComplexity.Quantum.Transfer.Endpoint
import QuantumQueryComplexity.Quantum.Transfer.Verifier

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Comparison of computations

**Theorem 4.1** of Cornelissen–Gilani–Zhou [CGZ].  Let `ρm` (negative) and `ρp` (positive) be
input distributions on the same Boolean coordinates `ι`, observed through `readM` and `readP`.
`ρp` may carry hidden labels, in which case `readP` ignores them.  Let `Υ` map the negative input
register to the positive one, with `Υ|ρm⟩ = |ρp⟩`, and suppose the workspace-uniform bound (4.1)

  `‖(Q⁺ₑΥ − ΥQ⁻ₑ) f‖² ≤ αₑ ‖f‖² + βₑ ‖f‖∞²`

with `αₑ, βₑ ≥ 0`.  If outputs can be verified exactly with `v` queries, the verification always
rejecting on negative inputs, then every `t`-query algorithm with average success `σ` under `ρp`
satisfies

  `√σ ≤ (t + v) √(maxₑ αₑ + ∑ₑ βₑ)`.

The proof composes the library pieces: append the verifier (`QAlg.appendVerifier`), apply the
transfer lemma (`jNorm_jointXorState_sub_le`) with the per-query error of CGZ (4.3)
(`FinDist.jNormSq_xorQueryErr_jointXorState_le`), and finish with the exact-verification endpoint
(`FinDist.goodMask_const_mul_eq_zero`).

The comparison bound is needed only on the workspace of the algorithm actually run, the verified
algorithm's `VerWS ι W v`.  A bound proved for every finite workspace, as in the paper, applies
directly.

## Main results

* `sqrt_avgXorSuccessProb_le_of_reject` — the comparison theorem for any computation that never
  accepts on the negative distribution, with an arbitrary initial mismatch `‖|ρp⟩ − Υ|ρm⟩‖`.
* `theorem_4_1` — **CGZ Theorem 4.1**, XOR (equivalently phase) model.
* `theorem_4_1_std` — the same bound for `q` value-oracle queries, at `2q` XOR queries.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι O W Ωm Ωp : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
  [Fintype Ωm] [DecidableEq Ωm] [Fintype Ωp] [DecidableEq Ωp]

/-- **Comparison of computations, rejecting form.**  If `B` never accepts on the support of the
negative distribution after `T` queries, then its average acceptance under the positive
distribution satisfies

  `√σ ≤ ‖|ρp⟩ − Υ|ρm⟩‖ + T √(maxₑ αₑ + ∑ₑ βₑ)`.

The bound (4.1) is assumed only on `B`'s workspace. -/
theorem sqrt_avgXorSuccessProb_le_of_reject (ρm : FinDist Ωm) (readM : Ωm → ι → Bool)
    (ρp : FinDist Ωp) (readP : Ωp → ι → Bool) (Υ : Matrix ρp.Supp ρm.Supp ℂ) {α β : ι → ℝ}
    (hα : ∀ e, 0 ≤ α e) (hβ : ∀ e, 0 ≤ β e) (B : QAlg ι Bool O W)
    (h41 : CompBound ρm (fun y : ρp.Supp => readP y) readM Υ α β W) (acc : O → Prop)
    [DecidablePred acc] (T : ℕ)
    (hrej : ∀ x : ρm.Supp, xorSuccessProbOn B T readM (fun _ => acc) x = 0) :
    Real.sqrt (ρp.avgXorSuccessProb B T readP (fun _ => acc))
      ≤ Real.sqrt (qNormSq (ρp.ket - Υ *ᵥ ρm.ket))
        + T * Real.sqrt ((⨆ e, α e) + ∑ e, β e) := by
  set ε := Real.sqrt ((⨆ e, α e) + ∑ e, β e)
  have hend := FinDist.sqrt_avgXorSuccessProb_le ρp readP (fun _ => acc) B T
    (Υ * ρm.jointXorState readM B T)
  have h0 : ρp.goodMask B.readout (fun _ => acc) (Υ * ρm.jointXorState readM B T) = 0 :=
    FinDist.goodMask_const_mul_eq_zero ρp B.readout acc Υ _
      (FinDist.wsMask_jointXorState_eq_zero ρm readM B T acc hrej)
  rw [h0, jNorm_zero, zero_add] at hend
  have htr := jNorm_jointXorState_sub_le ρm readM ρp readP Υ B (fun _ => ε) T fun j _ =>
    Real.sqrt_le_sqrt (FinDist.jNormSq_xorQueryErr_jointXorState_le ρm
      (fun y : ρp.Supp => readP y) readM Υ hα hβ h41 B j)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at htr
  exact hend.trans htr

/-- **Theorem 4.1 (Comparison of computations)** [CGZ].  Suppose `Υ|ρm⟩ = |ρp⟩`, the bound
(4.1) holds with nonnegative `αₑ, βₑ`, and the relation `Good` is verified by `V` with `v`
queries: `V` accepts every valid output on positive inputs and rejects every output on negative
inputs.  Then every algorithm `A` making `t` XOR queries has average success `σ` under `ρp` with

  `√σ ≤ (t + v) √(maxₑ αₑ + ∑ₑ βₑ)`. -/
theorem theorem_4_1 (ρm : FinDist Ωm) (readM : Ωm → ι → Bool) (ρp : FinDist Ωp)
    (readP : Ωp → ι → Bool) (Good : Ωp → O → Prop) [∀ ω, DecidablePred (Good ω)]
    (Υ : Matrix ρp.Supp ρm.Supp ℂ) (hΥ : Υ *ᵥ ρm.ket = ρp.ket) {α β : ι → ℝ}
    (hα : ∀ e, 0 ≤ α e) (hβ : ∀ e, 0 ≤ β e) {v : ℕ} (V : Verifier ι O v)
    (hcomplete : ∀ y : ρp.Supp, ∀ o, Good y o → V.accepts (readP y) o = true)
    (hsound : ∀ x : ρm.Supp, ∀ o, V.accepts (readM x) o = false) (A : QAlg ι Bool O W)
    (t : ℕ) (h41 : CompBound ρm (fun y : ρp.Supp => readP y) readM Υ α β (VerWS ι W v)) :
    Real.sqrt (ρp.avgXorSuccessProb A t readP Good)
      ≤ ((t : ℝ) + v) * Real.sqrt ((⨆ e, α e) + ∑ e, β e) := by
  have hrej : ∀ x : ρm.Supp,
      xorSuccessProbOn (A.appendVerifier t V) (t + v) readM (fun _ b => b = true) x = 0 :=
    fun x => xorSuccessProbOn_appendVerifier_eq_zero A t V readM x (hsound x)
  have hmain := sqrt_avgXorSuccessProb_le_of_reject ρm readM ρp readP Υ hα hβ
    (A.appendVerifier t V) h41 (fun b : Bool => b = true) (t + v) hrej
  rw [hΥ, sub_self] at hmain
  have hz : qNormSq (0 : ρp.Supp → ℂ) = 0 := by simp [qNormSq_def]
  rw [hz, Real.sqrt_zero, zero_add] at hmain
  push_cast at hmain
  refine le_trans (Real.sqrt_le_sqrt ?_) hmain
  unfold FinDist.avgXorSuccessProb
  refine Finset.sum_le_sum fun ω _ => ?_
  rcases (ρp.mass_nonneg ω).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left
      (xorSuccessProbOn_le_appendVerifier A t V readP Good ω (hcomplete ⟨ω, hpos⟩)) hpos.le

/-- **Theorem 4.1 in the value-oracle model.**  The value-oracle algorithm is simulated with two
XOR queries per query (`QAlg.simToXor`), so `q` value queries give
`√σ ≤ (2q + v) √(maxₑ αₑ + ∑ₑ βₑ)`. -/
theorem theorem_4_1_std [DecidableEq O] (ρm : FinDist Ωm) (readM : Ωm → ι → Bool)
    (ρp : FinDist Ωp) (readP : Ωp → ι → Bool) (Good : Ωp → O → Prop)
    [∀ ω, DecidablePred (Good ω)] (Υ : Matrix ρp.Supp ρm.Supp ℂ) (hΥ : Υ *ᵥ ρm.ket = ρp.ket)
    {α β : ι → ℝ} (hα : ∀ e, 0 ≤ α e) (hβ : ∀ e, 0 ≤ β e) {v : ℕ} (V : Verifier ι O v)
    (hcomplete : ∀ y : ρp.Supp, ∀ o, Good y o → V.accepts (readP y) o = true)
    (hsound : ∀ x : ρm.Supp, ∀ o, V.accepts (readM x) o = false) (A : QAlg ι Bool O W)
    (q : ℕ)
    (h41 : CompBound ρm (fun y : ρp.Supp => readP y) readM Υ α β
      (VerWS ι (Option Bool × W) v)) :
    Real.sqrt (ρp.avgSuccessProb A q readP Good)
      ≤ (2 * (q : ℝ) + v) * Real.sqrt ((⨆ e, α e) + ∑ e, β e) := by
  rw [← avgXorSuccessProb_simToXor]
  have h := theorem_4_1 ρm readM ρp readP Good Υ hΥ hα hβ V hcomplete hsound (A.simToXor q)
    (2 * q) h41
  push_cast at h
  exact h

end QuantumQueryComplexity
