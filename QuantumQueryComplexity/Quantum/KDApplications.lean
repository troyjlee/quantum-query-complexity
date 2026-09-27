import QuantumQueryComplexity.KD.Main
import QuantumQueryComplexity.Quantum.UniformHasDual
import QuantumQueryComplexity.Quantum.OneHotTransport
import QuantumQueryComplexity.Promise.Post
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# k-distinctness: the operational quantum-query endpoints

The `O(n^{k/(k+1)})` bounded-error quantum query complexity of
k-distinctness, as named theorems in both oracle models:

* **native** (transposition oracle):
  `Q_{1/3}(kdFun k) ≤ min{n, 8192·(1 + (k+1)·2^{k+1}·n^{k/(k+1)})}`,
  with the parametric form
  `Q_{1/3} ≤ 8192·(1 + 2^{k+1}·r + ∑_{ℓ<k} √(2^k·n^{ℓ+1}/(r+1)^ℓ))`
  for any stage width `r` with `2(r+k) ≤ n`;
* **one-hot** (the canonical one-hot XOR oracle model): the same at a
  direct factor two (`16384`), with the **exact** read-all cap `n` in
  both models.

The upper route preserves the learning-graph flow certificate:
`hasDual_kdFun`/`hasDual_kdFun_param` (split out of the `advPM` endpoints
in `KD/Main.lean`, which are retained there as weak-duality corollaries)
`→ HasDual.hasDualOn → qQueryOn_third_le_of_hasDualOn_uniform` — the
cardinality-free extraction, so the bounds are **uniform in the
alphabet**.  No matching lower bound is claimed for general `k`; the
`k = 2` regime is covered by the dedicated element-distinctness endpoints
(`EDApplications.lean`).

This file sits outside the `QuantumQueryComplexity.Quantum` aggregate: it is an
application layer importing both the classical k-distinctness development
and the quantum model, built by CI as an explicit cross-stream target.
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-! ## The native model -/

/-- **The parametric compiler bound**: for `2(r+k) ≤ n`,
`Q_{1/3}(kdFun k) ≤ 8192·(1 + 2^{k+1}·r + ∑_{ℓ<k} √(2^k·n^{ℓ+1}/(r+1)^ℓ))`. -/
theorem kd_qQuery_upper_param (k r : ℕ) (hk : 1 ≤ k)
    (hrn : 2 * (r + k) ≤ Fintype.card ι) :
    (qQuery (kdFun (ι := ι) (σ := σ) k) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + (2 ^ (k + 1) * r
            + ∑ ℓ ∈ Finset.range k,
                Real.sqrt (((2 ^ k * Fintype.card ι ^ (ℓ + 1) : ℕ) : ℝ)
                  / (((r + 1) ^ ℓ : ℕ) : ℝ)))) :=
  qQueryOn_third_le_of_hasDualOn_uniform
    (hasDual_kdFun_param k r hk hrn).hasDualOn
    (add_nonneg (by positivity)
      (Finset.sum_nonneg fun ℓ _ => Real.sqrt_nonneg _))

/-- **The headline compiler bound**:
`Q_{1/3}(kdFun k) ≤ 8192·(1 + (k+1)·2^{k+1}·n^{k/(k+1)})`, uniformly in
the alphabet. -/
theorem kd_qQuery_upper (k : ℕ) (hk : 1 ≤ k) :
    (qQuery (kdFun (ι := ι) (σ := σ) k) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + ((k : ℝ) + 1) * 2 ^ (k + 1)
            * (Fintype.card ι : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1))) :=
  qQueryOn_third_le_of_hasDualOn_uniform
    (hasDual_kdFun k hk ι σ).hasDualOn
    (mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- **Reading every position**: the exact cap `Q_{1/3}(kdFun k) ≤ n`. -/
theorem kd_qQuery_upper_length (k : ℕ) :
    qQuery (kdFun (ι := ι) (σ := σ) k) (1 / 3) ≤ Fintype.card ι :=
  qQueryOn_le_card (read := (id : (ι → σ) → ι → σ))
    (f := kdFun (ι := ι) (σ := σ) k)
    (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)

/-- **The unabsorbed minimum form**:
`Q_{1/3}(kdFun k) ≤ min{n, 8192·(1 + (k+1)·2^{k+1}·n^{k/(k+1)})}`. -/
theorem kd_qQuery_le_min (k : ℕ) (hk : 1 ≤ k) :
    (qQuery (kdFun (ι := ι) (σ := σ) k) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (uniformExtractionConstant
          * (1 + ((k : ℝ) + 1) * 2 ^ (k + 1)
            * (Fintype.card ι : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1)))) :=
  le_min (by exact_mod_cast kd_qQuery_upper_length k) (kd_qQuery_upper k hk)

/-! ## The one-hot model -/

/-- **The compiler bound in the one-hot model**, at a direct factor two:
`Q^{1-hot}_{1/3}(kdFun k) ≤ 16384·(1 + (k+1)·2^{k+1}·n^{k/(k+1)})`. -/
theorem kd_oneHotQQuery_upper (k : ℕ) (hk : 1 ≤ k) :
    (oneHotQQuery (kdFun (ι := ι) (σ := σ) k) (1 / 3) : ℝ)
      ≤ 16384 * (1 + ((k : ℝ) + 1) * 2 ^ (k + 1)
          * (Fintype.card ι : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1))) := by
  have h := oneHotQQueryOn_le_two_mul_of_qQueryOn_le
    (id_det (kdFun (ι := ι) (σ := σ) k)) (by norm_num)
    (kd_qQuery_upper (ι := ι) (σ := σ) k hk)
  rw [show (16384 : ℝ) = 2 * uniformExtractionConstant by
    norm_num [uniformExtractionConstant], mul_assoc]
  exact h

/-- **Reading every position, one-hot**: the exact cap `n` — direct, not
through simulation (which would weaken it to `2n`). -/
theorem kd_oneHotQQuery_upper_length (k : ℕ) :
    oneHotQQuery (kdFun (ι := ι) (σ := σ) k) (1 / 3) ≤ Fintype.card ι :=
  oneHotQQuery_le_card (kdFun (ι := ι) (σ := σ) k)
    (by norm_num : (0 : ℝ) ≤ 1 / 3)

/-- **The unabsorbed minimum form, one-hot**:
`Q^{1-hot}_{1/3}(kdFun k) ≤ min{n, 16384·(1 + (k+1)·2^{k+1}·n^{k/(k+1)})}`. -/
theorem kd_oneHotQQuery_le_min (k : ℕ) (hk : 1 ≤ k) :
    (oneHotQQuery (kdFun (ι := ι) (σ := σ) k) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (16384 * (1 + ((k : ℝ) + 1) * 2 ^ (k + 1)
            * (Fintype.card ι : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1)))) :=
  le_min (by exact_mod_cast kd_oneHotQQuery_upper_length k)
    (kd_oneHotQQuery_upper k hk)

end QuantumQueryComplexity
