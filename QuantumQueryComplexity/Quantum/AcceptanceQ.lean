import QuantumQueryComplexity.Quantum.KDApplications
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# k-distinctness: acceptance test

These statement pins cover the operational k-distinctness bounds.
The full `QuantumQueryComplexity` library imports this file, and the default
build checks it.

Pinned, with every convention literal:

1. **the classical certificates** — `HasDual (kdFun k)` at the parametric
   flow cost and at the headline `(k+1)·2^{k+1}·n^{k/(k+1)}`, split out of
   the `advPM` endpoints (which are retained in `KD/Main.lean` as
   weak-duality corollaries, pinned here too), no quantum import in their
   proofs;
2. **the native unabsorbed minimum** at the literal `8192`, error exactly
   `1/3`, exact read-all cap `n`;
3. **the one-hot unabsorbed minimum** at `16384` with the same exact cap.

No lower bound is claimed for general `k`; the `k = 2` regime is the
element-distinctness family (`AcceptanceL`).

Manual axiom checks:

    #print axioms QuantumQueryComplexity.kd_qQuery_le_min
      → [propext, Classical.choice, Quot.sound]
    #print axioms QuantumQueryComplexity.hasDual_kdFun
      → [propext, Classical.choice, Quot.sound]
-/

namespace QuantumQueryComplexity
namespace MilestoneKD

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-! ## 1. The classical certificates and the retained advPM corollaries -/

theorem dual_param_pinned (k r : ℕ) (hk : 1 ≤ k)
    (hrn : 2 * (r + k) ≤ Fintype.card ι) :
    HasDual (kdFun (ι := ι) (σ := σ) k)
      (2 ^ (k + 1) * r
        + ∑ ℓ ∈ Finset.range k,
            Real.sqrt (((2 ^ k * Fintype.card ι ^ (ℓ + 1) : ℕ) : ℝ)
              / (((r + 1) ^ ℓ : ℕ) : ℝ))) :=
  hasDual_kdFun_param k r hk hrn

theorem dual_pinned (k : ℕ) (hk : 1 ≤ k) :
    HasDual (kdFun (ι := ι) (σ := σ) k)
      (((k : ℝ) + 1) * 2 ^ (k + 1)
        * (Fintype.card ι : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1))) :=
  hasDual_kdFun k hk ι σ

theorem advPM_pinned (k : ℕ) (hk : 1 ≤ k) :
    advPM (kdFun (ι := ι) (σ := σ) k)
      ≤ ((k : ℝ) + 1) * 2 ^ (k + 1)
        * (Fintype.card ι : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1)) :=
  advPM_kdFun_le k hk ι σ

/-! ## 2. The native unabsorbed minimum -/

theorem native_min_pinned (k : ℕ) (hk : 1 ≤ k) :
    (qQuery (kdFun (ι := ι) (σ := σ) k) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (8192
          * (1 + ((k : ℝ) + 1) * 2 ^ (k + 1)
            * (Fintype.card ι : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1)))) := by
  have h := kd_qQuery_le_min (ι := ι) (σ := σ) k hk
  rwa [show uniformExtractionConstant = (8192 : ℝ) by
    norm_num [uniformExtractionConstant]] at h

/-! ## 3. The one-hot unabsorbed minimum -/

theorem oneHot_min_pinned (k : ℕ) (hk : 1 ≤ k) :
    (oneHotQQuery (kdFun (ι := ι) (σ := σ) k) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (16384 * (1 + ((k : ℝ) + 1) * 2 ^ (k + 1)
            * (Fintype.card ι : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1)))) :=
  kd_oneHotQQuery_le_min k hk

end MilestoneKD

end QuantumQueryComplexity
