import QuantumQueryComplexity.Quantum.LDSApplications
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Longest distinct substring: acceptance test

These statement pins cover the operational longest distinct substring bounds.
The full `QuantumQueryComplexity` library imports this file, and the default
build checks it.

Pinned, with every convention literal:

1. **the classical certificate** — `HasDualOn read (ldsFun ∘ read)` at
   `112·2^49·ldsDepth n·n^{2/3}`, for every promise `read`, no quantum
   import in its proof;
2. **the native unabsorbed minimum** at the literal `8192`, error exactly
   `1/3`, exact read-all cap `n`;
3. **the native lower bound and absorbed sandwich** — under exactly `2 ≤ n`
   and `4n² ≤ |σ|`: `7·n^{2/3}/176128 ≤ Q_{1/3} ≤ min{n,
   112·2^63·ldsDepth n·n^{2/3}}` (the output type is `ℕ`, so the lower
   bound goes through the exact `Fin (n+1)` recoding and the plurality
   `7/1376` finite-output extraction);
4. **the one-hot unabsorbed minimum** at `16384` with the same exact cap;
5. **the one-hot lower bound and sandwich** at `7/352256` and `112·2^64`;
6. **the real-logarithm displays** in both models,
   `Q ≤ 112·2^63·(1 + log₂ n)·n^{2/3}` and `112·2^64` one-hot.

Manual axiom checks on both sandwiches:

    #print axioms QuantumQueryComplexity.lds_qQuery_sandwich
      → [propext, Classical.choice, Quot.sound]
    #print axioms QuantumQueryComplexity.lds_oneHotQQuery_sandwich
      → [propext, Classical.choice, Quot.sound]
-/

namespace QuantumQueryComplexity
namespace MilestoneLDS

variable {n : ℕ} {σ : Type} [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X] [DecidableEq X]

/-! ## 1. The classical certificate -/

theorem dual_pinned (hn : 1 ≤ n) (read : X → Fin n → σ) :
    HasDualOn read (fun x => ldsFun (read x))
      (112 * (2 ^ 49 * (ldsDepth n : ℕ) * (n : ℝ) ^ ((2 : ℝ) / 3))) :=
  hasDualOn_ldsFun hn (le_max_left _ _) (le_two_pow_ldsDepth n)
    (two_pow_ldsDepth_le hn) read

/-! ## 2. The native unabsorbed minimum -/

theorem native_min_pinned (hn : 1 ≤ n) :
    (qQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (8192 * (1 + 112 * (2 ^ 49 * (ldsDepth n : ℕ)
          * (n : ℝ) ^ ((2 : ℝ) / 3)))) := by
  have h := lds_qQuery_le_min (σ := σ) hn
  rwa [show uniformExtractionConstant = (8192 : ℝ) by
    norm_num [uniformExtractionConstant],
    show nodeConst = (2 : ℝ) ^ 49 from rfl] at h

/-! ## 3. The native lower bound and sandwich -/

theorem native_lower_pinned (hn : 2 ≤ n)
    (hq : 4 * (n * n) ≤ Fintype.card σ) :
    7 * (n : ℝ) ^ ((2 : ℝ) / 3) / 176128
      ≤ (qQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ) :=
  lds_qQuery_lower hn hq

theorem native_sandwich_pinned (hn : 2 ≤ n)
    (hq : 4 * (n * n) ≤ Fintype.card σ) :
    7 * (n : ℝ) ^ ((2 : ℝ) / 3) / 176128
        ≤ (qQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
      ∧ (qQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
        ≤ min (n : ℝ)
            (112 * 2 ^ 63 * (ldsDepth n : ℕ) * (n : ℝ) ^ ((2 : ℝ) / 3)) :=
  lds_qQuery_sandwich hn hq

/-! ## 4. The one-hot unabsorbed minimum -/

theorem oneHot_min_pinned (hn : 1 ≤ n) :
    (oneHotQQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (16384 * (1 + 112 * (2 ^ 49 * (ldsDepth n : ℕ)
          * (n : ℝ) ^ ((2 : ℝ) / 3)))) := by
  have h := lds_oneHotQQuery_le_min (σ := σ) hn
  rwa [show nodeConst = (2 : ℝ) ^ 49 from rfl] at h

/-! ## 5. The one-hot lower bound and sandwich -/

theorem oneHot_lower_pinned (hn : 2 ≤ n)
    (hq : 4 * (n * n) ≤ Fintype.card σ) :
    7 * (n : ℝ) ^ ((2 : ℝ) / 3) / 352256
      ≤ (oneHotQQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ) :=
  lds_oneHotQQuery_lower hn hq

theorem oneHot_sandwich_pinned (hn : 2 ≤ n)
    (hq : 4 * (n * n) ≤ Fintype.card σ) :
    7 * (n : ℝ) ^ ((2 : ℝ) / 3) / 352256
        ≤ (oneHotQQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
      ∧ (oneHotQQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
        ≤ min (n : ℝ)
            (112 * 2 ^ 64 * (ldsDepth n : ℕ) * (n : ℝ) ^ ((2 : ℝ) / 3)) :=
  lds_oneHotQQuery_sandwich hn hq

/-! ## 6. The real-logarithm displays -/

theorem native_logb_pinned (hn : 1 ≤ n) :
    (qQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
      ≤ 112 * 2 ^ 63 * (1 + Real.logb 2 n) * (n : ℝ) ^ ((2 : ℝ) / 3) :=
  lds_qQuery_le_logb hn

theorem oneHot_logb_pinned (hn : 1 ≤ n) :
    (oneHotQQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
      ≤ 112 * 2 ^ 64 * (1 + Real.logb 2 n) * (n : ℝ) ^ ((2 : ℝ) / 3) :=
  lds_oneHotQQuery_le_logb hn

end MilestoneLDS

end QuantumQueryComplexity
