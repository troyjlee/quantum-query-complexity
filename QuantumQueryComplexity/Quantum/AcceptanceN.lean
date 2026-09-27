import QuantumQueryComplexity.Quantum.MaxApplications
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Maximum finding: acceptance test

These statement pins cover the operational maximum finding bounds.
The full `QuantumQueryComplexity` library imports this file, and the default
build checks it.

Pinned, with every convention literal:

1. **the classical certificates** — `HasDual` at `24·√n` for the maximum of
   any value map on the letters and for `MAX` itself, no quantum import in
   their proofs;
2. **the native unabsorbed minimum** at the literal `8192`, error exactly
   `1/3`, exact read-all cap `n`, for the generic value map and for `MAX`;
3. **the native lower bound and absorbed sandwich** — under exactly two
   distinct values `lo < hi`: `7·√n/1376 ≤ Q_{1/3} ≤ min{n, 204800·√n}`
   (the output type is the finite value order, so the lower bound is the
   direct plurality `7/1376` finite-output extraction — no recoding);
4. **the one-hot unabsorbed minimum** at `16384` with the same exact cap;
5. **the one-hot lower bound and sandwich** at `7/2752` and `409600`.

Manual axiom checks on both sandwiches:

    #print axioms QuantumQueryComplexity.max_qQuery_sandwich
      → [propext, Classical.choice, Quot.sound]
    #print axioms QuantumQueryComplexity.max_oneHotQQuery_sandwich
      → [propext, Classical.choice, Quot.sound]
-/

namespace QuantumQueryComplexity
namespace MilestoneMax

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Type} [Fintype A] [DecidableEq A] [LinearOrder A]
variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-! ## 1. The classical certificates -/

theorem dual_map_pinned (m : σ → A) :
    HasDual (fun x : ι → σ => maxFun fun j => m (x j))
      (24 * Real.sqrt (Fintype.card ι)) :=
  hasDual_maxMap m

theorem dual_pinned :
    HasDual (maxFun : (ι → A) → A) (24 * Real.sqrt (Fintype.card ι)) :=
  hasDual_maxFun

/-! ## 2. The native unabsorbed minimum -/

theorem native_map_upper_pinned [Nonempty A] (m : σ → A) :
    (qQuery (fun x : ι → σ => maxFun fun j => m (x j)) (1 / 3) : ℝ)
      ≤ 8192 * (1 + 24 * Real.sqrt (Fintype.card ι)) := by
  have h := maxMap_qQuery_upper (ι := ι) m
  rwa [show uniformExtractionConstant = (8192 : ℝ) by
    norm_num [uniformExtractionConstant]] at h

theorem native_min_pinned [Nonempty A] :
    (qQuery (maxFun : (ι → A) → A) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (8192 * (1 + 24 * Real.sqrt (Fintype.card ι))) := by
  have h := max_qQuery_le_min (ι := ι) (A := A)
  rwa [show uniformExtractionConstant = (8192 : ℝ) by
    norm_num [uniformExtractionConstant]] at h

/-! ## 3. The native lower bound and sandwich -/

theorem native_lower_pinned {lo hi : A} (h : lo < hi) :
    7 * Real.sqrt (Fintype.card ι) / 1376
      ≤ (qQuery (maxFun : (ι → A) → A) (1 / 3) : ℝ) :=
  max_qQuery_lower h

theorem native_sandwich_pinned {lo hi : A} (h : lo < hi) :
    7 * Real.sqrt (Fintype.card ι) / 1376
        ≤ (qQuery (maxFun : (ι → A) → A) (1 / 3) : ℝ)
      ∧ (qQuery (maxFun : (ι → A) → A) (1 / 3) : ℝ)
        ≤ min (Fintype.card ι : ℝ)
            (204800 * Real.sqrt (Fintype.card ι)) :=
  max_qQuery_sandwich h

/-! ## 4. The one-hot unabsorbed minimum -/

theorem oneHot_min_pinned [Nonempty A] :
    (oneHotQQuery (maxFun : (ι → A) → A) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (16384 * (1 + 24 * Real.sqrt (Fintype.card ι))) :=
  max_oneHotQQuery_le_min

/-! ## 5. The one-hot lower bound and sandwich -/

theorem oneHot_lower_pinned {lo hi : A} (h : lo < hi) :
    7 * Real.sqrt (Fintype.card ι) / 2752
      ≤ (oneHotQQuery (maxFun : (ι → A) → A) (1 / 3) : ℝ) :=
  max_oneHotQQuery_lower h

theorem oneHot_sandwich_pinned {lo hi : A} (h : lo < hi) :
    7 * Real.sqrt (Fintype.card ι) / 2752
        ≤ (oneHotQQuery (maxFun : (ι → A) → A) (1 / 3) : ℝ)
      ∧ (oneHotQQuery (maxFun : (ι → A) → A) (1 / 3) : ℝ)
        ≤ min (Fintype.card ι : ℝ)
            (409600 * Real.sqrt (Fintype.card ι)) :=
  max_oneHotQQuery_sandwich h

end MilestoneMax

end QuantumQueryComplexity
