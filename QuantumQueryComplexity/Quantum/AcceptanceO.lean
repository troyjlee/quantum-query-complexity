import QuantumQueryComplexity.Quantum.ReadOnceApplications
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Read-once formulas, OR, AND, and the balanced tree: acceptance test

These statement pins cover the operational read-once formulas bounds.
The full `QuantumQueryComplexity` library imports this file, and the default
build checks it.

Pinned, with every convention literal:

1. **the classical certificates** — `HasROCert` for the `OR` and `AND`
   gates at their fan-in, for the balanced AND-OR tree at `2^(d+1)`
   leaves, and the bundled dual `HasDual f (√n)` of every read-once
   formula, no quantum import in their proofs;
2. **the native unabsorbed minimum** at the literal `8192`, error exactly
   `1/3`, exact read-all cap `|ι|`, for every read-once formula;
3. **the native lower bound and absorbed sandwich** — **unconditionally**:
   `√n/36 ≤ Q_{1/3}(f) ≤ min{|ι|, 16384·√n}` (the read-once theorem pins
   `ADV±(f) = √n` exactly, and the output is Boolean, so the sharp `1/36`
   extraction applies with no cardinality hypotheses);
4. **the one-hot unabsorbed minimum** at `16384` with the same exact cap;
5. **the one-hot lower bound and sandwich** at `√n/72` and `32768`;
6. **the gates and the tree** — the sandwiches specialized to `OR`, `AND`
   (at `n = ` fan-in) and the balanced AND-OR tree (at `n = 2^(d+1)`,
   where the cap and the leaf count coincide).

Manual axiom checks on the general sandwiches and the tree:

    #print axioms QuantumQueryComplexity.HasROCert.qQuery_sandwich
      → [propext, Classical.choice, Quot.sound]
    #print axioms QuantumQueryComplexity.HasROCert.oneHotQQuery_sandwich
      → [propext, Classical.choice, Quot.sound]
    #print axioms QuantumQueryComplexity.andOrTree_qQuery_sandwich
      → [propext, Classical.choice, Quot.sound]
-/

namespace QuantumQueryComplexity
namespace MilestoneReadOnce

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 1. The classical certificates -/

theorem cert_orN_pinned [Nonempty ι] :
    HasROCert (orN : (ι → Bool) → Bool) (Fintype.card ι) :=
  hasROCert_orN

theorem cert_andN_pinned [Nonempty ι] :
    HasROCert (andN : (ι → Bool) → Bool) (Fintype.card ι) :=
  hasROCert_andN

theorem cert_tree_pinned (d : ℕ) :
    HasROCert (andOrTree d) (2 ^ (d + 1)) :=
  hasROCert_andOrTree d

theorem dual_pinned {f : (ι → Bool) → Bool} {n : ℕ} (h : HasROCert f n) :
    HasDual f (Real.sqrt (n : ℝ)) :=
  h.hasDual

theorem advPM_pinned {f : (ι → Bool) → Bool} {n : ℕ} (h : HasROCert f n) :
    advPM f = Real.sqrt (n : ℝ) :=
  h.hasAdvValue.1

/-! ## 2. The native unabsorbed minimum -/

theorem native_min_pinned {f : (ι → Bool) → Bool} {n : ℕ}
    (h : HasROCert f n) :
    (qQuery f (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (8192 * (1 + Real.sqrt (n : ℝ))) := by
  have h2 := h.qQuery_le_min
  rwa [show uniformExtractionConstant = (8192 : ℝ) by
    norm_num [uniformExtractionConstant]] at h2

/-! ## 3. The native lower bound and sandwich, unconditional -/

theorem native_lower_pinned {f : (ι → Bool) → Bool} {n : ℕ}
    (h : HasROCert f n) :
    Real.sqrt (n : ℝ) / 36 ≤ (qQuery f (1 / 3) : ℝ) :=
  h.qQuery_lower

theorem native_sandwich_pinned {f : (ι → Bool) → Bool} {n : ℕ}
    (h : HasROCert f n) :
    Real.sqrt (n : ℝ) / 36 ≤ (qQuery f (1 / 3) : ℝ)
      ∧ (qQuery f (1 / 3) : ℝ)
        ≤ min (Fintype.card ι : ℝ) (16384 * Real.sqrt (n : ℝ)) :=
  h.qQuery_sandwich

/-! ## 4. The one-hot unabsorbed minimum -/

theorem oneHot_min_pinned {f : (ι → Bool) → Bool} {n : ℕ}
    (h : HasROCert f n) :
    (oneHotQQuery f (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (16384 * (1 + Real.sqrt (n : ℝ))) :=
  h.oneHotQQuery_le_min

/-! ## 5. The one-hot lower bound and sandwich -/

theorem oneHot_lower_pinned {f : (ι → Bool) → Bool} {n : ℕ}
    (h : HasROCert f n) :
    Real.sqrt (n : ℝ) / 72 ≤ (oneHotQQuery f (1 / 3) : ℝ) :=
  h.oneHotQQuery_lower

theorem oneHot_sandwich_pinned {f : (ι → Bool) → Bool} {n : ℕ}
    (h : HasROCert f n) :
    Real.sqrt (n : ℝ) / 72 ≤ (oneHotQQuery f (1 / 3) : ℝ)
      ∧ (oneHotQQuery f (1 / 3) : ℝ)
        ≤ min (Fintype.card ι : ℝ) (32768 * Real.sqrt (n : ℝ)) :=
  h.oneHotQQuery_sandwich

/-! ## 6. The gates and the tree -/

theorem or_sandwich_pinned [Nonempty ι] :
    Real.sqrt (Fintype.card ι : ℝ) / 36
        ≤ (qQuery (orN : (ι → Bool) → Bool) (1 / 3) : ℝ)
      ∧ (qQuery (orN : (ι → Bool) → Bool) (1 / 3) : ℝ)
        ≤ min (Fintype.card ι : ℝ)
            (16384 * Real.sqrt (Fintype.card ι : ℝ)) :=
  orN_qQuery_sandwich

theorem and_sandwich_pinned [Nonempty ι] :
    Real.sqrt (Fintype.card ι : ℝ) / 36
        ≤ (qQuery (andN : (ι → Bool) → Bool) (1 / 3) : ℝ)
      ∧ (qQuery (andN : (ι → Bool) → Bool) (1 / 3) : ℝ)
        ≤ min (Fintype.card ι : ℝ)
            (16384 * Real.sqrt (Fintype.card ι : ℝ)) :=
  andN_qQuery_sandwich

theorem tree_sandwich_pinned (d : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (d + 1)) / 36
        ≤ (qQuery (andOrTree d) (1 / 3) : ℝ)
      ∧ (qQuery (andOrTree d) (1 / 3) : ℝ)
        ≤ min ((2 : ℝ) ^ (d + 1))
            (16384 * Real.sqrt ((2 : ℝ) ^ (d + 1))) :=
  andOrTree_qQuery_sandwich d

theorem tree_oneHot_sandwich_pinned (d : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (d + 1)) / 72
        ≤ (oneHotQQuery (andOrTree d) (1 / 3) : ℝ)
      ∧ (oneHotQQuery (andOrTree d) (1 / 3) : ℝ)
        ≤ min ((2 : ℝ) ^ (d + 1))
            (32768 * Real.sqrt ((2 : ℝ) ^ (d + 1))) :=
  andOrTree_oneHotQQuery_sandwich d

end MilestoneReadOnce

end QuantumQueryComplexity
