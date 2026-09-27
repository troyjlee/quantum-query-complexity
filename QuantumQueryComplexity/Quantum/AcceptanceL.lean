import QuantumQueryComplexity.Quantum.EDApplications
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Element distinctness: acceptance test

These statement pins cover the operational element distinctness bounds.
The full `QuantumQueryComplexity` library imports this file, and the default
build checks it.

Pinned, with every convention literal:

1. **The classical certificate** — `HasDual (edFun) (8·n^{2/3})`, no quantum
   import in its proof;
2. **the native unabsorbed minimum** — `Q_{1/3}(ED) ≤ min{n,
   8192·(1 + 8·n^{2/3})}`, error exactly `1/3`, exact read-all cap `n`;
3. **the native lower bound and pure-power sandwich** — under exactly
   `2 ≤ n` and `4n² ≤ |σ|`: `n^{2/3}/4608 ≤ Q_{1/3}(ED) ≤ min{n,
   73728·n^{2/3}}`;
4. **the one-hot unabsorbed minimum** — `16384` with the same exact cap `n`;
5. **the one-hot lower bound and pure-power sandwich** — `9216` and
   `147456`.

The native and canonical one-hot oracle models are distinguished by type
(`qQuery` vs `oneHotQQuery`); the constants `8192`, `16384`, `4608`, `9216`,
`73728`, `147456` are all literal below.  Manual axiom checks on both
headline sandwiches:

    #print axioms QuantumQueryComplexity.ed_qQuery_sandwich
      → [propext, Classical.choice, Quot.sound]
    #print axioms QuantumQueryComplexity.ed_oneHotQQuery_sandwich
      → [propext, Classical.choice, Quot.sound]
-/

namespace QuantumQueryComplexity
namespace MilestoneED

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-! ## 1. The classical certificate -/

theorem dual_pinned :
    HasDual (edFun (ι := ι) (σ := σ))
      (8 * (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)) :=
  hasDual_edFun ι σ

/-! ## 2. The native unabsorbed minimum -/

theorem native_min_pinned :
    (qQuery (edFun (ι := ι) (σ := σ)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (8192 * (1 + 8 * (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3))) := by
  have h := ed_qQuery_le_min (ι := ι) (σ := σ)
  rwa [show uniformExtractionConstant = (8192 : ℝ) by
    norm_num [uniformExtractionConstant]] at h

/-! ## 3. The native lower bound and sandwich -/

theorem native_lower_pinned (hn : 2 ≤ Fintype.card ι)
    (hq : 4 * (Fintype.card ι * Fintype.card ι) ≤ Fintype.card σ) :
    (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) / 4608
      ≤ (qQuery (edFun (ι := ι) (σ := σ)) (1 / 3) : ℝ) :=
  ed_qQuery_lower hn hq

theorem native_sandwich_pinned (hn : 2 ≤ Fintype.card ι)
    (hq : 4 * (Fintype.card ι * Fintype.card ι) ≤ Fintype.card σ) :
    (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) / 4608
        ≤ (qQuery (edFun (ι := ι) (σ := σ)) (1 / 3) : ℝ)
      ∧ (qQuery (edFun (ι := ι) (σ := σ)) (1 / 3) : ℝ)
        ≤ min (Fintype.card ι : ℝ)
            (73728 * (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)) :=
  ed_qQuery_sandwich hn hq

/-! ## 4. The one-hot unabsorbed minimum -/

theorem oneHot_min_pinned :
    (oneHotQQuery (edFun (ι := ι) (σ := σ)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (16384 * (1 + 8 * (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3))) :=
  ed_oneHotQQuery_le_min

/-! ## 5. The one-hot lower bound and sandwich -/

theorem oneHot_lower_pinned (hn : 2 ≤ Fintype.card ι)
    (hq : 4 * (Fintype.card ι * Fintype.card ι) ≤ Fintype.card σ) :
    (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) / 9216
      ≤ (oneHotQQuery (edFun (ι := ι) (σ := σ)) (1 / 3) : ℝ) :=
  ed_oneHotQQuery_lower hn hq

theorem oneHot_sandwich_pinned (hn : 2 ≤ Fintype.card ι)
    (hq : 4 * (Fintype.card ι * Fintype.card ι) ≤ Fintype.card σ) :
    (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) / 9216
        ≤ (oneHotQQuery (edFun (ι := ι) (σ := σ)) (1 / 3) : ℝ)
      ∧ (oneHotQQuery (edFun (ι := ι) (σ := σ)) (1 / 3) : ℝ)
        ≤ min (Fintype.card ι : ℝ)
            (147456 * (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)) :=
  ed_oneHotQQuery_sandwich hn hq

end MilestoneED

end QuantumQueryComplexity
