import QuantumQueryComplexity.Quantum.Characterization
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Plurality amplification and finite-output bounds: statement tests

These pins cover plurality amplification and the general-output `1/3`
lower bound. The full `QuantumQueryComplexity` library imports this file,
and the default build checks it. `AcceptanceC.lean` separately pins the
`1/16` finite-output characterization.

Pinned:

1. **The exponential-moment tail** — records with at least `t` wrong
   coordinates carry product weight at most `(1 + ε)^k / 2^t`; no Chernoff
   bound, no binomial-tail library.
2. **Plurality amplification** at general `k` and `ε`: `k + 1` runs, error
   `(1 + ε)^{k+1} / 2^{⌈(k+1)/2⌉}`, cost `(k + 1)·q`.
3. **The `43`-run contract** — `q ∈ QueryCounts f (1/3) → 43q ∈ QueryCounts
   f (1/16)`, hence `Q_{1/16}(f) ≤ 43·Q_{1/3}(f)` for finite outputs
   (`(4/3)^43 / 2^22 = 2^64 / 3^43 < 1/16`).
4. **The general-output `1/3` lower bound** — `(7/1376)·ADV±ₚ(f) ≤
   Q_{1/3}(f)` on any promise, and the total-function form.
5. **The finite-output characterization at `1/3`**, both halves — the
   additive form and the literally multiplicative form
   `(7/1376)·ADV±ₚ(f) ≤ Q_{1/3}(f) ≤ 2¹⁸·B·(Nat.clog 2 (3B))·√|σ|·ADV±ₚ(f)`.

    #print axioms QuantumQueryComplexity.mul_advPMOn_le_qQueryOn_third_finiteOutput
      → [propext, Classical.choice, Quot.sound]
-/

namespace QuantumQueryComplexity
namespace MilestoneH

variable {ι σ X O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype X] [Fintype O] [DecidableEq O]

/-! ## 1. The exponential-moment tail -/

theorem tail_pinned {k t : ℕ} {ε : ℝ} (p : Fin k → O → ℝ) (b : Fin k → O)
    (hp0 : ∀ j o, 0 ≤ p j o) (hp1 : ∀ j, ∑ o, p j o ≤ 1)
    (hpe : ∀ j, ∑ o ∈ Finset.univ.filter (fun o => o ≠ b j), p j o ≤ ε) :
    (∑ y ∈ Finset.univ.filter (fun y : Fin k → O => t ≤ wrongCount y b),
        ∏ j, p j (y j)) * 2 ^ t
      ≤ (1 + ε) ^ k :=
  sum_prod_tail_le p b hp0 hp1 hpe

/-! ## 2. Plurality amplification -/

theorem amplify_pinned {read : X → ι → σ} {f : X → O} {q : ℕ} {ε : ℝ}
    (hex : ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : QAlg ι σ O W), ComputesWithErrorOn A q read f ε) (k : ℕ) :
    ∃ (W' : Type) (_ : Fintype W') (_ : DecidableEq W')
      (A' : QAlg ι σ O W'),
      ComputesWithErrorOn A' ((k + 1) * q) read f
        ((1 + ε) ^ (k + 1) / 2 ^ ((k + 2) / 2)) :=
  amplify_plurality hex k

/-! ## 3. The `43`-run contract -/

theorem fortythree_pinned {read : X → ι → σ} {f : X → O} {q : ℕ}
    (hq : q ∈ QueryCounts read f (1 / 3)) :
    43 * q ∈ QueryCounts read f (1 / 16) :=
  fortythree_mem_queryCounts_sixteenth hq

example : ((1 + (1 / 3 : ℝ)) ^ 43 / 2 ^ 22) ≤ 1 / 16 := by norm_num

variable [Nonempty O] [DecidableEq X]

theorem sixteenth_le_third_pinned {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y) :
    qQueryOn read f (1 / 16) ≤ 43 * qQueryOn read f (1 / 3) :=
  qQueryOn_sixteenth_le_fortythree_mul_third hdet

/-! ## 4. The general-output `1/3` lower bound -/

theorem lower_third_pinned {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (7 / 1376 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 3) : ℝ) :=
  mul_advPMOn_le_qQueryOn_third_finiteOutput hdet

theorem lower_third_total_pinned (f : (ι → σ) → O) :
    (7 / 1376 : ℝ) * advPM f ≤ (qQuery f (1 / 3) : ℝ) :=
  mul_advPM_le_qQuery_third_finiteOutput f

/-! ## 5. The finite-output characterization at `1/3` -/

theorem characterization_third_pinned [Nonempty σ] (read : X → ι → σ) (f : X → O)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (7 / 1376 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 3) : ℝ) ∧
      (qQueryOn read f (1 / 3) : ℝ)
        ≤ 2 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
          * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ)
              * advPMOn read f)) :=
  qQueryOn_characterized_by_advPMOn_third read f hdet

theorem characterization_third_mul_pinned [Nonempty σ] (read : X → ι → σ)
    (f : X → O) (hdet : ∀ x y, read x = read y → f x = f y) :
    (7 / 1376 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 3) : ℝ) ∧
      (qQueryOn read f (1 / 3) : ℝ)
        ≤ 2 ^ 18 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
          * Real.sqrt (Fintype.card σ) * advPMOn read f :=
  qQueryOn_characterized_by_advPMOn_third_mul read f hdet

end MilestoneH
end QuantumQueryComplexity
