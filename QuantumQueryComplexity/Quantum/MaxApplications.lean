import QuantumQueryComplexity.Max.Lower
import QuantumQueryComplexity.HasDual
import QuantumQueryComplexity.Quantum.UniformHasDual
import QuantumQueryComplexity.Quantum.Plurality
import QuantumQueryComplexity.Quantum.OneHotTransport
import QuantumQueryComplexity.Promise.Post
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Maximum finding: the operational quantum-query endpoints

The `Θ(√n)` bounded-error quantum query complexity of maximum finding, as
named theorems in both oracle models:

* **native** (transposition oracle): `Q_{1/3}(MAX) ≤ min{n, 8192·(1 + 24·√n)}`
  and, whenever the value order has two distinct elements,
  `7·√n/1376 ≤ Q_{1/3}(MAX)` — the pure-power sandwich
  `7·√n/1376 ≤ Q ≤ min{n, 204800·√n}`;
* **one-hot** (the canonical one-hot XOR oracle model): the same at a direct
  factor two — `16384`, `7/2752`, `409600` — with the **exact** read-all cap
  `n` in both models.

The upper route preserves the weighted-scan dual certificate:
`hasDual_maxMap`/`hasDual_maxFun` (bundled in `QuantumQueryComplexity/HasDual.lean` from
`exists_maxMap_dual_isCostLe`) `→ HasDual.hasDualOn →
qQueryOn_third_le_of_hasDualOn_uniform` — the cardinality-free extraction,
so the generic bound is **uniform in the letter alphabet**.  The lower route
is `sqrt_card_le_advPM_maxFun` through the plurality `7/1376` finite-output
extraction (`mul_advPMOn_le_qQueryOn_third_finiteOutput`) at `read = id`;
the output type `A` is finite, so no recoding is needed.

The generic form takes any value map `m : σ → A` on the letters; the `MAX`
specializations read the order itself.  This file sits outside the
`QuantumQueryComplexity.Quantum` aggregate: it is an application layer importing both the
classical scan development and the quantum model, built by CI as an explicit
cross-stream target.
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Type} [Fintype A] [DecidableEq A] [LinearOrder A]
variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-! ## The native model -/

/-- **The cardinality-free compiler bound, generic value map**:
`Q_{1/3}(max_j m(x_j)) ≤ 8192·(1 + 24·√n)`, uniformly in the letter
alphabet. -/
theorem maxMap_qQuery_upper [Nonempty A] (m : σ → A) :
    (qQuery (fun x : ι → σ => maxFun fun j => m (x j)) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + 24 * Real.sqrt (Fintype.card ι)) :=
  qQueryOn_third_le_of_hasDualOn_uniform
    (hasDual_maxMap m).hasDualOn (by positivity)

/-- **The cardinality-free compiler bound for `MAX` itself**:
`Q_{1/3}(MAX) ≤ 8192·(1 + 24·√n)`. -/
theorem max_qQuery_upper [Nonempty A] :
    (qQuery (maxFun : (ι → A) → A) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + 24 * Real.sqrt (Fintype.card ι)) :=
  qQueryOn_third_le_of_hasDualOn_uniform
    (hasDual_maxFun (ι := ι) (A := A)).hasDualOn (by positivity)

/-- **Reading every position**: the exact cap `Q_{1/3}(MAX) ≤ n`. -/
theorem max_qQuery_upper_length [Nonempty A] :
    qQuery (maxFun : (ι → A) → A) (1 / 3) ≤ Fintype.card ι :=
  qQueryOn_le_card (read := (id : (ι → A) → ι → A))
    (f := (maxFun : (ι → A) → A))
    (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)

/-- **The unabsorbed minimum form**:
`Q_{1/3}(MAX) ≤ min{n, 8192·(1 + 24·√n)}`. -/
theorem max_qQuery_le_min [Nonempty A] :
    (qQuery (maxFun : (ι → A) → A) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (uniformExtractionConstant
          * (1 + 24 * Real.sqrt (Fintype.card ι))) :=
  le_min (by exact_mod_cast max_qQuery_upper_length) max_qQuery_upper

/-- **The operational lower bound**: whenever the value order has two
distinct elements, `7·√n/1376 ≤ Q_{1/3}(MAX)` — the star adversary bound
through the plurality `7/1376` finite-output extraction. -/
theorem max_qQuery_lower {lo hi : A} (h : lo < hi) :
    7 * Real.sqrt (Fintype.card ι) / 1376
      ≤ (qQuery (maxFun : (ι → A) → A) (1 / 3) : ℝ) := by
  have hA : Nonempty A := ⟨lo⟩
  have hadv := sqrt_card_le_advPM_maxFun (ι := ι) h
  have hpar := mul_advPMOn_le_qQueryOn_third_finiteOutput
    (read := (id : (ι → A) → ι → A)) (f := (maxFun : (ι → A) → A))
    (fun x y h => by rw [show x = y from h])
  have hid : advPMOn (id : (ι → A) → ι → A) (maxFun : (ι → A) → A)
      = advPM (maxFun : (ι → A) → A) := rfl
  rw [hid] at hpar
  calc 7 * Real.sqrt (Fintype.card ι) / 1376
      = (7 / 1376 : ℝ) * Real.sqrt (Fintype.card ι) := by ring
    _ ≤ (7 / 1376 : ℝ) * advPM (maxFun : (ι → A) → A) :=
        mul_le_mul_of_nonneg_left hadv (by norm_num)
    _ ≤ _ := hpar

/-- `n ≥ 1` puts the square root above one. -/
private lemma one_le_max_sqrt :
    (1 : ℝ) ≤ Real.sqrt (Fintype.card ι) := by
  have h1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    have : (1 : ℕ) ≤ Fintype.card ι := Fintype.card_pos
    exact_mod_cast this
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (Fintype.card ι) := Real.sqrt_le_sqrt h1

/-- **The native `Θ(√n)` sandwich**: whenever the value order has two
distinct elements,

    7·√n/1376 ≤ Q_{1/3}(MAX) ≤ min{n, 204800·√n},

with `204800 = 25·8192`. -/
theorem max_qQuery_sandwich {lo hi : A} (h : lo < hi) :
    7 * Real.sqrt (Fintype.card ι) / 1376
        ≤ (qQuery (maxFun : (ι → A) → A) (1 / 3) : ℝ)
      ∧ (qQuery (maxFun : (ι → A) → A) (1 / 3) : ℝ)
        ≤ min (Fintype.card ι : ℝ)
            (204800 * Real.sqrt (Fintype.card ι)) := by
  have hA : Nonempty A := ⟨lo⟩
  refine ⟨max_qQuery_lower h, le_min
    (by exact_mod_cast max_qQuery_upper_length) (le_trans max_qQuery_upper ?_)⟩
  have hx := one_le_max_sqrt (ι := ι)
  have hC : uniformExtractionConstant = (8192 : ℝ) := by
    norm_num [uniformExtractionConstant]
  rw [hC]
  nlinarith

/-! ## The one-hot model -/

/-- **The compiler bound in the one-hot model**, at a direct factor two:
`Q^{1-hot}_{1/3}(MAX) ≤ 16384·(1 + 24·√n)`. -/
theorem max_oneHotQQuery_upper [Nonempty A] :
    (oneHotQQuery (maxFun : (ι → A) → A) (1 / 3) : ℝ)
      ≤ 16384 * (1 + 24 * Real.sqrt (Fintype.card ι)) := by
  have h := oneHotQQueryOn_le_two_mul_of_qQueryOn_le (id_det _) (by norm_num)
    (max_qQuery_upper (ι := ι) (A := A))
  rw [show (16384 : ℝ) = 2 * uniformExtractionConstant by
    norm_num [uniformExtractionConstant], mul_assoc]
  exact h

/-- **Reading every position, one-hot**: the exact cap `n` — direct, not
through simulation (which would weaken it to `2n`). -/
theorem max_oneHotQQuery_upper_length [Nonempty A] :
    oneHotQQuery (maxFun : (ι → A) → A) (1 / 3) ≤ Fintype.card ι :=
  oneHotQQuery_le_card (maxFun : (ι → A) → A)
    (by norm_num : (0 : ℝ) ≤ 1 / 3)

/-- **The unabsorbed minimum form, one-hot**:
`Q^{1-hot}_{1/3}(MAX) ≤ min{n, 16384·(1 + 24·√n)}`. -/
theorem max_oneHotQQuery_le_min [Nonempty A] :
    (oneHotQQuery (maxFun : (ι → A) → A) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (16384 * (1 + 24 * Real.sqrt (Fintype.card ι))) :=
  le_min (by exact_mod_cast max_oneHotQQuery_upper_length)
    max_oneHotQQuery_upper

/-- **The one-hot lower bound**: `7·√n/2752 ≤ Q^{1-hot}_{1/3}(MAX)`,
`2752 = 2·1376`. -/
theorem max_oneHotQQuery_lower {lo hi : A} (h : lo < hi) :
    7 * Real.sqrt (Fintype.card ι) / 2752
      ≤ (oneHotQQuery (maxFun : (ι → A) → A) (1 / 3) : ℝ) := by
  have hA : Nonempty A := ⟨lo⟩
  have h2 := half_le_oneHotQQueryOn_of_le_qQueryOn
    (id_det (maxFun : (ι → A) → A)) (by norm_num) (max_qQuery_lower h)
  calc 7 * Real.sqrt (Fintype.card ι) / 2752
      = (7 * Real.sqrt (Fintype.card ι) / 1376) / 2 := by ring
    _ ≤ _ := h2

/-- **The one-hot `Θ(√n)` sandwich**: whenever the value order has two
distinct elements,

    7·√n/2752 ≤ Q^{1-hot}_{1/3}(MAX) ≤ min{n, 409600·√n},

with `409600 = 25·16384`. -/
theorem max_oneHotQQuery_sandwich {lo hi : A} (h : lo < hi) :
    7 * Real.sqrt (Fintype.card ι) / 2752
        ≤ (oneHotQQuery (maxFun : (ι → A) → A) (1 / 3) : ℝ)
      ∧ (oneHotQQuery (maxFun : (ι → A) → A) (1 / 3) : ℝ)
        ≤ min (Fintype.card ι : ℝ)
            (409600 * Real.sqrt (Fintype.card ι)) := by
  have hA : Nonempty A := ⟨lo⟩
  refine ⟨max_oneHotQQuery_lower h, le_min
    (by exact_mod_cast max_oneHotQQuery_upper_length)
    (le_trans max_oneHotQQuery_upper ?_)⟩
  have hx := one_le_max_sqrt (ι := ι)
  nlinarith

end QuantumQueryComplexity
