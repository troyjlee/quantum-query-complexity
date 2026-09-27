import QuantumQueryComplexity.EDLower.Main
import QuantumQueryComplexity.Quantum.UniformHasDual
import QuantumQueryComplexity.Quantum.OneHotTransport
import QuantumQueryComplexity.Promise.Post
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Element distinctness: the operational quantum-query endpoints

The `Θ(n^{2/3})` bounded-error quantum query complexity of element
distinctness, as named theorems in both oracle models:

* **native** (transposition oracle): `Q_{1/3}(ED) ≤ min{n, 8192·(1 + 8·n^{2/3})}`
  and, for `n ≥ 2` and `|σ| ≥ 4n²`, `n^{2/3}/4608 ≤ Q_{1/3}(ED)` — the
  pure-power sandwich `n^{2/3}/4608 ≤ Q ≤ min{n, 73728·n^{2/3}}`;
* **one-hot** (the canonical one-hot XOR oracle model): the same at a direct
  factor two — `16384`, `9216`, `147456` — with the **exact** read-all cap `n`
  in both models (the one-hot cap is `oneHotQQuery_le_card`, not a simulated
  `2n`).

The upper route preserves the learning-graph dual certificate:
`hasDual_edFun → HasDual.hasDualOn → qQueryOn_third_le_of_hasDualOn_uniform`
— the cardinality-free extraction, so the bounds are **uniform in the
alphabet**: no `[Nonempty σ]`, no `√|σ|`.  The lower route is
`advPM_edFun_ge` through the sharp Boolean `1/36` bound
(`mul_advPMOn_le_qQueryOn_of_error_third`) at `read = id`.

This file sits outside the `QuantumQueryComplexity.Quantum` aggregate: it is an
application layer importing both the classical ED development and the
quantum model, built by CI as an explicit cross-stream target.
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-! ## The native model -/

/-- **The cardinality-free compiler bound**:
`Q_{1/3}(ED) ≤ 8192·(1 + 8·n^{2/3})`, uniformly in the alphabet. -/
theorem ed_qQuery_upper :
    (qQuery (edFun (ι := ι) (σ := σ)) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + 8 * (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)) :=
  qQueryOn_third_le_of_hasDualOn_uniform
    (hasDual_edFun ι σ).hasDualOn (by positivity)

/-- **Reading every position**: the exact cap `Q_{1/3}(ED) ≤ n`. -/
theorem ed_qQuery_upper_length :
    qQuery (edFun (ι := ι) (σ := σ)) (1 / 3) ≤ Fintype.card ι :=
  qQueryOn_le_card (read := (id : (ι → σ) → ι → σ))
    (f := edFun (ι := ι) (σ := σ))
    (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)

/-- **The unabsorbed minimum form**:
`Q_{1/3}(ED) ≤ min{n, 8192·(1 + 8·n^{2/3})}`. -/
theorem ed_qQuery_le_min :
    (qQuery (edFun (ι := ι) (σ := σ)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ) (uniformExtractionConstant
          * (1 + 8 * (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3))) :=
  le_min (by exact_mod_cast ed_qQuery_upper_length) ed_qQuery_upper

/-- **The operational lower bound**: for `n ≥ 2` and `|σ| ≥ 4n²`,
`n^{2/3}/4608 ≤ Q_{1/3}(ED)` — Belovs' adversary bound through the sharp
Boolean `1/36` extraction, `4608 = 128·36`. -/
theorem ed_qQuery_lower (hn : 2 ≤ Fintype.card ι)
    (hq : 4 * (Fintype.card ι * Fintype.card ι) ≤ Fintype.card σ) :
    (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) / 4608
      ≤ (qQuery (edFun (ι := ι) (σ := σ)) (1 / 3) : ℝ) := by
  have hadv := advPM_edFun_ge (ι := ι) (σ := σ) hn hq
  have hpar := mul_advPMOn_le_qQueryOn_of_error_third
    (read := (id : (ι → σ) → ι → σ)) (f := edFun (ι := ι) (σ := σ))
    (fun x y h => by rw [show x = y from h])
  have hid : advPMOn (id : (ι → σ) → ι → σ) (edFun (ι := ι) (σ := σ))
      = advPM (edFun (ι := ι) (σ := σ)) := rfl
  rw [hid] at hpar
  calc (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) / 4608
      = (1 / 36 : ℝ) * ((Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) / 128) := by ring
    _ ≤ (1 / 36 : ℝ) * advPM (edFun (ι := ι) (σ := σ)) :=
        mul_le_mul_of_nonneg_left hadv (by norm_num)
    _ ≤ _ := hpar

/-- `n ≥ 2` puts the power above one. -/
private lemma one_le_ed_pow (hn : 2 ≤ Fintype.card ι) :
    (1 : ℝ) ≤ (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) := by
  have h1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    have : (1 : ℕ) ≤ Fintype.card ι := by omega
    exact_mod_cast this
  calc (1 : ℝ) = (1 : ℝ) ^ ((2 : ℝ) / 3) := (Real.one_rpow _).symm
    _ ≤ (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) :=
        Real.rpow_le_rpow (by norm_num) h1 (by norm_num)

/-- **The native `Θ(n^{2/3})` sandwich**: for `n ≥ 2` and `|σ| ≥ 4n²`,

    n^{2/3}/4608 ≤ Q_{1/3}(ED) ≤ min{n, 73728·n^{2/3}},

with `73728 = 9·8192`. -/
theorem ed_qQuery_sandwich (hn : 2 ≤ Fintype.card ι)
    (hq : 4 * (Fintype.card ι * Fintype.card ι) ≤ Fintype.card σ) :
    (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) / 4608
        ≤ (qQuery (edFun (ι := ι) (σ := σ)) (1 / 3) : ℝ)
      ∧ (qQuery (edFun (ι := ι) (σ := σ)) (1 / 3) : ℝ)
        ≤ min (Fintype.card ι : ℝ)
            (73728 * (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)) := by
  refine ⟨ed_qQuery_lower hn hq, le_min
    (by exact_mod_cast ed_qQuery_upper_length) (le_trans ed_qQuery_upper ?_)⟩
  have hx := one_le_ed_pow hn
  have hC : uniformExtractionConstant = (8192 : ℝ) := by
    norm_num [uniformExtractionConstant]
  rw [hC]
  nlinarith

/-! ## The one-hot model -/

/-- **The compiler bound in the one-hot model**, at a direct factor two:
`Q^{1-hot}_{1/3}(ED) ≤ 16384·(1 + 8·n^{2/3})`. -/
theorem ed_oneHotQQuery_upper :
    (oneHotQQuery (edFun (ι := ι) (σ := σ)) (1 / 3) : ℝ)
      ≤ 16384 * (1 + 8 * (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)) := by
  have h := oneHotQQueryOn_le_two_mul_of_qQueryOn_le (id_det _) (by norm_num)
    (ed_qQuery_upper (ι := ι) (σ := σ))
  rw [show (16384 : ℝ) = 2 * uniformExtractionConstant by
    norm_num [uniformExtractionConstant], mul_assoc]
  exact h

/-- **Reading every position, one-hot**: the exact cap `n` — direct, not
through simulation (which would weaken it to `2n`). -/
theorem ed_oneHotQQuery_upper_length :
    oneHotQQuery (edFun (ι := ι) (σ := σ)) (1 / 3) ≤ Fintype.card ι :=
  oneHotQQuery_le_card (edFun (ι := ι) (σ := σ))
    (by norm_num : (0 : ℝ) ≤ 1 / 3)

/-- **The unabsorbed minimum form, one-hot**:
`Q^{1-hot}_{1/3}(ED) ≤ min{n, 16384·(1 + 8·n^{2/3})}`. -/
theorem ed_oneHotQQuery_le_min :
    (oneHotQQuery (edFun (ι := ι) (σ := σ)) (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (16384 * (1 + 8 * (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3))) :=
  le_min (by exact_mod_cast ed_oneHotQQuery_upper_length) ed_oneHotQQuery_upper

/-- **The one-hot lower bound**: `n^{2/3}/9216 ≤ Q^{1-hot}_{1/3}(ED)`,
`9216 = 2·4608`. -/
theorem ed_oneHotQQuery_lower (hn : 2 ≤ Fintype.card ι)
    (hq : 4 * (Fintype.card ι * Fintype.card ι) ≤ Fintype.card σ) :
    (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) / 9216
      ≤ (oneHotQQuery (edFun (ι := ι) (σ := σ)) (1 / 3) : ℝ) := by
  have h := half_le_oneHotQQueryOn_of_le_qQueryOn (id_det _) (by norm_num)
    (ed_qQuery_lower hn hq)
  calc (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) / 9216
      = ((Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) / 4608) / 2 := by ring
    _ ≤ _ := h

/-- **The one-hot `Θ(n^{2/3})` sandwich**: for `n ≥ 2` and `|σ| ≥ 4n²`,

    n^{2/3}/9216 ≤ Q^{1-hot}_{1/3}(ED) ≤ min{n, 147456·n^{2/3}},

with `147456 = 9·16384`. -/
theorem ed_oneHotQQuery_sandwich (hn : 2 ≤ Fintype.card ι)
    (hq : 4 * (Fintype.card ι * Fintype.card ι) ≤ Fintype.card σ) :
    (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) / 9216
        ≤ (oneHotQQuery (edFun (ι := ι) (σ := σ)) (1 / 3) : ℝ)
      ∧ (oneHotQQuery (edFun (ι := ι) (σ := σ)) (1 / 3) : ℝ)
        ≤ min (Fintype.card ι : ℝ)
            (147456 * (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)) := by
  refine ⟨ed_oneHotQQuery_lower hn hq, le_min
    (by exact_mod_cast ed_oneHotQQuery_upper_length)
    (le_trans ed_oneHotQQuery_upper ?_)⟩
  have hx := one_le_ed_pow hn
  nlinarith

end QuantumQueryComplexity
