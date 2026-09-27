import QuantumQueryComplexity.Quantum.Amplitude.ApproxReflection
import QuantumQueryComplexity.Quantum.RobustSearch.Progress
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Recursive amplitude amplification with approximate reflections

The operator recursion of Magniez–Nayak–Roland–Santha (after Høyer–Mosca–de Wolf), abstractly:
a unit start vector `s`, a marker `S`, and a sequence of reflections `R 1, R 2, …` about `s`
of improving precision `β j`.

    chainA 0 = 1,     chainA (j+1) = (A_j · R_{j+1} · A_j†) · (S · A_j)

so each level uses three invocations of the preceding routine (two forwards, one inverse), one
exact marker and **one** new reflection; the coarse reflections are the ones used most often.

`ChainOK` collects what the analysis uses, in exactly the form it is used: `R (j+1)` is a
`β (j+1)`-approximate reflection about `s` on an allowed set `Dom j`; the marker acts as the
phase flip on the states `ψ_j = A_j s`; and `A_j† S ψ_j` is allowed.  (The compiled layer
derives these from support invariants of the routines.)

With `m j = ‖Π ψ_j‖²`:

* `abs_sqrt_m_succ_le` — `|√m_{j+1} − |3 − 4m_j|·√m_j| ≤ 2β_{j+1}·√m_j`.  The error of a level
  is **proportional to the amplitude**, because `A_j R A_j†` is an approximate reflection about
  the *actual* `ψ_j` with the same `β` (`IsApproxRefl.conj`): errors are not tripled.
* `m_succ_ge`, `sqrt_m_succ_le`, `qNorm_ψ_succ_sub_le` — growth from below and above, and the
  distance moved, `(2 + 2β)·√m_j`.
* `exists_level` — with `β j ≤ 2^{-(j+8)}`: if `m 0 ≥ ε` and `⌈1/ε⌉ ≤ 9^K`, some level
  `n ≤ K` has `m n ≥ 1/10` (`RobustSearch.progress`, the same potential argument).
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H O : Type} [Fintype H] [DecidableEq H]

/-- The level operators. -/
noncomputable def chainA (S : Matrix H H ℂ) (R : ℕ → Matrix H H ℂ) : ℕ → Matrix H H ℂ
  | 0 => 1
  | j + 1 => (chainA S R j * R (j + 1) * (chainA S R j)ᴴ) * (S * chainA S R j)

/-- The approximate reflection about the level-`j` state. -/
noncomputable def chainM (S : Matrix H H ℂ) (R : ℕ → Matrix H H ℂ) (j : ℕ) : Matrix H H ℂ :=
  chainA S R j * R (j + 1) * (chainA S R j)ᴴ

lemma chainA_succ (S : Matrix H H ℂ) (R : ℕ → Matrix H H ℂ) (j : ℕ) :
    chainA S R (j + 1) = chainM S R j * (S * chainA S R j) := rfl

lemma chainA_mem_unitaryGroup {S : Matrix H H ℂ} {R : ℕ → Matrix H H ℂ}
    (hS : S ∈ Matrix.unitaryGroup H ℂ) (hR : ∀ j, R j ∈ Matrix.unitaryGroup H ℂ) (j : ℕ) :
    chainA S R j ∈ Matrix.unitaryGroup H ℂ := by
  induction j with
  | zero => exact one_mem_qUnitary
  | succ j ih =>
      exact mul_mem_qUnitary (mul_mem_qUnitary (mul_mem_qUnitary ih (hR _))
        (conjTranspose_mem_qUnitary ih)) (mul_mem_qUnitary hS ih)

lemma chainM_mem_unitaryGroup {S : Matrix H H ℂ} {R : ℕ → Matrix H H ℂ}
    (hS : S ∈ Matrix.unitaryGroup H ℂ) (hR : ∀ j, R j ∈ Matrix.unitaryGroup H ℂ) (j : ℕ) :
    chainM S R j ∈ Matrix.unitaryGroup H ℂ :=
  mul_mem_qUnitary (mul_mem_qUnitary (chainA_mem_unitaryGroup hS hR j) (hR _))
    (conjTranspose_mem_qUnitary (chainA_mem_unitaryGroup hS hR j))

variable (rd : H → O) (G : O → Prop) [DecidablePred G]

/-- What the analysis of the recursion uses. -/
structure ChainOK (s : H → ℂ) (S : Matrix H H ℂ) (R : ℕ → Matrix H H ℂ) (β : ℕ → ℝ)
    (Dom : ℕ → Set (H → ℂ)) : Prop where
  unit : IsQState s
  S_unitary : S ∈ Matrix.unitaryGroup H ℂ
  R_unitary : ∀ j, R j ∈ Matrix.unitaryGroup H ℂ
  β_nonneg : ∀ j, 0 ≤ β j
  β_le : ∀ j, β j ≤ (1 / 2) ^ (j + 8)
  refl : ∀ j, IsApproxRefl (R (j + 1)) s (Dom j) (β (j + 1))
  flip : ∀ j, S *ᵥ (chainA S R j *ᵥ s) = phaseFlip rd G (chainA S R j *ᵥ s)
  dom : ∀ j, (chainA S R j)ᴴ *ᵥ phaseFlip rd G (chainA S R j *ᵥ s) ∈ Dom j

variable {rd G} {s : H → ℂ} {S : Matrix H H ℂ} {R : ℕ → Matrix H H ℂ} {β : ℕ → ℝ}
  {Dom : ℕ → Set (H → ℂ)}

namespace ChainOK

variable (h : ChainOK rd G s S R β Dom)

include h

/-- The level-`j` state. -/
noncomputable def ψ (_ : ChainOK rd G s S R β Dom) (j : ℕ) : H → ℂ := chainA S R j *ᵥ s

/-- Its marked mass. -/
noncomputable def m (j : ℕ) : ℝ := goodProb rd G (h.ψ j)

lemma isQState_ψ (j : ℕ) : IsQState (h.ψ j) :=
  IsQState.mulVec (chainA_mem_unitaryGroup h.S_unitary h.R_unitary j) h.unit

lemma m_nonneg (j : ℕ) : 0 ≤ h.m j := goodProb_nonneg _ _ _

lemma m_le_one (j : ℕ) : h.m j ≤ 1 := goodProb_le_one _ _ (h.isQState_ψ j)

/-- `A_j R_{j+1} A_j†` is a `β_{j+1}`-approximate reflection about the actual `ψ_j`. -/
lemma isApproxRefl_chainM (j : ℕ) :
    IsApproxRefl (chainM S R j) (h.ψ j) {χ | (chainA S R j)ᴴ *ᵥ χ ∈ Dom j} (β (j + 1)) :=
  (h.refl j).conj (chainA_mem_unitaryGroup h.S_unitary h.R_unitary j)

lemma ψ_succ (j : ℕ) : h.ψ (j + 1) = chainM S R j *ᵥ phaseFlip rd G (h.ψ j) := by
  rw [ψ, chainA_succ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h.flip j]
  rfl

theorem abs_sqrt_m_succ_le (j : ℕ) :
    |Real.sqrt (h.m (j + 1)) - |3 - 4 * h.m j| * Real.sqrt (h.m j)|
      ≤ 2 * β (j + 1) * Real.sqrt (h.m j) := by
  rw [m, h.ψ_succ]
  exact abs_sqrt_step_le (h.isQState_ψ j) (h.isApproxRefl_chainM j) (h.β_nonneg _) (h.dom j)

theorem qNorm_ψ_succ_sub_le (j : ℕ) :
    qNorm (h.ψ (j + 1) - h.ψ j) ≤ (2 + 2 * β (j + 1)) * Real.sqrt (h.m j) := by
  rw [h.ψ_succ]
  exact qNorm_step_sub_le (h.isQState_ψ j) (h.isApproxRefl_chainM j) (h.β_nonneg _) (h.dom j)

/-- Growth from above: `√m_{j+1} ≤ (3 + 2β)·√m_j`. -/
theorem sqrt_m_succ_le (j : ℕ) :
    Real.sqrt (h.m (j + 1)) ≤ (3 + 2 * β (j + 1)) * Real.sqrt (h.m j) := by
  have h1 := (abs_le.mp (h.abs_sqrt_m_succ_le j)).2
  have h2 : |3 - 4 * h.m j| ≤ 3 := by
    rw [abs_le]; constructor <;> nlinarith [h.m_nonneg j, h.m_le_one j]
  have := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg (h.m j))
  linarith

/-- Growth from below, in amplitude. -/
theorem le_sqrt_m_succ (j : ℕ) (hm : h.m j ≤ 1 / 2) :
    (3 - 4 * h.m j - 2 * β (j + 1)) * Real.sqrt (h.m j) ≤ Real.sqrt (h.m (j + 1)) := by
  have h1 := (abs_le.mp (h.abs_sqrt_m_succ_le j)).1
  have h2 : |3 - 4 * h.m j| = 3 - 4 * h.m j := abs_of_nonneg (by linarith)
  rw [h2] at h1
  linarith

/-- Growth from below, in mass. -/
theorem m_succ_ge (j : ℕ) (hm : h.m j ≤ 1 / 2) :
    (3 - 4 * (h.m j + β (j + 1) / 2)) ^ 2 * h.m j ≤ h.m (j + 1) := by
  have h1 := h.le_sqrt_m_succ j hm
  have hβ := h.β_le (j + 1)
  have hβ' : β (j + 1) ≤ 1 / 4 := hβ.trans (by
    calc (1 / 2 : ℝ) ^ (j + 1 + 8) ≤ (1 / 2) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num)
  have hpos : 0 ≤ 3 - 4 * h.m j - 2 * β (j + 1) := by linarith
  have hsq := mul_self_le_mul_self (mul_nonneg hpos (Real.sqrt_nonneg _)) h1
  rw [Real.mul_self_sqrt (h.m_nonneg _)] at hsq
  have hx := Real.mul_self_sqrt (h.m_nonneg j)
  obtain ⟨x, hxdef⟩ : ∃ x, x = Real.sqrt (h.m j) := ⟨_, rfl⟩
  rw [← hxdef] at hsq hx
  have : (3 - 4 * (h.m j + β (j + 1) / 2)) ^ 2 * h.m j
      = (3 - 4 * h.m j - 2 * β (j + 1)) * x * ((3 - 4 * h.m j - 2 * β (j + 1)) * x) := by
    rw [← hx]; ring
  rw [this]
  exact hsq

/-- **Some level has marked mass at least `1/10`.** -/
theorem exists_level {ε : ℝ} (hε : 0 < ε) (hm0 : ε ≤ h.m 0) {K : ℕ}
    (hK : ⌈1 / ε⌉₊ ≤ 9 ^ K) : ∃ n, n ≤ K ∧ 1 / 10 ≤ h.m n := by
  have hceil : 0 < ⌈1 / ε⌉₊ := Nat.ceil_pos.mpr (by positivity)
  obtain ⟨n, hn1, hnK, hn⟩ := RobustSearch.progress (fun n => h.m (n - 1)) (fun n => β n / 2)
    ⌈1 / ε⌉₊ K hceil (by exact_mod_cast hK) (fun n => h.m_nonneg _)
    (fun n => by have := h.β_nonneg n; positivity)
    (fun n _ => by
      have := h.β_le n
      rw [show n + 9 = (n + 8) + 1 from rfl, pow_succ]
      linarith)
    (by
      have hc : (0 : ℝ) < ⌈1 / ε⌉₊ := by exact_mod_cast hceil
      have h1 : 1 / ε ≤ ⌈1 / ε⌉₊ := Nat.le_ceil _
      have h2 : 1 / (⌈1 / ε⌉₊ : ℝ) ≤ ε := by
        rw [div_le_iff₀ hc]
        have := (div_le_iff₀ hε).mp h1
        linarith
      have h3 : (1 - (1 / 2 : ℝ) ^ 10) / ⌈1 / ε⌉₊ ≤ 1 / (⌈1 / ε⌉₊ : ℝ) :=
        div_le_div_of_nonneg_right (by norm_num) hc.le
      show _ ≤ h.m (1 - 1)
      exact h3.trans (h2.trans hm0))
    (fun n hn hlt => by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hlt ⊢
      have hstep := h.m_succ_ge k (by linarith)
      have hfac : (1 - (1 / 2 : ℝ) ^ (k + 1 + 10)) ≤ 1 := by
        have : (0 : ℝ) < (1 / 2) ^ (k + 1 + 10) := by positivity
        linarith
      have hnn : 0 ≤ (3 - 4 * (h.m k + β (k + 1) / 2)) ^ 2 * h.m k :=
        mul_nonneg (sq_nonneg _) (h.m_nonneg k)
      calc (1 - (1 / 2 : ℝ) ^ (k + 1 + 10)) * (3 - 4 * (h.m k + β (k + 1) / 2)) ^ 2 * h.m k
          = (1 - (1 / 2 : ℝ) ^ (k + 1 + 10))
              * ((3 - 4 * (h.m k + β (k + 1) / 2)) ^ 2 * h.m k) := by ring
        _ ≤ 1 * ((3 - 4 * (h.m k + β (k + 1) / 2)) ^ 2 * h.m k) :=
            mul_le_mul_of_nonneg_right hfac hnn
        _ ≤ h.m (k + 1) := by rw [one_mul]; exact hstep)
  exact ⟨n - 1, by omega, hn⟩

end ChainOK

end QuantumQueryComplexity
