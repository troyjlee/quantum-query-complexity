import QuantumQueryComplexity.LDS.Main
import QuantumQueryComplexity.LDS.Lower
import QuantumQueryComplexity.Quantum.UniformHasDual
import QuantumQueryComplexity.Quantum.Plurality
import QuantumQueryComplexity.Quantum.Postcomp
import QuantumQueryComplexity.Quantum.OneHotTransport
import QuantumQueryComplexity.Promise.Post
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Longest distinct substring: the operational quantum-query endpoints

The `Õ(n^{2/3})` bounded-error quantum query complexity of the longest
distinct substring problem (arXiv:2311.16401, Theorem 39), in both oracle
models:

* **native**: `Q_{1/3}(ldsFun) ≤ min{n, 8192·(1 + 112·2^49·ldsDepth n·n^{2/3})}`
  and, for `n ≥ 2` and `|σ| ≥ 4n²`, `7·n^{2/3}/176128 ≤ Q_{1/3}(ldsFun)`;
  the absorbed forms `Q ≤ min{n, 112·2^63·ldsDepth n·n^{2/3}}` and, over the
  real logarithm, `Q ≤ 112·2^63·(1 + log₂ n)·n^{2/3}`;
* **one-hot**: the direct factor-two forms — `16384`, `352256`, `2^64` —
  with the **exact** read-all cap `n` in both models.

The upper route preserves the outer-scan certificate: `hasDualOn_ldsFun` at
`read = id` feeds the cardinality-free extraction directly, so the bounds
are uniform in the alphabet — no `[Nonempty σ]`, no `√|σ|`.

**The output type is `ℕ`, and the lower route must respect it**: the
same-error lower bounds for general outputs assume a `Fintype`, so the
lower bound recodes through `Fin (n+1)` — free in both quantities, since
`ldsFun ≤ n` makes the truncation exact (`qQueryOn_postcomp_le` on the
query side, `advPMOn_comp_le` along `Fin.val` on the adversary side) — and
then applies the plurality finite-output bound `7/1376`; with the `n^{2/3}/128`
adversary lower bound this gives `7/176128 = (7/1376)·(1/128)`.

This file sits outside the `QuantumQueryComplexity.Quantum` aggregate: it is an
application layer importing both streams, built by CI as an explicit
cross-stream target.
-/

namespace QuantumQueryComplexity

variable {n : ℕ} {σ : Type} [Fintype σ] [DecidableEq σ]

/-! ## The native model -/

/-- **The cardinality-free compiler bound**: for `n ≥ 1`,
`Q_{1/3}(ldsFun) ≤ 8192·(1 + 112·2^49·ldsDepth n·n^{2/3})`. -/
theorem lds_qQuery_upper (hn : 1 ≤ n) :
    (qQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
      ≤ uniformExtractionConstant
          * (1 + 112 * (nodeConst * (ldsDepth n : ℕ)
              * (n : ℝ) ^ ((2 : ℝ) / 3))) := by
  have hC : (0 : ℝ) < nodeConst := nodeConst_pos
  have hx : (0 : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hd : (0 : ℝ) ≤ ((ldsDepth n : ℕ) : ℝ) := Nat.cast_nonneg _
  refine qQueryOn_third_le_of_hasDualOn_uniform ?_
    (by nlinarith [mul_nonneg (mul_nonneg hC.le hd) hx])
  exact hasDualOn_ldsFun hn (le_max_left _ _) (le_two_pow_ldsDepth n)
    (two_pow_ldsDepth_le hn) (id : (Fin n → σ) → Fin n → σ)

/-- **Reading every position**: the exact cap `Q_{1/3}(ldsFun) ≤ n`. -/
theorem lds_qQuery_upper_length :
    qQuery (ldsFun (n := n) (σ := σ)) (1 / 3) ≤ n := by
  have h := qQueryOn_le_card (read := (id : (Fin n → σ) → Fin n → σ))
    (f := ldsFun (n := n) (σ := σ))
    (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [Fintype.card_fin] at h

/-- **The unabsorbed minimum form**: for `n ≥ 1`,
`Q_{1/3}(ldsFun) ≤ min{n, 8192·(1 + 112·2^49·ldsDepth n·n^{2/3})}`. -/
theorem lds_qQuery_le_min (hn : 1 ≤ n) :
    (qQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (uniformExtractionConstant
          * (1 + 112 * (nodeConst * (ldsDepth n : ℕ)
              * (n : ℝ) ^ ((2 : ℝ) / 3)))) :=
  le_min (by exact_mod_cast lds_qQuery_upper_length) (lds_qQuery_upper hn)

/-- The `Fin (n+1)`-valued recoding of `ldsFun` — exact, since
`ldsFun ≤ n`. -/
private lemma ldsFun_eq_val_comp (α : Fin n → σ) :
    ldsFun (n := n) (σ := σ) α
      = ((⟨min (ldsFun α) n, by omega⟩ : Fin (n + 1)) : ℕ) := by
  have h := ldsFun_le (σ := σ) α
  simp [min_eq_left h]

/-- **The operational lower bound**: for `n ≥ 2` and `|σ| ≥ 4n²`,
`7·n^{2/3}/176128 ≤ Q_{1/3}(ldsFun)` — the adversary lower bound through the
plurality finite-output extraction after the exact `Fin (n+1)` recoding;
`176128 = 1376·128`. -/
theorem lds_qQuery_lower (hn : 2 ≤ n)
    (hq : 4 * (n * n) ≤ Fintype.card σ) :
    7 * (n : ℝ) ^ ((2 : ℝ) / 3) / 176128
      ≤ (qQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ) := by
  classical
  -- the finite recoding
  set g : ℕ → Fin (n + 1) := fun k => ⟨min k n, by omega⟩ with hg
  have hdet : ∀ x y : Fin n → σ, id x = id y →
      ldsFun (n := n) (σ := σ) x = ldsFun y :=
    fun x y h => by rw [show x = y from h]
  have hdetg : ∀ x y : Fin n → σ, id x = id y →
      g (ldsFun (n := n) (σ := σ) x) = g (ldsFun y) :=
    fun x y h => by rw [show x = y from h]
  -- the query side: recoding is free
  have hne : (QueryCounts (id : (Fin n → σ) → Fin n → σ)
      (ldsFun (n := n) (σ := σ)) (1 / 3 : ℝ)).Nonempty :=
    queryCounts_nonempty hdet (by norm_num)
  have hpost := qQueryOn_postcomp_le (read := (id : (Fin n → σ) → Fin n → σ))
    (f := ldsFun (n := n) (σ := σ)) g hne
  -- the finite-output lower bound on the recoded function
  have hfin := mul_advPMOn_le_qQueryOn_third_finiteOutput
    (read := (id : (Fin n → σ) → Fin n → σ))
    (f := fun α => g (ldsFun (n := n) (σ := σ) α)) hdetg
  -- the adversary side: the recoding does not lower the adversary value
  have hval : (fun α : Fin n → σ => ((g (ldsFun (n := n) (σ := σ) α)) : ℕ))
      = ldsFun (n := n) (σ := σ) := by
    funext α
    exact (ldsFun_eq_val_comp α).symm
  have hcomp : advPM (ldsFun (n := n) (σ := σ))
      ≤ advPMOn (id : (Fin n → σ) → Fin n → σ)
          (fun α => g (ldsFun (n := n) (σ := σ) α)) := by
    have h := advPMOn_comp_le (read := (id : (Fin n → σ) → Fin n → σ))
      (f := fun α => g (ldsFun (n := n) (σ := σ) α)) hdetg
      (fun v : Fin (n + 1) => (v : ℕ))
    have hid : advPMOn (id : (Fin n → σ) → Fin n → σ)
        (fun α => ((g (ldsFun (n := n) (σ := σ) α)) : ℕ))
        = advPM (ldsFun (n := n) (σ := σ)) := by
      rw [hval]
      rfl
    rwa [hid] at h
  have hadv := advPM_ldsFun_ge (n := n) (σ := σ) hn hq
  calc 7 * (n : ℝ) ^ ((2 : ℝ) / 3) / 176128
      = (7 / 1376 : ℝ) * ((n : ℝ) ^ ((2 : ℝ) / 3) / 128) := by ring
    _ ≤ (7 / 1376 : ℝ) * advPMOn (id : (Fin n → σ) → Fin n → σ)
          (fun α => g (ldsFun (n := n) (σ := σ) α)) := by
        refine mul_le_mul_of_nonneg_left (le_trans hadv hcomp) (by norm_num)
    _ ≤ (qQueryOn (id : (Fin n → σ) → Fin n → σ)
          (fun α => g (ldsFun (n := n) (σ := σ) α)) (1 / 3) : ℝ) := hfin
    _ ≤ _ := by exact_mod_cast hpost

/-- `n ≥ 1` puts the power above one. -/
private lemma one_le_lds_pow (hn : 1 ≤ n) :
    (1 : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3) := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  calc (1 : ℝ) = (1 : ℝ) ^ ((2 : ℝ) / 3) := (Real.one_rpow _).symm
    _ ≤ (n : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_le_rpow (by norm_num) h1 (by norm_num)

/-- The absorbed constant: `8192·(1 + 112·2^49·L·x) ≤ 112·2^63·L·x` for
`L ≥ 1`, `x ≥ 1`. -/
private lemma lds_absorb {L x : ℝ} (hL : 1 ≤ L) (hx : 1 ≤ x) :
    uniformExtractionConstant * (1 + 112 * (nodeConst * L * x))
      ≤ 112 * 2 ^ 63 * L * x := by
  have hC : uniformExtractionConstant = (8192 : ℝ) := by
    norm_num [uniformExtractionConstant]
  have hN : nodeConst = (2 : ℝ) ^ 49 := rfl
  rw [hC, hN]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ L - 1) (by linarith : (0:ℝ) ≤ x - 1)]

/-- **The absorbed upper bound**: for `n ≥ 1`,
`Q_{1/3}(ldsFun) ≤ 112·2^63·ldsDepth n·n^{2/3}`. -/
theorem lds_qQuery_upper_absorbed (hn : 1 ≤ n) :
    (qQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
      ≤ 112 * 2 ^ 63 * (ldsDepth n : ℕ) * (n : ℝ) ^ ((2 : ℝ) / 3) := by
  refine le_trans (lds_qQuery_upper hn) (lds_absorb ?_ (one_le_lds_pow hn))
  have h1 : 1 ≤ ldsDepth n := le_max_left _ _
  exact_mod_cast h1

/-- **The native `Õ(n^{2/3})` sandwich**: for `n ≥ 2` and `|σ| ≥ 4n²`,

    7·n^{2/3}/176128 ≤ Q_{1/3}(ldsFun) ≤ min{n, 112·2^63·ldsDepth n·n^{2/3}}. -/
theorem lds_qQuery_sandwich (hn : 2 ≤ n)
    (hq : 4 * (n * n) ≤ Fintype.card σ) :
    7 * (n : ℝ) ^ ((2 : ℝ) / 3) / 176128
        ≤ (qQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
      ∧ (qQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
        ≤ min (n : ℝ)
            (112 * 2 ^ 63 * (ldsDepth n : ℕ) * (n : ℝ) ^ ((2 : ℝ) / 3)) := by
  have hn1 : 1 ≤ n := by omega
  exact ⟨lds_qQuery_lower hn hq, le_min
    (by exact_mod_cast lds_qQuery_upper_length) (lds_qQuery_upper_absorbed hn1)⟩

/-- **The real-logarithm display**: for `n ≥ 1`,
`Q_{1/3}(ldsFun) ≤ 112·2^63·(1 + log₂ n)·n^{2/3}` — the operational form of
the paper's `O(n^{2/3} log n)`. -/
theorem lds_qQuery_le_logb (hn : 1 ≤ n) :
    (qQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
      ≤ 112 * 2 ^ 63 * (1 + Real.logb 2 n) * (n : ℝ) ^ ((2 : ℝ) / 3) := by
  have hx := one_le_lds_pow hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : (0 : ℝ) ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) hn1
  have hdep : ((ldsDepth n : ℕ) : ℝ) ≤ 1 + Real.logb 2 n := by
    rw [show ldsDepth n = max 1 (Nat.clog 2 n) from rfl]
    rcases max_cases 1 (Nat.clog 2 n) with ⟨heq, _⟩ | ⟨heq, hle⟩
    · rw [heq]
      push_cast
      linarith
    · rw [heq]
      by_cases hn2 : 2 ≤ n
      · have hc1 : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by norm_num) (by omega)
        have hlt : 2 ^ (Nat.clog 2 n - 1) < n :=
          Nat.pow_pred_clog_lt_self (b := 2) (x := n) (by norm_num) (by omega)
        have hlogb : ((Nat.clog 2 n - 1 : ℕ) : ℝ) ≤ Real.logb 2 (n : ℝ) := by
          rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity),
            Real.rpow_natCast]
          exact_mod_cast hlt.le
        have hcast : ((Nat.clog 2 n - 1 : ℕ) : ℝ)
            = ((Nat.clog 2 n : ℕ) : ℝ) - 1 := by
          push_cast [Nat.cast_sub hc1]
          ring
        rw [hcast] at hlogb
        linarith
      · have hn1' : n = 1 := by omega
        subst hn1'
        simp [Nat.clog]
  calc (qQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
      ≤ 112 * 2 ^ 63 * (ldsDepth n : ℕ) * (n : ℝ) ^ ((2 : ℝ) / 3) :=
        lds_qQuery_upper_absorbed hn
    _ ≤ 112 * 2 ^ 63 * (1 + Real.logb 2 n) * (n : ℝ) ^ ((2 : ℝ) / 3) := by
        have h63 : (0 : ℝ) < 112 * 2 ^ 63 := by positivity
        nlinarith

/-! ## The one-hot model -/

/-- **The compiler bound in the one-hot model**, at a direct factor two. -/
theorem lds_oneHotQQuery_upper (hn : 1 ≤ n) :
    (oneHotQQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
      ≤ 16384 * (1 + 112 * (nodeConst * (ldsDepth n : ℕ)
          * (n : ℝ) ^ ((2 : ℝ) / 3))) := by
  have h := oneHotQQueryOn_le_two_mul_of_qQueryOn_le (id_det _) (by norm_num)
    (lds_qQuery_upper (σ := σ) hn)
  rw [show (16384 : ℝ) = 2 * uniformExtractionConstant by
    norm_num [uniformExtractionConstant], mul_assoc]
  exact h

/-- **Reading every position, one-hot**: the exact cap `n`. -/
theorem lds_oneHotQQuery_upper_length :
    oneHotQQuery (ldsFun (n := n) (σ := σ)) (1 / 3) ≤ n := by
  have h := oneHotQQuery_le_card (ldsFun (n := n) (σ := σ))
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [Fintype.card_fin] at h

/-- **The unabsorbed minimum form, one-hot.** -/
theorem lds_oneHotQQuery_le_min (hn : 1 ≤ n) :
    (oneHotQQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
      ≤ min (n : ℝ) (16384 * (1 + 112 * (nodeConst * (ldsDepth n : ℕ)
          * (n : ℝ) ^ ((2 : ℝ) / 3)))) :=
  le_min (by exact_mod_cast lds_oneHotQQuery_upper_length)
    (lds_oneHotQQuery_upper hn)

/-- **The one-hot lower bound**:
`7·n^{2/3}/352256 ≤ Q^{1-hot}_{1/3}(ldsFun)`, `352256 = 2·176128`. -/
theorem lds_oneHotQQuery_lower (hn : 2 ≤ n)
    (hq : 4 * (n * n) ≤ Fintype.card σ) :
    7 * (n : ℝ) ^ ((2 : ℝ) / 3) / 352256
      ≤ (oneHotQQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ) := by
  have h := half_le_oneHotQQueryOn_of_le_qQueryOn (id_det _) (by norm_num)
    (lds_qQuery_lower hn hq)
  calc 7 * (n : ℝ) ^ ((2 : ℝ) / 3) / 352256
      = (7 * (n : ℝ) ^ ((2 : ℝ) / 3) / 176128) / 2 := by ring
    _ ≤ _ := h

/-- **The one-hot `Õ(n^{2/3})` sandwich**: for `n ≥ 2` and `|σ| ≥ 4n²`,

    7·n^{2/3}/352256 ≤ Q^{1-hot}_{1/3}(ldsFun)
      ≤ min{n, 112·2^64·ldsDepth n·n^{2/3}}. -/
theorem lds_oneHotQQuery_sandwich (hn : 2 ≤ n)
    (hq : 4 * (n * n) ≤ Fintype.card σ) :
    7 * (n : ℝ) ^ ((2 : ℝ) / 3) / 352256
        ≤ (oneHotQQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
      ∧ (oneHotQQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
        ≤ min (n : ℝ)
            (112 * 2 ^ 64 * (ldsDepth n : ℕ) * (n : ℝ) ^ ((2 : ℝ) / 3)) := by
  have hn1 : 1 ≤ n := by omega
  have hupper : (oneHotQQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
      ≤ 112 * 2 ^ 64 * (ldsDepth n : ℕ) * (n : ℝ) ^ ((2 : ℝ) / 3) := by
    have h := oneHotQQueryOn_le_two_mul_of_qQueryOn_le (id_det _) (by norm_num)
      (lds_qQuery_upper_absorbed (σ := σ) hn1)
    calc (oneHotQQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
        ≤ 2 * (112 * 2 ^ 63 * (ldsDepth n : ℕ) * (n : ℝ) ^ ((2 : ℝ) / 3)) := h
      _ = 112 * 2 ^ 64 * (ldsDepth n : ℕ) * (n : ℝ) ^ ((2 : ℝ) / 3) := by ring
  exact ⟨lds_oneHotQQuery_lower hn hq, le_min
    (by exact_mod_cast lds_oneHotQQuery_upper_length) hupper⟩

/-- **The real-logarithm display, one-hot**: for `n ≥ 1`,
`Q^{1-hot}_{1/3}(ldsFun) ≤ 112·2^64·(1 + log₂ n)·n^{2/3}`. -/
theorem lds_oneHotQQuery_le_logb (hn : 1 ≤ n) :
    (oneHotQQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
      ≤ 112 * 2 ^ 64 * (1 + Real.logb 2 n) * (n : ℝ) ^ ((2 : ℝ) / 3) := by
  have h := oneHotQQueryOn_le_two_mul_of_qQueryOn_le (id_det _) (by norm_num)
    (lds_qQuery_le_logb (σ := σ) hn)
  calc (oneHotQQuery (ldsFun (n := n) (σ := σ)) (1 / 3) : ℝ)
      ≤ 2 * (112 * 2 ^ 63 * (1 + Real.logb 2 n) * (n : ℝ) ^ ((2 : ℝ) / 3)) := h
    _ = 112 * 2 ^ 64 * (1 + Real.logb 2 n) * (n : ℝ) ^ ((2 : ℝ) / 3) := by ring

end QuantumQueryComplexity
