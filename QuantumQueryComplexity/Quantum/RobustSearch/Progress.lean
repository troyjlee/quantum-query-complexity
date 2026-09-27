import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option linter.style.header false

/-!
# Robust search: the scalar progress analysis

Pure real analysis, isolated from the circuit bookkeeping.  `a n`, `b n` are the accepted
marked and accepted unmarked masses at level `n ≥ 1`; the fresh test of level `n` has error
at most `2^{-(n+9)}`.

* `bad_le` — from `b 1 ≤ 2^{-10}` and `b (n+1) ≤ 2^{-(n+10)}·(3−4p)²·b n` with `0 ≤ p ≤ 1`:
  `b n ≤ 2^{-(n+9)}` at every level, unconditionally (also after the marked mass has
  saturated and the amplification overshoots).
* `progress` — from `a 1 ≥ (1 − 2^{-10})/m` and, whenever `a n < 1/10`,
  `a (n+1) ≥ (1 − 2^{-(n+10)})·(3 − 4(a n + b n))²·a n`:
  **some level `1 ≤ n ≤ K+1` has `a n ≥ 1/10`, as soon as `m ≤ 9^K`.**

The growth factor is `9·(1 − (8/3)a − small)`, not `9`; the loss `(8/3)·a n` is absorbed by
the potential `a·(1 + a)`, which grows by a full factor `9·(1 − 2^{-(n+5)})` per level while
`a < 1/10`: no backward induction and no sum over levels is needed.  High initial marked mass
is covered by the same statement (`n = 1`); zero marked mass makes `a 1 ≥ …` false and is
handled separately by `bad_le`.
-/

namespace QuantumQueryComplexity.RobustSearch

/-- `(3 − 4p)² ≤ 9` for a probability `p`. -/
lemma sq_le_nine {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : (3 - 4 * p) ^ 2 ≤ 9 := by nlinarith

theorem bad_le (b p : ℕ → ℝ) (hb0 : ∀ n, 0 ≤ b n) (hp0 : ∀ n, 0 ≤ p n) (hp1 : ∀ n, p n ≤ 1)
    (hb1 : b 1 ≤ (1 / 2) ^ 10)
    (hstep : ∀ n, 1 ≤ n → b (n + 1) ≤ (1 / 2) ^ (n + 10) * (3 - 4 * p n) ^ 2 * b n) :
    ∀ n, 1 ≤ n → b n ≤ (1 / 2 : ℝ) ^ (n + 9) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simpa using hb1
  | succ n hn ih =>
      have h9 := sq_le_nine (hp0 n) (hp1 n)
      have hpow : (0 : ℝ) < (1 / 2) ^ (n + 10) := by positivity
      have hsmall : (1 / 2 : ℝ) ^ (n + 9) ≤ (1 / 2) ^ 10 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have hsq : 0 ≤ (3 - 4 * p n) ^ 2 := sq_nonneg _
      calc b (n + 1) ≤ (1 / 2) ^ (n + 10) * (3 - 4 * p n) ^ 2 * b n := hstep n hn
        _ ≤ (1 / 2) ^ (n + 10) * 9 * (1 / 2) ^ 10 := by
            have : (3 - 4 * p n) ^ 2 * b n ≤ 9 * (1 / 2) ^ 10 :=
              mul_le_mul h9 (ih.trans hsmall) (hb0 n) (by norm_num)
            nlinarith
        _ ≤ (1 / 2) ^ (n + 1 + 9) := by
            rw [show n + 1 + 9 = n + 10 from rfl]
            nlinarith

/-- One step of the potential `a(1+a)`. -/
lemma potential_step {a b a' ε c : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 10) (hb0 : 0 ≤ b)
    (hε0 : 0 ≤ ε) (hη : ε + 8 / 3 * b ≤ c / 3) (hc : c ≤ 1 / 32)
    (hstep : (1 - ε) * (3 - 4 * (a + b)) ^ 2 * a ≤ a') :
    9 * (1 - c) * (a * (1 + a)) ≤ a' * (1 + a') := by
  have hη0 : 0 ≤ ε + 8 / 3 * b := by positivity
  have hc0 : 0 ≤ c := by linarith
  have hε1 : ε ≤ 1 / 96 := by linarith
  have hb1 : b ≤ 1 / 256 := by linarith
  -- the step factor
  have hs : 9 * (1 - 8 / 3 * a - (ε + 8 / 3 * b)) ≤ (1 - ε) * (3 - 4 * (a + b)) ^ 2 := by
    have h1 : 9 * (1 - 8 / 3 * (a + b)) ≤ (3 - 4 * (a + b)) ^ 2 := by
      nlinarith [sq_nonneg (a + b)]
    have h3 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 1 - ε by linarith)
    have h4 : 0 ≤ ε * a := mul_nonneg hε0 ha0
    have h5 : 0 ≤ ε * b := mul_nonneg hε0 hb0
    nlinarith
  obtain ⟨s, hs'⟩ : ∃ s, s = 1 - 8 / 3 * a - (ε + 8 / 3 * b) := ⟨_, rfl⟩
  rw [← hs'] at hs
  have hs0 : 0 ≤ s := by rw [hs']; linarith
  have hs1 : s ≤ 1 := by rw [hs']; linarith
  have ha' : 9 * s * a ≤ a' :=
    le_trans (by have := mul_le_mul_of_nonneg_right hs ha0; linarith) hstep
  have hx0 : 0 ≤ 9 * s * a := by positivity
  have hmono : 9 * s * a * (1 + 9 * s * a) ≤ a' * (1 + a') := by
    have h := mul_nonneg (sub_nonneg.mpr ha') (show (0 : ℝ) ≤ 1 + a' + 9 * s * a by linarith)
    nlinarith
  refine le_trans ?_ hmono
  have hq : (1 + a) ≤ (1 - 8 / 3 * a) * (1 + 9 * (1 - 8 / 3 * a) * a) := by
    have hid : (1 - 8 / 3 * a) * (1 + 9 * (1 - 8 / 3 * a) * a) - (1 + a)
        = a * (16 / 3 - 48 * a + 64 * a ^ 2) := by ring
    have : 0 ≤ a * (16 / 3 - 48 * a + 64 * a ^ 2) :=
      mul_nonneg ha0 (by nlinarith [sq_nonneg a])
    linarith
  have hkey : (1 + a) * (1 - c) ≤ s * (1 + 9 * s * a) := by
    have hexp : s * (1 + 9 * s * a)
        = (1 - 8 / 3 * a) * (1 + 9 * (1 - 8 / 3 * a) * a)
          - (ε + 8 / 3 * b) * (1 + 18 * (1 - 8 / 3 * a) * a) + 9 * (ε + 8 / 3 * b) ^ 2 * a := by
      rw [hs']; ring
    have h18 : 1 + 18 * (1 - 8 / 3 * a) * a ≤ 3 := by nlinarith [sq_nonneg a]
    have hR : (ε + 8 / 3 * b) * (1 + 18 * (1 - 8 / 3 * a) * a) ≤ c :=
      le_trans (mul_le_mul_of_nonneg_left h18 hη0) (by linarith)
    have h9 : 0 ≤ 9 * (ε + 8 / 3 * b) ^ 2 * a := by positivity
    have hac : 0 ≤ a * c := mul_nonneg ha0 hc0
    nlinarith
  calc 9 * (1 - c) * (a * (1 + a)) = 9 * a * ((1 + a) * (1 - c)) := by ring
    _ ≤ 9 * a * (s * (1 + 9 * s * a)) := mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = 9 * s * a * (1 + 9 * s * a) := by ring

theorem progress (a b : ℕ → ℝ) (m K : ℕ) (hm : 0 < m) (hK : (m : ℝ) ≤ 9 ^ K)
    (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n)
    (hb : ∀ n, 1 ≤ n → b n ≤ (1 / 2 : ℝ) ^ (n + 9))
    (ha1 : (1 - (1 / 2) ^ 10) / m ≤ a 1)
    (hstep : ∀ n, 1 ≤ n → a n < 1 / 10 →
      (1 - (1 / 2) ^ (n + 10)) * (3 - 4 * (a n + b n)) ^ 2 * a n ≤ a (n + 1)) :
    ∃ n, 1 ≤ n ∧ n ≤ K + 1 ∧ 1 / 10 ≤ a n := by
  by_contra hcon
  have hlt : ∀ n, 1 ≤ n → n ≤ K + 1 → a n < 1 / 10 := fun n h1 h2 =>
    not_le.mp fun h => hcon ⟨n, h1, h2, h⟩
  -- the potential grows by `9(1 − 2^{-(n+5)})` per level
  have hpot : ∀ n, 1 ≤ n → n ≤ K + 1 →
      9 ^ (n - 1) * (1 / 2 + (1 / 2) ^ (n + 4)) * a 1 ≤ a n * (1 + a n) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        intro _
        have := ha0 1
        norm_num
        nlinarith
    | succ n hn ih =>
        intro hle
        have ihn := ih (by omega)
        have hc : (1 / 2 : ℝ) ^ (n + 5) ≤ 1 / 32 := by
          calc (1 / 2 : ℝ) ^ (n + 5) ≤ (1 / 2) ^ 5 :=
                pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
            _ = 1 / 32 := by norm_num
        have hη : (1 / 2 : ℝ) ^ (n + 10) + 8 / 3 * b n ≤ (1 / 2) ^ (n + 5) / 3 := by
          have h1 := hb n hn
          have e1 : (1 / 2 : ℝ) ^ (n + 10) = (1 / 2) ^ (n + 5) * (1 / 32) := by
            ring
          have e2 : (1 / 2 : ℝ) ^ (n + 9) = (1 / 2) ^ (n + 5) * (1 / 16) := by
            ring
          have hpos : (0 : ℝ) < (1 / 2) ^ (n + 5) := by positivity
          rw [e1]; rw [e2] at h1
          nlinarith
        have hstep' := potential_step (ha0 n) (hlt n hn (by omega)) (hb0 n) (by positivity) hη hc
          (hstep n hn (hlt n hn (by omega)))
        have hn1 : n + 1 - 1 = (n - 1) + 1 := by omega
        rw [hn1, pow_succ]
        have e3 : (1 / 2 : ℝ) ^ (n + 1 + 4) = (1 / 2) ^ (n + 5) := rfl
        have e4 : (1 / 2 : ℝ) ^ (n + 4) = 2 * (1 / 2) ^ (n + 5) := by
          rw [show n + 5 = (n + 4) + 1 from rfl, pow_succ]; ring
        rw [e3]
        rw [e4] at ihn
        have hpos : (0 : ℝ) < (1 / 2) ^ (n + 5) := by positivity
        have h9 : (0 : ℝ) ≤ 9 ^ (n - 1) * a 1 := mul_nonneg (by positivity) (ha0 1)
        -- `(1/2 + 2t)(1 − t) ≥ 1/2 + t` for `t ≤ 1/32`
        have halg : (1 / 2 + (1 / 2 : ℝ) ^ (n + 5))
            ≤ (1 - (1 / 2) ^ (n + 5)) * (1 / 2 + 2 * (1 / 2) ^ (n + 5)) := by nlinarith
        calc 9 ^ (n - 1) * 9 * (1 / 2 + (1 / 2) ^ (n + 5)) * a 1
            ≤ 9 * (1 - (1 / 2) ^ (n + 5))
                * (9 ^ (n - 1) * (1 / 2 + 2 * (1 / 2) ^ (n + 5)) * a 1) := by
              nlinarith [mul_le_mul_of_nonneg_left halg h9]
          _ ≤ 9 * (1 - (1 / 2) ^ (n + 5)) * (a n * (1 + a n)) :=
              mul_le_mul_of_nonneg_left ihn (by nlinarith)
          _ ≤ a (n + 1) * (1 + a (n + 1)) := hstep'
  have hfin := hpot (K + 1) (by omega) le_rfl
  have hsmall := hlt (K + 1) (by omega) le_rfl
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Nat.add_sub_cancel] at hfin
  have h1 : (1 - (1 / 2) ^ 10) ≤ 9 ^ K * a 1 := by
    have := (div_le_iff₀ hm').mp ha1
    have ha1' := ha0 1
    nlinarith
  have hpos : (0 : ℝ) < (1 / 2) ^ (K + 1 + 4) := by positivity
  have h2 : (1 / 2 : ℝ) * (1 - (1 / 2) ^ 10) ≤ a (K + 1) * (1 + a (K + 1)) := by
    refine le_trans ?_ hfin
    have : 9 ^ K * (1 / 2 + (1 / 2 : ℝ) ^ (K + 1 + 4)) * a 1
        = (1 / 2 + (1 / 2 : ℝ) ^ (K + 1 + 4)) * (9 ^ K * a 1) := by ring
    rw [this]
    nlinarith
  have := ha0 (K + 1)
  norm_num at h2
  nlinarith

end QuantumQueryComplexity.RobustSearch
