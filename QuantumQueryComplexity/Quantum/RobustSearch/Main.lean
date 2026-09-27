import QuantumQueryComplexity.Quantum.RobustSearch.Filter
import QuantumQueryComplexity.Quantum.RobustSearch.Progress
import QuantumQueryComplexity.Quantum.FirstOf
set_option synthInstance.maxSize 3200
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Robust search: the algorithm and its guarantee

Search with bounded-error tests at `O(T·√m)` queries, **without a logarithmic factor**
(Høyer–Mosca–de Wolf).  Everything is a compiled `QAlg` with a fixed worst-case budget.

The algorithm `rsAlg bank i₀ K` runs, for every scale `n = 1, …, K+1`, twelve independent
copies of the level-`n` routine and returns the index of the first copy whose *computed*
flag is set (`OTrial.firstOf`).  No choice depends on the number of marked candidates.

With `a n`, `b n` the accepted marked / unmarked masses of level `n` on a fixed input:

* `bMass_le` — `b n ≤ 2^{-(n+9)}` at every scale, so all `12(K+1)` copies together return an
  unmarked index with probability `≤ 12·2^{-9}` (union bound): the recursion's own filters are
  accurate enough that **no separate final validation is needed**;
* `exists_level` — if a candidate is marked and `|I| ≤ 9^K`, some scale has `a n ≥ 1/10`
  (`RobustSearch.progress`), so the twelve copies of that scale all fail with probability
  `≤ (9/10)^12`;
* `two_thirds_le_good` — `Pr[a marked index] ≥ 1 − (9/10)^12 − 12·2^{-9} ≥ 2/3`;
* `two_thirds_le_none` — with no marked candidate, `Pr[none] ≥ 1 − 12·2^{-9} ≥ 2/3`.

Budget: `rsAlg_q : … = trialsLen T (K+1)`, the exact sum `12·∑ₙ levelLen T n`, and
`two_mul_trialsLen_le : 2·trialsLen T k + 2268·T ≤ 756·T·3^{k+1}`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

section Analysis

variable (bank : ℕ → TestBank ι σ I) (i₀ : I) (a : ι → σ) (mk : I → Bool)

/-- The accepted marked mass of level `n`. -/
noncomputable def aMass (n : ℕ) : ℝ := ∑ i, if mk i then (rsLevel bank i₀ n).u a i else 0

/-- The accepted unmarked mass of level `n`. -/
noncomputable def bMass (n : ℕ) : ℝ := ∑ i, if mk i then 0 else (rsLevel bank i₀ n).u a i

lemma aMass_nonneg (n : ℕ) : 0 ≤ aMass bank i₀ a mk n :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> [exact RSLevel.u_nonneg _ _ _; exact le_rfl]

lemma bMass_nonneg (n : ℕ) : 0 ≤ bMass bank i₀ a mk n :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> [exact le_rfl; exact RSLevel.u_nonneg _ _ _]

lemma aMass_add_bMass (n : ℕ) :
    aMass bank i₀ a mk n + bMass bank i₀ a mk n = (rsLevel bank i₀ n).p a := by
  rw [RSLevel.p_eq_sum, aMass, bMass, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

/-- The tests of the bank `n` have error at most `2^{-(n+9)}` on the input `a`. -/
structure BankOK : Prop where
  marked : ∀ n i, 1 ≤ n → mk i = true → 1 - (1 / 2 : ℝ) ^ (n + 9) ≤ (bank n).accProb a i
  unmarked : ∀ n i, 1 ≤ n → mk i = false → (bank n).accProb a i ≤ (1 / 2 : ℝ) ^ (n + 9)

variable {bank i₀ a mk}

lemma aMass_succ_ge (h : BankOK bank a mk) (n : ℕ) :
    (1 - (1 / 2) ^ (n + 10))
        * (3 - 4 * (aMass bank i₀ a mk n + bMass bank i₀ a mk n)) ^ 2 * aMass bank i₀ a mk n
      ≤ aMass bank i₀ a mk (n + 1) := by
  rw [aMass_add_bMass, aMass, aMass, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : mk i = true
  · rw [if_pos hi, if_pos hi, rsLevel_u_succ]
    have hτ := h.marked (n + 1) i (by omega) hi
    rw [show n + 1 + 9 = n + 10 from rfl] at hτ
    have hu := (rsLevel bank i₀ n).u_nonneg a i
    have hsq : 0 ≤ (3 - 4 * (rsLevel bank i₀ n).p a) ^ 2 * (rsLevel bank i₀ n).u a i :=
      mul_nonneg (sq_nonneg _) hu
    nlinarith [mul_le_mul_of_nonneg_left hτ hsq]
  · rw [if_neg hi, if_neg hi, mul_zero]

lemma bMass_succ_le (h : BankOK bank a mk) (n : ℕ) :
    bMass bank i₀ a mk (n + 1)
      ≤ (1 / 2) ^ (n + 10) * (3 - 4 * (rsLevel bank i₀ n).p a) ^ 2 * bMass bank i₀ a mk n := by
  rw [bMass, bMass, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : mk i = true
  · rw [if_pos hi, if_pos hi, mul_zero]
  · rw [if_neg hi, if_neg hi, rsLevel_u_succ]
    have hτ := h.unmarked (n + 1) i (by omega) (by simpa using hi)
    rw [show n + 1 + 9 = n + 10 from rfl] at hτ
    have hu := (rsLevel bank i₀ n).u_nonneg a i
    have hsq : 0 ≤ (3 - 4 * (rsLevel bank i₀ n).p a) ^ 2 * (rsLevel bank i₀ n).u a i :=
      mul_nonneg (sq_nonneg _) hu
    nlinarith [mul_le_mul_of_nonneg_left hτ hsq]

lemma rsLevel_u_one (i : I) :
    (rsLevel bank i₀ 1).u a i = (bank 1).accProb a i / Fintype.card I := by
  rw [rsLevel_u_succ]
  show (3 - 4 * (rsBase ι σ I).p a) ^ 2 * (rsBase ι σ I).u a i * _ = _
  rw [rsBase_p, rsBase_u]
  ring

lemma aMass_one_ge (h : BankOK bank a mk) (hex : ∃ i, mk i = true) :
    (1 - (1 / 2) ^ 10) / (Fintype.card I : ℝ) ≤ aMass bank i₀ a mk 1 := by
  obtain ⟨i, hi⟩ := hex
  have hc : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => if mk i then (rsLevel bank i₀ 1).u a i
    else 0) (fun j _ => by split_ifs <;> [exact RSLevel.u_nonneg _ _ _; exact le_rfl])
    (Finset.mem_univ i))
  simp only [hi, if_true]
  rw [rsLevel_u_one]
  exact div_le_div_of_nonneg_right (h.marked 1 i le_rfl hi) hc.le

lemma bMass_one_le (h : BankOK bank a mk) : bMass bank i₀ a mk 1 ≤ (1 / 2) ^ 10 := by
  have hc : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  calc bMass bank i₀ a mk 1 ≤ ∑ _i : I, (1 / 2 : ℝ) ^ 10 / Fintype.card I := by
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases hi : mk i = true
        · rw [if_pos hi]; positivity
        · rw [if_neg hi, rsLevel_u_one]
          exact div_le_div_of_nonneg_right (h.unmarked 1 i le_rfl (by simpa using hi)) hc.le
    _ = (1 / 2) ^ 10 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

/-- **The unmarked mass is small at every scale.** -/
theorem bMass_le (h : BankOK bank a mk) (n : ℕ) (hn : 1 ≤ n) :
    bMass bank i₀ a mk n ≤ (1 / 2) ^ (n + 9) :=
  RobustSearch.bad_le (bMass bank i₀ a mk) (fun n => (rsLevel bank i₀ n).p a)
    (bMass_nonneg bank i₀ a mk) (fun n => RSLevel.p_nonneg _ a) (fun n => RSLevel.p_le_one _ a)
    (bMass_one_le h) (fun n _ => bMass_succ_le h n) n hn

/-- **Some scale has marked mass at least `1/10`.** -/
theorem exists_level (h : BankOK bank a mk) (hex : ∃ i, mk i = true) {K : ℕ}
    (hK : Fintype.card I ≤ 9 ^ K) :
    ∃ n, 1 ≤ n ∧ n ≤ K + 1 ∧ 1 / 10 ≤ aMass bank i₀ a mk n :=
  RobustSearch.progress (aMass bank i₀ a mk) (bMass bank i₀ a mk) (Fintype.card I) K
    Fintype.card_pos (by exact_mod_cast hK) (aMass_nonneg bank i₀ a mk)
    (bMass_nonneg bank i₀ a mk) (fun n hn => bMass_le h n hn) (aMass_one_ge h hex)
    (fun n _ _ => aMass_succ_ge h n)

end Analysis

/-! ## The trials -/

section Trials

variable (bank : ℕ → TestBank ι σ I) (i₀ : I)

/-- One run of the level-`n` routine, as a trial. -/
noncomputable def rsTrial (n : ℕ) : OTrial ι σ I where
  W := (rsLevel bank i₀ n).Y
  alg := (rsLevel bank i₀ n).alg
  q := (rsLevel bank i₀ n).A.len

lemma rsTrial_pr_some (n : ℕ) (a : ι → σ) (i : I) :
    (rsTrial bank i₀ n).pr a (some i) = (rsLevel bank i₀ n).u a i :=
  (rsLevel bank i₀ n).alg_prob_some a i

lemma rsTrial_pr_none (n : ℕ) (a : ι → σ) :
    (rsTrial bank i₀ n).pr a none = 1 - (rsLevel bank i₀ n).p a :=
  (rsLevel bank i₀ n).alg_prob_none a

/-- Twelve copies at each of the scales `k, k−1, …, 1`. -/
noncomputable def rsTrials : ℕ → List (OTrial ι σ I)
  | 0 => []
  | k + 1 => List.replicate 12 (rsTrial bank i₀ (k + 1)) ++ rsTrials k

/-- **The robust search algorithm** with scale cutoff `K`. -/
noncomputable def rsAlg (K : ℕ) : OTrial ι σ I := OTrial.firstOf (rsTrials bank i₀ (K + 1))

/-- The total query count of the trials. -/
def trialsLen (T : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 12 * levelLen T (k + 1) + trialsLen T k

theorem two_mul_trialsLen_le (T k : ℕ) :
    2 * trialsLen T k + 2268 * T ≤ 756 * T * 3 ^ (k + 1) := by
  induction k with
  | zero => simp [trialsLen]; omega
  | succ k ih =>
      have h := levelLen_le T (k + 1)
      rw [trialsLen, pow_succ 3 (k + 1)]
      nlinarith

theorem rsAlg_q {T : ℕ} (hbank : ∀ n, (bank n).F.len = 12 * (n + 9) * T) (K : ℕ) :
    (rsAlg bank i₀ K).q = trialsLen T (K + 1) := by
  rw [rsAlg, OTrial.firstOf_q]
  generalize K + 1 = k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [rsTrials, List.map_append, List.sum_append, ih, List.map_replicate, List.sum_replicate,
        trialsLen, smul_eq_mul]
      congr 2
      exact rsLevel_len bank i₀ T hbank (k + 1)

variable {bank i₀} {a : ι → σ} {mk : I → Bool}

lemma rsTrial_good (n : ℕ) :
    (rsTrial bank i₀ n).good (fun i => mk i = true) a = aMass bank i₀ a mk n := by
  rw [OTrial.good, aMass]
  exact Finset.sum_congr rfl fun i _ => by rw [rsTrial_pr_some]

lemma rsTrial_bad (n : ℕ) :
    (rsTrial bank i₀ n).bad (fun i => mk i = true) a = bMass bank i₀ a mk n := by
  rw [OTrial.bad, bMass]
  exact Finset.sum_congr rfl fun i _ => by rw [rsTrial_pr_some]

lemma bad_sum_le (h : BankOK bank a mk) (k : ℕ) :
    ((rsTrials bank i₀ k).map fun T => T.bad (fun i => mk i = true) a).sum
      ≤ 12 * ((1 / 2) ^ 9 - (1 / 2) ^ (k + 9)) := by
  induction k with
  | zero => simp [rsTrials]
  | succ k ih =>
      rw [rsTrials, List.map_append, List.sum_append, List.map_replicate, List.sum_replicate,
        rsTrial_bad, nsmul_eq_mul]
      have hb := bMass_le (i₀ := i₀) h (k + 1) (by omega)
      have e : (1 / 2 : ℝ) ^ (k + 9) = 2 * (1 / 2) ^ (k + 1 + 9) := by
        rw [show k + 1 + 9 = (k + 9) + 1 from by ring, pow_succ]; ring
      push_cast
      nlinarith

lemma none_prod_nonneg (k : ℕ) :
    0 ≤ ((rsTrials bank i₀ k).map fun T => T.pr a none).prod :=
  List.prod_nonneg fun x hx => by
    obtain ⟨T, _, rfl⟩ := List.mem_map.mp hx
    exact T.pr_nonneg a none

lemma none_prod_le_one (k : ℕ) :
    ((rsTrials bank i₀ k).map fun T => T.pr a none).prod ≤ 1 := by
  induction k with
  | zero => simp [rsTrials]
  | succ k ih =>
      rw [rsTrials, List.map_append, List.prod_append, List.map_replicate, List.prod_replicate]
      have h1 : (rsTrial bank i₀ (k + 1)).pr a none ^ 12 ≤ 1 :=
        pow_le_one₀ (OTrial.pr_nonneg _ _ _) (OTrial.pr_le_one _ _ _)
      exact mul_le_one₀ h1 (none_prod_nonneg k) ih

lemma none_prod_le (k : ℕ) (hex : ∃ n, 1 ≤ n ∧ n ≤ k ∧ 1 / 10 ≤ aMass bank i₀ a mk n) :
    ((rsTrials bank i₀ k).map fun T => T.pr a none).prod ≤ (9 / 10) ^ 12 := by
  induction k with
  | zero => obtain ⟨n, h1, h2, _⟩ := hex; omega
  | succ k ih =>
      rw [rsTrials, List.map_append, List.prod_append, List.map_replicate, List.prod_replicate]
      obtain ⟨n, h1, h2, h3⟩ := hex
      have hx0 := (rsTrial bank i₀ (k + 1)).pr_nonneg a none
      have hx1 := (rsTrial bank i₀ (k + 1)).pr_le_one a none
      by_cases hn : n = k + 1
      · subst hn
        have hx : (rsTrial bank i₀ (k + 1)).pr a none ≤ 9 / 10 := by
          rw [rsTrial_pr_none, ← aMass_add_bMass bank i₀ a mk]
          have := bMass_nonneg bank i₀ a mk (k + 1)
          linarith
        calc _ ≤ (9 / 10 : ℝ) ^ 12 * 1 :=
              mul_le_mul (pow_le_pow_left₀ hx0 hx 12) (none_prod_le_one k) (none_prod_nonneg k)
                (by positivity)
          _ = _ := mul_one _
      · calc _ ≤ 1 * (9 / 10 : ℝ) ^ 12 :=
              mul_le_mul (pow_le_one₀ hx0 hx1) (ih ⟨n, h1, by omega, h3⟩) (none_prod_nonneg k)
                (by norm_num)
          _ = _ := one_mul _

/-- **A marked index is returned with probability at least `2/3`.** -/
theorem two_thirds_le_good (h : BankOK bank a mk) (hex : ∃ i, mk i = true) {K : ℕ}
    (hK : Fintype.card I ≤ 9 ^ K) :
    2 / 3 ≤ (rsAlg bank i₀ K).good (fun i => mk i = true) a := by
  rw [OTrial.good_eq, rsAlg, OTrial.pr_firstOf_none]
  have h1 := none_prod_le (K + 1) (exists_level (i₀ := i₀) h hex hK)
  have h2 := (OTrial.bad_firstOf_le (fun i => mk i = true) (rsTrials bank i₀ (K + 1)) a).trans
    (bad_sum_le h (K + 1))
  have hpos : (0 : ℝ) < (1 / 2) ^ (K + 1 + 9) := by positivity
  norm_num at h1 h2 ⊢
  linarith

/-- **With no marked candidate, `none` is returned with probability at least `2/3`.** -/
theorem two_thirds_le_none (h : BankOK bank a mk) (hno : ∀ i, mk i = false) (K : ℕ) :
    2 / 3 ≤ (rsAlg bank i₀ K).pr a none := by
  have hg : (rsAlg bank i₀ K).good (fun i => mk i = true) a = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [if_neg (by simp [hno i])]
  have h0 := OTrial.good_eq (fun i => mk i = true) (rsAlg bank i₀ K) a
  have h2 := (OTrial.bad_firstOf_le (fun i => mk i = true) (rsTrials bank i₀ (K + 1)) a).trans
    (bad_sum_le h (K + 1))
  have hpos : (0 : ℝ) < (1 / 2) ^ (K + 1 + 9) := by positivity
  rw [hg] at h0
  rw [rsAlg] at h0 ⊢
  norm_num at h2 ⊢
  linarith

end Trials

end QuantumQueryComplexity
