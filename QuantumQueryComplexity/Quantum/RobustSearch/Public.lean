import QuantumQueryComplexity.Quantum.RobustSearch.Main
set_option synthInstance.maxSize 3200
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Robust search: the public theorem

The caller supplies, for each of `m` candidates, a quantum algorithm `A i` (own workspace,
initial state and readout) and a budget `q i ≤ T`, such that on every input `x` of the promise
`A i` outputs `b x i` with probability at least `2/3` within `q i` queries.  Then

* `robustSearch A q T : OTrial ι σ (Fin m)` is a compiled algorithm with output
  `Option (Fin m)`; it is built from `A`, `q`, `T` alone — never from `b`, `read` or `x`;
* `robustSearch_q : (robustSearch A q T).q = robustSearchBudget m T`, and
  `robustSearchBudget_le : robustSearchBudget m T ≤ 10206 · T · ⌈√m⌉` — **no logarithm**;
* `robustSearch_solves` — it solves the relation `SearchOK b` with error `1/3`: if some
  candidate is marked it returns a marked index with probability `≥ 2/3`, otherwise it
  returns `none` with probability `≥ 2/3`;
* `robustOr_computes` — reading only whether the output is `some` computes the OR of the
  predicates with error `1/3` at the same budget.

This is a two-sided-error interface: an unmarked index *can* be returned (with small
probability), and nothing is claimed about the distribution over marked indices; the exact
verifier search of `Amplitude/Search.lean` keeps those stronger guarantees.  The predicates
may read the same input positions; no independence or injectivity is assumed.  `m = 0` is
the zero-query constant `none`; `T = 0` is allowed.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

/-- **Correct answers of a search**: a marked index, or `none` when nothing is marked. -/
def SearchOK {X I : Type} (b : X → I → Bool) (x : X) : Option I → Prop
  | some i => b x i = true
  | none => ∀ i, b x i = false

instance {X I : Type} [Fintype I] (b : X → I → Bool) (x : X) : DecidablePred (SearchOK b x) :=
  fun o => by cases o <;> simp only [SearchOK] <;> infer_instance

/-- The success probability of a relation is the summed probability of its valid outputs. -/
lemma goodProb_eq_sum_qProb {H O : Type} [Fintype H] [Fintype O] [DecidableEq O] (rd : H → O)
    (G : O → Prop) [DecidablePred G] (ψ : H → ℂ) :
    goodProb rd G ψ = ∑ o, if G o then qProb rd ψ o else 0 := by
  rw [goodProb, show (fun h => decide (G (rd h))) = (fun o => decide (G o)) ∘ rd from rfl,
    qProb_comp, Finset.sum_filter]
  exact Finset.sum_congr rfl fun o _ => by simp

section Supplied

variable {I : Type} [Fintype I] [DecidableEq I] {W : I → Type} [∀ i, Fintype (W i)]
  [∀ i, DecidableEq (W i)]

/-- The filter of scale `n`: `12·(n+9)` copies of the selected test, read by majority. -/
noncomputable def rsBank (A : ∀ i, QAlg ι σ Bool (W i)) (q : I → ℕ) (T : ℕ) (n : ℕ) :
    TestBank ι σ I :=
  (TestBank.ofAlgs A q T).pow (12 * (n + 9))

lemma rsBank_len (A : ∀ i, QAlg ι σ Bool (W i)) (q : I → ℕ) (T : ℕ) (n : ℕ) :
    (rsBank A q T n).F.len = 12 * (n + 9) * T := by
  rw [rsBank, TestBank.pow_len, TestBank.ofAlgs_len]

theorem bankOK_rsBank {A : ∀ i, QAlg ι σ Bool (W i)} {q : I → ℕ} {T : ℕ} (hq : ∀ i, q i ≤ T)
    {a : ι → σ} {mk : I → Bool} (hA : ∀ i, 2 / 3 ≤ (A i).prob a (q i) (mk i)) :
    BankOK (rsBank A q T) a mk where
  marked := fun n i _ hi => by
    refine TestBank.accProb_pow_twelve_ge _ ?_ (n + 9)
    rw [TestBank.accProb_ofAlgs hq, ← hi]
    exact hA i
  unmarked := fun n i _ hi => by
    refine TestBank.accProb_pow_twelve_le _ ?_ (n + 9)
    rw [TestBank.accProb_ofAlgs hq, ← hi]
    exact hA i

end Supplied

section Public

variable {m : ℕ} {W : Fin m → Type} [∀ i, Fintype (W i)] [∀ i, DecidableEq (W i)]

/-- **Robust search among `m` bounded-error tests.** -/
noncomputable def robustSearch (A : ∀ i, QAlg ι σ Bool (W i)) (q : Fin m → ℕ) (T : ℕ) :
    OTrial ι σ (Fin m) :=
  if h : 0 < m then
    haveI : Nonempty (Fin m) := ⟨⟨0, h⟩⟩
    rsAlg (rsBank A q T) ⟨0, h⟩ (Nat.clog 9 m)
  else OTrial.never

/-- **The budget**: an explicit function of `m` and `T`. -/
def robustSearchBudget (m T : ℕ) : ℕ := if 0 < m then trialsLen T (Nat.clog 9 m + 1) else 0

theorem robustSearch_q (A : ∀ i, QAlg ι σ Bool (W i)) (q : Fin m → ℕ) (T : ℕ) :
    (robustSearch A q T).q = robustSearchBudget m T := by
  by_cases h : 0 < m
  · haveI : Nonempty (Fin m) := ⟨⟨0, h⟩⟩
    rw [robustSearch, dif_pos h, robustSearchBudget, if_pos h]
    exact rsAlg_q _ _ (rsBank_len A q T) _
  · rw [robustSearch, dif_neg h, robustSearchBudget, if_neg h]
    rfl

/-- `3^{clog₉ m} ≤ 3·⌈√m⌉`. -/
lemma three_pow_clog_le {m : ℕ} (hm : 0 < m) :
    3 ^ Nat.clog 9 m ≤ 3 * ⌈Real.sqrt m⌉₊ := by
  have hceil : 1 ≤ ⌈Real.sqrt m⌉₊ := by
    rw [Nat.one_le_iff_ne_zero, Ne, Nat.ceil_eq_zero, not_le]
    exact Real.sqrt_pos.mpr (by exact_mod_cast hm)
  rcases Nat.lt_or_ge 1 m with h1 | h1
  · have hpos := Nat.clog_pos (by norm_num : 1 < 9) h1
    have hlt := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 9) h1
    obtain ⟨k, hk⟩ : ∃ k, Nat.clog 9 m = k + 1 := ⟨Nat.clog 9 m - 1, by omega⟩
    rw [hk, Nat.pred_succ] at hlt
    rw [hk, pow_succ, mul_comm]
    refine Nat.mul_le_mul_left 3 ?_
    have hreal : ((3 ^ k : ℕ) : ℝ) < Real.sqrt m := by
      rw [Real.lt_sqrt (by positivity)]
      have : ((9 ^ k : ℕ) : ℝ) < m := by exact_mod_cast hlt
      calc ((3 ^ k : ℕ) : ℝ) ^ 2 = ((9 ^ k : ℕ) : ℝ) := by
            push_cast; rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ < m := this
    exact_mod_cast (hreal.le.trans (Nat.le_ceil _))
  · have : m = 1 := by omega
    subst this
    simp only [Nat.clog_one_right, pow_zero]
    omega

/-- **`O(T·√m)`, with an explicit constant and no logarithm.** -/
theorem robustSearchBudget_le (m T : ℕ) :
    robustSearchBudget m T ≤ 10206 * T * ⌈Real.sqrt m⌉₊ := by
  by_cases h : 0 < m
  · rw [robustSearchBudget, if_pos h]
    have h1 := two_mul_trialsLen_le T (Nat.clog 9 m + 1)
    have h2 := three_pow_clog_le h
    have h3 : 3 ^ (Nat.clog 9 m + 1 + 1) = 9 * 3 ^ Nat.clog 9 m := by ring
    rw [h3] at h1
    have h4 : T * 3 ^ Nat.clog 9 m ≤ T * (3 * ⌈Real.sqrt m⌉₊) := Nat.mul_le_mul_left T h2
    nlinarith
  · rw [robustSearchBudget, if_neg h]
    exact Nat.zero_le _

variable {X : Type} [Fintype X]

/-- **The robust search theorem.** -/
theorem robustSearch_solves {A : ∀ i, QAlg ι σ Bool (W i)} {q : Fin m → ℕ} {T : ℕ}
    (hq : ∀ i, q i ≤ T) {read : X → ι → σ} {b : X → Fin m → Bool}
    (hA : ∀ x i, 2 / 3 ≤ (A i).prob (read x) (q i) (b x i)) :
    SolvesWithErrorOn (robustSearch A q T).alg (robustSearchBudget m T) read (SearchOK b)
      (1 / 3) := by
  intro x
  rw [← robustSearch_q A q T, successProbOn, goodProb_eq_sum_qProb, Fintype.sum_option]
  have hpr : ∀ o, qProb (robustSearch A q T).alg.readout
      ((robustSearch A q T).alg.state (read x) (robustSearch A q T).q) o
      = (robustSearch A q T).pr (read x) o := fun o => rfl
  simp only [hpr]
  have hnn : ∀ o, 0 ≤ (if SearchOK b x o then (robustSearch A q T).pr (read x) o else 0) :=
    fun o => by split_ifs <;> [exact OTrial.pr_nonneg _ _ _; exact le_rfl]
  by_cases hm : 0 < m
  · haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have hok := bankOK_rsBank hq (mk := b x) (hA x)
    by_cases hex : ∃ i, b x i = true
    · have hg := two_thirds_le_good (i₀ := ⟨0, hm⟩) hok hex
        ((Fintype.card_fin m).le.trans (Nat.le_pow_clog (by norm_num) m))
      rw [OTrial.good] at hg
      have hsum : (∑ i, if b x i = true then
          (rsAlg (rsBank A q T) ⟨0, hm⟩ (Nat.clog 9 m)).pr (read x) (some i) else 0)
          = ∑ i, if SearchOK b x (some i) then (robustSearch A q T).pr (read x) (some i)
            else 0 := by
        rw [robustSearch, dif_pos hm]
        rfl
      rw [hsum] at hg
      have := hnn none
      linarith
    · have hno : ∀ i, b x i = false := fun i => by
        by_contra hi
        exact hex ⟨i, by simpa using hi⟩
      have hn := two_thirds_le_none (i₀ := ⟨0, hm⟩) hok hno (Nat.clog 9 m)
      have hnone : (rsAlg (rsBank A q T) ⟨0, hm⟩ (Nat.clog 9 m)).pr (read x) none
          = (robustSearch A q T).pr (read x) none := by
        rw [robustSearch, dif_pos hm]
      rw [hnone] at hn
      rw [if_pos (show SearchOK b x none from hno)]
      have : 0 ≤ ∑ i, if SearchOK b x (some i) then (robustSearch A q T).pr (read x) (some i)
          else 0 := Finset.sum_nonneg fun i _ => hnn (some i)
      linarith
  · have h0 : m = 0 := by omega
    subst h0
    rw [if_pos (show SearchOK b x none from fun i => i.elim0)]
    have : (robustSearch A q T).pr (read x) none = 1 := by
      rw [robustSearch, dif_neg hm]
      exact OTrial.pr_never_none _
    rw [this]
    have : 0 ≤ ∑ i, if SearchOK b x (some i) then (robustSearch A q T).pr (read x) (some i)
        else 0 := Finset.sum_nonneg fun i _ => hnn (some i)
    linarith

/-- **The OR of bounded-error predicates**, at the same budget. -/
noncomputable def robustOr (A : ∀ i, QAlg ι σ Bool (W i)) (q : Fin m → ℕ) (T : ℕ) :
    QAlg ι σ Bool (robustSearch A q T).W :=
  QAlg.mapOut Option.isSome (robustSearch A q T).alg

theorem robustOr_computes {A : ∀ i, QAlg ι σ Bool (W i)} {q : Fin m → ℕ} {T : ℕ}
    (hq : ∀ i, q i ≤ T) {read : X → ι → σ} {b : X → Fin m → Bool}
    (hA : ∀ x i, 2 / 3 ≤ (A i).prob (read x) (q i) (b x i)) :
    ComputesWithErrorOn (robustOr A q T) (robustSearchBudget m T) read
      (fun x => decide (∃ i, b x i = true)) (1 / 3) := by
  intro x
  have hs := robustSearch_solves hq hA x
  rw [successProbOn, goodProb_eq_sum_qProb] at hs
  rw [robustOr, QAlg.mapOut_prob]
  refine le_trans hs (Finset.sum_le_sum fun o _ => ?_)
  have hp : 0 ≤ (robustSearch A q T).alg.prob (read x) (robustSearchBudget m T) o :=
    QAlg.prob_nonneg _ _ _ _
  by_cases hok : SearchOK b x o
  · rw [if_pos hok]
    cases o with
    | none =>
        have : ¬ ∃ i, b x i = true := fun ⟨i, hi⟩ => by simp [hok i] at hi
        rw [if_pos (by simp [this])]
        exact le_rfl
    | some i =>
        rw [if_pos (by simpa using ⟨i, hok⟩)]
        exact le_rfl
  · rw [if_neg hok]
    split_ifs <;> [exact hp; exact le_rfl]

end Public

end QuantumQueryComplexity
