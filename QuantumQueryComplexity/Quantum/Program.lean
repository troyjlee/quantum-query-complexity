import QuantumQueryComplexity.Quantum.AdaptiveRun
import QuantumQueryComplexity.Quantum.Padding

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Adaptive programs with fixed query budgets

Quantum algorithms built from subroutines often choose the next subroutine from the classical
outcomes of the earlier ones: an estimate fixes a sample size, a sample fixes a search, and a
global budget cuts the run short. A **program** `Prog ι σ O` is a finite tree of such calls on
one input `a : ι → σ`:

* `ret o` returns the value `o` (a leaf, possibly early);
* `call O' q P hP k` runs a subroutine with the fixed integer budget `q` and outcome law `P a`,
  realized by some algorithm (`hP : Realizes id q P`), and continues with the program `k o'`
  chosen by its outcome `o'`.

**Semantics.**
* `law p a` is the outcome law on input `a`. At a call, `law_call`:
  `(call O' q P hP k).law a o = ∑_{o'} P a o' · (k o').law a o`. Each call is run with fresh
  randomness, so **the law of the continuation given the transcript `o'` is `(k o').law a`**;
  every guarantee of a later call holds conditionally on the earlier outcomes.
* `budget p` is the largest total budget along a root-to-leaf path:
  `budget (call O' q P hP k) = q + max_{o'} budget (k o')` (`budget_call`). Branches may have
  different costs; nothing is padded to a per-call maximum.
* `realizes`: **one algorithm, chosen before the input, realizes `law p` with exactly
  `budget p` queries.**

**Timeouts.** `cutoff τ p B` follows `p` but returns the timeout value `τ` instead of making a
call whose budget exceeds what remains of the global budget `B`. Its budget is at most `B`
(`budget_cutoff_le`), it is `p` itself when `budget p ≤ B` (`cutoff_eq_self`), and for every
event its probability is at least that under `p` minus `overProb p a B`, the probability that the
path of `p` would cost more than `B` (`law_cutoff_ge`).

**Error composition.** If a call's outcome is good except with probability `ε`, and after every
good outcome the continuation's final output is correct except with probability `ε'`, the final
output is correct except with probability `ε + ε'` (`bad_call_le`).
-/

namespace QuantumQueryComplexity

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

/-- **An adaptive program** with output type `O`: a finite tree of subroutine calls with fixed
budgets, each realized by some algorithm on the full input. -/
inductive Prog (ι σ O : Type) [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] : Type 1
  /-- Return a value. -/
  | ret (o : O) : Prog ι σ O
  /-- Run a subroutine with budget `q` and outcome law `P`, then continue with `k` of its
  outcome. -/
  | call (O' : Type) [Fintype O'] [DecidableEq O'] (q : ℕ) (P : (ι → σ) → O' → ℝ)
      (hP : Realizes (id : (ι → σ) → ι → σ) q P) (k : O' → Prog ι σ O) : Prog ι σ O

namespace Prog

variable {O : Type}

/-- A realized law has total mass one. -/
private lemma prg_sum_eq_one {O' : Type} [Fintype O'] [DecidableEq O'] {q : ℕ}
    {P : (ι → σ) → O' → ℝ} (h : Realizes (id : (ι → σ) → ι → σ) q P) (a : ι → σ) :
    ∑ o, P a o = 1 := by
  obtain ⟨W, _, _, A, hA⟩ := h
  simp only [← hA a, QAlg.prob]
  exact sum_qProb_eq_one (A.state_isQState _ _) _

/-- A realized law is also realized with any larger budget (pad with idle queries). -/
private lemma prg_realizes_mono {O' : Type} [DecidableEq O'] {q q' : ℕ}
    {P : (ι → σ) → O' → ℝ} (h : Realizes (id : (ι → σ) → ι → σ) q P) (hq : q ≤ q') :
    Realizes (id : (ι → σ) → ι → σ) q' P := by
  obtain ⟨W, _, _, A, hA⟩ := h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hq
  exact ⟨CtrlWork ι W, inferInstance, inferInstance, padAlg A q n, fun a o => by
    rw [padAlg_prob]; exact hA a o⟩

/-- The point mass at `o` is realized with no queries. -/
private lemma prg_realizes_ret [DecidableEq O] (o : O) :
    Realizes (id : (ι → σ) → ι → σ) 0 fun _ o' => if o' = o then (1 : ℝ) else 0 := by
  refine ⟨Unit, inferInstance, inferInstance, constAlg ι σ o, fun a o' => ?_⟩
  simp only [QAlg.prob, constAlg]
  simp [eq_comm]

/-- **The budget**: the largest total budget along a root-to-leaf path. -/
noncomputable def budget : Prog ι σ O → ℕ
  | ret _ => 0
  | call _ q _ _ k => q + Finset.univ.sup fun o' => budget (k o')

/-- **The outcome law** on the input `a`. -/
noncomputable def law [DecidableEq O] (a : ι → σ) : Prog ι σ O → O → ℝ
  | ret o => fun o' => if o' = o then 1 else 0
  | call _ _ P _ k => fun o => ∑ o', P a o' * law a (k o') o

/-- The budget of a call: its own budget plus the largest budget of a continuation. -/
theorem budget_call (O' : Type) [Fintype O'] [DecidableEq O'] (q : ℕ) (P : (ι → σ) → O' → ℝ)
    (hP : Realizes (id : (ι → σ) → ι → σ) q P) (k : O' → Prog ι σ O) :
    (call O' q P hP k).budget = q + Finset.univ.sup fun o' => (k o').budget := by
  rfl

/-- **The law of a call**: the continuation after the outcome `o'` has law `(k o').law a`. -/
theorem law_call [DecidableEq O] (a : ι → σ) (O' : Type) [Fintype O'] [DecidableEq O'] (q : ℕ)
    (P : (ι → σ) → O' → ℝ) (hP : Realizes (id : (ι → σ) → ι → σ) q P) (k : O' → Prog ι σ O)
    (o : O) : (call O' q P hP k).law a o = ∑ o', P a o' * (k o').law a o := by
  rfl

/-- The law is nonnegative. -/
theorem law_nonneg [DecidableEq O] (a : ι → σ) (p : Prog ι σ O) (o : O) : 0 ≤ p.law a o := by
  induction p generalizing o with
  | ret o' =>
    simp only [law]
    split_ifs <;> norm_num
  | call O' q P hP k ih =>
    rw [law_call]
    exact Finset.sum_nonneg fun o' _ => mul_nonneg (hP.nonneg a o') (ih o' o)

/-- The law has total mass one. -/
theorem sum_law [Fintype O] [DecidableEq O] (a : ι → σ) (p : Prog ι σ O) :
    ∑ o, p.law a o = 1 := by
  induction p with
  | ret o => simp [law]
  | call O' q P hP k ih =>
    simp_rw [law_call]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ih, mul_one]
    exact prg_sum_eq_one hP a

/-- **Compilation**: one algorithm, independent of the input, realizes the program's law with
exactly `budget` queries. -/
theorem realizes [Fintype O] [DecidableEq O] (p : Prog ι σ O) :
    Realizes (id : (ι → σ) → ι → σ) p.budget fun a o => p.law a o := by
  induction p with
  | ret o => exact prg_realizes_ret o
  | call O' q P hP k ih =>
    have hk : ∀ o', Realizes (id : (ι → σ) → ι → σ) (Finset.univ.sup fun o' => (k o').budget)
        (fun a o => (k o').law a o) := fun o' =>
      prg_realizes_mono (ih o') (Finset.le_sup (f := fun o' => (k o').budget) (Finset.mem_univ o'))
    have hb := (Realizes.bind (P₂ := fun o' a o => (k o').law a o) hP hk).map Prod.snd
    rw [budget_call]
    refine hb.congr fun a o => ?_
    rw [law_call]
    simp [Finset.sum_filter, Fintype.sum_prod_type]

/-! ## Global budgets and timeouts -/

/-- **A global cutoff**: follow the program, but return `τ` instead of making a call whose
budget exceeds what remains of `B`. -/
noncomputable def cutoff (τ : O) : Prog ι σ O → ℕ → Prog ι σ O
  | ret o => fun _ => ret o
  | call O' q P hP k => fun B =>
      if q ≤ B then call O' q P hP fun o' => cutoff τ (k o') (B - q) else ret τ

/-- The probability that the path of the program costs more than `B`. -/
noncomputable def overProb (a : ι → σ) : Prog ι σ O → ℕ → ℝ
  | ret _ => fun _ => 0
  | call _ q P _ k => fun B =>
      if q ≤ B then ∑ o', P a o' * overProb a (k o') (B - q) else 1

/-- **A cutoff program respects its global budget.** -/
theorem budget_cutoff_le (τ : O) (p : Prog ι σ O) (B : ℕ) : (p.cutoff τ B).budget ≤ B := by
  induction p generalizing B with
  | ret o => simp [cutoff, budget]
  | call O' q P hP k ih =>
    simp only [cutoff]
    split_ifs with hq
    · rw [budget_call]
      have : (Finset.univ.sup fun o' => ((k o').cutoff τ (B - q)).budget) ≤ B - q :=
        Finset.sup_le fun o' _ => ih o' (B - q)
      omega
    · simp [budget]

/-- A cutoff that is never reached changes nothing. -/
theorem cutoff_eq_self (τ : O) (p : Prog ι σ O) {B : ℕ} (h : p.budget ≤ B) :
    p.cutoff τ B = p := by
  induction p generalizing B with
  | ret o => rfl
  | call O' q P hP k ih =>
    rw [budget_call] at h
    have hq : q ≤ B := by omega
    simp only [cutoff, hq, ↓reduceIte]
    congr 1
    funext o'
    exact ih o' (le_trans (Finset.le_sup (f := fun o' => (k o').budget) (Finset.mem_univ o'))
      (by omega))

/-- No path costs more than `B` when the budget is at most `B`. -/
theorem overProb_eq_zero (a : ι → σ) (p : Prog ι σ O) {B : ℕ} (h : p.budget ≤ B) :
    p.overProb a B = 0 := by
  induction p generalizing B with
  | ret o => rfl
  | call O' q P hP k ih =>
    rw [budget_call] at h
    have hq : q ≤ B := by omega
    simp only [overProb, hq, ↓reduceIte]
    refine Finset.sum_eq_zero fun o' _ => ?_
    rw [ih o' (le_trans (Finset.le_sup (f := fun o' => (k o').budget) (Finset.mem_univ o'))
      (by omega)), mul_zero]

/-- **The timeout changes each event's probability by at most the overrun probability.** -/
theorem law_cutoff_ge [Fintype O] [DecidableEq O] (a : ι → σ) (τ : O) (p : Prog ι σ O) (B : ℕ)
    (E : O → Prop) [DecidablePred E] :
    ∑ o, (if E o then p.law a o else 0) ≤
      ∑ o, (if E o then (p.cutoff τ B).law a o else 0) + p.overProb a B := by
  induction p generalizing B with
  | ret o => simp [cutoff, overProb]
  | call O' q P hP k ih =>
    by_cases hq : q ≤ B
    · have hc : (call O' q P hP k).cutoff τ B
          = call O' q P hP fun o' => (k o').cutoff τ (B - q) := by
        simp only [cutoff, hq, ↓reduceIte]
      have ho : (call O' q P hP k).overProb a B
          = ∑ o', P a o' * (k o').overProb a (B - q) := by
        simp only [overProb, hq, ↓reduceIte]
      have key : ∀ L : O' → O → ℝ, ∑ o, (if E o then ∑ o', P a o' * L o' o else 0)
          = ∑ o', P a o' * ∑ o, (if E o then L o' o else 0) := by
        intro L
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun o _ => ?_
        split_ifs <;> simp
      rw [hc, ho]
      simp_rw [law_call]
      rw [key, key, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun o' _ => ?_
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (ih o' (B - q)) (hP.nonneg a o')
    · have hc : (call O' q P hP k).cutoff τ B = ret τ := by
        simp only [cutoff, hq, ↓reduceIte]
      have ho : (call O' q P hP k).overProb a B = 1 := by
        simp only [overProb, hq, ↓reduceIte]
      rw [hc, ho]
      have h1 : ∑ o, (if E o then (call O' q P hP k).law a o else 0) ≤ 1 := by
        rw [← sum_law a (call O' q P hP k)]
        refine Finset.sum_le_sum fun o _ => ?_
        split_ifs
        · exact le_rfl
        · exact law_nonneg a _ o
      have h2 : 0 ≤ ∑ o, (if E o then (ret τ : Prog ι σ O).law a o else 0) := by
        refine Finset.sum_nonneg fun o _ => ?_
        split_ifs
        · exact law_nonneg a _ o
        · exact le_rfl
      linarith

/-! ## Error composition -/

/-- **Error composition along a call**: if the call's outcome is good except with probability
`ε`, and after each good outcome the continuation's output is correct except with probability
`ε'`, the output is correct except with probability `ε + ε'`. -/
theorem bad_call_le [Fintype O] [DecidableEq O] (a : ι → σ) {O' : Type} [Fintype O']
    [DecidableEq O'] {q : ℕ} {P : (ι → σ) → O' → ℝ} {hP : Realizes (id : (ι → σ) → ι → σ) q P}
    {k : O' → Prog ι σ O} (G : O' → Prop) [DecidablePred G] (Corr : O → Prop)
    [DecidablePred Corr] {ε ε' : ℝ} (hε' : 0 ≤ ε')
    (hG : ∑ o', (if G o' then 0 else P a o') ≤ ε)
    (hk : ∀ o', G o' → ∑ o, (if Corr o then 0 else (k o').law a o) ≤ ε') :
    ∑ o, (if Corr o then 0 else (call O' q P hP k).law a o) ≤ ε + ε' := by
  have hb : ∀ o', ∑ o, (if Corr o then 0 else (k o').law a o) ≤ 1 := fun o' => by
    rw [← sum_law a (k o')]
    refine Finset.sum_le_sum fun o _ => ?_
    split_ifs
    · exact law_nonneg a _ o
    · exact le_rfl
  calc ∑ o, (if Corr o then 0 else (call O' q P hP k).law a o)
      = ∑ o', P a o' * ∑ o, (if Corr o then 0 else (k o').law a o) := by
        simp_rw [law_call, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun o _ => ?_
        split_ifs <;> simp
    _ ≤ ∑ o', (ε' * P a o' + if G o' then 0 else P a o') := by
        refine Finset.sum_le_sum fun o' _ => ?_
        have hP0 := hP.nonneg a o'
        split_ifs with hg
        · nlinarith [mul_le_mul_of_nonneg_left (hk o' hg) hP0]
        · nlinarith [mul_le_mul_of_nonneg_left (hb o') hP0]
    _ = ε' * ∑ o', P a o' + ∑ o', (if G o' then 0 else P a o') := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ε + ε' := by
        rw [prg_sum_eq_one hP a]
        linarith

end Prog

end QuantumQueryComplexity
