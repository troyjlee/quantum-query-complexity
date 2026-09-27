import QuantumQueryComplexity.Quantum.Amplitude.FirstSuccess
set_option synthInstance.maxSize 3200
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The first success of a finite list of trials

`OTrial ι σ O` bundles an algorithm with optional output, its workspace and its query
budget.  `firstOf l` runs the trials of the list `l` independently (fresh workspaces, exact
product statistics from the bank-swap compiler) and returns the first `some`; it is one
compiled `QAlg` with the fixed budget `∑ q`.  For any validity predicate `G` on outputs:

* `pr_firstOf_none` — `Pr[none] = ∏ Pr_T[none]`;
* `bad_firstOf_le`  — `Pr[some invalid] ≤ ∑ Pr_T[some invalid]` (union bound);
* `good_eq`         — `Pr[some valid] = 1 − Pr[none] − Pr[some invalid]`.
-/

namespace QuantumQueryComplexity

variable {ι σ O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype O] [DecidableEq O]

/-- A bundled trial with optional output. -/
structure OTrial (ι σ O : Type) [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    [DecidableEq O] where
  /-- The workspace. -/
  W : Type
  [fW : Fintype W]
  [dW : DecidableEq W]
  /-- The algorithm. -/
  alg : QAlg ι σ (Option O) W
  /-- Its query budget. -/
  q : ℕ

attribute [instance] OTrial.fW OTrial.dW

namespace OTrial

/-- The outcome law of a trial at its budget. -/
noncomputable def pr (T : OTrial ι σ O) (a : ι → σ) (o : Option O) : ℝ := T.alg.prob a T.q o

lemma pr_nonneg (T : OTrial ι σ O) (a : ι → σ) (o : Option O) : 0 ≤ T.pr a o :=
  QAlg.prob_nonneg _ _ _ _

lemma sum_pr (T : OTrial ι σ O) (a : ι → σ) : ∑ o, T.pr a o = 1 := T.alg.sum_prob a T.q

lemma pr_le_one (T : OTrial ι σ O) (a : ι → σ) (o : Option O) : T.pr a o ≤ 1 := by
  rw [← T.sum_pr a]
  exact Finset.single_le_sum (fun o _ => T.pr_nonneg a o) (Finset.mem_univ o)

/-- The zero-query trial that never succeeds. -/
noncomputable def never : OTrial ι σ O where
  W := Unit
  alg := (QRoutine.identity (ι := ι) (σ := σ) (W := Unit)).toAlg
    (qBasis ((none, none, ()) : QBasis ι σ Unit)) (isQState_qBasis _) (fun _ => none)
  q := 0

lemma pr_never_none (a : ι → σ) : (never : OTrial ι σ O).pr a none = 1 := by
  have h := (never : OTrial ι σ O).sum_pr a
  rw [Fintype.sum_option] at h
  have h0 : ∀ y : O, (never : OTrial ι σ O).pr a (some y) = 0 := fun y => by
    change qProb (fun _ => (none : Option O)) _ (some y) = 0
    rw [qProb]
    simp
  rw [Finset.sum_eq_zero fun y _ => h0 y, add_zero] at h
  exact h

lemma pr_never_some (a : ι → σ) (y : O) : (never : OTrial ι σ O).pr a (some y) = 0 := by
  change qProb (fun _ => (none : Option O)) _ (some y) = 0
  rw [qProb]
  simp

/-- First success of two trials. -/
noncomputable def orElse (T₁ T₂ : OTrial ι σ O) : OTrial ι σ O where
  W := QBasis ι σ T₁.W × QBasis ι σ T₂.W
  alg := QAlg.orElse T₁.alg T₁.q T₂.alg T₂.q
  q := T₁.q + T₂.q

lemma pr_orElse_some (T₁ T₂ : OTrial ι σ O) (a : ι → σ) (y : O) :
    (T₁.orElse T₂).pr a (some y) = T₁.pr a (some y) + T₁.pr a none * T₂.pr a (some y) :=
  QAlg.orElse_prob_some T₁.alg T₁.q T₂.alg T₂.q a y

lemma pr_orElse_none (T₁ T₂ : OTrial ι σ O) (a : ι → σ) :
    (T₁.orElse T₂).pr a none = T₁.pr a none * T₂.pr a none :=
  QAlg.orElse_prob_none T₁.alg T₁.q T₂.alg T₂.q a

/-- **The first success of a list of trials.** -/
noncomputable def firstOf : List (OTrial ι σ O) → OTrial ι σ O
  | [] => never
  | T :: l => T.orElse (firstOf l)

theorem firstOf_q (l : List (OTrial ι σ O)) : (firstOf l).q = (l.map (·.q)).sum := by
  induction l with
  | nil => rfl
  | cons T l ih => rw [firstOf, List.map_cons, List.sum_cons, ← ih]; rfl

theorem pr_firstOf_none (l : List (OTrial ι σ O)) (a : ι → σ) :
    (firstOf l).pr a none = (l.map fun T => T.pr a none).prod := by
  induction l with
  | nil => exact pr_never_none a
  | cons T l ih => rw [firstOf, pr_orElse_none, ih, List.map_cons, List.prod_cons]

variable (G : O → Prop) [DecidablePred G]

/-- `Pr[some valid]`. -/
noncomputable def good (T : OTrial ι σ O) (a : ι → σ) : ℝ :=
  ∑ y, if G y then T.pr a (some y) else 0

/-- `Pr[some invalid]`. -/
noncomputable def bad (T : OTrial ι σ O) (a : ι → σ) : ℝ :=
  ∑ y, if G y then 0 else T.pr a (some y)

lemma bad_nonneg (T : OTrial ι σ O) (a : ι → σ) : 0 ≤ T.bad G a :=
  Finset.sum_nonneg fun y _ => by split_ifs <;> [exact le_rfl; exact T.pr_nonneg a _]

theorem good_eq (T : OTrial ι σ O) (a : ι → σ) :
    T.good G a = 1 - T.pr a none - T.bad G a := by
  have h := T.sum_pr a
  rw [Fintype.sum_option] at h
  have hsplit : ∑ y, T.pr a (some y) = T.good G a + T.bad G a := by
    rw [good, bad, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by split_ifs <;> simp
  linarith

theorem bad_firstOf_le (l : List (OTrial ι σ O)) (a : ι → σ) :
    (firstOf l).bad G a ≤ (l.map fun T => T.bad G a).sum := by
  induction l with
  | nil =>
      rw [firstOf, bad, List.map_nil, List.sum_nil]
      exact le_of_eq (Finset.sum_eq_zero fun y _ => by rw [pr_never_some, ite_self])
  | cons T l ih =>
      rw [firstOf, List.map_cons, List.sum_cons]
      refine le_trans ?_ (add_le_add_right ih _)
      have : (T.orElse (firstOf l)).bad G a
          = T.bad G a + T.pr a none * (firstOf l).bad G a := by
        rw [bad, bad, bad, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [pr_orElse_some]
        split_ifs <;> simp
      rw [this]
      have := mul_le_mul_of_nonneg_right (T.pr_le_one a none) ((firstOf l).bad_nonneg G a)
      linarith

end OTrial

end QuantumQueryComplexity
