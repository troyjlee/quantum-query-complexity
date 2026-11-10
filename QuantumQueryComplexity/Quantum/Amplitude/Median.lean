import QuantumQueryComplexity.Quantum.Plurality

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The median trick

An estimate that lands in an order-convex set `I` with probability at least `5/6` is boosted by
running it `2j + 1` times independently and returning the median (`median`): the median lies in
`I` as soon as more than half of the runs do (`median_mem`), so it misses `I` with probability at
most `(2/3)^j / 3` (`Realizes.median`). Moreover a run that returns some value surely makes the
median return it surely (`Realizes.median_pointMass`, of which `Realizes.median` is a corollary).
Plurality and majority (`Plurality.lean`, `Amplify.lean`)
need an exact target value; the median works for real-valued or rounded estimates, such as the
counts of `LabelSearch`.
-/

namespace QuantumQueryComplexity

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

/-- **The median** of `2j + 1` values: the entry at position `j` of their sorted list. -/
def median {O : Type} [LinearOrder O] {j : ℕ} (y : Fin (2 * j + 1) → O) : O :=
  ((List.ofFn y).insertionSort (· ≤ ·)).getD j (y 0)

/-- The number of indices whose value satisfies `p` is the count of `p` in the list of values. -/
private lemma med_card_filter_eq_countP {O : Type} (p : O → Prop) [DecidablePred p] :
    ∀ {n : ℕ} (y : Fin n → O),
      (Finset.univ.filter fun i => p (y i)).card = (List.ofFn y).countP (fun o => decide (p o))
  | 0, y => by simp
  | n + 1, y => by
    rw [Finset.card_filter, Fin.sum_univ_succ, ← Finset.card_filter, List.ofFn_succ,
      List.countP_cons, ← med_card_filter_eq_countP p (fun i => y i.succ), add_comm]
    simp only [decide_eq_true_eq]

/-- **The median lies in every order-convex set that contains more than half of the values.** -/
theorem median_mem {O : Type} [LinearOrder O] {j : ℕ} (I : O → Prop) [DecidablePred I]
    (hI : ∀ a b c, I a → I c → a ≤ b → b ≤ c → I b) (y : Fin (2 * j + 1) → O)
    (h : j + 1 ≤ (Finset.univ.filter fun i => I (y i)).card) : I (median y) := by
  set l := (List.ofFn y).insertionSort (· ≤ ·)
  have hperm : l.Perm (List.ofFn y) := List.perm_insertionSort _ _
  have hsort : l.Pairwise (· ≤ ·) := List.pairwise_insertionSort _ _
  have hlen : l.length = 2 * j + 1 := by rw [hperm.length_eq, List.length_ofFn]
  have hj : j < l.length := by omega
  have hmed : median y = l[j] := by
    change l.getD j (y 0) = l[j]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have hsplit : l = l.take j ++ l[j] :: l.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hcount : j + 1 ≤ l.countP (fun o => decide (I o)) := by
    rw [hperm.countP_eq, ← med_card_filter_eq_countP]
    exact h
  rw [hmed]
  by_contra hm
  have hA : (l.take j).length = j := by
    rw [List.length_take, hlen]
    omega
  have hB : (l.drop (j + 1)).length = j := by
    rw [List.length_drop, hlen]
    omega
  have hpw := hsort
  rw [hsplit, List.pairwise_append, List.pairwise_cons] at hpw
  rw [hsplit, List.countP_append, List.countP_cons_of_neg (by simpa using hm)] at hcount
  have hA' := List.countP_le_length (p := fun o => decide (I o)) (l := l.take j)
  have hB' := List.countP_le_length (p := fun o => decide (I o)) (l := l.drop (j + 1))
  obtain ⟨a, haA, haI⟩ := List.countP_pos_iff.mp
    (show 0 < (l.take j).countP (fun o => decide (I o)) by omega)
  obtain ⟨b, hbB, hbI⟩ := List.countP_pos_iff.mp
    (show 0 < (l.drop (j + 1)).countP (fun o => decide (I o)) by omega)
  exact hm (hI a l[j] b (of_decide_eq_true haI) (of_decide_eq_true hbI)
    (hpw.2.2 a haA l[j] List.mem_cons_self) (hpw.2.1.1 b hbB))

/-- The numeric endpoint of the median tail:
`(5/3)^(2j+1) / 5^(j+1) = (5/9)^j / 3 ≤ (2/3)^j / 3`. -/
private lemma med_pow_le (j : ℕ) : (5 / 3 : ℝ) ^ (2 * j + 1) / 5 ^ (j + 1) ≤ (2 / 3) ^ j / 3 := by
  have h1 : (5 / 3 : ℝ) ^ (2 * j + 1) = (25 / 9) ^ j * (5 / 3) := by
    rw [pow_succ, pow_mul]
    norm_num
  have hval : (5 / 3 : ℝ) ^ (2 * j + 1) / 5 ^ (j + 1) = (5 / 9) ^ j / 3 := by
    rw [h1, pow_succ, mul_div_mul_comm, ← div_pow]
    norm_num
    ring
  rw [hval]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by norm_num) j)
    (by norm_num)

/-- **The median tail**: if a draw from `p` falls outside `J` with probability at most `1/6`,
then `2j + 1` independent draws have at least `j + 1` values outside `J` with probability at most
`(2/3)^j / 3`.  Exponential moment with base `5`: the weight `5^{#outside}` has mean
`(1 + 4·Pr[outside])^{2j+1} ≤ (5/3)^{2j+1}`. -/
private lemma med_tail {O : Type} [Fintype O] (J : O → Prop) [DecidablePred J] (p : O → ℝ)
    (hp0 : ∀ o, 0 ≤ p o) (hp1 : ∑ o, p o = 1) (hpJ : 5 / 6 ≤ ∑ o, if J o then p o else 0)
    (j : ℕ) :
    ∑ y : Fin (2 * j + 1) → O,
      (if j + 1 ≤ (Finset.univ.filter fun i => ¬ J (y i)).card then ∏ i, p (y i) else 0)
      ≤ (2 / 3 : ℝ) ^ j / 3 := by
  set m : O → ℝ := fun o => if J o then 1 else 5 with hm
  have hm0 : ∀ o, 0 ≤ m o := fun o => by
    simp only [hm]
    split_ifs <;> norm_num
  have hfac : ∑ o, p o * m o ≤ 5 / 3 := by
    have hsplit : ∀ o, p o * m o = 5 * p o - 4 * (if J o then p o else 0) := fun o => by
      simp only [hm]
      split_ifs <;> ring
    simp only [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum, hp1]
    linarith
  have hstep : ∀ y : Fin (2 * j + 1) → O,
      (if j + 1 ≤ (Finset.univ.filter fun i => ¬ J (y i)).card then ∏ i, p (y i) else 0)
        * 5 ^ (j + 1) ≤ ∏ i, (p (y i) * m (y i)) := by
    intro y
    have hprod : ∏ i, m (y i) = 5 ^ (Finset.univ.filter fun i => ¬ J (y i)).card := by
      simp only [hm]
      rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    have hp : 0 ≤ ∏ i, p (y i) := Finset.prod_nonneg fun i _ => hp0 _
    rw [Finset.prod_mul_distrib, hprod]
    split_ifs with hy
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hy) hp
    · rw [zero_mul]
      positivity
  have h5 : (0 : ℝ) < 5 ^ (j + 1) := by positivity
  calc ∑ y : Fin (2 * j + 1) → O,
        (if j + 1 ≤ (Finset.univ.filter fun i => ¬ J (y i)).card then ∏ i, p (y i) else 0)
      = (∑ y : Fin (2 * j + 1) → O,
          (if j + 1 ≤ (Finset.univ.filter fun i => ¬ J (y i)).card then ∏ i, p (y i) else 0)
            * 5 ^ (j + 1)) / 5 ^ (j + 1) := by
        rw [← Finset.sum_mul, mul_div_cancel_right₀ _ h5.ne']
    _ ≤ (∑ y : Fin (2 * j + 1) → O, ∏ i, (p (y i) * m (y i))) / 5 ^ (j + 1) := by
        gcongr with y
        exact hstep y
    _ = (∏ _i : Fin (2 * j + 1), ∑ o, p o * m o) / 5 ^ (j + 1) := by
        rw [Fintype.prod_sum (fun (_ : Fin (2 * j + 1)) o => p o * m o)]
    _ ≤ (5 / 3) ^ (2 * j + 1) / 5 ^ (j + 1) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        gcongr
        exact Finset.sum_nonneg fun o _ => mul_nonneg (hp0 o) (hm0 o)
    _ ≤ (2 / 3) ^ j / 3 := med_pow_le j

/-- The median of a constant family is its value. -/
private lemma med_median_const {O : Type} [LinearOrder O] (j : ℕ) (o : O) :
    QuantumQueryComplexity.median (fun _ : Fin (2 * j + 1) => o) = o := by
  classical
  refine median_mem (fun b => b = o) (fun a b c ha hc hab hbc => ?_) _ ?_
  · subst ha hc
    exact le_antisymm hbc hab
  · rw [Finset.filter_true_of_mem fun _ _ => rfl, Finset.card_univ, Fintype.card_fin]
    omega

/-- **The median trick, keeping point masses**: if each run lands in the order-convex set `I x`
with probability at least `5/6`, the median of `2j + 1` independent runs misses it with
probability at most `(2/3)^j / 3`, with `2j + 1` times the budget; and a run that returns `o`
surely makes the median return `o` surely. -/
theorem Realizes.median_pointMass {X : Type} [Fintype X] {O : Type} [Fintype O] [LinearOrder O]
    {read : X → ι → σ} {q : ℕ} {P : X → O → ℝ} (h : Realizes read q P) (I : X → O → Prop)
    [∀ x, DecidablePred (I x)] (hI : ∀ x a b c, I x a → I x c → a ≤ b → b ≤ c → I x b)
    (hP : ∀ x, 5 / 6 ≤ ∑ o, if I x o then P x o else 0) (j : ℕ) :
    ∃ P' : X → O → ℝ, Realizes read ((2 * j + 1) * q) P' ∧
      (∀ x o, P x o = 1 → P' x o = 1) ∧
      ∀ x, 1 - (2 / 3 : ℝ) ^ j / 3 ≤ ∑ o, if I x o then P' x o else 0 := by
  have hfold := Realizes.foldRec (2 * j + 1) (fun _ => q) (fun _ => P) (fun _ => h)
  have hcost : (∑ _i : Fin (2 * j + 1), q) = (2 * j + 1) * q := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hcost] at hfold
  have hsum : ∀ x, ∑ o, P x o = 1 := fun x => by
    obtain ⟨W, _, _, A, hA⟩ := h
    simp only [← hA x]
    exact A.sum_prob _ _
  refine ⟨_, hfold.map (QuantumQueryComplexity.median (j := j)), fun x o hxo => ?_, fun x => ?_⟩
  · -- a point mass stays a point mass
    classical
    have hzero : ∀ o' ≠ o, P x o' = 0 := by
      have hrest := Finset.add_sum_erase Finset.univ (P x) (Finset.mem_univ o)
      rw [hsum x, hxo] at hrest
      have hrest0 : ∑ o' ∈ Finset.univ.erase o, P x o' = 0 := by linarith
      intro o' ho'
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun o'' _ => h.nonneg x o'')).mp hrest0 o'
        (Finset.mem_erase.mpr ⟨ho', Finset.mem_univ _⟩)
    rw [Finset.sum_eq_single (fun _ => o)]
    · simp [hxo]
    · intro y _ hy
      obtain ⟨i, hi⟩ : ∃ i, y i ≠ o := Function.ne_iff.mp hy
      exact Finset.prod_eq_zero (Finset.mem_univ i) (hzero _ hi)
    · intro hnot
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ (fun _ => o), med_median_const j o⟩)
        hnot
  have hP0 : ∀ o, 0 ≤ P x o := h.nonneg x
  have hP1 : ∑ o, P x o = 1 := hsum x
  set w : (Fin (2 * j + 1) → O) → ℝ := fun y => ∏ i, P x (y i) with hw
  have hw0 : ∀ y, 0 ≤ w y := fun y => Finset.prod_nonneg fun i _ => hP0 _
  have hw1 : ∑ y, w y = 1 := by
    rw [hw, ← Fintype.prod_sum (fun (_ : Fin (2 * j + 1)) o => P x o), hP1,
      Finset.prod_const_one]
  -- regroup the median distribution by records
  have hregroup : (∑ o, if I x o then
        ∑ y ∈ Finset.univ.filter (fun y => QuantumQueryComplexity.median y = o), w y else 0)
      = ∑ y, if I x (QuantumQueryComplexity.median y) then w y else 0 := by
    rw [← Finset.sum_fiberwise Finset.univ (QuantumQueryComplexity.median (j := j))
      (fun y => if I x (QuantumQueryComplexity.median y) then w y else 0)]
    refine Finset.sum_congr rfl fun o _ => ?_
    split_ifs with ho
    · refine Finset.sum_congr rfl fun y hy => ?_
      rw [(Finset.mem_filter.mp hy).2]
      simp only [ho, ite_true]
    · refine (Finset.sum_eq_zero fun y hy => ?_).symm
      rw [(Finset.mem_filter.mp hy).2]
      simp only [ho, ite_false]
  -- pointwise: the median is good unless at least `j + 1` runs are bad
  have hpoint : ∀ y, w y - (if j + 1 ≤ (Finset.univ.filter fun i => ¬ I x (y i)).card
      then w y else 0) ≤ if I x (QuantumQueryComplexity.median y) then w y else 0 := by
    intro y
    have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin (2 * j + 1) => I x (y i))
    rw [Finset.card_univ, Fintype.card_fin] at hsplit
    have hgood : ¬ j + 1 ≤ (Finset.univ.filter fun i => ¬ I x (y i)).card →
        I x (QuantumQueryComplexity.median y) := fun hb =>
      median_mem (I x) (hI x) y (by omega)
    have := hw0 y
    split_ifs with h1 h2 h2
    · linarith
    · linarith
    · linarith
    · exact absurd (hgood h1) h2
  have htail := med_tail (I x) (P x) hP0 hP1 (hP x) j
  calc 1 - (2 / 3 : ℝ) ^ j / 3
      ≤ ∑ y, w y - ∑ y, (if j + 1 ≤ (Finset.univ.filter fun i => ¬ I x (y i)).card
          then w y else 0) := by
        rw [hw1]
        linarith
    _ = ∑ y, (w y - (if j + 1 ≤ (Finset.univ.filter fun i => ¬ I x (y i)).card
          then w y else 0)) := (Finset.sum_sub_distrib _ _).symm
    _ ≤ ∑ y, if I x (QuantumQueryComplexity.median y) then w y else 0 :=
        Finset.sum_le_sum fun y _ => hpoint y
    _ = _ := hregroup.symm

/-- **The median trick**: if each run lands in the order-convex set `I x` with probability at
least `5/6`, the median of `2j + 1` independent runs misses it with probability at most
`(2/3)^j / 3`, with `2j + 1` times the budget. -/
theorem Realizes.median {X : Type} [Fintype X] {O : Type} [Fintype O] [LinearOrder O]
    {read : X → ι → σ} {q : ℕ} {P : X → O → ℝ} (h : Realizes read q P) (I : X → O → Prop)
    [∀ x, DecidablePred (I x)] (hI : ∀ x a b c, I x a → I x c → a ≤ b → b ≤ c → I x b)
    (hP : ∀ x, 5 / 6 ≤ ∑ o, if I x o then P x o else 0) (j : ℕ) :
    ∃ P' : X → O → ℝ, Realizes read ((2 * j + 1) * q) P' ∧
      ∀ x, 1 - (2 / 3 : ℝ) ^ j / 3 ≤ ∑ o, if I x o then P' x o else 0 := by
  obtain ⟨P', hP', -, hgood⟩ := h.median_pointMass I hI hP j
  exact ⟨P', hP', hgood⟩

end QuantumQueryComplexity
