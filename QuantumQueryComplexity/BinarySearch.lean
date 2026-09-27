import QuantumQueryComplexity.Adaptive
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Binary search in dual land

A quantum algorithm that locates the threshold of a monotone predicate does
`⌈log₂ s⌉` adaptive tests and pays for one test per level.  On the dual side
that is exactly a descriptor chain (`QuantumQueryComplexity/Adaptive.lean`): the level-`ℓ`
descriptor is the `ℓ`-th prefix of the answer, and *conditioned on the
previous levels* it is a single threshold test, because the earlier outcomes
pin the answer to a known dyadic block whose midpoint is then a constant.

  **`hasDualOn_thresholdSearch`** — if `ans x < 2 ^ L` and every threshold
  test `test q x = [ans x ≤ q]` has a dual solution of cost `g` on the
  promise, then `ans` itself has one of cost `L · g`.

Nothing here is specific to any problem: the caller supplies the family of
threshold tests and their cost.  For the longest-distinct-substring anchors
 the tests are windowed element-distinctness duals, giving
`g = 8 s^{2/3}` and a total of `8 s^{2/3} ⌈log₂ s⌉` — the dual-side
counterpart of the paper's Fact 36, without its noisy-search error
bookkeeping.

The one arithmetic fact behind the recursion is `div_two_pow_step`: knowing
`a / 2^{k+1}` leaves exactly two possibilities for `a / 2^k`, and a single
comparison of `a` against a constant decides between them.
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} [DecidableEq σ]
variable {X : Type} [Fintype X] [DecidableEq X]

/-- **One binary-search step.**  If the `(k+1)`-prefix of `a` is `P`, then its
`k`-prefix is `2P` or `2P + 1` according to a single comparison of `a` with
the block midpoint `(2P+1)·2^k`. -/
private lemma div_two_pow_step {a P k : ℕ} (h : a / 2 ^ (k + 1) = P) :
    a / 2 ^ k = if a ≤ (2 * P + 1) * 2 ^ k - 1 then 2 * P else 2 * P + 1 := by
  have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hmul : 0 < (2 * P + 1) * 2 ^ k := Nat.mul_pos (by omega) hpos
  have hdd : a / 2 ^ k / 2 = P := by
    rw [Nat.div_div_eq_div_mul, ← pow_succ]
    exact h
  have hle : 2 * P + 1 ≤ a / 2 ^ k ↔ (2 * P + 1) * 2 ^ k ≤ a :=
    Nat.le_div_iff_mul_le hpos
  by_cases hcmp : a ≤ (2 * P + 1) * 2 ^ k - 1
  · rw [if_pos hcmp]
    have h2 : ¬ (2 * P + 1 ≤ a / 2 ^ k) := fun hc => by
      have := hle.mp hc
      omega
    omega
  · rw [if_neg hcmp]
    have h2 : 2 * P + 1 ≤ a / 2 ^ k := hle.mpr (by omega)
    omega

/-- The `ℓ`-th prefix of the answer: the descriptor of binary-search level
`ℓ`, with the most significant bit at level `0`. -/
private def ansPre (L : ℕ) (ans : X → ℕ) (hans : ∀ x, ans x < 2 ^ L)
    (ℓ : Fin L) (x : X) : Fin (2 ^ L) :=
  ⟨ans x / 2 ^ (L - 1 - (ℓ : ℕ)), lt_of_le_of_lt (Nat.div_le_self _ _) (hans x)⟩

private lemma ansPre_val {L : ℕ} {ans : X → ℕ} (hans : ∀ x, ans x < 2 ^ L)
    (ℓ : Fin L) (x : X) :
    (ansPre L ans hans ℓ x : ℕ) = ans x / 2 ^ (L - 1 - (ℓ : ℕ)) := rfl

/-- **Binary search costs `L` tests.**  A quantity bounded by `2 ^ L` whose
threshold tests each have a dual solution of cost `g` has one of cost
`L · g`. -/
theorem hasDualOn_thresholdSearch {read : X → ι → σ} {L : ℕ} {ans : X → ℕ}
    {test : ℕ → X → Bool} {g : ℝ} (hans : ∀ x, ans x < 2 ^ L)
    (htest : ∀ q x, test q x = decide (ans x ≤ q))
    (hcost : ∀ q, HasDualOn read (test q) g) :
    HasDualOn read ans ((L : ℝ) * g) := by
  classical
  have hLpos : 0 < 2 ^ L := pow_pos (by norm_num) L
  -- each level is a single threshold test, at a position the fiber fixes
  have hlevels : ∀ (ℓ : Fin L) (t : Fin L → Fin (2 ^ L)),
      HasDualOn
        (fiberRead read (preTrans (ansPre L ans hans) ⟨0, hLpos⟩ (ℓ : ℕ)) t)
        (fun z => ansPre L ans hans ℓ z.val) g := by
    intro ℓ t
    have hℓ : (ℓ : ℕ) < L := ℓ.isLt
    -- the fiber pins the previous prefix
    obtain ⟨P, hfib⟩ : ∃ P : ℕ,
        ∀ z : Fiber (preTrans (ansPre L ans hans) ⟨0, hLpos⟩ (ℓ : ℕ)) t,
          ans z.val / 2 ^ (L - 1 - (ℓ : ℕ) + 1) = P := by
      rcases Nat.eq_zero_or_pos (ℓ : ℕ) with h0 | h0
      · refine ⟨0, fun z => ?_⟩
        rw [show L - 1 - (ℓ : ℕ) + 1 = L by omega]
        exact Nat.div_eq_of_lt (hans z.val)
      · refine ⟨(t ⟨(ℓ : ℕ) - 1, by omega⟩ : ℕ), fun z => ?_⟩
        have hc := congrFun z.2 ⟨(ℓ : ℕ) - 1, by omega⟩
        simp only [preTrans] at hc
        rw [if_pos (show (ℓ : ℕ) - 1 < (ℓ : ℕ) by omega)] at hc
        have hval := congrArg Fin.val hc
        rw [ansPre_val] at hval
        rw [show L - 1 - (ℓ : ℕ) + 1 = L - 1 - ((ℓ : ℕ) - 1) by omega]
        exact hval
    -- that test, restricted to the fiber
    have hcomap := (hcost ((2 * P + 1) * 2 ^ (L - 1 - (ℓ : ℕ)) - 1)).comap
      (fun z : Fiber (preTrans (ansPre L ans hans) ⟨0, hLpos⟩ (ℓ : ℕ)) t => z.val)
    refine hcomap.ofKer fun z w => ?_
    have hz := div_two_pow_step (hfib z)
    have hw := div_two_pow_step (hfib w)
    set q : ℕ := (2 * P + 1) * 2 ^ (L - 1 - (ℓ : ℕ)) - 1 with hqdef
    rw [htest, htest]
    constructor
    · intro h
      have hdec : (ans z.val ≤ q) ↔ (ans w.val ≤ q) := decide_eq_decide.mp h
      refine Fin.ext ?_
      rw [ansPre_val, ansPre_val, hz, hw]
      by_cases hzq : ans z.val ≤ q
      · rw [if_pos hzq, if_pos (hdec.mp hzq)]
      · rw [if_neg hzq, if_neg fun hc => hzq (hdec.mpr hc)]
    · intro h
      have hval : (ansPre L ans hans ℓ z.val : ℕ)
          = (ansPre L ans hans ℓ w.val : ℕ) := congrArg Fin.val h
      rw [ansPre_val, ansPre_val, hz, hw] at hval
      refine decide_eq_decide.mpr ⟨fun hc => ?_, fun hc => ?_⟩
      · by_contra hcw
        rw [if_pos hc, if_neg hcw] at hval
        omega
      · by_contra hcz
        rw [if_neg hcz, if_pos hc] at hval
        omega
  -- the transcript is the answer
  refine (hasDualOn_transcript (ansPre L ans hans) ⟨0, hLpos⟩ hlevels).ofKer
    (f' := ans) fun x y => ?_
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos L with hL | hL
    · have hx := hans x
      have hy := hans y
      rw [hL] at hx hy
      omega
    · have hc := congrFun h ⟨L - 1, by omega⟩
      have hval := congrArg Fin.val hc
      rw [ansPre_val, ansPre_val] at hval
      simpa using hval
  · intro h
    funext i
    refine Fin.ext ?_
    rw [ansPre_val, ansPre_val, h]

end QuantumQueryComplexity
