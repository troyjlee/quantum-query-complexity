import QuantumQueryComplexity.Max.Staircase
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.Sort

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The dyadic staircase: `ADV±(MAX) ≤ 2⌈log₂ m⌉ √n`

For `j < k` there is exactly one dyadic block of `[0, 2^L)` whose left half
contains `j` and whose right half contains `k` — namely the block at the highest
bit position where `j` and `k` differ.  Indexing the staircase's coordinates by
that block gives row and column masses `L = ⌈log₂ m⌉` instead of the `m` and `1`
of `QuantumQueryComplexity/Max/Simple.lean`, and hence the bound `2 L √n`.

Coordinates are indexed by **level and prefix**, `Sep L = Fin L × Fin (2 ^ L)`,
rather than by a threshold value.  That choice is what keeps this file short:
mathlib has no lowest-set-bit function for `ℕ`, so a threshold-indexed version
would have to build one and then a bijection onto `Sep L`, and would put
truncated subtraction underneath `2 ^ l`, which `omega` cannot see through.  In
the present encoding there is no subtraction and no induction, and the two mass
bounds are immediate because each level contributes at most one nonzero
coordinate — the prefix is *determined* by the value.

The cut carried by the coordinate `(l, p)` is written `2 * p + 1 ≤ x / 2 ^ l`
rather than the equivalent `p * 2 ^ (l + 1) + 2 ^ l ≤ x`, so that every support
condition reduces to linear arithmetic in the atoms `x / 2 ^ l` and `p`.
-/

namespace QuantumQueryComplexity

/-! ## Bit arithmetic -/

lemma div_pow_succ (x l : ℕ) : x / 2 ^ (l + 1) = x / 2 ^ l / 2 := by
  rw [pow_succ]
  exact (Nat.div_div_eq_div_mul x (2 ^ l) 2).symm

lemma testBit_false_iff {x l : ℕ} : x.testBit l = false ↔ x / 2 ^ l % 2 = 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_false_iff_not]
  omega

lemma testBit_true_iff {x l : ℕ} : x.testBit l = true ↔ x / 2 ^ l % 2 = 1 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_true_eq]

/-- Two numbers share their prefix above bit `l` exactly when all their bits
above `l` agree.  Every prefix argument in this file reduces to this. -/
lemma div_pow_eq_iff {j k l : ℕ} :
    j / 2 ^ (l + 1) = k / 2 ^ (l + 1) ↔ ∀ m, l < m → j.testBit m = k.testBit m := by
  constructor
  · intro h m hm
    obtain ⟨d, rfl⟩ : ∃ d, m = d + (l + 1) := ⟨m - (l + 1), by omega⟩
    rw [Nat.testBit_add, Nat.testBit_add, h]
  · intro h
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [← Nat.testBit_add, ← Nat.testBit_add]
    exact h _ (by omega)

/-- The highest bit position at which `j` and `k` differ. -/
lemma exists_top_diff_bit {j k : ℕ} (h : j ≠ k) :
    ∃ i, j.testBit i ≠ k.testBit i ∧ ∀ m, i < m → j.testBit m = k.testBit m := by
  obtain ⟨i, hi, hi'⟩ := Nat.exists_most_significant_bit (Nat.xor_ne_zero_iff.2 h)
  refine ⟨i, ?_, fun m hm => ?_⟩
  · simpa using hi
  · simpa using hi' m hm

/-- At the highest differing bit, the smaller number carries `0` and the larger
carries `1`.  Proved by contradiction through `Nat.lt_of_testBit`, not by
inspecting `j < k` directly. -/
lemma testBit_top_diff_of_lt {j k i : ℕ} (hjk : j < k)
    (hne : j.testBit i ≠ k.testBit i) (hup : ∀ m, i < m → j.testBit m = k.testBit m) :
    j.testBit i = false ∧ k.testBit i = true := by
  rcases hj : j.testBit i with _ | _
  · refine ⟨rfl, ?_⟩
    rcases hk : k.testBit i with _ | _
    · exact absurd (hj.trans hk.symm) hne
    · rfl
  · exfalso
    have hk : k.testBit i = false := by
      rcases hk : k.testBit i with _ | _
      · rfl
      · exact absurd (hj.trans hk.symm) hne
    exact absurd (Nat.lt_of_testBit i hk hj fun m hm => (hup m hm).symm) (by omega)

/-! ## Separating levels -/

/-- The levels whose dyadic block has `j` in its left half and `k` in its
right half. -/
def sepLv (L j k : ℕ) : Finset (Fin L) :=
  Finset.univ.filter fun l =>
    j / 2 ^ ((l : ℕ) + 1) = k / 2 ^ ((l : ℕ) + 1) ∧
      j.testBit (l : ℕ) = false ∧ k.testBit (l : ℕ) = true

lemma mem_sepLv {L j k : ℕ} {l : Fin L} :
    l ∈ sepLv L j k ↔ j / 2 ^ ((l : ℕ) + 1) = k / 2 ^ ((l : ℕ) + 1) ∧
      j.testBit (l : ℕ) = false ∧ k.testBit (l : ℕ) = true := by
  simp [sepLv]

/-- A separating level witnesses `j < k`.  This is what gives the `k ≤ j`
branch of the pairing for free. -/
lemma lt_of_mem_sepLv {L j k : ℕ} {l : Fin L} (h : l ∈ sepLv L j k) : j < k := by
  rw [mem_sepLv] at h
  exact Nat.lt_of_testBit (l : ℕ) h.2.1 h.2.2 (div_pow_eq_iff.1 h.1)

lemma card_sepLv_of_ge {L j k : ℕ} (h : k ≤ j) : (sepLv L j k).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  exact fun l hl => absurd (lt_of_mem_sepLv hl) (by omega)

lemma card_sepLv_of_lt {L j k : ℕ} (hjk : j < k) (hk : k < 2 ^ L) :
    (sepLv L j k).card = 1 := by
  obtain ⟨i, hne, hup⟩ := exists_top_diff_bit (Nat.ne_of_lt hjk)
  obtain ⟨hj0, hk1⟩ := testBit_top_diff_of_lt hjk hne hup
  have hiL : i < L := by
    by_contra hc
    push_neg at hc
    have h2 : 2 ^ i ≤ k := Nat.ge_two_pow_of_testBit hk1
    have h3 : (2 : ℕ) ^ L ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hc
    omega
  rw [Finset.card_eq_one]
  refine ⟨⟨i, hiL⟩, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, fun l hl => ?_⟩⟩
  · exact mem_sepLv.2 ⟨div_pow_eq_iff.2 hup, hj0, hk1⟩
  · rw [mem_sepLv] at hl
    refine Fin.ext ?_
    rcases lt_trichotomy (l : ℕ) i with hlt | heq | hgt
    · exact absurd (div_pow_eq_iff.1 hl.1 i hlt) hne
    · exact heq
    · refine absurd (hup (l : ℕ) hgt) ?_
      rw [hl.2.1, hl.2.2]
      simp

/-! ## The coordinate set and the two families -/

/-- A coordinate: a bit level `l < L` together with a prefix. -/
abbrev Sep (L : ℕ) := Fin L × Fin (2 ^ L)

/-- The row family: `j` sits in the left half of the block `(l, p)`. -/
def sepLeft (L j : ℕ) (c : Sep L) : ℝ :=
  if (c.2 : ℕ) = j / 2 ^ ((c.1 : ℕ) + 1) ∧ j.testBit (c.1 : ℕ) = false then 1 else 0

/-- The column family: `k` sits in the right half of the block `(l, p)`. -/
def sepRight (L k : ℕ) (c : Sep L) : ℝ :=
  if (c.2 : ℕ) = k / 2 ^ ((c.1 : ℕ) + 1) ∧ k.testBit (c.1 : ℕ) = true then 1 else 0

/-- Collapsing a sum over prefixes: only the prefix determined by `a`
contributes. -/
lemma sum_fin_ite {n a : ℕ} (ha : a < n) (P : Prop) [Decidable P] :
    (∑ p : Fin n, if (p : ℕ) = a ∧ P then (1 : ℝ) else 0) = if P then 1 else 0 := by
  by_cases hP : P
  · have hcongr : ∀ p : Fin n, (if (p : ℕ) = a ∧ P then (1 : ℝ) else 0)
        = if p = (⟨a, ha⟩ : Fin n) then 1 else 0 := fun p => by
      simp [hP, Fin.ext_iff]
    rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) => hcongr p,
      Finset.sum_ite_eq' Finset.univ (⟨a, ha⟩ : Fin n) fun _ => (1 : ℝ),
      if_pos (Finset.mem_univ _), if_pos hP]
  · simp [hP]

/-- **The pairing identity.**  For `j < k` exactly one dyadic block separates
them; for `k ≤ j` none does. -/
lemma sum_sepLeft_mul_sepRight {L j k : ℕ} (hj : j < 2 ^ L) (hk : k < 2 ^ L) :
    (∑ c : Sep L, sepLeft L j c * sepRight L k c) = if j < k then 1 else 0 := by
  have hterm : ∀ (l : Fin L) (p : Fin (2 ^ L)),
      sepLeft L j (l, p) * sepRight L k (l, p)
        = if (p : ℕ) = j / 2 ^ ((l : ℕ) + 1) ∧
            (j / 2 ^ ((l : ℕ) + 1) = k / 2 ^ ((l : ℕ) + 1) ∧
              j.testBit (l : ℕ) = false ∧ k.testBit (l : ℕ) = true) then 1 else 0 := by
    intro l p
    simp only [sepLeft, sepRight]
    by_cases h1 : (p : ℕ) = j / 2 ^ ((l : ℕ) + 1) ∧ j.testBit (l : ℕ) = false
    · by_cases h2 : (p : ℕ) = k / 2 ^ ((l : ℕ) + 1) ∧ k.testBit (l : ℕ) = true
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1.1, by rw [← h1.1, ← h2.1], h1.2, h2.2⟩]
        norm_num
      · rw [if_pos h1, if_neg h2, mul_zero, if_neg]
        rintro ⟨hp, hjk, -, hkb⟩
        exact h2 ⟨by rw [hp, hjk], hkb⟩
    · rw [if_neg h1, zero_mul, if_neg]
      rintro ⟨hp, -, hjb, -⟩
      exact h1 ⟨hp, hjb⟩
  rw [Fintype.sum_prod_type]
  have hstep : ∀ l : Fin L,
      (∑ p : Fin (2 ^ L), sepLeft L j (l, p) * sepRight L k (l, p))
        = if l ∈ sepLv L j k then (1 : ℝ) else 0 := by
    intro l
    rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) => hterm l p,
      sum_fin_ite (lt_of_le_of_lt (Nat.div_le_self _ _) hj)]
    congr 1
    simp [mem_sepLv]
  have hcard : (∑ l : Fin L, if l ∈ sepLv L j k then (1 : ℝ) else 0)
      = ((sepLv L j k).card : ℝ) := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hstep l, hcard]
  rcases lt_or_ge j k with h | h
  · rw [if_pos h, card_sepLv_of_lt h hk]
    norm_num
  · rw [if_neg (by omega), card_sepLv_of_ge h]
    norm_num

/-- Each level contributes at most one nonzero row coordinate, so the row mass
is at most `L`. -/
lemma sum_sepLeft_sq_le {L j : ℕ} (hj : j < 2 ^ L) :
    (∑ c : Sep L, sepLeft L j c * sepLeft L j c) ≤ (L : ℝ) := by
  have hsq : ∀ c : Sep L, sepLeft L j c * sepLeft L j c = sepLeft L j c := by
    intro c
    simp only [sepLeft]
    split_ifs <;> norm_num
  rw [Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => hsq c, Fintype.sum_prod_type]
  simp only [sepLeft]
  calc (∑ l : Fin L, ∑ p : Fin (2 ^ L),
          if (p : ℕ) = j / 2 ^ ((l : ℕ) + 1) ∧ j.testBit (l : ℕ) = false
            then (1 : ℝ) else 0)
      = ∑ l : Fin L, if j.testBit (l : ℕ) = false then (1 : ℝ) else 0 :=
        Finset.sum_congr rfl fun l _ =>
          sum_fin_ite (lt_of_le_of_lt (Nat.div_le_self _ _) hj) _
    _ ≤ ∑ _l : Fin L, (1 : ℝ) :=
        Finset.sum_le_sum fun l _ => by split_ifs <;> norm_num
    _ = (L : ℝ) := by simp

/-- The same for columns. -/
lemma sum_sepRight_sq_le {L k : ℕ} (hk : k < 2 ^ L) :
    (∑ c : Sep L, sepRight L k c * sepRight L k c) ≤ (L : ℝ) := by
  have hsq : ∀ c : Sep L, sepRight L k c * sepRight L k c = sepRight L k c := by
    intro c
    simp only [sepRight]
    split_ifs <;> norm_num
  rw [Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => hsq c, Fintype.sum_prod_type]
  simp only [sepRight]
  calc (∑ l : Fin L, ∑ p : Fin (2 ^ L),
          if (p : ℕ) = k / 2 ^ ((l : ℕ) + 1) ∧ k.testBit (l : ℕ) = true
            then (1 : ℝ) else 0)
      = ∑ l : Fin L, if k.testBit (l : ℕ) = true then (1 : ℝ) else 0 :=
        Finset.sum_congr rfl fun l _ =>
          sum_fin_ite (lt_of_le_of_lt (Nat.div_le_self _ _) hk) _
    _ ≤ ∑ _l : Fin L, (1 : ℝ) :=
        Finset.sum_le_sum fun l _ => by split_ifs <;> norm_num
    _ = (L : ℝ) := by simp

/-! ## Transporting to an arbitrary finite linear order -/

variable {A : Type*} [Fintype A] [DecidableEq A] [LinearOrder A]

/-- The rank of an alphabet value as a natural number. -/
noncomputable def rk (v : A) : ℕ := ((monoEquivOfFin A rfl).symm v : ℕ)

lemma rk_strictMono : StrictMono (rk : A → ℕ) := fun _ _ h =>
  (monoEquivOfFin A rfl).symm.strictMono h

lemma rk_lt_card (v : A) : rk v < Fintype.card A :=
  ((monoEquivOfFin A rfl).symm v).isLt

/-- The number of bit levels needed: `⌈log₂ m⌉`. -/
noncomputable def alphaBits (A : Type*) [Fintype A] : ℕ := Nat.clog 2 (Fintype.card A)

lemma rk_lt_two_pow (v : A) : rk v < 2 ^ alphaBits A :=
  lt_of_lt_of_le (rk_lt_card v) (Nat.le_pow_clog (by norm_num) _)

/-- **The dyadic staircase.**  The coordinate `(l, p)` cuts at the midpoint of
the `p`-th dyadic block of length `2 ^ (l+1)`, expressed as `2p + 1 ≤ x / 2 ^ l`
so that the support conditions are linear. -/
noncomputable def dyadicStaircase : Staircase A (Sep (alphaBits A)) where
  up c v := decide (2 * (c.2 : ℕ) + 1 ≤ rk v / 2 ^ (c.1 : ℕ))
  up_mono := fun _c _v _w hvw hv => by
    simp only [decide_eq_true_eq] at hv ⊢
    exact hv.trans (Nat.div_le_div_right (rk_strictMono.monotone hvw))
  a j c := sepLeft (alphaBits A) (rk j) c
  G k c := sepRight (alphaBits A) (rk k) c
  a_supp := fun j c h => by
    have hc : (c.2 : ℕ) = rk j / 2 ^ ((c.1 : ℕ) + 1) ∧
        (rk j).testBit (c.1 : ℕ) = false := by
      by_contra hcon
      rw [sepLeft, if_neg hcon] at h
      exact h rfl
    rw [decide_eq_false_iff_not, not_le]
    have h1 := div_pow_succ (rk j) (c.1 : ℕ)
    have h2 := testBit_false_iff.1 hc.2
    have h3 := Nat.div_add_mod (rk j / 2 ^ (c.1 : ℕ)) 2
    omega
  G_supp := fun k c h => by
    have hc : (c.2 : ℕ) = rk k / 2 ^ ((c.1 : ℕ) + 1) ∧
        (rk k).testBit (c.1 : ℕ) = true := by
      by_contra hcon
      rw [sepRight, if_neg hcon] at h
      exact h rfl
    rw [decide_eq_true_eq]
    have h1 := div_pow_succ (rk k) (c.1 : ℕ)
    have h2 := testBit_true_iff.1 hc.2
    have h3 := Nat.div_add_mod (rk k / 2 ^ (c.1 : ℕ)) 2
    omega
  pairing := fun j k hjk => by
    rw [sum_sepLeft_mul_sepRight (rk_lt_two_pow j) (rk_lt_two_pow k),
      if_pos (rk_strictMono hjk)]

/-- **`ADV±(MAX) ≤ 2⌈log₂ m⌉ √n`** for an `n`-tuple over an `m`-element
alphabet.

Together with `sqrt_card_le_advPM_maxFun` this pins `ADV±(MAX)` to within a
factor `2⌈log₂ m⌉`.  The true value is `Θ(√n)` with no alphabet dependence, but
every witness of this "threshold" shape costs `√n · γ₂(T_m) = Θ(√n log m)`;
removing the logarithm needs a witness encoding Dürr–Høyer's adaptivity. -/
theorem advPM_maxFun_le_bits {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hA : 0 < alphaBits A) :
    advPM (maxFun : (ι → A) → A)
      ≤ 2 * (alphaBits A : ℝ) * Real.sqrt (Fintype.card ι : ℝ) := by
  have hL : (0 : ℝ) < (alphaBits A : ℝ) := by exact_mod_cast hA
  have h := advPM_maxFun_le (ι := ι) (dyadicStaircase (A := A))
    (fun j => sum_sepLeft_sq_le (rk_lt_two_pow j))
    (fun k => sum_sepRight_sq_le (rk_lt_two_pow k)) hL hL
  refine h.trans (le_of_eq ?_)
  rw [show (Fintype.card ι : ℝ) * (alphaBits A : ℝ) * (alphaBits A : ℝ)
      = ((alphaBits A : ℝ) * (alphaBits A : ℝ)) * (Fintype.card ι : ℝ) from by ring,
    Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self hL.le]
  ring

end QuantumQueryComplexity
