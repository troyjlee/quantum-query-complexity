import QuantumQueryComplexity.LDS.Child
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# The dyadic top level

The node recursion solves *glued* windows
that touch a fixed position; the whole word's longest distinct substring is
recovered by running it on **dyadic crossing blocks**: for every scale, the
word is cut into blocks of length `2^(s+1)`, and each block is handed to the
node problem with its glue at the last position of the block's lower half.

    ldsFun α = sup over blocks with `mid < n` of  blds(mid) (α restricted to
                                                             the block)

The `≥` direction is immediate — a distinct window of a block is a distinct
window of `α`.  The `≤` direction is the covering argument: a window `[i, k]`
with `i < k` lies in a *smallest* dyadic block containing both ends, and
minimality forces `i` into the lower half and `k` into the upper, so the window
straddles that block's midpoint and is a legal node window.  Windows of length
one are covered too: every position is either a midpoint or its successor at
scale `0`.

Blocks are contiguous, so a block's word is `α ∘ intervalEmb`, and
`LDS/Child.lean`'s `isDistinct_intervalEmb` transfers distinctness both ways.
-/

namespace QuantumQueryComplexity

variable {n : ℕ} {σ : Type*} [DecidableEq σ]

/-! ## Dyadic blocks -/

/-- The left end of the dyadic block of scale `s` and index `j`; the block has
length `2 ^ (s + 1)`. -/
def blockLo (s j : ℕ) : ℕ := j * 2 ^ (s + 1)

/-- The block's midpoint: the last position of its lower half. -/
def blockMid (s j : ℕ) : ℕ := blockLo s j + 2 ^ s - 1

/-- The block's right end, clipped to the word. -/
def blockHi (n s j : ℕ) : ℕ := min (blockLo s j + 2 ^ (s + 1) - 1) (n - 1)

lemma two_pow_pos (s : ℕ) : 0 < 2 ^ s := Nat.two_pow_pos s

lemma two_pow_le_succ (s : ℕ) : 2 ^ s ≤ 2 ^ (s + 1) := by
  have h : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by ring
  have := two_pow_pos s
  omega

lemma blockLo_le_blockMid (s j : ℕ) : blockLo s j ≤ blockMid s j := by
  have := two_pow_pos s
  simp only [blockMid]
  omega

lemma blockMid_le_blockHi {s j : ℕ} (h : blockMid s j < n) :
    blockMid s j ≤ blockHi n s j := by
  have h1 := two_pow_pos s
  have h2 := two_pow_le_succ s
  simp only [blockHi, blockMid] at *
  omega

lemma blockHi_lt {s j : ℕ} (h : blockMid s j < n) : blockHi n s j < n := by
  simp only [blockHi]
  omega

/-- **The node problem on a dyadic block**, as a function of the whole word. -/
def blockVal (α : Fin n → σ) (s j : ℕ) : ℕ :=
  if h : blockMid s j < n then
    bldsFun (⟨blockMid s j - blockLo s j, by
        have h1 := blockLo_le_blockMid s j
        have h2 := blockMid_le_blockHi h
        omega⟩ : Fin (blockHi n s j + 1 - blockLo s j))
      (α ∘ intervalEmb (blockLo s j) (blockHi n s j) (blockHi_lt h))
  else 0

/-! ## The two directions -/

/-- Every block value is a genuine distinct-window length. -/
theorem blockVal_le_ldsFun (α : Fin n → σ) (s j : ℕ) : blockVal α s j ≤ ldsFun α := by
  simp only [blockVal]
  split
  · rename_i h
    refine bldsFun_le_of fun k k' hd _ => ?_
    rw [isDistinct_intervalEmb] at hd
    have := le_ldsFun hd
    simp only [winLen, intervalEmb_val] at this ⊢
    omega
  · exact Nat.zero_le _

/-- **The covering step**: a distinct window straddles the midpoint of the
smallest dyadic block containing it, so its length is one of the block
values. -/
theorem winLen_le_blockVal {α : Fin n → σ} {i k : Fin n} (hik : (i : ℕ) ≤ (k : ℕ))
    (hd : IsDistinct α i k) :
    ∃ s j : ℕ, winLen i k ≤ blockVal α s j := by
  classical
  -- the scales on which `i` and `k` share a block
  have hex : ∃ s : ℕ, (i : ℕ) / 2 ^ (s + 1) = (k : ℕ) / 2 ^ (s + 1) := by
    refine ⟨(k : ℕ), ?_⟩
    have h1 : (k : ℕ) < 2 ^ ((k : ℕ) + 1) := by
      have hself : (k : ℕ) < 2 ^ (k : ℕ) := Nat.lt_two_pow_self
      have h2 := two_pow_le_succ (k : ℕ)
      omega
    rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt h1]
  obtain ⟨s, hfind, hmin⟩ : ∃ s : ℕ, (i : ℕ) / 2 ^ (s + 1) = (k : ℕ) / 2 ^ (s + 1)
      ∧ ∀ t, t < s → (i : ℕ) / 2 ^ (t + 1) ≠ (k : ℕ) / 2 ^ (t + 1) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun t ht => Nat.find_min hex ht⟩
  refine ⟨s, (i : ℕ) / 2 ^ (s + 1), ?_⟩
  -- the block containing both ends
  have hpow : 0 < 2 ^ (s + 1) := two_pow_pos _
  have hdm := Nat.div_add_mod (i : ℕ) (2 ^ (s + 1))
  have hdmk := Nat.div_add_mod (k : ℕ) (2 ^ (s + 1))
  have hmod : (i : ℕ) % 2 ^ (s + 1) < 2 ^ (s + 1) := Nat.mod_lt _ hpow
  have hmodk : (k : ℕ) % 2 ^ (s + 1) < 2 ^ (s + 1) := Nat.mod_lt _ hpow
  have hlo : blockLo s ((i : ℕ) / 2 ^ (s + 1)) ≤ (i : ℕ) := by
    simp only [blockLo]
    rw [Nat.mul_comm]
    omega
  have hhi : (k : ℕ) ≤ blockLo s ((i : ℕ) / 2 ^ (s + 1)) + 2 ^ (s + 1) - 1 := by
    simp only [blockLo]
    have hcomm : (i : ℕ) / 2 ^ (s + 1) * 2 ^ (s + 1)
        = 2 ^ (s + 1) * ((i : ℕ) / 2 ^ (s + 1)) := by ring
    rw [← hfind] at hdmk
    omega
  -- minimality: the two ends fall in different halves
  have hmid : ((i : ℕ) ≤ blockMid s ((i : ℕ) / 2 ^ (s + 1))
      ∧ blockMid s ((i : ℕ) / 2 ^ (s + 1)) < (k : ℕ)) ∨ (s = 0 ∧ (i : ℕ) = (k : ℕ)) := by
    rcases eq_or_lt_of_le hik with heq | hlt
    · refine Or.inr ⟨?_, heq⟩
      by_contra hc
      exact hmin 0 (Nat.pos_of_ne_zero hc) (by rw [heq])
    refine Or.inl ?_
    rcases Nat.eq_zero_or_pos s with hs0 | hspos
    · -- scale `0`: the block is a pair, so `i` is its midpoint
      subst hs0
      have h2 : (2 : ℕ) ^ (0 + 1) = 2 := by norm_num
      simp only [blockMid, blockLo, h2] at *
      omega
    · -- `s > 0`: minimality of `s` puts `i` and `k` in different halves
      have hprev : (i : ℕ) / 2 ^ s ≠ (k : ℕ) / 2 ^ s := by
        have h := hmin (s - 1) (by omega)
        have hsub : s - 1 + 1 = s := by omega
        rwa [hsub] at h
      have hps : 0 < 2 ^ s := two_pow_pos s
      have hdi := Nat.div_add_mod (i : ℕ) (2 ^ s)
      have hdk := Nat.div_add_mod (k : ℕ) (2 ^ s)
      have hmi : (i : ℕ) % 2 ^ s < 2 ^ s := Nat.mod_lt _ hps
      have hmk : (k : ℕ) % 2 ^ s < 2 ^ s := Nat.mod_lt _ hps
      have hsplit : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by ring
      simp only [blockMid, blockLo]
      -- both are in the same `2^(s+1)`-block but different `2^s`-blocks
      have hqi : (i : ℕ) / 2 ^ s = 2 * ((i : ℕ) / 2 ^ (s + 1))
          ∨ (i : ℕ) / 2 ^ s = 2 * ((i : ℕ) / 2 ^ (s + 1)) + 1 := by
        have h := Nat.div_add_mod ((i : ℕ) / 2 ^ s) 2
        have hcomp : (i : ℕ) / 2 ^ s / 2 = (i : ℕ) / 2 ^ (s + 1) := by
          rw [Nat.div_div_eq_div_mul, show (2 : ℕ) ^ s * 2 = 2 ^ (s + 1) by ring]
        have hm2 : (i : ℕ) / 2 ^ s % 2 < 2 := Nat.mod_lt _ (by norm_num)
        omega
      have hqk : (k : ℕ) / 2 ^ s = 2 * ((k : ℕ) / 2 ^ (s + 1))
          ∨ (k : ℕ) / 2 ^ s = 2 * ((k : ℕ) / 2 ^ (s + 1)) + 1 := by
        have h := Nat.div_add_mod ((k : ℕ) / 2 ^ s) 2
        have hcomp : (k : ℕ) / 2 ^ s / 2 = (k : ℕ) / 2 ^ (s + 1) := by
          rw [Nat.div_div_eq_div_mul, show (2 : ℕ) ^ s * 2 = 2 ^ (s + 1) by ring]
        have hm2 : (k : ℕ) / 2 ^ s % 2 < 2 := Nat.mod_lt _ (by norm_num)
        omega
      have hile : (i : ℕ) / 2 ^ s * 2 ^ s ≤ (i : ℕ) := Nat.div_mul_le_self _ _
      have hkle : (k : ℕ) / 2 ^ s * 2 ^ s ≤ (k : ℕ) := Nat.div_mul_le_self _ _
      rw [← hfind] at hqk
      rcases hqi with hqi | hqi <;> rcases hqk with hqk | hqk
      · exfalso; exact hprev (hqi.trans hqk.symm)
      · constructor
        · have hib : (i : ℕ) < ((i : ℕ) / 2 ^ s + 1) * 2 ^ s := by
            have hexp2 : ((i : ℕ) / 2 ^ s + 1) * 2 ^ s
                = 2 ^ s * ((i : ℕ) / 2 ^ s) + 2 ^ s := by ring
            omega
          rw [hqi] at hib
          have this := hib
          have hexp : (2 * ((i : ℕ) / 2 ^ (s + 1)) + 1) * 2 ^ s
              = ((i : ℕ) / 2 ^ (s + 1)) * (2 * 2 ^ s) + 2 ^ s := by ring
          rw [hexp, ← hsplit] at this
          omega
        · have hkge : (2 * ((i : ℕ) / 2 ^ (s + 1)) + 1) * 2 ^ s ≤ (k : ℕ) := by
            rw [← hqk]; exact hkle
          have hexp : (2 * ((i : ℕ) / 2 ^ (s + 1)) + 1) * 2 ^ s
              = ((i : ℕ) / 2 ^ (s + 1)) * (2 * 2 ^ s) + 2 ^ s := by ring
          rw [hexp, ← hsplit] at hkge
          omega
      · exfalso
        have hlt' : (k : ℕ) / 2 ^ s < (i : ℕ) / 2 ^ s := by omega
        have : (k : ℕ) < (i : ℕ) := by
          have h1 : (k : ℕ) < ((k : ℕ) / 2 ^ s + 1) * 2 ^ s := by
            have hexp2 : ((k : ℕ) / 2 ^ s + 1) * 2 ^ s
                = 2 ^ s * ((k : ℕ) / 2 ^ s) + 2 ^ s := by ring
            omega
          have h2 : ((k : ℕ) / 2 ^ s + 1) * 2 ^ s ≤ ((i : ℕ) / 2 ^ s) * 2 ^ s :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        omega
      · exfalso; exact hprev (hqi.trans hqk.symm)
  -- so the window is a node window of that block
  have hmidlt : blockMid s ((i : ℕ) / 2 ^ (s + 1)) < n := by
    have hkn := k.isLt
    rcases hmid with ⟨h1, h2⟩ | ⟨hs0, heq⟩
    · omega
    · subst hs0
      have hpow : (2 : ℕ) ^ 0 = 1 := by norm_num
      simp only [blockMid, hpow] at *
      omega
  simp only [blockVal, dif_pos hmidlt]
  have hkn := k.isLt
  have hin := i.isLt
  have hhi2 : (k : ℕ) ≤ blockHi n s ((i : ℕ) / 2 ^ (s + 1)) := by
    simp only [blockHi]
    omega
  have hbi : (i : ℕ) - blockLo s ((i : ℕ) / 2 ^ (s + 1))
      < blockHi n s ((i : ℕ) / 2 ^ (s + 1)) + 1 - blockLo s ((i : ℕ) / 2 ^ (s + 1)) := by
    omega
  have hbk : (k : ℕ) - blockLo s ((i : ℕ) / 2 ^ (s + 1))
      < blockHi n s ((i : ℕ) / 2 ^ (s + 1)) + 1 - blockLo s ((i : ℕ) / 2 ^ (s + 1)) := by
    omega
  have hei : intervalEmb (blockLo s ((i : ℕ) / 2 ^ (s + 1)))
      (blockHi n s ((i : ℕ) / 2 ^ (s + 1))) (blockHi_lt hmidlt)
      ⟨(i : ℕ) - blockLo s ((i : ℕ) / 2 ^ (s + 1)), hbi⟩ = i := by
    apply Fin.ext
    simp only [intervalEmb_val]
    omega
  have hek : intervalEmb (blockLo s ((i : ℕ) / 2 ^ (s + 1)))
      (blockHi n s ((i : ℕ) / 2 ^ (s + 1))) (blockHi_lt hmidlt)
      ⟨(k : ℕ) - blockLo s ((i : ℕ) / 2 ^ (s + 1)), hbk⟩ = k := by
    apply Fin.ext
    simp only [intervalEmb_val]
    omega
  have hdc : IsDistinct (α ∘ intervalEmb (blockLo s ((i : ℕ) / 2 ^ (s + 1)))
      (blockHi n s ((i : ℕ) / 2 ^ (s + 1))) (blockHi_lt hmidlt))
      ⟨(i : ℕ) - blockLo s ((i : ℕ) / 2 ^ (s + 1)), hbi⟩
      ⟨(k : ℕ) - blockLo s ((i : ℕ) / 2 ^ (s + 1)), hbk⟩ := by
    rw [isDistinct_intervalEmb, hei, hek]
    exact hd
  have hmh : blockMid s ((i : ℕ) / 2 ^ (s + 1)) ≤ blockHi n s ((i : ℕ) / 2 ^ (s + 1)) :=
    blockMid_le_blockHi hmidlt
  have hlm : blockLo s ((i : ℕ) / 2 ^ (s + 1)) ≤ blockMid s ((i : ℕ) / 2 ^ (s + 1)) :=
    blockLo_le_blockMid _ _
  have htc : Touches (⟨blockMid s ((i : ℕ) / 2 ^ (s + 1))
        - blockLo s ((i : ℕ) / 2 ^ (s + 1)), by omega⟩ :
      Fin (blockHi n s ((i : ℕ) / 2 ^ (s + 1)) + 1
        - blockLo s ((i : ℕ) / 2 ^ (s + 1))))
      ⟨(i : ℕ) - blockLo s ((i : ℕ) / 2 ^ (s + 1)), hbi⟩
      ⟨(k : ℕ) - blockLo s ((i : ℕ) / 2 ^ (s + 1)), hbk⟩ := by
    rcases hmid with ⟨h1, h2⟩ | ⟨hs0, heq⟩
    · constructor <;> simp only [Fin.val_mk] <;> omega
    · subst hs0
      have hpow : (2 : ℕ) ^ 0 = 1 := by norm_num
      have hpow1 : (2 : ℕ) ^ (0 + 1) = 2 := by norm_num
      simp only [blockMid, blockLo, hpow, hpow1] at *
      constructor <;> simp only [Fin.val_mk] <;> omega
  have := le_bldsFun hdc htc
  simp only [winLen, Fin.val_mk] at this ⊢
  omega

/-- **The dyadic decomposition**: the longest distinct
substring of a nonempty word is attained by one of the dyadic block problems.
With `blockVal_le_ldsFun` this says the two are equal, which is the identity
the outer scan runs on. -/
theorem exists_blockVal_eq_ldsFun (hn : 0 < n) (α : Fin n → σ) :
    ∃ s j : ℕ, ldsFun α = blockVal α s j := by
  classical
  -- a window realising the maximum
  have hne : (Finset.univ : Finset (Fin n × Fin n)).Nonempty := by
    refine ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup Finset.univ hne
    (fun p : Fin n × Fin n => if IsDistinct α p.1 p.2 then winLen p.1 p.2 else 0)
  have hlds : ldsFun α = if IsDistinct α p.1 p.2 then winLen p.1 p.2 else 0 := hp
  have hone : 1 ≤ ldsFun α := one_le_ldsFun hn α
  have hguard : IsDistinct α p.1 p.2 := by
    by_contra hc
    rw [if_neg hc] at hlds
    omega
  rw [if_pos hguard] at hlds
  have hik : (p.1 : ℕ) ≤ (p.2 : ℕ) := by
    by_contra hc
    have : winLen p.1 p.2 = 0 := by simp only [winLen]; omega
    omega
  obtain ⟨s, j, hsj⟩ := winLen_le_blockVal hik hguard
  exact ⟨s, j, le_antisymm (hlds ▸ hsj) (blockVal_le_ldsFun α s j)⟩

end QuantumQueryComplexity
