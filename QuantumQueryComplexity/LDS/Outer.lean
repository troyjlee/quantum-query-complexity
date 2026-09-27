import QuantumQueryComplexity.LDS.Dyadic
import QuantumQueryComplexity.LDS.NodeDual
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The outer layer: dyadic blocks as scan slots

`LDS/Dyadic.lean` shows that the longest distinct substring is
attained by one of the dyadic block problems, and `LDS/NodeDual.lean` solves a
block problem at cost `nodeCost L (block size)`.  What is left is to present
the blocks as the *slots of one weighted maximum*.

Two things are needed for that, and both are here:

* `hasDualOn_blockVal` — a block problem's dual, on any promise, obtained from
  the node recursion by `pullbackCoord` along the block's `intervalEmb`.  A
  block whose midpoint falls off the word contributes the constant `0` and so
  costs nothing.
* `ldsFun_eq_maxFun_block` — the decomposition as a `maxFun` over a *finite*
  slot type.  The slots are indexed scale by scale, `Σ s ≤ L, Fin (numBlocks
  n s)`, rather than by all pairs: at scale `s` only about `n / 2^(s+1)` blocks
  exist, and charging the scan for `n` of them at every scale would cost
  `n^{7/6}` instead of `n^{2/3}`.

The remaining step — the weighted scan over these slots, whose cost is the
geometric sum `∑_s ⌈n/2^(s+1)⌉ · (C·L·2^{2(s+1)/3})²` — is `LDS/Main.lean`.
-/

namespace QuantumQueryComplexity

variable {n : ℕ} {σ : Type} [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X] [DecidableEq X]

/-! ## A block problem's dual -/

/-- The size of the block of scale `s` and index `j`. -/
def blockSize (n s j : ℕ) : ℕ := blockHi n s j + 1 - blockLo s j

lemma blockSize_le {n : ℕ} (hn : 0 < n) (s j : ℕ) : blockSize n s j ≤ n := by
  simp only [blockSize, blockHi]
  omega

/-- **A dyadic block problem has a dual solution** at the node cost of its
block, on any promise. -/
theorem hasDualOn_blockVal (L : ℕ) (hL : 1 ≤ L) (hn : n ≤ 2 ^ L)
    (read : X → Fin n → σ) (s j : ℕ) :
    ∃ T : X → ℕ, HasDualOn read (fun x => (T x, blockVal (read x) s j))
      (nodeCost L (blockSize n s j)) := by
  classical
  by_cases h : blockMid s j < n
  · -- the block is a genuine arena: run the node recursion on it
    have hsz : blockSize n s j ≤ 2 ^ L :=
      le_trans (blockSize_le (by omega) s j) hn
    have hglue : blockMid s j - blockLo s j < blockSize n s j := by
      have h1 := blockLo_le_blockMid s j
      have h2 := blockMid_le_blockHi h
      simp only [blockSize]
      omega
    obtain ⟨T, hT⟩ := hasDualOn_bldsFun (σ := σ) L hL (blockSize n s j) hsz
      (⟨blockMid s j - blockLo s j, hglue⟩ : Fin (blockSize n s j))
      (X := X) (fun x k => read x (intervalEmb (blockLo s j) (blockHi n s j)
        (blockHi_lt h) k))
    refine ⟨T, ?_⟩
    have hpull := hT.pullbackCoord
      (e := fun k : Fin (blockSize n s j) =>
        intervalEmb (blockLo s j) (blockHi n s j) (blockHi_lt h) k)
      (intervalEmb_strictMono (blockHi_lt h)).injective
    refine hpull.ofEq fun x => ?_
    have hbv : blockVal (read x) s j
        = bldsFun (⟨blockMid s j - blockLo s j, hglue⟩ : Fin (blockSize n s j))
          (fun k => read x (intervalEmb (blockLo s j) (blockHi n s j)
            (blockHi_lt h) k)) := by
      simp only [blockVal, dif_pos h]
      rfl
    rw [hbv]
  · -- the block falls off the word: the value is the constant `0`
    refine ⟨fun _ => 0, ?_⟩
    refine (hasDualOn_of_const read
      (f := fun x => ((0 : ℕ), blockVal (read x) s j)) fun x y => ?_).mono
      (nodeCost_nonneg L (blockSize n s j))
    simp only [blockVal, dif_neg h]

/-! ## The slots -/

/-- The number of blocks of scale `s` that meet the word. -/
def numBlocks (n s : ℕ) : ℕ := (n + 2 ^ (s + 1) - 1) / 2 ^ (s + 1)

/-- A valid block's index is in range. -/
lemma lt_numBlocks {s j : ℕ} (h : blockMid s j < n) : j < numBlocks n s := by
  have hpow := two_pow_pos (s + 1)
  have hlo := blockLo_le_blockMid s j
  have hj : j * 2 ^ (s + 1) < n := by
    simp only [blockLo] at hlo
    omega
  by_contra hc
  have hle : numBlocks n s ≤ j := by omega
  have hmul : numBlocks n s * 2 ^ (s + 1) ≤ j * 2 ^ (s + 1) :=
    Nat.mul_le_mul_right _ hle
  have hge : n ≤ numBlocks n s * 2 ^ (s + 1) := by
    have hdm := Nat.div_add_mod (n + 2 ^ (s + 1) - 1) (2 ^ (s + 1))
    have hmod : (n + 2 ^ (s + 1) - 1) % 2 ^ (s + 1) < 2 ^ (s + 1) :=
      Nat.mod_lt _ hpow
    have hcomm : numBlocks n s * 2 ^ (s + 1)
        = 2 ^ (s + 1) * ((n + 2 ^ (s + 1) - 1) / 2 ^ (s + 1)) := by
      simp only [numBlocks]
      ring
    omega
  omega

/-- A valid block's scale is at most `L`, once the word fits in `2 ^ L`. -/
lemma le_of_blockMid_lt {s j L : ℕ} (h : blockMid s j < n) (hn : n ≤ 2 ^ L) :
    s ≤ L := by
  have hlo := blockLo_le_blockMid s j
  have hps := two_pow_pos s
  have hbase : 2 ^ s ≤ n := by
    simp only [blockMid, blockLo] at h
    omega
  by_contra hc
  have hlt : L < s := by omega
  have hmono : (2 : ℕ) ^ (L + 1) ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsucc : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
  have hL := Nat.two_pow_pos L
  omega

/-- **The decomposition as a finite maximum** — the form the weighted scan
consumes.  Slots are indexed scale by scale, so their number is `O(n)`, not
`O(n log n)`. -/
theorem ldsFun_eq_maxFun_block {L : ℕ} (hn : 0 < n) (hnL : n ≤ 2 ^ L)
    (α : Fin n → σ) :
    ldsFun α = maxFun fun p : Option (Σ s : Fin (L + 1), Fin (numBlocks n s)) =>
      p.elim 0 fun q => blockVal α (q.1 : ℕ) (q.2 : ℕ) := by
  classical
  refine le_antisymm ?_ (maxFun_le fun p => ?_)
  swap
  · cases p with
    | none => exact Nat.zero_le _
    | some q => exact blockVal_le_ldsFun α _ _
  obtain ⟨s, j, hsj⟩ := exists_blockVal_eq_ldsFun hn α
  have hone : 1 ≤ ldsFun α := one_le_ldsFun hn α
  have hmid : blockMid s j < n := by
    by_contra hc
    rw [hsj] at hone
    simp only [blockVal, dif_neg hc] at hone
    omega
  have hsL : s ≤ L := le_of_blockMid_lt hmid hnL
  have hjb : j < numBlocks n s := lt_numBlocks hmid
  have := le_maxFun (fun p : Option (Σ s : Fin (L + 1), Fin (numBlocks n s)) =>
    p.elim 0 fun q => blockVal α (q.1 : ℕ) (q.2 : ℕ))
    (some ⟨⟨s, by omega⟩, ⟨j, hjb⟩⟩)
  rw [hsj]
  exact this

end QuantumQueryComplexity
