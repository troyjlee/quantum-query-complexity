import QuantumQueryComplexity.LDS.Outer
import QuantumQueryComplexity.LDS.OuterCost
import QuantumQueryComplexity.Promise.Max
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Longest distinct substring: the headline bound

The last assembly.  `LDS/Outer.lean` presents the word as a maximum over
dyadic blocks and solves each block; `Promise/Max.lean`'s weighted scan
combines them at cost `16 √(∑ c²)`; `LDS/OuterCost.lean` bounds that sum.

    advPM (ldsFun : (Fin n → σ) → ℕ) ≤ 112 · nodeConst · L · n^{2/3}

whenever `n ≤ 2^L ≤ 2n` — that is, for `L = ⌈log₂ n⌉`, the promised
`O(n^{2/3} log n)`, with no `log log n`: the weighted scan replaces the
paper's max-finding subroutine.

The scan's value maps project each block's *joint* output (descriptor chain
and value) to its value, which is legal exactly because it happens inside the
outer function — the joint-output discipline forbids only
recoding a joint by `ofKer`.  So the result is a dual for `ldsFun` itself, not
for a pair.
-/

namespace QuantumQueryComplexity

variable {n : ℕ} {σ : Type} [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X] [DecidableEq X]

/-! ## The slots and their costs -/

/-- The slots of the outer scan: one per dyadic block, plus an idle slot that
makes the type nonempty. -/
abbrev Slot (n L : ℕ) : Type := Option (Σ s : Fin (L + 1), Fin (numBlocks n s))

/-- Each block of a slot is nonempty. -/
lemma blockSize_pos {s j : ℕ} (hj : j < numBlocks n s) : 0 < blockSize n s j := by
  have hpow := two_pow_pos (s + 1)
  have hlt : blockLo s j < n := by
    have hdm := Nat.div_add_mod (n + 2 ^ (s + 1) - 1) (2 ^ (s + 1))
    have hmod : (n + 2 ^ (s + 1) - 1) % 2 ^ (s + 1) < 2 ^ (s + 1) := Nat.mod_lt _ hpow
    have hmul : (j + 1) * 2 ^ (s + 1) ≤ numBlocks n s * 2 ^ (s + 1) :=
      Nat.mul_le_mul_right _ hj
    have hcomm : numBlocks n s * 2 ^ (s + 1)
        = 2 ^ (s + 1) * ((n + 2 ^ (s + 1) - 1) / 2 ^ (s + 1)) := by
      simp only [numBlocks]
      ring
    have hexp : (j + 1) * 2 ^ (s + 1) = j * 2 ^ (s + 1) + 2 ^ (s + 1) := by ring
    simp only [blockLo]
    omega
  simp only [blockSize, blockHi, blockLo] at *
  omega

/-- The cost carried by each slot. -/
noncomputable def slotCost (n L : ℕ) : Slot n L → ℝ :=
  fun p => p.elim (nodeCost L 1) fun q => nodeCost L (blockSize n (q.1 : ℕ) (q.2 : ℕ))

lemma slotCost_pos (hL : 1 ≤ L) (p : Slot n L) : 0 < slotCost n L p := by
  have hC : (0 : ℝ) < nodeConst := nodeConst_pos
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have key : ∀ k : ℕ, 0 < k → 0 < nodeCost L k := by
    intro k hk
    have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hkr : (0 : ℝ) < (k : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hk' _
    unfold nodeCost
    exact mul_pos (mul_pos hC (by linarith)) hkr
  cases p with
  | none => exact key 1 (by norm_num)
  | some q => exact key _ (blockSize_pos q.2.isLt)

/-! ## The cost of the scan -/

/-- **The slot costs fit under `7 C L n^{2/3}`.**  This is `outer_sum_le`
after the block sizes are bounded by their scale. -/
theorem costNorm_slotCost_le {L : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L)
    (hL2 : (2 : ℕ) ^ (L + 2) ≤ 8 * n) :
    costNorm (slotCost n L) ≤ 7 * (nodeConst * L * (n : ℝ) ^ ((2 : ℝ) / 3)) := by
  have hC : (0 : ℝ) < nodeConst := nodeConst_pos
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn43 : (1 : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 3) := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    calc (1 : ℝ) = (1 : ℝ) ^ ((4 : ℝ) / 3) := (Real.one_rpow _).symm
      _ ≤ (n : ℝ) ^ ((4 : ℝ) / 3) := Real.rpow_le_rpow (by norm_num) hn1 (by norm_num)
  -- every slot's squared cost, in terms of its scale
  have hterm : ∀ (s : Fin (L + 1)) (j : Fin (numBlocks n s)),
      (nodeCost L (blockSize n (s : ℕ) (j : ℕ))) ^ 2
        ≤ (nodeConst * L) ^ 2 * (((2 : ℝ) ^ ((s : ℕ) + 1))) ^ ((4 : ℝ) / 3) := by
    intro s j
    have hle : (blockSize n (s : ℕ) (j : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((s : ℕ) + 1) := by
      have h : blockSize n (s : ℕ) (j : ℕ) ≤ 2 ^ ((s : ℕ) + 1) := by
        have e1 : blockHi n (s : ℕ) (j : ℕ)
            = min (blockLo (s : ℕ) (j : ℕ) + 2 ^ ((s : ℕ) + 1) - 1) (n - 1) := rfl
        have hp := two_pow_pos ((s : ℕ) + 1)
        have hp' := two_pow_pos (s : ℕ)
        simp only [blockSize, e1]
        omega
      exact_mod_cast h
    have hrp : ((blockSize n (s : ℕ) (j : ℕ) : ℕ) : ℝ) ^ ((2 : ℝ) / 3)
        ≤ ((2 : ℝ) ^ ((s : ℕ) + 1)) ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hle (by norm_num)
    have hsq : (((2 : ℝ) ^ ((s : ℕ) + 1)) ^ ((2 : ℝ) / 3)) ^ 2
        = ((2 : ℝ) ^ ((s : ℕ) + 1)) ^ ((4 : ℝ) / 3) := by
      rw [← Real.rpow_natCast (((2 : ℝ) ^ ((s : ℕ) + 1)) ^ ((2 : ℝ) / 3)) 2,
        ← Real.rpow_mul (by positivity)]
      norm_num
    have hnn : (0 : ℝ) ≤ ((blockSize n (s : ℕ) (j : ℕ) : ℕ) : ℝ) ^ ((2 : ℝ) / 3) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    unfold nodeCost
    calc (nodeConst * (L : ℝ) * ((blockSize n (s : ℕ) (j : ℕ) : ℕ) : ℝ) ^ ((2 : ℝ) / 3)) ^ 2
        = (nodeConst * L) ^ 2
            * (((blockSize n (s : ℕ) (j : ℕ) : ℕ) : ℝ) ^ ((2 : ℝ) / 3)) ^ 2 := by ring
      _ ≤ (nodeConst * L) ^ 2 * ((((2 : ℝ) ^ ((s : ℕ) + 1))) ^ ((2 : ℝ) / 3)) ^ 2 := by
          have hAB : (((blockSize n (s : ℕ) (j : ℕ) : ℕ) : ℝ) ^ ((2 : ℝ) / 3)) ^ 2
              ≤ ((((2 : ℝ) ^ ((s : ℕ) + 1))) ^ ((2 : ℝ) / 3)) ^ 2 := by
            rw [sq, sq]
            exact mul_le_mul hrp hrp hnn (le_trans hnn hrp)
          exact mul_le_mul_of_nonneg_left hAB (by positivity)
      _ = (nodeConst * L) ^ 2 * (((2 : ℝ) ^ ((s : ℕ) + 1))) ^ ((4 : ℝ) / 3) := by
          rw [hsq]
  -- each scale contributes at most `numBlocks` copies of its term
  have hscale : ∀ s : Fin (L + 1),
      ∑ j : Fin (numBlocks n (s : ℕ)), (nodeCost L (blockSize n (s : ℕ) (j : ℕ))) ^ 2
        ≤ (numBlocks n (s : ℕ) : ℝ) * ((nodeConst * L) ^ 2
            * (((2 : ℝ) ^ ((s : ℕ) + 1))) ^ ((4 : ℝ) / 3)) := by
    intro s
    calc ∑ j : Fin (numBlocks n (s : ℕ)),
          (nodeCost L (blockSize n (s : ℕ) (j : ℕ))) ^ 2
        ≤ ∑ _j : Fin (numBlocks n (s : ℕ)), ((nodeConst * L) ^ 2
            * (((2 : ℝ) ^ ((s : ℕ) + 1))) ^ ((4 : ℝ) / 3)) :=
          Finset.sum_le_sum fun j _ => hterm s j
      _ = (numBlocks n (s : ℕ) : ℝ) * ((nodeConst * L) ^ 2
            * (((2 : ℝ) ^ ((s : ℕ) + 1))) ^ ((4 : ℝ) / 3)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- and `⌈n/u⌉ · u^{4/3} ≤ n · u^{1/3} + u^{4/3}`
  have hstep : ∀ s : ℕ,
      (numBlocks n s : ℝ) * (((2 : ℝ) ^ (s + 1))) ^ ((4 : ℝ) / 3)
        ≤ (n : ℝ) * (((2 : ℝ) ^ (s + 1))) ^ ((1 : ℝ) / 3)
          + (((2 : ℝ) ^ (s + 1))) ^ ((4 : ℝ) / 3) := by
    intro s
    have hu : (0 : ℝ) < (2 : ℝ) ^ (s + 1) := by positivity
    have hsplit : ((2 : ℝ) ^ (s + 1)) ^ ((4 : ℝ) / 3)
        = ((2 : ℝ) ^ (s + 1)) * ((2 : ℝ) ^ (s + 1)) ^ ((1 : ℝ) / 3) := by
      rw [show (4 : ℝ) / 3 = 1 + (1 : ℝ) / 3 by ring, Real.rpow_add hu, Real.rpow_one]
    have hnb : (numBlocks n s : ℝ) * ((2 : ℝ) ^ (s + 1))
        ≤ (n : ℝ) + (2 : ℝ) ^ (s + 1) := by
      have h : numBlocks n s * 2 ^ (s + 1) ≤ n + 2 ^ (s + 1) := by
        have hdm := Nat.div_add_mod (n + 2 ^ (s + 1) - 1) (2 ^ (s + 1))
        have hpow := two_pow_pos (s + 1)
        have hmod : (n + 2 ^ (s + 1) - 1) % 2 ^ (s + 1) < 2 ^ (s + 1) := Nat.mod_lt _ hpow
        have hcomm : numBlocks n s * 2 ^ (s + 1)
            = 2 ^ (s + 1) * ((n + 2 ^ (s + 1) - 1) / 2 ^ (s + 1)) := by
          simp only [numBlocks]
          ring
        omega
      exact_mod_cast h
    have hup : (0 : ℝ) ≤ ((2 : ℝ) ^ (s + 1)) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hu.le _
    calc (numBlocks n s : ℝ) * ((2 : ℝ) ^ (s + 1)) ^ ((4 : ℝ) / 3)
        = ((numBlocks n s : ℝ) * ((2 : ℝ) ^ (s + 1)))
            * ((2 : ℝ) ^ (s + 1)) ^ ((1 : ℝ) / 3) := by rw [hsplit]; ring
      _ ≤ ((n : ℝ) + (2 : ℝ) ^ (s + 1)) * ((2 : ℝ) ^ (s + 1)) ^ ((1 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_right hnb hup
      _ = (n : ℝ) * ((2 : ℝ) ^ (s + 1)) ^ ((1 : ℝ) / 3)
            + ((2 : ℝ) ^ (s + 1)) ^ ((4 : ℝ) / 3) := by rw [hsplit]; ring
  have hCL : (0 : ℝ) ≤ (nodeConst * L) ^ 2 := by positivity
  have hsum : ∑ p : Slot n L, slotCost n L p * slotCost n L p
      ≤ (nodeConst * L) ^ 2 * (1 + 40 * (n : ℝ) ^ ((4 : ℝ) / 3)) := by
    have hone : slotCost n L none * slotCost n L none = (nodeConst * L) ^ 2 := by
      simp only [slotCost, Option.elim, nodeCost]
      rw [Nat.cast_one, Real.one_rpow]
      ring
    have hbody : ∑ q : Σ s : Fin (L + 1), Fin (numBlocks n (s : ℕ)),
          slotCost n L (some q) * slotCost n L (some q)
        ≤ (nodeConst * L) ^ 2 * (40 * (n : ℝ) ^ ((4 : ℝ) / 3)) := by
      have hsq : ∀ q : Σ s : Fin (L + 1), Fin (numBlocks n (s : ℕ)),
          slotCost n L (some q) * slotCost n L (some q)
            = (nodeCost L (blockSize n (q.1 : ℕ) (q.2 : ℕ))) ^ 2 := by
        intro q
        simp only [slotCost, Option.elim]
        ring
      rw [Finset.sum_congr rfl fun q _ => hsq q, Fintype.sum_sigma]
      calc ∑ s : Fin (L + 1), ∑ j : Fin (numBlocks n (s : ℕ)),
            (nodeCost L (blockSize n (s : ℕ) (j : ℕ))) ^ 2
          ≤ ∑ s : Fin (L + 1), ((nodeConst * L) ^ 2
              * ((n : ℝ) * (((2 : ℝ) ^ ((s : ℕ) + 1))) ^ ((1 : ℝ) / 3)
                + (((2 : ℝ) ^ ((s : ℕ) + 1))) ^ ((4 : ℝ) / 3))) := by
            refine Finset.sum_le_sum fun s _ => le_trans (hscale s) ?_
            have hs := hstep (s : ℕ)
            nlinarith
        _ = (nodeConst * L) ^ 2 * ∑ s : Fin (L + 1),
              ((n : ℝ) * (((2 : ℝ) ^ ((s : ℕ) + 1))) ^ ((1 : ℝ) / 3)
                + (((2 : ℝ) ^ ((s : ℕ) + 1))) ^ ((4 : ℝ) / 3)) := by
            rw [Finset.mul_sum]
        _ ≤ (nodeConst * L) ^ 2 * (40 * (n : ℝ) ^ ((4 : ℝ) / 3)) := by
            have hrange : ∑ s : Fin (L + 1),
                ((n : ℝ) * (((2 : ℝ) ^ ((s : ℕ) + 1))) ^ ((1 : ℝ) / 3)
                  + (((2 : ℝ) ^ ((s : ℕ) + 1))) ^ ((4 : ℝ) / 3))
                = ∑ s ∈ Finset.range (L + 1),
                  ((n : ℝ) * (((2 : ℝ) ^ (s + 1))) ^ ((1 : ℝ) / 3)
                    + (((2 : ℝ) ^ (s + 1))) ^ ((4 : ℝ) / 3)) :=
              Fin.sum_univ_eq_sum_range
                (fun s : ℕ => (n : ℝ) * (((2 : ℝ) ^ (s + 1))) ^ ((1 : ℝ) / 3)
                  + (((2 : ℝ) ^ (s + 1))) ^ ((4 : ℝ) / 3)) (L + 1)
            rw [hrange]
            exact mul_le_mul_of_nonneg_left (outer_sum_le hn hL2) hCL
    rw [Fintype.sum_option, hone]
    linarith
  have hbound : (nodeConst * L) ^ 2 * (1 + 40 * (n : ℝ) ^ ((4 : ℝ) / 3))
      ≤ (7 * (nodeConst * L * (n : ℝ) ^ ((2 : ℝ) / 3))) ^ 2 := by
    have hsq : ((n : ℝ) ^ ((2 : ℝ) / 3)) ^ 2 = (n : ℝ) ^ ((4 : ℝ) / 3) := by
      rw [← Real.rpow_natCast ((n : ℝ) ^ ((2 : ℝ) / 3)) 2, ← Real.rpow_mul hnpos.le]
      norm_num
    nlinarith
  unfold costNorm
  calc Real.sqrt (∑ p : Slot n L, slotCost n L p * slotCost n L p)
      ≤ Real.sqrt ((7 * (nodeConst * L * (n : ℝ) ^ ((2 : ℝ) / 3))) ^ 2) :=
        Real.sqrt_le_sqrt (le_trans hsum hbound)
    _ = 7 * (nodeConst * L * (n : ℝ) ^ ((2 : ℝ) / 3)) := by
        refine Real.sqrt_sq ?_
        have hnn : (0 : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hnpos.le _
        positivity

/-! ## The scan -/

/-- **The outer weighted scan.**  Every dyadic block problem is solved by the
node recursion of `LDS/NodeDual.lean`; the weighted scan takes their maximum at
cost `16 √(∑ c²)`, which `costNorm_slotCost_le` bounds.

The scan's value maps project each block's joint output `(descriptor, value)` to
its value.  That is legal because the projection happens *inside* the outer
function, not by recoding a child's dual. -/
theorem hasDualOn_ldsFun {L : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L) (hnL : n ≤ 2 ^ L)
    (hL2 : (2 : ℕ) ^ (L + 2) ≤ 8 * n) (read : X → Fin n → σ) :
    HasDualOn read (fun x => ldsFun (read x))
      (112 * (nodeConst * L * (n : ℝ) ^ ((2 : ℝ) / 3))) := by
  classical
  choose T hT using fun q : Σ s : Fin (L + 1), Fin (numBlocks n (s : ℕ)) =>
    hasDualOn_blockVal (X := X) (σ := σ) L hL hnL read (q.1 : ℕ) (q.2 : ℕ)
  have hg : ∀ p : Slot n L, HasDualOn read
      (fun x => p.elim ((0 : ℕ), (0 : ℕ))
        fun q => (T q x, blockVal (read x) (q.1 : ℕ) (q.2 : ℕ)))
      (slotCost n L p) := by
    intro p
    cases p with
    | none =>
        exact (hasDualOn_of_const read (f := fun _ : X => ((0 : ℕ), (0 : ℕ)))
          fun _ _ => rfl).mono (nodeCost_nonneg L 1)
    | some q => exact hT q
  have hmax := HasDualOn.maxMapFam (P := Slot n L) (V := ℕ × ℕ) (A := ℕ)
    (c := slotCost n L)
    (g := fun p x => p.elim ((0 : ℕ), (0 : ℕ))
      fun q => (T q x, blockVal (read x) (q.1 : ℕ) (q.2 : ℕ)))
    (slotCost_pos hL) (fun p v => p.elim 0 fun _ => v.2) hg
  refine (hmax.ofEq fun x => ?_).mono ?_
  · exact Eq.trans (congrArg maxFun (funext fun p => by cases p <;> rfl))
      (ldsFun_eq_maxFun_block (by omega : 0 < n) hnL (read x)).symm
  · have := costNorm_slotCost_le (n := n) (L := L) hn hL hL2
    linarith

/-! ## The headline bound -/

/-- **The longest distinct substring at cost `O(n^{2/3} L)`**, for any `L` with
`n ≤ 2 ^ L ≤ 2 n` — that is, for `L = ⌈log₂ n⌉`. -/
theorem advPM_ldsFun_le {L : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L) (hnL : n ≤ 2 ^ L)
    (hL2 : (2 : ℕ) ^ (L + 2) ≤ 8 * n) :
    advPM (fun α : Fin n → σ => ldsFun α)
      ≤ 112 * (nodeConst * L * (n : ℝ) ^ ((2 : ℝ) / 3)) := by
  have h := hasDualOn_ldsFun (X := (Fin n → σ)) hn hL hnL hL2 (fun α => α)
  have hnn : (0 : ℝ) ≤ 112 * (nodeConst * L * (n : ℝ) ^ ((2 : ℝ) / 3)) := by
    have : (0 : ℝ) < nodeConst := nodeConst_pos
    positivity
  have hid : advPM (fun α : Fin n → σ => ldsFun α)
      = advPMOn (fun α : Fin n → σ => α) (fun α => ldsFun α) := rfl
  rw [hid]
  exact advPMOn_le_of_hasDualOn hnn h

/-- The depth that works: `⌈log₂ n⌉`, kept at least `1`. -/
def ldsDepth (n : ℕ) : ℕ := max 1 (Nat.clog 2 n)

lemma le_two_pow_ldsDepth (n : ℕ) : n ≤ 2 ^ ldsDepth n := by
  refine le_trans (Nat.le_pow_clog (b := 2) (by norm_num) n) ?_
  exact Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)

lemma two_pow_ldsDepth_le (hn : 1 ≤ n) : (2 : ℕ) ^ (ldsDepth n + 2) ≤ 8 * n := by
  have hkey : (2 : ℕ) ^ ldsDepth n ≤ 2 * n := by
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      simp [ldsDepth, Nat.clog_of_right_le_one]
    · have hc : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by norm_num) h2
      have hmax : ldsDepth n = Nat.clog 2 n := max_eq_right hc
      have hlt : 2 ^ (Nat.clog 2 n - 1) < n := Nat.pow_pred_clog_lt_self (by norm_num) h2
      have hsucc : Nat.clog 2 n - 1 + 1 = Nat.clog 2 n := by omega
      calc (2 : ℕ) ^ ldsDepth n = 2 ^ (Nat.clog 2 n - 1 + 1) := by rw [hmax, hsucc]
        _ = 2 * 2 ^ (Nat.clog 2 n - 1) := by ring
        _ ≤ 2 * n := Nat.mul_le_mul_left _ hlt.le
  calc (2 : ℕ) ^ (ldsDepth n + 2) = 4 * 2 ^ ldsDepth n := by ring
    _ ≤ 4 * (2 * n) := Nat.mul_le_mul_left _ hkey
    _ = 8 * n := by ring

/-- **The headline bound.**  For every alphabet and every length,

    advPM (ldsFun) ≤ 112 · nodeConst · ⌈log₂ n⌉ · n^{2/3},

the `O(n^{2/3} log n)` of arXiv 2311.16401 Theorem 39 — with no `log log n`
factor, the weighted scan of `Promise/Max.lean` replacing the paper's
max-finding subroutine. -/
theorem advPM_ldsFun_le_clog (hn : 1 ≤ n) :
    advPM (fun α : Fin n → σ => ldsFun α)
      ≤ 112 * (nodeConst * (ldsDepth n : ℕ) * (n : ℝ) ^ ((2 : ℝ) / 3)) :=
  advPM_ldsFun_le hn (le_max_left _ _) (le_two_pow_ldsDepth n) (two_pow_ldsDepth_le hn)

/-- The same in terms of the real logarithm: `advPM (ldsFun) ≤ C · n^{2/3} ·
(1 + log₂ n)`.

The operational counterparts live in `Quantum/LDSApplications.lean`:
`lds_qQuery_sandwich` / `lds_qQuery_le_logb` (native transposition oracle)
and `lds_oneHotQQuery_sandwich` / `lds_oneHotQQuery_le_logb` (the canonical
one-hot XOR model), built on this file's `hasDualOn_ldsFun` certificate. -/
theorem advPM_ldsFun_le_logb (hn : 1 ≤ n) :
    advPM (fun α : Fin n → σ => ldsFun α)
      ≤ 112 * nodeConst * (1 + Real.logb 2 n) * (n : ℝ) ^ ((2 : ℝ) / 3) := by
  have hC : (0 : ℝ) < nodeConst := nodeConst_pos
  have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnn : (0 : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3) :=
    Real.rpow_nonneg (by linarith) _
  have hlog : (0 : ℝ) ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) hnr
  have hdep : ((ldsDepth n : ℕ) : ℝ) ≤ 1 + Real.logb 2 n := by
    have hpow : ((2 : ℝ)) ^ (ldsDepth n) ≤ 2 * (n : ℝ) := by
      have h := two_pow_ldsDepth_le hn
      have h2 : ((2 : ℕ) ^ ldsDepth n : ℝ) ≤ 2 * (n : ℝ) := by
        have h4 : (2 : ℕ) ^ ldsDepth n * 4 ≤ 8 * n := by
          have : (2 : ℕ) ^ (ldsDepth n + 2) = 2 ^ ldsDepth n * 4 := by ring
          omega
        have : ((2 : ℕ) ^ ldsDepth n : ℝ) * 4 ≤ 8 * (n : ℝ) := by exact_mod_cast h4
        linarith
      simpa using h2
    have hlb : Real.logb 2 (((2 : ℝ)) ^ (ldsDepth n)) ≤ Real.logb 2 (2 * (n : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) hpow
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hlb
    rw [Real.logb_mul (by norm_num) (by linarith),
      Real.logb_self_eq_one (by norm_num)] at hlb
    linarith
  have := advPM_ldsFun_le_clog (σ := σ) hn
  calc advPM (fun α : Fin n → σ => ldsFun α)
      ≤ 112 * (nodeConst * (ldsDepth n : ℕ) * (n : ℝ) ^ ((2 : ℝ) / 3)) := this
    _ ≤ 112 * nodeConst * (1 + Real.logb 2 n) * (n : ℝ) ^ ((2 : ℝ) / 3) := by
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdep hC.le) hnn
        nlinarith

end QuantumQueryComplexity
