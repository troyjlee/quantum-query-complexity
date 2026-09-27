import QuantumQueryComplexity.Quantum.Amplitude.TolerantPass
import QuantumQueryComplexity.Quantum.FirstOf
set_option synthInstance.maxSize 3200
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Search with an approximate reflection about the start state

The compiled approximate-reflection search algorithm: `110` independent
tolerant passes, first recorded vertex (`OTrial.firstOf`).  The caller supplies a preparation
routine (`S` queries), an exact marker (`C`), a sequence of reflection routines (`r j`) with
their cleanliness flags, and the vertex readout; and proves the support contract `SearchInv`
for the inputs of interest.

* `approxSearch_q` — the budget is `110 · passLen S C r (K+1)`: the setup is charged `110`
  times, **whatever the number of scales**;
* `approxSearch_pr_unmarked` — an unmarked vertex is returned with probability `0`;
* `two_thirds_le_approxSearch` — if the marked mass is at least `ε` and `⌈1/ε⌉ ≤ 9^K`, a marked
  vertex is returned with probability at least `1 − (99/100)^110 ≥ 2/3`;
* `approxSearch_pr_none_of_empty` — with no marked vertex, `none` is returned surely;
* `four_mul_chainLen_le`, `passLen_le` — with `r j ≤ ρ·(j + 9)` (cost of a reflection of
  precision `2^{-(j+8)}`): `4·q_j + 2C + ρ(2j+21) ≤ 3^j·(2C + 21ρ)` and
  `passLen S C r (K+1) ≤ S + C + 2·3^{K+2}·(2C + 21ρ)`: **no logarithmic factor**.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W V : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]

variable (prep : QRoutine ι σ W) (init : QBasis ι σ W → ℂ) (hinit : IsQState init)
  (mark : QRoutine ι σ W) (refl : ℕ → QRoutine ι σ W) (clean : ℕ → QBasis ι σ W → Bool)
  (vtx : QBasis ι σ W → V)

/-- **One tolerant pass**, as a trial. -/
noncomputable def passTrial (K : ℕ) : OTrial ι σ V where
  W := Slots (K + 2) V × CtrlWork ι W
  alg := (passR prep mark refl clean vtx K).toAlg
    (embedReg (emptySlots (K + 2) V) (embedCtrl false init))
    (by rw [IsQState, qNormSq_embedReg]; exact isQState_embedCtrl false hinit)
    (slotReadout ι σ W (K + 2) V)
  q := passLen prep.len mark.len (fun l => (refl l).len) (K + 1)

/-- **The search algorithm**: `110` passes, first recorded vertex. -/
noncomputable def approxSearch (K : ℕ) : OTrial ι σ V :=
  OTrial.firstOf (List.replicate 110 (passTrial prep init hinit mark refl clean vtx K))

theorem approxSearch_q (K : ℕ) :
    (approxSearch prep init hinit mark refl clean vtx K).q
      = 110 * passLen prep.len mark.len (fun l => (refl l).len) (K + 1) := by
  rw [approxSearch, OTrial.firstOf_q, List.map_replicate, List.sum_replicate, smul_eq_mul]
  rfl

variable {prep init hinit mark refl clean vtx} {Marked : V → Prop} [DecidablePred Marked]
  {a : ι → σ} {β : ℕ → ℝ} {F : ℕ → Set (QBasis ι σ W)}
  (h : SearchInv vtx Marked mark refl clean a (prep.run a *ᵥ init) β F)

include h

local notation "νv" => contV vtx Marked (prep.run a *ᵥ init) (mark.run a) (cleanOps refl clean a)

lemma passTrial_pr (K : ℕ) (o : Option V) :
    ∃ Ξ, SuppIn (foundBelow ι σ W (K + 2) Marked (K + 2)) Ξ
      ∧ (passTrial prep init hinit mark refl clean vtx K).pr a o
        = qProb (slotReadout ι σ W (K + 2) V)
            (embedReg (emptySlots (K + 2) V) (embedCtrl false (νv (K + 1))) + Ξ) o := by
  obtain ⟨Ξ, hΞ, hrun⟩ := h.passUpTo_run (N := K + 2) rfl (K + 1) (Nat.lt_succ_self _)
  refine ⟨Ξ, hΞ, ?_⟩
  have hstate : (passTrial prep init hinit mark refl clean vtx K).alg.state a
      (passTrial prep init hinit mark refl clean vtx K).q
      = embedReg (emptySlots (K + 2) V) (embedCtrl false (νv (K + 1))) + Ξ := by
    rw [← hrun]
    have hq : (passTrial prep init hinit mark refl clean vtx K).q
        = (passR prep mark refl clean vtx K).len := (passR_len prep mark refl clean vtx K).symm
    rw [hq]
    exact QRoutine.toAlg_state_len _ _ _ _ a
  show qProb _ ((passTrial prep init hinit mark refl clean vtx K).alg.state a _) o = _
  rw [hstate]
  rfl

theorem passTrial_pr_none (K : ℕ) :
    (passTrial prep init hinit mark refl clean vtx K).pr a none = qNormSq (νv (K + 1)) := by
  obtain ⟨Ξ, hΞ, hpr⟩ := passTrial_pr (hinit := hinit) h K none
  rw [hpr, qProb_slotReadout_none hΞ]

theorem passTrial_pr_unmarked (K : ℕ) {v : V} (hv : ¬ Marked v) :
    (passTrial prep init hinit mark refl clean vtx K).pr a (some v) = 0 := by
  obtain ⟨Ξ, hΞ, hpr⟩ := passTrial_pr (hinit := hinit) h K (some v)
  rw [hpr, qProb_slotReadout_unmarked hΞ hv]

lemma passTrial_bad (K : ℕ) :
    (passTrial prep init hinit mark refl clean vtx K).bad Marked a = 0 :=
  Finset.sum_eq_zero fun v _ => by
    by_cases hv : Marked v
    · rw [if_pos hv]
    · rw [if_neg hv, passTrial_pr_unmarked h K hv]

lemma approxSearch_bad (K : ℕ) :
    (approxSearch prep init hinit mark refl clean vtx K).bad Marked a = 0 := by
  refine le_antisymm ?_ (OTrial.bad_nonneg _ _ _)
  refine (OTrial.bad_firstOf_le Marked _ a).trans (le_of_eq ?_)
  rw [List.map_replicate, List.sum_replicate, passTrial_bad h, smul_zero]

/-- **An unmarked vertex is never returned.** -/
theorem approxSearch_pr_unmarked (K : ℕ) {v : V} (hv : ¬ Marked v) :
    (approxSearch prep init hinit mark refl clean vtx K).pr a (some v) = 0 := by
  have h0 := approxSearch_bad (hinit := hinit) h K
  rw [OTrial.bad, Finset.sum_eq_zero_iff_of_nonneg (fun v _ => by
    split_ifs <;> [exact le_rfl; exact OTrial.pr_nonneg _ _ _])] at h0
  have := h0 v (Finset.mem_univ v)
  rwa [if_neg hv] at this

lemma approxSearch_pr_none (K : ℕ) :
    (approxSearch prep init hinit mark refl clean vtx K).pr a none
      = qNormSq (νv (K + 1)) ^ 110 := by
  rw [approxSearch, OTrial.pr_firstOf_none, List.map_replicate, List.prod_replicate,
    passTrial_pr_none h]

/-- **A marked vertex is found with probability at least `2/3`.** -/
theorem two_thirds_le_approxSearch {ε : ℝ} (hε : 0 < ε)
    (hm0 : ε ≤ goodProb vtx Marked (prep.run a *ᵥ init)) {K : ℕ} (hK : ⌈1 / ε⌉₊ ≤ 9 ^ K) :
    2 / 3 ≤ (approxSearch prep init hinit mark refl clean vtx K).good Marked a := by
  rw [OTrial.good_eq, approxSearch_bad h, approxSearch_pr_none h]
  have hfail := h.pass_fail_le hε hm0 hK
  have h0 := qNormSq_nonneg (νv (K + 1))
  have hpow : qNormSq (νv (K + 1)) ^ 110 ≤ (99 / 100 : ℝ) ^ 110 := pow_le_pow_left₀ h0 hfail 110
  have hnum : (99 / 100 : ℝ) ^ 110 ≤ 1 / 3 := by norm_num
  linarith

/-- **With no marked vertex, `none` is returned surely.** -/
theorem approxSearch_pr_none_of_empty (hno : ∀ v, ¬ Marked v) (K : ℕ) :
    (approxSearch prep init hinit mark refl clean vtx K).pr a none = 1 := by
  have hgood : ∀ χ : QBasis ι σ W → ℂ, goodPart vtx Marked χ = 0 := fun χ => by
    funext q; rw [goodPart_apply, if_neg (hno _)]; rfl
  have hnorm : ∀ j, qNormSq (νv j) = 1 := by
    intro j
    induction j with
    | zero =>
        rw [h.chainOK.qNormSq_contV_zero, h.chainOK.m_zero, ← qNormSq_goodPart, hgood]
        simp [qNormSq_def]
    | succ j ih =>
        have := h.chainOK.qNormSq_contV_succ j
        rw [hgood, ih] at this
        simp only [qNormSq_def, Pi.zero_apply, map_zero, Finset.sum_const_zero, add_zero] at this
        rw [qNormSq_def]
        exact this
  rw [approxSearch_pr_none h, hnorm, one_pow]

omit h

/-! ## The budget -/

/-- `4·q_j + 2C + ρ(2j + 21) ≤ 3^j·(2C + 21ρ)`. -/
theorem four_mul_chainLen_le {C ρ : ℕ} {r : ℕ → ℕ} (hr : ∀ j, r j ≤ ρ * (j + 9)) (j : ℕ) :
    4 * chainLen C r j + 2 * C + ρ * (2 * j + 21) ≤ 3 ^ j * (2 * C + 21 * ρ) := by
  induction j with
  | zero => simp [chainLen]; ring_nf; exact le_rfl
  | succ j ih =>
      have := hr (j + 1)
      rw [chainLen, pow_succ]
      nlinarith

/-- **The cost of a pass**: one setup, and `O(3^K·(C + ρ))`. -/
theorem passLen_le {S C ρ : ℕ} {r : ℕ → ℕ} (hr : ∀ j, r j ≤ ρ * (j + 9)) (K : ℕ) :
    passLen S C r K + 2 * (2 * C + 21 * ρ) ≤ S + C + 2 * 3 ^ (K + 1) * (2 * C + 21 * ρ) := by
  induction K with
  | zero => simp [passLen]; nlinarith
  | succ K ih =>
      have h1 := four_mul_chainLen_le (C := C) hr (K + 1)
      have h2 : 2 * chainLen C r K + r (K + 1) + C ≤ chainLen C r (K + 1) := by
        rw [chainLen]; omega
      rw [passLen, pow_succ 3 (K + 1)]
      nlinarith

end QuantumQueryComplexity
