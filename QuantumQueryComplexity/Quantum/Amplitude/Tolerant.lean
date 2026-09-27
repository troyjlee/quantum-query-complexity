import QuantumQueryComplexity.Quantum.Amplitude.Recursive
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The tolerant protocol: unknown overlap, one preparation

When only a lower bound `ε` on the marked mass is known, the scales `j = 0, 1, …, K` must all
be tried.  Preparing the start state afresh at every scale would charge the setup `K + 1`
times.  Instead one prepared state is reused: after an unsuccessful check the *remaining*,
unmarked, **unnormalized** vector continues,

    ν 0 = (1 − Π) s,        ν (j+1) = (1 − Π) · M_j · ν j,       M_j = A_j R_{j+1} A_j†,

where `M_j` is an approximate reflection about the level state `ψ_j = A_j s`.  The `ψ_j` are
never prepared; they are *virtual*, and enter only through `M_j`.

* `qNormSq_contV_succ` — `‖ν (j+1)‖² + ‖Π M_j ν j‖² = ‖ν j‖²`: the success masses of the stages
  and the final remaining mass add up to `1 − m 0`; zero-probability branches need no care;
* `qNormSq_contV_le` — **one pass fails with probability at most `99/100`**: if `m 0 ≥ ε` and
  `⌈1/ε⌉ ≤ 9^K` then `‖ν (K+1)‖² ≤ 99/100`.

The proof is first order.  Let `j*` be the first level with `m ≥ 1/100`.  Below it the
amplitudes grow by at least `2.9` per level, so by geometric sums (kept as invariants):
`‖ψ_j − s‖ ≤ 3.1·√m_{j−1}`, and the part of `ν j` orthogonal to `ν 0` has norm at most
`3.3·√m_{j−1} + ∑β`.  At `j*` either the remaining mass is already below `99/100`, or
`|⟨ψ, ν⟩| ≥ 0.52` and the stage succeeds with mass `(2·0.52·√m − β)² ≥ 1/100`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H O : Type} [Fintype H] [DecidableEq H]

section Generic

variable (rd : H → O) (G : O → Prop) [DecidablePred G]

lemma qNormSq_good_add_bad (χ : H → ℂ) :
    qNormSq (goodPart rd G χ) + qNormSq (badPart rd G χ) = qNormSq χ := by
  have h := qNormSq_add (goodPart rd G χ) (badPart rd G χ)
  rw [goodPart_add_badPart, qInner_goodPart_badPart] at h
  simp only [Complex.zero_re, mul_zero, add_zero] at h
  exact h.symm

lemma qInner_goodPart_right (ψ φ : H → ℂ) :
    qInner ψ (goodPart rd G φ) = qInner (goodPart rd G ψ) (goodPart rd G φ) := by
  rw [qInner_def, qInner_def]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [goodPart_apply, goodPart_apply]
  split_ifs <;> simp

end Generic

/-- For unit vectors, `‖ψ − s‖² = 2 − 2·Re⟨ψ, s⟩`. -/
lemma qNormSq_sub_of_units {ψ s : H → ℂ} (hψ : IsQState ψ) (hs : IsQState s) :
    qNormSq (ψ - s) = 2 - 2 * (qInner ψ s).re := by
  have h : ψ - s = ψ + (-1 : ℂ) • s := by rw [neg_one_smul, sub_eq_add_neg]
  rw [h, qNormSq_add, qNormSq_smul, hψ, hs, qInner_smul_right]
  simp
  ring

/-- The component orthogonal to `u`. -/
noncomputable def orthTo (u v : H → ℂ) : H → ℂ := v - qInner u v • u

lemma orthTo_add (u v w : H → ℂ) : orthTo u (v + w) = orthTo u v + orthTo u w := by
  rw [orthTo, orthTo, orthTo, qInner_add_right, add_smul]; abel

lemma orthTo_sub (u v w : H → ℂ) : orthTo u (v - w) = orthTo u v - orthTo u w := by
  rw [orthTo, orthTo, orthTo, qInner_sub_right, sub_smul]; abel

lemma orthTo_smul (u : H → ℂ) (c : ℂ) (v : H → ℂ) : orthTo u (c • v) = c • orthTo u v := by
  rw [orthTo, orthTo, qInner_smul_right, smul_sub, smul_smul]

lemma orthTo_smul_self {u : H → ℂ} (hu : IsQState u) (c : ℂ) : orthTo u (c • u) = 0 := by
  rw [orthTo, qInner_smul_right, qInner_self, hu]
  simp

lemma qNorm_orthTo_le {u : H → ℂ} (hu : IsQState u) (v : H → ℂ) : qNorm (orthTo u v) ≤ qNorm v :=
  qNorm_sub_proj_le hu v

variable {rd : H → O} {G : O → Prop} [DecidablePred G] {s : H → ℂ} {S : Matrix H H ℂ}
  {R : ℕ → Matrix H H ℂ} {β : ℕ → ℝ} {Dom : ℕ → Set (H → ℂ)}

/-- **The continuing vector** of the tolerant protocol. -/
noncomputable def contV (rd : H → O) (G : O → Prop) [DecidablePred G] (s : H → ℂ)
    (S : Matrix H H ℂ) (R : ℕ → Matrix H H ℂ) : ℕ → (H → ℂ)
  | 0 => badPart rd G s
  | j + 1 => badPart rd G (chainM S R j *ᵥ contV rd G s S R j)

namespace ChainOK

variable (h : ChainOK rd G s S R β Dom)

include h

local notation "ν" => contV rd G s S R

lemma goodPart_contV (j : ℕ) : goodPart rd G (ν j) = 0 := by
  cases j <;> exact goodPart_badPart rd G _

/-- **Mass conservation**: success of the stage plus the remaining mass. -/
theorem qNormSq_contV_succ (j : ℕ) :
    qNormSq (ν (j + 1)) + qNormSq (goodPart rd G (chainM S R j *ᵥ ν j)) = qNormSq (ν j) := by
  have h1 := qNormSq_good_add_bad rd G (chainM S R j *ᵥ ν j)
  rw [qNormSq_mulVec (chainM_mem_unitaryGroup h.S_unitary h.R_unitary j)] at h1
  show qNormSq (badPart rd G (chainM S R j *ᵥ ν j)) + _ = _
  linarith

lemma qNormSq_contV_zero : qNormSq (ν 0) = 1 - h.m 0 := by
  have : h.ψ 0 = s := Matrix.one_mulVec s
  rw [ChainOK.m, this]
  exact qNormSq_badPart_eq h.unit

lemma qNormSq_contV_antitone {i j : ℕ} (hij : i ≤ j) : qNormSq (ν j) ≤ qNormSq (ν i) := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
      have := h.qNormSq_contV_succ j
      have hnn := qNormSq_nonneg (goodPart rd G (chainM S R j *ᵥ ν j))
      linarith

lemma qNormSq_contV_le_one (j : ℕ) : qNormSq (ν j) ≤ 1 := by
  have := h.qNormSq_contV_antitone (Nat.zero_le j)
  rw [h.qNormSq_contV_zero] at this
  linarith [h.m_nonneg 0]

lemma qNorm_contV_le_one (j : ℕ) : qNorm (ν j) ≤ 1 :=
  qNorm_le_of_qNormSq_le zero_le_one (by rw [one_pow]; exact h.qNormSq_contV_le_one j)

/-- The previous amplitude, `0` at level `0`. -/
noncomputable def prevx (_ : ChainOK rd G s S R β Dom) : ℕ → ℝ
  | 0 => 0
  | j + 1 => Real.sqrt (goodProb rd G (chainA S R j *ᵥ s))

lemma prevx_nonneg (j : ℕ) : 0 ≤ h.prevx j := by
  cases j
  · exact le_rfl
  · exact Real.sqrt_nonneg _

lemma β_le_small (j : ℕ) : β (j + 1) ≤ 1 / 512 := by
  refine (h.β_le (j + 1)).trans ?_
  calc (1 / 2 : ℝ) ^ (j + 1 + 8) ≤ (1 / 2) ^ 9 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ = 1 / 512 := by norm_num

/-- Below the threshold the amplitude grows by at least `2.9`. -/
lemma prevx_growth (j : ℕ) (hlt : ∀ i < j, h.m i < 1 / 100) :
    29 / 10 * h.prevx j ≤ Real.sqrt (h.m j) := by
  cases j with
  | zero => simp only [prevx, mul_zero]; exact Real.sqrt_nonneg _
  | succ j =>
      have hm := hlt j (Nat.lt_succ_self j)
      have h1 := h.le_sqrt_m_succ j (by linarith)
      have hβ := h.β_le_small j
      have hx : 0 ≤ Real.sqrt (h.m j) := Real.sqrt_nonneg _
      show 29 / 10 * Real.sqrt (h.m j) ≤ _
      nlinarith

variable (hν : ∀ j, (chainA S R j)ᴴ *ᵥ contV rd G s S R j ∈ Dom j)

include hν

/-- The continuing vector of a stage, up to the reflection error. -/
lemma qNorm_contV_succ_sub_le (j : ℕ) :
    qNorm (ν (j + 1) - ((2 * qInner (h.ψ j) (ν j)) • badPart rd G (h.ψ j) - ν j))
      ≤ β (j + 1) := by
  have h1 := qNorm_badPart_stage_sub_le (h.isQState_ψ j) (h.isApproxRefl_chainM j)
    (h.β_nonneg _) (hν j) (h.goodPart_contV j)
  exact h1.trans (by
    have := mul_le_mul_of_nonneg_left (h.qNorm_contV_le_one j) (h.β_nonneg (j + 1))
    linarith)

/-- The unit vector along `ν 0`. -/
noncomputable def refV (_ : ChainOK rd G s S R β Dom) : H → ℂ :=
  (((Real.sqrt (1 - goodProb rd G s))⁻¹ : ℝ) : ℂ) • ν 0

omit hν in
lemma m_zero : h.m 0 = goodProb rd G s := by
  rw [ChainOK.m, ChainOK.ψ, chainA, Matrix.one_mulVec]

omit hν in
lemma isQState_refV (hm0 : h.m 0 < 1) : IsQState h.refV := by
  have hpos : 0 < 1 - goodProb rd G s := by rw [← h.m_zero]; linarith
  have h0 := h.qNormSq_contV_zero
  rw [h.m_zero] at h0
  rw [IsQState, refV, qNormSq_smul, h0, Complex.normSq_ofReal, ← mul_inv,
    Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

omit hν in
lemma orthTo_refV_contV_zero (hm0 : h.m 0 < 1) : orthTo h.refV (ν 0) = 0 := by
  have hpos : 0 < 1 - goodProb rd G s := by rw [← h.m_zero]; linarith
  have hne : Real.sqrt (1 - goodProb rd G s) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have : ν 0 = ((Real.sqrt (1 - goodProb rd G s) : ℝ) : ℂ) • h.refV := by
    rw [refV, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hne, Complex.ofReal_one, one_smul]
  rw [this]
  exact orthTo_smul_self (h.isQState_refV hm0) _

/-- **The first-order invariants** below the threshold. -/
theorem invariants (hm0 : h.m 0 < 1) (j : ℕ) (hlt : ∀ i < j, h.m i < 1 / 100) :
    qNorm (h.ψ j - s) ≤ 31 / 10 * h.prevx j
    ∧ qNorm (orthTo h.refV (ν j)) ≤ 33 / 10 * h.prevx j + ((1 / 2) ^ 8 - (1 / 2) ^ (j + 8)) := by
  induction j with
  | zero =>
      have h0 : h.ψ 0 = s := Matrix.one_mulVec s
      refine ⟨?_, ?_⟩
      · rw [h0, sub_self, qNorm_zero]; simp [prevx]
      · rw [h.orthTo_refV_contV_zero hm0, qNorm_zero]; simp [prevx]
  | succ j ih =>
      have hlt' : ∀ i < j, h.m i < 1 / 100 := fun i hi => hlt i (by omega)
      obtain ⟨ih1, ih2⟩ := ih hlt'
      have hg := h.prevx_growth j hlt'
      have hp0 := h.prevx_nonneg j
      have hx0 : 0 ≤ Real.sqrt (h.m j) := Real.sqrt_nonneg _
      have hβ := h.β_le_small j
      have hβ0 := h.β_nonneg (j + 1)
      have hprev : h.prevx (j + 1) = Real.sqrt (h.m j) := rfl
      have hu := h.isQState_refV hm0
      rw [hprev]
      constructor
      · have hsplit : h.ψ (j + 1) - s = (h.ψ (j + 1) - h.ψ j) + (h.ψ j - s) := by abel
        rw [hsplit]
        refine (qNorm_add_le _ _).trans ?_
        have h1 := h.qNorm_ψ_succ_sub_le j
        have h2 := mul_le_mul_of_nonneg_right hβ hx0
        nlinarith
      · set w := (2 * qInner (h.ψ j) (ν j)) • badPart rd G (h.ψ j) - ν j with hw
        have he := h.qNorm_contV_succ_sub_le hν j
        have hsplit : orthTo h.refV (ν (j + 1))
            = orthTo h.refV (ν (j + 1) - w)
              + ((2 * qInner (h.ψ j) (ν j)) • orthTo h.refV (badPart rd G (h.ψ j))
                - orthTo h.refV (ν j)) := by
          rw [← orthTo_smul, ← orthTo_sub, ← orthTo_add, ← hw, sub_add_cancel]
        have hb : qNorm (orthTo h.refV (badPart rd G (h.ψ j))) ≤ 31 / 10 * h.prevx j := by
          have h1 : orthTo h.refV (badPart rd G (h.ψ j))
              = orthTo h.refV (badPart rd G (h.ψ j - s)) := by
            rw [badPart_sub, orthTo_sub]
            have : orthTo h.refV (badPart rd G s) = 0 := h.orthTo_refV_contV_zero hm0
            rw [this, sub_zero]
          rw [h1]
          exact ((qNorm_orthTo_le hu _).trans (qNorm_badPart_le rd G _)).trans ih1
        have hin : ‖qInner (h.ψ j) (ν j)‖ ≤ 1 := by
          refine (norm_qInner_le _ _).trans ?_
          rw [qNorm_eq_one (h.isQState_ψ j), one_mul]
          exact h.qNorm_contV_le_one j
        have h1 : qNorm ((2 * qInner (h.ψ j) (ν j)) • orthTo h.refV (badPart rd G (h.ψ j)))
            ≤ 2 * (31 / 10 * h.prevx j) := by
          rw [qNorm_smul, norm_mul, Complex.norm_ofNat]
          have := mul_le_mul hin hb (qNorm_nonneg _) zero_le_one
          nlinarith [qNorm_nonneg (orthTo h.refV (badPart rd G (h.ψ j))), norm_nonneg
            (qInner (h.ψ j) (ν j))]
        rw [hsplit]
        refine (qNorm_add_le _ _).trans ?_
        have h2 := qNorm_sub_le ((2 * qInner (h.ψ j) (ν j)) • orthTo h.refV (badPart rd G (h.ψ j)))
          (orthTo h.refV (ν j))
        have h3 := (qNorm_orthTo_le hu (ν (j + 1) - w)).trans he
        have hβ' := h.β_le (j + 1)
        have e1 : (1 / 2 : ℝ) ^ (j + 8) = 2 * (1 / 2) ^ (j + 1 + 8) := by
          rw [show j + 1 + 8 = (j + 8) + 1 from by ring, pow_succ]; ring
        nlinarith

omit h hν in
/-- The numerical core of the final stage. -/
lemma stage_num {x xp x0 d r g o b : ℝ} (hx : 1 / 10 ≤ x) (hxu : x ≤ (3 + 2 * b) * xp)
    (hxp0 : 0 ≤ xp) (hxp : xp < 1 / 10) (hx00 : 0 ≤ x0) (hx0 : x0 < 1 / 10) (hd0 : 0 ≤ d)
    (hd : d ≤ 31 / 10 * xp) (hr0 : 0 ≤ r) (hr : r ≤ 33 / 10 * xp + 1 / 256) (hg0 : 0 ≤ g)
    (hg : 99 / 100 - r ^ 2 ≤ g ^ 2) (ho : 1 - d ^ 2 / 2 - x * x0 ≤ o) (hb0 : 0 ≤ b)
    (hb : b ≤ 1 / 512) : 1 / 10 ≤ 2 * (g * o - r) * x - b := by
  have hr' : r ≤ 33391 / 100000 := by linarith
  have hd' : d ≤ 31 / 100 := by linarith
  have hd2 : d ^ 2 ≤ (31 / 100) ^ 2 := pow_le_pow_left₀ hd0 hd' 2
  have hr2 : r ^ 2 ≤ (33391 / 100000) ^ 2 := pow_le_pow_left₀ hr0 hr' 2
  have hg' : 937 / 1000 ≤ g := by
    by_contra hcon
    push_neg at hcon
    have : g ^ 2 < (937 / 1000) ^ 2 := pow_lt_pow_left₀ hcon hg0 (by norm_num)
    norm_num at this hr2
    linarith
  have hxu' : x ≤ 3004 / 10000 := by nlinarith
  have hxx0 : x * x0 ≤ x * (1 / 10) := mul_le_mul_of_nonneg_left hx0.le (by linarith)
  have ho' : 95195 / 100000 - x / 10 ≤ o := by norm_num at hd2; linarith
  have ho0 : 0 ≤ 95195 / 100000 - x / 10 := by linarith
  have hgo : 937 / 1000 * (95195 / 100000 - x / 10) ≤ g * o := mul_le_mul hg' ho' ho0 hg0
  have hx0' : 0 ≤ x := by linarith
  have hmain : (937 / 1000 * (95195 / 100000 - x / 10) - 33391 / 100000) * x
      ≤ (g * o - r) * x := mul_le_mul_of_nonneg_right (by linarith) hx0'
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hxu')]

/-- **One pass of the tolerant protocol fails with probability at most `99/100`.** -/
theorem qNormSq_contV_le {ε : ℝ} (hε : 0 < ε) (hm0 : ε ≤ h.m 0) {K : ℕ}
    (hK : ⌈1 / ε⌉₊ ≤ 9 ^ K) : qNormSq (ν (K + 1)) ≤ 99 / 100 := by
  classical
  by_cases hbig : 1 / 100 ≤ h.m 0
  · have := h.qNormSq_contV_antitone (Nat.zero_le (K + 1))
    rw [h.qNormSq_contV_zero] at this
    linarith
  push_neg at hbig
  -- the first level above the threshold
  obtain ⟨n0, hn0K, hn0⟩ := h.exists_level hε hm0 hK
  have hex : ∃ n, 1 / 100 ≤ h.m n := ⟨n0, by linarith⟩
  set js := Nat.find hex with hjs
  have hjs_ge : 1 / 100 ≤ h.m js := Nat.find_spec hex
  have hjs_lt : ∀ i < js, h.m i < 1 / 100 := fun i hi => not_le.mp (Nat.find_min hex hi)
  have hjs_le : js ≤ K := (Nat.find_min' hex (by linarith : 1 / 100 ≤ h.m n0)).trans hn0K
  have hjs_pos : 0 < js := by
    rcases Nat.eq_zero_or_pos js with h0 | h0
    · rw [h0] at hjs_ge; linarith
    · exact h0
  obtain ⟨k, hk⟩ : ∃ k, js = k + 1 := ⟨js - 1, by omega⟩
  have hm01 : h.m 0 < 1 := by linarith
  obtain ⟨inv1, inv2⟩ := h.invariants hν hm01 js hjs_lt
  -- either the remaining mass is already small, or the stage succeeds
  by_cases hN : qNormSq (ν js) < 99 / 100
  · exact (h.qNormSq_contV_antitone (by omega : js ≤ K + 1)).trans hN.le
  push_neg at hN
  have hu := h.isQState_refV hm01
  have hψ := h.isQState_ψ js
  set x := Real.sqrt (h.m js) with hx
  have hxp_def : h.prevx js = Real.sqrt (h.m k) := by rw [hk]; rfl
  have hmk : h.m k < 1 / 100 := hjs_lt k (by omega)
  have hxp : h.prevx js < 1 / 10 := by
    rw [hxp_def, show (1 / 10 : ℝ) = Real.sqrt (1 / 100) by
      rw [show (1 / 100 : ℝ) = (1 / 10) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (h.m_nonneg k) hmk
  have hx_ge : 1 / 10 ≤ x := by
    rw [hx, show (1 / 10 : ℝ) = Real.sqrt (1 / 100) by
      rw [show (1 / 100 : ℝ) = (1 / 10) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hjs_ge
  have hx_up : x ≤ (3 + 2 * β js) * h.prevx js := by
    rw [hx, hxp_def, hk]; exact h.sqrt_m_succ_le k
  have hx0 : Real.sqrt (h.m 0) < 1 / 10 := by
    rw [show (1 / 10 : ℝ) = Real.sqrt (1 / 100) by
      rw [show (1 / 100 : ℝ) = (1 / 10) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (h.m_nonneg 0) hbig
  -- the overlap with the reference direction
  have hRe : 1 - qNorm (h.ψ js - s) ^ 2 / 2 = (qInner (h.ψ js) s).re := by
    rw [qNorm_sq, qNormSq_sub_of_units hψ h.unit]; ring
  have hν0 : ν 0 = s - goodPart rd G s := by
    have := goodPart_add_badPart rd G s
    exact eq_sub_of_add_eq' this
  have hg0 : ‖qInner (h.ψ js) (goodPart rd G s)‖ ≤ x * Real.sqrt (h.m 0) := by
    rw [qInner_goodPart_right]
    refine (norm_qInner_le _ _).trans (le_of_eq ?_)
    rw [qNorm_goodPart_eq, qNorm_goodPart_eq, h.m_zero]
    rfl
  have ho1 : 1 - qNorm (h.ψ js - s) ^ 2 / 2 - x * Real.sqrt (h.m 0)
      ≤ ‖qInner (h.ψ js) (ν 0)‖ := by
    rw [hν0, qInner_sub_right, hRe]
    have h1 := norm_sub_norm_le (qInner (h.ψ js) s) (qInner (h.ψ js) (goodPart rd G s))
    have h2 := Complex.re_le_norm (qInner (h.ψ js) s)
    linarith
  have ho : 1 - qNorm (h.ψ js - s) ^ 2 / 2 - x * Real.sqrt (h.m 0)
      ≤ ‖qInner (h.ψ js) h.refV‖ := by
    refine ho1.trans ?_
    have hpos : 0 < 1 - goodProb rd G s := by rw [← h.m_zero]; linarith
    have hle : Real.sqrt (1 - goodProb rd G s) ≤ 1 :=
      (Real.sqrt_le_sqrt (by linarith [goodProb_nonneg rd G s])).trans (le_of_eq Real.sqrt_one)
    have hsp := Real.sqrt_pos.mpr hpos
    rw [refV, qInner_smul_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hsp.le)]
    have hinv : 1 ≤ (Real.sqrt (1 - goodProb rd G s))⁻¹ := (one_le_inv₀ hsp).mpr hle
    nlinarith [norm_nonneg (qInner (h.ψ js) (ν 0))]
  -- decompose `ν js` along the reference direction
  set γ := qInner h.refV (ν js) with hγ
  have hdec : ν js = γ • h.refV + orthTo h.refV (ν js) := by rw [orthTo]; abel
  have hgsq : 99 / 100 - qNorm (orthTo h.refV (ν js)) ^ 2 ≤ ‖γ‖ ^ 2 := by
    have := qNormSq_sub_proj hu (ν js)
    rw [qNorm_sq, ← Complex.normSq_eq_norm_sq]
    change _ ≤ Complex.normSq (qInner h.refV (ν js))
    have h2 : qNormSq (orthTo h.refV (ν js)) = qNormSq (ν js)
        - Complex.normSq (qInner h.refV (ν js)) := this
    linarith
  have hin : ‖γ‖ * ‖qInner (h.ψ js) h.refV‖ - qNorm (orthTo h.refV (ν js))
      ≤ ‖qInner (h.ψ js) (ν js)‖ := by
    have h1 : qInner (h.ψ js) (ν js)
        = γ * qInner (h.ψ js) h.refV + qInner (h.ψ js) (orthTo h.refV (ν js)) := by
      conv_lhs => rw [hdec]
      rw [qInner_add_right, qInner_smul_right]
    have h2 : ‖qInner (h.ψ js) (orthTo h.refV (ν js))‖ ≤ qNorm (orthTo h.refV (ν js)) := by
      refine (norm_qInner_le _ _).trans ?_
      rw [qNorm_eq_one hψ, one_mul]
    have h3 := norm_sub_norm_le (γ * qInner (h.ψ js) h.refV)
      (-qInner (h.ψ js) (orthTo h.refV (ν js)))
    rw [sub_neg_eq_add, ← h1, norm_neg, norm_mul] at h3
    linarith
  have hb512 : β js ≤ 1 / 512 := by rw [hk]; exact h.β_le_small k
  have hx_up' : x ≤ (3 + 2 * (1 / 512)) * h.prevx js :=
    hx_up.trans (mul_le_mul_of_nonneg_right (by linarith) (h.prevx_nonneg js))
  have hnum := stage_num hx_ge hx_up' (h.prevx_nonneg js) hxp (Real.sqrt_nonneg _) hx0
    (qNorm_nonneg _) inv1 (qNorm_nonneg _)
    (inv2.trans (by
      have : (0 : ℝ) < (1 / 2) ^ (js + 8) := by positivity
      have e : (1 / 2 : ℝ) ^ 8 = 1 / 256 := by norm_num
      rw [e]
      linarith))
    (norm_nonneg γ) hgsq ho (by norm_num) le_rfl
  -- the stage succeeds with mass at least `1/100`
  have hstage := le_qNorm_goodPart_stage hψ (h.isApproxRefl_chainM js) (h.β_nonneg _) (hν js)
    (h.goodPart_contV js)
  have hβmono : β (js + 1) * qNorm (ν js) ≤ 1 / 512 := by
    have := mul_le_mul (h.β_le_small js) (h.qNorm_contV_le_one js) (qNorm_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1 / 512)
    linarith
  have hbig2 : 1 / 10 ≤ qNorm (goodPart rd G (chainM S R js *ᵥ ν js)) := by
    have hx' : 0 ≤ x := Real.sqrt_nonneg _
    have := mul_le_mul_of_nonneg_right hin hx'
    have hx2 : Real.sqrt (goodProb rd G (h.ψ js)) = x := rfl
    rw [hx2] at hstage
    linarith
  have hσ : 1 / 100 ≤ qNormSq (goodPart rd G (chainM S R js *ᵥ ν js)) := by
    rw [← qNorm_sq]
    nlinarith [qNorm_nonneg (goodPart rd G (chainM S R js *ᵥ ν js))]
  have hcons := h.qNormSq_contV_succ js
  have hone := h.qNormSq_contV_le_one js
  exact (h.qNormSq_contV_antitone (by omega : js + 1 ≤ K + 1)).trans (by linarith)

end ChainOK

end QuantumQueryComplexity
