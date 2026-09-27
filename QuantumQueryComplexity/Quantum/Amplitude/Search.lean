import QuantumQueryComplexity.Quantum.Amplitude.Amplification
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 1000000
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Search by amplitude amplification

The input is `x : Fin n → Bool` (`n ≥ 1`), queried through the **native value oracle**; an
index `i` is *marked* when `x i = true`.

* Preparation: the uniform superposition over the index register is the input-independent
  initial vector; the preparation routine is the identity, `S = 0`.
* Marker: query, phase `−1` on answer `some true`, query again — `C = 2` native queries.  It
  is diagonal, with phase `−1` exactly on the clean basis states of marked indices.  (A
  one-query phase oracle belongs to a different oracle model; any conversion through
  `Simulation.lean` must be charged explicitly.)

`searchAlg n m` is the amplified algorithm, with output `Option (Fin n)` and budget
`searchBudget m = 8·m` (`= 4·((m−1)·2 + 2)`).  For every input:

* `searchAlg_prob_some_of_unmarked`: a returned index is **always** marked;
* `two_thirds_le_search_returnProb`: if at least `k ≥ 1` indices are marked and
  `m·√(k/n) ≥ 1`, an index is returned with probability `≥ 2/3`, without knowing the actual
  number of marked indices; with `m = ⌈√(n/k)⌉` the cost is at most `16·√(n/k)`;
* `searchAlg_prob_none_of_no_marked`: with no marked index, the output is `none` surely;
* `marked_mul_searchAlg_prob_some`: conditioned on returning an index, it is **exactly
  uniform** over the marked indices: `t · Pr[some i] = Pr[≠ none]` for every marked `i`.

`n = 0` is the zero-query constant algorithm (`search_zero`).
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

/-! ## A diagonal phase gate on the answer register -/

section Phase

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-- The phase `−1` on the answer `some s`. -/
noncomputable def ansPhase (s : σ) : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ :=
  Matrix.diagonal fun p => if p.2.1 = some s then -1 else 1

lemma ansPhase_mem_unitaryGroup (s : σ) :
    ansPhase (ι := ι) (W := W) s ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ansPhase,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext p
  simp only [Pi.star_apply]
  split_ifs <;> simp

/-- **The native phase marker for the answer `s`**: query, phase, query — two queries. -/
noncomputable def ansMarker (s : σ) : QRoutine ι σ W :=
  (QRoutine.query.comp (QRoutine.ofUnitary (ansPhase s) (ansPhase_mem_unitaryGroup s))).comp
    QRoutine.query

@[simp] lemma ansMarker_len (s : σ) : (ansMarker (ι := ι) (W := W) s).len = 2 := rfl

/-- The marker is diagonal: the phase of `p` is that of the queried state `oracleMap a p`. -/
theorem ansMarker_run_mulVec (s : σ) (a : ι → σ) (φ : QBasis ι σ W → ℂ) (p : QBasis ι σ W) :
    ((ansMarker s).run a *ᵥ φ) p
      = (if (oracleMap a p).2.1 = some s then -1 else 1) * φ p := by
  rw [ansMarker, QRoutine.comp_run, QRoutine.comp_run, QRoutine.query_run,
    QRoutine.ofUnitary_run, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    oracleMat_mulVec_apply, ansPhase, Matrix.mulVec_diagonal, oracleMat_mulVec_apply,
    oracleMap_involutive a p]

end Phase

/-! ## The search setup -/

variable {n : ℕ}

/-- The uniform superposition over the index register, answer register blank. -/
noncomputable def uniformIdx (n : ℕ) : QBasis (Fin n) Bool Unit → ℂ := fun p =>
  match p with
  | (some _, none, _) => (((Real.sqrt n)⁻¹ : ℝ) : ℂ)
  | _ => 0

/-- Sums against the uniform state: only the clean index states contribute, `1/n` each. -/
lemma sum_mul_normSq_uniformIdx (hn : 0 < n) (g : QBasis (Fin n) Bool Unit → ℝ) :
    ∑ p, g p * Complex.normSq (uniformIdx n p) = (∑ i : Fin n, g (some i, none, ())) / n := by
  have hc : Complex.normSq (((Real.sqrt n)⁻¹ : ℝ) : ℂ) = 1 / n := by
    rw [Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg n), one_div]
  rw [Fintype.sum_prod_type, Fintype.sum_option]
  simp only [Fintype.sum_prod_type, Fintype.sum_option, Fintype.sum_bool, Finset.univ_unique,
    Finset.sum_singleton, uniformIdx, map_zero, mul_zero, add_zero, zero_add, hc]
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma isQState_uniformIdx (hn : 0 < n) : IsQState (uniformIdx n) := by
  have h := sum_mul_normSq_uniformIdx hn (fun _ => 1)
  simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at h
  rw [IsQState, qNormSq_def, h]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- The index readout (the idle index reads as `0`; it carries no amplitude). -/
def idxReadout (hn : 0 < n) : QBasis (Fin n) Bool Unit → Fin n := fun p => p.1.getD ⟨0, hn⟩

/-- **The search setup**: `S = 0`, `C = 2`. -/
noncomputable def searchSetup (hn : 0 < n) : AmpSetup (Fin n) Bool Unit (Fin n) where
  prep := QRoutine.identity
  init := uniformIdx n
  init_isQState := isQState_uniformIdx hn
  mark := ansMarker true
  readout := idxReadout hn

/-- An index is marked when its bit is set. -/
abbrev Marked (x : Fin n → Bool) (i : Fin n) : Prop := x i = true

lemma searchSetup_prepared (hn : 0 < n) (a : Fin n → Bool) :
    (searchSetup hn).prepared a = uniformIdx n := by
  rw [AmpSetup.prepared]
  show (QRoutine.identity : QRoutine (Fin n) Bool Unit).run a *ᵥ uniformIdx n = _
  rw [QRoutine.identity_run, Matrix.one_mulVec]

/-- **The two-query native marker marks the uniform state.** -/
theorem searchSetup_marks (hn : 0 < n) :
    (searchSetup hn).Marks (id : (Fin n → Bool) → Fin n → Bool) Marked := by
  intro x
  beta_reduce
  simp only [id_eq, searchSetup_prepared]
  constructor
  · funext p
    show ((ansMarker true).run x *ᵥ _) p = _
    rw [ansMarker_run_mulVec, Pi.neg_apply, goodPart_apply]
    obtain ⟨k, t, w⟩ := p
    cases k with
    | none => simp [uniformIdx]
    | some i =>
        cases t with
        | none =>
            by_cases hx : x i = true
            · simp [show (searchSetup hn).readout ((some i, none, w) : QBasis (Fin n) Bool Unit) = i from rfl, Marked, hx]
            · simp [show (searchSetup hn).readout ((some i, none, w) : QBasis (Fin n) Bool Unit) = i from rfl, Marked, hx]
        | some b => simp [uniformIdx]
  · funext p
    show ((ansMarker true).run x *ᵥ _) p = _
    rw [ansMarker_run_mulVec, badPart_apply]
    obtain ⟨k, t, w⟩ := p
    cases k with
    | none => simp [uniformIdx]
    | some i =>
        cases t with
        | none =>
            by_cases hx : x i = true
            · simp [show (searchSetup hn).readout ((some i, none, w) : QBasis (Fin n) Bool Unit) = i from rfl, Marked, hx]
            · simp [show (searchSetup hn).readout ((some i, none, w) : QBasis (Fin n) Bool Unit) = i from rfl, Marked, hx]
        | some b => simp [uniformIdx]

/-- The number of marked indices. -/
def markedCount (x : Fin n → Bool) : ℕ := (Finset.univ.filter fun i => x i = true).card

/-- **The original success probability is `t/n`.** -/
theorem searchSetup_succProb (hn : 0 < n) (x : Fin n → Bool) :
    (searchSetup hn).succProb id Marked x = (markedCount x : ℝ) / n := by
  rw [AmpSetup.succProb, searchSetup_prepared, goodProb_eq_sum_ite]
  have h := sum_mul_normSq_uniformIdx hn
    (fun p => if Marked x ((searchSetup hn).readout p) then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at h
  rw [h, markedCount, Finset.card_filter]
  push_cast
  rfl

/-- The original probability of each index is `1/n`. -/
theorem searchSetup_orig_prob (hn : 0 < n) (x : Fin n → Bool) (i : Fin n) :
    (searchSetup hn).origAlg.prob x (searchSetup hn).prep.len i = 1 / n := by
  rw [QAlg.prob, AmpSetup.origAlg_state, searchSetup_prepared, qProb]
  have h := sum_mul_normSq_uniformIdx hn
    (fun p => if (searchSetup hn).readout p = i then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at h
  show (∑ p, if (searchSetup hn).readout p = i then _ else 0) = _
  rw [h]
  show (∑ j : Fin n, if (some j : Option (Fin n)).getD ⟨0, hn⟩ = i then (1 : ℝ) else 0) / n = _
  simp

/-! ## The search algorithm -/

/-- **Search**: the amplified algorithm of the search setup, output `Option (Fin n)`. -/
noncomputable def searchAlg (hn : 0 < n) (m : ℕ) (hm : 0 < m) :=
  (searchSetup hn).amplified m hm

/-- Its budget, `8·m` native queries. -/
def searchBudget (m : ℕ) : ℕ := 8 * m

lemma searchSetup_amplifiedBudget (hn : 0 < n) {m : ℕ} (hm : 0 < m) :
    (searchSetup hn).amplifiedBudget m = searchBudget m := by
  rw [AmpSetup.amplifiedBudget_eq, AmpSetup.trialBudget, searchBudget]
  change 4 * (0 + (m - 1) * (2 * 0 + 2) + 2) = 8 * m
  omega

variable (hn : 0 < n) {m : ℕ} (hm : 0 < m) (x : Fin n → Bool)

/-- **A returned index is always marked.** -/
theorem searchAlg_prob_some_of_unmarked {i : Fin n} (hi : x i = false) :
    (searchAlg hn m hm).prob x (searchBudget m) (some i) = 0 := by
  rw [← searchSetup_amplifiedBudget hn hm]
  exact (searchSetup hn).amplified_prob_some_of_not_good (searchSetup_marks hn) x hm
    (by simp [Marked, hi])

/-- The probability of returning an index. -/
noncomputable def searchReturnProb : ℝ :=
  1 - (searchAlg hn m hm).prob x (searchBudget m) none

/-- **With no marked index, the output is `none` surely.** -/
theorem searchAlg_prob_none_of_no_marked (h0 : markedCount x = 0) :
    (searchAlg hn m hm).prob x (searchBudget m) none = 1 := by
  rw [← searchSetup_amplifiedBudget hn hm]
  refine (searchSetup hn).amplified_prob_none_of_succProb_eq_zero (searchSetup_marks hn) x hm ?_
  rw [searchSetup_succProb, h0]; simp

/-- **Promised-density search**: if at least `k ≥ 1` indices are marked and `m·√(k/n) ≥ 1`,
an index is returned with probability at least `2/3` — the actual count is not needed. -/
theorem two_thirds_le_searchReturnProb {k : ℕ} (hk : 0 < k) (hkt : k ≤ markedCount x)
    (hmp : 1 ≤ (m : ℝ) * Real.sqrt ((k : ℝ) / n)) :
    2 / 3 ≤ searchReturnProb hn hm x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h := (searchSetup hn).two_thirds_le_returnProb (searchSetup_marks hn) x hm
    (p₀ := (k : ℝ) / n) (by positivity)
    (by rw [searchSetup_succProb]; gcongr) hmp
  rw [AmpSetup.returnProb, searchSetup_amplifiedBudget hn hm] at h
  exact h

/-- **Exact uniformity over the marked indices**, conditioned on returning one:
`t · Pr[some i] = Pr[≠ none]` for every marked `i`. -/
theorem markedCount_mul_searchAlg_prob_some {i : Fin n} (hi : x i = true) :
    (markedCount x : ℝ) * (searchAlg hn m hm).prob x (searchBudget m) (some i)
      = searchReturnProb hn hm x := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h := (searchSetup hn).succProb_mul_amplified_prob_some (searchSetup_marks hn) x hm i
  rw [searchSetup_succProb, AmpSetup.goodWeight, if_pos (by simpa [Marked] using hi),
    searchSetup_orig_prob, AmpSetup.returnProb, searchSetup_amplifiedBudget hn hm] at h
  rw [searchReturnProb]
  have h' := h
  field_simp at h'
  exact h'

/-- The iteration count for a promised density `k/n`: `⌈√(n/k)⌉`, with budget at most
`16·√(n/k)`. -/
theorem searchBudget_le (hn : 0 < n) {k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    1 ≤ (ampIterations ((k : ℝ) / n) : ℝ) * Real.sqrt ((k : ℝ) / n) ∧
    (searchBudget (ampIterations ((k : ℝ) / n)) : ℝ) ≤ 16 * Real.sqrt ((n : ℝ) / k) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hp₀ : (0 : ℝ) < (k : ℝ) / n := by positivity
  have hp1 : (k : ℝ) / n ≤ 1 := by
    rw [div_le_one hn']; exact_mod_cast hkn
  refine ⟨one_le_ampIterations_mul_sqrt hp₀, ?_⟩
  have h := ampIterations_le hp₀ hp1
  have hinv : 1 / Real.sqrt ((k : ℝ) / n) = Real.sqrt ((n : ℝ) / k) := by
    rw [one_div, ← Real.sqrt_inv, inv_div]
  rw [searchBudget]
  push_cast
  calc (8 : ℝ) * (ampIterations ((k : ℝ) / n) : ℝ) ≤ 8 * (2 / Real.sqrt ((k : ℝ) / n)) := by
        gcongr
    _ = 16 * (1 / Real.sqrt ((k : ℝ) / n)) := by ring
    _ = 16 * Real.sqrt ((n : ℝ) / k) := by rw [hinv]

/-! ## `n = 0` -/

/-- With no index at all, the zero-query constant algorithm returns `none` surely. -/
theorem search_zero (x : Fin 0 → Bool) :
    (constAlg (Fin 0) Bool (none : Option (Fin 0))).prob x 0 none = 1 := by
  simp [QAlg.prob, constAlg]

end QuantumQueryComplexity
