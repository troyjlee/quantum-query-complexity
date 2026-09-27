import QuantumQueryComplexity.Quantum.Amplitude.Search
import QuantumQueryComplexity.Quantum.Amplitude.Verifier

set_option synthInstance.maxSize 1000000
set_option synthInstance.maxHeartbeats 20000000
set_option maxHeartbeats 1000000
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Acceptance: amplitude amplification

Statement pins and edge cases.

1. Exact query counts: `grover.len = 2S+C`, `S + j(2S+C)`, the verified trial
   `S + j(2S+C) + C`, the four-trial budget `≤ 4m(2S+C) ≤ 16(S+C)/√p₀`.  No positivity of
   `S` or `C` is assumed anywhere.
2. `sin²((2j+1)θ)` for every `0 ≤ p ≤ 1`: `p = 0`, `p = 1`, zero iterations.
3. **Overshooting**: at `p = 3/4` one ordinary iteration has success exactly `0` — success
   is not monotone in the number of iterations, and no such lemma is used.
4. The public theorem: never an invalid `some y`; `≥ 2/3` pointwise from `pₓ ≥ p₀`; `none`
   surely at `pₓ = 0`; the conditional law in product and divided form.
5. A nonuniform prepared distribution: the ratio of two valid outputs is preserved, by the
   iterate and by the final algorithm (uniform search alone would not detect a bias).
6. Relations with several valid outputs on a noninjective promise map, and the
   equality-relation specialization to `ComputesWithErrorOn`.
8. **The verifier constructor** `AmpSetup.ofVerifier`: from `IsCoherentVerifier` alone (no
   `Marks`, embedding or readout hypothesis) the public guarantees follow with the logical
   probabilities; exact costs at `C = 2V`; the clean state of the ordinary iterates; and a
   concrete zero-query fixture (masses `1/2, 1/4, 1/4`, the first two outputs valid) whose
   verifier is constructed and proved, with no invalid return and the ratio `2:1` preserved
   by the public amplified algorithm.
7. Search: a returned index is always marked, `≥ 2/3` under a density promise, `none` surely
   without marked indices, exact uniformity, budget `8m ≤ 16√(n/k)` native queries.

Axioms: `lake env lean --trust=0 QuantumQueryComplexity/Test/AmplitudeAxioms.lean`.
-/

namespace QuantumQueryComplexity
namespace AmplitudeAmplificationAcceptance

variable {ι σ W X O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] [Fintype X]

/-! ## 1. Exact query counts -/

theorem acceptance_lengths [Fintype O] [DecidableEq O] (P : AmpSetup ι σ W O) (j m : ℕ) :
    P.grover.len = 2 * P.prep.len + P.mark.len
    ∧ (P.ampRoutine j).len = P.prep.len + j * (2 * P.prep.len + P.mark.len)
    ∧ (P.trialRoutine j).len = P.prep.len + j * (2 * P.prep.len + P.mark.len) + P.mark.len
    ∧ P.amplifiedBudget m
        = 4 * (P.prep.len + (m - 1) * (2 * P.prep.len + P.mark.len) + P.mark.len) :=
  ⟨P.grover_len, P.ampRoutine_len j, P.trialRoutine_len j, P.amplifiedBudget_eq m⟩

theorem acceptance_budget [Fintype O] [DecidableEq O] (P : AmpSetup ι σ W O) :
    (∀ m, 0 < m → P.amplifiedBudget m ≤ 4 * (m * (2 * P.prep.len + P.mark.len)))
    ∧ ∀ p₀ : ℝ, 0 < p₀ → p₀ ≤ 1 →
        (P.amplifiedBudget (ampIterations p₀) : ℝ)
          ≤ 16 * ((P.prep.len : ℝ) + P.mark.len) / Real.sqrt p₀ :=
  ⟨P.amplifiedBudget_le, fun _ h0 h1 => P.amplifiedBudget_le_real h0 h1⟩

/-- The adapters' costs: a verifier of cost `V` gives a marker of cost `2V`; the coherent
flag costs exactly the marker's `C`. -/
theorem acceptance_adapter_costs (Vr : QRoutine ι σ (Bool × W)) (mark : QRoutine ι σ W) :
    (markerOfVerifier Vr).len = 2 * Vr.len ∧ (flagRoutine mark).len = mark.len :=
  ⟨markerOfVerifier_len Vr, flagRoutine_len mark⟩

/-! ## 2–3. The success probability of the plain iterate -/

section Iterate

variable (P : AmpSetup ι σ W O) {read : X → ι → σ} {Good : X → O → Prop}
  [∀ x, DecidablePred (Good x)]

theorem acceptance_sin_sq (hP : P.Marks read Good) (x : X) (j : ℕ) :
    successProbOn (P.ampAlg j) (P.ampRoutine j).len read Good x
      = Real.sin ((2 * j + 1) * groverAngle (P.succProb read Good x)) ^ 2 :=
  P.successProbOn_ampAlg hP x j

/-- `p = 0`: every iterate has success `0`. -/
example (hP : P.Marks read Good) (x : X) (h0 : P.succProb read Good x = 0) (j : ℕ) :
    successProbOn (P.ampAlg j) (P.ampRoutine j).len read Good x = 0 := by
  rw [P.successProbOn_ampAlg hP, ← mul_ampA_sq (P.succProb_nonneg x) (P.succProb_le_one x), h0,
    zero_mul]

/-- `p = 1`: every iterate has success `1`. -/
example (hP : P.Marks read Good) (x : X) (h1 : P.succProb read Good x = 1) (j : ℕ) :
    successProbOn (P.ampAlg j) (P.ampRoutine j).len read Good x = 1 := by
  rw [P.successProbOn_ampAlg hP, h1, groverAngle, Real.sqrt_one, Real.arcsin_one]
  have h : Real.sin ((2 * (j : ℝ) + 1) * (Real.pi / 2)) ^ 2 = 1 := by
    have hc : Real.cos ((2 * (j : ℝ) + 1) * (Real.pi / 2)) = 0 := by
      rw [show (2 * (j : ℝ) + 1) * (Real.pi / 2) = Real.pi / 2 + j * Real.pi by ring,
        Real.cos_add_nat_mul_pi]
      simp
    have := Real.sin_sq_add_cos_sq ((2 * (j : ℝ) + 1) * (Real.pi / 2))
    rw [hc] at this
    linarith
  exact h

/-- Zero iterations: the original success probability. -/
example (hP : P.Marks read Good) (x : X) :
    successProbOn (P.ampAlg 0) (P.ampRoutine 0).len read Good x = P.succProb read Good x := by
  rw [P.successProbOn_ampAlg hP, ← mul_ampA_sq (P.succProb_nonneg x) (P.succProb_le_one x)]
  simp

/-- **Overshooting**: at `p = 3/4`, one iteration has success exactly `0`. -/
example (hP : P.Marks read Good) (x : X) (h : P.succProb read Good x = 3 / 4) :
    successProbOn (P.ampAlg 1) (P.ampRoutine 1).len read Good x = 0 := by
  rw [P.successProbOn_ampAlg hP, ← mul_ampA_sq (P.succProb_nonneg x) (P.succProb_le_one x), h,
    ampA_succ, ampA_zero, ampB_zero]
  norm_num

/-- **Ratios of valid outputs are preserved by the iterate** (nonuniform distributions). -/
example [DecidableEq O] (hP : P.Marks read Good) (x : X) (j : ℕ) {y₁ y₂ : O}
    (h₁ : Good x y₁) (h₂ : Good x y₂) :
    (P.ampAlg j).prob (read x) (P.ampRoutine j).len y₁ * P.origAlg.prob (read x) P.prep.len y₂
      = (P.ampAlg j).prob (read x) (P.ampRoutine j).len y₂
          * P.origAlg.prob (read x) P.prep.len y₁ := by
  rw [P.prob_ampAlg_of_good hP x j h₁, P.prob_ampAlg_of_good hP x j h₂]
  ring

end Iterate

/-! ## 4–5. The public theorem -/

section Public

variable [Fintype O] [DecidableEq O] (P : AmpSetup ι σ W O) {read : X → ι → σ}
  {Good : X → O → Prop} [∀ x, DecidablePred (Good x)]

theorem acceptance_public (hP : P.Marks read Good) (x : X) {m : ℕ} (hm : 0 < m) :
    (∀ y, ¬ Good x y →
        (P.amplified m hm).prob (read x) (P.amplifiedBudget m) (some y) = 0)
    ∧ (∀ p₀ : ℝ, 0 < p₀ → p₀ ≤ P.succProb read Good x → 1 ≤ (m : ℝ) * Real.sqrt p₀ →
        2 / 3 ≤ P.returnProb read x m hm)
    ∧ (P.succProb read Good x = 0 →
        (P.amplified m hm).prob (read x) (P.amplifiedBudget m) none = 1)
    ∧ ∀ y, P.succProb read Good x
          * (P.amplified m hm).prob (read x) (P.amplifiedBudget m) (some y)
        = P.returnProb read x m hm
          * (if Good x y then P.origAlg.prob (read x) P.prep.len y else 0) :=
  ⟨fun _ hy => P.amplified_prob_some_of_not_good hP x hm hy,
   fun _ h0 hpp hmp => P.two_thirds_le_returnProb hP x hm h0 hpp hmp,
   P.amplified_prob_none_of_succProb_eq_zero hP x hm,
   fun y => P.succProb_mul_amplified_prob_some hP x hm y⟩

theorem acceptance_cond_law (hP : P.Marks read Good) (x : X) {m : ℕ} (hm : 0 < m) (y : O)
    (hp : 0 < P.succProb read Good x) (hs : 0 < P.returnProb read x m hm) :
    (P.amplified m hm).prob (read x) (P.amplifiedBudget m) (some y) / P.returnProb read x m hm
      = (if Good x y then P.origAlg.prob (read x) P.prep.len y else 0)
          / P.succProb read Good x :=
  P.amplified_cond_law hP x hm y hp hs

theorem acceptance_solves (hP : P.Marks read Good) {p₀ : ℝ} (hp₀ : 0 < p₀)
    (hpp : ∀ x, p₀ ≤ P.succProb read Good x) :
    SolvesWithErrorOn (P.amplified (ampIterations p₀) (ampIterations_pos hp₀))
      (P.amplifiedBudget (ampIterations p₀)) read (AmpSetup.OptGood Good) (1 / 3) :=
  P.solvesWithErrorOn_amplified hP (ampIterations_pos hp₀) hp₀ hpp
    (one_le_ampIterations_mul_sqrt hp₀)

/-- **Ratios of valid outputs are preserved by the final algorithm**, through the random
iteration count, the mixture and the first-success selection. -/
example (hP : P.Marks read Good) (x : X) {m : ℕ} (hm : 0 < m) {y₁ y₂ : O}
    (h₁ : Good x y₁) (h₂ : Good x y₂) :
    (P.amplified m hm).prob (read x) (P.amplifiedBudget m) (some y₁)
        * P.origAlg.prob (read x) P.prep.len y₂
      = (P.amplified m hm).prob (read x) (P.amplifiedBudget m) (some y₂)
        * P.origAlg.prob (read x) P.prep.len y₁ := by
  rw [P.amplified_prob_some hP, P.amplified_prob_some hP, AmpSetup.goodWeight,
    AmpSetup.goodWeight, if_pos h₁, if_pos h₂]
  ring

end Public

/-! ## 6. Contracts and the equality relation -/

/-- A full-operator marker marks every prepared state. -/
example (P : AmpSetup ι σ W O) {read : X → ι → σ} {Good : X → O → Prop}
    [∀ x, DecidablePred (Good x)] (h : IsPhaseMarker P.mark read Good P.readout) :
    P.Marks read Good :=
  h.marksState _

theorem acceptance_equality_relation [DecidableEq O] {A : QAlg ι σ O W} {q : ℕ}
    {read : X → ι → σ} {f : X → O} {ε : ℝ} :
    SolvesWithErrorOn A q read (fun x y => y = f x) ε ↔ ComputesWithErrorOn A q read f ε :=
  solvesWithErrorOn_eq_iff

/-! ## 7. Search -/

theorem acceptance_search {n : ℕ} (hn : 0 < n) {m : ℕ} (hm : 0 < m) (x : Fin n → Bool) :
    (∀ i, x i = false → (searchAlg hn m hm).prob x (searchBudget m) (some i) = 0)
    ∧ (markedCount x = 0 → (searchAlg hn m hm).prob x (searchBudget m) none = 1)
    ∧ (∀ k, 0 < k → k ≤ markedCount x → 1 ≤ (m : ℝ) * Real.sqrt ((k : ℝ) / n) →
        2 / 3 ≤ searchReturnProb hn hm x)
    ∧ ∀ i, x i = true →
        (markedCount x : ℝ) * (searchAlg hn m hm).prob x (searchBudget m) (some i)
          = searchReturnProb hn hm x :=
  ⟨fun _ hi => searchAlg_prob_some_of_unmarked hn hm x hi,
   searchAlg_prob_none_of_no_marked hn hm x,
   fun _ hk hkt hmp => two_thirds_le_searchReturnProb hn hm x hk hkt hmp,
   fun _ hi => markedCount_mul_searchAlg_prob_some hn hm x hi⟩

theorem acceptance_search_budget {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    1 ≤ (ampIterations ((k : ℝ) / n) : ℝ) * Real.sqrt ((k : ℝ) / n) ∧
    (searchBudget (ampIterations ((k : ℝ) / n)) : ℝ) ≤ 16 * Real.sqrt ((n : ℝ) / k) :=
  searchBudget_le hn hk hkn

/-- The native marker costs exactly two queries; the search preparation costs none. -/
example {n : ℕ} (hn : 0 < n) :
    (searchSetup hn).mark.len = 2 ∧ (searchSetup hn).prep.len = 0 := ⟨rfl, rfl⟩

example (x : Fin 0 → Bool) :
    (constAlg (Fin 0) Bool (none : Option (Fin 0))).prob x 0 none = 1 := search_zero x

/-! ## 8. The verifier constructor -/

section Verifier

variable (prep : QRoutine ι σ W) (init : QBasis ι σ W → ℂ) (hinit : IsQState init)
  (rd : QBasis ι σ W → O) (verifier : QRoutine ι σ (Bool × W)) {read : X → ι → σ}
  {Good : X → O → Prop} [∀ x, DecidablePred (Good x)]

/-- Exact costs at `C = 2V`. -/
theorem acceptance_verifier_lengths [Fintype O] [DecidableEq O] (j m : ℕ) :
    let P := AmpSetup.ofVerifier prep init hinit rd verifier
    P.prep.len = prep.len ∧ P.mark.len = 2 * verifier.len
    ∧ P.grover.len = 2 * prep.len + 2 * verifier.len
    ∧ (P.ampRoutine j).len = prep.len + j * (2 * prep.len + 2 * verifier.len)
    ∧ (P.trialRoutine j).len
        = prep.len + j * (2 * prep.len + 2 * verifier.len) + 2 * verifier.len
    ∧ P.amplifiedBudget m
        = 4 * (prep.len + (m - 1) * (2 * prep.len + 2 * verifier.len) + 2 * verifier.len) := by
  intro P
  refine ⟨rfl, ofVerifier_mark_len .., ?_, ?_, ?_, ?_⟩
  · rw [AmpSetup.grover_len, ofVerifier_mark_len, ofVerifier_prep_len]
  · rw [AmpSetup.ampRoutine_len, ofVerifier_mark_len, ofVerifier_prep_len]
  · rw [AmpSetup.trialRoutine_len, ofVerifier_mark_len, ofVerifier_prep_len]
  · rw [AmpSetup.amplifiedBudget_eq, AmpSetup.trialBudget, ofVerifier_mark_len,
      ofVerifier_prep_len]

/-- The real budget at `C = 2V`: `16(S + 2V)/√p₀`. -/
theorem acceptance_verifier_budget [Fintype O] [DecidableEq O] {p₀ : ℝ} (hp₀ : 0 < p₀)
    (hp1 : p₀ ≤ 1) :
    ((AmpSetup.ofVerifier prep init hinit rd verifier).amplifiedBudget (ampIterations p₀) : ℝ)
      ≤ 16 * ((prep.len : ℝ) + 2 * verifier.len) / Real.sqrt p₀ := by
  have h := (AmpSetup.ofVerifier prep init hinit rd verifier).amplifiedBudget_le_real hp₀ hp1
  rw [ofVerifier_mark_len, ofVerifier_prep_len] at h
  push_cast at h
  exact h

/-- **From the verifier contract alone**: the public amplification guarantees, stated with
the original logical probabilities. -/
theorem acceptance_verifier_public [Fintype O] [DecidableEq O]
    (hV : IsCoherentVerifier verifier read Good rd) (x : X) {m : ℕ} (hm : 0 < m) :
    let P := AmpSetup.ofVerifier prep init hinit rd verifier
    let p := goodProb rd (Good x) (Matrix.mulVec (prep.run (read x)) init)
    (∀ y, ¬ Good x y → (P.amplified m hm).prob (read x) (P.amplifiedBudget m) (some y) = 0)
    ∧ (∀ p₀ : ℝ, 0 < p₀ → p₀ ≤ p → 1 ≤ (m : ℝ) * Real.sqrt p₀ →
        2 / 3 ≤ P.returnProb read x m hm)
    ∧ (p = 0 → (P.amplified m hm).prob (read x) (P.amplifiedBudget m) none = 1)
    ∧ ∀ y, p * (P.amplified m hm).prob (read x) (P.amplifiedBudget m) (some y)
        = P.returnProb read x m hm
          * (if Good x y then (prep.toAlg init hinit rd).prob (read x) prep.len y else 0) := by
  intro P p
  have hP := ofVerifier_marks prep init hinit rd verifier hV
  have hp : P.succProb read Good x = p := ofVerifier_succProb prep init hinit rd verifier x
  refine ⟨fun y hy => P.amplified_prob_some_of_not_good hP x hm hy,
    fun p₀ h0 hpp hmp => P.two_thirds_le_returnProb hP x hm h0 (hp ▸ hpp) hmp,
    fun h0 => P.amplified_prob_none_of_succProb_eq_zero hP x hm (hp.trans h0), fun y => ?_⟩
  have h := P.succProb_mul_amplified_prob_some hP x hm y
  rw [hp, AmpSetup.goodWeight, ofVerifier_origAlg_prob] at h
  exact h

/-- The ordinary iterates stay in the clean subspace. -/
theorem acceptance_verifier_clean (hV : IsCoherentVerifier verifier read Good rd) (x : X)
    (j : ℕ) :
    ∃ χ : QBasis ι σ W → ℂ,
      Matrix.mulVec (((AmpSetup.ofVerifier prep init hinit rd verifier).ampRoutine j).run (read x))
          (AmpSetup.ofVerifier prep init hinit rd verifier).init
        = embedReg false χ :=
  ⟨_, ofVerifier_ampRoutine_run prep init hinit rd verifier hV x j⟩

end Verifier

/-! ### A concrete fixture: three outputs with masses `1/2, 1/4, 1/4`, the first two valid

Zero queries everywhere (`S = 0`, `V = 0`).  The logical output is stored in a `Fin 3`
workspace; the exact verifier is the free permutation flipping the flag exactly on the
valid outputs.  Only its *clean* contract is proved — on a dirty flag the resulting marker
acts as `−(I − 2Π)`, which is why the constructor asks for no more. -/

namespace Fixture

/-- The logical readout: the stored output. -/
def rd3 : QBasis Empty Bool (Fin 3) → Fin 3 := fun p => p.2.2

/-- Outputs `0` and `1` are valid. -/
def Good3 (_ : Unit) (y : Fin 3) : Prop := y ≠ 2

instance (x : Unit) : DecidablePred (Good3 x) := fun y => by unfold Good3; infer_instance

/-- Amplitudes `1/√2, 1/2, 1/2` on the three outputs, registers blank. -/
noncomputable def init3 : QBasis Empty Bool (Fin 3) → ℂ := fun p =>
  match p with
  | (none, none, w) => if w = 0 then hadS else 2⁻¹
  | _ => 0

lemma sum_init3 (g : QBasis Empty Bool (Fin 3) → ℝ) :
    ∑ p, g p * Complex.normSq (init3 p)
      = g (none, none, 0) / 2 + g (none, none, 1) / 4 + g (none, none, 2) / 4 := by
  have h2 : Complex.normSq (2⁻¹ : ℂ) = 1 / 4 := by
    rw [Complex.normSq_inv]; norm_num [Complex.normSq_ofNat]
  rw [Fintype.sum_prod_type, Fintype.sum_option]
  simp only [Fintype.sum_prod_type, Fintype.sum_option, Fintype.sum_bool, Fin.sum_univ_three,
    Finset.univ_eq_empty, Finset.sum_empty, init3, map_zero, mul_zero, add_zero,
    if_true, Fin.reduceEq, if_false, normSq_hadS, h2]
  ring

lemma isQState_init3 : IsQState init3 := by
  have h := sum_init3 (fun _ => 1)
  simp only [one_mul] at h
  rw [IsQState, qNormSq_def, h]; norm_num

/-- Flip the flag exactly on the valid outputs. -/
def flipMap3 : QBasis Empty Bool (Bool × Fin 3) → QBasis Empty Bool (Bool × Fin 3)
  | (k, t, (f, w)) => (k, t, (if w = 2 then f else !f, w))

lemma flipMap3_involutive : Function.Involutive flipMap3 := by
  rintro ⟨k, t, f, w⟩
  by_cases hw : w = 2 <;> simp [flipMap3, hw]

/-- The zero-query exact verifier. -/
noncomputable def verifier3 : QRoutine Empty Bool (Bool × Fin 3) :=
  QRoutine.ofUnitary (qPerm (Function.Involutive.toPerm _ flipMap3_involutive))
    (qPerm_mem_unitaryGroup _)

/-- **The verifier's clean contract, proved.** -/
theorem isCoherentVerifier3 :
    IsCoherentVerifier verifier3 (fun (_ : Unit) (i : Empty) => i.elim) Good3 rd3 := by
  intro x φ
  funext p
  rw [verifier3, QRoutine.ofUnitary_run, qPerm_mulVec_apply]
  obtain ⟨k, t, f, w⟩ := p
  change embedReg false φ (flipMap3 (k, t, f, w)) = _
  simp only [Pi.add_apply, embedReg_apply, flipMap3, goodPart_apply, badPart_apply, rd3, Good3]
  by_cases hw : w = 2 <;> cases f <;> simp [hw]

/-- The constructed setup. -/
noncomputable def setup3 : AmpSetup Empty Bool (Bool × Fin 3) (Fin 3) :=
  AmpSetup.ofVerifier QRoutine.identity init3 isQState_init3 rd3 verifier3

theorem setup3_marks : setup3.Marks (fun (_ : Unit) (i : Empty) => i.elim) Good3 :=
  ofVerifier_marks _ _ _ _ _ isCoherentVerifier3

/-- `S = 0` and `V = 0`. -/
example : setup3.prep.len = 0 ∧ setup3.mark.len = 0 := ⟨rfl, by
  rw [setup3, ofVerifier_mark_len]; rfl⟩

lemma orig3_prob (y : Fin 3) :
    setup3.origAlg.prob (fun i : Empty => i.elim) setup3.prep.len y
      = if y = 0 then 1 / 2 else 1 / 4 := by
  rw [setup3, ofVerifier_origAlg_prob, QAlg.prob, QRoutine.toAlg_state_len,
    QRoutine.identity_run, Matrix.one_mulVec]
  show qProb rd3 init3 y = _
  rw [qProb]
  have h := sum_init3 (fun p => if rd3 p = y then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at h
  rw [h]
  fin_cases y <;> simp [rd3]

/-- **The original success mass is `3/4`.** -/
theorem setup3_succProb :
    setup3.succProb (fun (_ : Unit) (i : Empty) => i.elim) Good3 () = 3 / 4 := by
  rw [setup3, ofVerifier_succProb, QRoutine.identity_run, Matrix.one_mulVec,
    goodProb_eq_sum_ite]
  have h := sum_init3 (fun p => if Good3 () (rd3 p) then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at h
  rw [h]
  simp [rd3, Good3]
  norm_num

/-- **No invalid return, and the ratio `2:1` of the valid outputs is preserved** by the
public amplified algorithm. -/
theorem setup3_amplified {m : ℕ} (hm : 0 < m) :
    (setup3.amplified m hm).prob (fun i : Empty => i.elim) (setup3.amplifiedBudget m) (some 2)
        = 0
    ∧ (setup3.amplified m hm).prob (fun i : Empty => i.elim) (setup3.amplifiedBudget m) (some 0)
        = 2 * (setup3.amplified m hm).prob (fun i : Empty => i.elim) (setup3.amplifiedBudget m)
            (some 1) := by
  constructor
  · exact setup3.amplified_prob_some_of_not_good setup3_marks () hm (by simp [Good3])
  · rw [setup3.amplified_prob_some setup3_marks () hm, setup3.amplified_prob_some setup3_marks
      () hm, AmpSetup.goodWeight, AmpSetup.goodWeight, if_pos (by simp [Good3]),
      if_pos (by simp [Good3]), orig3_prob, orig3_prob]
    norm_num
    ring

end Fixture

end AmplitudeAmplificationAcceptance
end QuantumQueryComplexity
