import QuantumQueryComplexity.Quantum.Amplitude.LabelSearch
import QuantumQueryComplexity.Quantum.RoutineClose
import QuantumQueryComplexity.Quantum.Amplitude.CleanControl

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Clean coherent preparation of the uniform marked state

[CGKLPZ26, Lemma 2.4, last clause]. A known set `S` of `a` labels contains `r` marked labels
(`markedIn S x`). Given an estimate `r̂ > 0` within a factor `2` of `r` (`r ≤ 2r̂` and `r̂ ≤ 2r`, as
`CountGood` provides), a routine chosen before the input prepares the uniform superposition
`u = r^{−1/2} ∑_{i marked} |i⟩` on a label register `Option ι`, **cleanly**: there is no other
workspace, the query registers end blank, and

    ‖R |none⟩ − c·|u⟩‖ ≤ η    for some phase `‖c‖ = 1` depending on the input only

(`exists_coherentPrep`), with `prepBudget a r̂ η ≤ 200 √(a/r̂) (1 + ln(1/η))` queries
(`prepBudget_le`). The phase is unavoidable for amplitude-amplification preparations and harmless
where every use on the same input carries the same `c` (see `RoutineClose.lean` and
`ApproxWalkOK`). A positive estimate is needed: with `r̂ = 0` no fixed budget can prepare `u` for
every nonempty marked set.

**The same routine keeps blank query registers exactly**: on every input, promised or not, it
commutes with the projection onto blank query registers (`exists_coherentPrep_blank`, of which
`exists_coherentPrep` is a corollary). Closeness to a query-blank state alone would not give the
exact support and commutation hypotheses of a walk update (`ApproxWalkOK`). In the construction
every phase marker loads the label into the query index, queries twice and unloads, and every
reflection acts on the blank sector only, so each component maps query-blank states to
query-blank states.

Construction (replacing the fixed-point search of [YLC14] cited by the paper):
* **base**: the uniform state over `S` (query-free), then `k = ⌊(2/5)√(a/r̂)⌋` Grover iterations
  (`prepIters`), each a two-query phase marker and a query-free reflection. The state stays in
  `span{u, u⊥}` (`u⊥` uniform over the unmarked labels of `S`), and its success probability
  `sin²((2k+1)θ)`, `sin²θ = r/a`, is at least `1/16` whenever `r̂/2 ≤ r ≤ 2r̂`: if `k = 0` it is
  `r/a ≥ r̂/(2a) > 2/25`; if `k ≥ 1` then `(2k+1)θ ∈ [0.42, 2.67]` by `sin θ ≤ θ ≤ (π/2) sin θ`;
* **Grover's π/3 recursion** [Gro05]: `U_{m+1} = U_m ; S_t ; U_m⁻¹ ; S_0 ; U_m`, with `S_t` the
  phase `ω = e^{iπ/3}` on marked labels (two queries) and `S_0 = 1 − (1 − ω)|none⟩⟨none|`
  (free). Since `(1 − ω)ω = 1`, a failure probability `ε` becomes exactly `ε³`, and the state
  stays in `span{u, u⊥}`: after `m = prepLevels η` levels the failure probability is
  `(15/16)^{3^m} ≤ η²/2`, so the state is within `η` of `c·u`. The length is
  `3^m·2k + (3^m − 1) ≤ 3^m(2k + 1)`.
-/

namespace QuantumQueryComplexity

open scoped Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The uniform state over the marked labels** of `S`. -/
noncomputable def markedLabelState (S : Finset ι) (x : ι → Bool) : ι → ℂ := fun i =>
  if i ∈ markedIn S x then ((1 / Real.sqrt (markedIn S x).card : ℝ) : ℂ) else 0

/-- **A label state on the label register** `Option ι`, query registers blank:
`∑_i u_i |some i⟩`. -/
def labelVec (u : ι → ℂ) : QBasis ι Bool (Option ι) → ℂ := fun p =>
  if p.1 = none ∧ p.2.1 = none then
    (match p.2.2 with
      | some i => u i
      | none => 0)
  else 0

/-- **The blank label register** `|none⟩`, query registers blank. -/
def blankLabel : QBasis ι Bool (Option ι) := (none, none, none)

/-- **Blank query registers** on the label register: the query index and value are both `none`.
`flagProj labelQueryBlank` is the projection onto them. -/
def labelQueryBlank : QBasis ι Bool (Option ι) → Bool := fun p => decide (p.1 = none ∧ p.2.1 = none)

/-- Grover iterations of the base: `⌊(2/5)√(a/r̂)⌋`. -/
noncomputable def prepIters (a rh : ℕ) : ℕ := ⌊2 * Real.sqrt (a / rh) / 5⌋₊

/-- Levels of the π/3 recursion for precision `η`: `⌈log₃ ⌈ln(2/η²)/ln(16/15)⌉⌉`. -/
noncomputable def prepLevels (η : ℝ) : ℕ :=
  Nat.clog 3 ⌈Real.log (2 / η ^ 2) / Real.log (16 / 15)⌉₊

/-- **The preparation budget**: `3^m (2k + 1)`, `m = prepLevels η`, `k = prepIters a r̂`. -/
noncomputable def prepBudget (a rh : ℕ) (η : ℝ) : ℕ := 3 ^ prepLevels η * (2 * prepIters a rh + 1)

/-- `3 ^ clog 3 N ≤ 3 N + 1` for every `N`. -/
private lemma cpb_pow_clog_le (N : ℕ) : 3 ^ Nat.clog 3 N ≤ 3 * N + 1 := by
  rcases Nat.lt_or_ge 1 N with hN | hN
  · have h1 := Nat.pow_pred_clog_lt_self (b := 3) (by norm_num) hN
    have h2 : 0 < Nat.clog 3 N := Nat.clog_pos (by norm_num) hN
    have h3 : 3 ^ Nat.clog 3 N = 3 * 3 ^ (Nat.clog 3 N - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [Nat.pred_eq_sub_one] at h1
    omega
  · rw [Nat.clog_of_right_le_one hN]; omega

/-- `ln(1/η) ≥ 0` for `0 < η ≤ 1`. -/
private lemma cpb_log_one_div_nonneg {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    0 ≤ Real.log (1 / η) :=
  Real.log_nonneg (by rw [one_div]; exact one_le_inv_iff₀.mpr ⟨hη0, hη1⟩)

/-- The levels factor: `3 ^ prepLevels η ≤ 100 (1 + ln(1/η))` for `0 < η ≤ 1`. -/
private lemma cpb_pow_levels_le {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    ((3 ^ prepLevels η : ℕ) : ℝ) ≤ 100 * (1 + Real.log (1 / η)) := by
  have hL := cpb_log_one_div_nonneg hη0 hη1
  have hlogη : Real.log η = -Real.log (1 / η) := by rw [one_div, Real.log_inv, neg_neg]
  have hnum : Real.log (2 / η ^ 2) = Real.log 2 + 2 * Real.log (1 / η) := by
    rw [Real.log_div (by norm_num) (by positivity), Real.log_pow, hlogη]; push_cast; ring
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num); linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 1 / 16 ≤ Real.log (16 / 15) := by
    have := Real.one_sub_inv_le_log_of_pos (x := 16 / 15) (by norm_num)
    norm_num at this ⊢; linarith
  have hden0 : 0 < Real.log (16 / 15) := by linarith
  have hx0 : 0 ≤ Real.log (2 / η ^ 2) / Real.log (16 / 15) :=
    div_nonneg (by rw [hnum]; positivity) hden0.le
  have hx : Real.log (2 / η ^ 2) / Real.log (16 / 15) ≤
      16 * (Real.log 2 + 2 * Real.log (1 / η)) := by
    rw [div_le_iff₀ hden0, hnum]
    nlinarith
  have hN := Nat.ceil_lt_add_one (R := ℝ) hx0
  have hpow := cpb_pow_clog_le ⌈Real.log (2 / η ^ 2) / Real.log (16 / 15)⌉₊
  have h3 : ((3 ^ prepLevels η : ℕ) : ℝ) ≤
      3 * (⌈Real.log (2 / η ^ 2) / Real.log (16 / 15)⌉₊ : ℝ) + 1 := by
    unfold prepLevels; exact_mod_cast hpow
  nlinarith

/-- **The preparation budget is `O(√(a/r̂) log(1/η))`.** -/
theorem prepBudget_le {a rh : ℕ} (hr0 : 0 < rh) (hra : rh ≤ a) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1) :
    (prepBudget a rh η : ℝ) ≤ 200 * Real.sqrt (a / rh) * (1 + Real.log (1 / η)) := by
  have hu : 1 ≤ Real.sqrt (a / rh) := by
    rw [Real.one_le_sqrt, one_le_div (by exact_mod_cast hr0)]; exact_mod_cast hra
  have hk : (2 * prepIters a rh + 1 : ℝ) ≤ 9 / 5 * Real.sqrt (a / rh) := by
    have := Nat.floor_le (a := 2 * Real.sqrt (a / rh) / 5) (by positivity)
    unfold prepIters; linarith
  have hm := cpb_pow_levels_le hη0 hη1
  have hL := cpb_log_one_div_nonneg hη0 hη1
  unfold prepBudget
  push_cast at hm ⊢
  calc (3 : ℝ) ^ prepLevels η * (2 * prepIters a rh + 1)
      ≤ (100 * (1 + Real.log (1 / η))) * (9 / 5 * Real.sqrt (a / rh)) :=
        mul_le_mul hm hk (by positivity) (by positivity)
    _ ≤ 200 * Real.sqrt (a / rh) * (1 + Real.log (1 / η)) := by nlinarith

/-! ## Proof of `exists_coherentPrep_blank`: generic facts -/

section CppGeneric

variable {H : Type} [Fintype H] [DecidableEq H]

/-- The phase `φ` on the range of `P`: `1 − (1 − φ) P`. -/
private noncomputable def cpp_phase (φ : ℂ) (P : Matrix H H ℂ) : Matrix H H ℂ :=
  1 - (1 - φ) • P

/-- The phase on the range of `P`, on vectors. -/
private lemma cpp_phase_mulVec (φ : ℂ) (P : Matrix H H ℂ) (v : H → ℂ) :
    cpp_phase φ P *ᵥ v = v - (1 - φ) • (P *ᵥ v) := by
  rw [cpp_phase, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]

/-- A phase of modulus one on the range of a projector is unitary. -/
private lemma cpp_phase_mem_unitaryGroup {φ : ℂ} (hφ : star φ * φ = 1) {P : Matrix H H ℂ}
    (hP : IsQProjector P) : cpp_phase φ P ∈ Matrix.unitaryGroup H ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, cpp_phase,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hP.1]
  have h2 : (1 - φ) * star (1 - φ) = star (1 - φ) + (1 - φ) := by
    rw [star_sub, star_one]
    linear_combination hφ
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, hP.2]
  rw [smul_sub, smul_smul, h2, add_smul]
  abel

/-- A diagonal flag projector is a projector. -/
private lemma cpp_isQProjector_flagProj (c : H → Bool) : IsQProjector (flagProj c) :=
  ⟨flagProj_conjTranspose c, flagProj_mul_self c⟩

/-- Two diagonal flag projectors commute. -/
private lemma cpp_commute_flagProj (c d : H → Bool) : Commute (flagProj c) (flagProj d) := by
  change flagProj c * flagProj d = flagProj d * flagProj c
  rw [flagProj, flagProj, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext h
  ring

/-- `|ψ⟩⟨ψ|` commutes with a self-adjoint `B` fixing `ψ`. -/
private lemma cpp_commute_ketbra {B : Matrix H H ℂ} (hB : Bᴴ = B) {ψ : H → ℂ}
    (hψ : B *ᵥ ψ = ψ) : Commute (ketbra ψ) B := by
  change ketbra ψ * B = B * ketbra ψ
  rw [ketbra, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec, hψ]
  congr 1
  rw [show star ψ ᵥ* B = star ψ ᵥ* Bᴴ by rw [hB], ← Matrix.star_mulVec, hψ]

/-- A phase on the range of `P` commutes with whatever `P` commutes with. -/
private lemma cpp_commute_phase {φ : ℂ} {P B : Matrix H H ℂ} (h : Commute P B) :
    Commute (cpp_phase φ P) B :=
  (Commute.one_left B).sub_left (h.smul_left _)

/-- The reflection about a state fixed by a self-adjoint `B` commutes with `B`. -/
private lemma cpp_commute_stateRefl {B : Matrix H H ℂ} (hB : Bᴴ = B) {ψ : H → ℂ}
    (hψ : B *ᵥ ψ = ψ) : Commute (stateRefl ψ) B := by
  rw [stateRefl, qRefl]
  exact ((cpp_commute_ketbra hB hψ).smul_left _).sub_left (Commute.one_left B)

/-- The adjoint of a matrix commuting with a self-adjoint `B` commutes with `B`. -/
private lemma cpp_commute_conjTranspose {U B : Matrix H H ℂ} (hB : Bᴴ = B) (h : Commute U B) :
    Commute Uᴴ B := by
  have := congrArg Matrix.conjTranspose h.eq
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hB] at this
  exact this.symm

/-- **Grover's π/3 step** [Gro05]: if `U e = g + b` with `g` in the range of the projector `P`
and `b` in its kernel, then `U S₀ U† S_t U e = (ωε − 1 + ω) g + ωε b` with `ε = ‖b‖²`, where
`S_t = 1 − (1 − ω)P`, `S₀ = 1 − (1 − ω)|e⟩⟨e|` and `(1 − ω)² = −ω`. -/
private lemma cpp_pi3_step {U P : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (hP : IsQProjector P) {e g b : H → ℂ} (he : IsQState e) (hψ : U *ᵥ e = g + b)
    (hg : P *ᵥ g = g) (hb : P *ᵥ b = 0) {ω : ℂ} (hω : (1 - ω) ^ 2 = -ω) :
    (U * (cpp_phase ω (ketbra e) * (Uᴴ * (cpp_phase ω P * U)))) *ᵥ e
      = (ω * (qNormSq b : ℂ) - 1 + ω) • g + (ω * (qNormSq b : ℂ)) • b := by
  have hUU : Uᴴ * U = 1 := conjTranspose_mul_self_of_unitary hU
  have hUU' : U * Uᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  have horth : qInner g b = 0 := by
    rw [← hg, qInner_mulVec_left, hP.1, hb, qInner_zero_right]
  have hnorm : qNormSq g + qNormSq b = 1 := by
    have h1 := qNormSq_add g b
    rw [← hψ, qNormSq_mulVec hU, he, horth, Complex.zero_re, mul_zero, add_zero] at h1
    linarith
  have hgg : qInner (g + b) g = (qNormSq g : ℂ) := by
    rw [qInner_add_left, qInner_self, ← qInner_conj g b, horth, star_zero, add_zero]
  have hee : qInner e e = 1 := by
    rw [qInner_self, he]
    simp
  have hin : qInner e (Uᴴ *ᵥ g) = (qNormSq g : ℂ) := by
    rw [← qInner_mulVec_left, hψ, hgg]
  have h1 : cpp_phase ω P *ᵥ (U *ᵥ e) = (g + b) - (1 - ω) • g := by
    rw [cpp_phase_mulVec, hψ, Matrix.mulVec_add, hg, hb, add_zero]
  have h2 : Uᴴ *ᵥ ((g + b) - (1 - ω) • g) = e - (1 - ω) • (Uᴴ *ᵥ g) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, ← hψ, Matrix.mulVec_mulVec, hUU,
      Matrix.one_mulVec]
  have h3 : cpp_phase ω (ketbra e) *ᵥ (e - (1 - ω) • (Uᴴ *ᵥ g))
      = (e - (1 - ω) • (Uᴴ *ᵥ g)) - ((1 - ω) * (1 - (1 - ω) * qNormSq g)) • e := by
    rw [cpp_phase_mulVec, ketbra_mulVec, qInner_sub_right, qInner_smul_right, hee, hin,
      smul_smul]
  have h4 : U *ᵥ ((e - (1 - ω) • (Uᴴ *ᵥ g)) - ((1 - ω) * (1 - (1 - ω) * qNormSq g)) • e)
      = (g + b) - (1 - ω) • g - ((1 - ω) * (1 - (1 - ω) * qNormSq g)) • (g + b) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hψ,
      Matrix.mulVec_mulVec, hUU', Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, h1, h2, h3, h4]
  have hgn : (qNormSq g : ℂ) = 1 - qNormSq b := by
    rw [show qNormSq g = 1 - qNormSq b by linarith]
    push_cast
    ring
  rw [hgn]
  match_scalars <;> linear_combination (1 - (qNormSq b : ℂ)) * hω

/-- **Closeness from a small orthogonal error**: if a unit vector is `a·u + β` with `u` a unit
vector, `β ⊥ u` and `‖β‖² ≤ η²/2`, it is within `η` of `c·u` for a phase `c`. -/
private lemma cpp_close_of_split {u β : H → ℂ} {a : ℂ} (hu : IsQState u)
    (hψ : IsQState (a • u + β)) (horth : qInner u β = 0) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1) (hβ : qNormSq β ≤ η ^ 2 / 2) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ qNorm (a • u + β - c • u) ≤ η := by
  have hsplit : ∀ z : ℂ, qNormSq (z • u + β) = Complex.normSq z + qNormSq β := by
    intro z
    rw [qNormSq_add, qNormSq_smul, hu, qInner_smul_left, horth, mul_zero, Complex.zero_re,
      mul_zero, add_zero, mul_one]
  have h1 := hsplit a
  rw [hψ] at h1
  have hβ0 := qNormSq_nonneg β
  have hη2 : η ^ 2 ≤ 1 := by nlinarith
  have ha : a ≠ 0 := by
    rintro rfl
    rw [Complex.normSq_zero] at h1
    linarith
  have hnpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hnsq : Complex.normSq a = ‖a‖ ^ 2 := Complex.normSq_eq_norm_sq a
  have hn1 : ‖a‖ ≤ 1 := by nlinarith
  refine ⟨a / (‖a‖ : ℂ), ?_, ?_⟩
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnpos, div_self hnpos.ne']
  · have heq : a • u + β - (a / (‖a‖ : ℂ)) • u = (a - a / (‖a‖ : ℂ)) • u + β := by
      rw [sub_smul]
      abel
    rw [heq]
    apply qNorm_le_of_qNormSq_le hη0.le
    rw [hsplit]
    have hdiff : a - a / (‖a‖ : ℂ) = (((‖a‖ - 1) / ‖a‖ : ℝ) : ℂ) * a := by
      have : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
      push_cast
      field_simp
    rw [hdiff, Complex.normSq_mul, Complex.normSq_ofReal, hnsq]
    have : (‖a‖ - 1) / ‖a‖ * ((‖a‖ - 1) / ‖a‖) * ‖a‖ ^ 2 = (‖a‖ - 1) ^ 2 := by
      field_simp
    rw [this]
    nlinarith

end CppGeneric

/-! ## Proof of `exists_coherentPrep_blank`: the label register -/

section CppLabel

/-- Swap the query index and the label: `(k, t, w) ↦ (w, t, k)`. -/
private def cpp_swapMap : QBasis ι Bool (Option ι) → QBasis ι Bool (Option ι) :=
  fun p => (p.2.2, p.2.1, p.1)

/-- Swapping twice is the identity. -/
private lemma cpp_swapMap_involutive : Function.Involutive (cpp_swapMap (ι := ι)) :=
  fun _ => rfl

/-- The free permutation loading the label into the query index. -/
private def cpp_swap : Matrix (QBasis ι Bool (Option ι)) (QBasis ι Bool (Option ι)) ℂ :=
  qPerm (Function.Involutive.toPerm _ cpp_swapMap_involutive)

/-- The swap is unitary. -/
private lemma cpp_swap_mem :
    cpp_swap (ι := ι) ∈ Matrix.unitaryGroup (QBasis ι Bool (Option ι)) ℂ :=
  qPerm_mem_unitaryGroup _

/-- The swap on vectors. -/
private lemma cpp_swap_mulVec_apply (ψ : QBasis ι Bool (Option ι) → ℂ)
    (p : QBasis ι Bool (Option ι)) : (cpp_swap *ᵥ ψ) p = ψ (cpp_swapMap p) := by
  rw [cpp_swap, qPerm_mulVec_apply]
  rfl

/-- The answer register holds `true`. -/
private def cpp_ansTrue : QBasis ι Bool (Option ι) → Bool := fun p => decide (p.2.1 = some true)

/-- The basis states phased by the marker on input `x`. -/
private def cpp_mk (x : ι → Bool) : QBasis ι Bool (Option ι) → Bool :=
  fun p => cpp_ansTrue (oracleMap x (cpp_swapMap p))

/-- **The phase marker**: load the label, query, phase `φ` on the answer `true`, query, unload.
Two queries. -/
private noncomputable def cpp_markR (φ : ℂ) (hφ : star φ * φ = 1) :
    QRoutine ι Bool (Option ι) :=
  ((((QRoutine.ofUnitary cpp_swap cpp_swap_mem).comp QRoutine.query).comp
    (QRoutine.ofUnitary (cpp_phase φ (flagProj cpp_ansTrue))
      (cpp_phase_mem_unitaryGroup hφ (cpp_isQProjector_flagProj _)))).comp QRoutine.query).comp
    (QRoutine.ofUnitary cpp_swap cpp_swap_mem)

/-- The marker makes two queries. -/
private lemma cpp_markR_len (φ : ℂ) (hφ : star φ * φ = 1) :
    (cpp_markR (ι := ι) φ hφ).len = 2 := rfl

/-- The marker is the phase `φ` on the flag `cpp_mk x`. -/
private lemma cpp_markR_run (φ : ℂ) (hφ : star φ * φ = 1) (x : ι → Bool) :
    (cpp_markR φ hφ).run x = cpp_phase φ (flagProj (cpp_mk x)) := by
  refine matrix_ext_of_mulVec_qBasis fun r => ?_
  funext p
  simp only [cpp_markR, QRoutine.comp_run, QRoutine.query_run, QRoutine.ofUnitary_run,
    ← Matrix.mulVec_mulVec, cpp_swap_mulVec_apply, oracleMat_mulVec_apply, cpp_phase_mulVec,
    Pi.sub_apply, Pi.smul_apply, flagProj_mulVec, goodPart_apply, oracleMap_involutive x _,
    cpp_swapMap_involutive _]
  rfl

/-- The projection onto blank query registers is self-adjoint. -/
private lemma cpp_blank_conjTranspose :
    (flagProj (labelQueryBlank (ι := ι)))ᴴ = flagProj labelQueryBlank :=
  flagProj_conjTranspose _

/-- The marker keeps blank query registers (it is diagonal). -/
private lemma cpp_markR_commute (φ : ℂ) (hφ : star φ * φ = 1) (x : ι → Bool) :
    Commute ((cpp_markR φ hφ).run x) (flagProj labelQueryBlank) := by
  rw [cpp_markR_run]
  exact cpp_commute_phase (cpp_commute_flagProj _ _)

/-- Label states have blank query registers. -/
private lemma cpp_blank_labelVec (u : ι → ℂ) :
    flagProj labelQueryBlank *ᵥ labelVec u = labelVec u := by
  funext p
  rw [flagProj_mulVec, goodPart_apply]
  obtain ⟨k, t, w⟩ := p
  by_cases h : k = none ∧ t = none
  · simp [labelQueryBlank, h]
  · simp [labelQueryBlank, labelVec, h]

/-- The blank label has blank query registers. -/
private lemma cpp_blank_blankLabel :
    flagProj labelQueryBlank *ᵥ qBasis (blankLabel (ι := ι)) = qBasis blankLabel := by
  funext p
  rw [flagProj_mulVec, goodPart_apply]
  obtain ⟨k, t, w⟩ := p
  by_cases h : k = none ∧ t = none
  · simp [labelQueryBlank, h]
  · have : ((k, t, w) : QBasis ι Bool (Option ι)) ≠ blankLabel := by
      rintro ⟨⟩
      exact h ⟨rfl, rfl⟩
    simp [labelQueryBlank, h, this]

/-- The squared norm of a label state. -/
private lemma cpp_qNormSq_labelVec (u : ι → ℂ) :
    qNormSq (labelVec u) = ∑ i, Complex.normSq (u i) := by
  rw [qNormSq_def]
  simp [labelVec, Fintype.sum_prod_type, Fintype.sum_option]

/-- The uniform label state over a nonempty set is a unit vector. -/
private lemma cpp_isQState_indicator {T : Finset ι} (hT : T.Nonempty) :
    IsQState (labelVec fun i => if i ∈ T then ((1 / Real.sqrt T.card : ℝ) : ℂ) else 0) := by
  rw [IsQState, cpp_qNormSq_labelVec]
  have hc : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  simp only [apply_ite Complex.normSq, Complex.normSq_ofReal, Complex.normSq_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  field_simp
  rw [Real.sq_sqrt hc.le]

/-- The blank label is orthogonal to every label state. -/
private lemma cpp_qInner_blank_labelVec (u : ι → ℂ) :
    qInner (qBasis (blankLabel (ι := ι))) (labelVec u) = 0 := by
  rw [qInner_def, Finset.sum_eq_single (blankLabel (ι := ι))]
  · simp [labelVec, blankLabel]
  · intro q _ hq
    simp [qBasis_apply, hq]
  · simp

/-- The goodness flag of the marker on a label state keeps the marked labels. -/
private lemma cpp_goodPart_labelVec (x : ι → Bool) (u : ι → ℂ) :
    goodPart (cpp_mk x) (· = true) (labelVec u)
      = labelVec (fun i => if x i = true then u i else 0) := by
  funext p
  rw [goodPart_apply]
  obtain ⟨k, t, w⟩ := p
  rcases k with _ | k <;> rcases t with _ | t <;> rcases w with _ | w <;>
    simp [labelVec, cpp_mk, cpp_ansTrue, cpp_swapMap]

end CppLabel

/-! ## Proof of `exists_coherentPrep_blank`: the routine -/

section CppRoutine

/-- A scalar passes through `labelVec`. -/
private lemma cpp_labelVec_smul (c : ℂ) (u : ι → ℂ) : labelVec (c • u) = c • labelVec u := by
  funext p
  obtain ⟨k, t, w⟩ := p
  rcases k with _ | k <;> rcases t with _ | t <;> rcases w with _ | w <;> simp [labelVec]

/-- The uniform amplitudes over `S`. -/
private noncomputable def cpp_unif (S : Finset ι) : ι → ℂ :=
  fun i => if i ∈ S then ((1 / Real.sqrt S.card : ℝ) : ℂ) else 0

/-- The unit vector `(|blank⟩ + |s⟩)/√2`, whose reflection maps `|blank⟩` to `|s⟩`. -/
private noncomputable def cpp_w (S : Finset ι) : QBasis ι Bool (Option ι) → ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • (qBasis blankLabel + labelVec (cpp_unif S))

/-- The uniform state `|s⟩` over a nonempty `S` is a unit vector. -/
private lemma cpp_isQState_unif {S : Finset ι} (hS : S.Nonempty) :
    IsQState (labelVec (cpp_unif S)) :=
  cpp_isQState_indicator hS

/-- `(1/√2)² = 1/2`. -/
private lemma cpp_half : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = 1 / 2 := by
  rw [← Complex.ofReal_mul, div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast
  ring

/-- `(|blank⟩ + |s⟩)/√2` is a unit vector. -/
private lemma cpp_isQState_w {S : Finset ι} (hS : S.Nonempty) : IsQState (cpp_w S) := by
  rw [IsQState, cpp_w, qNormSq_smul, qNormSq_add, qNormSq_qBasis, cpp_isQState_unif hS,
    cpp_qInner_blank_labelVec, Complex.normSq_ofReal, Complex.zero_re, div_mul_div_comm, one_mul,
    Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The reflection about `(|blank⟩ + |s⟩)/√2` maps `|blank⟩` to `|s⟩`. -/
private lemma cpp_w_refl (S : Finset ι) :
    stateRefl (cpp_w S) *ᵥ qBasis blankLabel = labelVec (cpp_unif S) := by
  rw [stateRefl_mulVec, cpp_w, qInner_smul_left, qInner_add_left, qInner_self, qNormSq_qBasis,
    ← qInner_conj, cpp_qInner_blank_labelVec, star_zero, add_zero, smul_smul]
  have hc : 2 * (star ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 : ℝ) : ℂ)) * ((1 / Real.sqrt 2 : ℝ) : ℂ)
      = 1 := by
    rw [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_one, mul_one, mul_assoc, cpp_half]
    norm_num
  rw [hc, one_smul]
  abel

/-- `(|blank⟩ + |s⟩)/√2` has blank query registers. -/
private lemma cpp_blank_w (S : Finset ι) :
    flagProj labelQueryBlank *ᵥ cpp_w S = cpp_w S := by
  rw [cpp_w, Matrix.mulVec_smul, Matrix.mulVec_add, cpp_blank_blankLabel, cpp_blank_labelVec]

/-- The marked part of `|s⟩`. -/
private noncomputable def cpp_g (S : Finset ι) (x : ι → Bool) : QBasis ι Bool (Option ι) → ℂ :=
  goodPart (cpp_mk x) (· = true) (labelVec (cpp_unif S))

/-- The unmarked part of `|s⟩`. -/
private noncomputable def cpp_b (S : Finset ι) (x : ι → Bool) : QBasis ι Bool (Option ι) → ℂ :=
  badPart (cpp_mk x) (· = true) (labelVec (cpp_unif S))

/-- One Grover iteration: the marker with phase `−1`, then the reflection about `|s⟩`. -/
private noncomputable def cpp_groverR (S : Finset ι) (hS : S.Nonempty) :
    QRoutine ι Bool (Option ι) :=
  (cpp_markR (-1) (by norm_num)).comp
    (QRoutine.ofUnitary (stateRefl (labelVec (cpp_unif S)))
      (stateRefl_mem_unitaryGroup (cpp_isQState_unif hS)))

/-- **The base**: `|blank⟩ ↦ |s⟩`, then `k` Grover iterations; `2k` queries. -/
private noncomputable def cpp_baseR (S : Finset ι) (hS : S.Nonempty) (k : ℕ) :
    QRoutine ι Bool (Option ι) :=
  (QRoutine.ofUnitary (stateRefl (cpp_w S)) (stateRefl_mem_unitaryGroup (cpp_isQState_w hS))).comp
    ((cpp_groverR S hS).iterate k)

/-- The base makes `2k` queries. -/
private lemma cpp_baseR_len (S : Finset ι) (hS : S.Nonempty) (k : ℕ) :
    (cpp_baseR S hS k).len = 2 * k := by
  simp only [cpp_baseR, QRoutine.comp_len, QRoutine.ofUnitary_len, QRoutine.iterate_len,
    cpp_groverR, cpp_markR_len]
  ring

/-- The operator of the base. -/
private lemma cpp_baseR_run (S : Finset ι) (hS : S.Nonempty) (k : ℕ) (x : ι → Bool) :
    (cpp_baseR S hS k).run x
      = (stateRefl (labelVec (cpp_unif S)) * cpp_phase (-1) (flagProj (cpp_mk x))) ^ k
        * stateRefl (cpp_w S) := by
  rw [cpp_baseR, QRoutine.comp_run, QRoutine.iterate_run, cpp_groverR, QRoutine.comp_run,
    cpp_markR_run, QRoutine.ofUnitary_run, QRoutine.ofUnitary_run]

/-- The base keeps blank query registers. -/
private lemma cpp_baseR_commute (S : Finset ι) (hS : S.Nonempty) (k : ℕ) (x : ι → Bool) :
    Commute ((cpp_baseR S hS k).run x) (flagProj labelQueryBlank) := by
  rw [cpp_baseR_run]
  refine Commute.mul_left (Commute.pow_left (Commute.mul_left ?_ ?_) k) ?_
  · exact cpp_commute_stateRefl cpp_blank_conjTranspose (cpp_blank_labelVec _)
  · exact cpp_commute_phase (cpp_commute_flagProj _ _)
  · exact cpp_commute_stateRefl cpp_blank_conjTranspose (cpp_blank_w S)

/-- The base on the blank register: `α_k g + β_k b` [Geometry]. -/
private lemma cpp_baseR_mulVec (S : Finset ι) (hS : S.Nonempty) (k : ℕ) (x : ι → Bool) :
    (cpp_baseR S hS k).run x *ᵥ qBasis blankLabel
      = ((ampA (qNormSq (cpp_g S x)) k : ℝ) : ℂ) • cpp_g S x
        + ((ampB (qNormSq (cpp_g S x)) k : ℝ) : ℂ) • cpp_b S x := by
  rw [cpp_baseR_run, ← Matrix.mulVec_mulVec, cpp_w_refl]
  refine (groverSplit_parts (cpp_mk x) (· = true) (cpp_isQState_unif hS)).grover_pow_mulVec
    ?_ ?_ k
  · rw [cpp_phase_mulVec, flagProj_mulVec, goodPart_goodPart]
    module
  · rw [cpp_phase_mulVec, flagProj_mulVec, goodPart_badPart, smul_zero, sub_zero]

/-- `ω = e^{iπ/3}`. -/
private noncomputable def cpp_omega : ℂ := ⟨1 / 2, Real.sqrt 3 / 2⟩

/-- `|ω| = 1`. -/
private lemma cpp_omega_normSq : Complex.normSq cpp_omega = 1 := by
  have h3 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  rw [cpp_omega, Complex.normSq_mk]
  linear_combination (1 / 4 : ℝ) * h3

/-- `ω̄ ω = 1`. -/
private lemma cpp_omega_star : star cpp_omega * cpp_omega = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, cpp_omega_normSq, Complex.ofReal_one]

/-- `(1 − ω)² = −ω`, the identity behind the cubing of the failure. -/
private lemma cpp_omega_sq : (1 - cpp_omega) ^ 2 = -cpp_omega := by
  have h3 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  apply Complex.ext
  · simp [cpp_omega, sq]
    linear_combination (-1 / 4 : ℝ) * h3
  · simp [cpp_omega, sq]
    ring

/-- `S₀`: the phase `ω` on the blank register. Free. -/
private noncomputable def cpp_S0 : QRoutine ι Bool (Option ι) :=
  QRoutine.ofUnitary (cpp_phase cpp_omega (ketbra (qBasis blankLabel)))
    (cpp_phase_mem_unitaryGroup cpp_omega_star (isQProjector_ketbra (isQState_qBasis _)))

/-- **The π/3 recursion** [Gro05]: `U_{m+1} = U_m ; S_t ; U_m⁻¹ ; S_0 ; U_m`. -/
private noncomputable def cpp_levelR (U₀ : QRoutine ι Bool (Option ι)) :
    ℕ → QRoutine ι Bool (Option ι)
  | 0 => U₀
  | m + 1 => ((((cpp_levelR U₀ m).comp (cpp_markR cpp_omega cpp_omega_star)).comp
      (cpp_levelR U₀ m).inv).comp cpp_S0).comp (cpp_levelR U₀ m)

/-- `len(U_m) + 1 = 3^m (len(U_0) + 1)`. -/
private lemma cpp_levelR_len (U₀ : QRoutine ι Bool (Option ι)) (m : ℕ) :
    (cpp_levelR U₀ m).len + 1 = 3 ^ m * (U₀.len + 1) := by
  induction m with
  | zero => simp [cpp_levelR]
  | succ m ih =>
      simp only [cpp_levelR, QRoutine.comp_len, QRoutine.inv_len, cpp_markR_len]
      rw [show (cpp_S0 (ι := ι)).len = 0 from rfl,
        show 3 ^ (m + 1) * (U₀.len + 1) = 3 * (3 ^ m * (U₀.len + 1)) by ring, ← ih]
      ring

/-- The operator of one recursion level: `U S₀ U† S_t U`. -/
private lemma cpp_levelR_run_succ (U₀ : QRoutine ι Bool (Option ι)) (m : ℕ) (x : ι → Bool) :
    (cpp_levelR U₀ (m + 1)).run x
      = (cpp_levelR U₀ m).run x * (cpp_phase cpp_omega (ketbra (qBasis blankLabel))
        * (((cpp_levelR U₀ m).run x)ᴴ
          * (cpp_phase cpp_omega (flagProj (cpp_mk x)) * (cpp_levelR U₀ m).run x))) := by
  rw [cpp_levelR, QRoutine.comp_run, QRoutine.comp_run, QRoutine.comp_run, QRoutine.comp_run,
    QRoutine.inv_run, cpp_markR_run, cpp_S0, QRoutine.ofUnitary_run]

/-- Every level keeps blank query registers if the base does. -/
private lemma cpp_levelR_commute (U₀ : QRoutine ι Bool (Option ι)) (x : ι → Bool)
    (h0 : Commute (U₀.run x) (flagProj labelQueryBlank)) (m : ℕ) :
    Commute ((cpp_levelR U₀ m).run x) (flagProj labelQueryBlank) := by
  induction m with
  | zero => exact h0
  | succ m ih =>
      rw [cpp_levelR_run_succ]
      exact ih.mul_left
        ((cpp_commute_phase (cpp_commute_ketbra cpp_blank_conjTranspose
          cpp_blank_blankLabel)).mul_left
        ((cpp_commute_conjTranspose cpp_blank_conjTranspose ih).mul_left
        ((cpp_commute_phase (cpp_commute_flagProj _ _)).mul_left ih)))

/-- **The recursion cubes the failure**: the state stays `λ g + μ b` with `‖μ b‖² = ‖b‖^{2·3^m}`. -/
private lemma cpp_levelR_mulVec (U₀ : QRoutine ι Bool (Option ι)) (x : ι → Bool)
    {g b : QBasis ι Bool (Option ι) → ℂ} (hU₀ : U₀.run x *ᵥ qBasis blankLabel = g + b)
    (hg : flagProj (cpp_mk x) *ᵥ g = g) (hb : flagProj (cpp_mk x) *ᵥ b = 0) (m : ℕ) :
    ∃ l μ : ℂ, (cpp_levelR U₀ m).run x *ᵥ qBasis blankLabel = l • g + μ • b ∧
      qNormSq (μ • b) = qNormSq b ^ 3 ^ m := by
  induction m with
  | zero =>
      refine ⟨1, 1, ?_, ?_⟩
      · rw [one_smul, one_smul]
        exact hU₀
      · rw [one_smul, pow_zero, pow_one]
  | succ m ih =>
      obtain ⟨l, μ, h, hn⟩ := ih
      have hstep := cpp_pi3_step ((cpp_levelR U₀ m).run_mem_unitaryGroup x)
        (cpp_isQProjector_flagProj (cpp_mk x)) (isQState_qBasis blankLabel) h
        (by rw [Matrix.mulVec_smul, hg]) (by rw [Matrix.mulVec_smul, hb, smul_zero])
        cpp_omega_sq
      refine ⟨(cpp_omega * qNormSq (μ • b) - 1 + cpp_omega) * l,
        cpp_omega * qNormSq (μ • b) * μ, ?_, ?_⟩
      · rw [cpp_levelR_run_succ, hstep, smul_smul, smul_smul]
      · rw [← smul_smul, qNormSq_smul, hn, Complex.normSq_mul, cpp_omega_normSq,
          Complex.normSq_ofReal, pow_succ, pow_mul]
        ring

/-- `sin φ ≥ 1/4` on `[π/8, 7π/8]` (Jordan's inequality on both halves). -/
private lemma cpp_quarter_le_sin {φ : ℝ} (h1 : Real.pi / 8 ≤ φ) (h2 : φ ≤ 7 * Real.pi / 8) :
    1 / 4 ≤ Real.sin φ := by
  have hpi0 := Real.pi_pos
  have e : 2 / Real.pi * (Real.pi / 8) = 1 / 4 := by
    field_simp
    ring
  rcases le_total φ (Real.pi / 2) with hφ | hφ
  · have h := Real.mul_le_sin (by linarith) hφ
    have : 2 / Real.pi * (Real.pi / 8) ≤ 2 / Real.pi * φ := by gcongr
    linarith
  · rw [← Real.sin_pi_sub]
    have h := Real.mul_le_sin (x := Real.pi - φ) (by linarith) (by linarith)
    have : 2 / Real.pi * (Real.pi / 8) ≤ 2 / Real.pi * (Real.pi - φ) := by
      gcongr
      linarith
    linarith

/-- `θ ≤ (π/2) sin θ` on `[0, π/2]`. -/
private lemma cpp_le_pi_div_two_mul_sin {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2) :
    θ ≤ Real.pi / 2 * Real.sin θ := by
  have hpi0 := Real.pi_pos
  have h := mul_le_mul_of_nonneg_left (Real.mul_le_sin h0 h1) (half_pos hpi0).le
  have e : Real.pi / 2 * (2 / Real.pi * θ) = θ := by
    field_simp
  linarith

/-- The angle bounds of the base: with `p t² ∈ [1/2, 2]`, `t = √(a/r̂)` and `k = ⌊2t/5⌋ ≥ 1`,
`(2k + 1)√p ∈ [π/8, 7/4]`. -/
private lemma cpp_angle_bounds {k p t : ℝ} (hp0 : 0 < p) (hpt1 : p * t ^ 2 ≤ 2)
    (hpt2 : 1 / 2 ≤ p * t ^ 2) (hk1 : 1 ≤ k) (hkle : k ≤ 2 * t / 5) (hklt : 2 * t / 5 < k + 1) :
    Real.pi / 8 ≤ (2 * k + 1) * Real.sqrt p ∧ (2 * k + 1) * Real.sqrt p ≤ 7 / 4 := by
  have hpi' := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hss : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  have hs0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
  have ht52 : 5 / 2 ≤ t := by linarith
  have hkt : 3 / 5 * t ≤ 2 * k + 1 := by
    rcases le_total t 5 with ht5 | ht5 <;> linarith
  have hk6 : 2 * k + 1 ≤ 6 / 5 * t := by linarith
  have hk0 : 0 ≤ 2 * k + 1 := by linarith
  have hX : ((2 * k + 1) * Real.sqrt p) ^ 2 = (2 * k + 1) * (2 * k + 1) * p := by
    rw [mul_pow, hss]
    ring
  have hX0 : 0 ≤ (2 * k + 1) * Real.sqrt p := mul_nonneg hk0 hs0
  constructor
  · have hlo := mul_le_mul_of_nonneg_right (mul_le_mul hkt hkt (by linarith) hk0) hp0.le
    have e : 3 / 5 * t * (3 / 5 * t) * p = 9 / 25 * (p * t ^ 2) := by ring
    have hsq : 9 / 50 ≤ ((2 * k + 1) * Real.sqrt p) ^ 2 := by
      rw [hX]
      linarith
    have hpi8 : Real.pi / 8 * (Real.pi / 8) < 9 / 50 := by nlinarith
    by_contra hcon
    have := mul_self_lt_mul_self hX0 (lt_of_not_ge hcon)
    nlinarith
  · have hhi := mul_le_mul_of_nonneg_right (mul_le_mul hk6 hk6 hk0 (by linarith)) hp0.le
    have e : 6 / 5 * t * (6 / 5 * t) * p = 36 / 25 * (p * t ^ 2) := by ring
    have hsq : ((2 * k + 1) * Real.sqrt p) ^ 2 ≤ 72 / 25 := by
      rw [hX]
      linarith
    nlinarith

/-- **The base succeeds with probability at least `1/16`** when `r̂/2 ≤ r ≤ 2r̂`: the angle
`(2k + 1)θ` lies in `[π/8, 7π/8]`. -/
private lemma cpp_base_success {a r rh : ℕ} (hr : 0 < r) (hra : r ≤ a) (h1 : r ≤ 2 * rh)
    (h2 : rh ≤ 2 * r) :
    1 / 16 ≤ Real.sin ((2 * (prepIters a rh : ℝ) + 1) * groverAngle (r / a)) ^ 2 := by
  have ha : (0 : ℝ) < a := by exact_mod_cast hr.trans_le hra
  have hrh : (0 : ℝ) < rh := by exact_mod_cast (show 0 < rh by omega)
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have h1' : (r : ℝ) ≤ 2 * rh := by exact_mod_cast h1
  have h2' : (rh : ℝ) ≤ 2 * r := by exact_mod_cast h2
  have hra' : (r : ℝ) ≤ a := by exact_mod_cast hra
  have hp0 : (0 : ℝ) < r / a := div_pos hr' ha
  have hp1 : (r : ℝ) / a ≤ 1 := (div_le_one ha).mpr hra'
  have hsin : Real.sin (groverAngle (r / a)) = Real.sqrt (r / a) := sin_groverAngle hp1
  have hθ0 : 0 ≤ groverAngle (r / a) := Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _)
  have hθ1 : groverAngle (r / a) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have htt : Real.sqrt (a / rh) ^ 2 = a / rh := Real.sq_sqrt (div_pos ha hrh).le
  have hpt : (r : ℝ) / a * Real.sqrt (a / rh) ^ 2 = r / rh := by
    rw [htt]
    field_simp
  have hpt1 : (r : ℝ) / a * Real.sqrt (a / rh) ^ 2 ≤ 2 := by
    rw [hpt, div_le_iff₀ hrh]
    linarith
  have hpt2 : 1 / 2 ≤ (r : ℝ) / a * Real.sqrt (a / rh) ^ 2 := by
    rw [hpt, le_div_iff₀ hrh]
    linarith
  have hkle : (prepIters a rh : ℝ) ≤ 2 * Real.sqrt (a / rh) / 5 := Nat.floor_le (by positivity)
  have hklt : 2 * Real.sqrt (a / rh) / 5 < prepIters a rh + 1 := Nat.lt_floor_add_one _
  rcases Nat.eq_zero_or_pos (prepIters a rh) with hk0 | hk0
  · rw [hk0, Nat.cast_zero, mul_zero, zero_add, one_mul, hsin, Real.sq_sqrt hp0.le]
    rw [hk0, Nat.cast_zero, zero_add] at hklt
    have ht52 : Real.sqrt (a / rh) ^ 2 < 25 / 4 := by
      have := Real.sqrt_nonneg ((a : ℝ) / rh)
      nlinarith
    nlinarith [mul_lt_mul_of_pos_left ht52 hp0]
  · have hk1 : (1 : ℝ) ≤ prepIters a rh := by exact_mod_cast hk0
    obtain ⟨hlo, hhi⟩ := cpp_angle_bounds hp0 hpt1 hpt2 hk1 hkle hklt
    have hk0' : (0 : ℝ) ≤ 2 * prepIters a rh + 1 := by positivity
    have hθs := Real.sin_le hθ0
    have hθs' := cpp_le_pi_div_two_mul_sin hθ0 hθ1
    rw [hsin] at hθs hθs'
    have hpi0 := Real.pi_pos
    have hs := cpp_quarter_le_sin (φ := (2 * prepIters a rh + 1) * groverAngle (r / a))
      (hlo.trans (mul_le_mul_of_nonneg_left hθs hk0'))
      (by nlinarith [mul_le_mul_of_nonneg_left hθs' hk0'])
    nlinarith

/-- `(15/16)^{3^m} ≤ η²/2` for `m = prepLevels η`. -/
private lemma cpp_levels_bound {η : ℝ} (hη0 : 0 < η) :
    ((15 : ℝ) / 16) ^ 3 ^ prepLevels η ≤ η ^ 2 / 2 := by
  set N := ⌈Real.log (2 / η ^ 2) / Real.log (16 / 15)⌉₊
  have hN3 : N ≤ 3 ^ prepLevels η := Nat.le_pow_clog (by norm_num) N
  refine (pow_le_pow_of_le_one (by norm_num) (by norm_num) hN3).trans ?_
  have hl : 0 < Real.log (16 / 15) := Real.log_pos (by norm_num)
  have hNge : Real.log (2 / η ^ 2) ≤ N * Real.log (16 / 15) := by
    rw [← div_le_iff₀ hl]
    exact Nat.le_ceil _
  have hη2 : 0 < η ^ 2 / 2 := by positivity
  rw [← Real.log_le_log_iff (by positivity) hη2, Real.log_pow]
  have e1 : Real.log (15 / 16) = -Real.log (16 / 15) := by
    rw [← Real.log_inv]
    norm_num
  have e2 : Real.log (η ^ 2 / 2) = -Real.log (2 / η ^ 2) := by
    rw [← Real.log_inv, inv_div]
  rw [e1, e2]
  linarith

end CppRoutine

/-- **Clean coherent preparation keeping blank query registers** [CGKLPZ26, Lemma 2.4]: a routine
on the label register alone, chosen before the input, with at most `prepBudget a r̂ η` queries,
that on **every** input commutes with the projection onto blank query registers, and on every
input with `r̂/2 ≤ r ≤ 2r̂` maps the blank register to within `η` of `c·|u⟩`, for a phase `c`
depending on the input only. -/
theorem exists_coherentPrep_blank (S : Finset ι) {rh : ℕ} (hr0 : 0 < rh) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1) :
    ∃ R : QRoutine ι Bool (Option ι), R.len ≤ prepBudget S.card rh η ∧
      (∀ x : ι → Bool,
        R.run x * flagProj labelQueryBlank = flagProj labelQueryBlank * R.run x) ∧
      ∀ x : ι → Bool, (markedIn S x).card ≤ 2 * rh → rh ≤ 2 * (markedIn S x).card →
        ∃ c : ℂ, ‖c‖ = 1 ∧
          qNorm (R.run x *ᵥ qBasis blankLabel - c • labelVec (markedLabelState S x)) ≤ η := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine ⟨QRoutine.identity, Nat.zero_le _, fun x => ?_, fun x _ h2 => ?_⟩
    · rw [QRoutine.identity_run, Matrix.one_mul, Matrix.mul_one]
    · subst hS
      simp [markedIn] at h2
      omega
  refine ⟨cpp_levelR (cpp_baseR S hS (prepIters S.card rh)) (prepLevels η), ?_,
    fun x => (cpp_levelR_commute _ x (cpp_baseR_commute S hS _ x) _).eq, ?_⟩
  · have h := cpp_levelR_len (cpp_baseR S hS (prepIters S.card rh)) (prepLevels η)
    rw [cpp_baseR_len] at h
    rw [prepBudget, ← h]
    exact Nat.le_succ _
  intro x h1 h2
  have hr0 : 0 < (markedIn S x).card := by omega
  have hrS : (markedIn S x).card ≤ S.card := Finset.card_filter_le _ _
  have hr : (0 : ℝ) < (markedIn S x).card := by exact_mod_cast hr0
  have hu : IsQState (labelVec (markedLabelState S x)) :=
    cpp_isQState_indicator (Finset.card_pos.mp hr0)
  -- the marked part of `|s⟩` is `√(r/a) u`
  have hg_eq : cpp_g S x = ((Real.sqrt (markedIn S x).card / Real.sqrt S.card : ℝ) : ℂ)
      • labelVec (markedLabelState S x) := by
    rw [cpp_g, cpp_goodPart_labelVec, ← cpp_labelVec_smul]
    congr 1
    funext i
    simp only [cpp_unif, markedLabelState, Pi.smul_apply, smul_eq_mul]
    by_cases hm : i ∈ markedIn S x
    · obtain ⟨hi, hx⟩ := Finset.mem_filter.mp hm
      simp only [hx, hi, hm, ↓reduceIte]
      rw [← Complex.ofReal_mul]
      congr 1
      have := Real.sqrt_pos.mpr hr
      field_simp
    · by_cases hx : x i = true
      · have hi : i ∉ S := fun hi => hm (Finset.mem_filter.mpr ⟨hi, hx⟩)
        simp [hx, hi, hm]
      · simp [hx, hm]
  have hsplit := groverSplit_parts (cpp_mk x) (· = true) (cpp_isQState_unif hS)
  have hbn : qNormSq (cpp_b S x) = 1 - qNormSq (cpp_g S x) := hsplit.qNormSq_bad
  have hp1 : qNormSq (cpp_g S x) ≤ 1 := hsplit.qNormSq_good_le_one
  have hp : qNormSq (cpp_g S x) = (markedIn S x).card / S.card := by
    rw [hg_eq, qNormSq_smul, hu, Complex.normSq_ofReal, mul_one, div_mul_div_comm,
      Real.mul_self_sqrt (Nat.cast_nonneg _), Real.mul_self_sqrt (Nat.cast_nonneg _)]
  set p := qNormSq (cpp_g S x) with hpdef
  have hp0 : 0 ≤ p := qNormSq_nonneg _
  set k := prepIters S.card rh
  obtain ⟨l, μ, hrun, hnorm⟩ := cpp_levelR_mulVec (cpp_baseR S hS k) x
    (cpp_baseR_mulVec S hS k x)
    (by rw [Matrix.mulVec_smul, flagProj_mulVec, cpp_g, goodPart_goodPart])
    (by rw [Matrix.mulVec_smul, flagProj_mulVec, cpp_b, goodPart_badPart, smul_zero])
    (prepLevels η)
  -- the failure of the base is at most `15/16`
  have hε0 : qNormSq (((ampB p k : ℝ) : ℂ) • cpp_b S x) ≤ 15 / 16 := by
    rw [qNormSq_smul, Complex.normSq_ofReal, hbn]
    have hs : 1 / 16 ≤ Real.sin ((2 * (k : ℝ) + 1) * groverAngle p) ^ 2 := by
      have := cpp_base_success hr0 hrS h1 h2
      rwa [← hp] at this
    have hc : ampB p k * ampB p k * (1 - p)
        = Real.cos ((2 * (k : ℝ) + 1) * groverAngle p) ^ 2 := by
      rw [← mul_ampB_sq hp0 hp1 k]
      ring
    rw [hc]
    linarith [Real.sin_sq_add_cos_sq ((2 * (k : ℝ) + 1) * groverAngle p)]
  have hfail : qNormSq (μ • (((ampB p k : ℝ) : ℂ) • cpp_b S x)) ≤ η ^ 2 / 2 := by
    rw [hnorm]
    exact (pow_le_pow_left₀ (qNormSq_nonneg _) hε0 _).trans (cpp_levels_bound hη0)
  have hfinal : (cpp_levelR (cpp_baseR S hS k) (prepLevels η)).run x *ᵥ qBasis blankLabel
      = (l * ((ampA p k : ℂ) * ((Real.sqrt (markedIn S x).card / Real.sqrt S.card : ℝ) : ℂ)))
          • labelVec (markedLabelState S x) + μ • (((ampB p k : ℝ) : ℂ) • cpp_b S x) := by
    rw [hrun, ← hpdef, hg_eq, smul_smul, smul_smul, mul_assoc]
  have horth : qInner (labelVec (markedLabelState S x)) (μ • (((ampB p k : ℝ) : ℂ) • cpp_b S x))
      = 0 := by
    have hgu : goodPart (cpp_mk x) (· = true) (labelVec (markedLabelState S x))
        = labelVec (markedLabelState S x) := by
      rw [cpp_goodPart_labelVec]
      congr 1
      funext i
      by_cases hx : x i = true
      · simp [hx]
      · have hm : i ∉ markedIn S x := fun hm => hx (Finset.mem_filter.mp hm).2
        simp [hx, markedLabelState, hm]
    rw [qInner_smul_right, qInner_smul_right, ← hgu, cpp_b, qInner_goodPart_badPart, mul_zero,
      mul_zero]
  have hψ := IsQState.mulVec ((cpp_levelR (cpp_baseR S hS k) (prepLevels η)).run_mem_unitaryGroup x)
    (isQState_qBasis blankLabel)
  rw [hfinal] at hψ ⊢
  exact cpp_close_of_split hu hψ horth hη0 hη1 hfail

/-- **Clean coherent preparation** [CGKLPZ26, Lemma 2.4]: a routine on the label register alone,
chosen before the input, with at most `prepBudget a r̂ η` queries, that on every input with
`r̂/2 ≤ r ≤ 2r̂` maps the blank register to within `η` of `c·|u⟩`, for a phase `c` depending on
the input only. A corollary of `exists_coherentPrep_blank`. -/
theorem exists_coherentPrep (S : Finset ι) {rh : ℕ} (hr0 : 0 < rh) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1) :
    ∃ R : QRoutine ι Bool (Option ι), R.len ≤ prepBudget S.card rh η ∧
      ∀ x : ι → Bool, (markedIn S x).card ≤ 2 * rh → rh ≤ 2 * (markedIn S x).card →
        ∃ c : ℂ, ‖c‖ = 1 ∧
          qNorm (R.run x *ᵥ qBasis blankLabel - c • labelVec (markedLabelState S x)) ≤ η := by
  obtain ⟨R, hlen, -, hR⟩ := exists_coherentPrep_blank S hr0 hη0 hη1
  exact ⟨R, hlen, hR⟩

end QuantumQueryComplexity
