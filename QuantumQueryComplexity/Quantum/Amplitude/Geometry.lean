import QuantumQueryComplexity.Quantum.FiniteHilbert
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The two-reflection rotation of amplitude amplification

On a finite complex Hilbert space, let `ψ = g + b` be a unit vector split into an
(unnormalized) good part `g` and bad part `b`, orthogonal to each other, and let
`p = ‖g‖²`.  If `S` negates `g` and fixes `b` — only these two vectors matter, so a
clean-ancilla marker qualifies as much as a full `I − 2Π` — then the Grover iterate

    G = (2|ψ⟩⟨ψ| − I) · S

preserves the span of `g` and `b`:

    G g = (1 − 2p)·g − 2p·b,        G b = 2(1 − p)·g + (1 − 2p)·b,

so `G^j ψ = α_j·g + β_j·b` for the real sequences `ampA p`, `ampB p` of that recurrence.
Working with the **unnormalized** parts avoids every division: `p = 0` and `p = 1` are
covered by the same statement.  With `p = sin² θ`,

    sin θ · α_j = sin((2j+1)θ),      cos θ · β_j = cos((2j+1)θ),

hence the success mass `p·α_j² = sin²((2j+1)θ)`.  The successful component of `G^j ψ` is
`α_j·g`, a scalar multiple of the original successful component: amplification preserves
the conditional law of the output.

The sign convention of `G` is exactly the displayed one; `−G` would have the same
uncontrolled statistics but different eigenphases, which matters for amplitude estimation.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H : Type} [Fintype H] [DecidableEq H]

/-! ## The rank-one projector and the reflection about a state -/

/-- `|ψ⟩⟨ψ|`. -/
def ketbra (ψ : H → ℂ) : Matrix H H ℂ := Matrix.vecMulVec ψ (star ψ)

lemma ketbra_mulVec (ψ φ : H → ℂ) : ketbra ψ *ᵥ φ = qInner ψ φ • ψ := by
  funext h
  simp only [ketbra, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, qInner_def,
    Pi.smul_apply, smul_eq_mul, Pi.star_apply]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma isQProjector_ketbra {ψ : H → ℂ} (hψ : IsQState ψ) : IsQProjector (ketbra ψ) := by
  constructor
  · ext h k
    simp [ketbra, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]
  · rw [ketbra, Matrix.vecMulVec_mul_vecMulVec]
    have h1 : star ψ ⬝ᵥ ψ = (1 : ℂ) := by
      have := qInner_self ψ
      rw [qInner, hψ] at this
      simpa using this
    rw [h1, one_smul]

/-- A unitary conjugates `|η⟩⟨η|` to `|Pη⟩⟨Pη|`. -/
lemma mul_ketbra_mul_conjTranspose (P : Matrix H H ℂ) (η : H → ℂ) :
    P * ketbra η * Pᴴ = ketbra (P *ᵥ η) := by
  rw [ketbra, ketbra, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

/-- The reflection about the unit vector `ψ`: `2|ψ⟩⟨ψ| − I`. -/
def stateRefl (ψ : H → ℂ) : Matrix H H ℂ := qRefl (ketbra ψ)

lemma stateRefl_mem_unitaryGroup {ψ : H → ℂ} (hψ : IsQState ψ) :
    stateRefl ψ ∈ Matrix.unitaryGroup H ℂ :=
  qRefl_mem_unitaryGroup (isQProjector_ketbra hψ)

lemma stateRefl_mulVec (ψ φ : H → ℂ) :
    stateRefl ψ *ᵥ φ = (2 * qInner ψ φ) • ψ - φ := by
  rw [stateRefl, qRefl, Matrix.sub_mulVec, Matrix.smul_mulVec, ketbra_mulVec,
    Matrix.one_mulVec, smul_smul]

/-- Conjugating the reflection about `η` by a unitary `P` reflects about `Pη`. -/
lemma mul_stateRefl_mul_conjTranspose {P : Matrix H H ℂ}
    (hP : P ∈ Matrix.unitaryGroup H ℂ) (η : H → ℂ) :
    P * stateRefl η * Pᴴ = stateRefl (P *ᵥ η) := by
  have hPP : P * Pᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hP
    rwa [Matrix.star_eq_conjTranspose] at this
  rw [stateRefl, stateRefl, qRefl, qRefl, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, mul_ketbra_mul_conjTranspose, Matrix.mul_one, hPP]

/-! ## The coefficient sequences -/

/-- The coefficients `(α_j, β_j)` of the good and bad parts after `j` iterations. -/
noncomputable def ampPair (p : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 1)
  | j + 1 => ((1 - 2 * p) * (ampPair p j).1 + 2 * (1 - p) * (ampPair p j).2,
      -(2 * p) * (ampPair p j).1 + (1 - 2 * p) * (ampPair p j).2)

/-- The coefficient of the good part after `j` iterations. -/
noncomputable def ampA (p : ℝ) (j : ℕ) : ℝ := (ampPair p j).1
/-- The coefficient of the bad part after `j` iterations. -/
noncomputable def ampB (p : ℝ) (j : ℕ) : ℝ := (ampPair p j).2

@[simp] lemma ampA_zero (p : ℝ) : ampA p 0 = 1 := rfl
@[simp] lemma ampB_zero (p : ℝ) : ampB p 0 = 1 := rfl
lemma ampA_succ (p : ℝ) (j : ℕ) :
    ampA p (j + 1) = (1 - 2 * p) * ampA p j + 2 * (1 - p) * ampB p j := rfl
lemma ampB_succ (p : ℝ) (j : ℕ) :
    ampB p (j + 1) = -(2 * p) * ampA p j + (1 - 2 * p) * ampB p j := rfl

/-- **The rotation, without division**: with `p = sin² θ`. -/
theorem sin_mul_ampA_and_cos_mul_ampB (θ : ℝ) (j : ℕ) :
    Real.sin θ * ampA (Real.sin θ ^ 2) j = Real.sin ((2 * j + 1) * θ) ∧
    Real.cos θ * ampB (Real.sin θ ^ 2) j = Real.cos ((2 * j + 1) * θ) := by
  induction j with
  | zero => simp
  | succ j ih =>
      obtain ⟨hs, hc⟩ := ih
      have hangle : (2 * ((j + 1 : ℕ) : ℝ) + 1) * θ = (2 * (j : ℝ) + 1) * θ + 2 * θ := by
        push_cast; ring
      have h1 := Real.sin_sq_add_cos_sq θ
      rw [ampA_succ, ampB_succ, hangle, Real.sin_add, Real.cos_add, Real.sin_two_mul,
        Real.cos_two_mul, ← hs, ← hc]
      constructor
      · linear_combination (-(2 * Real.sin θ * ampA (Real.sin θ ^ 2) j
          + 2 * Real.sin θ * ampB (Real.sin θ ^ 2) j)) * h1
      · linear_combination (-(2 * Real.cos θ * ampB (Real.sin θ ^ 2) j)) * h1

lemma sin_mul_ampA (θ : ℝ) (j : ℕ) :
    Real.sin θ * ampA (Real.sin θ ^ 2) j = Real.sin ((2 * j + 1) * θ) :=
  (sin_mul_ampA_and_cos_mul_ampB θ j).1

lemma cos_mul_ampB (θ : ℝ) (j : ℕ) :
    Real.cos θ * ampB (Real.sin θ ^ 2) j = Real.cos ((2 * j + 1) * θ) :=
  (sin_mul_ampA_and_cos_mul_ampB θ j).2

/-- The Grover angle of a probability: `θ = arcsin √p`. -/
noncomputable def groverAngle (p : ℝ) : ℝ := Real.arcsin (Real.sqrt p)

lemma sin_groverAngle {p : ℝ} (h1 : p ≤ 1) :
    Real.sin (groverAngle p) = Real.sqrt p := by
  rw [groverAngle, Real.sin_arcsin]
  · linarith [Real.sqrt_nonneg p]
  · exact Real.sqrt_le_one.mpr h1 |>.trans_eq rfl

lemma sin_sq_groverAngle {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    Real.sin (groverAngle p) ^ 2 = p := by
  rw [sin_groverAngle h1, Real.sq_sqrt h0]

lemma cos_groverAngle_nonneg (p : ℝ) : 0 ≤ Real.cos (groverAngle p) :=
  Real.cos_arcsin_nonneg _

/-- **The success mass after `j` iterations is `sin²((2j+1)θ)`**, for every `0 ≤ p ≤ 1`
(the endpoints included). -/
theorem mul_ampA_sq {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (j : ℕ) :
    p * ampA p j ^ 2 = Real.sin ((2 * j + 1) * groverAngle p) ^ 2 := by
  have h := sin_mul_ampA (groverAngle p) j
  rw [sin_sq_groverAngle h0 h1] at h
  rw [← h, mul_pow, sin_sq_groverAngle h0 h1]

/-- The bad mass, likewise. -/
theorem mul_ampB_sq {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (j : ℕ) :
    (1 - p) * ampB p j ^ 2 = Real.cos ((2 * j + 1) * groverAngle p) ^ 2 := by
  have h := cos_mul_ampB (groverAngle p) j
  rw [sin_sq_groverAngle h0 h1] at h
  rw [← h, mul_pow, Real.cos_sq', sin_sq_groverAngle h0 h1]

/-! ## The invariant plane -/

/-- The data of one amplification problem in a Hilbert space: a unit vector split into
orthogonal good and bad parts. -/
structure GroverSplit (ψ g b : H → ℂ) : Prop where
  /-- `ψ` is a unit vector. -/
  unit : IsQState ψ
  /-- The split. -/
  split : ψ = g + b
  /-- The parts are orthogonal. -/
  orth : qInner g b = 0

namespace GroverSplit

variable {ψ g b : H → ℂ}

lemma qInner_good (h : GroverSplit ψ g b) : qInner ψ g = ((qNormSq g : ℝ) : ℂ) := by
  rw [h.split, qInner_add_left, qInner_self, ← qInner_conj g b, h.orth]
  simp

lemma qNormSq_bad (h : GroverSplit ψ g b) : qNormSq b = 1 - qNormSq g := by
  have := qNormSq_add g b
  rw [← h.split, h.unit, h.orth] at this
  simp only [Complex.zero_re, mul_zero, add_zero] at this
  linarith

lemma qInner_bad (h : GroverSplit ψ g b) : qInner ψ b = ((1 - qNormSq g : ℝ) : ℂ) := by
  rw [h.split, qInner_add_left, qInner_self, h.orth, h.qNormSq_bad]
  simp

lemma qNormSq_good_le_one (h : GroverSplit ψ g b) : qNormSq g ≤ 1 := by
  have := h.qNormSq_bad
  have := qNormSq_nonneg b
  linarith

/-- **One iterate on the good part.** -/
theorem iterate_good (h : GroverSplit ψ g b) {S : Matrix H H ℂ} (hSg : S *ᵥ g = -g) :
    (stateRefl ψ * S) *ᵥ g
      = ((1 - 2 * qNormSq g : ℝ) : ℂ) • g - ((2 * qNormSq g : ℝ) : ℂ) • b := by
  rw [← Matrix.mulVec_mulVec, hSg, Matrix.mulVec_neg, stateRefl_mulVec, h.qInner_good]
  rw [h.split]
  push_cast
  module

/-- **One iterate on the bad part.** -/
theorem iterate_bad (h : GroverSplit ψ g b) {S : Matrix H H ℂ} (hSb : S *ᵥ b = b) :
    (stateRefl ψ * S) *ᵥ b
      = ((2 * (1 - qNormSq g) : ℝ) : ℂ) • g + ((1 - 2 * qNormSq g : ℝ) : ℂ) • b := by
  rw [← Matrix.mulVec_mulVec, hSb, stateRefl_mulVec, h.qInner_bad]
  rw [h.split]
  push_cast
  module

/-- **The rotation**: any operator acting on `g` and `b` as the Grover iterate does moves
`ψ` to `α_j·g + β_j·b`. -/
theorem pow_mulVec_of_action (h : GroverSplit ψ g b) {G : Matrix H H ℂ}
    (hGg : G *ᵥ g = ((1 - 2 * qNormSq g : ℝ) : ℂ) • g - ((2 * qNormSq g : ℝ) : ℂ) • b)
    (hGb : G *ᵥ b = ((2 * (1 - qNormSq g) : ℝ) : ℂ) • g
      + ((1 - 2 * qNormSq g : ℝ) : ℂ) • b) (j : ℕ) :
    (G ^ j) *ᵥ ψ = ((ampA (qNormSq g) j : ℝ) : ℂ) • g + ((ampB (qNormSq g) j : ℝ) : ℂ) • b := by
  induction j with
  | zero => simp [h.split]
  | succ j ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_smul, hGg, hGb, ampA_succ, ampB_succ]
      push_cast
      module

/-- **The Grover iterate `(2|ψ⟩⟨ψ| − I)·S`**, for a marker correct on `g` and `b`. -/
theorem grover_pow_mulVec (h : GroverSplit ψ g b) {S : Matrix H H ℂ} (hSg : S *ᵥ g = -g)
    (hSb : S *ᵥ b = b) (j : ℕ) :
    ((stateRefl ψ * S) ^ j) *ᵥ ψ
      = ((ampA (qNormSq g) j : ℝ) : ℂ) • g + ((ampB (qNormSq g) j : ℝ) : ℂ) • b :=
  h.pow_mulVec_of_action (h.iterate_good hSg) (h.iterate_bad hSb) j

end GroverSplit

end QuantumQueryComplexity
