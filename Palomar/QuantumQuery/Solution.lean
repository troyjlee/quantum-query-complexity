/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import QuantumQueryComplexity.Quantum.Characterization
import QuantumQueryComplexity.Quantum.UniformHasDual
import QuantumQueryComplexity.Quantum.XorPolynomialMethod

/-!
# Adversary bounds and the polynomial method for quantum queries

Seven claims connect finite query algorithms to two lower-bound methods:
Boolean adversary strong duality and exact composition; a constant-factor
characterization in two oracle models; extraction from a supplied promise
dual; and degree bounds for acceptance probabilities in both models.

The query index has an idle value and the answer register a blank value.
The value oracle swaps blank with the input letter; the Boolean XOR oracle
fixes blank and XORs on ordinary answers. Workspaces are arbitrary finite
types. All unitary steps are input-independent; only queries access input.
Complexities count queries, with final basis measurement, not gates or time.

Sources: Høyer–Lee–Špalek (quant-ph/0611054v2, Theorems 2 and 13),
Reichardt (1005.1601v1, Theorem 1.3), Lee–Mittal–Reichardt–Špalek–Szegedy
(1011.3020v2, Theorems 3.4 and 4.1), Belovs–Lee (2004.06439v1,
Theorems 1 and 7), and Beals–Buhrman–Cleve–Mosca–de Wolf
(quant-ph/9802049v3, Lemma 4.2). See the metadata and
`docs/quantum-query/PAPER_CORRESPONDENCE.md` for exact scope and adaptations.
Constants are those proved here, not the papers' original constants.
The polynomial claims do not require the representing polynomial to be
multilinear. General state conversion and continuous-time queries are outside
this submission. The other algorithm families in the repository are not
selected by this Comparator configuration.
-/

namespace PalomarQuantumQuery

open Matrix
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

/-- The query, answer, and workspace registers; `none` means idle or blank. -/
abbrev Basis (ι σ W : Type) := Option ι × Option σ × W

/-- A finite quantum query algorithm with input-independent unitary steps. -/
structure Algorithm (ι σ O W : Type) [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] [Fintype W] [DecidableEq W] where
  /-- Initial amplitudes. -/
  init : Basis ι σ W → ℂ
  /-- The initial state has squared norm one. -/
  normalized : (∑ b, Complex.normSq (init b)) = 1
  /-- The step at time zero precedes all queries; other steps follow a query. -/
  step : ℕ → Matrix (Basis ι σ W) (Basis ι σ W) ℂ
  /-- Each step is unitary. -/
  unitary : ∀ t, step t ∈ Matrix.unitaryGroup (Basis ι σ W) ℂ
  /-- Classical output of the final basis measurement. -/
  readout : Basis ι σ W → O

variable {ι σ O W X : Type} [Fintype ι] [DecidableEq ι]
  [Fintype σ] [DecidableEq σ] [Fintype W] [DecidableEq W]

/-- The value oracle swaps blank with the queried letter and fixes idle. -/
def valueMap (a : ι → σ) : Basis ι σ W → Basis ι σ W
  | (none, t, w) => (none, t, w)
  | (some i, t, w) => (some i, Equiv.swap none (some (a i)) t, w)

/-- State after exactly `q` value queries. The oracle is an involution. -/
def valueState (A : Algorithm ι σ O W) (a : ι → σ) : ℕ → Basis ι σ W → ℂ
  | 0 => A.step 0 *ᵥ A.init
  | q + 1 => A.step (q + 1) *ᵥ (fun b => valueState A a q (valueMap a b))

/-- XOR on ordinary Boolean answers, fixing the blank answer. -/
def xorMap (a : ι → Bool) : Basis ι Bool W → Basis ι Bool W
  | (some i, some b, w) => (some i, some (xor b (a i)), w)
  | b => b

/-- State after exactly `q` XOR queries, with idle and blank sectors. -/
def xorState (A : Algorithm ι Bool O W) (a : ι → Bool) : ℕ → Basis ι Bool W → ℂ
  | 0 => A.step 0 *ᵥ A.init
  | q + 1 => A.step (q + 1) *ᵥ (fun b => xorState A a q (xorMap a b))

/-- Probability of a readout value under computational-basis measurement. -/
def probability [DecidableEq O] (readout : Basis ι σ W → O)
    (state : Basis ι σ W → ℂ) (o : O) : ℝ :=
  ∑ b, if readout b = o then Complex.normSq (state b) else 0

/-- Minimum achievable value-query count on observations `read`, at error `ε`.
The submitted bounds establish feasibility; the natural infimum is then a minimum. -/
def valueComplexity [DecidableEq O] (read : X → ι → σ) (f : X → O) (ε : ℝ) : ℕ :=
  sInf {q | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (A : Algorithm ι σ O V), ∀ x,
      1 - ε ≤ probability A.readout (valueState A (read x) q) (f x)}

/-- Minimum achievable XOR-query count on observations `read`, at error `ε`. -/
def xorComplexity [DecidableEq O] (read : X → ι → Bool) (f : X → O) (ε : ℝ) : ℕ :=
  sInf {q | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (A : Algorithm ι Bool O V), ∀ x,
      1 - ε ≤ probability A.readout (xorState A (read x) q) (f x)}

/-- Difference mask for coordinate `i` on the Boolean input cube. -/
def difference (i : ι) : Matrix (ι → Bool) (ι → Bool) ℝ :=
  Matrix.of fun x y => if x i = y i then 0 else 1

/-- Negative-weight adversary bound, using real symmetric matrices and L2 norm. -/
def adversary (f : (ι → Bool) → Bool) : ℝ :=
  sSup {r | ∃ Γ : Matrix (ι → Bool) (ι → Bool) ℝ,
    (Γ.IsHermitian ∧ ∀ x y, f x = f y → Γ x y = 0) ∧
    (∀ i, ‖Γ ⊙ difference i‖ ≤ 1) ∧ r = ‖Γ‖}

/-- A pair of real vector families satisfying all filtered dual constraints,
including zero on equal-output pairs, with both squared-norm costs at most `c`. -/
def DualFeasible [DecidableEq O] (K : Type) [Fintype K]
    (read : X → ι → σ) (f : X → O) (c : ℝ) : Prop :=
  ∃ u v : X → ι → K → ℝ,
    (∀ x y, (∑ i, if read x i = read y i then 0 else ∑ k, u x i k * v y i k)
      = if f x = f y then 0 else 1) ∧
    (∀ x, ∑ i, ∑ k, u x i k * u x i k ≤ c) ∧
    (∀ x, ∑ i, ∑ k, v x i k * v x i k ≤ c)

/-- Infimum of feasible nonnegative dual costs in all finite dimensions. -/
def dual (f : (ι → Bool) → Bool) : ℝ :=
  sInf {c | 0 ≤ c ∧ ∃ n : ℕ, DualFeasible (Fin n) id f c}

/-! ## Bridges to the proof library (not imported by the Challenge) -/

private def Algorithm.toLibrary (A : Algorithm ι σ O W) :
    QuantumQueryComplexity.QAlg ι σ O W :=
  ⟨A.init, A.normalized, A.step, A.unitary, A.readout⟩

private def Algorithm.ofLibrary (A : QuantumQueryComplexity.QAlg ι σ O W) :
    Algorithm ι σ O W :=
  ⟨A.init, A.init_isQState, A.step, A.step_unitary, A.readout⟩

private theorem to_ofLibrary (A : QuantumQueryComplexity.QAlg ι σ O W) :
    (Algorithm.ofLibrary A).toLibrary = A := by
  cases A
  rfl

private theorem valueState_toLibrary (A : Algorithm ι σ O W) (a : ι → σ) (q : ℕ) :
    valueState A a q = A.toLibrary.state a q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [valueState, QuantumQueryComplexity.QAlg.state_succ]
    change A.step (q + 1) *ᵥ _ = A.step (q + 1) *ᵥ _
    congr 1
    funext b
    rw [QuantumQueryComplexity.oracleMat_mulVec_apply, ← ih]
    rfl

private theorem xorMap_eq (a : ι → Bool) :
    xorMap (W := W) a = QuantumQueryComplexity.xorOracleMap a := by
  funext b
  rcases b with ⟨i, t, w⟩
  cases i <;> cases t <;> rfl

private theorem xorState_toLibrary (A : Algorithm ι Bool O W) (a : ι → Bool) (q : ℕ) :
    xorState A a q = QuantumQueryComplexity.xorState A.toLibrary a q := by
  classical
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [xorState, QuantumQueryComplexity.xorState_succ]
    change A.step (q + 1) *ᵥ _ = A.step (q + 1) *ᵥ _
    congr 1
    funext b
    rw [QuantumQueryComplexity.xorOracleMat_mulVec_apply, ← ih, xorMap_eq]

private theorem valueProbability_toLibrary [DecidableEq O]
    (A : Algorithm ι σ O W) (a : ι → σ) (q : ℕ) (o : O) :
    probability A.readout (valueState A a q) o = A.toLibrary.prob a q o := by
  rw [valueState_toLibrary]
  rfl

private theorem xorProbability_toLibrary [DecidableEq O]
    (A : Algorithm ι Bool O W) (a : ι → Bool) (q : ℕ) (o : O) :
    probability A.readout (xorState A a q) o =
      QuantumQueryComplexity.qProb A.toLibrary.readout
        (QuantumQueryComplexity.xorState A.toLibrary a q) o := by
  rw [xorState_toLibrary]
  rfl

private theorem valueComplexity_eq [Fintype X] [DecidableEq O]
    (read : X → ι → σ) (f : X → O) (ε : ℝ) :
    valueComplexity read f ε = QuantumQueryComplexity.qQueryOn read f ε := by
  unfold valueComplexity QuantumQueryComplexity.qQueryOn
  congr 1
  ext q
  constructor
  · rintro ⟨V, hV, hV', A, hA⟩
    refine ⟨V, hV, hV', A.toLibrary, ?_⟩
    intro x
    have hx := hA x
    rw [valueProbability_toLibrary] at hx
    exact hx
  · rintro ⟨V, hV, hV', A, hA⟩
    refine ⟨V, hV, hV', Algorithm.ofLibrary A, ?_⟩
    intro x
    rw [valueProbability_toLibrary, to_ofLibrary]
    exact hA x

private theorem xorComplexity_eq [Fintype X] [DecidableEq O]
    (read : X → ι → Bool) (f : X → O) (ε : ℝ) :
    xorComplexity read f ε = QuantumQueryComplexity.xorQQueryOn read f ε := by
  unfold xorComplexity QuantumQueryComplexity.xorQQueryOn
  congr 1
  ext q
  constructor
  · rintro ⟨V, hV, hV', A, hA⟩
    refine ⟨V, hV, hV', A.toLibrary, ?_⟩
    intro x
    have hx := hA x
    rw [xorProbability_toLibrary] at hx
    exact hx
  · rintro ⟨V, hV, hV', A, hA⟩
    refine ⟨V, hV, hV', Algorithm.ofLibrary A, ?_⟩
    intro x
    rw [xorProbability_toLibrary, to_ofLibrary]
    exact hA x

private theorem adversary_eq (f : (ι → Bool) → Bool) :
    adversary f = QuantumQueryComplexity.advPM f := rfl

private theorem dual_eq (f : (ι → Bool) → Bool) :
    dual f = QuantumQueryComplexity.advDual f := by
  unfold dual QuantumQueryComplexity.advDual
  congr 1
  ext c
  constructor
  · rintro ⟨hc, n, u, v, hcon, hu, hv⟩
    exact ⟨hc, n, ⟨u, v, hcon⟩, hu, hv⟩
  · rintro ⟨hc, n, P, hu, hv⟩
    exact ⟨hc, n, P.u, P.v, P.constraint, hu, hv⟩

/-- Boolean-output specialization of LMRSS Theorem 3.4, also BL Theorem 7:
the all-pairs filtered dual has exactly the primal value. -/
theorem strong_duality (f : (ι → Bool) → Bool) : dual f = adversary f := by
  rw [dual_eq, adversary_eq]
  exact QuantumQueryComplexity.advDual_eq_advPM f

/-- Exact uniform block composition, BL Theorem 1; HLS Theorem 13 gives the
lower direction. Both functions are total and Boolean, including constant cases. -/
theorem composition {κ : Type} [Fintype κ] [DecidableEq κ]
    (f : (ι → Bool) → Bool) (g : (κ → Bool) → Bool) :
    adversary (fun x : (ι × κ) → Bool => f (fun i => g (fun j => x (i, j))))
      = adversary f * adversary g := by
  exact QuantumQueryComplexity.advPM_composeFun_eq f g

/-- The total Boolean adversary characterization at error 1/3, adapted to
the value oracle with explicit constants; Reichardt Theorem 1.3 and HLS Theorem 2. -/
theorem value_characterization (f : (ι → Bool) → Bool) :
    (1 / 36 : ℝ) * adversary f ≤ (valueComplexity id f (1 / 3) : ℝ) ∧
    (valueComplexity id f (1 / 3) : ℝ) ≤ 2 ^ 14 * adversary f := by
  simp only [valueComplexity_eq, adversary_eq]
  exact QuantumQueryComplexity.boundedErrorQQuery_characterized_by_advPM f

/-- The Boolean XOR version, by factor-two simulations both ways. The idle
and blank sectors are explicit; removal of these sectors is not a submitted claim. -/
theorem xor_characterization (f : (ι → Bool) → Bool) :
    (1 / 72 : ℝ) * adversary f ≤ (xorComplexity id f (1 / 3) : ℝ) ∧
    (xorComplexity id f (1 / 3) : ℝ) ≤ 2 ^ 15 * adversary f := by
  simp only [xorComplexity_eq, adversary_eq]
  exact QuantumQueryComplexity.xorQQuery_characterized_by_advPM f

/-- Function-evaluation specialization of LMRSS Theorem 4.1: a supplied dual
gives an algorithm, uniformly in alphabet and output size. No general
state-conversion or finite-output adversary equality is asserted here. -/
theorem uniform_dual_upper_bound [Fintype X] [DecidableEq O] [Nonempty O]
    {K : Type} [Fintype K] (read : X → ι → σ) (f : X → O) {c : ℝ}
    (hc : 0 ≤ c) (h : DualFeasible K read f c) :
    (valueComplexity read f (1 / 3) : ℝ) ≤ 8192 * (1 + c) := by
  obtain ⟨u, v, hcon, hu, hv⟩ := h
  rw [valueComplexity_eq]
  exact QuantumQueryComplexity.qQueryOn_third_le_of_hasDualOn_uniform
    ⟨K, inferInstance, ⟨u, v, hcon⟩, hu, hv⟩ hc

/-- BBCMW Lemma 4.2 in the value-oracle model: every output probability is
represented on the Boolean cube by a real polynomial of degree at most `2q`. -/
theorem value_probability_polynomial [DecidableEq O]
    (A : Algorithm ι Bool O W) (q : ℕ) (o : O) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * q ∧ ∀ a : ι → Bool,
      MvPolynomial.eval (fun i => if a i then (1 : ℝ) else 0) p
        = probability A.readout (valueState A a q) o := by
  obtain ⟨p, hdeg, hp⟩ := A.toLibrary.exists_probability_polynomial q o
  refine ⟨p, hdeg, fun a => ?_⟩
  rw [valueProbability_toLibrary]
  exact hp a

/-- BBCMW Lemma 4.2 directly in the XOR model: degree `2q`, with no simulation
loss. Multilinearity is not part of this statement. -/
theorem xor_probability_polynomial [DecidableEq O]
    (A : Algorithm ι Bool O W) (q : ℕ) (o : O) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * q ∧ ∀ a : ι → Bool,
      MvPolynomial.eval (fun i => if a i then (1 : ℝ) else 0) p
        = probability A.readout (xorState A a q) o := by
  obtain ⟨p, hdeg, hp⟩ := QuantumQueryComplexity.exists_xor_probability_polynomial A.toLibrary q o
  refine ⟨p, hdeg, fun a => ?_⟩
  rw [xorProbability_toLibrary]
  exact hp a

end
end PalomarQuantumQuery
