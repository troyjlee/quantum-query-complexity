import QuantumQueryComplexity.Quantum.PolynomialLowerBound

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Acceptance: the polynomial method

Statement pins and boundary checks for `Polynomial/Boolean.lean`,
`Quantum/PolynomialMethod.lean`, `Quantum/XorPolynomialMethod.lean` and
`Quantum/PolynomialLowerBound.lean`.

1. **The `2·T` theorem**, native and XOR oracle alike (never `4·T`), for arbitrary finite
   index types, any output type, every query count including `0`.
2. **Zero queries**: the probability polynomial is constant; the empty index type and the
   constant algorithm are admitted.
3. **One exact query**: `projAlg` reads one bit; its acceptance polynomial for the answer
   `some true` has degree at most `2` and evaluates to that bit.
4. **The correctness bridge** at `ε = 0`, on a noninjective promise map, with the `[0, 1]`
   bounds holding on the whole cube.
5. **Lower-bound interfaces**: every complexity-level theorem carries an explicit
   nonemptiness hypothesis or discharges it from read-determinacy and `0 ≤ ε`.
6. **A worked obstruction**: no constant approximates a nonconstant bit within `ε < 1/2`,
   hence `1 ≤ Q_ε(xᵢ)` from the polynomial method alone.

Axioms are checked by the committed audit, run on every CI run:

    lake env lean --trust=0 QuantumQueryComplexity/Test/PolynomialAxioms.lean

Every declaration of the four production modules and of this file may depend only on
`propext`, `Classical.choice`, `Quot.sound`, transitively.
-/

namespace QuantumQueryComplexity
namespace PolynomialMethodAcceptance

/-! ## 1. The `2·T` theorem -/

theorem acceptance_degree_native :
    ∀ {ι O W : Type} [Fintype ι] [DecidableEq ι] [DecidableEq O] [Fintype W] [DecidableEq W]
      (A : QAlg ι Bool O W) (t : ℕ) (o : O),
      ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧ ∀ a, evalBool p a = A.prob a t o :=
  fun A t o => A.exists_probability_polynomial t o

theorem acceptance_degree_xor :
    ∀ {ι O W : Type} [Fintype ι] [DecidableEq ι] [DecidableEq O] [Fintype W] [DecidableEq W]
      (A : QAlg ι Bool O W) (t : ℕ) (o : O),
      ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧
        ∀ a, evalBool p a = qProb A.readout (xorState A a t) o :=
  fun A t o => exists_xor_probability_polynomial A t o

/-- The amplitude-level statement: degree at most `t` for both parts. -/
theorem acceptance_amplitudes :
    ∀ {ι O W : Type} [Fintype ι] [DecidableEq ι] [DecidableEq O] [Fintype W] [DecidableEq W]
      (A : QAlg ι Bool O W) (t : ℕ),
      ∃ Φ : QBasis ι Bool W → AmpPoly ι, (∀ b, (Φ b).DegLe t) ∧
        ∀ a b, (Φ b).evalC a = A.state a t b :=
  fun A t => A.hasAmpPoly_state t

/-! ## 2. Zero queries -/

/-- At `t = 0` the polynomial has degree `0`: it is constant, so the probability does not
depend on the input. -/
example {ι O W : Type} [Fintype ι] [DecidableEq ι] [DecidableEq O] [Fintype W] [DecidableEq W]
    (A : QAlg ι Bool O W) (o : O) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree = 0 ∧ ∀ a a', evalBool p a = evalBool p a' := by
  obtain ⟨p, hdeg, -⟩ := A.exists_probability_polynomial 0 o
  refine ⟨p, Nat.le_zero.mp (by simpa using hdeg), fun a a' => ?_⟩
  have hC : p = MvPolynomial.C (p.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp (by simpa using hdeg))
  rw [hC, evalBool_C, evalBool_C]

/-- The empty index type. -/
example {O W : Type} [DecidableEq O] [Fintype W] [DecidableEq W] (A : QAlg Empty Bool O W)
    (t : ℕ) (o : O) :
    ∃ p : MvPolynomial Empty ℝ, p.totalDegree ≤ 2 * t ∧ ∀ a, evalBool p a = A.prob a t o :=
  A.exists_probability_polynomial t o

/-- The constant algorithm computes a constant function exactly with no query; the
bridge gives a degree-`0` polynomial within `0` of it. -/
example {ι X : Type} [Fintype ι] [DecidableEq ι] [Fintype X] (read : X → ι → Bool) (c : Bool) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 0 ∧ ApproximatesOn p read (fun _ => c) 0 := by
  obtain ⟨p, hdeg, happ, -⟩ :=
    (computesWithErrorOn_const read c (f := fun _ => c) (fun _ => rfl) le_rfl).exists_approx_polynomial
  exact ⟨p, by simpa using hdeg, happ⟩

/-! ## 3. One exact query reads one bit -/

/-- `projAlg` announces `some (a i)` after one query; its acceptance polynomial for the
answer `some true` has degree at most `2` and is the bit `a i` on the cube. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 ∧ ∀ a : ι → Bool, evalBool p a = bit (a i) := by
  obtain ⟨p, hdeg, heval⟩ := (projAlg Bool i).exists_probability_polynomial 1 (some true)
  refine ⟨p, by simpa using hdeg, fun a => ?_⟩
  rw [heval]
  cases h : a i <;> simp [QAlg.prob, projAlg, oracleMat_mulVec_qBasis, h]

/-! ## 4. The correctness bridge -/

/-- Exact algorithms (`ε = 0`): the polynomial agrees with `bit ∘ f` on the promise. -/
example {ι X W : Type} [Fintype ι] [DecidableEq ι] [Fintype X] [Fintype W] [DecidableEq W]
    {A : QAlg ι Bool Bool W} {t : ℕ} {read : X → ι → Bool} {f : X → Bool}
    (h : ComputesWithErrorOn A t read f 0) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧ ∀ x, evalBool p (read x) = bit (f x) := by
  obtain ⟨p, hdeg, happ, -⟩ := h.exists_approx_polynomial
  exact ⟨p, hdeg, fun x => by have := happ x; rwa [abs_nonpos_iff, sub_eq_zero] at this⟩

/-- A noninjective promise map (two promise inputs with the same observation and the same
value) is admitted; the values stay in `[0, 1]` off the promise as well. -/
example {W : Type} [Fintype W] [DecidableEq W] {A : QAlg (Fin 1) Bool Bool W} {t : ℕ} {ε : ℝ}
    (h : ComputesWithErrorOn A t (fun x : Bool × Bool => fun _ : Fin 1 => x.1)
      (fun x => x.1) ε) :
    ∃ p : MvPolynomial (Fin 1) ℝ, p.totalDegree ≤ 2 * t ∧
      (∀ x : Bool × Bool, |evalBool p (fun _ => x.1) - bit x.1| ≤ ε) ∧
      ∀ a : Fin 1 → Bool, 0 ≤ evalBool p a ∧ evalBool p a ≤ 1 :=
  h.exists_approx_polynomial

/-! ## 5. Lower-bound interfaces -/

theorem acceptance_lower_native :
    ∀ {ι X : Type} [Fintype ι] [DecidableEq ι] [Fintype X] {read : X → ι → Bool} {f : X → Bool}
      {ε : ℝ} {d : ℕ}, (∀ x y, read x = read y → f x = f y) → 0 ≤ ε →
      PolyObstructionOn read f ε d →
        d < 2 * qQueryOn read f ε ∧ d / 2 + 1 ≤ qQueryOn read f ε :=
  fun hdet hε hobs =>
    ⟨lt_two_mul_qQueryOn_of_det hdet hε hobs, div_two_succ_le_qQueryOn_of_det hdet hε hobs⟩

theorem acceptance_lower_xor :
    ∀ {ι X : Type} [Fintype ι] [DecidableEq ι] [Fintype X] {read : X → ι → Bool} {f : X → Bool}
      {ε : ℝ} {d : ℕ}, (∀ x y, read x = read y → f x = f y) → 0 ≤ ε →
      PolyObstructionOn read f ε d →
        d < 2 * xorQQueryOn read f ε ∧ d / 2 + 1 ≤ xorQQueryOn read f ε :=
  fun hdet hε hobs =>
    ⟨lt_two_mul_xorQQueryOn_of_det hdet hε hobs, div_two_succ_le_xorQQueryOn_of_det hdet hε hobs⟩

theorem acceptance_lower_total :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {g : (ι → Bool) → Bool} {ε : ℝ} {d : ℕ}, 0 ≤ ε →
      PolyObstructionOn id g ε d → d < 2 * qQuery g ε ∧ d < 2 * xorQQueryOn id g ε :=
  fun hε hobs => ⟨lt_two_mul_qQuery hε hobs, lt_two_mul_xorQQuery hε hobs⟩

/-- The algorithm-level forms carry no nonemptiness hypothesis at all. -/
theorem acceptance_lower_algorithm :
    ∀ {ι X W : Type} [Fintype ι] [DecidableEq ι] [Fintype X] [Fintype W] [DecidableEq W]
      {read : X → ι → Bool} {f : X → Bool} {ε : ℝ} {d : ℕ} {A : QAlg ι Bool Bool W} {t : ℕ},
      PolyObstructionOn read f ε d →
        (ComputesWithErrorOn A t read f ε → d < 2 * t) ∧
        (XorComputesWithErrorOn A t read f ε → d < 2 * t) :=
  fun hobs => ⟨fun hA => lt_two_mul_of_computes hobs hA, fun hA => lt_two_mul_of_xorComputes hobs hA⟩

/-! ## 6. A worked obstruction: reading one bit needs a query -/

/-- No constant is within `ε < 1/2` of both values of a bit. -/
theorem polyObstruction_coord_zero {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) {ε : ℝ}
    (hε : ε < 1 / 2) : PolyObstructionOn id (fun a : ι → Bool => a i) ε 0 := by
  intro p hdeg happ
  have hC : p = MvPolynomial.C (p.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hdeg)
  have h0 := happ (fun _ => false)
  have h1 := happ (fun _ => true)
  rw [hC] at h0 h1
  simp only [id, evalBool_C, bit_true, bit_false, sub_zero] at h0 h1
  rw [abs_le] at h0 h1
  linarith [h0.2, h1.1]

/-- `1 ≤ Q_ε(xᵢ)` for every `0 ≤ ε < 1/2`, native and XOR, from the polynomial method. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) :
    1 ≤ qQuery (fun a : ι → Bool => a i) ε ∧ 1 ≤ xorQQueryOn id (fun a : ι → Bool => a i) ε := by
  have h1 := div_two_succ_le_qQuery hε0 (polyObstruction_coord_zero i hε)
  have h2 := div_two_succ_le_xorQQuery hε0 (polyObstruction_coord_zero i hε)
  exact ⟨by simpa using h1, by simpa using h2⟩

end PolynomialMethodAcceptance
end QuantumQueryComplexity
