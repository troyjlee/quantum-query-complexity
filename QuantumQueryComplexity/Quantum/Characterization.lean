import QuantumQueryComplexity.Quantum.UpperBound
import QuantumQueryComplexity.Quantum.UniformHasDual
import QuantumQueryComplexity.Quantum.Simulation
import QuantumQueryComplexity.Quantum.FiniteOutput
import QuantumQueryComplexity.Promise.Post
import QuantumQueryComplexity.Quantum.LowerBound.Main
import QuantumQueryComplexity.Quantum.LowerBound.MainBool
import QuantumQueryComplexity.Quantum.Plurality
import QuantumQueryComplexity.Duality.Main
import QuantumQueryComplexity.Duality.MainOn
set_option synthInstance.maxSize 800

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The fixed-error characterization for total Boolean functions (Milestone B)

The first end-to-end deliverable of the quantum layer:

    (7/32) · ADV±(f)  ≤  Q_{1/16}(f)  ≤  2¹⁴ · ADV±(f)

for every total Boolean function `f : (ι → Bool) → Bool`
(`qQuery_characterized_by_advPM`).  The lower half is Milestone A
(`mul_advPMOn_le_qQueryOn_of_error_sixteenth` at `read = id`); the upper half
chains **strong duality** (`exists_dualPair_of_advPM_lt`, giving dual pairs
of cost arbitrarily close to `ADV±`), the total-to-promise restriction
(`HasDual.hasDualOn`), and uniform extraction
(`qQueryOn_le_of_hasDualOn_uniform`). Taking arbitrarily small slack gives
`Q_{1/16}(f) ≤ 8192(1 + ADV±(f))` without assuming an optimal dual exists.
For nonconstant functions, `one_le_advPM` supplies `ADV± ≥ 1`, so this is at
most `2¹⁴·ADV±`. Constant functions cost zero queries.

This file deliberately sits **outside** the `QuantumQueryComplexity.Quantum` aggregate: it
imports `QuantumQueryComplexity.Duality.Main` — the tracked strong-duality development —
alongside the quantum hierarchy, like `Quantum/Applications.lean`.  Build it
explicitly with `lake build QuantumQueryComplexity.Quantum.Characterization`.

The conventional-error form is here too
(`boundedErrorQQuery_characterized_by_advPM`):

    (1/36) · ADV±(f)  ≤  Q_{1/3}(f)  ≤  2¹⁴ · ADV±(f)

— the upper half by error monotonicity, the lower half by the **sharp Boolean
output condition** of `LowerBound/OutputBool.lean` (no amplification).

The oracle-simulation theorem (`Quantum/Simulation.lean`) transports the
characterization into the conventional model
(`xorQQuery_characterized_by_advPM`, below): the **standard Boolean XOR
oracle with explicit idle-index and blank-answer sectors**, at two queries
per query.  Convention, stated for precision: that XOR model lives on the
same basis `Option ι × Option Bool × W`, acting as the textbook XOR on the
`some`-answer sector and as the identity on the idle and blank sectors; the
further padding equivalence to a literal `ι × Bool × W` basis is a standard
harmless extension and is not separately formalized.
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The operational lower bound, for total Boolean functions**:
`(7/32)·ADV±(f) ≤ Q_{1/16}(f)`.  Milestone A at `read = id`. -/
theorem mul_advPM_le_qQuery_sixteenth (f : (ι → Bool) → Bool) :
    (7 / 32 : ℝ) * advPM f ≤ (qQuery f (1 / 16) : ℝ) := by
  have h := mul_advPMOn_le_qQueryOn_of_error_sixteenth
    (read := (id : (ι → Bool) → ι → Bool)) (f := f)
    (fun x y hxy => by rw [show x = y from hxy])
  replace h : (7 / 32 : ℝ) * advPM f
      ≤ (qQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 16) : ℝ) := h
  exact h

/-- **The additive uniform upper bound, for total Boolean functions**:
strong duality and uniform extraction give `Q_{1/16}(f) ≤ 8192(1 + ADV±(f))`.
Arbitrarily small slack suffices; dual optimizer attainment is not needed. -/
theorem qQuery_sixteenth_le_one_add_advPM (f : (ι → Bool) → Bool) :
    (qQuery f (1 / 16) : ℝ) ≤ 8192 * (1 + advPM f) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hc : advPM f < advPM f + ε / 8192 := by linarith
  obtain ⟨m, P, hP⟩ := exists_dualPair_of_advPM_lt hc
  have hd : HasDual f (advPM f + ε / 8192) := ⟨Fin m, inferInstance, P, hP⟩
  have hu := qQueryOn_le_of_hasDualOn_uniform hd.hasDualOn
    ((advPM_nonneg f).trans hc.le)
  change (qQuery f (1 / 16) : ℝ) ≤ 8192 * (1 + (advPM f + ε / 8192)) at hu
  linarith

/-- **The algorithmic upper bound, for total Boolean functions**:
`Q_{1/16}(f) ≤ 2¹⁴·ADV±(f)`. The additive uniform bound absorbs its constant
term using `ADV± ≥ 1` for nonconstant functions; constants need no queries. -/
theorem qQuery_sixteenth_le_advPM (f : (ι → Bool) → Bool) :
    (qQuery f (1 / 16) : ℝ) ≤ 2 ^ 14 * advPM f := by
  by_cases hconst : ∀ x y : ι → Bool, f x = f y
  · have h0 : qQuery f (1 / 16) = 0 :=
      qQueryOn_const_eq_zero id (c := f (fun _ => false))
        (fun x => hconst x (fun _ => false)) (by norm_num)
    rw [h0, Nat.cast_zero]
    exact mul_nonneg (by norm_num) (advPM_nonneg f)
  · simp only [not_forall] at hconst
    obtain ⟨x, y, hxy⟩ := hconst
    have h1 : 1 ≤ advPM f := one_le_advPM hxy
    linarith [qQuery_sixteenth_le_one_add_advPM f]

/-- **The fixed-error characterization for total Boolean functions**
(Milestone B): `(7/32)·ADV±(f) ≤ Q_{1/16}(f) ≤ 2¹⁴·ADV±(f)`. -/
theorem qQuery_characterized_by_advPM (f : (ι → Bool) → Bool) :
    (7 / 32 : ℝ) * advPM f ≤ (qQuery f (1 / 16) : ℝ) ∧
      (qQuery f (1 / 16) : ℝ) ≤ 2 ^ 14 * advPM f :=
  ⟨mul_advPM_le_qQuery_sixteenth f, qQuery_sixteenth_le_advPM f⟩

/-- **The conventional-error upper bound is free** (error monotonicity):
`Q_{1/3}(f) ≤ Q_{1/16}(f) ≤ 2¹⁴·ADV±(f)`. -/
theorem boundedErrorQQuery_le_advPM (f : (ι → Bool) → Bool) :
    (boundedErrorQQuery f : ℝ) ≤ 2 ^ 14 * advPM f := by
  have hne : (QueryCounts (id : (ι → Bool) → ι → Bool) f (1 / 16)).Nonempty :=
    queryCounts_nonempty (fun x y hxy => by rw [show x = y from hxy])
      (by norm_num)
  have hmono : qQuery f (1 / 3) ≤ qQuery f (1 / 16) :=
    qQueryOn_mono (by norm_num) hne
  have hmono' : (boundedErrorQQuery f : ℝ) ≤ (qQuery f (1 / 16) : ℝ) := by
    exact_mod_cast hmono
  linarith [hmono', qQuery_sixteenth_le_advPM f]

/-- **The conventional-error lower bound** for total Boolean functions:
`(1/36)·ADV±(f) ≤ Q_{1/3}(f)`, via the sharp Boolean output condition — no
amplification. -/
theorem mul_advPM_le_boundedErrorQQuery (f : (ι → Bool) → Bool) :
    (1 / 36 : ℝ) * advPM f ≤ (boundedErrorQQuery f : ℝ) := by
  have h := mul_advPMOn_le_qQueryOn_of_error_third
    (read := (id : (ι → Bool) → ι → Bool)) (f := f)
    (fun x y hxy => by rw [show x = y from hxy])
  replace h : (1 / 36 : ℝ) * advPM f
      ≤ (qQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ) := h
  exact h

/-- **The conventional-error characterization** (Milestone B at `ε = 1/3`):
`(1/36)·ADV±(f) ≤ Q_{1/3}(f) ≤ 2¹⁴·ADV±(f)` for total Boolean `f`. -/
theorem boundedErrorQQuery_characterized_by_advPM (f : (ι → Bool) → Bool) :
    (1 / 36 : ℝ) * advPM f ≤ (boundedErrorQQuery f : ℝ) ∧
      (boundedErrorQQuery f : ℝ) ≤ 2 ^ 14 * advPM f :=
  ⟨mul_advPM_le_boundedErrorQQuery f, boundedErrorQQuery_le_advPM f⟩

/-- **The characterization in the Boolean XOR-oracle model**: for total
Boolean `f`, at error `1/3`, using the idle and blank sectors of `XorOracle.lean`,

    (1/72)·ADV±(f) ≤ Qˣ_{1/3}(f) ≤ 2¹⁵·ADV±(f),

by the two-queries-per-query simulation of `Quantum/Simulation.lean` applied
to the transposition-model characterization. -/
theorem xorQQuery_characterized_by_advPM (f : (ι → Bool) → Bool) :
    (1 / 72 : ℝ) * advPM f
        ≤ (xorQQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ) ∧
      (xorQQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ)
        ≤ 2 ^ 15 * advPM f := by
  have hdet : ∀ x y : ι → Bool, (id x : ι → Bool) = id y → f x = f y :=
    fun x y hxy => by rw [show x = y from hxy]
  have h1 := qQueryOn_le_two_mul_xorQQueryOn hdet
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have h2 := xorQQueryOn_le_two_mul_qQueryOn hdet
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have h1' : (qQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ)
      ≤ 2 * (xorQQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ) := by
    exact_mod_cast h1
  have h2' : (xorQQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ)
      ≤ 2 * (qQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ) := by
    exact_mod_cast h2
  have hlow : (1 / 36 : ℝ) * advPM f
      ≤ (qQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ) :=
    mul_advPM_le_boundedErrorQQuery f
  have hup : (qQueryOn (id : (ι → Bool) → ι → Bool) f (1 / 3) : ℝ)
      ≤ 2 ^ 14 * advPM f :=
    boundedErrorQQuery_le_advPM f
  constructor
  · linarith
  · linarith

/-! ## The promise-Boolean characterization (Milestone C step 1)

Promise strong duality (`Duality/MainOn.lean`) feeds the promise-native
extraction, and the lower bound was promise-native from the start. -/

section Promise

variable {σ X : Type} [Fintype σ] [DecidableEq σ] [Fintype X] [DecidableEq X]

/-- **The promise upper bound from the promise adversary bound.** -/
theorem qQueryOn_le_advPMOn_bool_sixteenth [Nonempty σ] (read : X → ι → σ) (f : X → Bool)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (qQueryOn read f (1 / 16) : ℝ)
      ≤ 8192 * (1 + 8 * Real.sqrt (Fintype.card σ) * advPMOn read f) := by
  by_cases hconst : ∀ x y : X, f x = f y
  · have h0 : qQueryOn read f (1 / 16) = 0 := by
      rcases isEmpty_or_nonempty X with he | hne
      · exact qQueryOn_const_eq_zero read (c := true)
          (fun x => (he.false x).elim) (by norm_num)
      · obtain ⟨x₀⟩ := hne
        exact qQueryOn_const_eq_zero read (c := f x₀) (fun x => hconst x x₀)
          (by norm_num)
    rw [h0, Nat.cast_zero]
    have hA0 := advPMOn_nonneg hdet
    have hs0 : (0 : ℝ) ≤ Real.sqrt (Fintype.card σ) := Real.sqrt_nonneg _
    nlinarith
  · simp only [not_forall] at hconst
    obtain ⟨x, y, hxy⟩ := hconst
    have hhalf := half_le_advPMOn hdet hxy
    obtain ⟨m, P, hP⟩ := exists_dualPairOn_of_advPMOn_lt hdet
      (show advPMOn read f < 2 * advPMOn read f from by linarith)
    have hup := qQueryOn_le_of_dualPairOn read f P hP (by linarith)
    have hb : 8192 * (1 + 4 * Real.sqrt (Fintype.card σ)
          * (2 * advPMOn read f))
        = 8192 * (1 + 8 * Real.sqrt (Fintype.card σ) * advPMOn read f) := by
      ring
    linarith [hup, hb.le, hb.ge]

/-- **The promise-Boolean characterization at fixed error `1/16`**
(Milestone C step 1): for any read-determined Boolean promise problem on a
finite **nonempty** alphabet,
`(7/32)·ADV±ₚ(f) ≤ Q_{1/16}(f) ≤ 8192(1 + 8√|σ|·ADV±ₚ(f))`.  The unsuffixed
name is the general-output theorem below. -/
theorem qQueryOn_characterized_by_advPMOn_bool_sixteenth [Nonempty σ] (read : X → ι → σ)
    (f : X → Bool) (hdet : ∀ x y, read x = read y → f x = f y) :
    (7 / 32 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 16) : ℝ) ∧
      (qQueryOn read f (1 / 16) : ℝ)
        ≤ 8192 * (1 + 8 * Real.sqrt (Fintype.card σ) * advPMOn read f) :=
  ⟨mul_advPMOn_le_qQueryOn_of_error_sixteenth hdet,
    qQueryOn_le_advPMOn_bool_sixteenth read f hdet⟩

/-- The multiplicative form at `1/16`, for problems nonconstant on the
promise: `Q_{1/16}(f) ≤ 2¹⁷·√|σ|·ADV±ₚ(f)`. -/
theorem qQueryOn_le_mul_advPMOn_bool_sixteenth [Nonempty σ] (read : X → ι → σ)
    (f : X → Bool) (hdet : ∀ x y, read x = read y → f x = f y)
    {x y : X} (hxy : f x ≠ f y) :
    (qQueryOn read f (1 / 16) : ℝ)
      ≤ 2 ^ 17 * Real.sqrt (Fintype.card σ) * advPMOn read f := by
  have hup := qQueryOn_le_advPMOn_bool_sixteenth read f hdet
  have hhalf := half_le_advPMOn hdet hxy
  have hs1 : (1 : ℝ) ≤ Real.sqrt (Fintype.card σ) := by
    have h1 : 1 ≤ Fintype.card σ := Fintype.card_pos_iff.mpr ‹Nonempty σ›
    have h2 : (1 : ℝ) ≤ (Fintype.card σ : ℝ) := by exact_mod_cast h1
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (Fintype.card σ) := Real.sqrt_le_sqrt h2
  have hprod : (1 : ℝ) * (1 / 2)
      ≤ Real.sqrt (Fintype.card σ) * advPMOn read f :=
    mul_le_mul hs1 hhalf (by norm_num) (Real.sqrt_nonneg _)
  linarith [hup, hprod]

/-- **The promise-Boolean characterization at bounded error `1/3`**: the
lower half is the sharp promise-native Boolean bound, the upper half is error
monotonicity into the `1/16` extraction. -/
theorem qQueryOn_characterized_by_advPMOn_bool_third [Nonempty σ]
    (read : X → ι → σ) (f : X → Bool)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (1 / 36 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 3) : ℝ) ∧
      (qQueryOn read f (1 / 3) : ℝ)
        ≤ 8192 * (1 + 8 * Real.sqrt (Fintype.card σ) * advPMOn read f) := by
  constructor
  · exact mul_advPMOn_le_qQueryOn_of_error_third hdet
  · have hmono : qQueryOn read f (1 / 3) ≤ qQueryOn read f (1 / 16) :=
      qQueryOn_mono (by norm_num) (queryCounts_nonempty hdet (by norm_num))
    have hup := qQueryOn_le_advPMOn_bool_sixteenth read f hdet
    have hcast : ((qQueryOn read f (1 / 3) : ℕ) : ℝ)
        ≤ ((qQueryOn read f (1 / 16) : ℕ) : ℝ) := by exact_mod_cast hmono
    linarith

/-! ## Finite outputs (Milestone C, the bit-encoding route)

Each encoding bit of `f` is a post-composition, so its promise adversary
bound is at most `f`'s (`advPMOn_comp_le`); the promise-Boolean
characterization supplies a `1/16`-algorithm per bit, and the independent-run
machinery (`Amplify.lean`, `FiniteOutput.lean`) amplifies and joins them. -/

/-- **The general-output upper bound**: for `f : X → O` with `O` a finite
nonempty output type of `m` values, on any promise and finite nonempty
alphabet,

    Q_{1/16}(f) ≤ 2·B·(Nat.clog 2 (3B)) · 8192(1 + 8√|σ|·ADV±ₚ(f)),
    B = Nat.clog 2 m

(`Nat.clog 2 0 = 0`, so singleton outputs are included) — the
`O(log m · loglog m · √|σ| · ADV±ₚ)` shape, at the SAME fixed error
`1/16` as the lower bound: with `t = Nat.clog 2 (3B)` the assembled error is `0`
for `B = 0`, exactly `1/16` for `B = 1`, and at most `1/(9B) ≤ 1/18` for
`B ≥ 2`. -/
theorem qQueryOn_le_advPMOn_finiteOutput_sixteenth {O : Type} [Fintype O]
    [DecidableEq O] [Nonempty O] [Nonempty σ] (read : X → ι → σ) (f : X → O)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (qQueryOn read f (1 / 16) : ℝ)
      ≤ 2 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
        * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ)
            * advPMOn read f)) := by
  classical
  set B : ℕ := encBits O with hB
  set t : ℕ := Nat.clog 2 (3 * B) with ht
  -- the per-bit data
  have hdetb : ∀ i : Fin B, ∀ x y, read x = read y →
      encBit (f x) i = encBit (f y) i := fun i x y hxy => by
    rw [hdet x y hxy]
  have halg : ∀ i : Fin B, ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : QAlg ι σ Bool W),
      ComputesWithErrorOn A
        (qQueryOn read (fun x => encBit (f x) i) (1 / 16)) read
        (fun x => encBit (f x) i) (1 / 16) := fun i =>
    exists_computes_qQueryOn (queryCounts_nonempty (hdetb i) (by norm_num))
  -- the assembled algorithm
  obtain ⟨W', hW1, hW2, A', hA'⟩ := exists_decode_computes t halg
  -- its error is at most `1/16` (three cases: `B = 0`, `B = 1`, `B ≥ 2`)
  have herr : (B : ℝ) * (1 / 4) ^ t ≤ 1 / 16 := by
    have hpow : ∀ hB1 : 1 ≤ B, (3 * B : ℝ) ≤ 2 ^ t := by
      intro _
      have := Nat.le_pow_clog (by norm_num : 1 < 2) (3 * B)
      rw [← ht] at this
      exact_mod_cast this
    rcases Nat.lt_or_ge B 2 with hB2 | hB2
    · have hcase : B = 0 ∨ B = 1 := by omega
      rcases hcase with hB0 | hB1
      · rw [hB0]
        norm_num
      · -- `B = 1`: from `3 ≤ 2^t` the round count `t` is at least `2`
        have hpow1 : (3 : ℝ) ≤ 2 ^ t := by
          have := hpow (by omega)
          rw [hB1] at this
          norm_num at this
          exact_mod_cast this
        have ht2 : 2 ≤ t := by
          by_contra hcon
          have htle : t ≤ 1 := by omega
          have : (2 : ℝ) ^ t ≤ 2 ^ 1 :=
            pow_le_pow_right₀ (by norm_num) htle
          norm_num at this
          linarith
        have hq : ((1 : ℝ) / 4) ^ t ≤ (1 / 4) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) ht2
        rw [hB1]
        norm_num at hq ⊢
        linarith
    · -- `B ≥ 2`: the error is at most `1/(9B) ≤ 1/18`
      have hBpos' : (2 : ℝ) ≤ B := by exact_mod_cast hB2
      have hpow' := hpow (by omega)
      have h4 : ((1 : ℝ) / 4) ^ t = ((2 : ℝ) ^ t * (2 : ℝ) ^ t)⁻¹ := by
        rw [show ((1 : ℝ) / 4) = ((2 : ℝ) * 2)⁻¹ from by norm_num,
          inv_pow, mul_pow]
      have hkey : 16 * (B : ℝ) ≤ (2 : ℝ) ^ t * (2 : ℝ) ^ t := by
        nlinarith [hpow', hBpos']
      rw [h4, mul_inv_le_iff₀ (by positivity)]
      linarith
  have hA3 : ComputesWithErrorOn A' (∑ i, 2 * t *
      qQueryOn read (fun x => encBit (f x) i) (1 / 16)) read f (1 / 16) :=
    hA'.mono herr
  -- the query count, bounded
  have hcount := qQueryOn_le hA3
  have hq0 : ∀ i : Fin B,
      ((qQueryOn read (fun x => encBit (f x) i) (1 / 16) : ℕ) : ℝ)
        ≤ 8192 * (1 + 8 * Real.sqrt (Fintype.card σ) * advPMOn read f) := by
    intro i
    have h1 := qQueryOn_le_advPMOn_bool_sixteenth read
      (fun x => encBit (f x) i) (hdetb i)
    have h2 : advPMOn read (fun x => encBit (f x) i) ≤ advPMOn read f :=
      advPMOn_comp_le hdet (fun o => encBit o i)
    have h3 : (0 : ℝ) ≤ 8 * Real.sqrt (Fintype.card σ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  have hcast : ((∑ i : Fin B, 2 * t *
      qQueryOn read (fun x => encBit (f x) i) (1 / 16) : ℕ) : ℝ)
      ≤ (B : ℝ) * (2 * t)
        * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ) * advPMOn read f)) := by
    push_cast
    calc (∑ i : Fin B, (2 : ℝ) * t *
          (qQueryOn read (fun x => encBit (f x) i) (1 / 16) : ℝ))
        ≤ ∑ _i : Fin B, (2 : ℝ) * t
            * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ)
              * advPMOn read f)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := hq0 i
          have ht0 : (0 : ℝ) ≤ 2 * t := by positivity
          nlinarith
      _ = (B : ℝ) * (2 * t)
            * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ)
              * advPMOn read f)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
  have hfinal : ((qQueryOn read f (1 / 16) : ℕ) : ℝ)
      ≤ (B : ℝ) * (2 * t)
        * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ) * advPMOn read f)) := by
    refine le_trans ?_ hcast
    exact_mod_cast hcount
  calc ((qQueryOn read f (1 / 16) : ℕ) : ℝ)
      ≤ (B : ℝ) * (2 * t)
        * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ) * advPMOn read f)) :=
        hfinal
    _ = 2 * (B : ℝ) * (t : ℝ)
        * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ) * advPMOn read f)) := by
        ring

/-- The conventional-error form, by monotonicity. -/
theorem qQueryOn_le_advPMOn_finiteOutput {O : Type} [Fintype O]
    [DecidableEq O] [Nonempty O] [Nonempty σ] (read : X → ι → σ) (f : X → O)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (qQueryOn read f (1 / 3) : ℝ)
      ≤ 2 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
        * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ)
            * advPMOn read f)) := by
  have h16 := qQueryOn_le_advPMOn_finiteOutput_sixteenth read f hdet
  have hmono : qQueryOn read f (1 / 3) ≤ qQueryOn read f (1 / 16) :=
    qQueryOn_mono (by norm_num) (queryCounts_nonempty hdet (by norm_num))
  have hmono' : ((qQueryOn read f (1 / 3) : ℕ) : ℝ)
      ≤ ((qQueryOn read f (1 / 16) : ℕ) : ℝ) := by exact_mod_cast hmono
  linarith

/-- **The finite-output characterization** (the reserved unsuffixed name):
the promise adversary bound characterizes fixed-error quantum query
complexity — the same error `1/16` on both sides — for any finite nonempty
output type, up to the alphabet factor `√|σ|` and a `log m · loglog m`
output factor. -/
theorem qQueryOn_characterized_by_advPMOn {O : Type} [Fintype O]
    [DecidableEq O] [Nonempty O] [Nonempty σ] (read : X → ι → σ) (f : X → O)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (7 / 32 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 16) : ℝ) ∧
      (qQueryOn read f (1 / 16) : ℝ)
        ≤ 2 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
          * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ)
              * advPMOn read f)) :=
  ⟨mul_advPMOn_le_qQueryOn_of_error_sixteenth hdet,
    qQueryOn_le_advPMOn_finiteOutput_sixteenth read f hdet⟩

/-- **The finite-output characterization at the conventional error `1/3`**
(Milestone H): the lower half by plurality amplification over `43` runs
(`Plurality.lean`, `Q_{1/16} ≤ 43·Q_{1/3}`), the upper half by monotonicity
from the `1/16` bound.

    (7/1376)·ADV±ₚ(f) ≤ Q_{1/3}(f)
      ≤ 2·B·(Nat.clog 2 (3B)) · 8192(1 + 8√|σ|·ADV±ₚ(f)),   B = Nat.clog 2 m. -/
theorem qQueryOn_characterized_by_advPMOn_third {O : Type} [Fintype O]
    [DecidableEq O] [Nonempty O] [Nonempty σ] (read : X → ι → σ) (f : X → O)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (7 / 1376 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 3) : ℝ) ∧
      (qQueryOn read f (1 / 3) : ℝ)
        ≤ 2 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
          * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ)
              * advPMOn read f)) :=
  ⟨mul_advPMOn_le_qQueryOn_third_finiteOutput hdet,
    qQueryOn_le_advPMOn_finiteOutput read f hdet⟩

/-- **The multiplicative asymptotic at the characterization's own error**:
absorbing the additive `1` via `half_le_advPMOn`,
`Q_{1/16}(f) ≤ 2¹⁸·B·(Nat.clog 2 (3B))·√|σ|·ADV±ₚ(f)`, `B = Nat.clog 2 m`
(`Nat.clog 2 0 = 0`). -/
theorem qQueryOn_le_mul_advPMOn_finiteOutput_sixteenth {O : Type} [Fintype O]
    [DecidableEq O] [Nonempty O] [Nonempty σ] (read : X → ι → σ) (f : X → O)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (qQueryOn read f (1 / 16) : ℝ)
      ≤ 2 ^ 18 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
        * Real.sqrt (Fintype.card σ) * advPMOn read f := by
  by_cases hconst : ∀ x y : X, f x = f y
  · -- constant: zero queries; the right side is nonnegative
    have h0 : qQueryOn read f (1 / 16) = 0 := by
      rcases isEmpty_or_nonempty X with he | hne
      · exact qQueryOn_const_eq_zero read (c := Classical.arbitrary O)
          (fun x => (he.false x).elim) (by norm_num)
      · obtain ⟨x₀⟩ := hne
        exact qQueryOn_const_eq_zero read (c := f x₀) (fun x => hconst x x₀)
          (by norm_num)
    rw [h0, Nat.cast_zero]
    have hA0 := advPMOn_nonneg hdet
    have hs0 : (0 : ℝ) ≤ Real.sqrt (Fintype.card σ) := Real.sqrt_nonneg _
    have hB0 : (0 : ℝ) ≤ (encBits O : ℝ) := Nat.cast_nonneg _
    have ht0 : (0 : ℝ) ≤ (Nat.clog 2 (3 * encBits O) : ℝ) := Nat.cast_nonneg _
    positivity
  · simp only [not_forall] at hconst
    obtain ⟨x, y, hxy⟩ := hconst
    have hhalf := half_le_advPMOn hdet hxy
    have hs1 : (1 : ℝ) ≤ Real.sqrt (Fintype.card σ) := by
      have h1 : 1 ≤ Fintype.card σ := Fintype.card_pos_iff.mpr ‹Nonempty σ›
      have h2 : (1 : ℝ) ≤ (Fintype.card σ : ℝ) := by exact_mod_cast h1
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt (Fintype.card σ) := Real.sqrt_le_sqrt h2
    have hprod : (1 : ℝ) * (1 / 2)
        ≤ Real.sqrt (Fintype.card σ) * advPMOn read f :=
      mul_le_mul hs1 hhalf (by norm_num) (Real.sqrt_nonneg _)
    have h16 := qQueryOn_le_advPMOn_finiteOutput_sixteenth read f hdet
    have hscalar : 8192 * (1 + 8 * Real.sqrt (Fintype.card σ)
          * advPMOn read f)
        ≤ 2 ^ 17 * (Real.sqrt (Fintype.card σ) * advPMOn read f) := by
      nlinarith [hprod]
    have hBt0 : (0 : ℝ)
        ≤ 2 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hscalar hBt0
    calc (qQueryOn read f (1 / 16) : ℝ)
        ≤ 2 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
          * (8192 * (1 + 8 * Real.sqrt (Fintype.card σ)
              * advPMOn read f)) := h16
      _ ≤ 2 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
          * (2 ^ 17 * (Real.sqrt (Fintype.card σ) * advPMOn read f)) := hmul
      _ = 2 ^ 18 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
          * Real.sqrt (Fintype.card σ) * advPMOn read f := by ring

/-- The conventional-error multiplicative form, by monotonicity. -/
theorem qQueryOn_le_mul_advPMOn_finiteOutput {O : Type} [Fintype O]
    [DecidableEq O] [Nonempty O] [Nonempty σ] (read : X → ι → σ) (f : X → O)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (qQueryOn read f (1 / 3) : ℝ)
      ≤ 2 ^ 18 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
        * Real.sqrt (Fintype.card σ) * advPMOn read f := by
  have h16 := qQueryOn_le_mul_advPMOn_finiteOutput_sixteenth read f hdet
  have hmono : qQueryOn read f (1 / 3) ≤ qQueryOn read f (1 / 16) :=
    qQueryOn_mono (by norm_num) (queryCounts_nonempty hdet (by norm_num))
  have hmono' : ((qQueryOn read f (1 / 3) : ℕ) : ℝ)
      ≤ ((qQueryOn read f (1 / 16) : ℕ) : ℝ) := by exact_mod_cast hmono
  linarith

/-- **The finite-output characterization at `1/3`, multiplicative**
(Milestone H): the plurality-amplified lower bound paired with the
multiplicative upper bound, so that "characterization" is literally a
two-sided proportionality —

    (7/1376)·ADV±ₚ(f) ≤ Q_{1/3}(f) ≤ 2¹⁸·B·(Nat.clog 2 (3B))·√|σ|·ADV±ₚ(f),
    B = Nat.clog 2 m. -/
theorem qQueryOn_characterized_by_advPMOn_third_mul {O : Type} [Fintype O]
    [DecidableEq O] [Nonempty O] [Nonempty σ] (read : X → ι → σ) (f : X → O)
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (7 / 1376 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 3) : ℝ) ∧
      (qQueryOn read f (1 / 3) : ℝ)
        ≤ 2 ^ 18 * (encBits O : ℝ) * (Nat.clog 2 (3 * encBits O) : ℝ)
          * Real.sqrt (Fintype.card σ) * advPMOn read f :=
  ⟨mul_advPMOn_le_qQueryOn_third_finiteOutput hdet,
    qQueryOn_le_mul_advPMOn_finiteOutput read f hdet⟩

end Promise

end QuantumQueryComplexity
