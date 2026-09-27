import QuantumQueryComplexity.Quantum.StateConversion
import QuantumQueryComplexity.Promise.Defs
set_option synthInstance.maxSize 800

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The witness states, built from a dual adversary solution

The construction Phase 5 needs: from a `DualPairOn read K f` this file builds the
generators, the fixed subspace, and both witness families, and discharges the
`IsPosWitness` contracts from the dual's feasibility identity.

## The layout

The workspace is `Option K`: the dual's register, plus a slot `none` used as a
flag.  Three kinds of basis point matter, and the oracle is what separates them:

    τ         = (none, none, none)              the target, in the idle sector
    b i k     = (some i, none, some k)          blank answer — the generators
    e i s k   = (some i, some s, some k)        the answer register holds `s`

The **generators are the blank-answer states** `b i k`.  That single choice is
what makes the whole construction work, because the transposition oracle sends

    O_x (b i k) = e i (read x i) k,

so `span {O_x · gen}` is the span of the *true-answer* states of `x` — the
input-dependent subspace, produced by conjugation rather than by fiat.  By
`inputProj_mulVec_eq_self_iff`, a state is fixed by `inputProj gen (read x)`
exactly when it **vanishes at every true-answer point of `x`**.

## The two witnesses

    posWitness x = τ  -  ∑_{i,k} u x i k · (∑_{s ≠ read x i} e i s k)
    negWitness y = τ  +  ∑_{i,k} v y i k · e i (read y i) k

The positive witness puts the dual's `u x` on every **false** answer letter, so
it vanishes on the true-answer points of `x` and the first contract is immediate.
The negative witness puts the dual's `v y` on the **true** answer letters of `y`,
so it is `τ` plus a correction supported exactly where `inputProj gen (read y)`
kills.

They meet only where the two inputs disagree, and there the dual's feasibility
identity

    ∑ i, [read x i ≠ read y i] · ∑ k, u x i k · v y i k  =  [f x ≠ f y]

says precisely what is needed:

    ⟪posWitness x, negWitness y⟫ = 1 - [f x ≠ f y] = [f x = f y].

So distinct outputs give **orthogonal** witnesses.  Taking `L` to be the
projector onto the span of the positive witnesses of the inputs with `f x = o`
then fixes every positive witness and annihilates every negative one — the two
`IsPosWitness` contracts, and the negative side's `L *ᵥ w = 0`, all from one
inner product.

The `|σ| - 1` in `qNormSq_posWitness` is the price of spreading `u x i k` over
every false letter: the construction cannot know which letter `y` will read.  It
is `1` for a Boolean alphabet.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ X O K : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype X] [DecidableEq X] [DecidableEq O] [Fintype K] [DecidableEq K]

/-! ## States of the construction's shape

Every state below is `α` on the target and `A i s k` on the answer-letter
points.  Proving the inner product and the norm once, for this shape, is what
keeps the rest of the file free of basis manipulation. -/

/-- A state of the construction's shape. -/
def scState (α : ℂ) (A : ι → σ → K → ℂ) : QBasis ι σ (Option K) → ℂ
  | (none, none, none) => α
  | (some i, some s, some k) => A i s k
  | _ => 0

@[simp] lemma scState_target (α : ℂ) (A : ι → σ → K → ℂ) :
    scState α A ((none, none, none) : QBasis ι σ (Option K)) = α := rfl

@[simp] lemma scState_letter (α : ℂ) (A : ι → σ → K → ℂ) (i : ι) (s : σ) (k : K) :
    scState α A ((some i, some s, some k) : QBasis ι σ (Option K)) = A i s k := rfl

@[simp] lemma scState_idle_reg (α : ℂ) (A : ι → σ → K → ℂ) (k : K) :
    scState α A ((none, none, some k) : QBasis ι σ (Option K)) = 0 := rfl

@[simp] lemma scState_idle_letter (α : ℂ) (A : ι → σ → K → ℂ) (s : σ) (w : Option K) :
    scState α A ((none, some s, w) : QBasis ι σ (Option K)) = 0 := by
  cases w <;> rfl

@[simp] lemma scState_blank (α : ℂ) (A : ι → σ → K → ℂ) (i : ι) (w : Option K) :
    scState α A ((some i, none, w) : QBasis ι σ (Option K)) = 0 := by
  cases w <;> rfl

@[simp] lemma scState_flag (α : ℂ) (A : ι → σ → K → ℂ) (i : ι) (s : σ) :
    scState α A ((some i, some s, none) : QBasis ι σ (Option K)) = 0 := rfl

/-- **The inner product of two states of this shape.** -/
theorem qInner_scState (α β : ℂ) (A B : ι → σ → K → ℂ) :
    qInner (scState α A) (scState β B)
      = star α * β + ∑ i : ι, ∑ s : σ, ∑ k : K, star (A i s k) * B i s k := by
  simp [qInner_def, Fintype.sum_prod_type, Fintype.sum_option]

/-- **The squared norm of a state of this shape.** -/
theorem qNormSq_scState (α : ℂ) (A : ι → σ → K → ℂ) :
    qNormSq (scState α A)
      = Complex.normSq α + ∑ i : ι, ∑ s : σ, ∑ k : K, Complex.normSq (A i s k) := by
  simp [qNormSq_def, Fintype.sum_prod_type, Fintype.sum_option]

lemma scState_add (α β : ℂ) (A B : ι → σ → K → ℂ) :
    scState (α + β) (fun i s k => A i s k + B i s k)
      = scState α A + scState (K := K) β B := by
  funext p
  obtain ⟨(_ | i), (_ | s), (_ | k)⟩ := p <;> simp

/-! ## The generators and the target -/

/-- **The generators**: the blank-answer states, one per index and dual
register. -/
def scGen : ι × K → (QBasis ι σ (Option K) → ℂ) :=
  fun j => qBasis ((some j.1, none, some j.2) : QBasis ι σ (Option K))

/-- The target: the flag state of the idle sector. -/
def scTarget : QBasis ι σ (Option K) → ℂ := scState 1 (fun _ _ _ => (0 : ℂ))

lemma qInner_qBasis_left {H : Type} [Fintype H] [DecidableEq H] (p : H) (ψ : H → ℂ) :
    qInner (qBasis p) ψ = ψ p := by
  rw [qInner_def, Finset.sum_eq_single p]
  · rw [qBasis_apply, if_pos rfl, star_one, one_mul]
  · intro h _ hh
    rw [qBasis_apply, if_neg hh, star_zero, zero_mul]
  · simp

/-- **What the generators test.**  Pairing a generator against a state read
through the oracle picks out the amplitude at a *true-answer* point. -/
theorem qInner_scGen_oracle (a : ι → σ) (φ : QBasis ι σ (Option K) → ℂ) (i : ι) (k : K) :
    qInner (scGen (i, k)) (oracleMat a *ᵥ φ) = φ (some i, some (a i), some k) := by
  rw [scGen, qInner_qBasis_left, oracleMat_mulVec_apply, oracleMap_blank]

/-- **Being fixed by the input projector is vanishing on the true answers.** -/
theorem inputProj_scGen_mulVec_eq_self_iff (a : ι → σ) (φ : QBasis ι σ (Option K) → ℂ) :
    inputProj scGen a *ᵥ φ = φ ↔ ∀ i k, φ (some i, some (a i), some k) = 0 := by
  rw [inputProj_mulVec_eq_self_iff]
  constructor
  · intro h i k
    rw [← qInner_scGen_oracle a φ i k]
    exact h (i, k)
  · rintro h ⟨i, k⟩
    rw [qInner_scGen_oracle]
    exact h i k

/-! ## The two witness families -/

variable (read : X → ι → σ) (f : X → O)

/-- **The positive witness** for `x`: the target, minus the dual's `u x` spread
over every *false* answer letter. -/
def posWitness (P : DualPairOn read K f) (x : X) : QBasis ι σ (Option K) → ℂ :=
  scState 1 (fun i s k => if s = read x i then 0 else -(P.u x i k : ℂ))

/-- **The negative witness** for `y`: the target, plus the dual's `v y` on the
*true* answer letters. -/
def negWitness (P : DualPairOn read K f) (y : X) : QBasis ι σ (Option K) → ℂ :=
  scState 1 (fun i s k => if s = read y i then (P.v y i k : ℂ) else 0)

/-- The negative witness's correction term, supported exactly on the true-answer
points of `y`. -/
def negCorr (P : DualPairOn read K f) (y : X) : QBasis ι σ (Option K) → ℂ :=
  scState 0 (fun i s k => if s = read y i then (P.v y i k : ℂ) else 0)

lemma negWitness_eq_target_add (P : DualPairOn read K f) (y : X) :
    negWitness read f P y = scTarget + negCorr read f P y := by
  funext p
  obtain ⟨(_ | i), (_ | s), (_ | k)⟩ := p <;>
    simp [negWitness, negCorr, scTarget]

/-! ## The dual constraint, as an inner product

The one computation the construction rests on. -/

/-- **Distinct outputs give orthogonal witnesses.**  This *is* the dual's
feasibility identity, read as an inner product. -/
theorem qInner_posWitness_negWitness (P : DualPairOn read K f) (x y : X) :
    qInner (posWitness read f P x) (negWitness read f P y)
      = if f x = f y then 1 else 0 := by
  rw [posWitness, negWitness, qInner_scState]
  have hterm : ∀ i : ι,
      (∑ s : σ, ∑ k : K,
        star (if s = read x i then (0 : ℂ) else -(P.u x i k : ℂ))
          * (if s = read y i then (P.v y i k : ℂ) else 0))
        = -(((if read x i = read y i then 0 else ∑ k, P.u x i k * P.v y i k : ℝ)) : ℂ) := by
    intro i
    rw [Finset.sum_eq_single (read y i)]
    · by_cases h : read x i = read y i
      · rw [if_pos h, Complex.ofReal_zero, neg_zero]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [if_pos h.symm, star_zero, zero_mul]
      · rw [if_neg h, Complex.ofReal_sum]
        rw [show -(∑ k : K, ((P.u x i k * P.v y i k : ℝ) : ℂ))
              = ∑ k : K, -(((P.u x i k * P.v y i k : ℝ) : ℂ)) from by simp]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [if_neg fun hcc => h hcc.symm, if_pos rfl]
        simp
    · intro s _ hs
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [if_neg hs, mul_zero]
    · simp
  simp only [hterm]
  rw [show (∑ i : ι, -(((if read x i = read y i then 0
        else ∑ k, P.u x i k * P.v y i k : ℝ)) : ℂ))
      = -(∑ i : ι, (((if read x i = read y i then 0
        else ∑ k, P.u x i k * P.v y i k : ℝ)) : ℂ)) from by simp]
  rw [← Complex.ofReal_sum, P.constraint x y]
  by_cases h : f x = f y <;> simp [h]

/-! ## The positive contracts -/

/-- **The positive witness vanishes on the true answers of its own input**, which
is the first contract. -/
theorem inputProj_mulVec_posWitness (P : DualPairOn read K f) (x : X) :
    inputProj scGen (read x) *ᵥ posWitness read f P x = posWitness read f P x := by
  rw [inputProj_scGen_mulVec_eq_self_iff]
  intro i k
  rw [posWitness, scState_letter, if_pos rfl]

/-- **The fixed subspace**: the span of the positive witnesses of the inputs that
`f` sends to `o`. -/
noncomputable def scKer (P : DualPairOn read K f) (o : O) :
    Matrix (QBasis ι σ (Option K)) (QBasis ι σ (Option K)) ℂ :=
  subProj (rawSpan (fun x : {x : X // f x = o} => posWitness read f P x.1))

theorem isQProjector_scKer (P : DualPairOn read K f) (o : O) :
    IsQProjector (scKer read f P o) := isQProjector_subProj _

/-- **The fixed subspace fixes the positive witnesses**, which is the second
contract. -/
theorem scKer_mulVec_posWitness (P : DualPairOn read K f) {o : O} {x : X}
    (hx : f x = o) : scKer read f P o *ᵥ posWitness read f P x
      = posWitness read f P x :=
  spanProj_mulVec_self (fun x : {x : X // f x = o} => posWitness read f P x.1) ⟨x, hx⟩

/-- **Both contracts**, so the detector of `InputDetector.lean` answers `+1` on
this witness exactly, at cost `4(T-1)`. -/
theorem isPosWitness_posWitness (P : DualPairOn read K f) {o : O} {x : X}
    (hx : f x = o) :
    IsPosWitness scGen (scKer read f P o) (read x) (posWitness read f P x) :=
  ⟨inputProj_mulVec_posWitness read f P x, scKer_mulVec_posWitness read f P hx⟩

/-! ## The negative side -/

/-- **The fixed subspace annihilates the negative witnesses.**  This is the
hypothesis `effective_chord_gap_sq_inputReflProduct` asks for, and it is exactly
the orthogonality supplied by the dual constraint. -/
theorem scKer_mulVec_negWitness (P : DualPairOn read K f) {o : O} {y : X}
    (hy : f y ≠ o) : scKer read f P o *ᵥ negWitness read f P y = 0 := by
  refine subProj_mulVec_of_mem_orthogonal _ ?_
  rw [mem_rawSpan_orthogonal_iff]
  rintro ⟨x, hx⟩
  rw [qInner_posWitness_negWitness, if_neg]
  rw [hx]
  exact fun h => hy h.symm

/-- A projector kills anything orthogonal to its own image of that vector.  This
is the general fact; it is stated here because nothing upstream needs it yet. -/
lemma mulVec_eq_zero_of_qInner_eq_zero {H : Type} [Fintype H] [DecidableEq H]
    {P : Matrix H H ℂ} (hP : IsQProjector P) {ψ : H → ℂ}
    (h : qInner (P *ᵥ ψ) ψ = 0) : P *ᵥ ψ = 0 := by
  have h1 : qInner (P *ᵥ ψ) (P *ᵥ ψ) = 0 := by
    rw [qInner_mulVec_left, Matrix.mulVec_mulVec, hP.1, hP.2, ← qInner_conj, h, star_zero]
  rw [qInner_self] at h1
  exact qNormSq_eq_zero_iff.mp (by exact_mod_cast h1)

/-- **The input projector kills the negative witness's correction term**, which
is supported exactly on the true-answer points it annihilates. -/
theorem inputProj_mulVec_negCorr (P : DualPairOn read K f) (y : X) :
    inputProj scGen (read y) *ᵥ negCorr read f P y = 0 := by
  refine mulVec_eq_zero_of_qInner_eq_zero (isQProjector_inputProj _ _) ?_
  have hfix : inputProj scGen (read y) *ᵥ (inputProj scGen (read y) *ᵥ negCorr read f P y)
      = inputProj scGen (read y) *ᵥ negCorr read f P y := by
    rw [Matrix.mulVec_mulVec, (isQProjector_inputProj scGen (read y)).2]
  have hvan := (inputProj_scGen_mulVec_eq_self_iff (read y) _).mp hfix
  simp only [negCorr] at hvan
  rw [qInner_def]
  refine Finset.sum_eq_zero fun p _ => ?_
  obtain ⟨(_ | i), (_ | s), (_ | k)⟩ := p <;>
    simp only [negCorr, scState_target, scState_letter, scState_idle_reg,
      scState_idle_letter, scState_blank, scState_flag, mul_zero, star_zero, zero_mul]
  by_cases hs : s = read y i
  · rw [hs, hvan i k, star_zero, zero_mul]
  · rw [if_neg hs, mul_zero]

/-- **The negative witness is the target, up to what the input projector
kills.**  This is the negative side's projected-direction obligation. -/
theorem inputProj_mulVec_negWitness (P : DualPairOn read K f) (y : X) :
    inputProj scGen (read y) *ᵥ negWitness read f P y = scTarget := by
  have hτ : inputProj scGen (read y) *ᵥ (scTarget : QBasis ι σ (Option K) → ℂ) = scTarget :=
    (inputProj_scGen_mulVec_eq_self_iff (read y) _).mpr fun i k => by
      rw [scTarget, scState_letter]
  rw [negWitness_eq_target_add, Matrix.mulVec_add, hτ, inputProj_mulVec_negCorr, add_zero]

/-! ## Overlap and norms

The exact algebra above says nothing about *size*; these are the estimates the
query bound will consume. -/

/-- **The positive witness has overlap exactly `1` with the target.**  The
correction term lives entirely off the target, so nothing is lost. -/
theorem qInner_scTarget_posWitness (P : DualPairOn read K f) (x : X) :
    qInner scTarget (posWitness read f P x) = 1 := by
  rw [scTarget, posWitness, qInner_scState]
  simp

/-- **The negative witness's norm is `1` plus the dual's `v`-mass.** -/
theorem qNormSq_negWitness (P : DualPairOn read K f) (y : X) :
    qNormSq (negWitness read f P y)
      = 1 + ∑ i : ι, ∑ k : K, P.v y i k * P.v y i k := by
  rw [negWitness, qNormSq_scState]
  have hi : ∀ i : ι, (∑ s : σ, ∑ k : K,
      Complex.normSq (if s = read y i then (P.v y i k : ℂ) else 0))
      = ∑ k : K, P.v y i k * P.v y i k := by
    intro i
    rw [Finset.sum_eq_single (read y i)]
    · exact Finset.sum_congr rfl fun k _ => by
        rw [if_pos rfl, Complex.normSq_ofReal]
    · intro s _ hs
      exact Finset.sum_eq_zero fun k _ => by rw [if_neg hs, Complex.normSq_zero]
    · simp
  simp only [hi]
  norm_num

/-- **The positive witness's norm**, exactly: `1` plus the dual's `u`-mass, once
per *false* letter. -/
theorem qNormSq_posWitness (P : DualPairOn read K f) (x : X) :
    qNormSq (posWitness read f P x)
      = 1 + ∑ i : ι, ∑ s : σ, (if s = read x i then 0
          else ∑ k : K, P.u x i k * P.u x i k) := by
  rw [posWitness, qNormSq_scState]
  have hi : ∀ (i : ι) (s : σ), (∑ k : K,
      Complex.normSq (if s = read x i then (0 : ℂ) else -(P.u x i k : ℂ)))
      = if s = read x i then 0 else ∑ k : K, P.u x i k * P.u x i k := by
    intro i s
    by_cases h : s = read x i
    · rw [if_pos h]
      exact Finset.sum_eq_zero fun k _ => by rw [if_pos h, Complex.normSq_zero]
    · rw [if_neg h]
      exact Finset.sum_congr rfl fun k _ => by
        rw [if_neg h, Complex.normSq_neg, Complex.normSq_ofReal]
  simp only [hi]
  norm_num

/-- The negative witness is short: `‖w‖² ≤ 1 + c` for a dual of cost `c`. -/
theorem qNormSq_negWitness_le {c : ℝ} (P : DualPairOn read K f) (hP : P.IsCostLe c)
    (y : X) : qNormSq (negWitness read f P y) ≤ 1 + c := by
  rw [qNormSq_negWitness]
  have := hP.2 y
  linarith

end QuantumQueryComplexity
