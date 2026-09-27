import QuantumQueryComplexity.Quantum.InputDetector
set_option synthInstance.maxSize 800

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Witness states for state conversion

Phase 5 begins here.  The detector of `InputDetector.lean` distinguishes two
kinds of vector: those **fixed** by the reflection product `R_P R_L`, which it
reports as `+1` exactly, and those in the **far window**, which it reports as
`-1` up to `16/(T²Δ²)`.  State conversion has to supply both, from a dual
adversary solution.

This file fixes the *contracts* — what a construction must prove — and derives
everything that follows from them formally, so that the construction itself has
a single, sharp target.

## The positive side

A positive witness for the input `a` is a state `φ` with

    inputProj v a *ᵥ φ = φ        and        L *ᵥ φ = φ.

Both reflections then fix `φ`, hence so does `inputReflProduct`, hence the
detector is **exactly** the identity on `uniformClock T φ`.  No estimate is
involved on this side, which is the point.

**The witness is not the bare target.**  In the corrected LMRSS construction the
fixed point is `φₓ = t₊ + (witness-workspace term)`, not `t₊` itself: `t₊` alone
is in general *not* fixed by `inputProj v a`, since being fixed means the
oracle-rotated state is orthogonal to **every** generator `v i`, which the
workspace term is exactly what arranges.  Building the algorithm around bare
`t₊` would be a real error, not a normalization detail, so the overlap
`⟪t₊, φₓ⟫` is a separate obligation of the construction rather than something
this interface can assume.

`inputProj_mulVec_eq_self_iff` reduces the first contract to one inner product
per generator, which is the form a construction can discharge.

## The negative side

A negative witness is a `w` with `L *ᵥ w = 0`.  That is precisely the hypothesis
of `effective_chord_gap_sq_inputReflProduct`, so the near component of `P w` is
at most `(Δ²/4)‖w‖²` and — by `le_qNormSq_chordFar_inputProj` — the far window
carries the rest.

That is the *spectral* half of the negative side, and it is all this interface
supplies.  It is **not** all the construction owes.  Two further obligations
stay with the concrete witness, and neither is formal:

* a bound on `‖w‖²`, since the effective gap charges `(Δ²/4)‖w‖²` against
  `‖P w‖²` — a negative witness of uncontrolled norm buys nothing;
* the identification of `inputProj v a *ᵥ w` with the intended `t₋` direction.
  As on the positive side, `w` carries a correction term beyond `t₋`, and what
  has to be shown is that `inputProj` *kills* that term, leaving the direction
  the algorithm measures.

So the asymmetry between the two sides is real but small: the positive side ends
in an exact fixed-point identity, the negative side in two estimates.  Both are
quantitative facts about a particular construction, which is why neither lives
in `IsPosWitness`.
-/

namespace QuantumQueryComplexity



open scoped Matrix
open Matrix

variable {ι σ W ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] {T : ℕ}

/-! ## Being fixed by the input projector -/

/-- **Fixed by the input projector = orthogonal to every generator, after the
query.**  `inputProj v a` conjugates the complement projector by one oracle call
on each side, so its fixed space is the pullback along the oracle of the
orthogonal complement of the generators. -/
theorem inputProj_mulVec_eq_self_iff (v : ι' → (QBasis ι σ W → ℂ)) (a : ι → σ)
    (φ : QBasis ι σ W → ℂ) :
    inputProj v a *ᵥ φ = φ ↔ ∀ i, qInner (v i) (oracleMat a *ᵥ φ) = 0 := by
  have hO : ∀ ψ : QBasis ι σ W → ℂ, oracleMat a *ᵥ (oracleMat a *ᵥ ψ) = ψ := fun ψ => by
    rw [Matrix.mulVec_mulVec, oracleMat_mul_self, Matrix.one_mulVec]
  have hsplit : inputProj v a *ᵥ φ
      = oracleMat a *ᵥ (subProj (rawSpan v)ᗮ *ᵥ (oracleMat a *ᵥ φ)) := by
    rw [inputProj, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hsplit]
  constructor
  · intro h
    have h2 := congrArg (fun ψ => oracleMat a *ᵥ ψ) h
    simp only [hO] at h2
    exact (mem_rawSpan_orthogonal_iff v _).mp
      ((subProj_mulVec_eq_self_iff _ _).mp h2)
  · intro h
    rw [(subProj_mulVec_eq_self_iff _ _).mpr ((mem_rawSpan_orthogonal_iff v _).mpr h),
      hO]

/-! ## The positive witness -/

/-- **A positive witness** for the input `a`: fixed by the input projector and by
`L`.  These are the two contracts a state-conversion construction must
discharge; everything below is formal consequence. -/
structure IsPosWitness (v : ι' → (QBasis ι σ W → ℂ))
    (L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (a : ι → σ)
    (φ : QBasis ι σ W → ℂ) : Prop where
  /-- The oracle-rotated witness is orthogonal to every generator. -/
  inputFixed : inputProj v a *ᵥ φ = φ
  /-- The witness lies in the fixed space of `L`. -/
  fixedL : L *ᵥ φ = φ

namespace IsPosWitness

variable {v : ι' → (QBasis ι σ W → ℂ)} {L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
  {a : ι → σ} {φ : QBasis ι σ W → ℂ}

/-- Build a witness from the generator-orthogonality form. -/
theorem of_inner (h : ∀ i, qInner (v i) (oracleMat a *ᵥ φ) = 0) (hL : L *ᵥ φ = φ) :
    IsPosWitness v L a φ :=
  ⟨(inputProj_mulVec_eq_self_iff v a φ).mpr h, hL⟩

/-- **The input reflection fixes the witness.** -/
theorem inputRefl_run_mulVec (h : IsPosWitness v L a φ) :
    (inputRefl v).run a *ᵥ φ = φ := by
  rw [inputRefl_run_eq_qRefl, qRefl, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, h.inputFixed]
  module

/-- **The `L`-reflection fixes the witness.** -/
theorem qRefl_mulVec (h : IsPosWitness v L a φ) : qRefl L *ᵥ φ = φ := by
  rw [qRefl, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h.fixedL]
  module

/-- **The reflection product fixes the witness.**  Both factors do, so the
product does — and this is the hypothesis the detector's completeness theorem
asks for. -/
theorem inputReflProduct_run_mulVec (h : IsPosWitness v L a φ)
    (hL : IsQProjector L) : (inputReflProduct v L hL).run a *ᵥ φ = φ := by
  rw [inputReflProduct_run, ← Matrix.mulVec_mulVec, h.qRefl_mulVec,
    ← inputRefl_run_eq_qRefl, h.inputRefl_run_mulVec]

/-- **Detector completeness, immediately.**  On a uniform clock over a positive
witness the detector is exactly the identity — no error term, at cost
`4(T-1)`. -/
theorem clockPhaseRefl_run_mulVec_uniformClock (h : IsPosWitness v L a φ)
    (hL : IsQProjector L) {T : ℕ} (hT : 0 < T) :
    (clockPhaseRefl (inputReflProduct v L hL) T).run a *ᵥ uniformClock T φ
      = uniformClock T φ :=
  clockPhaseRefl_run_mulVec_uniformClock_of_fixed _ hT a
    (h.inputReflProduct_run_mulVec hL)

/-- The witness lies in the near window for every `Δ`: it is fixed, so its chord
distance is zero. -/
theorem chordNearProj_mulVec (h : IsPosWitness v L a φ) (hL : IsQProjector L)
    (Δ : ℝ) :
    chordNearProj ((inputReflProduct v L hL).run a) Δ *ᵥ φ = φ :=
  chordNearProj_mulVec_of_fixed _ Δ (h.inputReflProduct_run_mulVec hL)

/-- …and therefore contributes nothing to the far window, which is what keeps
the two verdicts apart. -/
theorem chordFarProj_mulVec (h : IsPosWitness v L a φ) (hL : IsQProjector L)
    (Δ : ℝ) :
    chordFarProj ((inputReflProduct v L hL).run a) Δ *ᵥ φ = 0 :=
  chordFarProj_mulVec_of_fixed _ Δ (h.inputReflProduct_run_mulVec hL)

end IsPosWitness

/-! ## Generators are killed by the input projector

`inputProj v a` is `oracleMat a` conjugating the projector onto
`(rawSpan v)ᗮ`.  A generator, carried through the oracle, therefore lands on
the span itself and is annihilated.  This is the one fact the uniform
witness's projector contracts need, and it is generic: nothing about the
particular family `v` enters. -/

/-- **The fixed space of `inputProj`**, in the form a witness can check: one
inner product per generator, no spans. -/
theorem inputProj_mulVec_of_forall_qInner_eq_zero {ι σ W ι' : Type} [Fintype ι]
    [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype W] [DecidableEq W]
    (v : ι' → (QBasis ι σ W → ℂ)) (a : ι → σ) {ψ : QBasis ι σ W → ℂ}
    (h : ∀ p, qInner (v p) (oracleMat a *ᵥ ψ) = 0) :
    inputProj v a *ᵥ ψ = ψ := by
  exact (inputProj_mulVec_eq_self_iff v a ψ).mpr h

theorem inputProj_mulVec_oracle_generator {ι σ W ι' : Type} [Fintype ι]
    [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype W] [DecidableEq W]
    (v : ι' → (QBasis ι σ W → ℂ)) (a : ι → σ) (p : ι') :
    inputProj v a *ᵥ (oracleMat a *ᵥ v p) = 0 := by
  have hmem : (WithLp.toLp 2 (v p) : EuclideanSpace ℂ (QBasis ι σ W))
      ∈ ((rawSpan v)ᗮ)ᗮ :=
    Submodule.le_orthogonal_orthogonal _ (Submodule.subset_span ⟨p, rfl⟩)
  have hzero : subProj (rawSpan v)ᗮ *ᵥ v p = 0 :=
    subProj_mulVec_of_mem_orthogonal _ hmem
  have hinv : oracleMat a *ᵥ (oracleMat a *ᵥ v p) = v p := by
    rw [Matrix.mulVec_mulVec, oracleMat_mul_self, Matrix.one_mulVec]
  rw [inputProj, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv, hzero,
    Matrix.mulVec_zero]

end QuantumQueryComplexity
