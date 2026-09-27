import QuantumQueryComplexity.Quantum.Projector
import QuantumQueryComplexity.Quantum.Routine
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The input-dependent reflection, in exactly two queries

Step 2 of the Milestone B route.  The reflection the upper bound needs is about
the orthogonal complement of a span of input-dependent vectors; it is built as

  `O_a · (fixed reflection) · O_a`,

one query on each side of a fixed unitary, and **that is exactly two queries** —
`QRoutine.conjFixed` costs `2 · R.len`, and inversion is free because the
transposition oracle is self-adjoint.

**The sign is part of the statement.**  `spanRefl v` fixes the span, but the
construction reflects about the *complement*, and
`subRefl (rawSpan v)ᗮ = -spanRefl v`.  Dropping that minus would shift every
eigenphase by `π`, which controlled phase detection would then read off wrongly.
`inputRefl_run` therefore carries the negation explicitly.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-- **The input-dependent reflection**: reflect about the orthogonal complement
of a span, conjugated by one query on each side. -/
noncomputable def inputRefl (v : ι' → (QBasis ι σ W → ℂ)) : QRoutine ι σ W :=
  QRoutine.query.conjFixed (subRefl (rawSpan v)ᗮ) (subRefl_mem_unitaryGroup _)

/-- **Exactly two queries.** -/
@[simp] theorem inputRefl_len (v : ι' → (QBasis ι σ W → ℂ)) :
    (inputRefl v).len = 2 := by
  rw [inputRefl, QRoutine.conjFixed_len, QRoutine.query_len]

/-- **The operator it implements**, with the complement's sign explicit. -/
theorem inputRefl_run (v : ι' → (QBasis ι σ W → ℂ)) (a : ι → σ) :
    (inputRefl v).run a = oracleMat a * (-spanRefl v * oracleMat a) := by
  rw [inputRefl, QRoutine.conjFixed_run, QRoutine.query_run,
    QRoutine.oracleMat_conjTranspose, spanRefl_orthogonal]

/-- The same, before the sign is resolved: it is the conjugate of the
complement reflection. -/
theorem inputRefl_run' (v : ι' → (QBasis ι σ W → ℂ)) (a : ι → σ) :
    (inputRefl v).run a = oracleMat a * (subRefl (rawSpan v)ᗮ * oracleMat a) := by
  rw [inputRefl, QRoutine.conjFixed_run, QRoutine.query_run,
    QRoutine.oracleMat_conjTranspose]

/-! ## The bridge to the mathematical layer

The effective-gap theorem is cleanest stated for an arbitrary projector.  This
is the projector the operational two-query reflection actually reflects about,
so the final algorithm can instantiate the abstract theorem with it. -/

/-- **The input-dependent projector**: the fixed complement projector,
conjugated by one query on each side. -/
noncomputable def inputProj (v : ι' → (QBasis ι σ W → ℂ)) (a : ι → σ) :
    Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ :=
  oracleMat a * subProj (rawSpan v)ᗮ * oracleMat a

theorem isQProjector_inputProj (v : ι' → (QBasis ι σ W → ℂ)) (a : ι → σ) :
    IsQProjector (inputProj v a) := by
  have h := (isQProjector_subProj (rawSpan v)ᗮ).conj (oracleMat_mem_unitaryGroup a)
  rwa [QRoutine.oracleMat_conjTranspose] at h

/-- **The operational reflection is the reflection about that projector.** -/
theorem inputRefl_run_eq_qRefl (v : ι' → (QBasis ι σ W → ℂ)) (a : ι → σ) :
    (inputRefl v).run a = qRefl (inputProj v a) := by
  rw [inputRefl_run', qRefl, inputProj, subRefl, qRefl, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, oracleMat_mul_self]
  simp only [Matrix.mul_assoc]

/-! ## The composition-order trap

`QRoutine.comp` composes in **execution** order, while the matrix product
composes in the opposite one: `comp_run : (R.comp S).run a = S.run a * R.run a`.
So the operator `R_P · R_L` — the one the effective-gap theorem takes — is
implemented by running `L` **first**, i.e. by `RL.comp RP`.  Getting this
backwards would silently build `R_L · R_P`, whose spectrum is the same but whose
eigenvectors are not, so it is pinned here as a theorem rather than a comment. -/

/-- **The reflection product, in execution order.** -/
theorem comp_run_eq_qRefl_mul {RP RL : QRoutine ι σ W}
    {P L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ} (a : ι → σ)
    (hP : RP.run a = qRefl P) (hL : RL.run a = qRefl L) :
    (RL.comp RP).run a = qRefl P * qRefl L := by
  rw [QRoutine.comp_run, hP, hL]

@[simp] lemma comp_len_reflProd (RP RL : QRoutine ι σ W) :
    (RL.comp RP).len = RL.len + RP.len := rfl

/-! ## The reflection product

`effective_chord_gap_sq` consumes `qRefl P * qRefl L`.  This definition builds
exactly that operator as a routine, and in doing so **pins the two facts a query
count depends on**:

* the **order** — `L` is run first, so the operator is `R_P · R_L` and not its
  reverse (see the trap above);
* the **cost** — the `L`-side reflection is a *fixed*, input-independent unitary,
  supplied as a zero-query `ofUnitary`.  So the product costs exactly the two
  queries of the input-dependent side.  `inputRefl_len = 2` on its own says
  nothing about this: if both sides were input-dependent the product would cost
  four, and every downstream clock estimate would double.

`inputReflProduct_len` is therefore the theorem that licenses the `2` in the
detector's query accounting.  The specialization of the effective-gap theorem to
this routine lives in `OperationalGap.lean`, not here: this file is a basic
reflection client and should not drag the functional calculus in with it. -/

/-- **The reflection product** `R_P · R_L`, with `R_L` a fixed zero-query
reflection and `R_P` the input-dependent two-query reflection. -/
noncomputable def inputReflProduct (v : ι' → (QBasis ι σ W → ℂ))
    (L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (hL : IsQProjector L) :
    QRoutine ι σ W :=
  (QRoutine.ofUnitary (qRefl L) (qRefl_mem_unitaryGroup hL)).comp (inputRefl v)

/-- **Exactly two queries** — because the `L`-side is fixed. -/
@[simp] theorem inputReflProduct_len (v : ι' → (QBasis ι σ W → ℂ))
    (L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (hL : IsQProjector L) :
    (inputReflProduct v L hL).len = 2 := by
  rw [inputReflProduct, QRoutine.comp_len, QRoutine.ofUnitary_len, inputRefl_len]

/-- **The operator it implements**, in the order `effective_chord_gap_sq`
expects. -/
theorem inputReflProduct_run (v : ι' → (QBasis ι σ W → ℂ))
    (L : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (hL : IsQProjector L) (a : ι → σ) :
    (inputReflProduct v L hL).run a = qRefl (inputProj v a) * qRefl L := by
  rw [inputReflProduct, QRoutine.comp_run, QRoutine.ofUnitary_run,
    inputRefl_run_eq_qRefl]

theorem inputRefl_run_mem_unitaryGroup (v : ι' → (QBasis ι σ W → ℂ)) (a : ι → σ) :
    (inputRefl v).run a ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ :=
  QRoutine.run_mem_unitaryGroup _ a

end QuantumQueryComplexity
