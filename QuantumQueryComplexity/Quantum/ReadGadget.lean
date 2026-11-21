import QuantumQueryComplexity.Quantum.Routine
import QuantumQueryComplexity.Quantum.Measurement

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Reads-controlled unitaries: the read gadget

A workspace holds a **control register** `C` and a **target register** `D`. For every control
value `c` fix `k` addresses `addr c j : Option ι` (`j < k`; `none` means "do not read"), and for
every control value and every content of `k` answer slots a unitary `M c s` on `D`. The
**reads-controlled operator** (`readCtrlMat addr M x`) is

  `|c⟩|d⟩ ↦ |c⟩ ⊗ M c (x (addr c 0), …, x (addr c (k − 1))) |d⟩`,

where an idle address contributes a blank slot (`readAnswers`). It depends on the input `x`
only through the `k` letters read, and the reads may differ from one control value to another.

`exists_readGadget` realizes it with **one routine, fixed before the input, of exactly `2k`
queries** to the library's swap oracle (`oracleMat`, `Oracle.lean`): read the `k` addresses into
`k` blank scratch slots (a swap query writes `x i` into a blank answer register), apply the
fixed unitary `M c s` controlled by `c` and the scratch content `s`, and read the same addresses
again (the second swap query on a slot holding `x i` blanks it). The statement is about the
**parked sector** (`readPark`): the gadget's own query index idle, its answer register blank and
every scratch slot blank. There the routine acts as `readCtrlMat addr M x`, for every input `x`;
off that sector nothing is claimed. The unitaries `M c s` must be unitary for *every* scratch
content `s`, not only for the answers that occur, because the middle step of the routine is one
fixed unitary for all inputs.

This generalizes `WordSim.block` of the companion repository `quantum-query-problems` (gather,
act, ungather) from a swap of a decoded value to an arbitrary controlled unitary, with the swap
oracle in place of the word-XOR oracle.

`readLift` lifts a fixed operator on the control and target registers to the gadget's basis (no
queries), so that read gadgets and free unitaries compose with `QRoutine.comp` on the parked
sector; `qInner_readPark` and `qProb_readPark` say that parking is an isometric embedding that
a readout of the control and target registers sees unchanged.

## Main statements

* `exists_readGadget` — the read gadget: one routine with `2k` queries acting as
  `readCtrlMat addr M x` on parked vectors, for every input `x`.
* `readGadget`, `readGadget_len`, `readGadget_run_readPark` — the routine, chosen once.
* `readCtrlMat_mulVec_apply`, `readCtrlMat_mem_unitaryGroup` — what the operator does, and
  that it is unitary for every input.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ C D : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D] {k : ℕ}

/-- The scratch registers of the read gadget: `k` answer slots, each blank (`none`) or holding a
letter `some s`. -/
abbrev ReadScratch (σ : Type) (k : ℕ) : Type := Fin k → Option σ

/-- The blank scratch: every slot holds `none`. -/
def blankScratch : ReadScratch σ k := fun _ => none

/-- The workspace of the read gadget: the `k` scratch slots, then the control register `C` and
the target register `D`. -/
abbrev ReadWork (σ C D : Type) (k : ℕ) : Type := ReadScratch σ k × C × D

/-- What the `k` reads of the control value `c` return on the input `x`: slot `j` holds
`some (x i)` when `addr c j = some i`, and stays blank when `addr c j = none`. -/
def readAnswers (addr : C → Fin k → Option ι) (x : ι → σ) (c : C) : ReadScratch σ k :=
  fun j => (addr c j).map x

/-- **The reads-controlled operator** on the control and target registers:
`|c⟩|d⟩ ↦ |c⟩ ⊗ M c (readAnswers addr x c) |d⟩`. It is block diagonal in `c`, with block
`M c (readAnswers addr x c)`; it depends on the input `x` only through the letters at the
addresses `addr c j`. -/
def readCtrlMat (addr : C → Fin k → Option ι) (M : C → ReadScratch σ k → Matrix D D ℂ)
    (x : ι → σ) : Matrix (C × D) (C × D) ℂ :=
  Matrix.of fun p p' => if p.1 = p'.1 then M p.1 (readAnswers addr x p.1) p.2 p'.2 else 0

/-- A vector `Φ` on the control and target registers, **parked** in the gadget's basis: the query
index idle (`none`), the answer register blank (`none`), every scratch slot blank, and `Φ` on
the control and target registers. -/
def readPark (Φ : C × D → ℂ) : QBasis ι σ (ReadWork σ C D k) → ℂ :=
  fun p => if p.1 = none ∧ p.2.1 = none ∧ p.2.2.1 = blankScratch then Φ p.2.2.2 else 0

/-- A fixed operator `U` on the control and target registers, lifted to the gadget's basis: it
acts as `U` on the control and target registers and as the identity on the query index, the
answer register and the scratch slots. It makes no query. -/
def readLift (U : Matrix (C × D) (C × D) ℂ) :
    Matrix (QBasis ι σ (ReadWork σ C D k)) (QBasis ι σ (ReadWork σ C D k)) ℂ :=
  Matrix.of fun p p' =>
    if p.1 = p'.1 ∧ p.2.1 = p'.2.1 ∧ p.2.2.1 = p'.2.2.1 then U p.2.2.2 p'.2.2.2 else 0

/-- **What the reads-controlled operator does**: at the basis state `(c, d)` of the output, it
applies the block `M c (readAnswers addr x c)` to the slice `d' ↦ Φ (c, d')` of `Φ` at the
same control value. -/
theorem readCtrlMat_mulVec_apply (addr : C → Fin k → Option ι)
    (M : C → ReadScratch σ k → Matrix D D ℂ) (x : ι → σ) (Φ : C × D → ℂ) (c : C) (d : D) :
    (readCtrlMat addr M x *ᵥ Φ) (c, d) =
      (M c (readAnswers addr x c) *ᵥ fun d' => Φ (c, d')) d := by
  sorry

/-- The reads-controlled operator is unitary for every input `x`, provided every block `M c s`
is unitary. -/
theorem readCtrlMat_mem_unitaryGroup (addr : C → Fin k → Option ι)
    {M : C → ReadScratch σ k → Matrix D D ℂ} (hM : ∀ c s, M c s ∈ Matrix.unitaryGroup D ℂ)
    (x : ι → σ) : readCtrlMat addr M x ∈ Matrix.unitaryGroup (C × D) ℂ := by
  sorry

/-- A lifted unitary is unitary. -/
theorem readLift_mem_unitaryGroup {U : Matrix (C × D) (C × D) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (C × D) ℂ) :
    readLift (ι := ι) (σ := σ) (k := k) U ∈
      Matrix.unitaryGroup (QBasis ι σ (ReadWork σ C D k)) ℂ := by
  sorry

/-- **A lifted operator acts on parked vectors as the operator itself.** -/
theorem readLift_mulVec_readPark (U : Matrix (C × D) (C × D) ℂ) (Φ : C × D → ℂ) :
    readLift (ι := ι) (σ := σ) (k := k) U *ᵥ readPark Φ = readPark (U *ᵥ Φ) := by
  sorry

/-- **Parking is an isometric embedding**: it preserves inner products. -/
theorem qInner_readPark (Φ Ψ : C × D → ℂ) :
    qInner (readPark (ι := ι) (σ := σ) (k := k) Φ) (readPark Ψ) = qInner Φ Ψ := by
  sorry

/-- **A readout of the control and target registers sees a parked vector unchanged**: for every
readout `r` of the control and target registers and every outcome `o`, measuring the parked
vector with `r` applied to those registers gives the probability of `o` for `Φ`. -/
theorem qProb_readPark {O : Type} [DecidableEq O] (r : C × D → O) (Φ : C × D → ℂ) (o : O) :
    qProb (fun p : QBasis ι σ (ReadWork σ C D k) => r p.2.2.2) (readPark Φ) o = qProb r Φ o := by
  sorry

/-- **The read gadget.** Let `addr c j : Option ι` (`j < k`) be the addresses read for the
control value `c` (`none` = no read), and let every `M c s` be unitary on the target register
`D`, for every control value `c` and every scratch content `s`. Then one routine `R`, built from
`addr` and `M` alone (before any input is fixed), makes exactly `2k` swap queries and, for
**every** input `x : ι → σ` and every vector `Φ` on the control and target registers, maps the
parked vector of `Φ` to the parked vector of `readCtrlMat addr M x *ᵥ Φ`:

  `|c⟩|d⟩ ↦ |c⟩ ⊗ M c (x (addr c 0), …, x (addr c (k − 1))) |d⟩`

with the query index left idle, the answer register blank and the scratch slots blank. -/
theorem exists_readGadget (addr : C → Fin k → Option ι)
    (M : C → ReadScratch σ k → Matrix D D ℂ) (hM : ∀ c s, M c s ∈ Matrix.unitaryGroup D ℂ) :
    ∃ R : QRoutine ι σ (ReadWork σ C D k), R.len = 2 * k ∧
      ∀ (x : ι → σ) (Φ : C × D → ℂ),
        R.run x *ᵥ readPark Φ = readPark (readCtrlMat addr M x *ᵥ Φ) := by
  sorry

/-- **The read gadget**, chosen once from `exists_readGadget`: a routine of `2k` swap queries
acting as `readCtrlMat addr M x` on parked vectors, for every input `x`
(`readGadget_len`, `readGadget_run_readPark`). -/
noncomputable def readGadget (addr : C → Fin k → Option ι)
    (M : C → ReadScratch σ k → Matrix D D ℂ) (hM : ∀ c s, M c s ∈ Matrix.unitaryGroup D ℂ) :
    QRoutine ι σ (ReadWork σ C D k) :=
  (exists_readGadget addr M hM).choose

/-- The read gadget makes exactly `2k` queries. -/
@[simp] theorem readGadget_len (addr : C → Fin k → Option ι)
    (M : C → ReadScratch σ k → Matrix D D ℂ) (hM : ∀ c s, M c s ∈ Matrix.unitaryGroup D ℂ) :
    (readGadget addr M hM).len = 2 * k :=
  (exists_readGadget addr M hM).choose_spec.1

/-- On parked vectors the read gadget acts as the reads-controlled operator, for every input. -/
theorem readGadget_run_readPark (addr : C → Fin k → Option ι)
    (M : C → ReadScratch σ k → Matrix D D ℂ) (hM : ∀ c s, M c s ∈ Matrix.unitaryGroup D ℂ)
    (x : ι → σ) (Φ : C × D → ℂ) :
    (readGadget addr M hM).run x *ᵥ readPark Φ = readPark (readCtrlMat addr M x *ᵥ Φ) :=
  (exists_readGadget addr M hM).choose_spec.2 x Φ

end QuantumQueryComplexity
