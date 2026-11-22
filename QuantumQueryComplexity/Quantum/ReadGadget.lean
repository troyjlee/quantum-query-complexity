import QuantumQueryComplexity.Quantum.Routine
import QuantumQueryComplexity.Quantum.Measurement
import QuantumQueryComplexity.Quantum.SelectRoutine

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Reads-controlled unitaries: the read gadget

A workspace holds a **control register** `C` and a **target register** `D`. For every control
value `c` fix `k` addresses `addr c j : Option ι` (`j < k`; `none` means "do not read"), and for
every control value and every content `s : Fin k → Option σ` of `k` answer slots a unitary
`M c s` on `D`. The **reads-controlled operator** (`readCtrlMat addr M x`) is

  `|c⟩|d⟩ ↦ |c⟩ ⊗ M c (readAnswers addr x c) |d⟩`,

where slot `j` of `readAnswers addr x c` is `some (x i)` when `addr c j = some i` and blank
(`none`) when the address is idle. It depends on the input `x` only through the letters read,
and the reads may differ from one control value to another.

`exists_readGadget` realizes it with **one routine, fixed before the input, of exactly `2k`
queries** to the library's swap oracle (`oracleMat`, `Oracle.lean`): read the `k` addresses into
`k` blank scratch slots (a swap query writes `x i` into a blank answer register), apply the
fixed unitary `M c s` controlled by `c` and the scratch content `s`, and read the same addresses
again (the second swap query on a slot holding `x i` blanks it). The statement is about the
**parked sector** (`readPark`): the gadget's own query index idle, its answer register blank and
every scratch slot blank. There the routine acts as `readCtrlMat addr M x`, for every input `x`;
off that sector nothing is claimed. The hypothesis asks every block `M c s` to be unitary, for
*every* scratch content `s` and not only for the answers that occur: it makes the prescribed
middle gate, one fixed gate for all inputs acting on every scratch content, unitary on its whole
basis. (Blocks at scratch contents that never occur do not affect the action on the parked
sector; the hypothesis is a convenient sufficient condition, not a necessary one.)

This generalizes `WordSim.block` of the companion repository `quantum-query-problems` (gather,
act, ungather) from a swap of a decoded value to an arbitrary controlled unitary, with the swap
oracle in place of the word-XOR oracle.

`readLift` lifts a fixed operator on the control and target registers to the gadget's basis (no
queries), so that read gadgets and free unitaries compose with `QRoutine.comp` on the parked
sector; `qInner_readPark` and `qProb_readPark` say that parking is an isometric embedding that
a readout of the control and target registers sees unchanged.

## Proof

The routine is `gather.conjFixed middle` (`QRoutine.conjFixed`). `ReadGadget.gather` makes one
query per slot `j`: a fixed permutation exchanges the idle query index with `addr c j` and the
answer register with slot `j`, the query fills the blank answer, and the same permutation moves
the answer into slot `j` and idles the index again. On a parked basis state it writes
`readAnswers addr x c` into the scratch (`ReadGadget.gather_mulVec_readPark`). `ReadGadget.middle`
applies `M c s` to the target, controlled by `c` and the scratch content `s`; then `gather` is
undone, which blanks the scratch again because `gather` is unitary.

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

/-- The reads-controlled operator is the family `c ↦ M c (readAnswers addr x c)` made block
diagonal in the control register (`ctrlLift`, `SelectRoutine.lean`). -/
theorem readCtrlMat_eq_ctrlLift (addr : C → Fin k → Option ι)
    (M : C → ReadScratch σ k → Matrix D D ℂ) (x : ι → σ) :
    readCtrlMat addr M x =
      ctrlLift (Equiv.prodComm C D) fun c => M c (readAnswers addr x c) := by
  ext p p'
  simp [readCtrlMat, ctrlLift, Matrix.blockDiagonal_apply]

/-- **What the reads-controlled operator does**: at the basis state `(c, d)` of the output, it
applies the block `M c (readAnswers addr x c)` to the slice `d' ↦ Φ (c, d')` of `Φ` at the
same control value. -/
theorem readCtrlMat_mulVec_apply (addr : C → Fin k → Option ι)
    (M : C → ReadScratch σ k → Matrix D D ℂ) (x : ι → σ) (Φ : C × D → ℂ) (c : C) (d : D) :
    (readCtrlMat addr M x *ᵥ Φ) (c, d) =
      (M c (readAnswers addr x c) *ᵥ fun d' => Φ (c, d')) d := by
  rw [readCtrlMat_eq_ctrlLift, ctrlLift_mulVec_apply]
  rfl

/-- The reads-controlled operator is unitary for every input `x`, provided every block `M c s`
is unitary. -/
theorem readCtrlMat_mem_unitaryGroup (addr : C → Fin k → Option ι)
    {M : C → ReadScratch σ k → Matrix D D ℂ} (hM : ∀ c s, M c s ∈ Matrix.unitaryGroup D ℂ)
    (x : ι → σ) : readCtrlMat addr M x ∈ Matrix.unitaryGroup (C × D) ℂ := by
  rw [readCtrlMat_eq_ctrlLift]
  exact ctrlLift_mem_unitaryGroup _ fun c => hM c _

namespace ReadGadget

/-- The gadget's basis split into the control and target registers and the rest: the query
index, the answer register and the scratch slots. -/
def parkEquiv : QBasis ι σ (ReadWork σ C D k) ≃ (C × D) × (Option ι × Option σ × ReadScratch σ k)
    where
  toFun p := (p.2.2.2, p.1, p.2.1, p.2.2.1)
  invFun q := (q.2.1, q.2.2.1, q.2.2.2, q.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The parked content of the query index, the answer register and the scratch slots. -/
def parkBlank : Option ι × Option σ × ReadScratch σ k := (none, none, blankScratch)

/-- A parked vector is `Φ` on the control and target registers, split from the basis vector
`parkBlank` on the rest. -/
theorem readPark_eq_splitVec (Φ : C × D → ℂ) :
    readPark (ι := ι) (σ := σ) (k := k) Φ = splitVec parkEquiv Φ (qBasis parkBlank) := by
  funext p
  simp [readPark, splitVec, parkEquiv, parkBlank, qBasis_apply, mul_ite]

/-- A lifted operator is `U ⊗ 1` through `parkEquiv` (`kronLift`, `KronLift.lean`). -/
theorem readLift_eq_kronLift (U : Matrix (C × D) (C × D) ℂ) :
    readLift (ι := ι) (σ := σ) (k := k) U = kronLift parkEquiv U := by
  ext p q
  simp [readLift, kronLift, parkEquiv, Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite]

end ReadGadget

open ReadGadget in
/-- A lifted unitary is unitary. -/
theorem readLift_mem_unitaryGroup {U : Matrix (C × D) (C × D) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (C × D) ℂ) :
    readLift (ι := ι) (σ := σ) (k := k) U ∈
      Matrix.unitaryGroup (QBasis ι σ (ReadWork σ C D k)) ℂ := by
  rw [readLift_eq_kronLift]
  exact kronLift_mem_unitaryGroup _ hU

open ReadGadget in
/-- **A lifted operator acts on parked vectors as the operator itself.** -/
theorem readLift_mulVec_readPark (U : Matrix (C × D) (C × D) ℂ) (Φ : C × D → ℂ) :
    readLift (ι := ι) (σ := σ) (k := k) U *ᵥ readPark Φ = readPark (U *ᵥ Φ) := by
  rw [readLift_eq_kronLift, readPark_eq_splitVec, readPark_eq_splitVec, kronLift_mulVec_splitVec]

/-- **Parking is an isometric embedding**: it preserves inner products. -/
theorem qInner_readPark (Φ Ψ : C × D → ℂ) :
    qInner (readPark (ι := ι) (σ := σ) (k := k) Φ) (readPark Ψ) = qInner Φ Ψ := by
  simp [qInner_def, readPark, Fintype.sum_prod_type]

/-- **A readout of the control and target registers sees a parked vector unchanged**: for every
readout `r` of the control and target registers and every outcome `o`, measuring the parked
vector with `r` applied to those registers gives the probability of `o` for `Φ`. -/
theorem qProb_readPark {O : Type} [DecidableEq O] (r : C × D → O) (Φ : C × D → ℂ) (o : O) :
    qProb (fun p : QBasis ι σ (ReadWork σ C D k) => r p.2.2.2) (readPark Φ) o = qProb r Φ o := by
  simp only [qProb, readPark, Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single none fun i hi => by simp [hi],
    Fintype.sum_eq_single none fun a ha => by simp [ha],
    Fintype.sum_eq_single blankScratch fun s hs => by simp [hs]]
  simp

namespace ReadGadget

variable (addr : C → Fin k → Option ι)

/-- **Routing for slot `j`**: exchange the idle query index with the address `addr c j` of the
control value `c`, and the answer register with scratch slot `j`. A fixed involution of the
gadget's basis. -/
def route (j : Fin k) : QBasis ι σ (ReadWork σ C D k) → QBasis ι σ (ReadWork σ C D k)
  | (i, a, s, c, d) => (Equiv.swap none (addr c j) i, s j, Function.update s j a, c, d)

theorem route_involutive (j : Fin k) : Function.Involutive (route (σ := σ) (D := D) addr j) := by
  rintro ⟨i, a, s, c, d⟩
  simp [route, Function.update_idem]

/-- One read into slot `j`: route, query, route back. One query. -/
def call (j : Fin k) : QRoutine ι σ (ReadWork σ C D k) :=
  let g : QRoutine ι σ (ReadWork σ C D k) :=
    QRoutine.ofUnitary (qPerm ((route_involutive addr j).toPerm _)) (qPerm_mem_unitaryGroup _)
  (g.comp QRoutine.query).comp g

/-- The basis state with the query index idle, the answer register blank, scratch `s`, control
and target `z`. -/
def parkedAt (s : ReadScratch σ k) (z : C × D) : QBasis ι σ (ReadWork σ C D k) :=
  (none, none, s, z)

/-- A read into a blank slot `j` writes the answer of address `addr c j` there (blank if the
address is idle) and leaves the query registers idle and blank. -/
theorem call_run_parkedAt (x : ι → σ) (j : Fin k) (s : ReadScratch σ k) (z : C × D)
    (h : s j = none) :
    (call addr j).run x *ᵥ qBasis (parkedAt s z) =
      qBasis (parkedAt (Function.update s j (readAnswers addr x z.1 j)) z) := by
  simp only [call, QRoutine.comp_run, QRoutine.ofUnitary_run, QRoutine.query_run,
    ← Matrix.mulVec_mulVec, qPerm_mulVec_qBasis, oracleMat_mulVec_qBasis]
  congr 1
  change route addr j (oracleMap x (route addr j (parkedAt s z))) = _
  rcases z with ⟨c, d⟩
  cases ha : addr c j <;>
    simp [parkedAt, route, ha, h, readAnswers, oracleMap, Function.update_idem]

/-- **The gathering pass**: reads into the slots `0, …, m − 1` in order (`m ≤ k`). -/
def gather : ℕ → QRoutine ι σ (ReadWork σ C D k)
  | 0 => QRoutine.identity
  | m + 1 => if h : m < k then (gather m).comp (call addr ⟨m, h⟩) else gather m

theorem gather_len (m : ℕ) (hm : m ≤ k) : (gather (σ := σ) (D := D) addr m).len = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h : m < k := hm
    simp [gather, h, ih h.le, call]

/-- The answers of the first `m` slots, the others blank. -/
def partialAnswers (x : ι → σ) (c : C) (m : ℕ) : ReadScratch σ k :=
  fun j => if j.val < m then readAnswers addr x c j else none

theorem gather_run_parkedAt (x : ι → σ) (z : C × D) (m : ℕ) (hm : m ≤ k) :
    (gather addr m).run x *ᵥ qBasis (parkedAt blankScratch z) =
      qBasis (parkedAt (partialAnswers addr x z.1 m) z) := by
  induction m with
  | zero =>
    have hz : partialAnswers addr x z.1 0 = blankScratch := by
      funext j
      simp [partialAnswers, blankScratch]
    simp [gather, hz]
  | succ m ih =>
    have h : m < k := hm
    let j : Fin k := ⟨m, h⟩
    have blank : partialAnswers addr x z.1 m j = none := by simp [partialAnswers, j]
    rw [gather, dite_eq_left h, QRoutine.comp_run, ← Matrix.mulVec_mulVec, ih h.le,
      call_run_parkedAt _ _ j _ _ blank]
    congr 2
    funext l
    by_cases hl : l = j
    · subst l
      simp [j, partialAnswers]
    · have hn : l.val ≠ m := fun he => hl (Fin.ext he)
      simp [Function.update_of_ne hl, partialAnswers,
        show (l.val < m + 1) ↔ l.val < m by omega]

/-- `Φ` on the control and target registers, with the query registers idle and blank and the
scratch holding `s c` at the control value `c`. -/
def parkWith (s : C → ReadScratch σ k) (Φ : C × D → ℂ) : QBasis ι σ (ReadWork σ C D k) → ℂ :=
  fun p => if p.1 = none ∧ p.2.1 = none ∧ p.2.2.1 = s p.2.2.2.1 then Φ p.2.2.2 else 0

theorem parkWith_eq_sum (s : C → ReadScratch σ k) (Φ : C × D → ℂ) :
    parkWith (ι := ι) s Φ = ∑ z, Φ z • qBasis (parkedAt (s z.1) z) := by
  funext p
  rw [Finset.sum_apply, Finset.sum_eq_single p.2.2.2]
  · rcases p with ⟨i, a, s', c, d⟩
    simp [parkWith, parkedAt, qBasis_apply, mul_ite]
  · intro z _ hz
    have hne : p ≠ parkedAt (s z.1) z := fun e =>
      hz ((congrArg (fun v : QBasis ι σ (ReadWork σ C D k) => v.2.2.2) e).symm)
    simp [qBasis_apply, hne]
  · simp

/-- **The gathering pass on a parked vector** writes the answers of each control value into the
scratch. -/
theorem gather_mulVec_readPark (x : ι → σ) (Φ : C × D → ℂ) :
    (gather addr k).run x *ᵥ readPark Φ = parkWith (readAnswers addr x) Φ := by
  change (gather addr k).run x *ᵥ parkWith (fun _ => blankScratch) Φ = _
  have full (c : C) : partialAnswers addr x c k = readAnswers addr x c := by
    funext j
    simp [partialAnswers]
  simp only [parkWith_eq_sum, Matrix.mulVec_sum, Matrix.mulVec_smul,
    gather_run_parkedAt addr x _ k le_rfl, full]

/-- The gadget's basis split into the target register and the rest. -/
def targetEquiv : QBasis ι σ (ReadWork σ C D k) ≃ D × (Option ι × Option σ × ReadScratch σ k × C)
    where
  toFun p := (p.2.2.2.2, p.1, p.2.1, p.2.2.1, p.2.2.2.1)
  invFun q := (q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2, q.1)
  left_inv _ := rfl
  right_inv _ := rfl

variable (M : C → ReadScratch σ k → Matrix D D ℂ)

/-- **The middle gate**: `M c s` on the target register, controlled by the control value `c`
and the scratch content `s`. It does not depend on the input. -/
def middle : Matrix (QBasis ι σ (ReadWork σ C D k)) (QBasis ι σ (ReadWork σ C D k)) ℂ :=
  ctrlLift targetEquiv fun g => M g.2.2.2 g.2.2.1

theorem middle_mem_unitaryGroup (hM : ∀ c s, M c s ∈ Matrix.unitaryGroup D ℂ) :
    middle (ι := ι) M ∈ Matrix.unitaryGroup (QBasis ι σ (ReadWork σ C D k)) ℂ :=
  ctrlLift_mem_unitaryGroup _ fun g => hM g.2.2.2 g.2.2.1

/-- On the gathered vector the middle gate acts as the reads-controlled operator. -/
theorem middle_mulVec_parkWith (x : ι → σ) (Φ : C × D → ℂ) :
    middle (ι := ι) M *ᵥ parkWith (readAnswers addr x) Φ =
      parkWith (readAnswers addr x) (readCtrlMat addr M x *ᵥ Φ) := by
  funext p
  rcases p with ⟨i, a, s, c, d⟩
  rw [middle, ctrlLift_mulVec_apply]
  by_cases hp : i = none ∧ a = none ∧ s = readAnswers addr x c
  · rcases hp with ⟨rfl, rfl, rfl⟩
    rw [show parkWith (readAnswers addr x) (readCtrlMat addr M x *ᵥ Φ)
        (none, none, readAnswers addr x c, c, d) = (readCtrlMat addr M x *ᵥ Φ) (c, d) by
      simp [parkWith], readCtrlMat_mulVec_apply]
    simp [targetEquiv, parkWith, Matrix.mulVec, dotProduct]
  · simp [targetEquiv, parkWith, hp]

end ReadGadget

/-- **The read gadget.** Let `addr c j : Option ι` (`j < k`) be the addresses read for the
control value `c` (`none` = no read), and let every `M c s` be unitary on the target register
`D`, for every control value `c` and every scratch content `s`. Then one routine `R`, built from
`addr` and `M` alone (before any input is fixed), makes exactly `2k` swap queries and, for
**every** input `x : ι → σ` and every vector `Φ` on the control and target registers, maps the
parked vector of `Φ` to the parked vector of `readCtrlMat addr M x *ᵥ Φ`:

  `|c⟩|d⟩ ↦ |c⟩ ⊗ M c (readAnswers addr x c) |d⟩`

(slot `j` of the answers is `some (x i)` for `addr c j = some i`, blank for an idle address) with
the query index left idle, the answer register blank and the scratch slots blank. -/
theorem exists_readGadget (addr : C → Fin k → Option ι)
    (M : C → ReadScratch σ k → Matrix D D ℂ) (hM : ∀ c s, M c s ∈ Matrix.unitaryGroup D ℂ) :
    ∃ R : QRoutine ι σ (ReadWork σ C D k), R.len = 2 * k ∧
      ∀ (x : ι → σ) (Φ : C × D → ℂ),
        R.run x *ᵥ readPark Φ = readPark (readCtrlMat addr M x *ᵥ Φ) := by
  refine ⟨(ReadGadget.gather addr k).conjFixed (ReadGadget.middle M)
    (ReadGadget.middle_mem_unitaryGroup M hM), ?_, fun x Φ => ?_⟩
  · rw [QRoutine.conjFixed_len, ReadGadget.gather_len addr k le_rfl]
  · rw [QRoutine.conjFixed_run, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ReadGadget.gather_mulVec_readPark, ReadGadget.middle_mulVec_parkWith,
      ← ReadGadget.gather_mulVec_readPark, Matrix.mulVec_mulVec,
      conjTranspose_mul_self_of_unitary (QRoutine.run_mem_unitaryGroup _ x), Matrix.one_mulVec]

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
