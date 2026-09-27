import QuantumQueryComplexity.Quantum.KronLift
set_option synthInstance.maxSize 1600

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The independent-run compiler: exact product statistics

Two algorithms, compiled into one whose outcome distribution is the **exact
product** of theirs — the engine of amplification and of the finite-output
construction.

**Banks, not uncompute.**  The compiled workspace holds a full
`QBasis ι σ Wⱼ`-valued *bank* for each algorithm; the global initial state is
the tensor product of the two initial states parked in their banks, with
blank global query registers.  Phase `j` swaps bank `j` into the active
position (a basis permutation exchanging the global query/answer registers
with the bank's stored pair), runs algorithm `j`'s schedule lifted along the
oracle-compatible equivalence `pairEquivⱼ` (`KronLift.lean`), and swaps back.
Each phase therefore acts on a pristine tensor factor: no uncompute, no
factor two in the cost, and the final state is **literally**

    prodState blank (A₁.state a q₁) (A₂.state a q₂),

so the joint measurement factorizes exactly (`qProb_pairReadout`).

`Realizes read q P` packages "some algorithm has outcome distribution `P`
after `q` queries"; `Realizes.pair` is the compiler, `Realizes.map` reshapes
outcomes through the readout for free, and `Realizes.fold` iterates the pair
into a `k`-tuple with product statistics at cost `∑ qⱼ`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂]
  [DecidableEq W₂]

/-! ## The two factorizing equivalences and the two swaps -/

/-- Phase 1's view: system = (global registers, bank 1's workspace),
environment = (bank 1's parked registers, bank 2). -/
def pairEquiv₁ : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂)
    ≃ QBasis ι σ W₁ × ((Option ι × Option σ) × QBasis ι σ W₂) where
  toFun p := ((p.1, p.2.1, p.2.2.1.2.2), ((p.2.2.1.1, p.2.2.1.2.1), p.2.2.2))
  invFun q := (q.1.1, q.1.2.1, ((q.2.1.1, q.2.1.2, q.1.2.2), q.2.2))
  left_inv := by rintro ⟨idx, ans, ⟨⟨i₁, a₁, w₁⟩, β₂⟩⟩; rfl
  right_inv := by rintro ⟨⟨idx, ans, w₁⟩, ⟨⟨i₁, a₁⟩, β₂⟩⟩; rfl

/-- Phase 2's view. -/
def pairEquiv₂ : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂)
    ≃ QBasis ι σ W₂ × ((Option ι × Option σ) × QBasis ι σ W₁) where
  toFun p := ((p.1, p.2.1, p.2.2.2.2.2), ((p.2.2.2.1, p.2.2.2.2.1), p.2.2.1))
  invFun q := (q.1.1, q.1.2.1, (q.2.2, (q.2.1.1, q.2.1.2, q.1.2.2)))
  left_inv := by rintro ⟨idx, ans, ⟨β₁, ⟨i₂, a₂, w₂⟩⟩⟩; rfl
  right_inv := by rintro ⟨⟨idx, ans, w₂⟩, ⟨⟨i₂, a₂⟩, β₁⟩⟩; rfl

lemma oracleCompat_pairEquiv₁ :
    OracleCompat (pairEquiv₁ (ι := ι) (σ := σ) (W₁ := W₁) (W₂ := W₂)) := by
  rintro a ⟨(_ | i), ans, ⟨⟨i₁, a₁, w₁⟩, β₂⟩⟩ <;> rfl

lemma oracleCompat_pairEquiv₂ :
    OracleCompat (pairEquiv₂ (ι := ι) (σ := σ) (W₁ := W₁) (W₂ := W₂)) := by
  rintro a ⟨(_ | i), ans, ⟨β₁, ⟨i₂, a₂, w₂⟩⟩⟩ <;> rfl

/-- Swap the global query/answer registers with bank 1's parked pair. -/
def pairSwap₁Map : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂)
    → QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂)
  | (idx, ans, ((i₁, a₁, w₁), β₂)) => (i₁, a₁, ((idx, ans, w₁), β₂))

lemma pairSwap₁Map_involutive :
    Function.Involutive
      (pairSwap₁Map (ι := ι) (σ := σ) (W₁ := W₁) (W₂ := W₂)) := by
  rintro ⟨idx, ans, ⟨⟨i₁, a₁, w₁⟩, β₂⟩⟩
  rfl

/-- Swap the global query/answer registers with bank 2's parked pair. -/
def pairSwap₂Map : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂)
    → QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂)
  | (idx, ans, (β₁, (i₂, a₂, w₂))) => (i₂, a₂, (β₁, (idx, ans, w₂)))

lemma pairSwap₂Map_involutive :
    Function.Involutive
      (pairSwap₂Map (ι := ι) (σ := σ) (W₁ := W₁) (W₂ := W₂)) := by
  rintro ⟨idx, ans, ⟨β₁, ⟨i₂, a₂, w₂⟩⟩⟩
  rfl

/-- The swap-in unitary for bank 1. -/
def pairSwap₁Mat : Matrix (QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂))
    (QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂)) ℂ :=
  qPerm (Function.Involutive.toPerm _ pairSwap₁Map_involutive)

lemma pairSwap₁Mat_mem_unitaryGroup :
    pairSwap₁Mat (ι := ι) (σ := σ) (W₁ := W₁) (W₂ := W₂)
      ∈ Matrix.unitaryGroup _ ℂ :=
  qPerm_mem_unitaryGroup _

lemma pairSwap₁Mat_mulVec_apply
    (ψ : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂) → ℂ) (p) :
    (pairSwap₁Mat *ᵥ ψ) p = ψ (pairSwap₁Map p) := by
  rw [pairSwap₁Mat, qPerm_mulVec_apply]
  rfl

/-- The swap-in unitary for bank 2. -/
def pairSwap₂Mat : Matrix (QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂))
    (QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂)) ℂ :=
  qPerm (Function.Involutive.toPerm _ pairSwap₂Map_involutive)

lemma pairSwap₂Mat_mem_unitaryGroup :
    pairSwap₂Mat (ι := ι) (σ := σ) (W₁ := W₁) (W₂ := W₂)
      ∈ Matrix.unitaryGroup _ ℂ :=
  qPerm_mem_unitaryGroup _

lemma pairSwap₂Mat_mulVec_apply
    (ψ : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂) → ℂ) (p) :
    (pairSwap₂Mat *ᵥ ψ) p = ψ (pairSwap₂Map p) := by
  rw [pairSwap₂Mat, qPerm_mulVec_apply]
  rfl

/-! ## Product states -/

/-- The banked product state: `χ` on the global registers, `ψⱼ` in bank
`j`. -/
def prodState (χ : Option ι × Option σ → ℂ) (ψ₁ : QBasis ι σ W₁ → ℂ)
    (ψ₂ : QBasis ι σ W₂ → ℂ) :
    QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂) → ℂ :=
  fun p => χ (p.1, p.2.1) * ψ₁ p.2.2.1 * ψ₂ p.2.2.2

/-- Blank global registers. -/
def blankReg : Option ι × Option σ → ℂ :=
  fun q => if q = (none, none) then 1 else 0

lemma sum_normSq_blankReg :
    (∑ q : Option ι × Option σ, Complex.normSq (blankReg q)) = 1 := by
  rw [Finset.sum_eq_single ((none, none) : Option ι × Option σ)]
  · simp [blankReg]
  · intro q _ hq
    simp [blankReg, hq]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The double-sum factorization used twice below. -/
private lemma sum_sum_factor (C : ℝ) (F : QBasis ι σ W₁ → ℝ)
    (G : QBasis ι σ W₂ → ℝ) :
    (∑ β₁, ∑ β₂, C * (F β₁ * G β₂))
      = C * (∑ β₁, F β₁) * ∑ β₂, G β₂ := by
  have hinner : ∀ β₁, (∑ β₂, C * (F β₁ * G β₂))
      = (C * F β₁) * ∑ β₂, G β₂ := by
    intro β₁
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun β₂ _ => by ring
  rw [Finset.sum_congr rfl fun β₁ _ => hinner β₁, ← Finset.sum_mul,
    ← Finset.mul_sum]

lemma qNormSq_prodState (χ : Option ι × Option σ → ℂ)
    (ψ₁ : QBasis ι σ W₁ → ℂ) (ψ₂ : QBasis ι σ W₂ → ℂ) :
    qNormSq (prodState χ ψ₁ ψ₂)
      = (∑ q, Complex.normSq (χ q)) * qNormSq ψ₁ * qNormSq ψ₂ := by
  rw [qNormSq_def, qNormSq_def, qNormSq_def]
  rw [show (∑ p : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂),
        Complex.normSq (prodState χ ψ₁ ψ₂ p))
      = ∑ i : Option ι, ∑ a : Option σ, ∑ β₁ : QBasis ι σ W₁,
          ∑ β₂ : QBasis ι σ W₂,
          Complex.normSq (χ (i, a)) * (Complex.normSq (ψ₁ β₁)
            * Complex.normSq (ψ₂ β₂)) from by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun β₁ _ => Finset.sum_congr rfl fun β₂ _ => ?_
    rw [prodState, Complex.normSq_mul, Complex.normSq_mul]
    ring]
  rw [Fintype.sum_prod_type, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact sum_sum_factor _ _ _

lemma isQState_prodState {ψ₁ : QBasis ι σ W₁ → ℂ} {ψ₂ : QBasis ι σ W₂ → ℂ}
    (h₁ : IsQState ψ₁) (h₂ : IsQState ψ₂) :
    IsQState (prodState blankReg ψ₁ ψ₂) := by
  rw [IsQState, qNormSq_prodState, sum_normSq_blankReg, h₁, h₂]
  norm_num

/-! ## The phase actions -/

lemma pairSwap₁_mulVec_prodState (χ : Option ι × Option σ → ℂ)
    (ψ₁ : QBasis ι σ W₁ → ℂ) (ψ₂ : QBasis ι σ W₂ → ℂ) :
    pairSwap₁Mat *ᵥ prodState χ ψ₁ ψ₂
      = splitVec pairEquiv₁ ψ₁ (fun q => χ q.1 * ψ₂ q.2) := by
  funext p
  rw [pairSwap₁Mat_mulVec_apply]
  obtain ⟨idx, ans, ⟨⟨i₁, a₁, w₁⟩, β₂⟩⟩ := p
  show χ (i₁, a₁) * ψ₁ (idx, ans, w₁) * ψ₂ β₂
    = ψ₁ (idx, ans, w₁) * (χ (i₁, a₁) * ψ₂ β₂)
  ring

lemma pairSwap₁_mulVec_splitVec (χ : Option ι × Option σ → ℂ)
    (ψ₁ : QBasis ι σ W₁ → ℂ) (ψ₂ : QBasis ι σ W₂ → ℂ) :
    pairSwap₁Mat *ᵥ splitVec pairEquiv₁ ψ₁ (fun q => χ q.1 * ψ₂ q.2)
      = prodState χ ψ₁ ψ₂ := by
  funext p
  rw [pairSwap₁Mat_mulVec_apply]
  obtain ⟨idx, ans, ⟨⟨i₁, a₁, w₁⟩, β₂⟩⟩ := p
  show ψ₁ (i₁, a₁, w₁) * (χ (idx, ans) * ψ₂ β₂)
    = χ (idx, ans) * ψ₁ (i₁, a₁, w₁) * ψ₂ β₂
  ring

lemma pairSwap₂_mulVec_prodState (χ : Option ι × Option σ → ℂ)
    (ψ₁ : QBasis ι σ W₁ → ℂ) (ψ₂ : QBasis ι σ W₂ → ℂ) :
    pairSwap₂Mat *ᵥ prodState χ ψ₁ ψ₂
      = splitVec pairEquiv₂ ψ₂ (fun q => χ q.1 * ψ₁ q.2) := by
  funext p
  rw [pairSwap₂Mat_mulVec_apply]
  obtain ⟨idx, ans, ⟨β₁, ⟨i₂, a₂, w₂⟩⟩⟩ := p
  show χ (i₂, a₂) * ψ₁ β₁ * ψ₂ (idx, ans, w₂)
    = ψ₂ (idx, ans, w₂) * (χ (i₂, a₂) * ψ₁ β₁)
  ring

lemma pairSwap₂_mulVec_splitVec (χ : Option ι × Option σ → ℂ)
    (ψ₁ : QBasis ι σ W₁ → ℂ) (ψ₂ : QBasis ι σ W₂ → ℂ) :
    pairSwap₂Mat *ᵥ splitVec pairEquiv₂ ψ₂ (fun q => χ q.1 * ψ₁ q.2)
      = prodState χ ψ₁ ψ₂ := by
  funext p
  rw [pairSwap₂Mat_mulVec_apply]
  obtain ⟨idx, ans, ⟨β₁, ⟨i₂, a₂, w₂⟩⟩⟩ := p
  show ψ₂ (i₂, a₂, w₂) * (χ (idx, ans) * ψ₁ β₁)
    = χ (idx, ans) * ψ₁ β₁ * ψ₂ (i₂, a₂, w₂)
  ring

/-! ## The compiled routine -/

/-- **The pair compiler**: swap in bank 1, run schedule 1 lifted, swap out;
swap in bank 2, run schedule 2 lifted, swap out.  `R₁.len + R₂.len`
queries. -/
def pairRoutine (R₁ : QRoutine ι σ W₁) (R₂ : QRoutine ι σ W₂) :
    QRoutine ι σ (QBasis ι σ W₁ × QBasis ι σ W₂) :=
  (QRoutine.ofUnitary pairSwap₁Mat pairSwap₁Mat_mem_unitaryGroup).comp
    ((R₁.kronLift pairEquiv₁).comp
      ((QRoutine.ofUnitary pairSwap₁Mat pairSwap₁Mat_mem_unitaryGroup).comp
        ((QRoutine.ofUnitary pairSwap₂Mat pairSwap₂Mat_mem_unitaryGroup).comp
          ((R₂.kronLift pairEquiv₂).comp
            (QRoutine.ofUnitary pairSwap₂Mat
              pairSwap₂Mat_mem_unitaryGroup)))))

@[simp] lemma pairRoutine_len (R₁ : QRoutine ι σ W₁) (R₂ : QRoutine ι σ W₂) :
    (pairRoutine R₁ R₂).len = R₁.len + R₂.len := by
  show 0 + (R₁.len + (0 + (0 + (R₂.len + 0)))) = R₁.len + R₂.len
  omega

/-- **The compiled run is the product of the runs.** -/
theorem pairRoutine_run_prodState (R₁ : QRoutine ι σ W₁)
    (R₂ : QRoutine ι σ W₂) (a : ι → σ) (χ : Option ι × Option σ → ℂ)
    (ψ₁ : QBasis ι σ W₁ → ℂ) (ψ₂ : QBasis ι σ W₂ → ℂ) :
    (pairRoutine R₁ R₂).run a *ᵥ prodState χ ψ₁ ψ₂
      = prodState χ (R₁.run a *ᵥ ψ₁) (R₂.run a *ᵥ ψ₂) := by
  have hrun : (pairRoutine R₁ R₂).run a
      = pairSwap₂Mat * ((R₂.kronLift pairEquiv₂).run a * (pairSwap₂Mat
          * (pairSwap₁Mat * ((R₁.kronLift pairEquiv₁).run a
            * pairSwap₁Mat)))) := by
    rw [pairRoutine, QRoutine.comp_run, QRoutine.comp_run, QRoutine.comp_run,
      QRoutine.comp_run, QRoutine.comp_run, QRoutine.ofUnitary_run,
      QRoutine.ofUnitary_run]
    noncomm_ring
  rw [hrun, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    pairSwap₁_mulVec_prodState]
  rw [show (R₁.kronLift pairEquiv₁).run a
      = (R₁.kronLift pairEquiv₁).runUpto a R₁.len from rfl,
    QRoutine.kronLift_runUpto_splitVec oracleCompat_pairEquiv₁,
    show R₁.runUpto a R₁.len = R₁.run a from rfl,
    pairSwap₁_mulVec_splitVec, pairSwap₂_mulVec_prodState]
  rw [show (R₂.kronLift pairEquiv₂).run a
      = (R₂.kronLift pairEquiv₂).runUpto a R₂.len from rfl,
    QRoutine.kronLift_runUpto_splitVec oracleCompat_pairEquiv₂,
    show R₂.runUpto a R₂.len = R₂.run a from rfl,
    pairSwap₂_mulVec_splitVec]

/-! ## The joint measurement factorizes -/

variable {O₁ O₂ : Type} [DecidableEq O₁] [DecidableEq O₂]

/-- Read both banks. -/
def pairReadout (r₁ : QBasis ι σ W₁ → O₁) (r₂ : QBasis ι σ W₂ → O₂) :
    QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂) → O₁ × O₂ :=
  fun p => (r₁ p.2.2.1, r₂ p.2.2.2)

theorem qProb_pairReadout (r₁ : QBasis ι σ W₁ → O₁) (r₂ : QBasis ι σ W₂ → O₂)
    (χ : Option ι × Option σ → ℂ) (ψ₁ : QBasis ι σ W₁ → ℂ)
    (ψ₂ : QBasis ι σ W₂ → ℂ) (o₁ : O₁) (o₂ : O₂) :
    qProb (pairReadout r₁ r₂) (prodState χ ψ₁ ψ₂) (o₁, o₂)
      = (∑ q, Complex.normSq (χ q)) * qProb r₁ ψ₁ o₁ * qProb r₂ ψ₂ o₂ := by
  rw [qProb, qProb, qProb]
  rw [show (∑ p : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂),
        if pairReadout r₁ r₂ p = (o₁, o₂) then
          Complex.normSq (prodState χ ψ₁ ψ₂ p) else 0)
      = ∑ i : Option ι, ∑ a : Option σ, ∑ β₁ : QBasis ι σ W₁,
          ∑ β₂ : QBasis ι σ W₂,
          Complex.normSq (χ (i, a))
            * ((if r₁ β₁ = o₁ then Complex.normSq (ψ₁ β₁) else 0)
              * (if r₂ β₂ = o₂ then Complex.normSq (ψ₂ β₂) else 0)) from by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun β₁ _ => Finset.sum_congr rfl fun β₂ _ => ?_
    rw [show pairReadout r₁ r₂ ((i, a, (β₁, β₂))
        : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂)) = (r₁ β₁, r₂ β₂)
      from rfl]
    rw [show prodState χ ψ₁ ψ₂ ((i, a, (β₁, β₂))
        : QBasis ι σ (QBasis ι σ W₁ × QBasis ι σ W₂))
        = χ (i, a) * ψ₁ β₁ * ψ₂ β₂ from rfl]
    by_cases h1 : r₁ β₁ = o₁ <;> by_cases h2 : r₂ β₂ = o₂ <;>
      simp [h1, h2, Prod.ext_iff, Complex.normSq_mul] <;> ring]
  rw [Fintype.sum_prod_type, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact sum_sum_factor _ _ _

/-! ## `Realizes`, and the product-run calculus -/

section Realizes

variable {X : Type} [Fintype X] {O O' : Type} [DecidableEq O] [DecidableEq O']

/-- Some algorithm has outcome distribution `P` after `q` queries. -/
def Realizes (read : X → ι → σ) (q : ℕ) (P : X → O → ℝ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (A : QAlg ι σ O W),
    ∀ x o, A.prob (read x) q o = P x o

lemma Realizes.congr {read : X → ι → σ} {q : ℕ} {P Q : X → O → ℝ}
    (h : Realizes read q P) (hPQ : ∀ x o, P x o = Q x o) :
    Realizes read q Q := by
  obtain ⟨W, hW, hW', A, hA⟩ := h
  exact ⟨W, hW, hW', A, fun x o => (hA x o).trans (hPQ x o)⟩

/-- Every distribution an algorithm realizes is one the model measures:
values are probabilities of the final state. -/
lemma Realizes.nonneg {read : X → ι → σ} {q : ℕ} {P : X → O → ℝ}
    (h : Realizes read q P) (x : X) (o : O) : 0 ≤ P x o := by
  obtain ⟨W, hW, hW', A, hA⟩ := h
  rw [← hA x o]
  exact A.prob_nonneg _ _ _

/-- **The pair compiler, packaged**: two realizable distributions have a
jointly realizable product, at the sum of the costs. -/
theorem Realizes.pair {read : X → ι → σ} {q₁ q₂ : ℕ} {P₁ : X → O → ℝ}
    {P₂ : X → O' → ℝ} (h₁ : Realizes read q₁ P₁) (h₂ : Realizes read q₂ P₂) :
    Realizes read (q₁ + q₂)
      (fun x o => P₁ x o.1 * P₂ x o.2 : X → O × O' → ℝ) := by
  classical
  obtain ⟨V₁, _, _, A₁, hA₁⟩ := h₁
  obtain ⟨V₂, _, _, A₂, hA₂⟩ := h₂
  refine ⟨QBasis ι σ V₁ × QBasis ι σ V₂, inferInstance, inferInstance,
    (pairRoutine (QRoutine.mk q₁ A₁.step A₁.step_unitary)
        (QRoutine.mk q₂ A₂.step A₂.step_unitary)).toAlg
      (prodState blankReg A₁.init A₂.init)
      (isQState_prodState A₁.init_isQState A₂.init_isQState)
      (pairReadout A₁.readout A₂.readout), ?_⟩
  intro x o
  obtain ⟨o₁, o₂⟩ := o
  have hlen : (pairRoutine (QRoutine.mk q₁ A₁.step A₁.step_unitary)
      (QRoutine.mk q₂ A₂.step A₂.step_unitary)).len = q₁ + q₂ := by
    rw [pairRoutine_len]
  have hstate : ((pairRoutine (QRoutine.mk q₁ A₁.step A₁.step_unitary)
        (QRoutine.mk q₂ A₂.step A₂.step_unitary)).toAlg
      (prodState blankReg A₁.init A₂.init)
      (isQState_prodState A₁.init_isQState A₂.init_isQState)
      (pairReadout A₁.readout A₂.readout)).state (read x) (q₁ + q₂)
      = prodState blankReg (A₁.state (read x) q₁) (A₂.state (read x) q₂) := by
    rw [← hlen, QRoutine.toAlg_state_len, pairRoutine_run_prodState]
    rw [show (QRoutine.mk q₁ A₁.step A₁.step_unitary).run (read x)
        = (QRoutine.mk q₁ A₁.step A₁.step_unitary).runUpto (read x) q₁
      from rfl, ← state_eq_runUpto2 A₁ q₁]
    rw [show (QRoutine.mk q₂ A₂.step A₂.step_unitary).run (read x)
        = (QRoutine.mk q₂ A₂.step A₂.step_unitary).runUpto (read x) q₂
      from rfl, ← state_eq_runUpto2 A₂ q₂]
  rw [QAlg.prob, hstate]
  rw [show ((pairRoutine (QRoutine.mk q₁ A₁.step A₁.step_unitary)
        (QRoutine.mk q₂ A₂.step A₂.step_unitary)).toAlg
      (prodState blankReg A₁.init A₂.init)
      (isQState_prodState A₁.init_isQState A₂.init_isQState)
      (pairReadout A₁.readout A₂.readout)).readout
      = pairReadout A₁.readout A₂.readout from rfl]
  rw [qProb_pairReadout, sum_normSq_blankReg, one_mul]
  rw [show qProb A₁.readout (A₁.state (read x) q₁) o₁
      = A₁.prob (read x) q₁ o₁ from rfl,
    show qProb A₂.readout (A₂.state (read x) q₂) o₂
      = A₂.prob (read x) q₂ o₂ from rfl, hA₁, hA₂]

/-- Reshaping the outcome through the readout is free. -/
theorem Realizes.map [Fintype O] {read : X → ι → σ} {q : ℕ} {P : X → O → ℝ}
    (h : Realizes read q P) (g : O → O') :
    Realizes read q (fun x o' =>
      ∑ o ∈ Finset.univ.filter (fun o => g o = o'), P x o) := by
  obtain ⟨W, hW, hW', A, hA⟩ := h
  refine ⟨W, hW, hW',
    (QRoutine.mk q A.step A.step_unitary).toAlg A.init A.init_isQState
      (fun p => g (A.readout p)), ?_⟩
  intro x o
  rw [QAlg.prob,
    show ((QRoutine.mk q A.step A.step_unitary).toAlg A.init A.init_isQState
        (fun p => g (A.readout p))).readout
      = fun p => g (A.readout p) from rfl,
    show ((QRoutine.mk q A.step A.step_unitary).toAlg A.init A.init_isQState
        (fun p => g (A.readout p))).state (read x) q
      = (QRoutine.mk q A.step A.step_unitary).runUpto (read x) q *ᵥ A.init
      from QRoutine.toAlg_state _ _ _ _ _ q,
    ← state_eq_runUpto2 A q]
  rw [qProb]
  rw [show (∑ h, if g (A.readout h) = o then
        Complex.normSq (A.state (read x) q h) else 0)
      = ∑ h, ∑ b ∈ Finset.univ.filter (fun b => g b = o),
          if A.readout h = b then
            Complex.normSq (A.state (read x) q h) else 0 from by
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_filter]
    rw [Finset.sum_eq_single (A.readout h)]
    · by_cases hg : g (A.readout h) = o <;> simp [hg]
    · intro b _ hb
      by_cases hg : g b = o <;> simp [hg, Ne.symm hb]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← hA x b, QAlg.prob, qProb]

/-- The bijective special case: relabel the outcomes. -/
theorem Realizes.map_equiv [Fintype O] {read : X → ι → σ} {q : ℕ}
    {P : X → O → ℝ} (h : Realizes read q P) (g : O ≃ O') :
    Realizes read q (fun x o' => P x (g.symm o')) := by
  refine (h.map g).congr fun x o' => ?_
  have hset : Finset.univ.filter (fun o => g o = o') = {g.symm o'} := by
    ext o
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hgo
      rw [← hgo, Equiv.symm_apply_apply]
    · rintro rfl
      exact g.apply_symm_apply o'
  rw [hset, Finset.sum_singleton]

end Realizes

end QuantumQueryComplexity
