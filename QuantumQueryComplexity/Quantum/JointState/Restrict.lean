import QuantumQueryComplexity.Quantum.JointState.Success
import QuantumQueryComplexity.Quantum.Postcomp

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Restricting the index set, with padding by known zeros

Let `φ : ι → Option κ` assign to some of the indices `i` of an algorithm a coordinate `φ i` of
another index set `κ`.  An input `a : κ → Bool` induces the padded input `padRead φ a : ι → Bool`,
which reads `a (φ i)` when `φ i = some k` and the known value `false` when `φ i = none`.  No
injectivity is required.

An XOR-model algorithm `A` on `ι` is simulated by an XOR-model algorithm `A.restrictIdx φ` on `κ`
with **the same number of queries**: on input `a` the simulation behaves as `A` does on
`padRead φ a` (`xorSuccessProbOn_restrictIdx`).

**Construction.**
* The simulation's workspace is `A`'s whole basis `QBasis ι Bool W`, and its own index and answer
  registers start idle and blank.
* Around every query, the simulation applies an involutive basis permutation, controlled on
  `A`'s index register `i`.  It exchanges the simulation's blank index with `φ i`, and it swaps
  the simulation's answer register with `A`'s.  An index with `φ i = none` stays idle, so the
  query is the identity, which is XOR with the known value `false`.
* The readout reads `A`'s answer from the simulation's answer register.

This is the coherent restriction behind lower bounds for problems in which some input bits are
known in advance, such as the pairs that are not edges of a host graph.

`xorSuccessProbOn_postcomp` records that relabelling the readout (`QAlg.postcomp`) changes only
the success relation.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι κ O O' W X : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype W] [DecidableEq W] [Fintype X]

/-- **The padded input**: `a (φ i)` where `φ i = some k`, and the known value `false` where
`φ i = none`. -/
def padRead (φ : ι → Option κ) (a : κ → Bool) : ι → Bool := fun i =>
  match φ i with
  | some k => a k
  | none => false

/-! ## The construction -/

section Lift

variable {R : Type} [Fintype R] [DecidableEq R]

/-- The simulation's basis, split as (workspace, simulation registers). -/
private def wEquiv : QBasis κ Bool R ≃ R × (Option κ × Option Bool) where
  toFun p := (p.2.2, (p.1, p.2.1))
  invFun x := (x.2.1, x.2.2, x.1)
  left_inv := by rintro ⟨k, c, r⟩; rfl
  right_inv := by rintro ⟨r, k, c⟩; rfl

/-- An operator on the workspace, acting as the identity on the simulation's registers. -/
private noncomputable def wLift (M : Matrix R R ℂ) :
    Matrix (QBasis κ Bool R) (QBasis κ Bool R) ℂ :=
  (Matrix.blockDiagonal fun _ : Option κ × Option Bool => M).submatrix wEquiv wEquiv

private lemma wLift_mem_unitaryGroup {M : Matrix R R ℂ} (hM : M ∈ Matrix.unitaryGroup R ℂ) :
    wLift (κ := κ) M ∈ Matrix.unitaryGroup (QBasis κ Bool R) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, wLift,
    Matrix.conjTranspose_submatrix, Matrix.blockDiagonal_conjTranspose,
    Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]
  rw [show (fun _ : Option κ × Option Bool => Mᴴ * M)
    = (1 : Option κ × Option Bool → Matrix R R ℂ) from
      funext fun _ => conjTranspose_mul_self_of_unitary hM,
    Matrix.blockDiagonal_one, Matrix.submatrix_one_equiv]

private lemma wLift_mulVec_apply (M : Matrix R R ℂ) (v : QBasis κ Bool R → ℂ)
    (p : QBasis κ Bool R) :
    (wLift M *ᵥ v) p = (M *ᵥ fun r => v (p.1, p.2.1, r)) p.2.2 := by
  obtain ⟨k, c, r⟩ := p
  simp only [Matrix.mulVec, dotProduct, wLift, Matrix.submatrix_apply]
  rw [← Equiv.sum_comp wEquiv.symm, Fintype.sum_prod_type]
  simp [Matrix.blockDiagonal_apply, wEquiv]

/-- A workspace state, with the simulation's index and answer registers idle and blank. -/
private def rEmbed (ψ : R → ℂ) : QBasis κ Bool R → ℂ :=
  fun p => if p.1 = none ∧ p.2.1 = none then ψ p.2.2 else 0

private lemma wLift_mulVec_rEmbed (M : Matrix R R ℂ) (ψ : R → ℂ) :
    wLift (κ := κ) M *ᵥ rEmbed ψ = rEmbed (M *ᵥ ψ) := by
  funext p
  rw [wLift_mulVec_apply]
  by_cases h : p.1 = none ∧ p.2.1 = none
  · have hψ : (fun r => rEmbed (κ := κ) ψ (p.1, p.2.1, r)) = ψ :=
      funext fun r => by simp [rEmbed, h]
    rw [hψ]
    simp [rEmbed, h]
  · have hψ : (fun r => rEmbed (κ := κ) ψ (p.1, p.2.1, r)) = 0 :=
      funext fun r => by simp only [rEmbed, h, ↓reduceIte, Pi.zero_apply]
    rw [hψ, Matrix.mulVec_zero]
    simp only [rEmbed, h, ↓reduceIte, Pi.zero_apply]

/-- Sums over the embedded sector. -/
private lemma sum_rEmbed_sector (f : R → ℝ) :
    ∑ p : QBasis κ Bool R, (if p.1 = none ∧ p.2.1 = none then f p.2.2 else 0) = ∑ r, f r := by
  simp [Fintype.sum_prod_type, ite_and]

private lemma isQState_rEmbed {ψ : R → ℂ} (hψ : IsQState ψ) :
    IsQState (rEmbed (κ := κ) ψ) := by
  rw [IsQState] at hψ ⊢
  rw [← hψ, qNormSq_def, qNormSq_def,
    ← sum_rEmbed_sector (κ := κ) (fun r => Complex.normSq (ψ r))]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : p.1 = none ∧ p.2.1 = none <;> simp [rEmbed, h]

end Lift

section Perm

variable (φ : ι → Option κ)

/-- The simulation's index matching `A`'s index register: `φ i`, idle for an idle `i`. -/
private def liftIdx (i : Option ι) : Option κ := i.bind φ

/-- **The basis permutation around each query**, controlled on `A`'s index `i`: exchange the
simulation's index between blank and `φ i`, and swap the two answer registers. -/
private def rMap (p : QBasis κ Bool (QBasis ι Bool W)) : QBasis κ Bool (QBasis ι Bool W) :=
  (Equiv.swap none (liftIdx φ p.2.2.1) p.1, p.2.2.2.1, (p.2.2.1, p.2.1, p.2.2.2.2))

private lemma rMap_involutive : Function.Involutive (rMap (W := W) φ) := by
  rintro ⟨k, c, i, b, w⟩
  simp [rMap]

private def rPerm : Equiv.Perm (QBasis κ Bool (QBasis ι Bool W)) :=
  Function.Involutive.toPerm _ (rMap_involutive (W := W) φ)

private lemma rPerm_mulVec_apply (ψ : QBasis κ Bool (QBasis ι Bool W) → ℂ)
    (p : QBasis κ Bool (QBasis ι Bool W)) :
    (qPerm (rPerm φ) *ᵥ ψ) p = ψ (rMap φ p) := by
  rw [qPerm_mulVec_apply]
  rfl

private lemma xorOracleMap_fst {ι' : Type} [Fintype ι'] [DecidableEq ι'] {W' : Type}
    [Fintype W'] [DecidableEq W'] (a : ι' → Bool) (q : QBasis ι' Bool W') :
    (xorOracleMap a q).1 = q.1 ∧ (xorOracleMap a q).2.2 = q.2.2 := by
  rcases q with ⟨_ | j, t, r⟩ <;> exact ⟨rfl, rfl⟩

private lemma optXor_some_false (t : Option Bool) : optXor t (some false) = t := by
  cases t <;> simp

/-- **One simulated query**: the permutation, the `κ`-oracle on `a`, and the permutation again
act on the embedded sector as the `ι`-oracle on the padded input. -/
private lemma rPerm_xor_rPerm (a : κ → Bool) (ψ : QBasis ι Bool W → ℂ) :
    qPerm (rPerm φ) *ᵥ (xorOracleMat a *ᵥ (qPerm (rPerm φ) *ᵥ rEmbed ψ))
      = rEmbed (xorOracleMat (padRead φ a) *ᵥ ψ) := by
  funext p
  rw [rPerm_mulVec_apply, xorOracleMat_mulVec_apply, rPerm_mulVec_apply]
  obtain ⟨k, c, i, b, w⟩ := p
  by_cases h : k = none ∧ c = none
  · obtain ⟨rfl, rfl⟩ := h
    rcases i with _ | i
    · simp [rMap, rEmbed, liftIdx, xorOracleMat_mulVec_apply]
    · rcases hφ : φ i with _ | j
      · simp [rMap, rEmbed, liftIdx, hφ, padRead, xorOracleMat_mulVec_apply,
          optXor_some_false]
      · simp [rMap, rEmbed, liftIdx, hφ, padRead, xorOracleMat_mulVec_apply]
  · obtain ⟨h1, h2⟩ := xorOracleMap_fst a (rMap φ ((k, c, i, b, w) : QBasis κ Bool _))
    generalize xorOracleMap a (rMap φ ((k, c, i, b, w) : QBasis κ Bool _)) = q at h1 h2
    have hk : (rMap φ q).1 = k := by
      simp [rMap, h1, h2]
    have hc : (rMap φ q).2.1 = c := by
      simp [rMap, h2]
    simp only [rEmbed, hk, hc, h, ↓reduceIte]

end Perm

/-- The steps of the simulation: `A`'s step on the workspace, conjugated by the permutation
around each query. -/
private noncomputable def rStep (A : QAlg ι Bool O W) (φ : ι → Option κ) :
    ℕ → Matrix (QBasis κ Bool (QBasis ι Bool W)) (QBasis κ Bool (QBasis ι Bool W)) ℂ
  | 0 => qPerm (rPerm φ) * wLift (A.step 0)
  | s + 1 => qPerm (rPerm φ) * wLift (A.step (s + 1)) * qPerm (rPerm φ)

private lemma rStep_mem_unitaryGroup (A : QAlg ι Bool O W) (φ : ι → Option κ) (s : ℕ) :
    rStep A φ s ∈ Matrix.unitaryGroup (QBasis κ Bool (QBasis ι Bool W)) ℂ := by
  cases s with
  | zero =>
      exact (Matrix.unitaryGroup _ ℂ).mul_mem (qPerm_mem_unitaryGroup _)
        (wLift_mem_unitaryGroup (A.step_unitary 0))
  | succ s =>
      exact (Matrix.unitaryGroup _ ℂ).mul_mem ((Matrix.unitaryGroup _ ℂ).mul_mem
        (qPerm_mem_unitaryGroup _) (wLift_mem_unitaryGroup (A.step_unitary (s + 1))))
        (qPerm_mem_unitaryGroup _)

/-- **The restricted simulation** of an XOR-model algorithm on `ι` by one on `κ`, through
`φ : ι → Option κ`.  It makes the same number of queries.  Its workspace holds `A`'s whole basis.
-/
noncomputable def QAlg.restrictIdx (A : QAlg ι Bool O W) (φ : ι → Option κ) :
    QAlg κ Bool O (QBasis ι Bool W) where
  init := rEmbed A.init
  init_isQState := isQState_rEmbed A.init_isQState
  step := rStep A φ
  step_unitary := rStep_mem_unitaryGroup A φ
  readout p := A.readout (p.2.2.1, p.2.1, p.2.2.2.2)

/-- The simulation's state is `A`'s state on the padded input, embedded and permuted. -/
private lemma xorState_restrictIdx (A : QAlg ι Bool O W) (φ : ι → Option κ) (a : κ → Bool)
    (t : ℕ) :
    xorState (A.restrictIdx φ) a t
      = qPerm (rPerm φ) *ᵥ rEmbed (xorState A (padRead φ a) t) := by
  classical
  induction t with
  | zero =>
      rw [xorState_zero, xorState_zero]
      change (qPerm (rPerm φ) * wLift (A.step 0)) *ᵥ rEmbed A.init = _
      rw [← Matrix.mulVec_mulVec, wLift_mulVec_rEmbed]
  | succ t ih =>
      rw [xorState_succ, xorState_succ, ih]
      change (qPerm (rPerm φ) * wLift (A.step (t + 1)) * qPerm (rPerm φ)) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, rPerm_xor_rPerm, wLift_mulVec_rEmbed]

/-- The simulation's readout sees `A`'s readout on the embedded, permuted state. -/
private lemma goodProb_restrictIdx (A : QAlg ι Bool O W) (φ : ι → Option κ) (G : O → Prop)
    [DecidablePred G] (ψ : QBasis ι Bool W → ℂ) :
    goodProb (A.restrictIdx φ).readout G (qPerm (rPerm φ) *ᵥ rEmbed ψ)
      = goodProb A.readout G ψ := by
  rw [goodProb_eq_sum_ite, goodProb_eq_sum_ite]
  conv_lhs => rw [← Equiv.sum_comp (rPerm φ)]
  conv_rhs => rw [← sum_rEmbed_sector (κ := κ)
    (fun r => if G (A.readout r) then Complex.normSq (ψ r) else 0)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [rPerm_mulVec_apply, show rPerm φ p = rMap φ p from rfl, rMap_involutive φ p]
  obtain ⟨k, c, i, b, w⟩ := p
  rw [show (A.restrictIdx φ).readout (rMap φ (k, c, i, b, w)) = A.readout (i, b, w) from rfl]
  by_cases h : k = none ∧ c = none <;> by_cases hG : G (A.readout (i, b, w)) <;>
    simp [rEmbed, h, hG]

/-- **The restriction is exact**: after `t` XOR queries on input `read x`, the simulation succeeds
with exactly the probability that `A` succeeds after `t` XOR queries on the padded input
`padRead φ (read x)`, for every relation `Good`. -/
theorem xorSuccessProbOn_restrictIdx (A : QAlg ι Bool O W) (φ : ι → Option κ)
    (t : ℕ) (read : X → κ → Bool) (Good : X → O → Prop) [∀ x, DecidablePred (Good x)] (x : X) :
    xorSuccessProbOn (A.restrictIdx φ) t read Good x
      = xorSuccessProbOn A t (fun x => padRead φ (read x)) Good x := by
  rw [xorSuccessProbOn, xorSuccessProbOn, xorState_restrictIdx, goodProb_restrictIdx]

/-- Relabelling the readout leaves the XOR state unchanged. -/
private lemma xorState_postcomp (A : QAlg ι Bool O W) (g : O → O') (a : ι → Bool) (t : ℕ) :
    xorState (A.postcomp g) a t = xorState A a t := by
  classical
  induction t with
  | zero => rfl
  | succ t ih => rw [xorState_succ, xorState_succ, ih, QAlg.postcomp_step]

/-- Relabelling the readout changes only the success relation. -/
theorem xorSuccessProbOn_postcomp (A : QAlg ι Bool O W) (g : O → O') (t : ℕ)
    (read : X → ι → Bool) (Good : X → O' → Prop) [∀ x, DecidablePred (Good x)] (x : X) :
    xorSuccessProbOn (A.postcomp g) t read Good x
      = xorSuccessProbOn A t read (fun x o => Good x (g o)) x := by
  rw [xorSuccessProbOn, xorSuccessProbOn, xorState_postcomp]
  rfl

/-! ## Restriction for complexities -/

/-- **Restriction monotonicity of the XOR query complexity.** If every input `y` of `g` is
mapped, by reading `read' y` through `φ` with known zeros, to an input `x` of `f` with the same
answer, then `g` is no harder than `f`. The nonemptiness hypothesis excludes the junk value
`sInf ∅ = 0`. -/
theorem xorQQueryOn_le_of_padRead {Y : Type} [Fintype Y] [DecidableEq O] {read : X → ι → Bool}
    {f : X → O} {read' : Y → κ → Bool} {g : Y → O} {ε : ℝ} (φ : ι → Option κ)
    (hne : (XorQueryCounts read f ε).Nonempty)
    (hmap : ∀ y, ∃ x, read x = padRead φ (read' y) ∧ f x = g y) :
    xorQQueryOn read' g ε ≤ xorQQueryOn read f ε := by
  classical
  obtain ⟨V, _, _, A, hA⟩ := Nat.sInf_mem hne
  refine Nat.sInf_le (mem_xorQueryCounts (A := A.restrictIdx φ) fun y => ?_)
  obtain ⟨x, hx, hfx⟩ := hmap y
  have h := xorSuccessProbOn_restrictIdx A φ (xorQQueryOn read f ε) read'
    (fun y o => o = g y) y
  rw [xorSuccessProbOn, xorSuccessProbOn, goodProb_eq, goodProb_eq, ← hx] at h
  rw [h, ← hfx]
  exact hA x

end QuantumQueryComplexity
