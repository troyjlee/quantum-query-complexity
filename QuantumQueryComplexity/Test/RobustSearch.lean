import QuantumQueryComplexity.Quantum.RobustSearch.Public

set_option synthInstance.maxSize 3200
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Acceptance: robust search

1. **Coherent selection**: one invocation costs the common length; the operator equation; the
   state equation on a *superposition* of sectors (false for a classical mixture of the
   selected routines, which has no such unitary); the padded adapter for algorithms with
   different workspaces, budgets, initial states and readouts; selection controlled by a
   spectator register entangled with anything.
2. **Named repetition and majority**: cost `k·len`, the final state keeps every bank
   (garbage preserved), the exact product law, the `12·n` bound from error `1/3`.
3. **The recursion**: exact query recurrence `3q + q_filter`, the closed form, the exact state
   recurrence `u' = (3−4p)²·u·τ`.
4. **The public theorem**, from the caller's bounded-error algorithms alone: no exact verifier,
   no adversary certificate, arbitrary `read` (overlapping accesses, noninjective promise
   maps), dependent workspaces.  Budget `≤ 10206·T·⌈√m⌉`; `m = 0`, `m = 1`, `T = 0`, and the
   scale cutoff at exact powers of nine.
5. **A noisy input-dependent tester**: query bit `i`, XOR a fresh `1/4`-biased noise bit.  It
   errs with probability exactly `1/4` on both sides — in particular it has false positives
   on a false input — and robust search over these testers finds a `1` among `m` bits.
-/

namespace QuantumQueryComplexity
namespace RobustSearchAcceptance

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

/-! ## 1. Coherent selection -/

section Select

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {W : Ω → Type} [∀ ω, Fintype (W ω)]
  [∀ ω, DecidableEq (W ω)]

/-- One invocation of all selected routines in superposition costs `L`, not `∑ len`. -/
example (L : ℕ) (R : ∀ ω, QRoutine ι σ (W ω)) : (QRoutine.sig L R).len = L := rfl

theorem acceptance_select {L : ℕ} {R : ∀ ω, QRoutine ι σ (W ω)} (hL : ∀ ω, (R ω).len = L)
    (a : ι → σ) (φ : ∀ ω, QBasis ι σ (W ω) → ℂ) :
    (QRoutine.sig L R).run a = sigFam (fun ω => (R ω).run a)
    ∧ (QRoutine.sig L R).run a *ᵥ (∑ ω, embedSig ω (φ ω))
        = ∑ ω, embedSig ω ((R ω).run a *ᵥ φ ω) :=
  ⟨QRoutine.sig_run hL a, QRoutine.sig_run_mulVec_sum hL a φ⟩

/-- Different workspaces, budgets, initial states and readouts; cost `T`. -/
theorem acceptance_select_padded {O : Type} [DecidableEq O] (A : ∀ ω, QAlg ι σ O (W ω))
    (q : Ω → ℕ) (T : ℕ) (hq : ∀ ω, q ω ≤ T) (a : ι → σ) (ω : Ω) (o : O) :
    (selectPadded A q T).len = T
    ∧ (selectPadded A q T).run a *ᵥ selectInit A ω
        = embedSig ω (embedCtrl false ((A ω).state a (q ω)))
    ∧ qProb (selectReadout A) ((selectPadded A q T).run a *ᵥ selectInit A ω) o
        = (A ω).prob a (q ω) o :=
  ⟨rfl, selectPadded_run hq a ω, selectPadded_prob hq a ω o⟩

/-- Selection controlled by a spectator bank, for an arbitrary spectator vector. -/
theorem acceptance_bankCtrl {W₁ W₂ I : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂]
    [DecidableEq W₂] [Fintype I] [DecidableEq I] (c : QBasis ι σ W₁ → I)
    (U : I → Matrix (QBasis ι σ W₂) (QBasis ι σ W₂) ℂ) (χ : Option ι × Option σ → ℂ)
    (φ : QBasis ι σ W₁ → ℂ) (ξ : QBasis ι σ W₂ → ℂ) :
    bankCtrl c U *ᵥ prodState χ φ ξ = ∑ i, prodState χ (qRestrict c i φ) (U i *ᵥ ξ) :=
  bankCtrl_mulVec_prodState c U χ φ ξ

end Select

/-! ## 2. Named repetition and majority -/

section Majority

variable {V : Type} [Fintype V] [DecidableEq V]

theorem acceptance_pow (R : QRoutine ι σ V) (a : ι → σ) (η : QBasis ι σ V → ℂ) (k : ℕ)
    (rd : QBasis ι σ V → Bool) (y : Fin k → Bool) :
    (powRoutine R k).len = k * R.len
    ∧ (powRoutine R k).run a *ᵥ powInit η k = powInit (R.run a *ᵥ η) k
    ∧ qProb (powReadout rd k) (powInit (R.run a *ᵥ η) k) y
        = ∏ j, qProb rd (R.run a *ᵥ η) (y j) :=
  ⟨powRoutine_len R k, powRoutine_run R a η k, qProb_powReadout rd k y⟩

theorem acceptance_majority (rd : QBasis ι σ V → Bool) {ψ : QBasis ι σ V → ℂ}
    (hψ : IsQState ψ) (b : Bool) (hε : qProb rd ψ (!b) ≤ 1 / 3) (n : ℕ) :
    qProb (majReadout rd (12 * n)) (powInit ψ (12 * n)) (!b) ≤ (1 / 2) ^ n :=
  maj_twelve_le rd hψ b hε n

end Majority

/-! ## 3. The recursion -/

section Recursion

variable {I : Type} [Fintype I] [DecidableEq I]

theorem acceptance_step (L : RSLevel ι σ I) (K : TestBank ι σ I) (i₀ : I) (a : ι → σ) (i : I) :
    (L.next K i₀).A.len = 3 * L.A.len + K.F.len
    ∧ (L.next K i₀).u a i = (3 - 4 * L.p a) ^ 2 * L.u a i * K.accProb a i
    ∧ L.p a = ∑ j, L.u a j :=
  ⟨L.next_len K i₀, L.next_u K i₀ a i, L.p_eq_sum a⟩

example (T n : ℕ) : levelLen T (n + 1) = 3 * levelLen T n + 12 * (n + 10) * T := rfl

example (T n : ℕ) : levelLen T n + T * (6 * n + 63) = 63 * T * 3 ^ n := levelLen_closed T n

end Recursion

/-! ## 4. The public theorem -/

section Public

variable {X : Type} [Fintype X] {m : ℕ} {W : Fin m → Type} [∀ i, Fintype (W i)]
  [∀ i, DecidableEq (W i)]

theorem acceptance_robustSearch (A : ∀ i, QAlg ι σ Bool (W i)) (q : Fin m → ℕ) (T : ℕ)
    (hq : ∀ i, q i ≤ T) (read : X → ι → σ) (b : X → Fin m → Bool)
    (hA : ∀ x i, 2 / 3 ≤ (A i).prob (read x) (q i) (b x i)) :
    (robustSearch A q T).q = robustSearchBudget m T
    ∧ robustSearchBudget m T ≤ 10206 * T * ⌈Real.sqrt m⌉₊
    ∧ SolvesWithErrorOn (robustSearch A q T).alg (robustSearchBudget m T) read (SearchOK b)
        (1 / 3)
    ∧ ComputesWithErrorOn (robustOr A q T) (robustSearchBudget m T) read
        (fun x => decide (∃ i, b x i = true)) (1 / 3) :=
  ⟨robustSearch_q A q T, robustSearchBudget_le m T, robustSearch_solves hq hA,
    robustOr_computes hq hA⟩

/-- The relation: a marked index, or `none` exactly when nothing is marked. -/
example (b : X → Fin m → Bool) (x : X) (i : Fin m) :
    (SearchOK b x (some i) ↔ b x i = true) ∧ (SearchOK b x none ↔ ∀ i, b x i = false) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- `m = 0`: no queries. -/
example (T : ℕ) : robustSearchBudget 0 T = 0 := rfl

lemma levelLen_zero (n : ℕ) : levelLen 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [levelLen, ih]; simp

/-- `T = 0`: no queries. -/
example (m : ℕ) : robustSearchBudget m 0 = 0 := by
  have h : ∀ k, trialsLen 0 k = 0 := fun k => by
    induction k with
    | zero => rfl
    | succ k ih => rw [trialsLen, ih, levelLen_zero]
  rw [robustSearchBudget]
  split_ifs <;> [exact h _; rfl]

/-- Scale cutoffs: `m = 1`, an exact power of nine, and just above it. -/
example : Nat.clog 9 1 = 0 ∧ Nat.clog 9 9 = 1 ∧ Nat.clog 9 10 = 2 ∧ Nat.clog 9 81 = 2 := by
  refine ⟨by simp, ?_, ?_, ?_⟩ <;> decide

/-- `m = 1`: twelve copies of the single scale, `12·120·T` queries. -/
example (T : ℕ) : robustSearchBudget 1 T = 1440 * T := by
  rw [robustSearchBudget, if_pos (by norm_num), Nat.clog_one_right]
  simp only [trialsLen, levelLen]
  ring

end Public

/-! ## 5. A noisy input-dependent tester -/

namespace Noisy

variable {n : ℕ}

/-- Index register on `i`, answer register blank, noise bit `1` with probability `1/4`. -/
noncomputable def noisyInit (i : Fin n) : QBasis (Fin n) Bool Bool → ℂ := fun p =>
  if p.1 = some i ∧ p.2.1 = none then (if p.2.2 then 2⁻¹ else ((Real.sqrt 3 / 2 : ℝ) : ℂ)) else 0

lemma sum_noisyInit (i : Fin n) (g : QBasis (Fin n) Bool Bool → ℝ) :
    ∑ p, g p * Complex.normSq (noisyInit i p)
      = 3 / 4 * g (some i, none, false) + 1 / 4 * g (some i, none, true) := by
  have h2 : Complex.normSq (2⁻¹ : ℂ) = 1 / 4 := by
    rw [Complex.normSq_inv]; norm_num [Complex.normSq_ofNat]
  have h3 : Complex.normSq ((Real.sqrt 3 / 2 : ℝ) : ℂ) = 3 / 4 := by
    rw [Complex.normSq_ofReal]
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    nlinarith
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (some i)]
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single none]
    · rw [Fintype.sum_bool]
      simp only [noisyInit, and_self, if_true, h2, h3, Bool.false_eq_true, if_false]
      ring
    · intro t _ ht
      exact Finset.sum_eq_zero fun w _ => by simp [noisyInit, ht]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro k _ hk
    exact Finset.sum_eq_zero fun y _ => by simp [noisyInit, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma isQState_noisyInit (i : Fin n) : IsQState (noisyInit i) := by
  have h := sum_noisyInit i fun _ => 1
  simp only [one_mul] at h
  rw [IsQState, qNormSq_def, h]
  norm_num

/-- **The noisy tester of bit `i`**: one query; output `answer XOR noise`. -/
noncomputable def noisyTest (i : Fin n) : QAlg (Fin n) Bool Bool Bool where
  init := noisyInit i
  init_isQState := isQState_noisyInit i
  step := fun _ => 1
  step_unitary := fun _ => one_mem_qUnitary
  readout := fun p => xor (p.2.1 == some true) p.2.2

/-- **Its outcome law**: the input bit with probability `3/4`, the wrong bit with `1/4`. -/
theorem noisyTest_prob (a : Fin n → Bool) (i : Fin n) (o : Bool) :
    (noisyTest i).prob a 1 o = if o = a i then 3 / 4 else 1 / 4 := by
  have hstate : (noisyTest i).state a 1 = oracleMat a *ᵥ noisyInit i := by
    rw [QAlg.state_succ, QAlg.state_zero]
    change (1 : Matrix _ _ ℂ) *ᵥ (oracleMat a *ᵥ ((1 : Matrix _ _ ℂ) *ᵥ noisyInit i)) = _
    rw [Matrix.one_mulVec, Matrix.one_mulVec]
  rw [QAlg.prob, hstate, qProb]
  have hre : (∑ p, if (noisyTest i).readout p = o
        then Complex.normSq ((oracleMat a *ᵥ noisyInit i) p) else 0)
      = ∑ p, (if (noisyTest i).readout (oracleMap a p) = o then (1 : ℝ) else 0)
          * Complex.normSq (noisyInit i p) := by
    rw [← Equiv.sum_comp (Function.Involutive.toPerm _ (oracleMap_involutive a))]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Function.Involutive.coe_toPerm, oracleMat_mulVec_apply,
      (oracleMap_involutive a) p]
    split_ifs <;> simp
  rw [hre, sum_noisyInit]
  cases ha : a i <;> cases o <;> simp [noisyTest, oracleMap, ha]

/-- It errs with probability `1/4` on both sides: **false positives on a false input**. -/
example (a : Fin n → Bool) (i : Fin n) (h : a i = false) : (noisyTest i).prob a 1 true = 1 / 4 := by
  rw [noisyTest_prob, if_neg (by simp [h])]

theorem noisyTest_ok (a : Fin n → Bool) (i : Fin n) : 2 / 3 ≤ (noisyTest i).prob a 1 (a i) := by
  rw [noisyTest_prob, if_pos rfl]; norm_num

/-- **Robust search over the noisy testers**: a `1` among `n` bits, or `none`, with error
`1/3`, in at most `10206·⌈√n⌉` queries.  The testers overlap freely with the input. -/
theorem noisy_search (n : ℕ) :
    SolvesWithErrorOn (robustSearch (fun i : Fin n => noisyTest i) (fun _ => 1) 1).alg
      (robustSearchBudget n 1) (fun x : Fin n → Bool => x) (SearchOK fun x i => x i) (1 / 3)
    ∧ robustSearchBudget n 1 ≤ 10206 * ⌈Real.sqrt n⌉₊ := by
  refine ⟨robustSearch_solves (fun _ => le_rfl) fun x i => noisyTest_ok x i, ?_⟩
  have := robustSearchBudget_le n 1
  simpa using this

end Noisy

end RobustSearchAcceptance
end QuantumQueryComplexity
