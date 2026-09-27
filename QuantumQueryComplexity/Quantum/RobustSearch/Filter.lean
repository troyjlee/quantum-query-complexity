import QuantumQueryComplexity.Quantum.RobustSearch.Recursion
set_option synthInstance.maxSize 3200
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Robust search: the test banks and the level sequence

* `TestBank.ofAlgs A q T` — the bank of the supplied algorithms: the workspaces `W i`, initial
  states and readouts may all differ; each `A i` is run for its own `q i ≤ T` queries and
  parked (`selectPadded`), so **one test of a superposition of candidates costs `T`**.
  `accProb_ofAlgs`: the test of `i` accepts with the probability that `A i` outputs `true`.
* `TestBank.pow K k` — `k` fresh copies read by majority (`CoherentMajority.lean`), cost
  `k · K.F.len`.  `accProb_pow_twelve_ge / _le`: from error `1/3`, `12·n` copies accept a
  marked candidate with probability `≥ 1 − 2^{-n}` and an unmarked one with `≤ 2^{-n}`.
* `rsBase` — level `0`: the uniform superposition of the indices, flag constantly set, no
  queries.  `rsLevel bank i₀ n` — `n` recursion steps, the step into level `n` using the
  bank `bank n`.
* `levelLen T n`, `rsLevel_len` — the exact query count, `q₀ = 0`,
  `q_{n+1} = 3·q_n + 12·(n+10)·T`, and the closed form
  `levelLen_closed : q_n + T·(6n + 63) = 63·T·3ⁿ`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  {I : Type} [Fintype I] [DecidableEq I]

namespace TestBank

section OfAlgs

variable {W : I → Type} [∀ i, Fintype (W i)] [∀ i, DecidableEq (W i)]

/-- **The bank of the supplied bounded-error algorithms.** -/
noncomputable def ofAlgs (A : ∀ i, QAlg ι σ Bool (W i)) (q : I → ℕ) (T : ℕ) : TestBank ι σ I where
  B := Σ i, CtrlWork ι (W i)
  F := selectPadded A q T
  β := selectInit A
  β_unit := isQState_selectInit A
  t := selectReadout A

@[simp] lemma ofAlgs_len (A : ∀ i, QAlg ι σ Bool (W i)) (q : I → ℕ) (T : ℕ) :
    (ofAlgs A q T).F.len = T := rfl

theorem accProb_ofAlgs {A : ∀ i, QAlg ι σ Bool (W i)} {q : I → ℕ} {T : ℕ}
    (hq : ∀ i, q i ≤ T) (a : ι → σ) (i : I) (o : Bool) :
    qProb (ofAlgs A q T).t ((ofAlgs A q T).F.run a *ᵥ (ofAlgs A q T).β i) o
      = (A i).prob a (q i) o :=
  selectPadded_prob hq a i o

end OfAlgs

variable (K : TestBank ι σ I)

/-- **`k` fresh copies, read by majority.** -/
noncomputable def pow (k : ℕ) : TestBank ι σ I where
  B := PowWork ι σ K.B k
  F := powRoutine K.F k
  β := fun i => powInit (K.β i) k
  β_unit := fun i => isQState_powInit (K.β_unit i) k
  t := majReadout K.t k

@[simp] lemma pow_len (k : ℕ) : (K.pow k).F.len = k * K.F.len := powRoutine_len K.F k

lemma accProb_pow (k : ℕ) (a : ι → σ) (i : I) :
    (K.pow k).accProb a i = qProb (majReadout K.t k) (powInit (K.F.run a *ᵥ K.β i) k) true := by
  show qProb (majReadout K.t k) ((powRoutine K.F k).run a *ᵥ powInit (K.β i) k) true = _
  rw [powRoutine_run]

lemma isQState_run (a : ι → σ) (i : I) : IsQState (K.F.run a *ᵥ K.β i) :=
  IsQState.mulVec (K.F.run_mem_unitaryGroup a) (K.β_unit i)

lemma qProb_not_le {a : ι → σ} {i : I} {bv : Bool}
    (h : 2 / 3 ≤ qProb K.t (K.F.run a *ᵥ K.β i) bv) :
    qProb K.t (K.F.run a *ᵥ K.β i) (!bv) ≤ 1 / 3 := by
  have hsum := sum_qProb_eq_one (K.isQState_run a i) K.t
  rw [Fintype.sum_bool] at hsum
  cases bv
  · simp only [Bool.not_false]; linarith
  · simp only [Bool.not_true]; linarith

/-- A marked candidate passes `12·n` copies with probability `≥ 1 − 2^{-n}`. -/
theorem accProb_pow_twelve_ge {a : ι → σ} {i : I}
    (h : 2 / 3 ≤ qProb K.t (K.F.run a *ᵥ K.β i) true) (n : ℕ) :
    1 - (1 / 2) ^ n ≤ (K.pow (12 * n)).accProb a i := by
  rw [accProb_pow]
  exact one_sub_le_maj_twelve K.t (K.isQState_run a i) true (K.qProb_not_le h) n

/-- An unmarked candidate passes `12·n` copies with probability `≤ 2^{-n}`. -/
theorem accProb_pow_twelve_le {a : ι → σ} {i : I}
    (h : 2 / 3 ≤ qProb K.t (K.F.run a *ᵥ K.β i) false) (n : ℕ) :
    (K.pow (12 * n)).accProb a i ≤ (1 / 2) ^ n := by
  rw [accProb_pow]
  exact maj_twelve_le K.t (K.isQState_run a i) false (K.qProb_not_le h) n

end TestBank

/-! ## The base level -/

section Base

variable (ι σ I)

/-- The uniform superposition of the indices, query registers blank. -/
noncomputable def uniformWork : QBasis ι σ I → ℂ := fun y =>
  if y.1 = none ∧ y.2.1 = none then (((Real.sqrt (Fintype.card I))⁻¹ : ℝ) : ℂ) else 0

variable {ι σ I}

lemma sum_uniformWork [Nonempty I] (g : I → ℝ) :
    ∑ y : QBasis ι σ I, g y.2.2 * Complex.normSq (uniformWork ι σ I y)
      = (∑ i, g i) / Fintype.card I := by
  have hc : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hn : Complex.normSq (((Real.sqrt (Fintype.card I))⁻¹ : ℝ) : ℂ)
      = 1 / (Fintype.card I : ℝ) := by
    rw [Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt hc.le, one_div]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single none]
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single none]
    · simp only [uniformWork, and_self, if_true, hn]
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    · intro t _ ht
      exact Finset.sum_eq_zero fun i _ => by simp [uniformWork, ht]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro k _ hk
    exact Finset.sum_eq_zero fun y _ => by simp [uniformWork, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma isQState_uniformWork [Nonempty I] : IsQState (uniformWork ι σ I) := by
  have h := sum_uniformWork (ι := ι) (σ := σ) (I := I) fun _ => 1
  have hc : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  simp only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [IsQState, qNormSq_def, h, div_self hc.ne']

variable (ι σ I)

/-- **Level `0`**: every index, flag set, no queries. -/
noncomputable def rsBase [Nonempty I] : RSLevel ι σ I where
  Y := I
  A := QRoutine.identity
  init := uniformWork ι σ I
  init_unit := isQState_uniformWork
  acc := fun _ => true
  idx := fun y => y.2.2

variable {ι σ I}

lemma rsBase_u [Nonempty I] (a : ι → σ) (i : I) :
    (rsBase ι σ I).u a i = 1 / Fintype.card I := by
  show qProb (fun y : QBasis ι σ I => (true, y.2.2))
    ((QRoutine.identity (ι := ι) (σ := σ) (W := I)).run a *ᵥ uniformWork ι σ I) (true, i) = _
  rw [QRoutine.identity_run, Matrix.one_mulVec, qProb]
  have h := sum_uniformWork (ι := ι) (σ := σ) (I := I) fun j => if j = i then 1 else 0
  rw [Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _)] at h
  rw [← h]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y.2.2 = i <;> simp [hy]

lemma rsBase_p [Nonempty I] (a : ι → σ) : (rsBase ι σ I).p a = 1 := by
  rw [RSLevel.p_eq_sum]
  simp only [rsBase_u, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  field_simp

end Base

/-! ## The level sequence -/

/-- `n` recursion steps; the step into level `n` uses the bank `bank n`. -/
noncomputable def rsLevel [Nonempty I] (bank : ℕ → TestBank ι σ I) (i₀ : I) : ℕ → RSLevel ι σ I
  | 0 => rsBase ι σ I
  | n + 1 => (rsLevel bank i₀ n).next (bank (n + 1)) i₀

/-- The query count of level `n` with filters of `12·(n+9)` copies of cost `T`. -/
def levelLen (T : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 3 * levelLen T n + 12 * (n + 10) * T

theorem levelLen_closed (T n : ℕ) : levelLen T n + T * (6 * n + 63) = 63 * T * 3 ^ n := by
  induction n with
  | zero => simp [levelLen]; ring
  | succ n ih =>
      rw [levelLen, pow_succ]
      nlinarith

theorem levelLen_le (T n : ℕ) : levelLen T n ≤ 63 * T * 3 ^ n := by
  have := levelLen_closed T n
  omega

theorem rsLevel_len [Nonempty I] (bank : ℕ → TestBank ι σ I) (i₀ : I) (T : ℕ)
    (hbank : ∀ n, (bank n).F.len = 12 * (n + 9) * T) (n : ℕ) :
    (rsLevel bank i₀ n).A.len = levelLen T n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [rsLevel, RSLevel.next_len, ih, hbank, levelLen]

theorem rsLevel_u_succ [Nonempty I] (bank : ℕ → TestBank ι σ I) (i₀ : I) (n : ℕ) (a : ι → σ)
    (i : I) :
    (rsLevel bank i₀ (n + 1)).u a i
      = (3 - 4 * (rsLevel bank i₀ n).p a) ^ 2 * (rsLevel bank i₀ n).u a i
        * (bank (n + 1)).accProb a i :=
  (rsLevel bank i₀ n).next_u (bank (n + 1)) i₀ a i

end QuantumQueryComplexity
