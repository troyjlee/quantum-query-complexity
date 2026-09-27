import QuantumQueryComplexity.Quantum.KronLift

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000

/-!
# Classical post-queries after a quantum algorithm

`A.postQuery sel Q dec` runs `A` for `Q` queries, parks the query registers, then makes `k`
further **classical** queries at the indices `sel o j` selected by the outcome `o` that `A`
would announce (read off the parked basis state), stores the answers in `k` workspace slots
and announces `dec o answers`.  No measurement is taken in between: every post-step is a
basis permutation, so the final state is `∑_p ψ_Q(p) |Φ_a p⟩` with `Φ_a` injective
(`postQuery_state_add`), and

    prob (Q + k) o' = ∑_{o : dec o (a ∘ sel o) = o'} prob_A Q o        (`postQuery_prob_eq_sum`).

Consequences: every outcome of positive probability is `dec o (a ∘ sel o)` for some `o`
(`postQuery_exists_of_pos`), and the mass of any set of raw outcomes is carried to its image
(`sum_prob_le_postQuery`).  This is the verification wrapper of the ordered-product theorems:
with `sel` the positions of the raw record and `dec` the record rewritten with the queried
letters, every branch's output is truthful.

The construction follows `ReadAll.lean`: **swap, don't assign**.  `pqParkPerm` swaps the query
registers with a parking slot, `movePerm j` transposes `none` with the `j`-th target in the
index register (a transposition, so unitary, although the target depends on the workspace),
and `storePerm j` swaps the answer register with the blank slot `j`.  One physical query is
spent per slot, idle when the slot's target is `none`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ O O' : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {W : Type} [Fintype W] [DecidableEq W]

/-- The parked query registers. -/
abbrev Park (ι σ : Type) : Type := Option ι × Option σ

/-- The wrapper's workspace: the original workspace, the parked registers, `k` answer slots. -/
abbrev PQWork (ι σ W : Type) (k : ℕ) : Type := W × Park ι σ × (Fin k → Option σ)

section Basics

variable (ι σ W) (k : ℕ)

/-- The factorizing equivalence: the query registers and `W` form the system. -/
def pqEquiv : QBasis ι σ (PQWork ι σ W k) ≃ QBasis ι σ W × (Park ι σ × (Fin k → Option σ)) where
  toFun p := ((p.1, p.2.1, p.2.2.1), p.2.2.2)
  invFun q := (q.1.1, q.1.2.1, (q.1.2.2, q.2))
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

lemma pqEquiv_oracleCompat : OracleCompat (pqEquiv ι σ W k) := by
  intro a p
  rcases p with ⟨i, s, w, d⟩
  cases i <;> rfl

/-- The blank environment: parked registers empty, all slots blank. -/
def pqBlank : Park ι σ × (Fin k → Option σ) := ((none, none), fun _ => none)

end Basics

section Perms

variable {k : ℕ} (A : QAlg ι σ O W) (sel : O → Fin k → Option ι)

/-- The outcome `A` would announce, read off the parked registers. -/
def pqOut (p : QBasis ι σ (PQWork ι σ W k)) : O :=
  A.readout (p.2.2.2.1.1, p.2.2.2.1.2, p.2.2.1)

/-- The index of the `j`-th extra query (`none` beyond the `k` slots). -/
def pqTarget (o : O) (j : ℕ) : Option ι := if h : j < k then sel o ⟨j, h⟩ else none

lemma pqTarget_of_lt {j : ℕ} (h : j < k) (o : O) : pqTarget sel o j = sel o ⟨j, h⟩ := dif_pos h

lemma pqTarget_of_le {j : ℕ} (h : k ≤ j) (o : O) : pqTarget sel o j = none := dif_neg (by omega)

/-- Swap the query registers with the parking slot. -/
def pqParkMap (p : QBasis ι σ (PQWork ι σ W k)) : QBasis ι σ (PQWork ι σ W k) :=
  (p.2.2.2.1.1, p.2.2.2.1.2, (p.2.2.1, (p.1, p.2.1), p.2.2.2.2))

lemma pqParkMap_involutive : Function.Involutive (pqParkMap (ι := ι) (σ := σ) (W := W) (k := k)) := by
  rintro ⟨i, s, w, ⟨pi, ps⟩, ans⟩; rfl

def pqParkPerm : Equiv.Perm (QBasis ι σ (PQWork ι σ W k)) :=
  Function.Involutive.toPerm _ pqParkMap_involutive

/-- Transpose `none` with the `j`-th target in the index register. -/
def moveMap (j : ℕ) (p : QBasis ι σ (PQWork ι σ W k)) : QBasis ι σ (PQWork ι σ W k) :=
  (Equiv.swap none (pqTarget sel (pqOut A p) j) p.1, p.2)

lemma moveMap_involutive (j : ℕ) : Function.Involutive (moveMap A sel j) := by
  rintro ⟨i, s, rest⟩
  simp [moveMap, pqOut]

def movePerm (j : ℕ) : Equiv.Perm (QBasis ι σ (PQWork ι σ W k)) :=
  Function.Involutive.toPerm _ (moveMap_involutive A sel j)

/-- Swap the answer register with slot `j` (idle beyond the `k` slots). -/
def storeMap (j : ℕ) (p : QBasis ι σ (PQWork ι σ W k)) : QBasis ι σ (PQWork ι σ W k) :=
  if h : j < k then
    (p.1, p.2.2.2.2 ⟨j, h⟩, (p.2.2.1, p.2.2.2.1, Function.update p.2.2.2.2 ⟨j, h⟩ p.2.1))
  else p

lemma storeMap_involutive (j : ℕ) :
    Function.Involutive (storeMap (ι := ι) (σ := σ) (W := W) (k := k) j) := by
  rintro ⟨i, s, w, pk, ans⟩
  unfold storeMap
  split_ifs with h
  · simp [Function.update_idem]
  · rfl

def storePerm (j : ℕ) : Equiv.Perm (QBasis ι σ (PQWork ι σ W k)) :=
  Function.Involutive.toPerm _ (storeMap_involutive j)

/-! ## The schedule -/

variable (Q : ℕ)

/-- The wrapper's step at time `t`: `A`'s step lifted for `t < Q`; at `t = Q` also park and
aim at the first target; afterwards store the previous answer, return the index register to
`none` and aim at the next target. -/
noncomputable def postStep (t : ℕ) :
    Matrix (QBasis ι σ (PQWork ι σ W k)) (QBasis ι σ (PQWork ι σ W k)) ℂ :=
  if t < Q then kronLift (pqEquiv ι σ W k) (A.step t)
  else if t = Q then
    qPerm (movePerm A sel 0) * (qPerm pqParkPerm * kronLift (pqEquiv ι σ W k) (A.step Q))
  else qPerm (movePerm A sel (t - Q)) * (qPerm (movePerm A sel (t - Q - 1)) * qPerm (storePerm (t - Q - 1)))

lemma postStep_unitary (t : ℕ) :
    postStep A sel Q t ∈ Matrix.unitaryGroup (QBasis ι σ (PQWork ι σ W k)) ℂ := by
  unfold postStep
  split_ifs
  · exact kronLift_mem_unitaryGroup _ (A.step_unitary t)
  · exact mul_mem_qUnitary (qPerm_mem_unitaryGroup _) (mul_mem_qUnitary
      (qPerm_mem_unitaryGroup _) (kronLift_mem_unitaryGroup _ (A.step_unitary Q)))
  · exact mul_mem_qUnitary (qPerm_mem_unitaryGroup _) (mul_mem_qUnitary
      (qPerm_mem_unitaryGroup _) (qPerm_mem_unitaryGroup _))

lemma postStep_of_lt {t : ℕ} (h : t < Q) :
    postStep A sel Q t = kronLift (pqEquiv ι σ W k) (A.step t) := if_pos h

lemma postStep_self :
    postStep A sel Q Q
      = qPerm (movePerm A sel 0) * (qPerm pqParkPerm * kronLift (pqEquiv ι σ W k) (A.step Q)) := by
  unfold postStep
  rw [if_neg (lt_irrefl _), if_pos rfl]

lemma postStep_add (j : ℕ) :
    postStep A sel Q (Q + j + 1)
      = qPerm (movePerm A sel (j + 1)) * (qPerm (movePerm A sel j) * qPerm (storePerm j)) := by
  unfold postStep
  rw [if_neg (by omega), if_neg (by omega)]
  have h2 : Q + j + 1 - Q - 1 = j := by omega
  have h1 : Q + j + 1 - Q = j + 1 := by omega
  rw [h2, h1]

variable (dec : O → (Fin k → Option σ) → O')

/-- **The post-query wrapper.** -/
noncomputable def _root_.QuantumQueryComplexity.QAlg.postQuery : QAlg ι σ O' (PQWork ι σ W k) where
  init := splitVec (pqEquiv ι σ W k) A.init (qBasis (pqBlank ι σ k))
  init_isQState := by
    show qNormSq _ = 1
    rw [qNormSq_splitVec, show qNormSq A.init = 1 from A.init_isQState, qNormSq_qBasis, one_mul]
  step := postStep A sel Q
  step_unitary := postStep_unitary A sel Q
  readout := fun p => dec (pqOut A p) p.2.2.2.2

lemma postQuery_step (t : ℕ) : (A.postQuery sel Q dec).step t = postStep A sel Q t := rfl

/-! ## The state before the extra queries -/

theorem postQuery_state_of_lt (a : ι → σ) :
    ∀ {t : ℕ}, t < Q → (A.postQuery sel Q dec).state a t
      = splitVec (pqEquiv ι σ W k) (A.state a t) (qBasis (pqBlank ι σ k))
  | 0, h => by
    show postStep A sel Q 0 *ᵥ splitVec (pqEquiv ι σ W k) A.init (qBasis (pqBlank ι σ k)) = _
    rw [postStep_of_lt A sel Q h, kronLift_mulVec_splitVec]
    rfl
  | t + 1, h => by
    rw [QAlg.state_succ, postQuery_state_of_lt a (by omega), postQuery_step,
      postStep_of_lt A sel Q h, oracleMat_mulVec_splitVec (pqEquiv_oracleCompat ι σ W k),
      kronLift_mulVec_splitVec]
    rfl

theorem postQuery_state_self (a : ι → σ) :
    (A.postQuery sel Q dec).state a Q
      = qPerm (movePerm A sel 0) *ᵥ (qPerm pqParkPerm *ᵥ
          splitVec (pqEquiv ι σ W k) (A.state a Q) (qBasis (pqBlank ι σ k))) := by
  cases Q with
  | zero =>
    show postStep A sel 0 0 *ᵥ splitVec (pqEquiv ι σ W k) A.init (qBasis (pqBlank ι σ k)) = _
    rw [postStep_self, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, kronLift_mulVec_splitVec]
    rfl
  | succ Q' =>
    rw [QAlg.state_succ, postQuery_state_of_lt A sel (Q' + 1) dec a (Nat.lt_succ_self _),
      postQuery_step, postStep_self, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      oracleMat_mulVec_splitVec (pqEquiv_oracleCompat ι σ W k), kronLift_mulVec_splitVec]
    rfl

/-! ## The classical phase -/

/-- A split state with a basis environment is a sum of basis states. -/
lemma splitVec_qBasis_eq_sum {β γ δ : Type} [Fintype β] [DecidableEq β] [Fintype γ]
    [DecidableEq γ] [Fintype δ] [DecidableEq δ] (e : β ≃ γ × δ) (φ : γ → ℂ) (d : δ) :
    splitVec e φ (qBasis d) = ∑ p, φ p • qBasis (e.symm (p, d)) := by
  funext q
  rw [splitVec_apply, Finset.sum_apply, qBasis_apply]
  simp only [Pi.smul_apply, qBasis_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (e q).1]
  · by_cases h : (e q).2 = d
    · have hq : q = e.symm ((e q).1, d) := by rw [← h]; simp
      rw [if_pos h, if_pos hq]
    · have hq : q ≠ e.symm ((e q).1, d) := by
        intro hq; apply h; rw [hq]; simp
      rw [if_neg h, if_neg hq]
  · intro p _ hp
    rw [if_neg, mul_zero]
    intro hq; apply hp; rw [hq]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The answers stored after `j` extra queries. -/
def pqAns (a : ι → σ) (o : O) (j : ℕ) : Fin k → Option σ :=
  fun m => if (m : ℕ) < j then Option.map a (sel o m) else none

lemma pqAns_zero (a : ι → σ) (o : O) : pqAns sel a o 0 = fun _ => none := by
  funext m; simp [pqAns]

lemma pqAns_self (a : ι → σ) (o : O) {j : ℕ} (h : j < k) : pqAns sel a o j ⟨j, h⟩ = none := by
  simp [pqAns]

lemma pqAns_update (a : ι → σ) (o : O) {j : ℕ} (h : j < k) :
    Function.update (pqAns sel a o j) ⟨j, h⟩ (Option.map a (sel o ⟨j, h⟩))
      = pqAns sel a o (j + 1) := by
  funext m
  by_cases hm : m = ⟨j, h⟩
  · subst hm; rw [Function.update_self, pqAns]; simp
  · rw [Function.update_of_ne hm, pqAns, pqAns]
    have : (m : ℕ) ≠ j := fun hc => hm (Fin.ext hc)
    by_cases hlt : (m : ℕ) < j
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]

lemma pqAns_of_le (a : ι → σ) (o : O) {j : ℕ} (h : k ≤ j) :
    pqAns sel a o (j + 1) = pqAns sel a o j := by
  funext m
  simp only [pqAns]
  have := m.isLt
  rw [if_pos (by omega), if_pos (by omega)]

lemma pqAns_k (a : ι → σ) (o : O) : pqAns sel a o k = fun m => Option.map a (sel o m) := by
  funext m; simp [pqAns, m.isLt]

/-- The classical image of a basis state of `A` after `j` extra queries. -/
def pqImage (a : ι → σ) (j : ℕ) (p : QBasis ι σ W) : QBasis ι σ (PQWork ι σ W k) :=
  (pqTarget sel (A.readout p) j, none, (p.2.2, (p.1, p.2.1), pqAns sel a (A.readout p) j))

lemma pqImage_injective (a : ι → σ) (j : ℕ) : Function.Injective (pqImage A sel a j) := by
  intro p q h
  simp only [pqImage, Prod.mk.injEq] at h
  obtain ⟨_, _, hw, ⟨hi, hs⟩, _⟩ := h
  exact Prod.ext hi (Prod.ext hs hw)

/-- One extra query advances the classical image. -/
lemma pqImage_step (a : ι → σ) (j : ℕ) (p : QBasis ι σ W) :
    movePerm A sel (j + 1) (movePerm A sel j (storePerm j (oracleMap a (pqImage A sel a j p))))
      = pqImage A sel a (j + 1) p := by
  rcases p with ⟨i₀, s₀, w⟩
  show moveMap A sel (j + 1) (moveMap A sel j (storeMap j (oracleMap a
    (pqImage A sel a j (i₀, s₀, w))))) = _
  -- the stored slots after this query
  have hstore : storeMap j (oracleMap a (pqImage A sel a j (i₀, s₀, w)))
      = (pqTarget sel (A.readout (i₀, s₀, w)) j, none,
          (w, (i₀, s₀), pqAns sel a (A.readout (i₀, s₀, w)) (j + 1))) := by
    by_cases hj : j < k
    · rw [pqImage, pqTarget_of_lt sel hj]
      cases hsel : sel (A.readout (i₀, s₀, w)) ⟨j, hj⟩ with
      | none =>
          rw [oracleMap_none, storeMap, dif_pos hj]
          simp only
          rw [pqAns_self sel a _ hj, ← pqAns_update sel a _ hj, hsel]
          rfl
      | some i =>
          rw [oracleMap_blank, storeMap, dif_pos hj]
          simp only
          rw [pqAns_self sel a _ hj, ← pqAns_update sel a _ hj, hsel]
          rfl
    · rw [pqImage, pqTarget_of_le sel (by omega), oracleMap_none,
        storeMap, dif_neg hj, pqAns_of_le sel a _ (by omega)]
  rw [hstore]
  simp only [moveMap, pqOut]
  rw [Equiv.swap_apply_right, Equiv.swap_apply_left]
  rfl

/-- **The invariant of the classical phase**: after `Q + j` queries the state is the
`A`-state after `Q` queries, transported basis state by basis state. -/
theorem postQuery_state_add (a : ι → σ) :
    ∀ j : ℕ, (A.postQuery sel Q dec).state a (Q + j)
      = ∑ p, (A.state a Q) p • qBasis (pqImage A sel a j p)
  | 0 => by
    rw [Nat.add_zero, postQuery_state_self, splitVec_qBasis_eq_sum, Matrix.mulVec_sum,
      Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, qPerm_mulVec_qBasis, qPerm_mulVec_qBasis]
    rcases p with ⟨i, s, w⟩
    have hpt : movePerm A sel 0 (pqParkPerm ((pqEquiv ι σ W k).symm ((i, s, w), pqBlank ι σ k)))
        = pqImage A sel a 0 (i, s, w) := by
      show moveMap A sel 0 (pqParkMap ((pqEquiv ι σ W k).symm ((i, s, w), pqBlank ι σ k))) = _
      simp only [moveMap, pqParkMap, pqImage, pqAns_zero, pqEquiv, pqBlank, pqOut,
        Equiv.coe_fn_symm_mk]
      rw [Equiv.swap_apply_left]
    rw [hpt]
  | j + 1 => by
    rw [show Q + (j + 1) = Q + j + 1 by ring, QAlg.state_succ, postQuery_state_add a j,
      postQuery_step, postStep_add, Matrix.mulVec_sum, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, oracleMat_mulVec_qBasis, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, qPerm_mulVec_qBasis, qPerm_mulVec_qBasis, qPerm_mulVec_qBasis,
      pqImage_step]

/-! ## The outcome distribution -/

variable [DecidableEq O] [DecidableEq O']

/-- Measuring a sum of distinct basis states: the mass of each is its squared coefficient. -/
lemma qProb_sum_smul_qBasis {H H' : Type} [Fintype H] [DecidableEq H] [Fintype H']
    [DecidableEq H'] {O' : Type} [DecidableEq O'] (r : H' → O') (Φ : H → H')
    (hΦ : Function.Injective Φ) (c : H → ℂ) (o' : O') :
    qProb r (∑ p, c p • qBasis (Φ p)) o'
      = ∑ p, if r (Φ p) = o' then Complex.normSq (c p) else 0 := by
  have hvec : ∀ h, (∑ p, c p • qBasis (Φ p)) h = ∑ p, if h = Φ p then c p else 0 := by
    intro h
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [qBasis_apply]
  have hoff : ∀ h, (∀ p, h ≠ Φ p) → (∑ p, c p • qBasis (Φ p)) h = 0 := by
    intro h hh
    rw [hvec]
    exact Finset.sum_eq_zero fun p _ => if_neg (hh p)
  have hon : ∀ p, (∑ q, c q • qBasis (Φ q)) (Φ p) = c p := by
    intro p
    rw [hvec, Finset.sum_eq_single p]
    · rw [if_pos rfl]
    · intro q _ hq
      rw [if_neg]
      intro he
      exact hq (hΦ he).symm
    · intro h; exact absurd (Finset.mem_univ _) h
  unfold qProb
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image Φ)) (fun h _ hnot => ?_),
    Finset.sum_image (fun x _ y _ hxy => hΦ hxy)]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [hon]
  · rw [hoff h, Complex.normSq_zero]
    · split_ifs <;> rfl
    · intro p hp
      exact hnot (Finset.mem_image.2 ⟨p, Finset.mem_univ _, hp.symm⟩)

/-- **The outcome distribution of the wrapper**, basis state by basis state. -/
theorem postQuery_prob (a : ι → σ) (o' : O') :
    (A.postQuery sel Q dec).prob a (Q + k) o'
      = ∑ p, if dec (A.readout p) (fun m => Option.map a (sel (A.readout p) m)) = o'
          then Complex.normSq ((A.state a Q) p) else 0 := by
  rw [QAlg.prob, postQuery_state_add, qProb_sum_smul_qBasis _ _ (pqImage_injective A sel a k)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [show (A.postQuery sel Q dec).readout (pqImage A sel a k p)
    = dec (A.readout p) (pqAns sel a (A.readout p) k) from rfl, pqAns_k]

/-- **The outcome distribution of the wrapper**, by raw outcomes: the mass of `o'` is the
mass of the raw outcomes that verify to `o'`. -/
theorem postQuery_prob_eq_sum [Fintype O] (a : ι → σ) (o' : O') :
    (A.postQuery sel Q dec).prob a (Q + k) o'
      = ∑ o ∈ Finset.univ.filter (fun o => dec o (fun m => Option.map a (sel o m)) = o'),
          A.prob a Q o := by
  rw [postQuery_prob]
  simp only [QAlg.prob, qProb]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Every outcome of positive probability is a verified raw outcome.** -/
theorem postQuery_exists_of_pos (a : ι → σ) (o' : O')
    (h : 0 < (A.postQuery sel Q dec).prob a (Q + k) o') :
    ∃ o, dec o (fun m => Option.map a (sel o m)) = o' := by
  rw [postQuery_prob] at h
  obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  refine ⟨A.readout p, ?_⟩
  by_contra hne
  exact hp (if_neg hne)

/-- **Mass is carried to the image**: raw outcomes in `S` verify into `S'`, so `S'` is at least
as likely as `S` was. -/
theorem sum_prob_le_postQuery [Fintype O] (a : ι → σ) (S : Finset O) (S' : Finset O')
    (hS : ∀ o ∈ S, dec o (fun m => Option.map a (sel o m)) ∈ S') :
    ∑ o ∈ S, A.prob a Q o ≤ ∑ o' ∈ S', (A.postQuery sel Q dec).prob a (Q + k) o' := by
  simp only [postQuery_prob_eq_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  calc ∑ o ∈ S, A.prob a Q o
      = ∑ o ∈ S, (if dec o (fun m => Option.map a (sel o m)) ∈ S' then A.prob a Q o else 0) :=
        Finset.sum_congr rfl fun o ho => by rw [if_pos (hS o ho)]
    _ ≤ ∑ o, (if dec o (fun m => Option.map a (sel o m)) ∈ S' then A.prob a Q o else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun o _ _ => by
          split_ifs
          · exact A.prob_nonneg _ _ _
          · exact le_rfl
    _ = ∑ o, ∑ o' ∈ S', (if dec o (fun m => Option.map a (sel o m)) = o' then A.prob a Q o
          else 0) := by
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [Finset.sum_ite_eq]

end Perms

end QuantumQueryComplexity
