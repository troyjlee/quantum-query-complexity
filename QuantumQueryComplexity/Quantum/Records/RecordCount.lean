import QuantumQueryComplexity.Quantum.Records.Product
import QuantumQueryComplexity.Quantum.JointState.Oracle

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Query locality and the record-count bound

For a product distribution `ρ` with full-support marginals, a query to coordinate `i` is an
input-dependent workspace operator that reads only `xᵢ`. It commutes with every `Eⱼ` and `Dⱼ`,
`j ≠ i`, so it can change the record set only at `i`:

    P_{S'} Oᵢ P_S = 0  unless  S' △ S ⊆ {i}    (`recProj_mul_jOracle_mul_recProj`).

An oracle family that preserves an index-register sector, acts input-independently on the idle
sector and reads only `xᵢ` on sector `i` (`IsSectorLocal`) therefore adds at most one record per
query (`recLe_mul_jOracle`). The library's value oracle and XOR oracle are sector local. Since the
initial joint state `|ρ⟩ ⊗ U₀|init⟩` has no records and the algorithm's own unitaries act only on
the workspace, **after `t` queries the joint state has at most `t` records**:

    Ψₜ ∈ (⊕_{|S| ≤ t} P_S) ⊗ workspace    (`recLe_mul_jointState`, `recLe_mul_jointXorState`).

This is [Bel26, Proposition 3.2], for every product reference distribution and in both oracle
models.

## Main definitions

* `FinDist.recLe`: the projection onto records of size at most `t`.
* `IsSectorLocal`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ A : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype A]

/-- **A sector-local oracle family.** `O a` is block diagonal for the sectors `sec`; on a column in
the idle sector `none` it does not depend on the input; on a column in sector `some i` it depends
on the input only through `aᵢ`. -/
def IsSectorLocal (sec : A → Option ι) (O : (ι → σ) → Matrix A A ℂ) : Prop :=
  (∀ a p q, sec p ≠ sec q → O a p q = 0) ∧
    ∀ a b p q, (∀ i, sec q = some i → a i = b i) → O a p q = O b p q

/-- The entries of the value oracle: `1` at `(p, oracleMap a p)`, `0` elsewhere. -/
private lemma oracleMat_apply_eq {W : Type} [Fintype W] [DecidableEq W] (a : ι → σ)
    (p q : QBasis ι σ W) : oracleMat a p q = if oracleMap a p = q then 1 else 0 := by
  have h := oracleMat_mulVec_apply a (Pi.single q 1) p
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
  rw [h, Pi.single_apply]

/-- The value oracle is sector local for its index register. -/
theorem isSectorLocal_oracleMat {W : Type} [Fintype W] [DecidableEq W] :
    IsSectorLocal (fun p : QBasis ι σ W => p.1) oracleMat := by
  refine ⟨fun a p q hpq => ?_, fun a b p q hab => ?_⟩
  · rw [oracleMat_apply_eq, ite_eq_right_iff]
    intro hq
    exact (hpq (by rw [← hq]; exact (oracleMap_fst a p).symm)).elim
  · rw [oracleMat_apply_eq, oracleMat_apply_eq]
    obtain ⟨_ | i, t, w⟩ := p
    · rfl
    · by_cases hq : q.1 = some i
      · rw [oracleMap_some, oracleMap_some, hab i hq]
      · have h1 : oracleMap a ((some i, t, w) : QBasis ι σ W) ≠ q := fun h => hq (by rw [← h]; rfl)
        have h2 : oracleMap b ((some i, t, w) : QBasis ι σ W) ≠ q := fun h => hq (by rw [← h]; rfl)
        simp only [h1, h2, ↓reduceIte]

/-- The XOR oracle is sector local for its index register. -/
theorem isSectorLocal_xorOracleMat {W : Type} [Fintype W] [DecidableEq W] :
    IsSectorLocal (fun p : QBasis ι Bool W => p.1) xorOracleMat := by
  refine ⟨fun a p q hpq => ?_, fun a b p q hab => ?_⟩
  · rw [xorOracleMat_apply, ite_eq_right_iff]
    intro hq
    obtain ⟨_ | i, t, w⟩ := p <;> exact absurd (by rw [← hq]; rfl) hpq
  · rw [xorOracleMat_apply, xorOracleMat_apply]
    obtain ⟨_ | i, t, w⟩ := p
    · rfl
    · by_cases hq : q.1 = some i
      · rw [xorOracleMap_some, xorOracleMap_some, hab i hq]
      · have h1 : xorOracleMap a ((some i, t, w) : QBasis ι Bool W) ≠ q :=
          fun h => hq (by rw [← h]; rfl)
        have h2 : xorOracleMap b ((some i, t, w) : QBasis ι Bool W) ≠ q :=
          fun h => hq (by rw [← h]; rfl)
        simp only [h1, h2, ↓reduceIte]

/-! ## Splitting an oracle family by sectors -/

section Split

variable {X : Type}

/-- The joint oracle as an additive map of joint vectors. -/
private def jOracleHom (O : (ι → σ) → Matrix A A ℂ) (read : X → ι → σ) :
    JVec X A →+ JVec X A :=
  AddMonoidHom.mk' (jOracle O read) fun g g' => by
    funext x
    exact Matrix.mulVec_add _ (g x) (g' x)

/-- The joint oracle is additive in the joint vector. -/
private lemma jOracle_sum {κ : Type} (O : (ι → σ) → Matrix A A ℂ) (read : X → ι → σ)
    (s : Finset κ) (g : κ → JVec X A) :
    jOracle O read (∑ k ∈ s, g k) = ∑ k ∈ s, jOracle O read (g k) :=
  map_sum (jOracleHom O read) g s

/-- The columns of an oracle family in sector `k`, the other columns set to zero. -/
private def secPart (sec : A → Option ι) (O : (ι → σ) → Matrix A A ℂ) (k : Option ι) :
    (ι → σ) → Matrix A A ℂ := fun a p q => if sec q = k then O a p q else 0

/-- A joint oracle is the sum of its sector parts. -/
private lemma jOracle_eq_sum_secPart (sec : A → Option ι) (O : (ι → σ) → Matrix A A ℂ)
    (read : X → ι → σ) (g : JVec X A) :
    jOracle O read g = ∑ k, jOracle (secPart sec O k) read g := by
  ext x p
  simp only [jOracle, Matrix.sum_apply, Matrix.mulVec, dotProduct, secPart]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [ite_mul]

/-- The idle-sector part of a sector-local family does not depend on the input. -/
private lemma secPart_none {sec : A → Option ι} {O : (ι → σ) → Matrix A A ℂ}
    (hO : IsSectorLocal sec O) (a b : ι → σ) : secPart sec O none a = secPart sec O none b := by
  ext p q
  simp only [secPart]
  split_ifs with hq
  · exact hO.2 a b p q fun i hi => absurd (hq.symm.trans hi) (by simp)
  · rfl

/-- The sector-`i` part of a sector-local family depends on the input only through `aᵢ`. -/
private lemma secPart_some {sec : A → Option ι} {O : (ι → σ) → Matrix A A ℂ}
    (hO : IsSectorLocal sec O) (i : ι) (a b : ι → σ) :
    secPart sec O (some i) a = secPart sec O (some i) (Function.update b i (a i)) := by
  ext p q
  simp only [secPart]
  split_ifs with hq
  · refine hO.2 _ _ p q fun i' hi' => ?_
    obtain rfl : i = i' := Option.some_injective _ (hq.symm.trans hi')
    simp
  · rfl

end Split

namespace FinDist

variable (ρ : FinDist (ι → σ))

/-- **The projection onto at most `t` records**, `∑_{|S| ≤ t} P_S`. -/
noncomputable def recLe (t : ℕ) : Matrix ρ.Supp ρ.Supp ℂ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset ι => S.card ≤ t), ρ.recProj S

variable {ρ}

/-- An input-register operator whose entries vanish between inputs with different `xᵢ` commutes
with a joint oracle reading only `xᵢ`. -/
private lemma mul_jOracle_of_apply_eq_zero {i : ι} (M : σ → Matrix A A ℂ)
    (B : Matrix ρ.Supp ρ.Supp ℂ) (hB : ∀ x y : ρ.Supp, x.1 i ≠ y.1 i → B x y = 0)
    (g : JVec ρ.Supp A) :
    B * jOracle (fun a => M (a i)) (fun x : ρ.Supp => (x : ι → σ)) g
      = jOracle (fun a => M (a i)) (fun x : ρ.Supp => (x : ι → σ)) (B * g) := by
  ext x p
  simp only [jOracle, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hxy : x.1 i = y.1 i
  · rw [hxy]
    exact Finset.sum_congr rfl fun q _ => by ring
  · simp [hB x y hxy]

/-- `Eⱼ` commutes with a joint oracle reading only `xᵢ`, `j ≠ i`. -/
private lemma condExp_mul_jOracle {i j : ι} (hji : j ≠ i) (M : σ → Matrix A A ℂ)
    (g : JVec ρ.Supp A) :
    ρ.condExp j * jOracle (fun a => M (a i)) (fun x : ρ.Supp => (x : ι → σ)) g
      = jOracle (fun a => M (a i)) (fun x : ρ.Supp => (x : ι → σ)) (ρ.condExp j * g) := by
  refine mul_jOracle_of_apply_eq_zero M _ (fun x y hxy => ?_) g
  simp only [condExp, ite_eq_right_iff]
  exact fun hag => absurd (hag i hji.symm) hxy

/-- `Dⱼ` commutes with a joint oracle reading only `xᵢ`, `j ≠ i`. -/
private lemma condDiff_mul_jOracle {i j : ι} (hji : j ≠ i) (M : σ → Matrix A A ℂ)
    (g : JVec ρ.Supp A) :
    ρ.condDiff j * jOracle (fun a => M (a i)) (fun x : ρ.Supp => (x : ι → σ)) g
      = jOracle (fun a => M (a i)) (fun x : ρ.Supp => (x : ι → σ)) (ρ.condDiff j * g) := by
  refine mul_jOracle_of_apply_eq_zero M _ (fun x y hxy => ?_) g
  have hne : x ≠ y := fun h => hxy (by rw [h])
  simp only [condDiff, Matrix.sub_apply, Matrix.one_apply_ne hne, condExp, zero_sub, neg_eq_zero,
    ite_eq_right_iff]
  exact fun hag => absurd (hag i hji.symm) hxy

/-- **Query locality** [Bel26, (3.18)]: an operator reading only coordinate `i` moves records only
at `i`. -/
theorem recProj_mul_jOracle_mul_recProj (h : ρ.IsFullProduct) {i : ι} (M : σ → Matrix A A ℂ)
    {S S' : Finset ι} (hSS : ¬ symmDiff S' S ⊆ {i}) (f : JVec ρ.Supp A) :
    ρ.recProj S' * jOracle (fun a => M (a i)) (fun x : ρ.Supp => (x : ι → σ))
      (ρ.recProj S * f) = 0 := by
  obtain ⟨j, hj, hji⟩ := Finset.not_subset.mp hSS
  rw [Finset.mem_singleton] at hji
  rcases Finset.mem_symmDiff.mp hj with ⟨hj', hjS⟩ | ⟨hjS, hj'⟩
  · have h1 : ρ.recProj S = ρ.condExp j * ρ.recProj S := by
      rw [condExp_mul_recProj h]
      simp [hjS]
    have h2 : ρ.recProj S' * ρ.condExp j = 0 := by
      have := congrArg Matrix.conjTranspose (condExp_mul_recProj h j S')
      simpa [hj', Matrix.conjTranspose_mul, (recProj_isHermitian S').eq,
        (ρ.condExp_isHermitian j).eq] using this
    rw [h1, Matrix.mul_assoc, ← condExp_mul_jOracle hji, ← Matrix.mul_assoc, h2, Matrix.zero_mul]
  · have h1 : ρ.recProj S = ρ.condDiff j * ρ.recProj S := by
      rw [condDiff_mul_recProj h]
      simp [hjS]
    have h2 : ρ.recProj S' * ρ.condDiff j = 0 := by
      have := congrArg Matrix.conjTranspose (condDiff_mul_recProj h j S')
      simpa [hj', Matrix.conjTranspose_mul, (recProj_isHermitian S').eq,
        (ρ.condDiff_isHermitian j).eq] using this
    rw [h1, Matrix.mul_assoc, ← condDiff_mul_jOracle hji, ← Matrix.mul_assoc, h2, Matrix.zero_mul]

/-- A joint vector with no component on records larger than `s` is fixed by `recLe s`. -/
private lemma recLe_mul_eq_self_of (h : ρ.IsFullProduct) {s : ℕ} {g : JVec ρ.Supp A}
    (hg : ∀ S : Finset ι, s < S.card → ρ.recProj S * g = 0) : ρ.recLe s * g = g := by
  rw [recLe, Matrix.sum_mul]
  conv_rhs => rw [← Matrix.one_mul g, ← sum_recProj h, Matrix.sum_mul]
  refine Finset.sum_filter_of_ne fun S _ hS => ?_
  by_contra hc
  exact hS (hg S (not_le.mp hc))

/-- The initial joint state `|ρ⟩ ⊗ v` has no records. -/
private lemma recLe_mul_ket_smul (h : ρ.IsFullProduct) (s : ℕ) (v : A → ℂ) (g : JVec ρ.Supp A)
    (hg : ∀ x, g x = ρ.ket x • v) : ρ.recLe s * g = g := by
  refine recLe_mul_eq_self_of h fun S hS => ?_
  have hk := recProj_mulVec_ket h S
  have hS0 : S ≠ ∅ := Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp (by omega))
  simp only [hS0, ↓reduceIte] at hk
  ext x p
  have hx := congrFun hk x
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hx
  simp only [Matrix.mul_apply, hg, Pi.smul_apply, smul_eq_mul, Matrix.zero_apply]
  calc ∑ y, ρ.recProj S x y * (ρ.ket y * v p) = (∑ y, ρ.recProj S x y * ρ.ket y) * v p := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ = 0 := by rw [hx, zero_mul]

/-- **A sector-local query adds at most one record.** -/
theorem recLe_mul_jOracle (h : ρ.IsFullProduct) (sec : A → Option ι)
    {O : (ι → σ) → Matrix A A ℂ} (hO : IsSectorLocal sec O) {t : ℕ} {f : JVec ρ.Supp A}
    (hf : ρ.recLe t * f = f) :
    ρ.recLe (t + 1) * jOracle O (fun x : ρ.Supp => (x : ι → σ)) f
      = jOracle O (fun x : ρ.Supp => (x : ι → σ)) f := by
  refine recLe_mul_eq_self_of h fun S' hS' => ?_
  rw [← hf, recLe, Matrix.sum_mul, jOracle_sum, Matrix.mul_sum]
  refine Finset.sum_eq_zero fun S hS => ?_
  have hSt : S.card ≤ t := (Finset.mem_filter.mp hS).2
  rw [jOracle_eq_sum_secPart sec, Matrix.mul_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  obtain ⟨b, -⟩ := (inferInstance : Nonempty ρ.Supp)
  rcases k with _ | i
  · classical
    have hw : jOracle (secPart sec O none) (fun x : ρ.Supp => (x : ι → σ)) (ρ.recProj S * f)
        = wsOp (secPart sec O none b) (ρ.recProj S * f) := by
      funext x
      simp only [jOracle, wsOp]
      rw [secPart_none hO]
    have hne : S' ≠ S := by
      rintro rfl
      omega
    rw [hw, mul_wsOp, ← Matrix.mul_assoc, recProj_mul_recProj h hne, Matrix.zero_mul]
    funext x
    exact Matrix.mulVec_zero _
  · have hM : secPart sec O (some i)
        = fun a => secPart sec O (some i) (Function.update b i (a i)) :=
      funext fun a => secPart_some hO i a b
    rw [hM]
    refine recProj_mul_jOracle_mul_recProj h
      (fun c => secPart sec O (some i) (Function.update b i c)) (fun hsub => ?_) f
    have hsub' : S' ⊆ insert i S := by
      intro x hx
      by_cases hxS : x ∈ S
      · exact Finset.mem_insert_of_mem hxS
      · have hx' := hsub (Finset.mem_symmDiff.mpr (Or.inl ⟨hx, hxS⟩))
        rw [Finset.mem_singleton] at hx'
        rw [hx']
        exact Finset.mem_insert_self i S
    have := (Finset.card_le_card hsub').trans (Finset.card_insert_le i S)
    omega

/-- **The record-count bound** [Bel26, Proposition 3.2], value oracle: after `t` queries the joint
state has at most `t` records. -/
theorem recLe_mul_jointState (h : ρ.IsFullProduct) {O W : Type} [Fintype W] [DecidableEq W]
    (A : QAlg ι σ O W) (t : ℕ) :
    ρ.recLe t * ρ.jointState id A t = ρ.jointState id A t := by
  induction t with
  | zero =>
    exact recLe_mul_ket_smul h 0 _ _ fun x => by rw [ρ.jointState_zero id A]
  | succ t ih =>
    rw [jointState_succ, mul_wsOp]
    congr 1
    exact recLe_mul_jOracle h (fun p => p.1) isSectorLocal_oracleMat ih

/-- **The record-count bound**, XOR oracle. -/
theorem recLe_mul_jointXorState {ρ : FinDist (ι → Bool)} (h : ρ.IsFullProduct) {O W : Type}
    [Fintype W] [DecidableEq W] (A : QAlg ι Bool O W) (t : ℕ) :
    ρ.recLe t * ρ.jointXorState id A t = ρ.jointXorState id A t := by
  induction t with
  | zero =>
    exact recLe_mul_ket_smul h 0 _ _ fun x => by rw [ρ.jointXorState_zero id A]
  | succ t ih =>
    rw [jointXorState_succ, mul_wsOp]
    congr 1
    exact recLe_mul_jOracle h (fun p => p.1) isSectorLocal_xorOracleMat ih

end FinDist

end QuantumQueryComplexity
