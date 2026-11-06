import QuantumQueryComplexity.Quantum.Records.HiddenTransfer
import QuantumQueryComplexity.Quantum.Transfer.Lemma

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Knowledge and query gain

Belovs splits the transferred state `ΥΨ` into a part that "knows" the answer and a part that does
not [Bel26, Sections 3.7, 3.9]. The split is by records (`Product.lean`): a hidden type `μ` comes
with a **knowledge system** `L_μ`, an upward-closed family of sets of coordinates not containing
`∅` (`IsKnowledgeSystem`, [Bel26, Definition 3.16]), and the **knowledge operator**

    Υ⁺ = Υ ∘ (∑_{S ∈ L_μ} P_S)   on the rows of type μ    (`knowOp`, [Bel26, Definition 3.17]).

With `Υ⁻` the operator of the complementary family, `Υ⁺ + Υ⁻ = Υ` (`knowOp_add_knowOp_compl`).
Knowledge `‖Υ⁺Ψ‖` starts at zero (`knowOp_mul_ket_smul`) and is unchanged by the algorithm's own
unitaries (they act on the workspace).

The **boundary** `∂ᵢL_μ` consists of the sets outside `L_μ` that enter it when `i` is added
[Bel26, Definition 3.20], and the **query-gain operator** `Ψ^∂` (`gainOp`) applies the knowledge
operator of `∂ᵢL` on the sector of queries to `i`. For a sector-local oracle `O`
(`RecordCount.lean`) the commutators are equal [Bel26, Lemma 3.21, Corollary 3.22]:

    Υ⁺ O − O Υ⁺ = O Ψ^∂ − Ψ^∂ O    (`knowOp_jOracle_sub`).

The query-gain bound [Bel26, Corollary 3.23] and the knowledge bound [Bel26, Corollary 3.24]
follow by the triangle inequality, in the value and XOR models; the refined squared bound
[Bel26, Lemma 6.13] holds for every coordinate projection `Ξ` of the problem side that fixes the
gain operator (`jNormSq_knowOp_jOracle_sub_le`).

All of this holds for every product reference distribution with full-support marginals; [Bel26]
uses the uniform distribution on `Z_qⁿ`, whose records are the Fourier supports.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {Ω M : Type} [Fintype Ω] [DecidableEq Ω]

namespace FinDist

/-- **A knowledge system** [Bel26, Definition 3.16]: for each type, a family of sets of
coordinates that does not contain `∅` and is upward closed. -/
def IsKnowledgeSystem (L : M → Set (Finset ι)) : Prop :=
  (∀ μ, ∅ ∉ L μ) ∧ ∀ μ S T, S ⊆ T → S ∈ L μ → T ∈ L μ

/-- The projection onto the records whose set lies in `F`, `∑_{S ∈ F} P_S`. -/
noncomputable def recIn (ρ : FinDist (ι → σ)) (F : Set (Finset ι)) :
    Matrix ρ.Supp ρ.Supp ℂ := by
  classical exact ∑ S ∈ Finset.univ.filter (· ∈ F), ρ.recProj S

/-- **The (pseudo-)knowledge operator** [Bel26, Definition 3.17]: on the rows of type `μ`, the
transfer operator restricted to the records in `L μ`. -/
noncomputable def knowOp (ρ : FinDist (ι → σ)) (ν : FinDist Ω) (read : Ω → ι → σ)
    (type : Ω → M) (L : M → Set (Finset ι)) : Matrix ν.Supp ρ.Supp ℂ :=
  fun ω x => (xferOp ρ ν read * ρ.recIn (L (type ω))) ω x

/-- **The boundary** `∂ᵢL` [Bel26, Definition 3.20]: the sets outside `L μ` that enter `L μ` when
`i` is added. -/
def boundary (L : M → Set (Finset ι)) (i : ι) : M → Set (Finset ι) :=
  fun μ => {S | S ∉ L μ ∧ insert i S ∈ L μ}

/-- **The query-gain operator** `Ψ^∂` [Bel26, Definition 3.20]: on the columns whose index
register holds `i`, the knowledge operator of `∂ᵢL`; zero on the idle sector. -/
noncomputable def gainOp (ρ : FinDist (ι → σ)) (ν : FinDist Ω) (read : Ω → ι → σ)
    (type : Ω → M) (L : M → Set (Finset ι)) {W : Type} (f : JVec ρ.Supp (QBasis ι σ W)) :
    JVec ν.Supp (QBasis ι σ W) :=
  fun ω p => match p.1 with
    | none => 0
    | some i => ∑ x, knowOp ρ ν read type (boundary L i) ω x * f x p

variable {ρ : FinDist (ι → σ)} {ν : FinDist Ω} {read : Ω → ι → σ} {type : Ω → M}
  {L : M → Set (Finset ι)}

/-! ## Projections onto families of records -/

/-- The projections of two disjoint families add up to the projection of their union. -/
private lemma recIn_add_recIn {F G E : Set (Finset ι)} (hE : ∀ S, S ∈ E ↔ S ∈ F ∨ S ∈ G)
    (hFG : ∀ S, S ∈ F → S ∉ G) : ρ.recIn F + ρ.recIn G = ρ.recIn E := by
  classical
  simp only [recIn, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hF : S ∈ F
  · simp [hF, hFG S hF, (hE S).2 (Or.inl hF)]
  · by_cases hG : S ∈ G <;> simp [hF, hG, hE S]

/-- The projection onto all records is the identity. -/
private lemma recIn_univ (h : ρ.IsFullProduct) : ρ.recIn (Set.univ : Set (Finset ι)) = 1 := by
  classical
  simp only [recIn, Set.mem_univ, Finset.filter_true_of_mem (fun _ _ => trivial)]
  exact sum_recProj h

/-- A row of `Υ⁺ g` is the same row of `Υ (Π_{L μ} g)`, `μ` the type of the row. -/
private lemma knowOp_mul_row {A : Type} [Fintype A] (g : JVec ρ.Supp A) (ω : ν.Supp) :
    (knowOp ρ ν read type L * g) ω = (xferOp ρ ν read * (ρ.recIn (L (type ω)) * g)) ω := by
  funext p
  rw [← Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
  rfl

/-- A record projection with a nonempty set kills the initial joint state `|ρ⟩ ⊗ v`. -/
private lemma recProj_mul_ket_smul (h : ρ.IsFullProduct) {A : Type} [Fintype A] {S : Finset ι}
    (hS : S ≠ ∅) (v : A → ℂ) (g : JVec ρ.Supp A) (hg : ∀ x, g x = ρ.ket x • v) :
    ρ.recProj S * g = 0 := by
  have hk := recProj_mulVec_ket h S
  simp only [hS, ↓reduceIte] at hk
  ext x p
  have hx := congrFun hk x
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hx
  simp only [Matrix.mul_apply, hg, Pi.smul_apply, smul_eq_mul, Matrix.zero_apply]
  calc ∑ y, ρ.recProj S x y * (ρ.ket y * v p) = (∑ y, ρ.recProj S x y * ρ.ket y) * v p := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ = 0 := by rw [hx, zero_mul]

/-- A family of records not containing `∅` kills the initial joint state `|ρ⟩ ⊗ v`. -/
private lemma recIn_mul_ket_smul (h : ρ.IsFullProduct) {A : Type} [Fintype A]
    {F : Set (Finset ι)} (hF : ∅ ∉ F) (v : A → ℂ) (g : JVec ρ.Supp A)
    (hg : ∀ x, g x = ρ.ket x • v) : ρ.recIn F * g = 0 := by
  classical
  simp only [recIn, Matrix.sum_mul]
  refine Finset.sum_eq_zero fun S hS => recProj_mul_ket_smul h (fun h0 => hF ?_) v g hg
  rw [← h0]
  exact (Finset.mem_filter.mp hS).2

/-- **`Υ⁺ + Υ⁻ = Υ`** [Bel26, (3.42)]. -/
theorem knowOp_add_knowOp_compl (h : ρ.IsFullProduct) :
    knowOp ρ ν read type L + knowOp ρ ν read type (fun μ => (L μ)ᶜ) = xferOp ρ ν read := by
  ext ω x
  simp only [Matrix.add_apply, knowOp]
  rw [← Matrix.add_apply, ← Matrix.mul_add,
    recIn_add_recIn (F := L (type ω)) (G := (L (type ω))ᶜ) (E := Set.univ) (fun S => by simp [em])
      (fun _ hS hc => hc hS), recIn_univ h, Matrix.mul_one]

/-- **No knowledge at the start** [Bel26, Proposition 3.19(a)]: `Υ⁺(|ρ⟩ ⊗ v) = 0`. -/
theorem knowOp_mul_ket_smul (h : ρ.IsFullProduct) (hL : IsKnowledgeSystem L) {A : Type}
    [Fintype A] (v : A → ℂ) (g : JVec ρ.Supp A) (hg : ∀ x, g x = ρ.ket x • v) :
    knowOp ρ ν read type L * g = 0 := by
  ext ω p
  rw [knowOp_mul_row, recIn_mul_ket_smul h (hL.1 _) v g hg, Matrix.mul_zero]

/-! ## Query locality for families of records -/

/-- The joint oracle as an additive map of joint vectors. -/
private def jOracleAddHom {X A : Type} [Fintype A] (O : (ι → σ) → Matrix A A ℂ)
    (rd : X → ι → σ) : JVec X A →+ JVec X A :=
  AddMonoidHom.mk' (jOracle O rd) fun g g' => by
    funext x
    exact Matrix.mulVec_add _ (g x) (g' x)

/-- The joint oracle is additive over finite sums. -/
private lemma jOracle_finsetSum {X A κ : Type} [Fintype A] (O : (ι → σ) → Matrix A A ℂ)
    (rd : X → ι → σ) (s : Finset κ) (g : κ → JVec X A) :
    jOracle O rd (∑ k ∈ s, g k) = ∑ k ∈ s, jOracle O rd (g k) :=
  map_sum (jOracleAddHom O rd) g s

/-- Every joint vector is the sum of its record components. -/
private lemma sum_recProj_mul (h : ρ.IsFullProduct) {A : Type} [Fintype A] (g : JVec ρ.Supp A) :
    ∑ S, ρ.recProj S * g = g := by
  rw [← Matrix.sum_mul, sum_recProj h, Matrix.one_mul]

/-- A finite family of records that does not separate `S` from `S △ {i}` gives a projection
commuting with every operator reading only `xᵢ`. -/
private lemma sum_recProj_mul_jOracle (h : ρ.IsFullProduct) {A : Type} [Fintype A] {i : ι}
    (Mi : σ → Matrix A A ℂ) (s : Finset (Finset ι))
    (hs : ∀ S S' : Finset ι, symmDiff S' S ⊆ {i} → (S' ∈ s ↔ S ∈ s)) (g : JVec ρ.Supp A) :
    (∑ S ∈ s, ρ.recProj S) * jOracle (fun a => Mi (a i)) (fun x : ρ.Supp => (x : ι → σ)) g
      = jOracle (fun a => Mi (a i)) (fun x : ρ.Supp => (x : ι → σ))
          ((∑ S ∈ s, ρ.recProj S) * g) := by
  set N := jOracle (fun a => Mi (a i)) (fun x : ρ.Supp => (x : ι → σ)) with hN
  have hT : ∀ S S', (S' ∈ s ↔ S ∈ s) ∨ ρ.recProj S' * N (ρ.recProj S * g) = 0 := by
    intro S S'
    by_cases hsub : symmDiff S' S ⊆ {i}
    · exact Or.inl (hs S S' hsub)
    · exact Or.inr (recProj_mul_jOracle_mul_recProj h Mi hsub g)
  have hL : (∑ S' ∈ s, ρ.recProj S') * N g
      = ∑ S' ∈ s, ∑ S ∈ s, ρ.recProj S' * N (ρ.recProj S * g) := by
    rw [Matrix.sum_mul]
    refine Finset.sum_congr rfl fun S' hS' => ?_
    conv_lhs => rw [← sum_recProj_mul h g, hN, jOracle_finsetSum, Matrix.mul_sum]
    refine (Finset.sum_subset (Finset.subset_univ s) fun S _ hS => ?_).symm
    rcases hT S S' with hiff | h0
    · exact absurd (hiff.mp hS') hS
    · exact h0
  have hR : N ((∑ S ∈ s, ρ.recProj S) * g)
      = ∑ S ∈ s, ∑ S' ∈ s, ρ.recProj S' * N (ρ.recProj S * g) := by
    rw [Matrix.sum_mul, hN, jOracle_finsetSum, ← hN]
    refine Finset.sum_congr rfl fun S hS => ?_
    conv_lhs => rw [← sum_recProj_mul h (N (ρ.recProj S * g))]
    refine (Finset.sum_subset (Finset.subset_univ s) fun S' _ hS' => ?_).symm
    rcases hT S S' with hiff | h0
    · exact absurd (hiff.mpr hS) hS'
    · exact h0
  rw [hL, hR, Finset.sum_comm]

/-- Sets differing at most at `i` have the same insertion of `i`. -/
private lemma insert_eq_of_symmDiff_subset {i : ι} {S S' : Finset ι} (h : symmDiff S' S ⊆ {i}) :
    insert i S' = insert i S := by
  ext j
  simp only [Finset.mem_insert]
  by_cases hj : j = i
  · simp [hj]
  · have hj' : j ∉ symmDiff S' S := fun hm => hj (Finset.mem_singleton.mp (h hm))
    rw [Finset.mem_symmDiff] at hj'
    tauto

/-- **The query identity on the input side** [Bel26, Lemma 3.21]: for an operator `N` reading only
`xᵢ` and an upward-closed family `F`, `Π_F N − N Π_F = N Π_{∂ᵢF} − Π_{∂ᵢF} N`. -/
private lemma recIn_jOracle_sub (h : ρ.IsFullProduct) (μ : M)
    (hF : ∀ S T, S ⊆ T → S ∈ L μ → T ∈ L μ) {A : Type} [Fintype A] {i : ι}
    (Mi : σ → Matrix A A ℂ) (g : JVec ρ.Supp A) :
    ρ.recIn (L μ) * jOracle (fun a => Mi (a i)) (fun x : ρ.Supp => (x : ι → σ)) g
        - jOracle (fun a => Mi (a i)) (fun x : ρ.Supp => (x : ι → σ)) (ρ.recIn (L μ) * g)
      = jOracle (fun a => Mi (a i)) (fun x : ρ.Supp => (x : ι → σ))
          (ρ.recIn (boundary L i μ) * g)
        - ρ.recIn (boundary L i μ) * jOracle (fun a => Mi (a i))
            (fun x : ρ.Supp => (x : ι → σ)) g := by
  classical
  set N := jOracle (fun a => Mi (a i)) (fun x : ρ.Supp => (x : ι → σ)) with hN
  -- `F ∪ ∂ᵢF = {S | insert i S ∈ F}` does not separate `S` from `S △ {i}`.
  have hsplit : ρ.recIn (L μ) + ρ.recIn (boundary L i μ) = ρ.recIn {S | insert i S ∈ L μ} := by
    refine recIn_add_recIn (fun S => ⟨fun hS => ?_, fun hS => ?_⟩) fun S hS hb => hb.1 hS
    · by_cases hSF : S ∈ L μ
      · exact Or.inl hSF
      · exact Or.inr ⟨hSF, hS⟩
    · rcases hS with hS | hS
      · exact hF S _ (Finset.subset_insert i S) hS
      · exact hS.2
  have hcomm : ρ.recIn {S | insert i S ∈ L μ} * N g = N (ρ.recIn {S | insert i S ∈ L μ} * g) := by
    rw [recIn, hN]
    refine sum_recProj_mul_jOracle h Mi _ (fun S S' hss => ?_) g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    rw [insert_eq_of_symmDiff_subset hss]
  have hF' : ρ.recIn (L μ) = ρ.recIn {S | insert i S ∈ L μ} - ρ.recIn (boundary L i μ) :=
    eq_sub_of_add_eq hsplit
  rw [hF', Matrix.sub_mul, Matrix.sub_mul, hN, jOracle_sub, ← hN, hcomm]
  abel

/-! ## Splitting a sector-local oracle by sectors -/

section Sectors

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The columns of an oracle family in index-register sector `k`, the other columns set to
zero. -/
private def secQ (O : (ι → σ) → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (k : Option ι) :
    (ι → σ) → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ :=
  fun a p q => if q.1 = k then O a p q else 0

/-- A joint oracle is the sum of its sector parts. -/
private lemma jOracle_eq_sum_secQ {X : Type} (O : (ι → σ) → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (rd : X → ι → σ) (g : JVec X (QBasis ι σ W)) :
    jOracle O rd g = ∑ k, jOracle (secQ O k) rd g := by
  ext x p
  simp only [jOracle, Matrix.sum_apply, Matrix.mulVec, dotProduct, secQ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [ite_mul]

/-- The idle-sector part of a sector-local family does not depend on the input. -/
private lemma secQ_none {O : (ι → σ) → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
    (hO : IsSectorLocal (fun p : QBasis ι σ W => p.1) O) (a b : ι → σ) :
    secQ O none a = secQ O none b := by
  ext p q
  simp only [secQ]
  split_ifs with hq
  · exact hO.2 a b p q fun i hi => absurd (hq.symm.trans hi) (by simp)
  · rfl

/-- The sector-`i` part of a sector-local family depends on the input only through `aᵢ`. -/
private lemma secQ_some {O : (ι → σ) → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
    (hO : IsSectorLocal (fun p : QBasis ι σ W => p.1) O) (i : ι) (a b : ι → σ) :
    secQ O (some i) a = secQ O (some i) (Function.update b i (a i)) := by
  ext p q
  simp only [secQ]
  split_ifs with hq
  · refine hO.2 _ _ p q fun i' hi' => ?_
    obtain rfl : i = i' := Option.some_injective _ (hq.symm.trans hi')
    simp
  · rfl

/-- The sector-`k` part of a joint oracle only sees the columns in sector `k`. -/
private lemma jOracle_secQ_congr {X : Type}
    (O : (ι → σ) → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) (k : Option ι) (rd : X → ι → σ)
    {g g' : JVec X (QBasis ι σ W)} (hgg : ∀ x q, q.1 = k → g x q = g' x q) :
    jOracle (secQ O k) rd g = jOracle (secQ O k) rd g' := by
  ext x p
  simp only [jOracle, Matrix.mulVec, dotProduct, secQ]
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs with hq
  · rw [hgg x q hq]
  · simp

/-- The sector-`k` part of a block-diagonal joint oracle lands in sector `k`. -/
private lemma jOracle_secQ_apply_of_ne {X : Type}
    {O : (ι → σ) → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
    (hO : IsSectorLocal (fun p : QBasis ι σ W => p.1) O) (k : Option ι) (rd : X → ι → σ)
    (g : JVec X (QBasis ι σ W)) (x : X) {p : QBasis ι σ W} (hp : p.1 ≠ k) :
    jOracle (secQ O k) rd g x p = 0 := by
  simp only [jOracle, Matrix.mulVec, dotProduct, secQ]
  refine Finset.sum_eq_zero fun q _ => ?_
  split_ifs with hq
  · rw [hO.1 _ p q (fun he => hp (he.trans hq)), zero_mul]
  · rw [zero_mul]

end Sectors

/-- The input-side gain map of a family of record sets `B i`: on the columns whose index register
holds `i`, the projection `Π_{B i}`; zero on the idle sector. -/
private noncomputable def gX (ρ : FinDist (ι → σ)) (B : ι → Set (Finset ι)) {W : Type}
    (f : JVec ρ.Supp (QBasis ι σ W)) : JVec ρ.Supp (QBasis ι σ W) :=
  fun x p => match p.1 with
    | none => 0
    | some i => (ρ.recIn (B i) * f) x p

/-- The gain operator is the transfer of the input-side gain map, row by row. -/
private lemma gainOp_row {W : Type} (f : JVec ρ.Supp (QBasis ι σ W)) (ω : ν.Supp) :
    gainOp ρ ν read type L f ω
      = (xferOp ρ ν read * gX ρ (fun i => boundary L i (type ω)) f) ω := by
  funext p
  rcases p with ⟨_ | i, t, w⟩
  · simp [gainOp, gX, Matrix.mul_apply]
  · change ((xferOp ρ ν read * ρ.recIn (boundary L i (type ω))) * f) ω (some i, t, w)
      = (xferOp ρ ν read * (ρ.recIn (boundary L i (type ω)) * f)) ω (some i, t, w)
    rw [Matrix.mul_assoc]

/-- The input-side gain map is additive over finite sums. -/
private lemma gX_finsetSum {W κ : Type} (B : ι → Set (Finset ι)) (s : Finset κ)
    (g : κ → JVec ρ.Supp (QBasis ι σ W)) : gX ρ B (∑ k ∈ s, g k) = ∑ k ∈ s, gX ρ B (g k) := by
  ext x ⟨_ | i, t, w⟩
  · simp [gX, Matrix.sum_apply]
  · simp [gX, Matrix.mul_sum, Matrix.sum_apply]

/-- The input-side gain map vanishes on joint vectors in the idle sector. -/
private lemma gX_of_none {W : Type} (B : ι → Set (Finset ι)) {g : JVec ρ.Supp (QBasis ι σ W)}
    (hg : ∀ x q, q.1 ≠ none → g x q = 0) : gX ρ B g = 0 := by
  ext x ⟨_ | i, t, w⟩
  · rfl
  · change ∑ y, ρ.recIn (B i) x y * g y (some i, t, w) = 0
    exact Finset.sum_eq_zero fun y _ => by rw [hg y _ (by simp), mul_zero]

/-- On joint vectors in sector `i`, the input-side gain map is `Π_{B i}`. -/
private lemma gX_of_some {W : Type} (B : ι → Set (Finset ι)) {i : ι}
    {g : JVec ρ.Supp (QBasis ι σ W)} (hg : ∀ x q, q.1 ≠ some i → g x q = 0) :
    gX ρ B g = ρ.recIn (B i) * g := by
  ext x ⟨_ | j, t, w⟩
  · change 0 = ∑ y, ρ.recIn (B i) x y * g y (none, t, w)
    exact (Finset.sum_eq_zero fun y _ => by rw [hg y _ (by simp), mul_zero]).symm
  · by_cases hji : j = i
    · subst hji
      rfl
    · change ∑ y, ρ.recIn (B j) x y * g y (some j, t, w)
        = ∑ y, ρ.recIn (B i) x y * g y (some j, t, w)
      rw [Finset.sum_eq_zero fun y _ => by rw [hg y _ (by simpa using hji), mul_zero],
        Finset.sum_eq_zero fun y _ => by rw [hg y _ (by simpa using hji), mul_zero]]

/-- **The query identity on the input side** for a sector-local oracle [Bel26, Corollary 3.22]. -/
private lemma recIn_jOracle_sub_gX (h : ρ.IsFullProduct) (hL : IsKnowledgeSystem L) (μ : M)
    {W : Type} [Fintype W] [DecidableEq W]
    {O : (ι → σ) → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
    (hO : IsSectorLocal (fun p : QBasis ι σ W => p.1) O) (f : JVec ρ.Supp (QBasis ι σ W)) :
    ρ.recIn (L μ) * jOracle O (fun x : ρ.Supp => (x : ι → σ)) f
        - jOracle O (fun x : ρ.Supp => (x : ι → σ)) (ρ.recIn (L μ) * f)
      = jOracle O (fun x : ρ.Supp => (x : ι → σ)) (gX ρ (fun i => boundary L i μ) f)
        - gX ρ (fun i => boundary L i μ) (jOracle O (fun x : ρ.Supp => (x : ι → σ)) f) := by
  obtain ⟨b⟩ := (inferInstance : Nonempty ρ.Supp)
  simp only [jOracle_eq_sum_secQ O (fun x : ρ.Supp => (x : ι → σ))]
  rw [Matrix.mul_sum, gX_finsetSum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases k with _ | i
  · have hw : ∀ g : JVec ρ.Supp (QBasis ι σ W),
        jOracle (secQ O none) (fun x : ρ.Supp => (x : ι → σ)) g = wsOp (secQ O none b.1) g := by
      intro g
      funext x
      simp only [jOracle, wsOp]
      rw [secQ_none hO]
    have h1 : jOracle (secQ O none) (fun x : ρ.Supp => (x : ι → σ))
        (gX ρ (fun i => boundary L i μ) f) = 0 := by
      rw [jOracle_secQ_congr O none _ (g' := 0) fun x q hq => by
        rcases q with ⟨_ | j, t, w⟩
        · rfl
        · simp at hq]
      funext x
      exact Matrix.mulVec_zero _
    have h2 : gX ρ (fun i => boundary L i μ)
        (jOracle (secQ O none) (fun x : ρ.Supp => (x : ι → σ)) f) = 0 :=
      gX_of_none _ fun x q hq => jOracle_secQ_apply_of_ne hO none _ f x hq
    rw [h1, h2, hw, hw, mul_wsOp, sub_self, sub_self]
  · have h1 : jOracle (secQ O (some i)) (fun x : ρ.Supp => (x : ι → σ))
        (gX ρ (fun i => boundary L i μ) f)
          = jOracle (secQ O (some i)) (fun x : ρ.Supp => (x : ι → σ))
              (ρ.recIn (boundary L i μ) * f) := by
      refine jOracle_secQ_congr O (some i) _ fun x q hq => ?_
      rcases q with ⟨_ | j, t, w⟩
      · simp at hq
      · obtain rfl : j = i := Option.some_injective _ hq
        rfl
    have h2 : gX ρ (fun i => boundary L i μ)
        (jOracle (secQ O (some i)) (fun x : ρ.Supp => (x : ι → σ)) f)
          = ρ.recIn (boundary L i μ)
              * jOracle (secQ O (some i)) (fun x : ρ.Supp => (x : ι → σ)) f :=
      gX_of_some _ fun x q hq => jOracle_secQ_apply_of_ne hO (some i) _ f x hq
    have hM : secQ O (some i) = fun a => secQ O (some i) (Function.update b.1 i (a i)) :=
      funext fun a => secQ_some hO i a b.1
    rw [h1, h2, hM]
    exact recIn_jOracle_sub h μ (hL.2 μ) (fun c => secQ O (some i) (Function.update b.1 i c)) f

/-- **The query identity** [Bel26, Lemma 3.21, Corollary 3.22]: for a sector-local oracle,
`Υ⁺ O − O Υ⁺ = O Ψ^∂ − Ψ^∂ O`. -/
theorem knowOp_jOracle_sub (h : ρ.IsFullProduct) (hL : IsKnowledgeSystem L) {W : Type}
    [Fintype W] [DecidableEq W] {O : (ι → σ) → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
    (hO : IsSectorLocal (fun p : QBasis ι σ W => p.1) O) (f : JVec ρ.Supp (QBasis ι σ W)) :
    knowOp ρ ν read type L * jOracle O (fun x : ρ.Supp => (x : ι → σ)) f
        - jOracle O (fun ω : ν.Supp => read ω) (knowOp ρ ν read type L * f)
      = jOracle O (fun ω : ν.Supp => read ω) (gainOp ρ ν read type L f)
        - gainOp ρ ν read type L (jOracle O (fun x : ρ.Supp => (x : ι → σ)) f) := by
  ext ω p
  have e2 : jOracle O (fun ω : ν.Supp => read ω) (knowOp ρ ν read type L * f) ω
      = (xferOp ρ ν read
          * jOracle O (fun x : ρ.Supp => (x : ι → σ)) (ρ.recIn (L (type ω)) * f)) ω := by
    rw [xferOp_mul_jOracle]
    simp only [jOracle, knowOp_mul_row]
  have e3 : jOracle O (fun ω : ν.Supp => read ω) (gainOp ρ ν read type L f) ω
      = (xferOp ρ ν read * jOracle O (fun x : ρ.Supp => (x : ι → σ))
          (gX ρ (fun i => boundary L i (type ω)) f)) ω := by
    rw [xferOp_mul_jOracle]
    simp only [jOracle, gainOp_row]
  rw [Matrix.sub_apply, Matrix.sub_apply, knowOp_mul_row, e2, e3, gainOp_row, ← Matrix.sub_apply,
    ← Matrix.sub_apply, ← Matrix.mul_sub, ← Matrix.mul_sub, recIn_jOracle_sub_gX h hL _ hO f]

/-- The commutator `Υ⁺ O f − O Υ⁺ f` is at most the two query gains. -/
private lemma jNorm_knowOp_jOracle_sub_jOracle_le (h : ρ.IsFullProduct)
    (hL : IsKnowledgeSystem L) {W : Type} [Fintype W] [DecidableEq W]
    {O : (ι → σ) → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
    (hO : IsSectorLocal (fun p : QBasis ι σ W => p.1) O)
    (hU : ∀ a, O a ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) (f : JVec ρ.Supp (QBasis ι σ W)) :
    jNorm (knowOp ρ ν read type L * jOracle O (fun x : ρ.Supp => (x : ι → σ)) f
        - jOracle O (fun ω : ν.Supp => read ω) (knowOp ρ ν read type L * f))
      ≤ jNorm (gainOp ρ ν read type L f)
        + jNorm (gainOp ρ ν read type L (jOracle O (fun x : ρ.Supp => (x : ι → σ)) f)) := by
  rw [knowOp_jOracle_sub h hL hO f, sub_eq_add_neg]
  refine (jNorm_add_le _ _).trans ?_
  rw [jNorm_neg, jNorm_jOracle_of_mem_unitaryGroup hU]

/-- **The query-gain bound for one query** [Bel26, Corollary 3.23]: for a unitary sector-local
oracle, knowledge grows by at most `‖Ψ^∂ f‖ + ‖Ψ^∂ O f‖`. -/
theorem jNorm_knowOp_jOracle_sub_le (h : ρ.IsFullProduct) (hL : IsKnowledgeSystem L)
    {W : Type} [Fintype W] [DecidableEq W]
    {O : (ι → σ) → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
    (hO : IsSectorLocal (fun p : QBasis ι σ W => p.1) O)
    (hU : ∀ a, O a ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ) (f : JVec ρ.Supp (QBasis ι σ W)) :
    jNorm (knowOp ρ ν read type L * jOracle O (fun x : ρ.Supp => (x : ι → σ)) f)
        - jNorm (knowOp ρ ν read type L * f)
      ≤ jNorm (gainOp ρ ν read type L f)
        + jNorm (gainOp ρ ν read type L (jOracle O (fun x : ρ.Supp => (x : ι → σ)) f)) := by
  have h1 := jNorm_add_le (knowOp ρ ν read type L * jOracle O (fun x : ρ.Supp => (x : ι → σ)) f
      - jOracle O (fun ω : ν.Supp => read ω) (knowOp ρ ν read type L * f))
    (jOracle O (fun ω : ν.Supp => read ω) (knowOp ρ ν read type L * f))
  rw [sub_add_cancel, jNorm_jOracle_of_mem_unitaryGroup hU] at h1
  linarith [jNorm_knowOp_jOracle_sub_jOracle_le (ν := ν) (read := read) (type := type) h hL hO hU f]

/-- **The knowledge bound** [Bel26, Corollary 3.24], value oracle: after `t` queries the knowledge
is at most the sum of the query gains. -/
theorem jNorm_knowOp_jointState_le (h : ρ.IsFullProduct) (hL : IsKnowledgeSystem L)
    {O W : Type} [Fintype W] [DecidableEq W] (A : QAlg ι σ O W) (t : ℕ) :
    jNorm (knowOp ρ ν read type L * ρ.jointState id A t)
      ≤ ∑ j ∈ Finset.range t,
          (jNorm (gainOp ρ ν read type L (ρ.jointState id A j))
            + jNorm (gainOp ρ ν read type L
                (jOracle oracleMat (fun x : ρ.Supp => (x : ι → σ)) (ρ.jointState id A j)))) := by
  induction t with
  | zero =>
    rw [knowOp_mul_ket_smul h hL (A.step 0 *ᵥ A.init) _ fun x => by rw [ρ.jointState_zero id A]]
    simp
  | succ t ih =>
    have hs : ρ.jointState id A (t + 1) = wsOp (A.step (t + 1))
        (jOracle oracleMat (fun x : ρ.Supp => (x : ι → σ)) (ρ.jointState id A t)) :=
      jointState_succ ρ id A t
    rw [hs, mul_wsOp, jNorm_wsOp_of_mem_unitaryGroup (A.step_unitary _), Finset.sum_range_succ]
    linarith [jNorm_knowOp_jOracle_sub_le (ν := ν) (read := read) (type := type) h hL
      isSectorLocal_oracleMat oracleMat_mem_unitaryGroup (ρ.jointState id A t)]

/-- **The knowledge bound**, XOR oracle. -/
theorem jNorm_knowOp_jointXorState_le {ρ : FinDist (ι → Bool)} (h : ρ.IsFullProduct)
    {read : Ω → ι → Bool} (hL : IsKnowledgeSystem L) {O W : Type} [Fintype W] [DecidableEq W]
    (A : QAlg ι Bool O W) (t : ℕ) :
    jNorm (knowOp ρ ν read type L * ρ.jointXorState id A t)
      ≤ ∑ j ∈ Finset.range t,
          (jNorm (gainOp ρ ν read type L (ρ.jointXorState id A j))
            + jNorm (gainOp ρ ν read type L
                (jOracle xorOracleMat (fun x : ρ.Supp => (x : ι → Bool))
                  (ρ.jointXorState id A j)))) := by
  induction t with
  | zero =>
    rw [knowOp_mul_ket_smul h hL (A.step 0 *ᵥ A.init) _ fun x => by
      rw [ρ.jointXorState_zero id A]]
    simp
  | succ t ih =>
    have hs : ρ.jointXorState id A (t + 1) = wsOp (A.step (t + 1))
        (jOracle xorOracleMat (fun x : ρ.Supp => (x : ι → Bool)) (ρ.jointXorState id A t)) :=
      jointXorState_succ ρ id A t
    rw [hs, mul_wsOp, jNorm_wsOp_of_mem_unitaryGroup (A.step_unitary _), Finset.sum_range_succ]
    linarith [jNorm_knowOp_jOracle_sub_le (ν := ν) (read := read) (type := type) h hL
      isSectorLocal_xorOracleMat xorOracleMat_mem_unitaryGroup (ρ.jointXorState id A t)]

/-- The coordinate projection `Ξ` of the problem side onto the pairs (label, index register) in
`ξ` [Bel26, Definition 6.11]. -/
def xiMask (ξ : ν.Supp → Option ι → Prop) [∀ ω, DecidablePred (ξ ω)] {W : Type}
    (g : JVec ν.Supp (QBasis ι σ W)) : JVec ν.Supp (QBasis ι σ W) :=
  fun ω p => if ξ ω p.1 then g ω p else 0

/-- `Ξ` commutes with differences. -/
private lemma xiMask_sub (ξ : ν.Supp → Option ι → Prop) [∀ ω, DecidablePred (ξ ω)] {W : Type}
    (g g' : JVec ν.Supp (QBasis ι σ W)) : xiMask ξ (g - g') = xiMask ξ g - xiMask ξ g' := by
  ext ω p
  simp only [xiMask, Matrix.sub_apply]
  split_ifs <;> simp

/-- `Ξ` commutes with a block-diagonal joint oracle. -/
private lemma xiMask_jOracle {W : Type} [Fintype W] [DecidableEq W]
    {O : (ι → σ) → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
    (hO : IsSectorLocal (fun p : QBasis ι σ W => p.1) O) (ξ : ν.Supp → Option ι → Prop)
    [∀ ω, DecidablePred (ξ ω)] (rd : ν.Supp → ι → σ) (g : JVec ν.Supp (QBasis ι σ W)) :
    xiMask ξ (jOracle O rd g) = jOracle O rd (xiMask ξ g) := by
  ext ω p
  simp only [xiMask, jOracle, Matrix.mulVec, dotProduct]
  split_ifs with hp
  · refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs with hq
    · rfl
    · rw [hO.1 _ p q (fun he => hq (by simp only at he; rwa [← he])), zero_mul, zero_mul]
  · refine (Finset.sum_eq_zero fun q _ => ?_).symm
    split_ifs with hq
    · rw [hO.1 _ p q (fun he => hp (by simp only at he; rwa [he])), zero_mul]
    · rw [mul_zero]

/-- `Ξ` fixes the gain operator when there is no gain outside `ξ`. -/
private lemma xiMask_gainOp (ξ : ν.Supp → Option ι → Prop) [∀ ω, DecidablePred (ξ ω)]
    (hξ : ∀ ω i x, ¬ ξ ω (some i) → knowOp ρ ν read type (boundary L i) ω x = 0) {W : Type}
    (g : JVec ρ.Supp (QBasis ι σ W)) :
    xiMask ξ (gainOp ρ ν read type L g) = gainOp ρ ν read type L g := by
  ext ω ⟨_ | i, t, w⟩
  · simp [xiMask, gainOp]
  · simp only [xiMask, gainOp]
    split_ifs with hp
    · rfl
    · exact (Finset.sum_eq_zero fun x _ => by rw [hξ ω i x hp, zero_mul]).symm

/-- `Ξ` splits the squared norm: `‖g‖² = ‖Ξg‖² + ‖g − Ξg‖²`. -/
private lemma jNormSq_eq_xiMask_add (ξ : ν.Supp → Option ι → Prop) [∀ ω, DecidablePred (ξ ω)]
    {W : Type} [Fintype W] (g : JVec ν.Supp (QBasis ι σ W)) :
    jNormSq g = jNormSq (xiMask ξ g) + jNormSq (g - xiMask ξ g) := by
  simp only [jNormSq, qNormSq_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun p _ => ?_
  simp only [xiMask, Matrix.sub_apply]
  split_ifs <;> simp

/-- If `Ξ` fixes `a − c`, then `‖a‖² − ‖c‖² ≤ 2‖Ξc‖‖a − c‖ + ‖a − c‖²`. -/
private lemma jNormSq_sub_le_of_xiMask (ξ : ν.Supp → Option ι → Prop)
    [∀ ω, DecidablePred (ξ ω)] {W : Type} [Fintype W] (a c : JVec ν.Supp (QBasis ι σ W))
    (hw : xiMask ξ (a - c) = a - c) :
    jNormSq a - jNormSq c ≤ 2 * jNorm (xiMask ξ c) * jNorm (a - c) + jNorm (a - c) ^ 2 := by
  classical
  have hΞa : xiMask ξ a = xiMask ξ c + (a - c) := by
    rw [← hw, xiMask_sub]
    abel
  have hcomp : a - xiMask ξ a = c - xiMask ξ c := by
    rw [hΞa]
    abel
  have hsa := jNormSq_eq_xiMask_add ξ a
  have hsc := jNormSq_eq_xiMask_add ξ c
  rw [hcomp, hΞa] at hsa
  have h1 : jNormSq (xiMask ξ c + (a - c)) ≤ (jNorm (xiMask ξ c) + jNorm (a - c)) ^ 2 := by
    rw [← jNorm_sq]
    exact pow_le_pow_left₀ (jNorm_nonneg _) (jNorm_add_le _ _) 2
  have h2 : jNormSq (xiMask ξ c) = jNorm (xiMask ξ c) ^ 2 := (jNorm_sq _).symm
  nlinarith [h1, h2, hsa, hsc]

/-- **The refined query-gain bound** [Bel26, Lemma 6.13]: for a unitary sector-local oracle and a
coordinate projection `Ξ` that fixes the gain operator (no gain outside `ξ`),

    ‖Υ⁺Of‖² − ‖Υ⁺f‖² ≤ 2‖ΞΥ⁺f‖ (‖Ψ^∂f‖ + ‖Ψ^∂Of‖) + (‖Ψ^∂f‖ + ‖Ψ^∂Of‖)². -/
theorem jNormSq_knowOp_jOracle_sub_le (h : ρ.IsFullProduct) (hL : IsKnowledgeSystem L)
    {W : Type} [Fintype W] [DecidableEq W]
    {O : (ι → σ) → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ}
    (hO : IsSectorLocal (fun p : QBasis ι σ W => p.1) O)
    (hU : ∀ a, O a ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ)
    (ξ : ν.Supp → Option ι → Prop) [∀ ω, DecidablePred (ξ ω)]
    (hξ : ∀ ω i x, ¬ ξ ω (some i) → knowOp ρ ν read type (boundary L i) ω x = 0)
    (f : JVec ρ.Supp (QBasis ι σ W)) :
    jNormSq (knowOp ρ ν read type L * jOracle O (fun x : ρ.Supp => (x : ι → σ)) f)
        - jNormSq (knowOp ρ ν read type L * f)
      ≤ 2 * jNorm (xiMask ξ (knowOp ρ ν read type L * f))
          * (jNorm (gainOp ρ ν read type L f)
            + jNorm (gainOp ρ ν read type L (jOracle O (fun x : ρ.Supp => (x : ι → σ)) f)))
        + (jNorm (gainOp ρ ν read type L f)
            + jNorm (gainOp ρ ν read type L
                (jOracle O (fun x : ρ.Supp => (x : ι → σ)) f))) ^ 2 := by
  have hΞw : xiMask ξ (knowOp ρ ν read type L * jOracle O (fun x : ρ.Supp => (x : ι → σ)) f
        - jOracle O (fun ω : ν.Supp => read ω) (knowOp ρ ν read type L * f))
      = knowOp ρ ν read type L * jOracle O (fun x : ρ.Supp => (x : ι → σ)) f
        - jOracle O (fun ω : ν.Supp => read ω) (knowOp ρ ν read type L * f) := by
    rw [knowOp_jOracle_sub h hL hO f, xiMask_sub, xiMask_jOracle hO, xiMask_gainOp ξ hξ,
      xiMask_gainOp ξ hξ]
  have key := jNormSq_sub_le_of_xiMask ξ _ _ hΞw
  have hcb : jNormSq (jOracle O (fun ω : ν.Supp => read ω) (knowOp ρ ν read type L * f))
      = jNormSq (knowOp ρ ν read type L * f) := by
    rw [← jNorm_sq, ← jNorm_sq, jNorm_jOracle_of_mem_unitaryGroup hU]
  have hΞcb : jNorm (xiMask ξ (jOracle O (fun ω : ν.Supp => read ω)
        (knowOp ρ ν read type L * f))) = jNorm (xiMask ξ (knowOp ρ ν read type L * f)) := by
    rw [xiMask_jOracle hO, jNorm_jOracle_of_mem_unitaryGroup hU]
  rw [hcb, hΞcb] at key
  have hwle := jNorm_knowOp_jOracle_sub_jOracle_le (ν := ν) (read := read) (type := type) h hL hO
    hU f
  have hZ0 := jNorm_nonneg (xiMask ξ (knowOp ρ ν read type L * f))
  have hV0 := jNorm_nonneg (knowOp ρ ν read type L * jOracle O (fun x : ρ.Supp => (x : ι → σ)) f
    - jOracle O (fun ω : ν.Supp => read ω) (knowOp ρ ν read type L * f))
  nlinarith [mul_le_mul_of_nonneg_left hwle hZ0, pow_le_pow_left₀ hV0 hwle 2]

end FinDist

end QuantumQueryComplexity
