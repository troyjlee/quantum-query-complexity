import QuantumQueryComplexity.Quantum.Records.ZqRecords

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Zhandry's compressed oracle and its relation to the records of product distributions

Zhandry's compressed-oracle (recording) technique [Zha19], in the exposition of Hamoudi [Ham25,
Section 4.1], adds an empty symbol `⊥` to each coordinate of the input register. The **database
register** has basis `ι → Option σ`, with `none` the empty symbol (the library's blank-answer
convention). For coordinate `i`, the **recording operator** `Rᵢ` (`FinDist.recOp`) exchanges `|⊥⟩`
with the conditional-mean vector `|√μᵢ⟩ = ∑_a √μᵢ(a) |a⟩` of the coordinate (`FinDist.meanVec`;
the uniform superposition for uniform inputs [Ham25, Definition 36], `√(1−p)|0⟩ + √p|1⟩` for
Bernoulli(`p`) bits [CMSZ21, HM23]) and fixes their orthogonal complement. It is a Hermitian
involution. The **compression** of a joint vector is `C = R ι` (`FinDist.compress`): embed the
input register into the database register (`FinDist.dbEmbed`) and apply `R = ⊗ᵢ Rᵢ`.

**Relation to the records (Layer D).** For a product distribution with full-support marginals,
compression is an isometry that relabels the record decomposition of `Product.lean`: the
projection onto the database strings whose non-`⊥` positions (`dbSupp`) form the set `S` pulls back
to the record projection `P_S` (`FinDist.dbProj_dbSupp_eq_mul_compress`). So the record set of a
database state is its set of non-`⊥` positions, and every statement about records is a statement
about databases (`FinDist.jNormSq_dbProj_compress_mul`). The initial state compresses to the empty
database (`FinDist.compress_mul_vecMulVec_ket`), and after `t` queries the database holds at most
`t` entries [Ham25, Fact 37] (`FinDist.dbProj_card_gt_mul_compress_jointZqState`).

**Progress measures.** The recording oracle `O_rec = R O R` [Ham25, Definition 38]
(`FinDist.recOracle`) acts on the database register, where the oracle reads `⊥` as a fixed
symbol `a₀` (`dbRead`). Compression intertwines the oracle with the recording oracle, so the
compressed run is the run with the recording oracle from the empty database [Ham25, Theorem 39]
(`FinDist.compress_mul_jRun`). A Zhandry progress measure is `‖Π C Ψₜ‖` for a projection `Π` onto a
set of database strings (`dbProj`). Its growth per query is the commutator `‖[O_rec, Π] C Ψⱼ‖`
(`FinDist.jNorm_dbProj_compress_jRun_le`); this is the transfer lemma
(`jNorm_jRun_sub_mul_le`) with equal source and target registers: the database register with its
oracle, and `K = R Π R`, run from `0` on the target side.

## Main definitions

* `FinDist.meanVec`, `FinDist.recOp`, `FinDist.recOpAll`: the conditional-mean vectors and the
  recording operators `Rᵢ` and `R = ⊗ᵢ Rᵢ`.
* `FinDist.dbEmbed`, `FinDist.compress`: the embedding `ι` and the compression `C = R ι`.
* `dbSupp`, `dbProj`, `dbRead`: the non-`⊥` positions of a database string, the projection onto a
  set of database strings, and reading a database string with `⊥` read as `a₀`.
* `FinDist.recOracle`: the recording oracle `R O R`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {B : Type} [Fintype B] [DecidableEq B]

/-! ## Database strings -/

/-- **The record set of a database string**: its non-`⊥` positions. -/
def dbSupp (d : ι → Option σ) : Finset ι :=
  Finset.univ.filter fun i => (d i).isSome

/-- **The projection onto a set `P` of database strings**, diagonal in the database basis. -/
noncomputable def dbProj (P : Set (ι → Option σ)) :
    Matrix (ι → Option σ) (ι → Option σ) ℂ := by
  classical exact Matrix.diagonal fun d => if d ∈ P then 1 else 0

/-- Reading a database string as an input, with `⊥` read as the symbol `a₀`. -/
def dbRead (a₀ : σ) (d : ι → Option σ) : ι → σ :=
  fun i => (d i).getD a₀

/-- The database string with no entries. -/
def dbEmpty : ι → Option σ := fun _ => none

namespace FinDist

variable (ρ : FinDist (ι → σ))

/-! ## The recording operator -/

/-- **The conditional-mean vector** of coordinate `i`: `|√μᵢ⟩ = ∑_a √μᵢ(a) |a⟩`, a unit vector. For
the uniform distribution on `Z_qⁿ` it is the uniform superposition; for Bernoulli(`p`) bits it is
`√(1−p)|0⟩ + √p|1⟩`. -/
noncomputable def meanVec (i : ι) (a : σ) : ℂ :=
  ((Real.sqrt (ρ.marg i a) : ℝ) : ℂ)

/-- **The recording operator** `Rᵢ` of coordinate `i` on `ℂ^{Option σ}` [Zha19; Ham25,
Definition 36]: it exchanges `|⊥⟩` (`none`) with the conditional-mean vector `|√μᵢ⟩` and fixes
their orthogonal complement, `Rᵢ = I − |⊥⟩⟨⊥| − |m⟩⟨m| + |⊥⟩⟨m| + |m⟩⟨⊥|` with `m = √μᵢ`. -/
noncomputable def recOp (i : ι) : Matrix (Option σ) (Option σ) ℂ := fun u v =>
  match u, v with
  | none, none => 0
  | none, some b => ρ.meanVec i b
  | some a, none => ρ.meanVec i a
  | some a, some b => (if a = b then 1 else 0) - ρ.meanVec i a * ρ.meanVec i b

/-- **The recording operator** `R = ⊗ᵢ Rᵢ` on the database register. -/
noncomputable def recOpAll : Matrix (ι → Option σ) (ι → Option σ) ℂ :=
  fun d e => ∏ i, ρ.recOp i (d i) (e i)

/-- The embedding `ι` of the input register into the database register: `|x⟩ ↦ |x⟩`. -/
def dbEmbed : Matrix (ι → Option σ) ρ.Supp ℂ :=
  fun d x => if d = (fun i => some (x.1 i)) then 1 else 0

/-- **The compression** `C = R ι` from the input register to the database register. -/
noncomputable def compress : Matrix (ι → Option σ) ρ.Supp ℂ :=
  ρ.recOpAll * ρ.dbEmbed

/-- **The recording oracle** `O_rec = R O R` on the database register [Ham25, Definition 38], where
the oracle `O` reads `⊥` as `a₀`. -/
noncomputable def recOracle (O : (ι → σ) → Matrix B B ℂ) (a₀ : σ)
    (f : JVec (ι → Option σ) B) : JVec (ι → Option σ) B :=
  ρ.recOpAll * jOracle O (dbRead a₀) (ρ.recOpAll * f)

private lemma star_meanVec (i : ι) (a : σ) : star (ρ.meanVec i a) = ρ.meanVec i a := by
  simp [meanVec]

/-- `|√μᵢ⟩` is a unit vector. -/
theorem sum_meanVec_mul_self (i : ι) : ∑ a, ρ.meanVec i a * ρ.meanVec i a = 1 := by
  have h : ∀ a, Real.sqrt (ρ.marg i a) * Real.sqrt (ρ.marg i a) = ρ.marg i a :=
    fun a => Real.mul_self_sqrt (marg_nonneg (ρ := ρ) i a)
  simp only [meanVec, ← Complex.ofReal_mul, h]
  rw [← Complex.ofReal_sum, sum_marg, Complex.ofReal_one]

/-- A sum whose terms are `√μᵢ(x)² c` is `c`. -/
private lemma sum_meanVec_sq (i : ι) (f : σ → ℂ) (c : ℂ)
    (hf : ∀ x, f x = ρ.meanVec i x * ρ.meanVec i x * c) : ∑ x, f x = c := by
  rw [Finset.sum_congr rfl fun x _ => hf x, ← Finset.sum_mul, sum_meanVec_mul_self, one_mul]

/-- `Rᵢ` is an involution: `Rᵢ² = I`. -/
theorem recOp_mul_self (i : ι) : ρ.recOp i * ρ.recOp i = 1 := by
  have hs := sum_meanVec_mul_self ρ i
  ext u w
  rcases u with _ | a <;> rcases w with _ | b
  · simp only [Matrix.mul_apply, recOp, Fintype.sum_option, mul_zero, hs, zero_add, one_apply_eq]
  · simp only [Matrix.mul_apply, recOp, Fintype.sum_option, zero_mul, mul_sub, mul_ite, mul_one,
      mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, zero_add,
      ne_eq, reduceCtorEq, not_false_eq_true, one_apply_ne]
    rw [sum_meanVec_sq ρ i _ (ρ.meanVec i b), sub_self]
    exact fun x => by ring
  · simp only [Matrix.mul_apply, recOp, Fintype.sum_option, mul_zero, sub_mul, ite_mul, one_mul,
      zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, zero_add,
      ne_eq, reduceCtorEq, not_false_eq_true, one_apply_ne]
    rw [sum_meanVec_sq ρ i _ (ρ.meanVec i a), sub_self]
    exact fun x => by ring
  · simp only [Matrix.mul_apply, recOp, Fintype.sum_option, mul_sub, mul_ite, mul_one, mul_zero,
      sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, Finset.sum_ite_eq, Matrix.one_apply, Option.some.injEq]
    rw [sum_meanVec_sq ρ i _ (ρ.meanVec i a * ρ.meanVec i b)]
    · ring
    · exact fun x => by ring

/-- `Rᵢ` is Hermitian. -/
theorem recOp_isHermitian (i : ι) : (ρ.recOp i).IsHermitian := by
  refine Matrix.IsHermitian.ext fun u v => ?_
  rcases u with _ | a <;> rcases v with _ | b
  · exact star_zero _
  · exact star_meanVec ρ i b
  · exact star_meanVec ρ i a
  · simp only [recOp, eq_comm, mul_comm, star_sub, RCLike.star_def,
      MonoidWithZeroHom.map_ite_one_zero, star_mul', star_meanVec]

/-- `Rᵢ` is unitary. -/
theorem recOp_mem_unitaryGroup (i : ι) : ρ.recOp i ∈ Matrix.unitaryGroup (Option σ) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, (ρ.recOp_isHermitian i).eq,
    recOp_mul_self]

/-- Tensor-product matrices on `ι → τ` multiply factorwise. -/
private lemma sum_prod_mul_prod {τ : Type} [Fintype τ] (F G : ι → Matrix τ τ ℂ) (d e : ι → τ) :
    ∑ f : ι → τ, (∏ i, F i (d i) (f i)) * ∏ i, G i (f i) (e i)
      = ∏ i, (F i * G i) (d i) (e i) := by
  simp_rw [← Finset.prod_mul_distrib, Matrix.mul_apply]
  rw [Fintype.prod_sum]

/-- The identity on `ι → τ` is the tensor product of identities. -/
private lemma prod_one_apply {τ : Type} [DecidableEq τ] (d e : ι → τ) :
    ∏ i, (1 : Matrix τ τ ℂ) (d i) (e i) = (1 : Matrix (ι → τ) (ι → τ) ℂ) d e := by
  by_cases hde : d = e
  · subst hde
    simp
  · rw [Matrix.one_apply, ite_eq_right hde]
    obtain ⟨k, hk⟩ : ∃ k, d k ≠ e k := by
      by_contra hc
      push Not at hc
      exact hde (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])

/-- `R` is an involution. -/
theorem recOpAll_mul_self : ρ.recOpAll * ρ.recOpAll = 1 := by
  ext d e
  rw [Matrix.mul_apply]
  change ∑ f : ι → Option σ, (∏ i, ρ.recOp i (d i) (f i)) * ∏ i, ρ.recOp i (f i) (e i) = _
  rw [sum_prod_mul_prod]
  simp_rw [recOp_mul_self]
  exact prod_one_apply d e

/-- `R` is Hermitian. -/
theorem recOpAll_isHermitian : ρ.recOpAll.IsHermitian := by
  refine Matrix.IsHermitian.ext fun d e => ?_
  change star (∏ i, ρ.recOp i (e i) (d i)) = ∏ i, ρ.recOp i (d i) (e i)
  rw [star_prod]
  exact Finset.prod_congr rfl fun i _ => (ρ.recOp_isHermitian i).apply (d i) (e i)

/-- `R` is unitary. -/
theorem recOpAll_mem_unitaryGroup :
    ρ.recOpAll ∈ Matrix.unitaryGroup (ι → Option σ) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ρ.recOpAll_isHermitian.eq,
    recOpAll_mul_self]

/-- The entries of the compression: `⟨d|C|x⟩ = ∏ᵢ ⟨dᵢ|Rᵢ|xᵢ⟩`. -/
theorem compress_apply (d : ι → Option σ) (x : ρ.Supp) :
    ρ.compress d x = ∏ i, ρ.recOp i (d i) (some (x.1 i)) := by
  rw [compress, Matrix.mul_apply]
  simp only [dbEmbed, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rfl

/-! ## Compression relabels the records -/

/-- The embedding of an input string is injective. -/
private lemma some_comp_eq_iff {x y : ρ.Supp} :
    ((fun i => some (x.1 i)) = fun i => some (y.1 i)) ↔ x = y := by
  constructor
  · intro h
    exact Subtype.ext (funext fun i => Option.some_injective _ (congrFun h i))
  · rintro rfl
    rfl

/-- The embedding is an isometry. -/
private lemma conjTranspose_dbEmbed_mul_dbEmbed : ρ.dbEmbedᴴ * ρ.dbEmbed = 1 := by
  ext x y
  simp only [Matrix.mul_apply, conjTranspose_apply, dbEmbed, RCLike.star_def,
    MonoidWithZeroHom.map_ite_one_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, Matrix.one_apply, some_comp_eq_iff, eq_comm]

/-- **Compression is an isometry**: `C† C = I`. -/
theorem conjTranspose_compress_mul_compress : ρ.compressᴴ * ρ.compress = 1 := by
  rw [compress, Matrix.conjTranspose_mul, ρ.recOpAll_isHermitian.eq, Matrix.mul_assoc,
    ← Matrix.mul_assoc ρ.recOpAll, recOpAll_mul_self, Matrix.one_mul,
    conjTranspose_dbEmbed_mul_dbEmbed]

/-- Compression preserves the norm of joint vectors, on every finite workspace. -/
theorem jNormSq_compress_mul (g : JVec ρ.Supp B) : jNormSq (ρ.compress * g) = jNormSq g := by
  exact jNormSq_mul_of_isometry ρ.conjTranspose_compress_mul_compress g

variable {ρ}

variable (ρ) in
/-- `√(μᵢ(a) μᵢ(b)) = √μᵢ(a) √μᵢ(b)`. -/
private lemma sqrt_marg_mul (i : ι) (a b : σ) :
    ((Real.sqrt (ρ.marg i a * ρ.marg i b) : ℝ) : ℂ) = ρ.meanVec i a * ρ.meanVec i b := by
  rw [Real.sqrt_mul (marg_nonneg (ρ := ρ) i a), Complex.ofReal_mul]
  rfl

variable (ρ) in
/-- The coordinate identity behind the relabelling:
`∑_a ⟨v|Rᵢ|a⟩ ⟨a|P_{S,i}|b⟩ = [i ∈ S ↔ v ≠ ⊥] ⟨v|Rᵢ|b⟩`. -/
private lemma sum_recOp_mul_recFactor (S : Finset ι) (i : ι) (v : Option σ) (b : σ) :
    ∑ a, ρ.recOp i v (some a) * ρ.recFactor S i a b
      = (if (i ∈ S ↔ v.isSome = true) then 1 else 0) * ρ.recOp i v (some b) := by
  simp only [recFactor, sqrt_marg_mul]
  by_cases hi : i ∈ S <;> rcases v with _ | c
  · simp only [recOp, hi, ↓reduceIte, Option.isSome_none, Bool.false_eq_true, iff_false,
      not_true_eq_false, zero_mul]
    simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    rw [sum_meanVec_sq ρ i _ (ρ.meanVec i b), sub_self]
    exact fun x => by ring
  · simp only [recOp, hi, ↓reduceIte, Option.isSome_some, one_mul]
    simp only [mul_sub, mul_ite, mul_one, mul_zero, sub_mul, ite_mul, one_mul, zero_mul,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_ite_eq]
    rw [sum_meanVec_sq ρ i _ (ρ.meanVec i c * ρ.meanVec i b)]
    · ring
    · exact fun x => by ring
  · simp only [recOp, hi, ↓reduceIte, Option.isSome_none, Bool.false_eq_true, one_mul]
    exact sum_meanVec_sq ρ i _ _ fun x => by ring
  · simp only [recOp, hi, ↓reduceIte, Option.isSome_some, iff_true, zero_mul]
    simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
    rw [sum_meanVec_sq ρ i _ (ρ.meanVec i c * ρ.meanVec i b), sub_self]
    exact fun x => by ring

omit [Fintype σ] [DecidableEq σ] in
private lemma dbSupp_eq_iff (d : ι → Option σ) (S : Finset ι) :
    dbSupp d = S ↔ ∀ i ∈ Finset.univ, (i ∈ S ↔ (d i).isSome = true) := by
  simp only [Finset.ext_iff, dbSupp, Finset.mem_filter, Finset.mem_univ, true_and, forall_const]
  exact forall_congr' fun i => Iff.comm

/-- **Compression relabels the records** (relation to Layer D): for a product distribution with
full-support marginals, the projection onto the database strings whose non-`⊥` positions form
`S` corresponds under compression to the record projection `P_S`: `Π_{dbSupp = S} C = C P_S`. -/
theorem dbProj_dbSupp_eq_mul_compress (h : ρ.IsFullProduct) (S : Finset ι) :
    dbProj {d : ι → Option σ | dbSupp d = S} * ρ.compress = ρ.compress * ρ.recProj S := by
  ext d y
  rw [dbProj, Matrix.diagonal_mul, Matrix.mul_apply]
  change _ = ∑ x : ρ.Supp, ρ.compress d x * ∏ i, ρ.recFactor S i (x.1 i) (y.1 i)
  simp_rw [compress_apply]
  rw [sum_supp_eq_univ (mass_pos_of_isFullProduct h) (fun x : ι → σ =>
    (∏ i, ρ.recOp i (d i) (some (x i))) * ∏ i, ρ.recFactor S i (x i) (y.1 i))]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i a => ρ.recOp i (d i) (some a) * ρ.recFactor S i a (y.1 i))]
  simp_rw [sum_recOp_mul_recFactor, Finset.prod_mul_distrib, Finset.prod_boole]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ((dbSupp_eq_iff d S).mp h1) h2
  · exact absurd ((dbSupp_eq_iff d S).mpr h2) h1
  · rfl

/-- The record projection `P_S` is the pullback of the database projection: `C† Π_{dbSupp = S} C =
P_S`. -/
theorem conjTranspose_compress_mul_dbProj_mul_compress (h : ρ.IsFullProduct) (S : Finset ι) :
    ρ.compressᴴ * dbProj {d : ι → Option σ | dbSupp d = S} * ρ.compress = ρ.recProj S := by
  rw [Matrix.mul_assoc, dbProj_dbSupp_eq_mul_compress h, ← Matrix.mul_assoc,
    conjTranspose_compress_mul_compress, Matrix.one_mul]

/-- The same for a family `F` of record sets: `Π_{dbSupp ∈ F} C = C Π_F`. -/
theorem dbProj_dbSupp_mem_mul_compress (h : ρ.IsFullProduct) (F : Set (Finset ι)) :
    dbProj {d : ι → Option σ | dbSupp d ∈ F} * ρ.compress = ρ.compress * ρ.recIn F := by
  classical
  rw [recIn, Matrix.mul_sum]
  simp_rw [← dbProj_dbSupp_eq_mul_compress h]
  ext d y
  rw [Matrix.sum_apply]
  simp only [dbProj, Matrix.diagonal_mul]
  rw [← Finset.sum_mul]
  congr 1
  simp only [Set.mem_ofPred_eq]
  by_cases hd : dbSupp d ∈ F
  · rw [Finset.sum_eq_single_of_mem (dbSupp d) (by simpa using hd) fun S _ hS => ?_]
    · simp [hd]
    · simp [Ne.symm hS]
  · rw [Finset.sum_eq_zero fun S hS => ?_]
    · simp [hd]
    · have hne : dbSupp d ≠ S := fun e => hd (e ▸ (Finset.mem_filter.mp hS).2)
      simp [hne]

/-- **Records are database entries**: the weight of a joint vector on the records in `F` is the
weight of its compression on the database strings with record set in `F`. -/
theorem jNormSq_dbProj_compress_mul (h : ρ.IsFullProduct) (F : Set (Finset ι))
    (g : JVec ρ.Supp B) :
    jNormSq (dbProj {d : ι → Option σ | dbSupp d ∈ F} * (ρ.compress * g))
      = jNormSq (ρ.recIn F * g) := by
  rw [← Matrix.mul_assoc, dbProj_dbSupp_mem_mul_compress h, Matrix.mul_assoc,
    jNormSq_compress_mul]

variable (ρ) in
/-- The coordinate identity behind the initial state: `∑_a ⟨v|Rᵢ|a⟩ √μᵢ(a) = [v = ⊥]`. -/
theorem sum_recOp_mul_meanVec (i : ι) (v : Option σ) :
    ∑ a, ρ.recOp i v (some a) * ρ.meanVec i a = if v = none then 1 else 0 := by
  rcases v with _ | c
  · simp only [recOp, ↓reduceIte]
    exact sum_meanVec_mul_self ρ i
  · simp only [recOp, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, reduceCtorEq]
    rw [sum_meanVec_sq ρ i _ (ρ.meanVec i c), sub_self]
    exact fun x => by ring

/-- For a full product distribution, `|ρ⟩ = ⊗ᵢ |√μᵢ⟩`. -/
private lemma ket_eq_prod_meanVec (h : ρ.IsFullProduct) (x : ρ.Supp) :
    ρ.ket x = ∏ i, ρ.meanVec i (x.1 i) := by
  rw [ket, mass_eq_prod_marg h, Real.sqrt_prod _ fun k _ => marg_nonneg (ρ := ρ) _ _,
    Complex.ofReal_prod]
  rfl

/-- `C |ρ⟩ = |⊥…⊥⟩`. -/
private lemma compress_mulVec_ket (h : ρ.IsFullProduct) :
    ρ.compress *ᵥ ρ.ket = Pi.single dbEmpty 1 := by
  funext d
  rw [Matrix.mulVec, dotProduct]
  simp_rw [compress_apply, ket_eq_prod_meanVec h]
  rw [sum_supp_eq_univ (mass_pos_of_isFullProduct h) (fun x : ι → σ =>
    (∏ i, ρ.recOp i (d i) (some (x i))) * ∏ i, ρ.meanVec i (x i))]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i a => ρ.recOp i (d i) (some a) * ρ.meanVec i a)]
  simp_rw [sum_recOp_mul_meanVec]
  rw [Finset.prod_boole, Pi.single_apply]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (funext fun i => h1 i (Finset.mem_univ i)) h2
  · exact absurd (fun i _ => congrFun h2 i) h1
  · rfl

/-- **The initial record is empty** [Ham25, Section 4.1]: `C (|ρ⟩ ⊗ v) = |⊥…⊥⟩ ⊗ v`. -/
theorem compress_mul_vecMulVec_ket (h : ρ.IsFullProduct) (v : B → ℂ) :
    ρ.compress * vecMulVec ρ.ket v = vecMulVec (Pi.single dbEmpty 1) v := by
  rw [Matrix.mul_vecMulVec, compress_mulVec_ket h]

/-- Projections onto disjoint sets of database strings are orthogonal. -/
private lemma dbProj_mul_dbProj_eq_zero {P Q : Set (ι → Option σ)} (hPQ : ∀ d ∈ P, d ∉ Q) :
    dbProj P * dbProj Q = 0 := by
  rw [dbProj, dbProj, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
  congr 1
  funext d
  by_cases hd : d ∈ P
  · simp [hd, hPQ d hd]
  · simp [hd]

/-- A joint vector with at most `t` records compresses to databases with at most `t` entries. -/
theorem dbProj_card_gt_mul_compress_of_recLe (h : ρ.IsFullProduct) {t : ℕ} {g : JVec ρ.Supp B}
    (hg : ρ.recLe t * g = g) :
    dbProj {d : ι → Option σ | t < (dbSupp d).card} * (ρ.compress * g) = 0 := by
  have hrec : ρ.recLe t = ρ.recIn {S | S.card ≤ t} := by
    rw [recLe, recIn]
    congr 1
    ext S
    simp
  rw [← hg, ← Matrix.mul_assoc ρ.compress, hrec, ← dbProj_dbSupp_mem_mul_compress h,
    Matrix.mul_assoc, ← Matrix.mul_assoc (dbProj _), dbProj_mul_dbProj_eq_zero, Matrix.zero_mul]
  intro d hd hd'
  simp only [Set.mem_ofPred_eq] at hd hd'
  omega

/-- **The record size** [Ham25, Fact 37], value-oracle model: after `t` queries the compressed
joint state is supported on databases with at most `t` entries. -/
theorem dbProj_card_gt_mul_compress_jointState (h : ρ.IsFullProduct) {O W : Type} [Fintype W]
    [DecidableEq W] (A : QAlg ι σ O W) (t : ℕ) :
    dbProj {d : ι → Option σ | t < (dbSupp d).card} * (ρ.compress * ρ.jointState id A t) = 0 := by
  exact dbProj_card_gt_mul_compress_of_recLe h (recLe_mul_jointState h A t)

/-! ## The recording oracle and progress measures -/

variable (ρ) in
/-- The row of `ι M` at the embedding of an input string is the row of `M`. -/
private lemma dbEmbed_mul_apply_some {A : Type} [Fintype A] (M : Matrix ρ.Supp A ℂ)
    (x : ρ.Supp) : (ρ.dbEmbed * M) (fun i => some (x.1 i)) = M x := by
  funext p
  rw [Matrix.mul_apply]
  simp only [dbEmbed, some_comp_eq_iff, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

variable (ρ) in
/-- The rows of `ι M` away from the embedded input strings vanish. -/
private lemma dbEmbed_mul_apply_of_ne {A : Type} [Fintype A] (M : Matrix ρ.Supp A ℂ)
    (d : ι → Option σ) (hd : ∀ x : ρ.Supp, d ≠ fun i => some (x.1 i)) :
    (ρ.dbEmbed * M) d = 0 := by
  funext p
  rw [Matrix.mul_apply]
  simp [dbEmbed, hd]

variable (ρ) in
/-- The embedding intertwines the oracle with the oracle reading `⊥` as `a₀`. -/
private lemma dbEmbed_mul_jOracle (O : (ι → σ) → Matrix B B ℂ) (a₀ : σ) (g : JVec ρ.Supp B) :
    ρ.dbEmbed * jOracle O (fun x : ρ.Supp => x.1) g = jOracle O (dbRead a₀) (ρ.dbEmbed * g) := by
  funext d
  by_cases hd : ∃ x : ρ.Supp, d = fun i => some (x.1 i)
  · obtain ⟨x, rfl⟩ := hd
    rw [dbEmbed_mul_apply_some]
    change O x.1 *ᵥ g x
      = O (dbRead a₀ fun i => some (x.1 i)) *ᵥ (ρ.dbEmbed * g) (fun i => some (x.1 i))
    rw [dbEmbed_mul_apply_some]
    rfl
  · push Not at hd
    rw [dbEmbed_mul_apply_of_ne ρ _ d hd]
    change 0 = O (dbRead a₀ d) *ᵥ (ρ.dbEmbed * g) d
    rw [dbEmbed_mul_apply_of_ne ρ _ d hd, Matrix.mulVec_zero]

variable (ρ) in
/-- **Compression intertwines the oracle with the recording oracle**: `C O = O_rec C`, for any
oracle family and any reading `a₀` of `⊥`. -/
theorem compress_mul_jOracle (O : (ι → σ) → Matrix B B ℂ) (a₀ : σ) (g : JVec ρ.Supp B) :
    ρ.compress * jOracle O (fun x : ρ.Supp => x.1) g = ρ.recOracle O a₀ (ρ.compress * g) := by
  have h1 : ρ.compress * g = ρ.recOpAll * (ρ.dbEmbed * g) := Matrix.mul_assoc _ _ _
  rw [h1, recOracle, ← Matrix.mul_assoc ρ.recOpAll ρ.recOpAll, recOpAll_mul_self, Matrix.one_mul,
    compress, Matrix.mul_assoc, dbEmbed_mul_jOracle ρ O a₀]

variable (ρ) in
/-- **Indistinguishability** [Ham25, Theorem 39]: the compressed run is the run with the recording
oracle, started from the compressed initial vector. -/
theorem compress_mul_jRun (O : (ι → σ) → Matrix B B ℂ) (a₀ : σ) (U : ℕ → Matrix B B ℂ)
    (f₀ : JVec ρ.Supp B) (t : ℕ) :
    ρ.compress * jRun (jOracle O (fun x : ρ.Supp => x.1)) U f₀ t
      = jRun (ρ.recOracle O a₀) U (ρ.compress * f₀) t := by
  induction t with
  | zero => rw [jRun_zero, jRun_zero, mul_wsOp]
  | succ t ih => rw [jRun_succ, jRun_succ, mul_wsOp, compress_mul_jOracle ρ O a₀, ih]

variable (ρ) in
/-- The embedding intertwines the runs. -/
private lemma jRun_dbEmbed (O : (ι → σ) → Matrix B B ℂ) (a₀ : σ) (U : ℕ → Matrix B B ℂ)
    (f₀ : JVec ρ.Supp B) (t : ℕ) :
    jRun (jOracle O (dbRead a₀)) U (ρ.dbEmbed * f₀) t
      = ρ.dbEmbed * jRun (jOracle O (fun x : ρ.Supp => x.1)) U f₀ t := by
  induction t with
  | zero => rw [jRun_zero, jRun_zero, mul_wsOp]
  | succ t ih => rw [jRun_succ, jRun_succ, mul_wsOp, ih, dbEmbed_mul_jOracle ρ O a₀]

omit [DecidableEq ι] [DecidableEq σ] in
/-- The run of a joint oracle from `0` stays at `0`. -/
private lemma jRun_jOracle_zero {X : Type} [Fintype X] [DecidableEq X]
    (O : (ι → σ) → Matrix B B ℂ) (read : X → ι → σ) (U : ℕ → Matrix B B ℂ) (t : ℕ) :
    jRun (jOracle O read) U (0 : JVec X B) t = 0 := by
  have h0 : jOracle O read (0 : JVec X B) = 0 := by
    funext x
    exact Matrix.mulVec_zero _
  induction t with
  | zero => rw [jRun_zero, wsOp_eq_mul_transpose, Matrix.zero_mul]
  | succ t ih => rw [jRun_succ, ih, h0, wsOp_eq_mul_transpose, Matrix.zero_mul]

variable (ρ) in
/-- The query error of `K = R Π R` on the embedded run is `R` times the commutator of the
recording oracle with `Π` on the compressed run. -/
private lemma jOracle_sub_mul_jOracle_dbEmbed (O : (ι → σ) → Matrix B B ℂ) (a₀ : σ)
    (P : Set (ι → Option σ)) (Ψ : JVec ρ.Supp B) :
    jOracle O (dbRead a₀) (ρ.recOpAll * dbProj P * ρ.recOpAll * (ρ.dbEmbed * Ψ))
        - ρ.recOpAll * dbProj P * ρ.recOpAll * jOracle O (dbRead a₀) (ρ.dbEmbed * Ψ)
      = ρ.recOpAll * (ρ.recOracle O a₀ (dbProj P * (ρ.compress * Ψ))
        - dbProj P * ρ.recOracle O a₀ (ρ.compress * Ψ)) := by
  have hRR : ∀ M : JVec (ι → Option σ) B, ρ.recOpAll * (ρ.recOpAll * M) = M := fun M => by
    rw [← Matrix.mul_assoc, recOpAll_mul_self, Matrix.one_mul]
  simp only [recOracle, compress, Matrix.mul_sub, Matrix.mul_assoc, hRR]

variable (ρ) in
/-- **The growth of a progress measure** [Zha19; Ham25, Section 4]: for any set `P` of database
strings, after `t` queries

  `‖Π C Ψₜ‖ ≤ ‖Π C Ψ₀‖ + ∑_{j<t} ‖O_rec Π C Ψⱼ − Π O_rec C Ψⱼ‖`.

Derived from the transfer lemma (`jNorm_jRun_sub_mul_le`) with equal source and target registers:
both are the database register with the oracle `O` reading `⊥` as `a₀`, the map is `K = R Π R`,
and the target run starts from `0`. -/
theorem jNorm_dbProj_compress_jRun_le (O : (ι → σ) → Matrix B B ℂ)
    (hO : ∀ a, O a ∈ Matrix.unitaryGroup B ℂ) (a₀ : σ) {U : ℕ → Matrix B B ℂ}
    (hU : ∀ t, U t ∈ Matrix.unitaryGroup B ℂ) (f₀ : JVec ρ.Supp B) (P : Set (ι → Option σ))
    (t : ℕ) :
    jNorm (dbProj P * (ρ.compress * jRun (jOracle O (fun x : ρ.Supp => x.1)) U f₀ t))
      ≤ jNorm (dbProj P * (ρ.compress * f₀))
        + ∑ j ∈ Finset.range t,
            jNorm (ρ.recOracle O a₀ (dbProj P * (ρ.compress
                * jRun (jOracle O (fun x : ρ.Supp => x.1)) U f₀ j))
              - dbProj P * ρ.recOracle O a₀ (ρ.compress
                * jRun (jOracle O (fun x : ρ.Supp => x.1)) U f₀ j)) := by
  have hR : ρ.recOpAllᴴ * ρ.recOpAll = 1 := by
    rw [ρ.recOpAll_isHermitian.eq, recOpAll_mul_self]
  have hK : ∀ X : JVec ρ.Supp B, ρ.recOpAll * dbProj P * ρ.recOpAll * (ρ.dbEmbed * X)
      = ρ.recOpAll * (dbProj P * (ρ.compress * X)) := fun X => by
    simp only [compress, Matrix.mul_assoc]
  have key := jNorm_jRun_sub_mul_le (ρ.recOpAll * dbProj P * ρ.recOpAll)
    (jOracle O (dbRead a₀)) (jOracle O (dbRead a₀))
    (fun g h => (jNorm_jOracle_sub_jOracle hO (dbRead a₀) g h).le) hU (ρ.dbEmbed * f₀) 0
    (fun j => jNorm (ρ.recOracle O a₀ (dbProj P * (ρ.compress
        * jRun (jOracle O (fun x : ρ.Supp => x.1)) U f₀ j))
      - dbProj P * ρ.recOracle O a₀ (ρ.compress
        * jRun (jOracle O (fun x : ρ.Supp => x.1)) U f₀ j))) t
    (fun j _ => by
      rw [jRun_dbEmbed, jOracle_sub_mul_jOracle_dbEmbed, jNorm_mul_of_isometry hR])
  rw [jRun_jOracle_zero, zero_sub, jNorm_neg, zero_sub, jNorm_neg, jRun_dbEmbed, hK, hK,
    jNorm_mul_of_isometry hR, jNorm_mul_of_isometry hR] at key
  exact key

end FinDist

/-! ## The phase-oracle model over `Z_q` -/

section PhaseModel

variable {q : ℕ} [NeZero q] {O W : Type} [Fintype W] [DecidableEq W]

namespace FinDist

/-- The phase-model joint state is the run started from `|ρ⟩ ⊗ init`. -/
theorem jointZqState_eq_jRun {Ω : Type} [Fintype Ω] [DecidableEq Ω] (ρ : FinDist Ω)
    (read : Ω → ι → ZMod q) (A : QAlg ι (ZMod q) O W) (t : ℕ) :
    ρ.jointZqState read A t
      = jRun (jOracle phaseZqOracleMat (fun x : ρ.Supp => read x)) A.step
          (vecMulVec ρ.ket A.init) t := by
  induction t with
  | zero =>
    rw [jointZqState_zero, jRun_zero]
    funext x
    rw [wsOp, vecMulVec_row, Matrix.mulVec_smul]
  | succ t ih => rw [jointZqState_succ, jRun_succ, ih]

variable {ρ : FinDist (ι → ZMod q)}

/-- **The record size in the phase model** [Ham25, Fact 37]: after `t` phase queries the
compressed joint state is supported on databases with at most `t` entries. -/
theorem dbProj_card_gt_mul_compress_jointZqState (h : ρ.IsFullProduct) (A : QAlg ι (ZMod q) O W)
    (t : ℕ) :
    dbProj {d : ι → Option (ZMod q) | t < (dbSupp d).card} * (ρ.compress * ρ.jointZqState id A t)
      = 0 := by
  exact dbProj_card_gt_mul_compress_of_recLe h (recLe_mul_jointZqState h A t)

/-- **Indistinguishability in the phase model** [Ham25, Theorem 39]: the compressed joint state is
the run of the recording oracle (with `⊥` read as `0`, so a query to an empty entry has phase `1`)
from the empty database. -/
theorem compress_mul_jointZqState (h : ρ.IsFullProduct) (A : QAlg ι (ZMod q) O W) (t : ℕ) :
    ρ.compress * ρ.jointZqState id A t
      = jRun (ρ.recOracle phaseZqOracleMat 0) A.step (vecMulVec (Pi.single dbEmpty 1) A.init)
          t := by
  rw [jointZqState_eq_jRun]
  exact (compress_mul_jRun ρ phaseZqOracleMat 0 A.step _ t).trans
    (by rw [compress_mul_vecMulVec_ket h])

/-- **The growth of a progress measure in the phase model**: if the empty database is not in `P`,
then `‖Π C Ψₜ‖ ≤ ∑_{j<t} ‖O_rec Π C Ψⱼ − Π O_rec C Ψⱼ‖`. -/
theorem jNorm_dbProj_compress_jointZqState_le (h : ρ.IsFullProduct) (A : QAlg ι (ZMod q) O W)
    {P : Set (ι → Option (ZMod q))} (hP : dbEmpty ∉ P) (t : ℕ) :
    jNorm (dbProj P * (ρ.compress * ρ.jointZqState id A t))
      ≤ ∑ j ∈ Finset.range t,
          jNorm (ρ.recOracle phaseZqOracleMat 0 (dbProj P * (ρ.compress * ρ.jointZqState id A j))
            - dbProj P * ρ.recOracle phaseZqOracleMat 0 (ρ.compress * ρ.jointZqState id A j)) := by
  have hz : ∀ j, ρ.jointZqState id A j = jRun (jOracle phaseZqOracleMat (fun x : ρ.Supp => x.1))
      A.step (vecMulVec ρ.ket A.init) j := fun j => jointZqState_eq_jRun ρ id A j
  have key := jNorm_dbProj_compress_jRun_le ρ phaseZqOracleMat
    (fun a => phaseZqOracleMat_mem_unitaryGroup a) 0 A.step_unitary (vecMulVec ρ.ket A.init) P t
  have hv : dbProj P *ᵥ (Pi.single dbEmpty 1 : (ι → Option (ZMod q)) → ℂ) = 0 := by
    rw [dbProj, Matrix.diagonal_mulVec_single]
    simp [hP]
  rw [compress_mul_vecMulVec_ket h, Matrix.mul_vecMulVec, hv, Matrix.zero_vecMulVec, jNorm_zero,
    zero_add] at key
  simp only [hz]
  exact key

end FinDist

end PhaseModel

end QuantumQueryComplexity
