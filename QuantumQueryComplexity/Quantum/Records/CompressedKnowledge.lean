import QuantumQueryComplexity.Quantum.Records.Compressed
import QuantumQueryComplexity.Quantum.Records.ZqFourier

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Progress measures and knowledge [Bel26, Section 3.8]

Belovs compares his knowledge `‖Υ⁺ψ‖` with Zhandry's progress measure `‖Π R ψ‖` [Bel26, Section
3.8]. A set `P` of database strings defines the (pseudo-)knowledge family
`L_P(y) = {S | y|_S ∈ P}` (`dbKnow`), where `y|_S` is the database string recording `y` on `S`
and `⊥` elsewhere (`restrictDb`). For arbitrary `P` this family need not be upward closed or
exclude `∅`, so it need not be a knowledge system (`FinDist.IsKnowledgeSystem`). For Search
with target symbol `a`, `P` is the set of databases recording `a` somewhere (`searchDb`), and
`L_P(y) = {S | ∃ i ∈ S, yᵢ = a}` is Belovs's knowledge system for Search (`dbKnow_searchDb`).
Belovs takes `Υ = I`, that is, the hidden problem is the reference distribution itself: `ν = ρ`,
read and typed by the identity.

* **Agreement on single record states.** For a product distribution with full-support marginals
  and a vector `ψ` in one record subspace `P_S`, `Π C ψ = R_S Υ⁺ψ`, where `R_S` applies the
  recording operators off `S` only (`FinDist.compressOff`); so `‖Π C ψ‖ = ‖Υ⁺ψ‖`
  (`FinDist.dbProj_mul_compress_of_recProj`, `FinDist.jNorm_dbProj_compress_of_recProj`). For the
  uniform distribution on `Z_qⁿ` and a Fourier character this is Belovs's identity
  `Π R |σ̂⟩ = R_{supp σ} Υ⁺ |σ̂⟩` (`FinDist.dbProj_searchDb_compress_fourierVec`).
* **They differ in general.** For `n = q = 2` and `ψ = |1̂ ↦ 1⟩ + |2̂ ↦ 1⟩`, the knowledge is
  `‖Υ⁺ψ‖² = 3/2` but the progress measure is `‖Π R ψ‖² = 1` (`knowledge_ne_progress_example`).
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {B : Type} [Fintype B] [DecidableEq B]

/-- The database string recording `y` on `S` and `⊥` elsewhere. -/
def restrictDb (y : ι → σ) (S : Finset ι) : ι → Option σ :=
  fun i => if i ∈ S then some (y i) else none

/-- **The (pseudo-)knowledge family of a set of database strings** [Bel26, Section 3.8]:
`S ∈ L_P(y)` iff the database recording `y` on `S` lies in `P`. For arbitrary `P` it need not be
upward closed or exclude `∅`, so it need not be a knowledge system (`FinDist.IsKnowledgeSystem`).
-/
def dbKnow (P : Set (ι → Option σ)) : (ι → σ) → Set (Finset ι) :=
  fun y => {S | restrictDb y S ∈ P}

/-- **The databases solving Search**: those recording the symbol `a` at some position. -/
def searchDb (a : σ) : Set (ι → Option σ) :=
  {d | ∃ i, d i = some a}

/-- For Search, `L_P` is Belovs's knowledge system: `S ∈ L(y)` iff `yᵢ = a` for some `i ∈ S`
[Bel26, Section 3.8]. -/
theorem dbKnow_searchDb (a : σ) (y : ι → σ) :
    dbKnow (searchDb a) y = {S : Finset ι | ∃ i ∈ S, y i = a} := by
  ext S
  simp [dbKnow, searchDb, restrictDb]

namespace FinDist

variable (ρ : FinDist (ι → σ))

/-- **Partial compression** `R_S ι`: embed the input register and apply `Rᵢ` for `i ∉ S` only. -/
noncomputable def compressOff (S : Finset ι) : Matrix (ι → Option σ) ρ.Supp ℂ :=
  fun d x => ∏ i, if i ∈ S then (if d i = some (x.1 i) then 1 else 0)
    else ρ.recOp i (d i) (some (x.1 i))

/-- Partial compression is an isometry. -/
theorem conjTranspose_compressOff_mul_compressOff (S : Finset ι) :
    (ρ.compressOff S)ᴴ * ρ.compressOff S = 1 := by
  ext x y
  have hfac : ∀ i, ∑ v : Option σ,
      star (if i ∈ S then (if v = some (x.1 i) then (1 : ℂ) else 0)
        else ρ.recOp i v (some (x.1 i)))
      * (if i ∈ S then (if v = some (y.1 i) then (1 : ℂ) else 0)
        else ρ.recOp i v (some (y.1 i))) = if x.1 i = y.1 i then 1 else 0 := by
    intro i
    by_cases hi : i ∈ S
    · simp only [hi, ↓reduceIte]
      rw [Fintype.sum_option]
      simp [eq_comm]
    · simp only [hi, ↓reduceIte]
      have hM := congrFun (congrFun (ρ.recOp_mul_self i) (some (x.1 i))) (some (y.1 i))
      rw [Matrix.mul_apply, Matrix.one_apply] at hM
      have hH : ∀ v, star (ρ.recOp i v (some (x.1 i))) = ρ.recOp i (some (x.1 i)) v := fun v =>
        congrFun (congrFun (ρ.recOp_isHermitian i) (some (x.1 i))) v
      simp only [hH, hM, Option.some.injEq]
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply, compressOff, star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i v => star (if i ∈ S then (if v = some (x.1 i) then (1 : ℂ) else 0)
        else ρ.recOp i v (some (x.1 i)))
      * (if i ∈ S then (if v = some (y.1 i) then (1 : ℂ) else 0)
        else ρ.recOp i v (some (y.1 i)))), Finset.prod_congr rfl fun i _ => hfac i,
    Finset.prod_boole]
  simp [Subtype.ext_iff, funext_iff]

variable {ρ}

/-- A matrix with product entries times `P_S`, entrywise a product of coordinate sums. -/
private lemma mul_recProj_apply_prod (h : ρ.IsFullProduct) {τ : Type} (S : Finset ι)
    (a : ι → τ → σ → ℂ) (A : Matrix (ι → τ) ρ.Supp ℂ)
    (hA : ∀ d x, A d x = ∏ i, a i (d i) (x.1 i)) (d : ι → τ) (y : ρ.Supp) :
    (A * ρ.recProj S) d y = ∏ i, ∑ c, a i (d i) c * ρ.recFactor S i c (y.1 i) := by
  rw [Matrix.mul_apply, Fintype.prod_sum]
  simp only [hA, recProj, ← Finset.prod_mul_distrib]
  exact sum_supp_eq_univ (mass_pos_of_isFullProduct h)
    (fun z => ∏ i, a i (d i) (z i) * ρ.recFactor S i (z i) (y.1 i))

/-- The record factor in terms of the conditional-mean vector. -/
private lemma recFactor_eq (h : ρ.IsFullProduct) (S : Finset ι) (i : ι) (a b : σ) :
    ρ.recFactor S i a b = if i ∈ S then (if a = b then 1 else 0) - ρ.meanVec i a * ρ.meanVec i b
      else ρ.meanVec i a * ρ.meanVec i b := by
  rw [recFactor, meanVec, meanVec, ← Complex.ofReal_mul, ← Real.sqrt_mul (marg_pos h i a).le]

/-- One coordinate of `C P_S`. -/
private lemma sum_recOp_mul_recFactor (h : ρ.IsFullProduct) (S : Finset ι) (i : ι)
    (v : Option σ) (b : σ) :
    ∑ c, ρ.recOp i v (some c) * ρ.recFactor S i c b
      = if i ∈ S then ρ.recOp i v (some b) - (if v = none then ρ.meanVec i b else 0)
        else (if v = none then ρ.meanVec i b else 0) := by
  simp only [recFactor_eq h]
  by_cases hi : i ∈ S
  · simp only [hi, ↓reduceIte, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ← mul_assoc, ← Finset.sum_mul,
      sum_recOp_mul_meanVec ρ, ite_mul, one_mul, zero_mul]
  · simp only [hi, ↓reduceIte, ← mul_assoc, ← Finset.sum_mul, sum_recOp_mul_meanVec ρ, ite_mul,
      one_mul, zero_mul]

/-- One coordinate of `R_S P_S`: the same as one coordinate of `C P_S`. -/
private lemma sum_compressOff_mul_recFactor (h : ρ.IsFullProduct) (S : Finset ι) (i : ι)
    (v : Option σ) (b : σ) :
    ∑ c, (if i ∈ S then (if v = some c then (1 : ℂ) else 0) else ρ.recOp i v (some c))
        * ρ.recFactor S i c b
      = if i ∈ S then ρ.recOp i v (some b) - (if v = none then ρ.meanVec i b else 0)
        else (if v = none then ρ.meanVec i b else 0) := by
  by_cases hi : i ∈ S
  · simp only [hi, ↓reduceIte]
    cases v with
    | none => simp [recOp]
    | some e => simp [recOp, recFactor_eq h, hi]
  · simp only [hi, ↓reduceIte]
    simpa [hi] using sum_recOp_mul_recFactor h S i v b

open Classical in
/-- On the record subspace `P_S`, the record projection `Π_F` is `[S ∈ F]`. -/
private lemma recIn_mul_of_recProj (h : ρ.IsFullProduct) (F : Set (Finset ι)) {S : Finset ι}
    {g : JVec ρ.Supp B} (hg : ρ.recProj S * g = g) (x : ρ.Supp) (b : B) :
    (ρ.recIn F * g) x b = if S ∈ F then g x b else 0 := by
  classical
  have hT : ∀ T, (ρ.recProj T * g) x b = if T = S then g x b else 0 := by
    intro T
    by_cases hTS : T = S
    · rw [ite_eq_left hTS, hTS, hg]
    · rw [ite_eq_right hTS]
      conv_lhs => rw [← hg]
      rw [← Matrix.mul_assoc, recProj_mul_recProj h hTS, Matrix.zero_mul, Matrix.zero_apply]
  unfold recIn
  rw [Matrix.sum_mul, Matrix.sum_apply]
  simp only [hT]
  rw [Finset.sum_ite_eq']
  simp

open Classical in
/-- **The knowledge operator for `Υ = I` on a record subspace**: row `x` of `Υ⁺ g` is `g x` if
`S ∈ L x` and `0` otherwise. -/
private lemma knowOp_self_mul_of_recProj (h : ρ.IsFullProduct) (L : (ι → σ) → Set (Finset ι))
    {S : Finset ι} {g : JVec ρ.Supp B} (hg : ρ.recProj S * g = g) (x : ρ.Supp) (b : B) :
    (knowOp ρ ρ id id L * g) x b = if S ∈ L x.1 then g x b else 0 := by
  classical
  have hrow : (knowOp ρ ρ id id L * g) x b
      = ∑ w, xferOp ρ ρ id x w * (ρ.recIn (L x.1) * g) w b := by
    rw [← Matrix.mul_apply, Matrix.mul_apply]
    simp only [knowOp, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  rw [hrow, xferOp_sum_mul h, id_eq, div_self (ρ.mass_pos x).ne', Real.sqrt_one,
    Complex.ofReal_one, one_mul]
  exact recIn_mul_of_recProj h _ hg x b

/-- `C P_S = R_S P_S`: on the record subspace `P_S`, compression only acts off `S`. -/
private lemma compress_mul_recProj_eq (h : ρ.IsFullProduct) (S : Finset ι) :
    ρ.compress * ρ.recProj S = ρ.compressOff S * ρ.recProj S := by
  ext d y
  rw [mul_recProj_apply_prod h S (fun i v c => ρ.recOp i v (some c)) _ (compress_apply ρ),
    mul_recProj_apply_prod h S (fun i v c => if i ∈ S then (if v = some c then (1 : ℂ) else 0)
      else ρ.recOp i v (some c)) (ρ.compressOff S) (fun _ _ => rfl)]
  exact Finset.prod_congr rfl fun i _ => by
    rw [sum_recOp_mul_recFactor h, sum_compressOff_mul_recFactor h]

/-- `C P_S` is supported on the database strings that are `⊥` off `S`. -/
private lemma compress_mul_recProj_apply_eq_none (h : ρ.IsFullProduct) {S : Finset ι}
    {d : ι → Option σ} {y : ρ.Supp} (hz : (ρ.compress * ρ.recProj S) d y ≠ 0) {i : ι}
    (hi : i ∉ S) : d i = none := by
  by_contra hd
  apply hz
  rw [mul_recProj_apply_prod h S (fun i v c => ρ.recOp i v (some c)) _ (compress_apply ρ)]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [sum_recOp_mul_recFactor h, hi, hd])

/-- A matrix times a column vector, as a joint vector with workspace `Unit`. -/
private lemma mul_col_eq {X Y : Type} [Fintype Y] (U : Matrix X Y ℂ) (v : Y → ℂ) :
    U * Matrix.of (fun y (_ : Unit) => v y) = Matrix.of fun x (_ : Unit) => (U *ᵥ v) x := by
  ext x u
  rfl

/-- **Agreement on single record states** [Bel26, Section 3.8]: for a joint vector `g` in the
record subspace `P_S`, the progress projection of its compression is the partial compression of
its knowledge, `Π_P C g = R_S Υ⁺ g`, where `Υ⁺` is the knowledge operator of `L_P` for `Υ = I`. -/
theorem dbProj_mul_compress_of_recProj (h : ρ.IsFullProduct) (P : Set (ι → Option σ))
    (S : Finset ι) {g : JVec ρ.Supp B} (hg : ρ.recProj S * g = g) :
    dbProj P * (ρ.compress * g) = ρ.compressOff S * (knowOp ρ ρ id id (dbKnow P) * g) := by
  classical
  set M : Matrix ρ.Supp ρ.Supp ℂ :=
    Matrix.diagonal fun x => if restrictDb x.1 S ∈ P then 1 else 0 with hM
  have hK : knowOp ρ ρ id id (dbKnow P) * g = M * (ρ.recProj S * g) := by
    rw [hg]
    ext x b
    rw [knowOp_self_mul_of_recProj h _ hg, hM, Matrix.diagonal_mul]
    by_cases hx : restrictDb x.1 S ∈ P <;> simp [dbKnow, hx]
  have hCR := compress_mul_recProj_eq h S
  have hmat : dbProj P * ρ.compress * ρ.recProj S = ρ.compressOff S * M * ρ.recProj S := by
    set dS : (ι → Option σ) → (ι → Option σ) := fun d i => if i ∈ S then d i else none with hdS
    have h1 : ρ.compressOff S * M
        = Matrix.diagonal (fun d => if dS d ∈ P then (1 : ℂ) else 0) * ρ.compressOff S := by
      ext d x
      rw [hM, Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases hc : ρ.compressOff S d x = 0
      · simp [hc]
      · have hdx : restrictDb x.1 S = dS d := by
          funext i
          by_cases hi : i ∈ S
          · have hne := Finset.prod_ne_zero_iff.mp hc i (Finset.mem_univ i)
            simp only [hi, ↓reduceIte, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
              not_not] at hne
            simp [restrictDb, hdS, hi, hne]
          · simp [restrictDb, hdS, hi]
        rw [hdx, mul_comm]
    rw [h1]
    simp only [Matrix.mul_assoc]
    rw [← hCR]
    ext d y
    rw [dbProj, Matrix.diagonal_mul, Matrix.diagonal_mul]
    by_cases hz : (ρ.compress * ρ.recProj S) d y = 0
    · simp [hz]
    · have hd : dS d = d := by
        funext i
        by_cases hi : i ∈ S
        · simp [hdS, hi]
        · simp [hdS, hi, compress_mul_recProj_apply_eq_none h hz hi]
      rw [hd]
  calc dbProj P * (ρ.compress * g) = dbProj P * (ρ.compress * (ρ.recProj S * g)) := by rw [hg]
    _ = (dbProj P * ρ.compress * ρ.recProj S) * g := by simp only [Matrix.mul_assoc]
    _ = (ρ.compressOff S * M * ρ.recProj S) * g := by rw [hmat]
    _ = ρ.compressOff S * (M * (ρ.recProj S * g)) := by simp only [Matrix.mul_assoc]
    _ = ρ.compressOff S * (knowOp ρ ρ id id (dbKnow P) * g) := by rw [hK]

/-- On a single record subspace, Zhandry's progress measure equals Belovs's knowledge:
`‖Π_P C g‖ = ‖Υ⁺ g‖`. -/
theorem jNorm_dbProj_compress_of_recProj (h : ρ.IsFullProduct) (P : Set (ι → Option σ))
    (S : Finset ι) {g : JVec ρ.Supp B} (hg : ρ.recProj S * g = g) :
    jNorm (dbProj P * (ρ.compress * g)) = jNorm (knowOp ρ ρ id id (dbKnow P) * g) := by
  rw [dbProj_mul_compress_of_recProj h P S hg, jNorm, jNorm,
    jNormSq_mul_of_isometry (conjTranspose_compressOff_mul_compressOff ρ S)]

/-- A character lies in the record subspace of its support. -/
private lemma recProj_zsupp_mulVec_fourierVec {q : ℕ} [NeZero q] (τ : ι → ZMod q) :
    (uniform (ι → ZMod q)).recProj (zsupp τ)
        *ᵥ (fun x : (uniform (ι → ZMod q)).Supp => fourierVec τ x.1)
      = fun x : (uniform (ι → ZMod q)).Supp => fourierVec τ x.1 := by
  rw [recProj_uniform_mulVec_fourier,
    ite_eq_left (show Finset.univ.filter (fun i => τ i ≠ 0) = zsupp τ from rfl)]

/-- **Belovs's identity** `Π R |σ̂⟩ = R_{supp σ} Υ⁺ |σ̂⟩` for Search over the uniform
distribution on `Z_qⁿ` [Bel26, Section 3.8]. -/
theorem dbProj_searchDb_compress_fourierVec {q : ℕ} [NeZero q] (a : ZMod q) (τ : ι → ZMod q) :
    dbProj (searchDb a) *ᵥ ((uniform (ι → ZMod q)).compress
        *ᵥ fun x : (uniform (ι → ZMod q)).Supp => fourierVec τ x.1)
      = (uniform (ι → ZMod q)).compressOff (zsupp τ)
        *ᵥ (knowOp (uniform (ι → ZMod q)) (uniform (ι → ZMod q)) id id (dbKnow (searchDb a))
          *ᵥ fun x : (uniform (ι → ZMod q)).Supp => fourierVec τ x.1) := by
  have hg : (uniform (ι → ZMod q)).recProj (zsupp τ)
      * Matrix.of (fun (x : (uniform (ι → ZMod q)).Supp) (_ : Unit) => fourierVec τ x.1)
      = Matrix.of fun (x : (uniform (ι → ZMod q)).Supp) (_ : Unit) => fourierVec τ x.1 := by
    rw [mul_col_eq, recProj_zsupp_mulVec_fourierVec]
  have key := dbProj_mul_compress_of_recProj isFullProduct_uniform (searchDb a) (zsupp τ) hg
  rw [mul_col_eq, mul_col_eq, mul_col_eq, mul_col_eq] at key
  funext d
  exact congrFun (congrFun key d) ()

open Classical in
/-- The knowledge operator for `Υ = I` on a vector in a record subspace. -/
private lemma knowOp_self_mulVec_of_recProj (h : ρ.IsFullProduct) (L : (ι → σ) → Set (Finset ι))
    {S : Finset ι} {v : ρ.Supp → ℂ} (hv : ρ.recProj S *ᵥ v = v) (x : ρ.Supp) :
    (knowOp ρ ρ id id L *ᵥ v) x = if S ∈ L x.1 then v x else 0 := by
  have hg : ρ.recProj S * Matrix.of (fun y (_ : Unit) => v y)
      = Matrix.of (fun y (_ : Unit) => v y) := by
    rw [mul_col_eq, hv]
  have := knowOp_self_mul_of_recProj h L hg x ()
  rw [mul_col_eq] at this
  exact this

/-- An isometry preserves the squared norm of vectors. -/
private lemma qNormSq_mulVec_of_isometry {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] {U : Matrix Y X ℂ} (hU : Uᴴ * U = 1) (v : X → ℂ) :
    qNormSq (U *ᵥ v) = qNormSq v := by
  have := jNormSq_mul_of_isometry (A := Unit) hU (Matrix.of fun x (_ : Unit) => v x)
  rw [mul_col_eq] at this
  simpa [jNormSq, qNormSq] using this

/-- `C v` vanishes off the database strings that are `⊥` off `S`, for `v` in `P_S`. -/
private lemma compress_mulVec_apply_eq_zero (h : ρ.IsFullProduct) {S : Finset ι}
    {v : ρ.Supp → ℂ} (hv : ρ.recProj S *ᵥ v = v) {d : ι → Option σ} {i : ι} (hi : i ∉ S)
    (hd : d i ≠ none) : (ρ.compress *ᵥ v) d = 0 := by
  rw [← hv, Matrix.mulVec_mulVec]
  refine Finset.sum_eq_zero fun y _ => ?_
  by_cases hz : (ρ.compress * ρ.recProj S) d y = 0
  · simp only [hz, zero_mul]
  · exact absurd (compress_mul_recProj_apply_eq_none h hz hi) hd

/-- `R_S w` vanishes on the database strings with a `⊥` in `S`. -/
private lemma compressOff_mulVec_apply_eq_zero {S : Finset ι} (w : ρ.Supp → ℂ)
    {d : ι → Option σ} {i : ι} (hi : i ∈ S) (hd : d i = none) :
    (ρ.compressOff S *ᵥ w) d = 0 := by
  refine Finset.sum_eq_zero fun x _ => ?_
  have hc : ρ.compressOff S d x = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, hd])
  simp only [hc, zero_mul]

end FinDist

/-! ## The example `n = q = 2` -/

/-- `ω₂ = −1`. -/
private lemma zqRoot_two : zqRoot 2 = -1 := by
  rw [zqRoot, ← Complex.exp_pi_mul_I]
  congr 1
  push_cast
  ring

/-- The nontrivial character of `Z₂`: `ω₂^x = (−1)^x`. -/
private lemma zqChar_one_two (x : ZMod 2) : zqChar 1 x = if x = 1 then -1 else 1 := by
  have hx : x = 0 ∨ x = 1 := by
    revert x
    decide
  have h1 : (1 : ZMod 2).val = 1 := rfl
  rcases hx with rfl | rfl
  · simp [zqChar]
  · simp [zqChar, zqRoot_two, h1]

/-- The characters `|ĵ ↦ 1⟩` of `Z₂²`: `±1/2`. -/
private lemma fourierVec_single_two (j : Fin 2) (x : Fin 2 → ZMod 2) :
    FinDist.fourierVec (Pi.single j 1) x = (if x j = 1 then -1 else 1) / 2 := by
  rw [FinDist.fourierVec_eq, Finset.prod_eq_single j, Pi.single_eq_same, zqChar_one_two]
  · congr 1
    rw [Fintype.card_fin, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, zqChar_zero_left]
  · simp

/-- A sum over the support of the uniform distribution on `Z₂²`, written out. -/
private lemma sum_supp_fin_two {M : Type*} [AddCommMonoid M] (f : (Fin 2 → ZMod 2) → M) :
    ∑ x : (FinDist.uniform (Fin 2 → ZMod 2)).Supp, f x.1
      = f ![0, 0] + f ![0, 1] + f ![1, 0] + f ![1, 1] := by
  rw [FinDist.sum_supp_uniform_zq f, ← (finTwoArrowEquiv (ZMod 2)).symm.sum_comp,
    Fintype.sum_prod_type]
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := rfl
  simp only [hu, Finset.sum_pair (show (0 : ZMod 2) ≠ 1 by decide), finTwoArrowEquiv_symm_apply]
  abel

/-- The support of the character `|ĵ ↦ 1⟩` is `{j}`. -/
private lemma zsupp_single_two (j : Fin 2) : zsupp (Pi.single j (1 : ZMod 2)) = {j} := by
  ext i
  by_cases hi : i = j
  · subst hi
    simp [zsupp]
  · simp [zsupp, hi]

/-- Vectors with disjoint supports are orthogonal. -/
private lemma qNormSq_add_of_disjoint {H : Type} [Fintype H] [DecidableEq H] {u v : H → ℂ}
    (huv : ∀ x, u x = 0 ∨ v x = 0) : qNormSq (u + v) = qNormSq u + qNormSq v := by
  rw [qNormSq_def, qNormSq_def, qNormSq_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rcases huv x with hx | hx <;> simp [hx]

/-- The knowledge of a character `|ĵ ↦ 1⟩`: `−1/2` on the inputs with `xⱼ = 1`. -/
private lemma knowOp_mulVec_fourierVec_single_two (j : Fin 2)
    (x : (FinDist.uniform (Fin 2 → ZMod 2)).Supp) :
    (FinDist.knowOp (FinDist.uniform (Fin 2 → ZMod 2)) (FinDist.uniform (Fin 2 → ZMod 2)) id id
        (dbKnow (searchDb (1 : ZMod 2)))
      *ᵥ fun y : (FinDist.uniform (Fin 2 → ZMod 2)).Supp => FinDist.fourierVec (Pi.single j 1) y.1)
        x = if x.1 j = 1 then -1 / 2 else 0 := by
  rw [FinDist.knowOp_self_mulVec_of_recProj FinDist.isFullProduct_uniform _
    (FinDist.recProj_zsupp_mulVec_fourierVec _), dbKnow_searchDb, zsupp_single_two]
  simp only [Set.mem_ofPred_eq, Finset.mem_singleton, exists_eq_left, fourierVec_single_two]
  by_cases hx : x.1 j = 1 <;> simp [hx]

/-- The knowledge of a character `|ĵ ↦ 1⟩` has squared norm `1/2`. -/
private lemma qNormSq_knowOp_fourierVec_single_two (j : Fin 2) :
    qNormSq (FinDist.knowOp (FinDist.uniform (Fin 2 → ZMod 2))
        (FinDist.uniform (Fin 2 → ZMod 2)) id id (dbKnow (searchDb (1 : ZMod 2)))
      *ᵥ fun y : (FinDist.uniform (Fin 2 → ZMod 2)).Supp => FinDist.fourierVec (Pi.single j 1) y.1)
      = 1 / 2 := by
  rw [qNormSq_def]
  simp only [knowOp_mulVec_fourierVec_single_two]
  refine (sum_supp_fin_two (fun y => Complex.normSq (if y j = 1 then -1 / 2 else 0))).trans ?_
  fin_cases j <;> norm_num [Complex.normSq_div]

/-- The vector `|1̂ ↦ 1⟩ + |2̂ ↦ 1⟩` of [Bel26, Section 3.8]: the sum of the two characters of
`Z_2²` with one nonzero frequency. -/
noncomputable def belovsExampleVec : (FinDist.uniform (Fin 2 → ZMod 2)).Supp → ℂ :=
  fun x => FinDist.fourierVec (Pi.single 0 1) x.1 + FinDist.fourierVec (Pi.single 1 1) x.1

/-- In the example, the knowledge is `‖Υ⁺ψ‖² = 3/2`: `Υ⁺ψ = −½(|10⟩ + |01⟩ + 2|11⟩)`. -/
theorem qNormSq_knowOp_belovsExampleVec :
    qNormSq (FinDist.knowOp (FinDist.uniform (Fin 2 → ZMod 2)) (FinDist.uniform (Fin 2 → ZMod 2))
      id id (dbKnow (searchDb (1 : ZMod 2))) *ᵥ belovsExampleVec) = 3 / 2 := by
  rw [show belovsExampleVec = (fun x : (FinDist.uniform (Fin 2 → ZMod 2)).Supp =>
      FinDist.fourierVec (Pi.single 0 1) x.1) + (fun x : (FinDist.uniform (Fin 2 → ZMod 2)).Supp =>
      FinDist.fourierVec (Pi.single 1 1) x.1) from rfl, Matrix.mulVec_add, qNormSq_def]
  simp only [Pi.add_apply, knowOp_mulVec_fourierVec_single_two]
  refine (sum_supp_fin_two (fun y => Complex.normSq ((if y 0 = 1 then -1 / 2 else 0)
    + (if y 1 = 1 then -1 / 2 else 0)))).trans ?_
  norm_num [Complex.normSq_div]

/-- In the example, the progress measure is `‖Π R ψ‖² = 1`: `Π R ψ = −(|1⊥⟩ + |⊥1⟩)/√2`. -/
theorem qNormSq_dbProj_compress_belovsExampleVec :
    qNormSq (dbProj (searchDb (1 : ZMod 2))
      *ᵥ ((FinDist.uniform (Fin 2 → ZMod 2)).compress *ᵥ belovsExampleVec)) = 1 := by
  have hv := fun j : Fin 2 => FinDist.recProj_zsupp_mulVec_fourierVec (ι := Fin 2) (q := 2)
    (Pi.single j 1)
  have hdisj : ∀ d, (dbProj (searchDb (1 : ZMod 2))
        *ᵥ ((FinDist.uniform (Fin 2 → ZMod 2)).compress
          *ᵥ fun x : (FinDist.uniform (Fin 2 → ZMod 2)).Supp =>
            FinDist.fourierVec (Pi.single 0 1) x.1)) d = 0
      ∨ (dbProj (searchDb (1 : ZMod 2))
        *ᵥ ((FinDist.uniform (Fin 2 → ZMod 2)).compress
          *ᵥ fun x : (FinDist.uniform (Fin 2 → ZMod 2)).Supp =>
            FinDist.fourierVec (Pi.single 1 1) x.1)) d = 0 := by
    intro d
    by_cases hd : d 0 = none
    · left
      rw [FinDist.dbProj_searchDb_compress_fourierVec]
      exact FinDist.compressOff_mulVec_apply_eq_zero _ (by simp [zsupp_single_two]) hd
    · right
      rw [dbProj, Matrix.mulVec_diagonal,
        FinDist.compress_mulVec_apply_eq_zero FinDist.isFullProduct_uniform (hv 1)
          (by simp [zsupp_single_two]) hd, mul_zero]
  rw [show belovsExampleVec = (fun x : (FinDist.uniform (Fin 2 → ZMod 2)).Supp =>
      FinDist.fourierVec (Pi.single 0 1) x.1) + (fun x : (FinDist.uniform (Fin 2 → ZMod 2)).Supp =>
      FinDist.fourierVec (Pi.single 1 1) x.1) from rfl, Matrix.mulVec_add, Matrix.mulVec_add,
    qNormSq_add_of_disjoint hdisj, FinDist.dbProj_searchDb_compress_fourierVec,
    FinDist.dbProj_searchDb_compress_fourierVec,
    FinDist.qNormSq_mulVec_of_isometry (FinDist.conjTranspose_compressOff_mul_compressOff _ _),
    FinDist.qNormSq_mulVec_of_isometry (FinDist.conjTranspose_compressOff_mul_compressOff _ _),
    qNormSq_knowOp_fourierVec_single_two, qNormSq_knowOp_fourierVec_single_two]
  norm_num

/-- **Knowledge and the progress measure differ** [Bel26, Section 3.8]: for `n = q = 2`, the
vector `|1̂ ↦ 1⟩ + |2̂ ↦ 1⟩` has knowledge `‖Υ⁺ψ‖² = 3/2` but progress `‖Π R ψ‖² = 1`. -/
theorem knowledge_ne_progress_example :
    qNormSq (FinDist.knowOp (FinDist.uniform (Fin 2 → ZMod 2)) (FinDist.uniform (Fin 2 → ZMod 2))
        id id (dbKnow (searchDb (1 : ZMod 2))) *ᵥ belovsExampleVec)
      ≠ qNormSq (dbProj (searchDb (1 : ZMod 2))
        *ᵥ ((FinDist.uniform (Fin 2 → ZMod 2)).compress *ᵥ belovsExampleVec)) := by
  rw [qNormSq_knowOp_belovsExampleVec, qNormSq_dbProj_compress_belovsExampleVec]
  norm_num

end QuantumQueryComplexity
