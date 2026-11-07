import QuantumQueryComplexity.Quantum.Records.CompressedKnowledge
import QuantumQueryComplexity.Quantum.ZqSimulation

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The compressed oracle applied to Search [Ham25, Proposition 42]

The validation of the compressed-oracle progress measures: find a position holding the symbol `a`
in a uniformly random string `x ∈ Z_qⁿ`, with phase queries over `Z_q`. The progress measure is
`Δₜ = ‖Π C Ψₜ‖` (`searchProgress`), where `Π` projects onto the databases recording `a`
(`searchDb a`). Following [Ham25, Proposition 42]:

* **Initial condition**: `Δ₀ = 0` (`searchProgress_zero`).
* **Progress evolution**: the commutator of the recording oracle with `Π` has norm at most
  `√(10/q)` (`jNorm_recOracle_comm_searchDb_le`), so by the transfer lemma
  (`FinDist.jNorm_dbProj_compress_jointZqState_le`) `Δₜ ≤ t √(10/q)` (`searchProgress_le`).
* **Final condition**: the average success probability `p` satisfies `√p ≤ Δₜ + √(2/q)`
  (`sqrt_avgZqSuccessProb_search_le`).

Hence `p ≤ (√10 t + √2)²/q` with phase queries (`avgZqSuccessProb_search_le`) and
`p ≤ (2√10 t + √2)²/q` with value queries, through the simulation at two phase queries per query
(`avgSuccessProb_search_le`). Average success `2/3` needs `t ≥ √(q/15) − √(1/5)` phase queries
[Ham25, Proposition 42] (`le_of_avgZqSuccessProb_search`), or half that many value queries
(`le_of_avgSuccessProb_search`).

Hamoudi's proof bounds `‖Π O_rec (I − Π) ψ‖`; the commutator adds the orthogonal term
`(I − Π) O_rec Π ψ`, whose norm obeys the same bound, so the constant `√(10/q)` is unchanged.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix FinDist

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q]
variable {O W : Type} [Fintype W] [DecidableEq W]

/-! ## Single-coordinate operators on strings -/

section SingleCoord

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The tensor product `⊗ⱼ Nⱼ` of operators on the coordinates of a string. -/
private def tensorMat (N : ι → Matrix κ κ ℂ) : Matrix (ι → κ) (ι → κ) ℂ :=
  fun d e => ∏ j, N j (d j) (e j)

private lemma tensorMat_mul (N N' : ι → Matrix κ κ ℂ) :
    tensorMat N * tensorMat N' = tensorMat fun j => N j * N' j := by
  ext d e
  simp only [tensorMat, Matrix.mul_apply, Fintype.prod_sum, Finset.prod_mul_distrib]

private lemma tensorMat_one : tensorMat (fun _ : ι => (1 : Matrix κ κ ℂ)) = 1 := by
  ext d e
  simp only [tensorMat, Matrix.one_apply, Fintype.prod_boole, funext_iff]

private lemma conjTranspose_tensorMat (N : ι → Matrix κ κ ℂ) :
    (tensorMat N)ᴴ = tensorMat fun j => (N j)ᴴ := by
  ext d e
  simp only [tensorMat, Matrix.conjTranspose_apply, star_prod]

/-- A diagonal operator reading one coordinate is a single-coordinate operator. -/
private lemma diagonal_eq_tensorMat (i : ι) (g : κ → ℂ) :
    Matrix.diagonal (fun e : ι → κ => g (e i))
      = tensorMat fun j => if j = i then Matrix.diagonal g else 1 := by
  ext d e
  by_cases hde : d = e
  · subst hde
    rw [Matrix.diagonal_apply_eq, tensorMat, Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  · rw [Matrix.diagonal_apply_ne _ hde]
    obtain ⟨j, hj⟩ : ∃ j, d j ≠ e j := by
      by_contra h
      push Not at h
      exact hde (funext h)
    refine (Finset.prod_eq_zero (Finset.mem_univ j) ?_).symm
    by_cases hji : j = i
    · subst hji
      simp [Matrix.diagonal_apply_ne _ hj]
    · simp [hji, Matrix.one_apply_ne hj]

/-- A single-coordinate operator acts by summing over the value of that coordinate. -/
private lemma tensorMat_single_mulVec (i : ι) (M : Matrix κ κ ℂ) (v : (ι → κ) → ℂ)
    (d : ι → κ) :
    (tensorMat (fun j => if j = i then M else 1) *ᵥ v) d
      = ∑ u, M (d i) u * v (Function.update d i u) := by
  have hT : ∀ u, tensorMat (fun j => if j = i then M else 1) d (Function.update d i u)
      = M (d i) u := by
    intro u
    rw [tensorMat, Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      rw [ite_eq_right hj, Function.update_of_ne hj, Matrix.one_apply_eq]
    · simp
  have h0 : ∀ e ∈ Finset.univ, e ∉ Finset.univ.image (Function.update d i) →
      tensorMat (fun j => if j = i then M else 1) d e * v e = 0 := by
    intro e _ he
    obtain ⟨j, hji, hj⟩ : ∃ j, j ≠ i ∧ d j ≠ e j := by
      by_contra h
      push Not at h
      refine he (Finset.mem_image.mpr ⟨e i, Finset.mem_univ _, funext fun j => ?_⟩)
      by_cases hji : j = i
      · subst hji
        simp
      · simp [hji, h j hji]
    rw [tensorMat, Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hji, Matrix.one_apply_ne hj]),
      zero_mul]
  simp only [Matrix.mulVec, dotProduct]
  rw [← Finset.sum_subset (Finset.subset_univ _) h0,
    Finset.sum_image fun u _ u' _ h => Function.update_injective d i h]
  simp only [hT]

/-- A tensor product of unitaries is unitary. -/
private lemma tensorMat_mem_unitaryGroup (N : ι → Matrix κ κ ℂ)
    (hN : ∀ j, N j ∈ Matrix.unitaryGroup κ ℂ) : tensorMat N ∈ Matrix.unitaryGroup (ι → κ) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, conjTranspose_tensorMat,
    tensorMat_mul, ← tensorMat_one]
  congr 1
  funext j
  have h := Matrix.mem_unitaryGroup_iff.mp (hN j)
  rwa [Matrix.star_eq_conjTranspose] at h

/-- Masking coordinate `i` of a tensor product: `D (⊗ⱼ Nⱼ) = (⊗_{j ≠ i} Nⱼ) (D Nᵢ)`, where `D` is
diagonal and reads coordinate `i`. -/
private lemma diagonal_mul_tensorMat (i : ι) (g : κ → ℂ) (N : ι → Matrix κ κ ℂ) :
    Matrix.diagonal (fun e : ι → κ => g (e i)) * tensorMat N
      = tensorMat (fun j => if j = i then 1 else N j)
        * tensorMat (fun j => if j = i then Matrix.diagonal g * N i else 1) := by
  rw [diagonal_eq_tensorMat, tensorMat_mul, tensorMat_mul]
  congr 1
  funext j
  by_cases hji : j = i
  · subst hji
    simp
  · simp [hji]

/-- Reindexing a sum by changing one coordinate. -/
private lemma sum_ite_update (i : ι) (u w : κ) (g : (ι → κ) → ℝ) :
    ∑ d : ι → κ, (if d i = u then g (Function.update d i w) else 0)
      = ∑ e : ι → κ, (if e i = w then g e else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun d => Function.update d i w) (fun e => Function.update e i u)
    ?_ ?_ ?_ ?_ ?_
  · intro d _
    simp
  · intro e _
    simp
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    simp [← hd]
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    simp [← he]
  · intro d _
    rfl

private lemma sum_ite_sum_update (i : ι) (u : κ) (g : (ι → κ) → ℝ) :
    ∑ d : ι → κ, (if d i = u then ∑ v, g (Function.update d i v) else 0) = ∑ e, g e := by
  have h : ∀ d : ι → κ, (if d i = u then ∑ v, g (Function.update d i v) else 0)
      = ∑ v, if d i = u then g (Function.update d i v) else 0 := fun d => by
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun d _ => h d, Finset.sum_comm]
  simp_rw [sum_ite_update]
  rw [Finset.sum_comm]
  simp

private lemma sum_eq_sum_sum_ite (i : ι) (F : (ι → κ) → ℝ) :
    ∑ d, F d = ∑ u : κ, ∑ d : ι → κ, (if d i = u then F d else 0) := by
  rw [Finset.sum_comm]
  simp

/-- Cauchy–Schwarz for finite sums of complex numbers. -/
private lemma normSq_sum_mul_le {κ' : Type} [Fintype κ'] [DecidableEq κ'] (z w : κ' → ℂ) :
    Complex.normSq (∑ v, z v * w v)
      ≤ (∑ v, Complex.normSq (z v)) * ∑ v, Complex.normSq (w v) := by
  have h := qInner_norm_le (fun v => star (z v)) w
  simp only [qInner_def, qNormSq_def, Complex.star_def, Complex.normSq_conj, Complex.conj_conj]
    at h
  rw [Complex.normSq_eq_norm_sq]
  calc ‖∑ v, z v * w v‖ ^ 2
      ≤ (Real.sqrt (∑ v, Complex.normSq (z v)) * Real.sqrt (∑ v, Complex.normSq (w v))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by
        rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun v _ => Complex.normSq_nonneg _),
          Real.sq_sqrt (Finset.sum_nonneg fun v _ => Complex.normSq_nonneg _)]

/-- **The masked single-coordinate bound**: if `φ` vanishes where coordinate `i` holds `a`, the
part of `Mφ` where coordinate `i` holds `a` has squared norm at most
`∑_{v ≠ a} |M(a, v)|² ‖φ‖²`. -/
private lemma sum_normSq_single_le (M : Matrix κ κ ℂ) (i : ι) (a : κ) (φ : (ι → κ) → ℂ)
    (hφ : ∀ d, d i = a → φ d = 0) :
    ∑ d : ι → κ, (if d i = a then
        Complex.normSq (∑ v, M (d i) v * φ (Function.update d i v)) else 0)
      ≤ (∑ v, if v = a then 0 else Complex.normSq (M a v)) * ∑ d, Complex.normSq (φ d) := by
  set K := ∑ v, if v = a then 0 else Complex.normSq (M a v)
  have hpt : ∀ d : ι → κ, (if d i = a then
        Complex.normSq (∑ v, M (d i) v * φ (Function.update d i v)) else 0)
      ≤ K * (if d i = a then ∑ v, Complex.normSq (φ (Function.update d i v)) else 0) := by
    intro d
    split_ifs with hd
    · have hsum : ∑ v, M (d i) v * φ (Function.update d i v)
          = ∑ v, (if v = a then 0 else M a v) * φ (Function.update d i v) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases hv : v = a
        · rw [hv, ← hd, Function.update_eq_self, hφ d hd]
          simp
        · simp [hv, hd]
      rw [hsum]
      refine (normSq_sum_mul_le _ _).trans (le_of_eq ?_)
      congr 1
      refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs <;> simp
    · simp
  calc _ ≤ ∑ d : ι → κ, K * (if d i = a then
          ∑ v, Complex.normSq (φ (Function.update d i v)) else 0) :=
        Finset.sum_le_sum fun d _ => hpt d
    _ = K * ∑ d, Complex.normSq (φ d) := by
        rw [← Finset.mul_sum, sum_ite_sum_update i a (fun e => Complex.normSq (φ e))]

/-- **The commutator bound for one column** [Ham25, Proposition 42]: for a single-coordinate
operator `M` on coordinate `i` and the projection onto the strings containing `a`, split a vector
into its parts `ψin` on and `ψout` off these strings. The commutator applied to it is
`−M ψout` on the strings containing `a` and `M ψin` off them, and its squared norm is at most
`K ‖ψ‖²` when `K` bounds `∑_{v ≠ a} |M(a, v)|²` and `∑_{u ≠ a} |M(u, a)|²`. -/
private lemma comm_col_le (M : Matrix κ κ ℂ) (i : ι) (a : κ) (ψin ψout X : (ι → κ) → ℂ)
    (hin : ∀ d, (∀ j, d j ≠ a) → ψin d = 0) (hout : ∀ d j, d j = a → ψout d = 0)
    (hX1 : ∀ d, (∃ j, d j = a) → X d = -∑ v, M (d i) v * ψout (Function.update d i v))
    (hX2 : ∀ d, (∀ j, d j ≠ a) → X d = ∑ v, M (d i) v * ψin (Function.update d i v))
    {K : ℝ} (hK1 : ∑ v, (if v = a then 0 else Complex.normSq (M a v)) ≤ K)
    (hK2 : ∑ u, (if u = a then 0 else Complex.normSq (M u a)) ≤ K) :
    ∑ d, Complex.normSq (X d)
      ≤ K * ∑ d, (Complex.normSq (ψin d) + Complex.normSq (ψout d)) := by
  set F1 : (ι → κ) → ℝ := fun d => if d i = a then
    Complex.normSq (∑ v, M (d i) v * ψout (Function.update d i v)) else 0
  set F2 : (ι → κ) → ℝ := fun d => if d i = a then 0 else
    Complex.normSq (M (d i) a) * Complex.normSq (ψin (Function.update d i a))
  have hpt : ∀ d, Complex.normSq (X d) ≤ F1 d + F2 d := by
    intro d
    by_cases hS : ∃ j, d j = a
    · rw [hX1 d hS, Complex.normSq_neg]
      by_cases hd : d i = a
      · simp [F1, F2, hd]
      · obtain ⟨j, hj⟩ := hS
        have hji : j ≠ i := fun h => hd (h ▸ hj)
        have h0 : ∑ v, M (d i) v * ψout (Function.update d i v) = 0 :=
          Finset.sum_eq_zero fun v _ => by
            rw [hout _ j (by rw [Function.update_of_ne hji]; exact hj), mul_zero]
        rw [h0, map_zero]
        simp only [F1, F2, hd, ↓reduceIte, zero_add]
        exact mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
    · push Not at hS
      rw [hX2 d hS]
      have hd : d i ≠ a := hS i
      have h1 : ∑ v, M (d i) v * ψin (Function.update d i v)
          = M (d i) a * ψin (Function.update d i a) := by
        refine Finset.sum_eq_single a (fun v _ hv => ?_) (by simp)
        rw [hin _ (fun j => ?_), mul_zero]
        by_cases hji : j = i
        · subst hji
          simp [hv]
        · rw [Function.update_of_ne hji]
          exact hS j
      rw [h1, Complex.normSq_mul]
      simp [F1, F2, hd]
  have hK0 : 0 ≤ K :=
    (Finset.sum_nonneg fun v _ => by split_ifs <;> simp [Complex.normSq_nonneg]).trans hK1
  have hF1 : ∑ d, F1 d ≤ K * ∑ d, Complex.normSq (ψout d) :=
    (sum_normSq_single_le M i a ψout fun d hd => hout d i hd).trans
      (mul_le_mul_of_nonneg_right hK1 (Finset.sum_nonneg fun d _ => Complex.normSq_nonneg _))
  have hF2 : ∑ d, F2 d ≤ K * ∑ d, Complex.normSq (ψin d) := by
    have h : ∑ d, F2 d = (∑ u, if u = a then 0 else Complex.normSq (M u a))
        * ∑ e : ι → κ, (if e i = a then Complex.normSq (ψin e) else 0) := by
      rw [sum_eq_sum_sum_ite i, Finset.sum_mul]
      refine Finset.sum_congr rfl fun u _ => ?_
      have h' : ∀ d : ι → κ, (if d i = u then F2 d else 0)
          = (if u = a then 0 else Complex.normSq (M u a))
            * (if d i = u then Complex.normSq (ψin (Function.update d i a)) else 0) := by
        intro d
        by_cases hdu : d i = u
        · simp only [F2, hdu, ↓reduceIte]
          split_ifs <;> simp
        · simp [hdu]
      rw [Finset.sum_congr rfl fun d _ => h' d, ← Finset.mul_sum,
        sum_ite_update i u a (fun e => Complex.normSq (ψin e))]
    rw [h]
    refine mul_le_mul hK2 ?_
      (Finset.sum_nonneg fun e _ => by split_ifs <;> simp [Complex.normSq_nonneg]) hK0
    exact Finset.sum_le_sum fun e _ => by split_ifs <;> simp [Complex.normSq_nonneg]
  calc ∑ d, Complex.normSq (X d) ≤ ∑ d, (F1 d + F2 d) := Finset.sum_le_sum fun d _ => hpt d
    _ ≤ K * ∑ d, Complex.normSq (ψout d) + K * ∑ d, Complex.normSq (ψin d) := by
        rw [Finset.sum_add_distrib]
        exact add_le_add hF1 hF2
    _ = K * ∑ d, (Complex.normSq (ψin d) + Complex.normSq (ψout d)) := by
        rw [Finset.sum_add_distrib]
        ring

end SingleCoord


/-! ## The recording oracle for uniform inputs and the phase oracle -/

section Uniform

/-- The conditional-mean amplitudes of the uniform distribution are `1/√q`. -/
private lemma meanVec_uniform (i : ι) (b : ZMod q) :
    (uniform (ι → ZMod q)).meanVec i b = ((Real.sqrt (1 / q) : ℝ) : ℂ) := by
  rw [FinDist.meanVec, marg_uniform_zq]

private lemma normSq_sqrt_inv_q : Complex.normSq ((Real.sqrt (1 / q) : ℝ) : ℂ) = 1 / q := by
  rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by positivity)]

private lemma norm_zqChar (c x : ZMod q) : ‖zqChar c x‖ = 1 := by
  rw [zqChar, norm_pow, norm_zqRoot, one_pow]

private lemma normSq_zqChar (c x : ZMod q) : Complex.normSq (zqChar c x) = 1 := by
  rw [Complex.normSq_eq_norm_sq, norm_zqChar, one_pow]

/-- The recording oracle acts on each workspace column `p` by `R Φ_p R`, where `Φ_p` is the
diagonal phase of the column. -/
private lemma recOracle_phase_apply (f : JVec (ι → Option (ZMod q)) (QBasis ι (ZMod q) W))
    (d : ι → Option (ZMod q)) (p : QBasis ι (ZMod q) W) :
    (uniform (ι → ZMod q)).recOracle phaseZqOracleMat 0 f d p
      = (((uniform (ι → ZMod q)).recOpAll
          * Matrix.diagonal (fun e => phaseZqSign (dbRead 0 e) p)
          * (uniform (ι → ZMod q)).recOpAll) *ᵥ (fun e => f e p)) d := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [FinDist.recOracle, jOracle, phaseZqOracleMat, Matrix.mul_apply, Matrix.mulVec,
    dotProduct]
  simp [Matrix.diagonal_apply]

private lemma zqChar_zero_right (c : ZMod q) : zqChar c 0 = 1 := by
  rw [zqChar_comm, zqChar_zero_left]

/-- The single-coordinate operator `Mᵢ = Rᵢ Φ_c Rᵢ` of the recording oracle on a query
`(i, c)`, where `Φ_c` multiplies `|b⟩` by `ω_q^{cb}` and fixes `|⊥⟩`. -/
private noncomputable def recPhase (i : ι) (c : ZMod q) :
    Matrix (Option (ZMod q)) (Option (ZMod q)) ℂ :=
  (uniform (ι → ZMod q)).recOp i
    * Matrix.diagonal (fun u : Option (ZMod q) => zqChar c (u.getD 0))
    * (uniform (ι → ZMod q)).recOp i

private lemma recPhase_some_none (i : ι) {c : ZMod q} (hc : c ≠ 0) (a : ZMod q) :
    recPhase i c (some a) none = ((Real.sqrt (1 / q) : ℝ) : ℂ) * zqChar c a := by
  rw [recPhase, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Fintype.sum_option, FinDist.recOp, meanVec_uniform,
    Option.getD_some, Option.getD_none]
  set s : ℂ := ((Real.sqrt (1 / q) : ℝ) : ℂ)
  have h : ∀ x, ((if a = x then 1 else 0) - s * s) * zqChar c x * s
      = (if a = x then s * zqChar c x else 0) - s * s * s * zqChar c x := by
    intro x
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    ← Finset.mul_sum, sum_zqChar]
  simp [hc]

private lemma recPhase_some_some (i : ι) {c : ZMod q} (hc : c ≠ 0) {a x : ZMod q} (hax : a ≠ x) :
    recPhase i c (some a) (some x)
      = ((Real.sqrt (1 / q) : ℝ) : ℂ) * ((Real.sqrt (1 / q) : ℝ) : ℂ)
        * (1 - zqChar c a - zqChar c x) := by
  rw [recPhase, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Fintype.sum_option, FinDist.recOp, meanVec_uniform,
    Option.getD_some, Option.getD_none, zqChar_zero_right]
  set s : ℂ := ((Real.sqrt (1 / q) : ℝ) : ℂ)
  have h : ∀ y, ((if a = y then 1 else 0) - s * s) * zqChar c y * ((if y = x then 1 else 0) - s * s)
      = (if a = y then -(s * s) * zqChar c y else 0) + (if y = x then -(s * s) * zqChar c y else 0)
        + s * s * s * s * zqChar c y := by
    intro y
    split_ifs with h1 h2 h2
    · exact absurd (h1.trans h2) hax
    all_goals ring
  rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq', ← Finset.mul_sum, sum_zqChar]
  simp only [Finset.mem_univ, ↓reduceIte, hc, mul_zero, add_zero]
  ring

/-- `Mᵢ` is symmetric, since `Rᵢ` is real symmetric and `Φ_c` diagonal. -/
private lemma recPhase_symm (i : ι) (c : ZMod q) (u v : Option (ZMod q)) :
    recPhase i c u v = recPhase i c v u := by
  have hR : ((uniform (ι → ZMod q)).recOp i)ᵀ = (uniform (ι → ZMod q)).recOp i := by
    ext u v
    cases u <;> cases v <;> simp [FinDist.recOp, eq_comm, mul_comm]
  have hM : (recPhase i c)ᵀ = recPhase i c := by
    rw [recPhase, Matrix.transpose_mul, Matrix.transpose_mul, hR, Matrix.diagonal_transpose,
      Matrix.mul_assoc]
  have h := congrFun₂ hM v u
  rwa [Matrix.transpose_apply] at h

/-- **The off-diagonal weight of `Mᵢ`** [Ham25, Proposition 42]: `∑_{v ≠ a} |Mᵢ(a, v)|² ≤ 10/q`. -/
private lemma sum_normSq_recPhase_le (i : ι) (c a : ZMod q) :
    ∑ v, (if v = some a then 0 else Complex.normSq (recPhase i c (some a) v)) ≤ 10 / q := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  by_cases hc : c = 0
  · have h1 : recPhase i c = 1 := by
      have hD : Matrix.diagonal (fun u : Option (ZMod q) => zqChar c (u.getD 0)) = 1 := by
        simp only [hc, zqChar_zero_left]
        exact Matrix.diagonal_one
      rw [recPhase, hD, Matrix.mul_one, FinDist.recOp_mul_self]
    have h0 : ∀ v, (if v = some a then 0 else Complex.normSq (recPhase i c (some a) v)) = 0 := by
      intro v
      split_ifs with hv
      · rfl
      · rw [h1, Matrix.one_apply_ne (Ne.symm hv), map_zero]
    rw [Finset.sum_congr rfl fun v _ => h0 v, Finset.sum_const_zero]
    positivity
  · rw [Fintype.sum_option, ite_eq_right (Option.some_ne_none a).symm,
      recPhase_some_none i hc, Complex.normSq_mul, normSq_sqrt_inv_q, normSq_zqChar, mul_one]
    have hx : ∀ x : ZMod q,
        (if some x = some a then 0 else Complex.normSq (recPhase i c (some a) (some x)))
          ≤ 9 / (q : ℝ) ^ 2 := by
      intro x
      split_ifs with hx
      · positivity
      · have hax : a ≠ x := fun h => hx (by rw [h])
        rw [recPhase_some_some i hc hax, Complex.normSq_mul, Complex.normSq_mul,
          normSq_sqrt_inv_q, Complex.normSq_eq_norm_sq (1 - _ - _)]
        have h3 : ‖1 - zqChar c a - zqChar c x‖ ≤ 3 := by
          calc ‖1 - zqChar c a - zqChar c x‖ ≤ ‖1 - zqChar c a‖ + ‖zqChar c x‖ := norm_sub_le _ _
            _ ≤ ‖(1 : ℂ)‖ + ‖zqChar c a‖ + ‖zqChar c x‖ := by gcongr; exact norm_sub_le _ _
            _ = 3 := by rw [norm_one, norm_zqChar, norm_zqChar]; norm_num
        have h9 : ‖1 - zqChar c a - zqChar c x‖ ^ 2 ≤ 9 := by
          nlinarith [norm_nonneg (1 - zqChar c a - zqChar c x)]
        calc 1 / (q : ℝ) * (1 / q) * ‖1 - zqChar c a - zqChar c x‖ ^ 2
            ≤ 1 / (q : ℝ) * (1 / q) * 9 := by gcongr
          _ = 9 / (q : ℝ) ^ 2 := by ring
    calc 1 / (q : ℝ) + ∑ x : ZMod q,
          (if some x = some a then 0 else Complex.normSq (recPhase i c (some a) (some x)))
        ≤ 1 / q + ∑ _x : ZMod q, 9 / (q : ℝ) ^ 2 := by gcongr with x; exact hx x
      _ = 10 / q := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
        field_simp
        ring
/-- For a column `(some i, some c, w)`, the recording oracle is the single-coordinate operator
`Mᵢ` on coordinate `i`, using `Rⱼ² = 1` for `j ≠ i`. -/
private lemma recOracle_phase_apply_some
    (f : JVec (ι → Option (ZMod q)) (QBasis ι (ZMod q) W)) (d : ι → Option (ZMod q)) (i : ι)
    (c : ZMod q) (w : W) :
    (uniform (ι → ZMod q)).recOracle phaseZqOracleMat 0 f d (some i, some c, w)
      = ∑ v, recPhase i c (d i) v * f (Function.update d i v) (some i, some c, w) := by
  have hD : Matrix.diagonal (fun e : ι → Option (ZMod q) =>
        phaseZqSign (W := W) (dbRead 0 e) (some i, some c, w))
      = tensorMat fun j => if j = i then
          Matrix.diagonal (fun u : Option (ZMod q) => zqChar c (u.getD 0)) else 1 :=
    diagonal_eq_tensorMat i (fun u : Option (ZMod q) => zqChar c (u.getD 0))
  have hR : (uniform (ι → ZMod q)).recOpAll = tensorMat (uniform (ι → ZMod q)).recOp := rfl
  have hT : (uniform (ι → ZMod q)).recOpAll
        * Matrix.diagonal (fun e : ι → Option (ZMod q) =>
            phaseZqSign (W := W) (dbRead 0 e) (some i, some c, w))
        * (uniform (ι → ZMod q)).recOpAll
      = tensorMat fun j => if j = i then recPhase i c else 1 := by
    rw [hD, hR, tensorMat_mul, tensorMat_mul]
    congr 1
    funext j
    by_cases hji : j = i
    · subst hji
      simp [recPhase]
    · simp [hji, FinDist.recOp_mul_self]
  rw [recOracle_phase_apply, hT, tensorMat_single_mulVec]

/-- On the columns without a query (no index or no answer), the recording oracle is the
identity. -/
private lemma recOracle_phase_apply_of_eq_one
    (f : JVec (ι → Option (ZMod q)) (QBasis ι (ZMod q) W)) (d : ι → Option (ZMod q))
    (p : QBasis ι (ZMod q) W) (hp : ∀ b : ι → ZMod q, phaseZqSign b p = 1) :
    (uniform (ι → ZMod q)).recOracle phaseZqOracleMat 0 f d p = f d p := by
  have hD : Matrix.diagonal (fun e : ι → Option (ZMod q) => phaseZqSign (dbRead 0 e) p) = 1 := by
    simp only [hp]
    exact Matrix.diagonal_one
  rw [recOracle_phase_apply, hD, Matrix.mul_one, FinDist.recOpAll_mul_self, Matrix.one_mulVec]

end Uniform

section DbProj

variable {σ B : Type} [Fintype σ] [DecidableEq σ] [Fintype B]

private lemma mem_searchDb {a : σ} {d : ι → Option σ} : d ∈ searchDb a ↔ ∃ j, d j = some a :=
  Iff.rfl

private lemma dbProj_mul_apply_of_mem {P : Set (ι → Option σ)} (g : JVec (ι → Option σ) B)
    {d : ι → Option σ} (hd : d ∈ P) (p : B) : (dbProj P * g) d p = g d p := by
  classical
  simp [dbProj, Matrix.diagonal_mul, hd]

private lemma dbProj_mul_apply_of_notMem {P : Set (ι → Option σ)} (g : JVec (ι → Option σ) B)
    {d : ι → Option σ} (hd : d ∉ P) (p : B) : (dbProj P * g) d p = 0 := by
  classical
  simp [dbProj, Matrix.diagonal_mul, hd]

end DbProj

/-! ## Tools for the final condition -/

section Final

variable {σ B : Type} [Fintype σ] [DecidableEq σ] [Fintype B] [DecidableEq B]

private lemma goodMask_add {Ω : Type} [Fintype Ω] [DecidableEq Ω] (ρ : FinDist Ω) {O' : Type}
    (rd : B → O') (Good : Ω → O' → Prop) [∀ ω, DecidablePred (Good ω)] (f g : JVec ρ.Supp B) :
    ρ.goodMask rd Good (f + g) = ρ.goodMask rd Good f + ρ.goodMask rd Good g := by
  ext x b
  simp only [FinDist.goodMask, Matrix.add_apply]
  split_ifs <;> simp

private lemma jNorm_goodMask_le {Ω : Type} [Fintype Ω] [DecidableEq Ω] (ρ : FinDist Ω)
    {O' : Type} (rd : B → O') (Good : Ω → O' → Prop) [∀ ω, DecidablePred (Good ω)]
    (f : JVec ρ.Supp B) : jNorm (ρ.goodMask rd Good f) ≤ jNorm f := by
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun x _ => ?_)
  rw [qNormSq_def, qNormSq_def]
  refine Finset.sum_le_sum fun b _ => ?_
  simp only [FinDist.goodMask]
  split_ifs <;> simp [Complex.normSq_nonneg]

open scoped MatrixOrder ComplexOrder in
/-- `C†` is a contraction, since `C` is an isometry. -/
private lemma jNorm_conjTranspose_compress_mul_le (ρ : FinDist (ι → σ))
    (g : JVec (ι → Option σ) B) : jNorm (ρ.compressᴴ * g) ≤ jNorm g := by
  set C := ρ.compress
  have hC : Cᴴ * C = 1 := ρ.conjTranspose_compress_mul_compress
  have hle : (Cᴴ)ᴴ * Cᴴ ≤ ((1 : ℝ) : ℂ) • (1 : Matrix (ι → Option σ) (ι → Option σ) ℂ) := by
    rw [Matrix.conjTranspose_conjTranspose, Complex.ofReal_one, one_smul, Matrix.le_iff]
    have h : 1 - C * Cᴴ = (1 - C * Cᴴ)ᴴ * (1 - C * Cᴴ) := by
      have hP : C * Cᴴ * (C * Cᴴ) = C * Cᴴ := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc Cᴴ, hC, Matrix.one_mul]
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hP]
      simp
    rw [h]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have := jNormSq_mul_le_smul hle g
  rw [one_mul] at this
  exact Real.sqrt_le_sqrt this

/-- The entries of `C† h`: `(C† h)(x) = (R h)(x)`, reading the input `x` as a full database. -/
private lemma conjTranspose_compress_mul_apply (ρ : FinDist (ι → σ))
    (h : JVec (ι → Option σ) B) (x : ρ.Supp) (p : B) :
    (ρ.compressᴴ * h) x p = (ρ.recOpAll *ᵥ fun d => h d p) (fun j => some (x.1 j)) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    FinDist.compress_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  congr 1
  exact ρ.recOpAll_isHermitian.apply _ d

/-- Inputs are databases without `⊥`: a sum over the support is at most the sum over all
databases. -/
private lemma sum_supp_le_sum_db (ρ : FinDist (ι → σ)) (F : (ι → Option σ) → ℝ)
    (hF : ∀ e, 0 ≤ F e) : ∑ x : ρ.Supp, F (fun j => some (x.1 j)) ≤ ∑ e, F e := by
  let emb : ρ.Supp ↪ (ι → Option σ) := ⟨fun x j => some (x.1 j), fun x y h =>
    Subtype.ext (funext fun j => Option.some_injective _ (congrFun h j))⟩
  calc ∑ x : ρ.Supp, F (fun j => some (x.1 j)) = ∑ e ∈ Finset.univ.map emb, F e :=
        (Finset.sum_map Finset.univ emb F).symm
    _ ≤ ∑ e, F e :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun e _ _ => hF e

end Final

/-- The off-diagonal weight of row `a` of `Rᵢ` for uniform inputs:
`∑_{v ≠ a} |Rᵢ(a, v)|² ≤ 2/q`. -/
private lemma sum_normSq_recOp_le (i : ι) (a : ZMod q) :
    ∑ v, (if v = some a then 0
      else Complex.normSq ((uniform (ι → ZMod q)).recOp i (some a) v)) ≤ 2 / q := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  rw [Fintype.sum_option, ite_eq_right (Option.some_ne_none a).symm]
  have hx : ∀ x : ZMod q, (if some x = some a then 0
      else Complex.normSq ((uniform (ι → ZMod q)).recOp i (some a) (some x)))
        ≤ 1 / (q : ℝ) ^ 2 := by
    intro x
    split_ifs with hx
    · positivity
    · have hax : a ≠ x := fun h => hx (by rw [h])
      simp only [FinDist.recOp, meanVec_uniform, hax, ↓reduceIte, zero_sub, Complex.normSq_neg,
        Complex.normSq_mul, normSq_sqrt_inv_q]
      apply le_of_eq
      ring
  calc Complex.normSq ((uniform (ι → ZMod q)).recOp i (some a) none)
        + ∑ x : ZMod q, (if some x = some a then 0
          else Complex.normSq ((uniform (ι → ZMod q)).recOp i (some a) (some x)))
      ≤ 1 / q + ∑ _x : ZMod q, 1 / (q : ℝ) ^ 2 := by
        gcongr with x
        · simp [FinDist.recOp, meanVec_uniform]
        · exact hx x
    _ = 2 / q := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
        field_simp
        ring

/-- **The masked recording operator** (final condition): if `φ` vanishes where coordinate `i`
holds `a`, the part of `R φ` where coordinate `i` holds `a` has squared norm at most
`(2/q) ‖φ‖²`. Indeed `[dᵢ = a] R = R_{−i} ([dᵢ = a] Rᵢ)` with `R_{−i}` unitary. -/
private lemma sum_mask_normSq_recOpAll_le (i : ι) (a : ZMod q)
    (φ : (ι → Option (ZMod q)) → ℂ) (hφ : ∀ d, d i = some a → φ d = 0) :
    ∑ e, (if e i = some a then
        Complex.normSq (((uniform (ι → ZMod q)).recOpAll *ᵥ φ) e) else 0)
      ≤ 2 / q * ∑ d, Complex.normSq (φ d) := by
  set fa : Option (ZMod q) → ℂ := fun u => if u = some a then 1 else 0 with hfa
  have hR : (uniform (ι → ZMod q)).recOpAll = tensorMat (uniform (ι → ZMod q)).recOp := rfl
  have hRm : tensorMat (fun j => if j = i then (1 : Matrix (Option (ZMod q)) (Option (ZMod q)) ℂ)
      else (uniform (ι → ZMod q)).recOp j) ∈ Matrix.unitaryGroup (ι → Option (ZMod q)) ℂ := by
    refine tensorMat_mem_unitaryGroup _ fun j => ?_
    split_ifs
    · exact one_mem _
    · exact FinDist.recOp_mem_unitaryGroup _ j
  calc ∑ e, (if e i = some a then
        Complex.normSq (((uniform (ι → ZMod q)).recOpAll *ᵥ φ) e) else 0)
      = qNormSq (Matrix.diagonal (fun e : ι → Option (ZMod q) => fa (e i))
          *ᵥ ((uniform (ι → ZMod q)).recOpAll *ᵥ φ)) := by
        rw [qNormSq_def]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Matrix.mulVec_diagonal]
        by_cases he : e i = some a <;> simp [hfa, he]
    _ = qNormSq (tensorMat (fun j => if j = i then 1 else (uniform (ι → ZMod q)).recOp j)
          *ᵥ (tensorMat (fun j => if j = i then
            Matrix.diagonal fa * (uniform (ι → ZMod q)).recOp i else 1) *ᵥ φ)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hR, diagonal_mul_tensorMat]
    _ = qNormSq (tensorMat (fun j => if j = i then
            Matrix.diagonal fa * (uniform (ι → ZMod q)).recOp i else 1) *ᵥ φ) :=
        qNormSq_mulVec hRm _
    _ = ∑ d : ι → Option (ZMod q), (if d i = some a then Complex.normSq
          (∑ u, (uniform (ι → ZMod q)).recOp i (d i) u * φ (Function.update d i u)) else 0) := by
        rw [qNormSq_def]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [tensorMat_single_mulVec]
        simp only [Matrix.diagonal_mul, hfa]
        by_cases hd : d i = some a <;> simp [hd]
    _ ≤ (∑ v, if v = some a then 0
          else Complex.normSq ((uniform (ι → ZMod q)).recOp i (some a) v))
          * ∑ d, Complex.normSq (φ d) :=
        sum_normSq_single_le _ i (some a) φ hφ
    _ ≤ 2 / q * ∑ d, Complex.normSq (φ d) :=
        mul_le_mul_of_nonneg_right (sum_normSq_recOp_le i a)
          (Finset.sum_nonneg fun d _ => Complex.normSq_nonneg _)

/-- **The final-condition bound off `Π`**: for `φ` vanishing on the databases recording `a`,
`‖G C† φ‖ ≤ √(2/q) ‖φ‖`, where `G` masks to the outputs `i` with `xᵢ = a`. -/
private lemma jNorm_goodMask_compress_le (a : ZMod q) {B : Type} [Fintype B] [DecidableEq B]
    (rd : B → ι) (φ : JVec (ι → Option (ZMod q)) B) (hφ : ∀ d ∈ searchDb a, ∀ p, φ d p = 0) :
    jNorm ((uniform (ι → ZMod q)).goodMask rd (fun x i => x i = a)
        ((uniform (ι → ZMod q)).compressᴴ * φ)) ≤ Real.sqrt (2 / q) * jNorm φ := by
  rw [jNorm, jNorm, ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  rw [jNormSq_eq_sum_qNormSq_col, jNormSq_eq_sum_qNormSq_col, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [qNormSq_def, qNormSq_def]
  set F : (ι → Option (ZMod q)) → ℝ := fun e => if e (rd p) = some a then
    Complex.normSq (((uniform (ι → ZMod q)).recOpAll *ᵥ fun d => φ d p) e) else 0 with hF
  calc ∑ x, Complex.normSq ((uniform (ι → ZMod q)).goodMask rd (fun x i => x i = a)
        ((uniform (ι → ZMod q)).compressᴴ * φ) x p)
      = ∑ x : (uniform (ι → ZMod q)).Supp, F (fun j => some (x.1 j)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [hF, FinDist.goodMask, conjTranspose_compress_mul_apply, Option.some_inj]
        split_ifs <;> simp
    _ ≤ ∑ e, F e :=
        sum_supp_le_sum_db _ F fun e => by
          simp only [hF]
          split_ifs <;> simp [Complex.normSq_nonneg]
    _ ≤ 2 / q * ∑ d, Complex.normSq (φ d p) :=
        sum_mask_normSq_recOpAll_le (rd p) a _
          fun d hd => hφ d (mem_searchDb.mpr ⟨rd p, hd⟩) p

/-- **The progress measure for Search** [Ham25, Proposition 42]: `Δₜ = ‖Π C Ψₜ‖`, the weight of the
compressed phase-model joint state on the databases recording the symbol `a`. -/
noncomputable def searchProgress (a : ZMod q) (A : QAlg ι (ZMod q) O W) (t : ℕ) : ℝ :=
  jNorm (dbProj (searchDb a)
    * ((uniform (ι → ZMod q)).compress * (uniform (ι → ZMod q)).jointZqState id A t))

/-- **Initial condition**: the record starts empty, so `Δ₀ = 0`. -/
theorem searchProgress_zero (a : ZMod q) (A : QAlg ι (ZMod q) O W) : searchProgress a A 0 = 0 := by
  have h : dbProj (searchDb a) *ᵥ (Pi.single dbEmpty 1 : (ι → Option (ZMod q)) → ℂ) = 0 := by
    funext d
    by_cases hd : d = dbEmpty
    · subst hd
      have hP : (dbEmpty : ι → Option (ZMod q)) ∉ searchDb a := fun h => by
        obtain ⟨j, hj⟩ := mem_searchDb.mp h
        simp [dbEmpty] at hj
      classical
      simp [dbProj, Matrix.mulVec_diagonal, hP]
    · classical
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, dbProj, Matrix.diagonal_apply_ne _ hd]
  rw [searchProgress, FinDist.compress_mul_jointZqState isFullProduct_uniform A 0, jRun_zero,
    mul_wsOp, Matrix.mul_vecMulVec, h, Matrix.zero_vecMulVec]
  have h0 : wsOp (A.step 0) (0 : JVec (ι → Option (ZMod q)) (QBasis ι (ZMod q) W)) = 0 := by
    rw [wsOp_eq_mul_transpose, Matrix.zero_mul]
  rw [h0, jNorm_zero]

/-- **The per-query growth for Search** [Ham25, Proposition 42]: the commutator of the recording
oracle (phase oracle over `Z_q`, uniform inputs) with the projection onto the databases recording
`a` has norm at most `√(10/q)`. -/
theorem jNorm_recOracle_comm_searchDb_le (a : ZMod q)
    (φ : JVec (ι → Option (ZMod q)) (QBasis ι (ZMod q) W)) :
    jNorm ((uniform (ι → ZMod q)).recOracle phaseZqOracleMat 0 (dbProj (searchDb a) * φ)
        - dbProj (searchDb a) * (uniform (ι → ZMod q)).recOracle phaseZqOracleMat 0 φ)
      ≤ Real.sqrt (10 / q) * jNorm φ := by
  set X := (uniform (ι → ZMod q)).recOracle phaseZqOracleMat 0 (dbProj (searchDb a) * φ)
    - dbProj (searchDb a) * (uniform (ι → ZMod q)).recOracle phaseZqOracleMat 0 φ with hX
  suffices h : jNormSq X ≤ 10 / q * jNormSq φ by
    rw [jNorm, jNorm, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt h
  rw [jNormSq_eq_sum_qNormSq_col, jNormSq_eq_sum_qNormSq_col, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  have htriv : (∀ b : ι → ZMod q, phaseZqSign b p = 1) →
      qNormSq (fun d => X d p) ≤ 10 / q * qNormSq (fun d => φ d p) := by
    intro hp
    have h0 : (fun d => X d p) = 0 := by
      funext d
      simp only [hX, Matrix.sub_apply, Pi.zero_apply]
      rw [recOracle_phase_apply_of_eq_one _ _ _ hp]
      by_cases hd : d ∈ searchDb a
      · rw [dbProj_mul_apply_of_mem _ hd, dbProj_mul_apply_of_mem _ hd,
          recOracle_phase_apply_of_eq_one _ _ _ hp, sub_self]
      · rw [dbProj_mul_apply_of_notMem _ hd, dbProj_mul_apply_of_notMem _ hd, sub_self]
    rw [h0, qNormSq_zero]
    exact mul_nonneg (by positivity) (qNormSq_nonneg _)
  obtain ⟨_ | i, _ | c, w⟩ := p
  · exact htriv fun _ => rfl
  · exact htriv fun _ => rfl
  · exact htriv fun _ => rfl
  set ψin : (ι → Option (ZMod q)) → ℂ := fun e =>
    (dbProj (searchDb a) * φ : JVec (ι → Option (ZMod q)) (QBasis ι (ZMod q) W)) e
      (some i, some c, w)
  set ψout : (ι → Option (ZMod q)) → ℂ := fun e => φ e (some i, some c, w)
    - (dbProj (searchDb a) * φ : JVec (ι → Option (ZMod q)) (QBasis ι (ZMod q) W)) e
      (some i, some c, w)
  have hsplit : ∑ d, (Complex.normSq (ψin d) + Complex.normSq (ψout d))
      = qNormSq (fun d => φ d (some i, some c, w)) := by
    rw [qNormSq_def]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hd : d ∈ searchDb a
    · simp [ψin, ψout, dbProj_mul_apply_of_mem _ hd]
    · simp [ψin, ψout, dbProj_mul_apply_of_notMem _ hd]
  rw [qNormSq_def, ← hsplit]
  refine comm_col_le (recPhase i c) i (some a) ψin ψout (fun d => X d (some i, some c, w))
    ?_ ?_ ?_ ?_ (sum_normSq_recPhase_le i c a) ?_
  · intro d hd
    exact dbProj_mul_apply_of_notMem _ (fun h => (mem_searchDb.mp h).elim hd) _
  · intro d j hj
    simp only [ψout]
    rw [dbProj_mul_apply_of_mem _ (mem_searchDb.mpr ⟨j, hj⟩), sub_self]
  · intro d hd
    simp only [hX, Matrix.sub_apply]
    rw [dbProj_mul_apply_of_mem _ (mem_searchDb.mpr hd), recOracle_phase_apply_some,
      recOracle_phase_apply_some, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [ψout]
    ring
  · intro d hd
    simp only [hX, Matrix.sub_apply]
    rw [dbProj_mul_apply_of_notMem _ (fun h => (mem_searchDb.mp h).elim hd), sub_zero,
      recOracle_phase_apply_some]
  · calc ∑ u, (if u = some a then 0 else Complex.normSq (recPhase i c u (some a)))
        = ∑ u, (if u = some a then 0 else Complex.normSq (recPhase i c (some a) u)) :=
          Finset.sum_congr rfl fun u _ => by rw [recPhase_symm]
      _ ≤ 10 / q := sum_normSq_recPhase_le i c a

/-- **Progress evolution**: `Δₜ ≤ t √(10/q)`. -/
theorem searchProgress_le (a : ZMod q) (A : QAlg ι (ZMod q) O W) (t : ℕ) :
    searchProgress a A t ≤ t * Real.sqrt (10 / q) := by
  have hP : (dbEmpty : ι → Option (ZMod q)) ∉ searchDb a := fun h => by
    obtain ⟨j, hj⟩ := mem_searchDb.mp h
    simp [dbEmpty] at hj
  refine (FinDist.jNorm_dbProj_compress_jointZqState_le isFullProduct_uniform A hP t).trans ?_
  calc _ ≤ ∑ _j ∈ Finset.range t, Real.sqrt (10 / q) := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine (jNorm_recOracle_comm_searchDb_le a _).trans (le_of_eq ?_)
        rw [jNorm, FinDist.jNormSq_compress_mul, FinDist.jNormSq_jointZqState, Real.sqrt_one,
          mul_one]
    _ = t * Real.sqrt (10 / q) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Final condition** [Ham25, Proposition 42]: the average success probability of finding a
position holding `a` satisfies `√p ≤ Δₜ + √(2/q)`. -/
theorem sqrt_avgZqSuccessProb_search_le (a : ZMod q) (A : QAlg ι (ZMod q) ι W) (t : ℕ) :
    Real.sqrt ((uniform (ι → ZMod q)).avgZqSuccessProb A t id (fun x i => x i = a))
      ≤ searchProgress a A t + Real.sqrt (2 / q) := by
  set Ψ := (uniform (ι → ZMod q)).jointZqState id A t with hΨ
  set C := (uniform (ι → ZMod q)).compress with hC
  set P : Matrix (ι → Option (ZMod q)) (ι → Option (ZMod q)) ℂ := dbProj (searchDb a) with hP
  rw [FinDist.avgZqSuccessProb_eq_jNormSq_goodMask]
  change jNorm ((uniform (ι → ZMod q)).goodMask A.readout (fun x i => x i = a) Ψ)
    ≤ jNorm (P * (C * Ψ)) + Real.sqrt (2 / q)
  have hdec : Ψ = Cᴴ * (P * (C * Ψ)) + Cᴴ * ((1 - P) * (C * Ψ)) := by
    rw [← Matrix.mul_add, ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul, ← Matrix.mul_assoc,
      hC, FinDist.conjTranspose_compress_mul_compress, Matrix.one_mul]
  have hCΨ : jNorm (C * Ψ) = 1 := by
    rw [jNorm, hC, FinDist.jNormSq_compress_mul, hΨ, FinDist.jNormSq_jointZqState,
      Real.sqrt_one]
  have hout : ∀ d ∈ searchDb a, ∀ p,
      ((1 - P) * (C * Ψ) : JVec (ι → Option (ZMod q)) (QBasis ι (ZMod q) W)) d p = 0 := by
    intro d hd p
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, hP, dbProj_mul_apply_of_mem _ hd,
      sub_self]
  have hle : jNorm ((1 - P) * (C * Ψ)) ≤ jNorm (C * Ψ) := by
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun d _ => ?_)
    rw [qNormSq_def, qNormSq_def]
    refine Finset.sum_le_sum fun p _ => ?_
    by_cases hd : d ∈ searchDb a
    · rw [hout d hd p, map_zero]
      exact Complex.normSq_nonneg _
    · rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, hP, dbProj_mul_apply_of_notMem _ hd,
        sub_zero]
  calc jNorm ((uniform (ι → ZMod q)).goodMask A.readout (fun x i => x i = a) Ψ)
      = jNorm ((uniform (ι → ZMod q)).goodMask A.readout (fun x i => x i = a)
            (Cᴴ * (P * (C * Ψ)))
          + (uniform (ι → ZMod q)).goodMask A.readout (fun x i => x i = a)
            (Cᴴ * ((1 - P) * (C * Ψ)))) := by
        rw [← goodMask_add, ← hdec]
    _ ≤ jNorm ((uniform (ι → ZMod q)).goodMask A.readout (fun x i => x i = a)
            (Cᴴ * (P * (C * Ψ))))
          + jNorm ((uniform (ι → ZMod q)).goodMask A.readout (fun x i => x i = a)
            (Cᴴ * ((1 - P) * (C * Ψ)))) := jNorm_add_le _ _
    _ ≤ jNorm (P * (C * Ψ)) + Real.sqrt (2 / q) * 1 := by
        refine add_le_add ((jNorm_goodMask_le _ _ _ _).trans
          (jNorm_conjTranspose_compress_mul_le _ _)) ?_
        refine (jNorm_goodMask_compress_le a A.readout _ hout).trans ?_
        exact mul_le_mul_of_nonneg_left (hle.trans hCΨ.le) (Real.sqrt_nonneg _)
    _ = jNorm (P * (C * Ψ)) + Real.sqrt (2 / q) := by rw [mul_one]

/-- **Search under the uniform distribution, phase oracle** [Ham25, Proposition 42]: after `t`
phase queries, the average probability of finding a position holding `a` is at most
`(√10 t + √2)²/q`. -/
theorem avgZqSuccessProb_search_le (a : ZMod q) (A : QAlg ι (ZMod q) ι W) (t : ℕ) :
    (uniform (ι → ZMod q)).avgZqSuccessProb A t id (fun x i => x i = a)
      ≤ (Real.sqrt 10 * t + Real.sqrt 2) ^ 2 / q := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hp : 0 ≤ (uniform (ι → ZMod q)).avgZqSuccessProb A t id (fun x i => x i = a) := by
    rw [FinDist.avgZqSuccessProb_eq_jNormSq_goodMask]
    exact jNormSq_nonneg _
  have h1 := (sqrt_avgZqSuccessProb_search_le a A t).trans
    (add_le_add_left (searchProgress_le a A t) _)
  have h2 : (t : ℝ) * Real.sqrt (10 / q) + Real.sqrt (2 / q)
      = (Real.sqrt 10 * t + Real.sqrt 2) / Real.sqrt q := by
    rw [Real.sqrt_div' _ hq.le, Real.sqrt_div' _ hq.le]
    ring
  rw [h2] at h1
  calc (uniform (ι → ZMod q)).avgZqSuccessProb A t id (fun x i => x i = a)
      = Real.sqrt ((uniform (ι → ZMod q)).avgZqSuccessProb A t id (fun x i => x i = a)) ^ 2 :=
        (Real.sq_sqrt hp).symm
    _ ≤ ((Real.sqrt 10 * t + Real.sqrt 2) / Real.sqrt q) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    _ = (Real.sqrt 10 * t + Real.sqrt 2) ^ 2 / q := by rw [div_pow, Real.sq_sqrt hq.le]

/-- The value-oracle average success after `t` queries is the phase-model average success of the
simulation after `2t` phase queries. -/
private lemma avgSuccessProb_eq_avgZqSuccessProb_simStdToZq (a : ZMod q)
    (A : QAlg ι (ZMod q) ι W) (t : ℕ) :
    (uniform (ι → ZMod q)).avgSuccessProb A t id (fun x i => x i = a)
      = (uniform (ι → ZMod q)).avgZqSuccessProb (A.simStdToZq t) (2 * t) id
          (fun x i => x i = a) := by
  rw [FinDist.avgSuccessProb, FinDist.avgZqSuccessProb]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [zqSuccessProbOn_simStdToZq]

/-- **Search under the uniform distribution, value oracle**: after `t` value queries, the average
probability of finding a position holding `a` is at most `(2√10 t + √2)²/q`. -/
theorem avgSuccessProb_search_le (a : ZMod q) (A : QAlg ι (ZMod q) ι W) (t : ℕ) :
    (uniform (ι → ZMod q)).avgSuccessProb A t id (fun x i => x i = a)
      ≤ (2 * Real.sqrt 10 * t + Real.sqrt 2) ^ 2 / q := by
  rw [avgSuccessProb_eq_avgZqSuccessProb_simStdToZq]
  refine (avgZqSuccessProb_search_le a (A.simStdToZq t) (2 * t)).trans (le_of_eq ?_)
  push_cast
  ring

/-- **Average success `2/3` needs `√(q/15) − √(1/5)` phase queries** [Ham25, Proposition 42]. -/
theorem le_of_avgZqSuccessProb_search (a : ZMod q) (A : QAlg ι (ZMod q) ι W) (t : ℕ)
    (h : 2 / 3 ≤ (uniform (ι → ZMod q)).avgZqSuccessProb A t id (fun x i => x i = a)) :
    Real.sqrt (q / 15) - Real.sqrt (1 / 5) ≤ t := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have h1 : 2 / 3 * q ≤ (Real.sqrt 10 * t + Real.sqrt 2) ^ 2 :=
    (le_div_iff₀ hq).mp (h.trans (avgZqSuccessProb_search_le a A t))
  have h2 : Real.sqrt (2 / 3 * q) ≤ Real.sqrt 10 * t + Real.sqrt 2 :=
    (Real.sqrt_le_sqrt h1).trans_eq (Real.sqrt_sq (by positivity))
  have h3 : Real.sqrt (q / 15) * Real.sqrt 10 = Real.sqrt (2 / 3 * q) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  have h4 : Real.sqrt (1 / 5) * Real.sqrt 10 = Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by positivity)]
    norm_num
  have h10 : 0 < Real.sqrt 10 := by positivity
  refine le_of_mul_le_mul_right ?_ h10
  rw [sub_mul, h3, h4]
  linarith

/-- **Average success `2/3` needs `(√(q/15) − √(1/5))/2` value queries.** -/
theorem le_of_avgSuccessProb_search (a : ZMod q) (A : QAlg ι (ZMod q) ι W) (t : ℕ)
    (h : 2 / 3 ≤ (uniform (ι → ZMod q)).avgSuccessProb A t id (fun x i => x i = a)) :
    (Real.sqrt (q / 15) - Real.sqrt (1 / 5)) / 2 ≤ t := by
  rw [avgSuccessProb_eq_avgZqSuccessProb_simStdToZq] at h
  have h' := le_of_avgZqSuccessProb_search a (A.simStdToZq t) (2 * t) h
  push_cast at h'
  linarith

end QuantumQueryComplexity
