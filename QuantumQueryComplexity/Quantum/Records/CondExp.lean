import QuantumQueryComplexity.Quantum.JointState.Basic

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Conditional averaging over one coordinate

Let `ρ` be a distribution on strings `ι → σ` over a finite alphabet `σ`.  Fixing every
coordinate except `i` splits the support into **fibres**.  The conditional average `Eᵢ`
(`FinDist.condExp ρ i`) replaces each workspace vector by its conditional mean over its fibre,

  `(Eᵢ f)ˣ = E_ρ[f^X | X_{ι∖i} = x_{ι∖i}]`,

and `Dᵢ = I − Eᵢ` (`FinDist.condDiff ρ i`) keeps the deviation from that mean
(Cornelissen–Gilani–Zhou, (3.4) and Section 4.2).  On the input register, in the square-root
weighted coordinates of `JointState/Basic.lean`, `Eᵢ` is an orthogonal projection: on each
fibre it projects onto the conditional state `∑_y √(ρ(y)/ρ(fibre)) |y⟩`.

These are the **record operators**.  For a product distribution the `Dᵢ` commute and their
joint eigenspaces are the record subspaces of Zhandry's compressed oracle; for dependent
distributions they need not commute, and only the operators remain.

## Main results

* `condExp_isHermitian`, `condExp_mul_self`, `condExp_mul_condDiff` — `Eᵢ`, `Dᵢ` are
  complementary orthogonal projections; `0 ≤ Eᵢ ≤ I`, `0 ≤ Dᵢ ≤ I`.
* `condExp_mulVec_ket` — `Eᵢ |ρ⟩ = |ρ⟩`.
* `wvec_condExp_mul` — the workspace form of `Eᵢ` is the conditional mean.
* `jNormSq_condDiff_mul` — `‖Dᵢ f‖²` is the conditional variance averaged over the other
  coordinates.
* `commute_condExp_coordDiag` — **query locality**: an operator that is diagonal on the input
  register and reads only coordinate `i` (a phase query to `i`) commutes with `Eⱼ` and `Dⱼ` for
  every `j ≠ i`, for every distribution.
-/

namespace QuantumQueryComplexity

open scoped Matrix MatrixOrder ComplexOrder
open Matrix

variable {ι σ A : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype A]

/-- `x` and `y` agree at every coordinate other than `i`. -/
def AgreeOff (i : ι) (x y : ι → σ) : Prop := ∀ j, j ≠ i → x j = y j

instance (i : ι) : DecidableRel (AgreeOff (σ := σ) i) := fun _ _ => by
  unfold AgreeOff; infer_instance

lemma AgreeOff.refl (i : ι) (x : ι → σ) : AgreeOff i x x := fun _ _ => rfl

lemma AgreeOff.symm {i : ι} {x y : ι → σ} (h : AgreeOff i x y) : AgreeOff i y x :=
  fun j hj => (h j hj).symm

lemma AgreeOff.trans {i : ι} {x y z : ι → σ} (h₁ : AgreeOff i x y) (h₂ : AgreeOff i y z) :
    AgreeOff i x z :=
  fun j hj => (h₁ j hj).trans (h₂ j hj)

namespace FinDist

variable (ρ : FinDist (ι → σ))

/-- The mass of the fibre of `x` for coordinate `i`: the strings that agree with `x` off `i`. -/
noncomputable def fiberMass (i : ι) (x : ι → σ) : ℝ :=
  ∑ y, if AgreeOff i x y then ρ.mass y else 0

/-- Summing a function that vanishes off the support over `ρ.Supp` or over all strings gives
the same result. -/
private lemma sum_supp_eq_sum {M : Type*} [AddCommMonoid M] (g : (ι → σ) → M)
    (hg : ∀ y, ρ.mass y = 0 → g y = 0) :
    ∑ y : ρ.Supp, g y = ∑ y, g y := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun y => 0 < ρ.mass y) (by simp) g]
  apply Finset.sum_filter_of_ne
  intro y _ hy
  exact lt_of_le_of_ne (ρ.mass_nonneg y) (fun h => hy (hg y h.symm))

/-- The fibre mass as a sum over the support. -/
private lemma sum_supp_agree (i : ι) (x : ι → σ) :
    ∑ y : ρ.Supp, (if AgreeOff i x y.1 then ρ.mass y else 0) = ρ.fiberMass i x := by
  rw [fiberMass, sum_supp_eq_sum ρ (fun y => if AgreeOff i x y then ρ.mass y else 0)]
  intro y hy
  simp [hy]

/-- The fibre of a support point has positive mass. -/
theorem fiberMass_pos (i : ι) (x : ρ.Supp) : 0 < ρ.fiberMass i x := by
  unfold fiberMass
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum
    (f := fun y => if AgreeOff i x.1 y then ρ.mass y else 0) (fun y _ => ?_)
    (Finset.mem_univ x.1))
  · simp only [ite_eq_left (AgreeOff.refl i x.1)]
    exact x.2
  · split_ifs
    · exact ρ.mass_nonneg y
    · exact le_rfl

/-- The fibre mass is constant on fibres. -/
theorem fiberMass_congr {i : ι} {x y : ι → σ} (h : AgreeOff i x y) :
    ρ.fiberMass i x = ρ.fiberMass i y := by
  unfold fiberMass
  refine Finset.sum_congr rfl fun z _ => ?_
  exact if_congr ⟨h.symm.trans, h.trans⟩ rfl rfl

/-- **Conditional averaging** `Eᵢ` on the input register, in square-root weighted coordinates:
the entry at `(x, y)` is `√(ρ(x) ρ(y)) / ρ(fibre of x)` when `x` and `y` agree off `i`. -/
noncomputable def condExp (i : ι) : Matrix ρ.Supp ρ.Supp ℂ := fun x y =>
  if AgreeOff i x.1 y.1 then
    ((Real.sqrt (ρ.mass x * ρ.mass y) / ρ.fiberMass i x : ℝ) : ℂ)
  else 0

/-- **The conditional difference** `Dᵢ = I − Eᵢ`. -/
noncomputable def condDiff (i : ι) : Matrix ρ.Supp ρ.Supp ℂ := 1 - ρ.condExp i

/-- The entries of `Eᵢ` with the square root split. -/
private lemma condExp_apply (i : ι) (x y : ρ.Supp) :
    ρ.condExp i x y = if AgreeOff i x.1 y.1 then
      ((Real.sqrt (ρ.mass x) * Real.sqrt (ρ.mass y) / ρ.fiberMass i x : ℝ) : ℂ) else 0 := by
  unfold condExp
  rw [Real.sqrt_mul (ρ.mass_nonneg _)]

theorem condExp_isHermitian (i : ι) : (ρ.condExp i).IsHermitian := by
  refine Matrix.IsHermitian.ext fun x y => ?_
  simp only [condExp_apply]
  by_cases h : AgreeOff i x.1 y.1
  · rw [ite_eq_left h.symm, ite_eq_left h, Complex.star_def, Complex.conj_ofReal,
      ← fiberMass_congr ρ h, mul_comm (Real.sqrt _)]
  · rw [ite_eq_right (fun h' => h h'.symm), ite_eq_right h, star_zero]

theorem condExp_mul_self (i : ι) : ρ.condExp i * ρ.condExp i = ρ.condExp i := by
  ext x y
  rw [mul_apply]
  have hm := (ρ.fiberMass_pos i x).ne'
  by_cases hxy : AgreeOff i x.1 y.1
  · have key : ∀ z : ρ.Supp, ρ.condExp i x z * ρ.condExp i z y =
        (((if AgreeOff i x.1 z.1 then ρ.mass z else 0) *
          (Real.sqrt (ρ.mass x) * Real.sqrt (ρ.mass y) / ρ.fiberMass i x ^ 2) : ℝ) : ℂ) := by
      intro z
      simp only [condExp_apply]
      by_cases hxz : AgreeOff i x.1 z.1
      · simp only [ite_eq_left hxz, ite_eq_left (hxz.symm.trans hxy)]
        rw [← fiberMass_congr ρ hxz, ← Complex.ofReal_mul]
        congr 1
        have hz := Real.mul_self_sqrt (ρ.mass_nonneg z)
        linear_combination
          (Real.sqrt (ρ.mass x) * Real.sqrt (ρ.mass y) / ρ.fiberMass i x ^ 2) * hz
      · simp only [ite_eq_right hxz, zero_mul, Complex.ofReal_zero]
    rw [Finset.sum_congr rfl fun z _ => key z, ← Complex.ofReal_sum, ← Finset.sum_mul,
      sum_supp_agree, condExp_apply, ite_eq_left hxy]
    congr 1
    field_simp
  · rw [condExp_apply, ite_eq_right hxy]
    refine Finset.sum_eq_zero fun z _ => ?_
    simp only [condExp_apply]
    by_cases hxz : AgreeOff i x.1 z.1
    · rw [ite_eq_right (fun hzy => hxy (hxz.trans hzy)), mul_zero]
    · rw [ite_eq_right hxz, zero_mul]

theorem condDiff_isHermitian (i : ι) : (ρ.condDiff i).IsHermitian := by
  exact Matrix.isHermitian_one.sub (ρ.condExp_isHermitian i)

theorem condDiff_mul_self (i : ι) : ρ.condDiff i * ρ.condDiff i = ρ.condDiff i := by
  simp only [condDiff, sub_mul, mul_sub, one_mul, mul_one, condExp_mul_self, sub_self, sub_zero]

theorem condExp_mul_condDiff (i : ι) : ρ.condExp i * ρ.condDiff i = 0 := by
  rw [condDiff, mul_sub, mul_one, condExp_mul_self, sub_self]

/-- A Hermitian idempotent matrix is positive semidefinite. -/
private lemma posSemidef_of_idem {n : Type} [Fintype n] [DecidableEq n] {P : Matrix n n ℂ}
    (hP : P.IsHermitian) (h : P * P = P) : P.PosSemidef := by
  have e : P = Pᴴ * P := by rw [hP.eq, h]
  rw [e]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem condExp_nonneg (i : ι) : 0 ≤ ρ.condExp i := by
  rw [Matrix.nonneg_iff_posSemidef]
  exact posSemidef_of_idem (ρ.condExp_isHermitian i) (ρ.condExp_mul_self i)

theorem condExp_le_one (i : ι) : ρ.condExp i ≤ 1 := by
  rw [Matrix.le_iff]
  exact posSemidef_of_idem (ρ.condDiff_isHermitian i) (ρ.condDiff_mul_self i)

theorem condDiff_nonneg (i : ι) : 0 ≤ ρ.condDiff i := by
  rw [Matrix.nonneg_iff_posSemidef]
  exact posSemidef_of_idem (ρ.condDiff_isHermitian i) (ρ.condDiff_mul_self i)

theorem condDiff_le_one (i : ι) : ρ.condDiff i ≤ 1 := by
  rw [Matrix.le_iff, condDiff, sub_sub_cancel]
  exact posSemidef_of_idem (ρ.condExp_isHermitian i) (ρ.condExp_mul_self i)

/-- `Eᵢ |ρ⟩ = |ρ⟩`. -/
theorem condExp_mulVec_ket (i : ι) : ρ.condExp i *ᵥ ρ.ket = ρ.ket := by
  funext x
  have hm := (ρ.fiberMass_pos i x).ne'
  simp only [mulVec, dotProduct]
  have key : ∀ y : ρ.Supp, ρ.condExp i x y * ρ.ket y =
      (((if AgreeOff i x.1 y.1 then ρ.mass y else 0) *
        (Real.sqrt (ρ.mass x) / ρ.fiberMass i x) : ℝ) : ℂ) := by
    intro y
    simp only [condExp_apply, ket]
    by_cases hxy : AgreeOff i x.1 y.1
    · simp only [ite_eq_left hxy]
      rw [← Complex.ofReal_mul]
      congr 1
      have hy := Real.mul_self_sqrt (ρ.mass_nonneg y)
      linear_combination (Real.sqrt (ρ.mass x) / ρ.fiberMass i x) * hy
    · simp only [ite_eq_right hxy, zero_mul, Complex.ofReal_zero]
  rw [Finset.sum_congr rfl fun y _ => key y, ← Complex.ofReal_sum, ← Finset.sum_mul,
    sum_supp_agree, ket]
  congr 1
  field_simp

/-- `Dᵢ |ρ⟩ = 0`. -/
theorem condDiff_mulVec_ket (i : ι) : ρ.condDiff i *ᵥ ρ.ket = 0 := by
  rw [condDiff, sub_mulVec, one_mulVec, condExp_mulVec_ket, sub_self]

/-- The conditional weight of `y` given the fibre of `x`. -/
noncomputable def condWeight (i : ι) (x y : ρ.Supp) : ℝ :=
  if AgreeOff i x.1 y.1 then ρ.mass y / ρ.fiberMass i x else 0

lemma condWeight_nonneg (i : ι) (x y : ρ.Supp) : 0 ≤ ρ.condWeight i x y := by
  unfold condWeight
  split_ifs
  · exact div_nonneg (ρ.mass_nonneg _) (ρ.fiberMass_pos i x).le
  · exact le_rfl

/-- The conditional weights on each fibre sum to one. -/
theorem sum_condWeight (i : ι) (x : ρ.Supp) : ∑ y, ρ.condWeight i x y = 1 := by
  have hm := (ρ.fiberMass_pos i x).ne'
  have h : ∀ y : ρ.Supp, ρ.condWeight i x y =
      (if AgreeOff i x.1 y.1 then ρ.mass y else 0) / ρ.fiberMass i x := by
    intro y
    unfold condWeight
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun y _ => h y, ← Finset.sum_div, sum_supp_agree, div_self hm]

/-- The entry identity behind the workspace form of `Eᵢ`. -/
private lemma inv_sqrt_mul_condExp (i : ι) (x y : ρ.Supp) :
    ((Real.sqrt (ρ.mass x))⁻¹ : ℂ) * ρ.condExp i x y
      = (ρ.condWeight i x y : ℂ) * ((Real.sqrt (ρ.mass y))⁻¹ : ℂ) := by
  rw [condExp_apply, condWeight]
  by_cases hxy : AgreeOff i x.1 y.1
  · simp only [ite_eq_left hxy]
    rw [← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    have hx := (Real.sqrt_pos.mpr (ρ.mass_pos x)).ne'
    have hy := (Real.sqrt_pos.mpr (ρ.mass_pos y)).ne'
    have hm := (ρ.fiberMass_pos i x).ne'
    have hyy := Real.mul_self_sqrt (ρ.mass_nonneg y)
    field_simp
    linear_combination hyy
  · simp only [ite_eq_right hxy, mul_zero, Complex.ofReal_zero, zero_mul]

/-- **The workspace form of `Eᵢ`**: the workspace vector of `Eᵢ f` at `x` is the conditional
mean of the workspace vectors of `f` over the fibre of `x`. -/
theorem wvec_condExp_mul (i : ι) (f : JVec ρ.Supp A) (x : ρ.Supp) :
    ρ.wvec (ρ.condExp i * f) x = ∑ y, (ρ.condWeight i x y : ℂ) • ρ.wvec f y := by
  funext a
  simp only [wvec, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← mul_assoc, ← mul_assoc, inv_sqrt_mul_condExp]

/-- **The conditional variance.** `‖Dᵢ f‖²` averages, over `x ∼ ρ`, the squared distance of the
workspace vector at `x` from its conditional mean. -/
theorem jNormSq_condDiff_mul (i : ι) (f : JVec ρ.Supp A) :
    jNormSq (ρ.condDiff i * f)
      = ∑ x : ρ.Supp, ρ.mass x * qNormSq (ρ.wvec f x - ρ.wvec (ρ.condExp i * f) x) := by
  rw [jNormSq_eq_sum_wvec]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [condDiff, Matrix.sub_mul, Matrix.one_mul]
  congr 2
  funext a
  simp [wvec, mul_sub]

/-- `⟨f, Dᵢ f⟩ = ‖Dᵢ f‖²`. -/
theorem jInner_condDiff_mul (i : ι) (f : JVec ρ.Supp A) :
    jInner f (ρ.condDiff i * f) = (jNormSq (ρ.condDiff i * f) : ℂ) := by
  have h : ρ.condDiff i * f = (ρ.condDiff i)ᴴ * (ρ.condDiff i * f) := by
    rw [(ρ.condDiff_isHermitian i).eq, ← Matrix.mul_assoc, ρ.condDiff_mul_self i]
  conv_lhs => rw [h]
  rw [jInner_mul_right, conjTranspose_conjTranspose, jInner_self]

/-- A diagonal operator on the input register that reads only coordinate `i`; for
`φ c = ω^(c·b)` it is the phase query to `i`. -/
noncomputable def coordDiag (i : ι) (φ : σ → ℂ) : Matrix ρ.Supp ρ.Supp ℂ :=
  Matrix.diagonal fun x => φ (x.1 i)

/-- **Query locality**: an operator reading only coordinate `i` commutes with conditional
averaging over any other coordinate, for every distribution. -/
theorem commute_condExp_coordDiag {i j : ι} (hij : j ≠ i) (φ : σ → ℂ) :
    Commute (ρ.condExp j) (ρ.coordDiag i φ) := by
  unfold Commute SemiconjBy
  ext x y
  simp only [coordDiag, mul_diagonal, diagonal_mul]
  by_cases h : AgreeOff j x.1 y.1
  · rw [h i hij.symm, mul_comm]
  · simp [condExp, h]

theorem commute_condDiff_coordDiag {i j : ι} (hij : j ≠ i) (φ : σ → ℂ) :
    Commute (ρ.condDiff j) (ρ.coordDiag i φ) := by
  unfold condDiff
  exact (Commute.one_left _).sub_left (ρ.commute_condExp_coordDiag hij φ)

end FinDist

end QuantumQueryComplexity
