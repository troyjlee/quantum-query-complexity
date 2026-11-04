import QuantumQueryComplexity.Quantum.Records.Resampling

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Bernoulli bits conditioned to avoid all-ones patterns

Let `F` be a finite family of nonempty sets of coordinates and `0 < p ≤ 1/2`.  The allowed
strings `Ω = {x : x_C ≠ 1_C for every C ∈ F}` form a downward-closed set containing the all-zero
string, and `μ = Bernoulli(p)^{⊗ι}( · | Ω)` (Cornelissen–Gilani–Zhou, (4.11)).  The structure
`CondBern` bundles `F` and `p`; `CondBern.dist` is `μ` as a `FinDist`.

Given all coordinates except `i`, either setting `xᵢ = 1` completes a forbidden set, so `i` is
forced to zero (`¬ Free i x`), or both values are allowed and `xᵢ` is a Bernoulli(p) bit
(`condWeight_eq`).  This gives the explicit two-point formulas for `Dᵢ` (CGZ (4.4),
`wvec_condDiff_mul`) and the conditional variance `p(1 − p)‖f¹ − f⁰‖²` (CGZ (4.12),
`jNormSq_condDiff_mul_eq`).

The indicator `Aᵢⱼ(x)` of CGZ (4.16) (`Interact`, operator `interactOp`) marks the
configurations on which resampling `i` and `j` can fail to commute.  It depends only on the
coordinates outside `{i, j}`, so it commutes with `Dᵢ` and `Dⱼ`.

## General helpers

The first section holds facts valid for every distribution: workspace vectors at arbitrary
strings (`FinDist.wvecAt`), commutation of `Eᵢ` with diagonal operators that ignore coordinate
`i`, the infinity-norm bounds `‖Eᵢ f‖∞ ≤ ‖f‖∞` and `‖Dᵢ f‖∞ ≤ 2‖f‖∞`, and locality of `DᵢDⱼ`.
The summation identity `sum_eq_sum_twoFiber` regroups a sum over strings by the four
assignments of two coordinates.
-/

namespace QuantumQueryComplexity

open scoped Matrix MatrixOrder ComplexOrder
open Matrix

variable {ι A : Type} [Fintype ι] [DecidableEq ι] [Fintype A]

/-! ## Facts valid for every distribution -/

namespace FinDist

section General

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] (ρ : FinDist Ω)

/-- The workspace vector of `f` at an arbitrary point: `ρ.wvec f` on the support, zero off it. -/
noncomputable def wvecAt (f : JVec ρ.Supp A) (y : Ω) : A → ℂ :=
  if h : 0 < ρ.mass y then ρ.wvec f ⟨y, h⟩ else 0

@[simp] lemma wvecAt_coe (f : JVec ρ.Supp A) (x : ρ.Supp) : ρ.wvecAt f x.1 = ρ.wvec f x := by
  rw [wvecAt, dite_eq_left x.2]

/-- Summing a function that vanishes off the support over `ρ.Supp` or over all points gives
the same result. -/
private lemma sum_supp_eq_sum' {M : Type*} [AddCommMonoid M] (g : Ω → M)
    (hg : ∀ y, ρ.mass y = 0 → g y = 0) :
    ∑ y : ρ.Supp, g y = ∑ y, g y := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun y => 0 < ρ.mass y) (by simp) g]
  apply Finset.sum_filter_of_ne
  intro y _ hy
  exact lt_of_le_of_ne (ρ.mass_nonneg y) (fun h => hy (hg y h.symm))

/-- The triangle inequality for finite sums, in squared-norm form. -/
private lemma sqrt_qNormSq_sum_le {β : Type*} (s : Finset β) (v : β → A → ℂ) :
    √(qNormSq (∑ i ∈ s, v i)) ≤ ∑ i ∈ s, √(qNormSq (v i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb]
    exact (sqrt_qNormSq_add_le _ _).trans (by linarith)

private lemma sqrt_qNormSq_ofReal_smul {r : ℝ} (hr : 0 ≤ r) (v : A → ℂ) :
    √(qNormSq ((r : ℂ) • v)) = r * √(qNormSq v) := by
  classical
  rw [qNormSq_smul, Complex.normSq_ofReal, Real.sqrt_mul (mul_self_nonneg r),
    Real.sqrt_mul_self hr]

private lemma qNormSq_neg' (v : A → ℂ) : qNormSq (-v) = qNormSq v := by
  simp only [qNormSq_def, Pi.neg_apply, Complex.normSq_neg]

private lemma qNormSq_sub_comm' (v w : A → ℂ) : qNormSq (v - w) = qNormSq (w - v) := by
  rw [← neg_sub, qNormSq_neg']

private lemma sqrt_qNormSq_sub_le (v w : A → ℂ) :
    √(qNormSq (v - w)) ≤ √(qNormSq v) + √(qNormSq w) := by
  classical
  rw [sub_eq_add_neg, ← qNormSq_neg' w]
  exact sqrt_qNormSq_add_le _ _

end General

section Coordinates

variable {σ : Type} [Fintype σ] [DecidableEq σ] (ρ : FinDist (ι → σ))

/-- A diagonal input operator that ignores coordinate `i` commutes with `Eᵢ`. -/
theorem commute_condExp_diagonal (i : ι) {d : ρ.Supp → ℂ}
    (hd : ∀ x y : ρ.Supp, AgreeOff i x.1 y.1 → d x = d y) :
    Commute (ρ.condExp i) (Matrix.diagonal d) := by
  unfold Commute SemiconjBy
  ext x y
  simp only [mul_diagonal, diagonal_mul]
  by_cases h : AgreeOff i x.1 y.1
  · rw [hd x y h, mul_comm]
  · simp [condExp, h]

theorem commute_condDiff_diagonal (i : ι) {d : ρ.Supp → ℂ}
    (hd : ∀ x y : ρ.Supp, AgreeOff i x.1 y.1 → d x = d y) :
    Commute (ρ.condDiff i) (Matrix.diagonal d) := by
  unfold condDiff
  exact (Commute.one_left _).sub_left (ρ.commute_condExp_diagonal i hd)

/-- The workspace form of `Dᵢ = I − Eᵢ`. -/
private lemma wvec_condDiff_mul_eq_sub (i : ι) (f : JVec ρ.Supp A) (x : ρ.Supp) :
    ρ.wvec (ρ.condDiff i * f) x = ρ.wvec f x - ρ.wvec (ρ.condExp i * f) x := by
  rw [condDiff, Matrix.sub_mul, Matrix.one_mul]
  funext a
  simp [wvec, mul_sub]

/-- `‖Eᵢ f‖∞ ≤ ‖f‖∞`: a conditional mean is an average of workspace vectors. -/
theorem infNormSq_condExp_mul_le (i : ι) (f : JVec ρ.Supp A) :
    ρ.infNormSq (ρ.condExp i * f) ≤ ρ.infNormSq f := by
  classical
  apply infNormSq_le
  intro x
  set K := √(ρ.infNormSq f)
  have hK : ∀ y, √(qNormSq (ρ.wvec f y)) ≤ K := fun y =>
    Real.sqrt_le_sqrt (ρ.qNormSq_wvec_le_infNormSq f y)
  have key : √(qNormSq (ρ.wvec (ρ.condExp i * f) x)) ≤ K := by
    rw [wvec_condExp_mul]
    refine (sqrt_qNormSq_sum_le _ _).trans ?_
    calc ∑ y, √(qNormSq ((ρ.condWeight i x y : ℂ) • ρ.wvec f y))
        = ∑ y, ρ.condWeight i x y * √(qNormSq (ρ.wvec f y)) :=
          Finset.sum_congr rfl fun y _ =>
            sqrt_qNormSq_ofReal_smul (ρ.condWeight_nonneg i x y) _
      _ ≤ ∑ y, ρ.condWeight i x y * K := by
          gcongr with y
          · exact ρ.condWeight_nonneg i x y
          · exact hK y
      _ = K := by rw [← Finset.sum_mul, ρ.sum_condWeight, one_mul]
  calc qNormSq (ρ.wvec (ρ.condExp i * f) x)
      = √(qNormSq (ρ.wvec (ρ.condExp i * f) x)) ^ 2 := (Real.sq_sqrt (qNormSq_nonneg _)).symm
    _ ≤ K ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) key 2
    _ = ρ.infNormSq f := Real.sq_sqrt (ρ.infNormSq_nonneg f)

/-- `‖Dᵢ f‖∞ ≤ 2‖f‖∞`. -/
theorem infNormSq_condDiff_mul_le (i : ι) (f : JVec ρ.Supp A) :
    ρ.infNormSq (ρ.condDiff i * f) ≤ 4 * ρ.infNormSq f := by
  classical
  apply infNormSq_le
  intro x
  set K := √(ρ.infNormSq f)
  have h1 : √(qNormSq (ρ.wvec f x)) ≤ K :=
    Real.sqrt_le_sqrt (ρ.qNormSq_wvec_le_infNormSq f x)
  have h2 : √(qNormSq (ρ.wvec (ρ.condExp i * f) x)) ≤ K := Real.sqrt_le_sqrt
    ((ρ.qNormSq_wvec_le_infNormSq _ x).trans (ρ.infNormSq_condExp_mul_le i f))
  have key : √(qNormSq (ρ.wvec (ρ.condDiff i * f) x)) ≤ 2 * K := by
    rw [wvec_condDiff_mul_eq_sub]
    exact (sqrt_qNormSq_sub_le _ _).trans (by linarith)
  calc qNormSq (ρ.wvec (ρ.condDiff i * f) x)
      = √(qNormSq (ρ.wvec (ρ.condDiff i * f) x)) ^ 2 := (Real.sq_sqrt (qNormSq_nonneg _)).symm
    _ ≤ (2 * K) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) key 2
    _ = 4 * ρ.infNormSq f := by
        rw [mul_pow, Real.sq_sqrt (ρ.infNormSq_nonneg f)]
        norm_num

/-- `DᵢDⱼ` preserves the coordinates outside `{i, j}`. -/
theorem condDiff_mul_condDiff_apply_eq_zero (i j : ι) {x y : ρ.Supp}
    (hxy : ∃ k, k ≠ i ∧ k ≠ j ∧ x.1 k ≠ y.1 k) :
    (ρ.condDiff i * ρ.condDiff j) x y = 0 := by
  obtain ⟨k, hki, hkj, hk⟩ := hxy
  have hne : x ≠ y := fun h => hk (h ▸ rfl)
  have hE : ∀ l, k ≠ l → ρ.condExp l x y = 0 := fun l hkl => by
    simp only [condExp]
    exact ite_eq_right fun h => hk (h k hkl)
  have hEE : (ρ.condExp i * ρ.condExp j) x y = 0 := by
    rw [mul_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hxz : AgreeOff i x.1 z.1
    · have hzy : ¬ AgreeOff j z.1 y.1 := fun h => hk ((hxz k hki).trans (h k hkj))
      simp only [condExp]
      rw [ite_eq_right hzy, mul_zero]
    · simp only [condExp]
      rw [ite_eq_right hxz, zero_mul]
  simp only [condDiff, sub_mul, mul_sub, one_mul, mul_one, Matrix.sub_apply,
    one_apply_ne hne, hE i hki, hE j hkj, hEE, sub_zero]

end Coordinates

end FinDist

/-- Regrouping by one coordinate: a sum over strings is a sum over the strings that are zero
at `i`, of the two assignments of that coordinate. -/
private lemma sum_eq_sum_oneFiber {M : Type} [AddCommMonoid M] (i : ι) (φ : (ι → Bool) → M) :
    ∑ x, φ x = ∑ z ∈ Finset.univ.filter (fun z : ι → Bool => z i = false),
      (φ z + φ (Function.update z i true)) := by
  rw [Finset.sum_add_distrib, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun z : ι → Bool => z i = false)]
  congr 1
  refine Finset.sum_nbij' (fun x => Function.update x i false)
    (fun z => Function.update z i true) ?_ ?_ ?_ ?_ ?_
  · intro x _
    simp
  · intro z _
    simp
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_false] at hx
    rw [Function.update_idem, ← hx, Function.update_eq_self]
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    rw [Function.update_idem, ← hz, Function.update_eq_self]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_false] at hx
    rw [Function.update_idem, ← hx, Function.update_eq_self]

/-- **Regrouping by two coordinates.** A sum over strings equals a sum over the strings that are
zero at `i` and `j`, of the four assignments of those two coordinates. -/
theorem sum_eq_sum_twoFiber {M : Type} [AddCommMonoid M] {i j : ι} (hij : i ≠ j)
    (φ : (ι → Bool) → M) :
    ∑ x, φ x = ∑ z ∈ Finset.univ.filter (fun z : ι → Bool => z i = false ∧ z j = false),
      (φ z + φ (Function.update z i true) + φ (Function.update z j true)
        + φ (Function.update (Function.update z i true) j true)) := by
  set ψ : (ι → Bool) → M := fun z =>
    if z i = false then φ z + φ (Function.update z i true) else 0 with hψ
  have h1 : ∑ x, φ x = ∑ z, ψ z := by
    rw [sum_eq_sum_oneFiber i, Finset.sum_filter]
  rw [h1, sum_eq_sum_oneFiber j, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hi : Function.update z j true i = z i := Function.update_of_ne hij _ _
  by_cases hzi : z i = false <;> by_cases hzj : z j = false <;>
    simp [hψ, hzi, hzj, hi, Function.update_comm hij, add_assoc]

/-! ## The conditioned Bernoulli distribution -/

/-- The product Bernoulli(p) mass of a string. -/
noncomputable def bernMass (p : ℝ) (x : ι → Bool) : ℝ := ∏ i, if x i then p else 1 - p

/-- `x` avoids every all-ones pattern of `F`: each `C ∈ F` has a coordinate where `x` is zero. -/
def Avoids (F : Finset (Finset ι)) (x : ι → Bool) : Prop := ∀ C ∈ F, ∃ k ∈ C, x k = false

instance (F : Finset (Finset ι)) : DecidablePred (Avoids F) := fun _ => by
  unfold Avoids; infer_instance

/-- Avoidance is downward closed. -/
theorem Avoids.mono {F : Finset (Finset ι)} {x y : ι → Bool} (hx : Avoids F x)
    (hyx : ∀ k, y k = true → x k = true) : Avoids F y := by
  intro C hC
  obtain ⟨k, hk, hxk⟩ := hx C hC
  refine ⟨k, hk, ?_⟩
  by_contra h
  rw [Bool.not_eq_false] at h
  rw [hyx k h] at hxk
  exact Bool.noConfusion hxk

/-- **Bernoulli(p) bits conditioned to avoid a family of all-ones patterns** (CGZ (4.11)). -/
structure CondBern (ι : Type) [Fintype ι] [DecidableEq ι] where
  /-- The forbidden coordinate sets. -/
  forbidden : Finset (Finset ι)
  /-- Every forbidden set is nonempty, so the all-zero string is allowed. -/
  forbidden_nonempty : ∀ C ∈ forbidden, C.Nonempty
  /-- The bias. -/
  p : ℝ
  p_pos : 0 < p
  p_le_half : p ≤ 1 / 2

namespace CondBern

variable (μ : CondBern ι)

/-- The normalizing constant `ν(Ω)`. -/
noncomputable def normConst : ℝ :=
  ∑ x, if Avoids μ.forbidden x then bernMass μ.p x else 0

private lemma one_sub_p_pos : 0 < 1 - μ.p := by linarith [μ.p_le_half]

private lemma bernMass_pos (x : ι → Bool) : 0 < bernMass μ.p x :=
  Finset.prod_pos fun i _ => by
    split_ifs
    exacts [μ.p_pos, μ.one_sub_p_pos]

theorem normConst_pos : 0 < μ.normConst := by
  unfold normConst
  refine Finset.sum_pos' (fun x _ => ?_) ⟨fun _ => false, Finset.mem_univ _, ?_⟩
  · split_ifs
    exacts [(μ.bernMass_pos x).le, le_rfl]
  · have : Avoids μ.forbidden (fun _ => false) := fun C hC => by
      obtain ⟨k, hk⟩ := μ.forbidden_nonempty C hC
      exact ⟨k, hk, rfl⟩
    rw [ite_eq_left this]
    exact μ.bernMass_pos _

/-- The conditioned mass of a string. -/
noncomputable def rawMass (x : ι → Bool) : ℝ :=
  if Avoids μ.forbidden x then bernMass μ.p x / μ.normConst else 0

theorem rawMass_nonneg (x : ι → Bool) : 0 ≤ μ.rawMass x := by
  unfold rawMass
  split_ifs
  · exact div_nonneg (μ.bernMass_pos x).le μ.normConst_pos.le
  · exact le_rfl

theorem sum_rawMass : ∑ x, μ.rawMass x = 1 := by
  have h : ∀ x, μ.rawMass x =
      (if Avoids μ.forbidden x then bernMass μ.p x else 0) / μ.normConst := by
    intro x
    unfold rawMass
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun x _ => h x, ← Finset.sum_div]
  exact div_self μ.normConst_pos.ne'

/-- **The distribution** `μ = ν( · | Ω)`. -/
noncomputable def dist : FinDist (ι → Bool) := ⟨μ.rawMass, μ.rawMass_nonneg, μ.sum_rawMass⟩

/-- The support of `μ` is exactly the set of allowed strings. -/
theorem mass_pos_iff (x : ι → Bool) : 0 < μ.dist.mass x ↔ Avoids μ.forbidden x := by
  change 0 < μ.rawMass x ↔ _
  unfold rawMass
  split_ifs with h
  · exact iff_of_true (div_pos (μ.bernMass_pos x) μ.normConst_pos) h
  · exact iff_of_false (lt_irrefl 0) h

/-- Coordinate `i` is **free** at `x`: setting it to one keeps the string allowed. -/
def Free (i : ι) (x : ι → Bool) : Prop := Avoids μ.forbidden (Function.update x i true)

instance (i : ι) : DecidablePred (μ.Free i) := fun _ => by unfold Free; infer_instance

/-- Freedom of `i` depends only on the coordinates other than `i`. -/
private lemma update_eq_update_of_agreeOff {i : ι} {x y : ι → Bool} (h : AgreeOff i x y)
    (b : Bool) : Function.update x i b = Function.update y i b := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp
  · simp [Function.update_of_ne hk, h k hk]

theorem free_congr {i : ι} {x y : ι → Bool} (h : AgreeOff i x y) : μ.Free i x ↔ μ.Free i y := by
  unfold Free
  rw [update_eq_update_of_agreeOff h]

/-- A coordinate equal to one at a support point is free there. -/
theorem free_of_true {i : ι} (x : μ.dist.Supp) (h : x.1 i = true) : μ.Free i x.1 := by
  unfold Free
  rw [← h, Function.update_eq_self]
  exact (μ.mass_pos_iff x.1).mp x.2

/-- The Bernoulli(p) weight of a bit. -/
noncomputable def bitWeight (b : Bool) : ℝ := if b then μ.p else 1 - μ.p

private lemma dist_mass_apply (x : ι → Bool) : μ.dist.mass x = μ.rawMass x := rfl

private lemma agreeOff_update (i : ι) (x : ι → Bool) (b : Bool) :
    AgreeOff i x (Function.update x i b) := fun _ hk => (Function.update_of_ne hk _ _).symm

private lemma eq_update_of_agreeOff {i : ι} {x y : ι → Bool} (h : AgreeOff i x y) :
    y = Function.update x i (y i) := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp
  · rw [Function.update_of_ne hk, h k hk]

/-- A sum over the fibre `{y | AgreeOff i x y}` of Boolean strings has two terms. -/
private lemma sum_agreeOff_bool {M : Type} [AddCommMonoid M] (i : ι) (x : ι → Bool)
    (g : (ι → Bool) → M) :
    ∑ z, (if AgreeOff i x z then g z else 0)
      = g (Function.update x i false) + g (Function.update x i true) := by
  have hne : Function.update x i false ≠ Function.update x i true := fun h => by
    simpa using congrFun h i
  rw [Fintype.sum_eq_add _ _ hne, ite_eq_left (agreeOff_update i x false),
    ite_eq_left (agreeOff_update i x true)]
  rintro z ⟨hz0, hz1⟩
  refine ite_eq_right fun h => ?_
  have hz := eq_update_of_agreeOff h
  cases hzi : z i
  · exact hz0 (by rw [hz, hzi])
  · exact hz1 (by rw [hz, hzi])

/-- The fibre mass for one coordinate of conditioned Bernoulli bits. -/
private lemma fiberMass_eq (i : ι) (x : ι → Bool) :
    μ.dist.fiberMass i x
      = μ.rawMass (Function.update x i false) + μ.rawMass (Function.update x i true) :=
  sum_agreeOff_bool i x (fun z => μ.dist.mass z)

/-- The conditioned mass of the coordinates other than `i`. -/
private noncomputable def restMass (i : ι) (x : ι → Bool) : ℝ :=
  (∏ k ∈ Finset.univ \ {i}, if x k then μ.p else 1 - μ.p) / μ.normConst

private lemma restMass_pos (i : ι) (x : ι → Bool) : 0 < μ.restMass i x :=
  div_pos (Finset.prod_pos fun _ _ => by
    split_ifs
    exacts [μ.p_pos, μ.one_sub_p_pos]) μ.normConst_pos

private lemma bernMass_update (i : ι) (x : ι → Bool) (b : Bool) :
    bernMass μ.p (Function.update x i b)
      = μ.bitWeight b * ∏ k ∈ Finset.univ \ {i}, (if x k then μ.p else 1 - μ.p) := by
  unfold bernMass bitWeight
  rw [← Finset.prod_update_of_mem (Finset.mem_univ i)]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : k = i
  · subst hk
    simp
  · simp [Function.update_of_ne hk]

private lemma avoids_update_false {i : ι} {x : ι → Bool} (h : μ.Free i x) :
    Avoids μ.forbidden (Function.update x i false) := by
  refine Avoids.mono h fun k hk => ?_
  by_cases hki : k = i
  · subst hki
    simp at hk
  · rw [Function.update_of_ne hki] at hk ⊢
    exact hk

/-- At a free coordinate both completions are allowed, with Bernoulli(p) weights. -/
private lemma rawMass_update_of_free {i : ι} {x : ι → Bool} (h : μ.Free i x) (b : Bool) :
    μ.rawMass (Function.update x i b) = μ.bitWeight b * μ.restMass i x := by
  have hav : Avoids μ.forbidden (Function.update x i b) := by
    cases b
    · exact μ.avoids_update_false h
    · exact h
  rw [rawMass, ite_eq_left hav, bernMass_update, restMass, mul_div_assoc]

private lemma rawMass_update_true_of_not_free {i : ι} {x : ι → Bool} (h : ¬ μ.Free i x) :
    μ.rawMass (Function.update x i true) = 0 := by
  rw [rawMass]
  exact ite_eq_right h

private lemma fiberMass_of_free {i : ι} {x : ι → Bool} (h : μ.Free i x) :
    μ.dist.fiberMass i x = μ.restMass i x := by
  rw [fiberMass_eq, μ.rawMass_update_of_free h, μ.rawMass_update_of_free h, bitWeight,
    bitWeight]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  ring

/-- At a forced coordinate the fibre of a support point within the support is that point. -/
private lemma eq_of_not_free {i : ι} {x y : μ.dist.Supp} (h : ¬ μ.Free i x.1)
    (hxy : AgreeOff i x.1 y.1) : x = y := by
  have hx : x.1 i = false := by
    by_contra hx
    exact h (μ.free_of_true x (by simpa using hx))
  have hy : y.1 i = false := by
    by_contra hy
    rw [Bool.not_eq_false] at hy
    have := y.2
    rw [eq_update_of_agreeOff hxy, hy, dist_mass_apply,
      μ.rawMass_update_true_of_not_free h] at this
    exact lt_irrefl 0 this
  apply Subtype.ext
  rw [eq_update_of_agreeOff hxy, hy, ← hx, Function.update_eq_self]

private lemma fiberMass_of_not_free {i : ι} {x : μ.dist.Supp} (h : ¬ μ.Free i x.1) :
    μ.dist.fiberMass i x.1 = μ.dist.mass x.1 := by
  have hx : x.1 i = false := by
    by_contra hx
    exact h (μ.free_of_true x (by simpa using hx))
  rw [fiberMass_eq, μ.rawMass_update_true_of_not_free h, add_zero, ← hx,
    Function.update_eq_self, dist_mass_apply]

/-- **The conditional law of one coordinate.** Given the other coordinates, `xᵢ` is a
Bernoulli(p) bit if `i` is free, and is forced (the fibre is a single point) otherwise. -/
theorem condWeight_eq (i : ι) (x y : μ.dist.Supp) :
    μ.dist.condWeight i x y =
      if AgreeOff i x.1 y.1 then
        (if μ.Free i x.1 then μ.bitWeight (y.1 i) else if x = y then 1 else 0)
      else 0 := by
  unfold FinDist.condWeight
  by_cases hxy : AgreeOff i x.1 y.1
  · rw [ite_eq_left hxy, ite_eq_left hxy]
    by_cases hf : μ.Free i x.1
    · have hm : μ.dist.mass y.1 = μ.bitWeight (y.1 i) * μ.restMass i x.1 := by
        rw [dist_mass_apply]
        conv_lhs => rw [eq_update_of_agreeOff hxy]
        exact μ.rawMass_update_of_free hf _
      rw [ite_eq_left hf, μ.fiberMass_of_free hf, hm, mul_div_assoc,
        div_self (μ.restMass_pos i x.1).ne', mul_one]
    · rw [ite_eq_right hf]
      obtain rfl := μ.eq_of_not_free hf hxy
      rw [ite_eq_left rfl, μ.fiberMass_of_not_free hf, div_self x.2.ne']
  · rw [ite_eq_right hxy, ite_eq_right hxy]

private lemma bitWeight_pos (b : Bool) : 0 < μ.bitWeight b := by
  unfold bitWeight
  split_ifs
  exacts [μ.p_pos, μ.one_sub_p_pos]

/-- The entries of `Eᵢ` for conditioned Bernoulli bits, in square-root weighted coordinates. -/
theorem condExp_apply_eq (i : ι) (x y : μ.dist.Supp) :
    μ.dist.condExp i x y =
      if AgreeOff i x.1 y.1 then
        (if μ.Free i x.1 then
          ((Real.sqrt (μ.bitWeight (x.1 i) * μ.bitWeight (y.1 i)) : ℝ) : ℂ)
        else if x = y then 1 else 0)
      else 0 := by
  have hw := μ.condWeight_eq i x y
  have hw0 := μ.condWeight_eq i x x
  unfold FinDist.condWeight at hw hw0
  unfold FinDist.condExp
  have hm := μ.dist.fiberMass_pos i x
  rw [ite_eq_left (AgreeOff.refl i x.1), ite_eq_left (AgreeOff.refl i x.1)] at hw0
  by_cases hxy : AgreeOff i x.1 y.1
  · rw [ite_eq_left hxy, ite_eq_left hxy]
    rw [ite_eq_left hxy, ite_eq_left hxy] at hw
    by_cases hf : μ.Free i x.1
    · rw [ite_eq_left hf] at hw hw0 ⊢
      congr 1
      rw [div_eq_iff hm.ne'] at hw hw0
      rw [hw, hw0, show μ.bitWeight (x.1 i) * μ.dist.fiberMass i x.1 *
          (μ.bitWeight (y.1 i) * μ.dist.fiberMass i x.1)
          = (μ.bitWeight (x.1 i) * μ.bitWeight (y.1 i)) *
            (μ.dist.fiberMass i x.1 * μ.dist.fiberMass i x.1) by ring,
        Real.sqrt_mul (mul_pos (μ.bitWeight_pos _) (μ.bitWeight_pos _)).le,
        Real.sqrt_mul_self hm.le, mul_div_assoc, div_self hm.ne', mul_one]
    · rw [ite_eq_right hf] at hw0 ⊢
      obtain rfl := μ.eq_of_not_free hf hxy
      rw [ite_eq_left rfl] at hw0 ⊢
      rw [Real.sqrt_mul_self (μ.dist.mass_nonneg _), hw0, Complex.ofReal_one]
  · rw [ite_eq_right hxy, ite_eq_right hxy]

private lemma two_point (b : Bool) (u v : A → ℂ) :
    u - (((μ.bitWeight b : ℝ) : ℂ) • u + ((μ.bitWeight (!b) : ℝ) : ℂ) • v)
      = ((if b then 1 - μ.p else μ.p : ℝ) : ℂ) • (u - v) := by
  funext a
  cases b <;>
  · simp only [bitWeight, Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true,
      ite_false, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring

/-- **The two-point formulas** (CGZ (4.4)): at a free coordinate,
`(Dᵢ f)⁰ = p (f⁰ − f¹)` and `(Dᵢ f)¹ = (1 − p)(f¹ − f⁰)`; at a forced coordinate `Dᵢ f = 0`. -/
theorem wvec_condDiff_mul (i : ι) (f : JVec μ.dist.Supp A) (x : μ.dist.Supp) :
    μ.dist.wvec (μ.dist.condDiff i * f) x =
      if μ.Free i x.1 then
        ((if x.1 i then 1 - μ.p else μ.p : ℝ) : ℂ) •
          (μ.dist.wvec f x - μ.dist.wvecAt f (Function.update x.1 i (!x.1 i)))
      else 0 := by
  classical
  rw [FinDist.wvec_condDiff_mul_eq_sub, FinDist.wvec_condExp_mul]
  by_cases hf : μ.Free i x.1
  · rw [ite_eq_left hf]
    have hx'av : Avoids μ.forbidden (Function.update x.1 i (!x.1 i)) := by
      cases hxi : x.1 i
      · exact hf
      · exact μ.avoids_update_false hf
    let y' : μ.dist.Supp :=
      ⟨Function.update x.1 i (!x.1 i), (μ.mass_pos_iff _).mpr hx'av⟩
    have hne : x ≠ y' := fun h => by
      have := congrArg (fun z : μ.dist.Supp => z.1 i) h
      simp [y'] at this
    have hagree : AgreeOff i x.1 y'.1 := agreeOff_update i x.1 _
    have hy'i : y'.1 i = !x.1 i := Function.update_self _ _ _
    have hwat : μ.dist.wvecAt f (Function.update x.1 i (!x.1 i)) = μ.dist.wvec f y' :=
      μ.dist.wvecAt_coe f y'
    rw [Fintype.sum_eq_add x y' hne]
    · rw [hwat, μ.condWeight_eq, μ.condWeight_eq, ite_eq_left (AgreeOff.refl _ _),
        ite_eq_left hf, ite_eq_left hagree, ite_eq_left hf, hy'i]
      exact μ.two_point _ _ _
    · rintro z ⟨hzx, hzy⟩
      rw [FinDist.condWeight, ite_eq_right, Complex.ofReal_zero, zero_smul]
      intro h
      have hz := eq_update_of_agreeOff h
      by_cases hzi : z.1 i = x.1 i
      · exact hzx (Subtype.ext (by rw [hz, hzi, Function.update_eq_self]))
      · exact hzy (Subtype.ext (by rw [hz, Bool.eq_not_of_ne hzi]))
  · rw [ite_eq_right hf]
    have h : ∀ y, (μ.dist.condWeight i x y : ℂ) • μ.dist.wvec f y
        = if x = y then μ.dist.wvec f y else 0 := by
      intro y
      rw [μ.condWeight_eq, ite_eq_right hf]
      by_cases hxy : x = y
      · subst hxy
        simp [AgreeOff.refl]
      · rw [ite_eq_right hxy, ite_eq_right hxy]
        split_ifs <;> simp
    rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _),
      sub_self]

/-- **The conditional variance** (CGZ (4.12)): each free pair `{x, x + eᵢ}` contributes
`p(1 − p)` times its total mass `μ(x)/(1 − p)`, times `‖f^{x+eᵢ} − fˣ‖²`. -/
theorem jNormSq_condDiff_mul_eq (i : ι) (f : JVec μ.dist.Supp A) :
    jNormSq (μ.dist.condDiff i * f) = ∑ x : μ.dist.Supp,
      if x.1 i = false ∧ μ.Free i x.1 then
        μ.p * μ.dist.mass x *
          qNormSq (μ.dist.wvecAt f (Function.update x.1 i true) - μ.dist.wvec f x)
      else 0 := by
  classical
  set c : (ι → Bool) → ℝ := fun z => if z i then 1 - μ.p else μ.p with hc
  set G : (ι → Bool) → ℝ := fun z => if μ.Free i z then μ.dist.mass z * (c z * c z) *
      qNormSq (μ.dist.wvecAt f z - μ.dist.wvecAt f (Function.update z i (!z i))) else 0
    with hG
  set H : (ι → Bool) → ℝ := fun z => if z i = false ∧ μ.Free i z then μ.p * μ.dist.mass z *
      qNormSq (μ.dist.wvecAt f (Function.update z i true) - μ.dist.wvecAt f z) else 0
    with hH
  have hL : jNormSq (μ.dist.condDiff i * f) = ∑ x : μ.dist.Supp, G x.1 := by
    rw [FinDist.jNormSq_eq_sum_wvec]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [μ.wvec_condDiff_mul]
    by_cases hf : μ.Free i x.1
    · rw [ite_eq_left hf, hG]
      dsimp only
      rw [ite_eq_left hf, qNormSq_smul, Complex.normSq_ofReal, FinDist.wvecAt_coe, hc]
      ring
    · rw [ite_eq_right hf, hG]
      dsimp only
      rw [ite_eq_right hf, qNormSq_zero, mul_zero]
  have hR : (∑ x : μ.dist.Supp, if x.1 i = false ∧ μ.Free i x.1 then μ.p * μ.dist.mass x *
      qNormSq (μ.dist.wvecAt f (Function.update x.1 i true) - μ.dist.wvec f x) else 0)
      = ∑ x : μ.dist.Supp, H x.1 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hH]
    dsimp only
    rw [FinDist.wvecAt_coe]
  rw [hL, hR, FinDist.sum_supp_eq_sum' μ.dist G (fun z hz => by simp [hG, hz]),
    FinDist.sum_supp_eq_sum' μ.dist H (fun z hz => by simp [hH, hz]),
    sum_eq_sum_oneFiber i G, sum_eq_sum_oneFiber i H]
  refine Finset.sum_congr rfl fun z hz => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
  have hfree : μ.Free i (Function.update z i true) ↔ μ.Free i z :=
    (μ.free_congr (agreeOff_update i z true)).symm
  have hzz : Function.update (Function.update z i true) i false = z := by
    rw [Function.update_idem, ← hz, Function.update_eq_self]
  simp only [hG, hH, hc, hz, Function.update_self, hfree, Bool.not_false, Bool.not_true, hzz]
  by_cases hf : μ.Free i z
  · have h0 := μ.rawMass_update_of_free hf false
    have h1 := μ.rawMass_update_of_free hf true
    rw [← hz, Function.update_eq_self, hz] at h0
    simp only [hf, dist_mass_apply, h0, h1, bitWeight]
    rw [FinDist.qNormSq_sub_comm' (μ.dist.wvecAt f z)]
    simp
    ring
  · simp [hf]

/-! ## Interacting coordinates -/

/-- **`Aᵢⱼ(x)`** (CGZ (4.16)): some forbidden set contains `i` and `j`, and `x` is one on the
rest of it. -/
def Interact (i j : ι) (x : ι → Bool) : Prop :=
  ∃ C ∈ μ.forbidden, i ∈ C ∧ j ∈ C ∧ ∀ k ∈ C, k ≠ i → k ≠ j → x k = true

instance (i j : ι) : DecidablePred (μ.Interact i j) := fun _ => by
  unfold Interact; infer_instance

theorem interact_comm (i j : ι) (x : ι → Bool) : μ.Interact i j x ↔ μ.Interact j i x := by
  constructor <;>
  · rintro ⟨C, hC, hi, hj, h⟩
    exact ⟨C, hC, hj, hi, fun k hk hk1 hk2 => h k hk hk2 hk1⟩

/-- `Aᵢⱼ` depends only on the coordinates outside `{i, j}`. -/
theorem interact_congr {i j : ι} {x y : ι → Bool} (h : ∀ k, k ≠ i → k ≠ j → x k = y k) :
    μ.Interact i j x ↔ μ.Interact i j y := by
  constructor
  · rintro ⟨C, hC, hi, hj, hx⟩
    exact ⟨C, hC, hi, hj, fun k hk hki hkj => (h k hki hkj).symm.trans (hx k hk hki hkj)⟩
  · rintro ⟨C, hC, hi, hj, hy⟩
    exact ⟨C, hC, hi, hj, fun k hk hki hkj => (h k hki hkj).trans (hy k hk hki hkj)⟩

/-- The diagonal operator `Aᵢⱼ` on the input register. -/
noncomputable def interactOp (i j : ι) : Matrix μ.dist.Supp μ.dist.Supp ℂ :=
  Matrix.diagonal fun x => if μ.Interact i j x.1 then 1 else 0

theorem interactOp_isHermitian (i j : ι) : (μ.interactOp i j).IsHermitian := by
  refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
  funext x
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem interactOp_mul_self (i j : ι) : μ.interactOp i j * μ.interactOp i j = μ.interactOp i j := by
  rw [interactOp, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  split_ifs <;> simp

theorem interactOp_nonneg (i j : ι) : 0 ≤ μ.interactOp i j := by
  rw [Matrix.nonneg_iff_posSemidef, interactOp, Matrix.posSemidef_diagonal_iff]
  intro x
  split_ifs <;> simp

theorem interactOp_le_one (i j : ι) : μ.interactOp i j ≤ 1 := by
  rw [Matrix.le_iff, interactOp, ← Matrix.diagonal_one, Matrix.diagonal_sub,
    Matrix.posSemidef_diagonal_iff]
  intro x
  split_ifs <;> simp

/-- `[Aᵢⱼ, Dᵢ] = 0`. -/
theorem commute_interactOp_condDiff_left (i j : ι) :
    Commute (μ.interactOp i j) (μ.dist.condDiff i) := by
  refine (μ.dist.commute_condDiff_diagonal i fun x y h => ?_).symm
  have : μ.Interact i j x.1 ↔ μ.Interact i j y.1 :=
    μ.interact_congr fun k hki _ => h k hki
  simp only [this]

/-- `[Aᵢⱼ, Dⱼ] = 0`. -/
theorem commute_interactOp_condDiff_right (i j : ι) :
    Commute (μ.interactOp i j) (μ.dist.condDiff j) := by
  refine (μ.dist.commute_condDiff_diagonal j fun x y h => ?_).symm
  have : μ.Interact i j x.1 ↔ μ.Interact i j y.1 :=
    μ.interact_congr fun k _ hkj => h k hkj
  simp only [this]

end CondBern

end QuantumQueryComplexity
