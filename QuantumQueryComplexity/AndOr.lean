import QuantumQueryComplexity.DualCompose
set_option linter.style.header false

/-!
# The two-bit AND and OR functions have adversary bound `√2`

We compute `ADV±(AND₂) = ADV±(OR₂) = √2` *with a matching dual certificate*,
i.e. we establish `HasAdvValue and2 (√2)` and `HasAdvValue or2 (√2)`.  Strong
duality is therefore available at these functions unconditionally, so the
perfect composition theorem applies to them.

The primal witness is the star matrix of HLŠ §6: the adversary matrix
supported on the two edges joining `11` to its neighbours `01` and `10`.  Its
spectral norm is `√2` and each masked norm `‖Γ ⊙ D_i‖` is `1`.

The dual witness is one-dimensional (`K = Unit`), with weights
`α = 2^(-1/4)` at `11`, `β = 2^(1/4)` on the sensitive coordinate of each
neighbour, and `δ = 2^(1/4)/2` at `00`; its cost is exactly `√2`.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-! ## Enumeration of the four two-bit inputs -/

/-- The input `00`. -/
abbrev i00 : Fin 2 → Bool := ![false, false]
/-- The input `01`. -/
abbrev i01 : Fin 2 → Bool := ![false, true]
/-- The input `10`. -/
abbrev i10 : Fin 2 → Bool := ![true, false]
/-- The input `11`. -/
abbrev i11 : Fin 2 → Bool := ![true, true]

lemma fin2Bool_cases (w : Fin 2 → Bool) :
    w = i00 ∨ w = i01 ∨ w = i10 ∨ w = i11 := by decide +revert

lemma sum_fin2Bool (f : (Fin 2 → Bool) → ℝ) :
    ∑ w : Fin 2 → Bool, f w = f i00 + f i01 + f i10 + f i11 := by
  rw [show (Finset.univ : Finset (Fin 2 → Bool)) = {i00, i01, i10, i11} from
    by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

lemma dotProduct_fin2Bool (x y : (Fin 2 → Bool) → ℝ) :
    x ⬝ᵥ y = x i00 * y i00 + x i01 * y i01 + x i10 * y i10 + x i11 * y i11 :=
  sum_fin2Bool fun w => x w * y w

/-! ## The two-bit AND function and its primal witness -/

/-- The two-bit AND function. -/
def and2 : (Fin 2 → Bool) → Bool := fun x => x 0 && x 1

/-- The star adversary matrix for `AND₂`, centred at `11`. -/
noncomputable def and2Gamma : Matrix (Fin 2 → Bool) (Fin 2 → Bool) ℝ :=
  pairMatrix i01 i11 + pairMatrix i10 i11

lemma and2Gamma_mulVec_apply (y : (Fin 2 → Bool) → ℝ) (w : Fin 2 → Bool) :
    (and2Gamma *ᵥ y) w
      = ((if i01 = w then y i11 else 0) + (if i11 = w then y i01 else 0))
        + ((if i10 = w then y i11 else 0) + (if i11 = w then y i10 else 0)) := by
  rw [and2Gamma, Matrix.add_mulVec, pairMatrix_mulVec, pairMatrix_mulVec]
  rfl

lemma and2Gamma_bilinear (x y : (Fin 2 → Bool) → ℝ) :
    x ⬝ᵥ and2Gamma *ᵥ y
      = (x i01 + x i10) * y i11 + x i11 * (y i01 + y i10) := by
  rw [show x ⬝ᵥ and2Gamma *ᵥ y = ∑ w, x w * (and2Gamma *ᵥ y) w from rfl,
    sum_fin2Bool]
  simp only [and2Gamma_mulVec_apply]
  norm_num +decide
  ring

lemma norm_and2Gamma_le : ‖and2Gamma‖ ≤ Real.sqrt 2 := by
  refine l2_opNorm_le_of_forall_dotProduct _ (Real.sqrt_nonneg 2) fun x y => ?_
  rw [and2Gamma_bilinear]
  have hx := dotProduct_fin2Bool x x
  have hy := dotProduct_fin2Bool y y
  have hcs : ((x i01 + x i10) * y i11 + x i11 * (y i01 + y i10)) ^ 2
      ≤ ((x i01 + x i10) ^ 2 / 2 + (x i11) ^ 2) *
        (2 * (y i11) ^ 2 + (y i01 + y i10) ^ 2) := by
    nlinarith [sq_nonneg ((x i01 + x i10) * (y i01 + y i10) - 2 * x i11 * y i11)]
  have hX : (x i01 + x i10) ^ 2 / 2 + (x i11) ^ 2 ≤ x ⬝ᵥ x := by
    rw [hx]
    nlinarith [sq_nonneg (x i01 - x i10), sq_nonneg (x i00)]
  have hY : 2 * (y i11) ^ 2 + (y i01 + y i10) ^ 2 ≤ 2 * (y ⬝ᵥ y) := by
    rw [hy]
    nlinarith [sq_nonneg (y i01 - y i10), sq_nonneg (y i00)]
  have hsq : ((x i01 + x i10) * y i11 + x i11 * (y i01 + y i10)) ^ 2
      ≤ 2 * (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
    calc ((x i01 + x i10) * y i11 + x i11 * (y i01 + y i10)) ^ 2
        ≤ ((x i01 + x i10) ^ 2 / 2 + (x i11) ^ 2) *
          (2 * (y i11) ^ 2 + (y i01 + y i10) ^ 2) := hcs
      _ ≤ (x ⬝ᵥ x) * (2 * (y ⬝ᵥ y)) :=
          mul_le_mul hX hY (by positivity) (dotProduct_self_nonneg x)
      _ = 2 * (x ⬝ᵥ x) * (y ⬝ᵥ y) := by ring
  calc |(x i01 + x i10) * y i11 + x i11 * (y i01 + y i10)|
      = Real.sqrt (((x i01 + x i10) * y i11 + x i11 * (y i01 + y i10)) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (2 * (x ⬝ᵥ x) * (y ⬝ᵥ y)) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt 2 * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
        rw [Real.sqrt_mul
            (mul_nonneg (by norm_num) (dotProduct_self_nonneg x)),
          Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]

/-- The top eigenvector of the star matrix. -/
noncomputable def and2Vec : (Fin 2 → Bool) → ℝ :=
  fun w => if w = i01 then 1 else if w = i10 then 1
    else if w = i11 then Real.sqrt 2 else 0

lemma sqrt_two_le_norm_and2Gamma : Real.sqrt 2 ≤ ‖and2Gamma‖ := by
  have h := abs_dotProduct_mulVec_le and2Gamma and2Vec and2Vec
  rw [and2Gamma_bilinear] at h
  have e00 : and2Vec i00 = 0 := by norm_num [and2Vec]
  have e01 : and2Vec i01 = 1 := by norm_num [and2Vec]
  have e10 : and2Vec i10 = 1 := by norm_num [and2Vec]
  have e11 : and2Vec i11 = Real.sqrt 2 := by norm_num [and2Vec]
  have hdot : and2Vec ⬝ᵥ and2Vec = 4 := by
    rw [dotProduct_fin2Bool, e00, e01, e10, e11,
      Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have h4 : Real.sqrt (4:ℝ) = 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [e01, e10, e11, hdot, h4] at h
  have habs : |(1 + 1 : ℝ) * Real.sqrt 2 + Real.sqrt 2 * (1 + 1)|
      = 4 * Real.sqrt 2 := by
    rw [abs_of_nonneg (by positivity)]
    ring
  rw [habs] at h
  linarith

lemma norm_and2Gamma : ‖and2Gamma‖ = Real.sqrt 2 :=
  le_antisymm norm_and2Gamma_le sqrt_two_le_norm_and2Gamma

lemma and2Gamma_isAdvMatrix : IsAdvMatrix and2 and2Gamma := by
  refine ⟨(pairMatrix_isHermitian _ _).add (pairMatrix_isHermitian _ _), ?_⟩
  intro x y hxy
  rw [and2Gamma, Matrix.add_apply]
  have h1 : ¬(i01 = x ∧ i11 = y) := by
    rintro ⟨rfl, rfl⟩
    exact absurd hxy (by simp [and2])
  have h2 : ¬(i11 = x ∧ i01 = y) := by
    rintro ⟨rfl, rfl⟩
    exact absurd hxy (by simp [and2])
  have h3 : ¬(i10 = x ∧ i11 = y) := by
    rintro ⟨rfl, rfl⟩
    exact absurd hxy (by simp [and2])
  have h4 : ¬(i11 = x ∧ i10 = y) := by
    rintro ⟨rfl, rfl⟩
    exact absurd hxy (by simp [and2])
  rw [pairMatrix_apply_eq_zero h1 h2, pairMatrix_apply_eq_zero h3 h4, add_zero]

lemma and2Gamma_hadamard_zero : and2Gamma ⊙ advD 0 = pairMatrix i01 i11 := by
  rw [and2Gamma, Matrix.add_hadamard, pairMatrix_hadamard_advD,
    pairMatrix_hadamard_advD, if_neg (by decide), if_pos (by decide), add_zero]

lemma and2Gamma_hadamard_one : and2Gamma ⊙ advD 1 = pairMatrix i10 i11 := by
  rw [and2Gamma, Matrix.add_hadamard, pairMatrix_hadamard_advD,
    pairMatrix_hadamard_advD, if_pos (by decide), if_neg (by decide), zero_add]

lemma and2Gamma_feasible : ∀ i : Fin 2, ‖and2Gamma ⊙ advD i‖ ≤ 1 := by
  rw [Fin.forall_fin_two]
  constructor
  · rw [and2Gamma_hadamard_zero, norm_pairMatrix (by decide)]
  · rw [and2Gamma_hadamard_one, norm_pairMatrix (by decide)]

theorem sqrt_two_le_advPM_and2 : Real.sqrt 2 ≤ advPM and2 := by
  have h := le_advPM and2Gamma_isAdvMatrix and2Gamma_feasible
  rwa [norm_and2Gamma] at h

/-! ## The dual witness -/

/-- `β = 2^(1/4)`. -/
noncomputable def and2Beta : ℝ := Real.sqrt (Real.sqrt 2)
/-- `α = 2^(-1/4)`. -/
noncomputable def and2Alpha : ℝ := 1 / and2Beta
/-- `δ = 2^(1/4)/2`. -/
noncomputable def and2Delta : ℝ := and2Beta / 2

lemma and2Beta_pos : 0 < and2Beta :=
  Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by norm_num))

lemma and2Beta_ne_zero : and2Beta ≠ 0 := ne_of_gt and2Beta_pos

lemma and2Beta_sq : and2Beta * and2Beta = Real.sqrt 2 :=
  Real.mul_self_sqrt (Real.sqrt_nonneg 2)

lemma sqrt_two_pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

lemma two_div_sqrt_two : 2 / Real.sqrt 2 = Real.sqrt 2 := by
  rw [eq_comm, eq_div_iff (ne_of_gt sqrt_two_pos),
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- The one-dimensional dual weights for `AND₂`. -/
noncomputable def and2DualVec (x : Fin 2 → Bool) (i : Fin 2) : ℝ :=
  if x 0 && x 1 then and2Alpha
  else if x 0 || x 1 then (if x i then 0 else and2Beta)
  else and2Delta

/-- The dual solution for `AND₂`. -/
noncomputable def and2Dual : DualPair Unit and2 where
  u x i _ := and2DualVec x i
  v x i _ := and2DualVec x i
  constraint x y := by
    have hβ : and2Beta ≠ 0 := and2Beta_ne_zero
    rw [Fin.sum_univ_two]
    rcases fin2Bool_cases x with rfl | rfl | rfl | rfl <;>
      rcases fin2Bool_cases y with rfl | rfl | rfl | rfl <;>
      simp [and2DualVec, and2, and2Alpha, and2Delta] <;>
      field_simp <;> norm_num

lemma and2Alpha_sq : and2Alpha * and2Alpha = 1 / Real.sqrt 2 := by
  rw [and2Alpha, div_mul_div_comm, one_mul, and2Beta_sq]

lemma and2Alpha_cost :
    and2Alpha * and2Alpha + and2Alpha * and2Alpha = Real.sqrt 2 := by
  rw [and2Alpha_sq, show 1 / Real.sqrt 2 + 1 / Real.sqrt 2
      = 2 / Real.sqrt 2 by ring]
  exact two_div_sqrt_two

lemma and2Delta_cost :
    and2Delta * and2Delta + and2Delta * and2Delta ≤ Real.sqrt 2 := by
  rw [and2Delta, show and2Beta / 2 * (and2Beta / 2)
      + and2Beta / 2 * (and2Beta / 2) = and2Beta * and2Beta / 2 by ring,
    and2Beta_sq]
  linarith [sqrt_two_pos]

lemma and2Dual_isCostLe : and2Dual.IsCostLe (Real.sqrt 2) := by
  have key : ∀ x : Fin 2 → Bool,
      (∑ i : Fin 2, ∑ _k : Unit, and2DualVec x i * and2DualVec x i)
        ≤ Real.sqrt 2 := by
    intro x
    rw [Fin.sum_univ_two]
    rcases fin2Bool_cases x with rfl | rfl | rfl | rfl
    · simpa [and2DualVec] using and2Delta_cost
    · simpa [and2DualVec] using le_of_eq and2Beta_sq
    · simpa [and2DualVec] using le_of_eq and2Beta_sq
    · simpa [and2DualVec] using le_of_eq and2Alpha_cost
  exact ⟨key, key⟩

theorem advDual_and2_le : advDual and2 ≤ Real.sqrt 2 :=
  advDual_le_of_dualPair and2Dual (Real.sqrt_nonneg 2) and2Dual_isCostLe

/-- **`ADV±(AND₂) = √2`, with a matching dual certificate.** -/
theorem hasAdvValue_and2 : HasAdvValue and2 (Real.sqrt 2) :=
  hasAdvValue_of_le sqrt_two_le_advPM_and2 advDual_and2_le

/-! ## Invariance of the adversary bound under relabelling

Negating the output, or negating a set of input bits, changes neither the
primal nor the dual value.  This transfers the `AND₂` computation to `OR₂`.
-/

section Invariance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma isAdvMatrix_not {f : (ι → Bool) → Bool}
    {Γ : Matrix (ι → Bool) (ι → Bool) ℝ} :
    IsAdvMatrix (fun x => !(f x)) Γ ↔ IsAdvMatrix f Γ := by
  constructor
  · exact fun h => ⟨h.1, fun x y hxy => h.2 x y (congrArg (fun b => !b) hxy)⟩
  · exact fun h => ⟨h.1, fun x y hxy => h.2 x y (Bool.not_inj hxy)⟩

theorem advPM_not (f : (ι → Bool) → Bool) :
    advPM (fun x => !(f x)) = advPM f := by
  have key : ∀ g : (ι → Bool) → Bool,
      advPM (fun x => !(g x)) ≤ advPM g := fun g =>
    advPM_le fun Γ h1 h2 => le_advPM (isAdvMatrix_not.mp h1) h2
  refine le_antisymm (key f) ?_
  have h := key (fun x => !(f x))
  simpa using h

/-- Transport of a dual solution along output negation. -/
def DualPair.notFun {K : Type*} [Fintype K] {f : (ι → Bool) → Bool}
    (P : DualPair K f) : DualPair K (fun x => !(f x)) where
  u := P.u
  v := P.v
  constraint x y := by
    rw [P.constraint x y]
    by_cases h : f x = f y
    · rw [if_pos h, if_pos (by simp [h])]
    · rw [if_neg h, if_neg (by simpa using h)]

theorem advDual_not (f : (ι → Bool) → Bool) :
    advDual (fun x => !(f x)) = advDual f := by
  have key : ∀ g : (ι → Bool) → Bool,
      advDual (fun x => !(g x)) ≤ advDual g := by
    intro g
    refine le_csInf (dualCosts_nonempty g) ?_
    rintro c ⟨hc, n, P, hP⟩
    exact advDual_le_of_dualPair P.notFun hc ⟨hP.1, hP.2⟩
  refine le_antisymm (key f) ?_
  have h := key (fun x => !(f x))
  simpa using h

/-- Negating every input bit. -/
def flipAll : (ι → Bool) ≃ (ι → Bool) where
  toFun x := fun i => !(x i)
  invFun x := fun i => !(x i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

lemma flipAll_apply (x : ι → Bool) (i : ι) : flipAll x i = !(x i) := rfl

lemma flipAll_coord_iff (x y : ι → Bool) (i : ι) :
    (flipAll x i = flipAll y i) ↔ (x i = y i) := by
  simp [flipAll_apply]

lemma isAdvMatrix_comp_flipAll {f : (ι → Bool) → Bool}
    {Γ : Matrix (ι → Bool) (ι → Bool) ℝ} (h : IsAdvMatrix f Γ) :
    IsAdvMatrix (fun x => f (flipAll x))
      (Γ.submatrix flipAll flipAll) := by
  refine ⟨?_, fun x y hxy => h.2 _ _ hxy⟩
  show (Γ.submatrix flipAll flipAll)ᴴ = _
  ext a b
  simp only [Matrix.conjTranspose_apply, Matrix.submatrix_apply, star_trivial]
  exact (isHermitian_apply_symm h.1 _ _).symm

lemma submatrix_flipAll_hadamard (Γ : Matrix (ι → Bool) (ι → Bool) ℝ) (i : ι) :
    (Γ.submatrix flipAll flipAll) ⊙ advD i
      = (Γ ⊙ advD i).submatrix flipAll flipAll := by
  ext x y
  simp only [Matrix.hadamard_apply, Matrix.submatrix_apply, advD_apply]
  by_cases hi : x i = y i
  · rw [if_pos hi, if_pos ((flipAll_coord_iff x y i).mpr hi)]
  · rw [if_neg hi, if_neg (fun h => hi ((flipAll_coord_iff x y i).mp h))]

theorem advPM_comp_flipAll (f : (ι → Bool) → Bool) :
    advPM (fun x => f (flipAll x)) = advPM f := by
  have key : ∀ g : (ι → Bool) → Bool,
      advPM (fun x => g (flipAll x)) ≤ advPM g := by
    intro g
    refine advPM_le fun Γ h1 h2 => ?_
    have hsub : IsAdvMatrix g (Γ.submatrix flipAll flipAll) := by
      refine ⟨?_, fun x y hxy => ?_⟩
      · show (Γ.submatrix flipAll flipAll)ᴴ = _
        ext a b
        simp only [Matrix.conjTranspose_apply, Matrix.submatrix_apply,
          star_trivial]
        exact (isHermitian_apply_symm h1.1 _ _).symm
      · refine h1.2 _ _ ?_
        show g (flipAll (flipAll x)) = g (flipAll (flipAll y))
        simpa [flipAll] using hxy
    have hfeas : ∀ i, ‖(Γ.submatrix flipAll flipAll) ⊙ advD i‖ ≤ 1 := by
      intro i
      rw [submatrix_flipAll_hadamard, l2_opNorm_submatrix_equiv]
      exact h2 i
    have := le_advPM hsub hfeas
    rwa [l2_opNorm_submatrix_equiv] at this
  refine le_antisymm (key f) ?_
  have h := key (fun x => f (flipAll x))
  have hff : (fun x => f (flipAll (flipAll x))) = f := by
    funext x
    congr 1
    funext i
    simp [flipAll]
  rwa [hff] at h

/-- Transport of a dual solution along input negation. -/
def DualPair.compFlipAll {K : Type*} [Fintype K] {f : (ι → Bool) → Bool}
    (P : DualPair K f) : DualPair K (fun x => f (flipAll x)) where
  u x i k := P.u (flipAll x) i k
  v x i k := P.v (flipAll x) i k
  constraint x y := by
    rw [← P.constraint (flipAll x) (flipAll y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : x i = y i
    · rw [if_pos hi, if_pos ((flipAll_coord_iff x y i).mpr hi)]
    · rw [if_neg hi, if_neg (fun h => hi ((flipAll_coord_iff x y i).mp h))]

theorem advDual_comp_flipAll (f : (ι → Bool) → Bool) :
    advDual (fun x => f (flipAll x)) = advDual f := by
  have key : ∀ g : (ι → Bool) → Bool,
      advDual (fun x => g (flipAll x)) ≤ advDual g := by
    intro g
    refine le_csInf (dualCosts_nonempty g) ?_
    rintro c ⟨hc, n, P, hP⟩
    refine advDual_le_of_dualPair P.compFlipAll hc ⟨?_, ?_⟩
    · exact fun x => hP.1 (flipAll x)
    · exact fun x => hP.2 (flipAll x)
  refine le_antisymm (key f) ?_
  have h := key (fun x => f (flipAll x))
  have hff : (fun x => f (flipAll (flipAll x))) = f := by
    funext x
    congr 1
    funext i
    simp [flipAll]
  rwa [hff] at h

theorem HasAdvValue.not {f : (ι → Bool) → Bool} {c : ℝ} (h : HasAdvValue f c) :
    HasAdvValue (fun x => !(f x)) c :=
  ⟨by rw [advPM_not]; exact h.1, by rw [advDual_not]; exact h.2⟩

theorem HasAdvValue.compFlipAll {f : (ι → Bool) → Bool} {c : ℝ}
    (h : HasAdvValue f c) : HasAdvValue (fun x => f (flipAll x)) c :=
  ⟨by rw [advPM_comp_flipAll]; exact h.1,
    by rw [advDual_comp_flipAll]; exact h.2⟩

end Invariance

/-! ## The two-bit OR function -/

/-- The two-bit OR function. -/
def or2 : (Fin 2 → Bool) → Bool := fun x => x 0 || x 1

lemma or2_eq : or2 = fun x => !(and2 (flipAll x)) := by
  funext x
  simp [or2, and2, flipAll]

/-- **`ADV±(OR₂) = √2`, with a matching dual certificate.** -/
theorem hasAdvValue_or2 : HasAdvValue or2 (Real.sqrt 2) := by
  rw [or2_eq]
  exact hasAdvValue_and2.compFlipAll.not

end QuantumQueryComplexity
