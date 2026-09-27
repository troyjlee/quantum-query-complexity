import QuantumQueryComplexity.Defs
import QuantumQueryComplexity.Spectral
set_option linter.style.header false

/-!
# Basic properties of the adversary bound

Accessor lemmas for `advPM` as a conditionally complete supremum, the a priori
bound `‖Γ‖ ≤ card²` for feasible matrices (which makes the value set bounded
above), and the un-normalized witness lemma `norm_div_le_advPM` — the workhorse
for proving lower bounds on `advPM`.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {O : Type*} {f : (ι → σ) → O} {Γ : Matrix (ι → σ) (ι → σ) ℝ}

lemma advPM_set_nonempty (f : (ι → σ) → O) :
    {r : ℝ | ∃ Γ, IsAdvMatrix f Γ ∧ (∀ i, ‖Γ ⊙ advD i‖ ≤ 1) ∧
      r = ‖Γ‖}.Nonempty :=
  ⟨‖(0 : Matrix (ι → σ) (ι → σ) ℝ)‖, 0, isAdvMatrix_zero f,
    fun i => by simp, rfl⟩

/-- All entries of a feasible matrix are bounded by `1` in absolute value:
off-diagonal entries embed into some `Γ ⊙ advD i`, and entries with
`f x = f y` (in particular the diagonal) vanish. -/
lemma abs_apply_le_one_of_feasible (h1 : IsAdvMatrix f Γ)
    (h2 : ∀ i, ‖Γ ⊙ advD i‖ ≤ 1) (x y : ι → σ) : |Γ x y| ≤ 1 := by
  by_cases hf : f x = f y
  · simp [h1.apply_eq_zero hf]
  · have hxy : x ≠ y := fun h => hf (by rw [h])
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    have h3 := abs_entry_le_l2_opNorm (Γ ⊙ advD i) x y
    rw [hadamard_advD_apply, if_neg hi] at h3
    exact h3.trans (h2 i)

/-- The a priori bound making the `advPM` value set bounded above. -/
lemma norm_le_of_feasible (h1 : IsAdvMatrix f Γ)
    (h2 : ∀ i, ‖Γ ⊙ advD i‖ ≤ 1) :
    ‖Γ‖ ≤ (Fintype.card (ι → σ) : ℝ) ^ 2 := by
  refine (l2_opNorm_le_sum_abs Γ).trans ?_
  calc ∑ x, ∑ y, |Γ x y| ≤ ∑ _x : ι → σ, ∑ _y : ι → σ, (1 : ℝ) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
        abs_apply_le_one_of_feasible h1 h2 x y
    _ = (Fintype.card (ι → σ) : ℝ) ^ 2 := by
      simp [Finset.sum_const, Finset.card_univ, pow_two]

lemma bddAbove_advPM_set (f : (ι → σ) → O) :
    BddAbove {r : ℝ | ∃ Γ, IsAdvMatrix f Γ ∧ (∀ i, ‖Γ ⊙ advD i‖ ≤ 1) ∧
      r = ‖Γ‖} := by
  refine ⟨(Fintype.card (ι → σ) : ℝ) ^ 2, ?_⟩
  rintro r ⟨Γ, h1, h2, rfl⟩
  exact norm_le_of_feasible h1 h2

/-- Every feasible matrix certifies a lower bound on `advPM`. -/
theorem le_advPM (h1 : IsAdvMatrix f Γ) (h2 : ∀ i, ‖Γ ⊙ advD i‖ ≤ 1) :
    ‖Γ‖ ≤ advPM f :=
  le_csSup (bddAbove_advPM_set f) ⟨Γ, h1, h2, rfl⟩

theorem advPM_nonneg (f : (ι → σ) → O) : 0 ≤ advPM f := by
  simpa using le_advPM (isAdvMatrix_zero f) fun i => by simp

theorem advPM_le {c : ℝ}
    (hc : ∀ Γ, IsAdvMatrix f Γ → (∀ i, ‖Γ ⊙ advD i‖ ≤ 1) → ‖Γ‖ ≤ c) :
    advPM f ≤ c := by
  refine csSup_le (advPM_set_nonempty f) ?_
  rintro r ⟨Γ, h1, h2, rfl⟩
  exact hc Γ h1 h2

/-- ε-accessor: any value below `advPM f` is beaten by a feasible witness. -/
theorem exists_lt_of_lt_advPM {c : ℝ} (h : c < advPM f) :
    ∃ Γ, IsAdvMatrix f Γ ∧ (∀ i, ‖Γ ⊙ advD i‖ ≤ 1) ∧ c < ‖Γ‖ := by
  obtain ⟨r, hr, hcr⟩ := exists_lt_of_lt_csSup (advPM_set_nonempty f) h
  obtain ⟨Γ, h1, h2, rfl⟩ := hr
  exact ⟨Γ, h1, h2, hcr⟩

/-- **Un-normalized witness lemma**: an adversary matrix all of whose Schur
norms are at most `c` certifies `‖Γ‖ / c ≤ advPM f`.  This is the paper's
ratio formulation, division-free at the point of use. -/
theorem norm_div_le_advPM (h1 : IsAdvMatrix f Γ) {c : ℝ}
    (h2 : ∀ i, ‖Γ ⊙ advD i‖ ≤ c) (hc : 0 < c) : ‖Γ‖ / c ≤ advPM f := by
  have k1 : IsAdvMatrix f (c⁻¹ • Γ) := h1.smul c⁻¹
  have k2 : ∀ i, ‖(c⁻¹ • Γ) ⊙ advD i‖ ≤ 1 := fun i => by
    rw [Matrix.smul_hadamard, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hc)]
    calc c⁻¹ * ‖Γ ⊙ advD i‖ ≤ c⁻¹ * c :=
        mul_le_mul_of_nonneg_left (h2 i) (inv_pos.mpr hc).le
      _ = 1 := inv_mul_cancel₀ hc.ne'
  have h := le_advPM k1 k2
  rwa [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc),
    inv_mul_eq_div] at h

theorem adv_le_advPM (f : (ι → σ) → O) : adv f ≤ advPM f := by
  refine csSup_le ?_ ?_
  · exact ⟨‖(0 : Matrix (ι → σ) (ι → σ) ℝ)‖, 0, isAdvMatrix_zero f,
      fun i => by simp, fun x y => le_rfl, rfl⟩
  · rintro r ⟨Γ, h1, h2, -, rfl⟩
    exact le_advPM h1 h2

theorem advPM_eq_zero_of_forall_eq (h : ∀ x y, f x = f y) : advPM f = 0 :=
  le_antisymm
    (advPM_le fun Γ hΓ _ => by
      have hΓ0 : Γ = 0 := by
        ext x y
        rw [Matrix.zero_apply]
        exact hΓ.apply_eq_zero (h x y)
      simp [hΓ0])
    (advPM_nonneg f)

/-! ## The elementary two-entry witness -/

/-- The elementary adversary matrix `e_{xy} + e_{yx}` supported on a single
symmetric pair of entries. -/
def pairMatrix (x y : ι → σ) : Matrix (ι → σ) (ι → σ) ℝ :=
  Matrix.single x y 1 + Matrix.single y x 1

lemma pairMatrix_isHermitian (x y : ι → σ) :
    (pairMatrix x y).IsHermitian := by
  show (pairMatrix x y)ᴴ = pairMatrix x y
  ext a b
  simp only [Matrix.conjTranspose_apply, pairMatrix, Matrix.add_apply,
    Matrix.single_apply, star_trivial]
  rw [add_comm]
  congr 1
  · exact if_congr (by tauto) rfl rfl
  · exact if_congr (by tauto) rfl rfl

lemma single_one_mulVec (a b : ι → σ) (u : (ι → σ) → ℝ) :
    Matrix.single a b (1 : ℝ) *ᵥ u = fun w => if a = w then u b else 0 := by
  funext w
  by_cases haw : a = w
  · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, ite_and, haw]
  · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, ite_and, haw]

lemma pairMatrix_mulVec (x y : ι → σ) (u : (ι → σ) → ℝ) :
    pairMatrix x y *ᵥ u
      = fun w => (if x = w then u y else 0) + if y = w then u x else 0 := by
  rw [pairMatrix, Matrix.add_mulVec, single_one_mulVec, single_one_mulVec]
  rfl

lemma pairMatrix_apply_eq_zero {x y a b : ι → σ} (h1 : ¬(x = a ∧ y = b))
    (h2 : ¬(y = a ∧ x = b)) : pairMatrix x y a b = 0 := by
  simp [pairMatrix, Matrix.single_apply, h1, h2]

/-- Masking a pair matrix by a difference matrix either leaves it alone or
kills it, according to whether the pair differs in that coordinate. -/
lemma pairMatrix_hadamard_advD (x y : ι → σ) (i : ι) :
    pairMatrix x y ⊙ advD i = if x i = y i then 0 else pairMatrix x y := by
  by_cases hi : x i = y i
  · rw [if_pos hi]
    ext a b
    rw [Matrix.hadamard_apply, Matrix.zero_apply, advD_apply]
    by_cases h1 : x = a ∧ y = b
    · obtain ⟨rfl, rfl⟩ := h1
      rw [if_pos hi, mul_zero]
    · by_cases h2 : y = a ∧ x = b
      · obtain ⟨rfl, rfl⟩ := h2
        rw [if_pos hi.symm, mul_zero]
      · rw [pairMatrix_apply_eq_zero h1 h2, zero_mul]
  · rw [if_neg hi]
    ext a b
    rw [Matrix.hadamard_apply, advD_apply]
    by_cases h1 : x = a ∧ y = b
    · obtain ⟨rfl, rfl⟩ := h1
      rw [if_neg hi, mul_one]
    · by_cases h2 : y = a ∧ x = b
      · obtain ⟨rfl, rfl⟩ := h2
        rw [if_neg fun h => hi h.symm, mul_one]
      · rw [pairMatrix_apply_eq_zero h1 h2, zero_mul]

lemma norm_pairMatrix {x y : ι → σ} (hxy : x ≠ y) : ‖pairMatrix x y‖ = 1 := by
  classical
  -- `norm_le_of_eigenvector_family` needs `[Nonempty (ι → σ)]`; the hypothesis
  -- `x` supplies the witness, so no `[Nonempty σ]` instance is required.
  haveI : Nonempty (ι → σ) := ⟨x⟩
  have hmul : ∀ u : (ι → σ) → ℝ, pairMatrix x y *ᵥ u
      = fun w => (if x = w then u y else 0) + if y = w then u x else 0 := by
    intro u
    rw [pairMatrix, Matrix.add_mulVec, single_one_mulVec, single_one_mulVec]
    rfl
  refine le_antisymm ?_ ?_
  · set v : (ι → σ) → (ι → σ) → ℝ := fun z =>
      if z = x then Pi.single x 1 + Pi.single y 1
      else if z = y then Pi.single x 1 - Pi.single y 1
      else Pi.single z 1 with hv
    set μ : (ι → σ) → ℝ := fun z =>
      if z = x then 1 else if z = y then -1 else 0 with hμ
    have hvx : v x = Pi.single x 1 + Pi.single y 1 := by rw [hv]; simp
    have hvy : v y = Pi.single x 1 - Pi.single y 1 := by
      rw [hv]; simp [Ne.symm hxy]
    have hvz : ∀ z, z ≠ x → z ≠ y → v z = Pi.single z 1 := by
      intro z h1 h2; rw [hv]; simp [h1, h2]
    have hμx : μ x = 1 := by rw [hμ]; simp
    have hμy : μ y = -1 := by rw [hμ]; simp [Ne.symm hxy]
    have hμz : ∀ z, z ≠ x → z ≠ y → μ z = 0 := by
      intro z h1 h2; rw [hμ]; simp [h1, h2]
    refine norm_le_of_eigenvector_family (pairMatrix_isHermitian x y) v μ
      zero_le_one ?_ ?_ ?_
    · intro z
      by_cases hzx : z = x
      · rw [hzx, hvx, hμx, hmul]
        funext w
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, one_smul,
          smul_eq_mul, one_mul]
        by_cases hwx : w = x <;> by_cases hwy : w = y
        · exact absurd (hwx.symm.trans hwy) hxy
        · simp [hwx, hxy, Ne.symm hxy]
        · simp [hwy, hxy, Ne.symm hxy]
        · simp [hwx, hwy, Ne.symm hwx, Ne.symm hwy]
      · by_cases hzy : z = y
        · rw [hzy, hvy, hμy, hmul]
          funext w
          simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
          by_cases hwx : w = x <;> by_cases hwy : w = y
          · exact absurd (hwx.symm.trans hwy) hxy
          · simp [hwx, hxy, Ne.symm hxy]
          · simp [hwy, hxy, Ne.symm hxy]
          · simp [hwx, hwy, Ne.symm hwx, Ne.symm hwy]
        · rw [hvz z hzx hzy, hμz z hzx hzy, hmul]
          funext w
          simp [Pi.single_apply, Ne.symm hzx, Ne.symm hzy]
    · rw [eq_top_iff, ← (Pi.basisFun ℝ (ι → σ)).span_eq]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨z, rfl⟩
      rw [Pi.basisFun_apply]
      by_cases hzx : z = x
      · rw [hzx]
        have hx2 : (Pi.single x 1 : (ι → σ) → ℝ)
            = (2⁻¹ : ℝ) • (v x + v y) := by
          rw [hvx, hvy]
          funext w
          simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
          ring
        rw [hx2]
        exact Submodule.smul_mem _ _ (Submodule.add_mem _
          (Submodule.subset_span ⟨x, rfl⟩) (Submodule.subset_span ⟨y, rfl⟩))
      · by_cases hzy : z = y
        · rw [hzy]
          have hy2 : (Pi.single y 1 : (ι → σ) → ℝ)
              = (2⁻¹ : ℝ) • (v x - v y) := by
            rw [hvx, hvy]
            funext w
            simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
            ring
          rw [hy2]
          exact Submodule.smul_mem _ _ (Submodule.sub_mem _
            (Submodule.subset_span ⟨x, rfl⟩) (Submodule.subset_span ⟨y, rfl⟩))
        · rw [← hvz z hzx hzy]
          exact Submodule.subset_span ⟨z, rfl⟩
    · intro z
      simp only [hμ]
      split_ifs <;> norm_num
  · have h := abs_entry_le_l2_opNorm (pairMatrix x y) x y
    have hval : pairMatrix x y x y = 1 := by
      simp [pairMatrix, Matrix.single_apply, Ne.symm hxy]
    rw [hval] at h
    simpa using h

theorem one_le_advPM {x y : ι → σ} (hf : f x ≠ f y) : 1 ≤ advPM f := by
  have hxy : x ≠ y := fun h => hf (by rw [h])
  have hadv : IsAdvMatrix f (pairMatrix x y) := by
    refine ⟨pairMatrix_isHermitian x y, ?_⟩
    intro a b hab
    by_cases h1 : x = a ∧ y = b
    · obtain ⟨rfl, rfl⟩ := h1
      exact absurd hab hf
    · by_cases h2 : y = a ∧ x = b
      · obtain ⟨rfl, rfl⟩ := h2
        exact absurd hab.symm hf
      · simp [pairMatrix, Matrix.single_apply, h1, h2]
  have hfeas : ∀ i, ‖pairMatrix x y ⊙ advD i‖ ≤ 1 := by
    intro i
    by_cases hi : x i = y i
    · have h0 : pairMatrix x y ⊙ advD i = 0 := by
        ext a b
        rw [Matrix.hadamard_apply, Matrix.zero_apply, advD_apply]
        by_cases h1 : x = a ∧ y = b
        · obtain ⟨rfl, rfl⟩ := h1
          rw [if_pos hi, mul_zero]
        · by_cases h2 : y = a ∧ x = b
          · obtain ⟨rfl, rfl⟩ := h2
            rw [if_pos hi.symm, mul_zero]
          · have hz : pairMatrix x y a b = 0 := by
              simp [pairMatrix, Matrix.single_apply, h1, h2]
            rw [hz, zero_mul]
      rw [h0, norm_zero]
      exact zero_le_one
    · have h1 : pairMatrix x y ⊙ advD i = pairMatrix x y := by
        ext a b
        rw [Matrix.hadamard_apply, advD_apply]
        by_cases h1 : x = a ∧ y = b
        · obtain ⟨rfl, rfl⟩ := h1
          rw [if_neg hi, mul_one]
        · by_cases h2 : y = a ∧ x = b
          · obtain ⟨rfl, rfl⟩ := h2
            rw [if_neg (fun h => hi h.symm), mul_one]
          · have hz : pairMatrix x y a b = 0 := by
              simp [pairMatrix, Matrix.single_apply, h1, h2]
            rw [hz, zero_mul]
      rw [h1, norm_pairMatrix hxy]
  have h := le_advPM hadv hfeas
  rwa [norm_pairMatrix hxy] at h

theorem advPM_eq_zero_iff : advPM f = 0 ↔ ∀ x y, f x = f y := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    obtain ⟨x, y, hxy⟩ := hc
    have h1 := one_le_advPM hxy
    rw [h] at h1
    norm_num at h1
  · exact advPM_eq_zero_of_forall_eq

end QuantumQueryComplexity
