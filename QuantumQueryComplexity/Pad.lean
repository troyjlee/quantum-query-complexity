import QuantumQueryComplexity.DualCompose
set_option linter.style.header false

/-!
# Padding: adding dummy variables changes nothing

A function `f` on `ι₀` extends to `padFun f` on `ι₀ ⊕ γ` by ignoring the
`γ`-variables.  We show `HasAdvValue f c → HasAdvValue (padFun f) c`, which
is what lets read-once sub-formulas of different sizes be composed over a
common variable type.

Only the *easy* direction is needed on each side, because `HasAdvValue` pins
both the primal and the dual value and weak duality closes the sandwich:

* primal `≥`: the block-diagonal matrix `padMatrix Γ` (copies of `Γ`, one per
  assignment to the dummy variables) has the same norm and the same masked
  norms as `Γ`;
* dual `≤`: a dual solution extends by zero on the dummy coordinates.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι₀ γ : Type*} [Fintype ι₀] [DecidableEq ι₀] [Fintype γ]
  [DecidableEq γ]

/-- The `ι₀`-part of a padded input. -/
def inPart (x : (ι₀ ⊕ γ) → Bool) : ι₀ → Bool := fun i => x (Sum.inl i)

/-- The dummy part of a padded input. -/
def outPart (x : (ι₀ ⊕ γ) → Bool) : γ → Bool := fun j => x (Sum.inr j)

@[simp] lemma inPart_elim (a : ι₀ → Bool) (r : γ → Bool) :
    inPart (Sum.elim a r) = a := rfl

@[simp] lemma outPart_elim (a : ι₀ → Bool) (r : γ → Bool) :
    outPart (Sum.elim a r) = r := rfl

/-- Extending a function by dummy variables. -/
def padFun (f : (ι₀ → Bool) → Bool) : ((ι₀ ⊕ γ) → Bool) → Bool :=
  fun x => f (inPart x)

lemma sum_sumArrow (F : ((ι₀ ⊕ γ) → Bool) → ℝ) :
    ∑ u : (ι₀ ⊕ γ) → Bool, F u
      = ∑ a : ι₀ → Bool, ∑ r : γ → Bool, F (Sum.elim a r) := by
  have h1 : ∑ u : (ι₀ ⊕ γ) → Bool, F u
      = ∑ p : (ι₀ → Bool) × (γ → Bool), F (Sum.elim p.1 p.2) := by
    refine Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow ι₀ γ Bool) _ _
      fun u => ?_
    congr 1
    funext s
    cases s <;> rfl
  rw [h1, Fintype.sum_prod_type]

/-- The block-diagonal padding of an adversary matrix: one copy of `Γ` for
each assignment to the dummy variables. -/
noncomputable def padMatrix (Γ : Matrix (ι₀ → Bool) (ι₀ → Bool) ℝ) :
    Matrix ((ι₀ ⊕ γ) → Bool) ((ι₀ ⊕ γ) → Bool) ℝ :=
  Matrix.of fun x y =>
    if outPart x = outPart y then Γ (inPart x) (inPart y) else 0

@[simp] lemma padMatrix_apply (Γ : Matrix (ι₀ → Bool) (ι₀ → Bool) ℝ)
    (x y : (ι₀ ⊕ γ) → Bool) :
    (padMatrix (γ := γ) Γ) x y =
      if outPart x = outPart y then Γ (inPart x) (inPart y) else 0 := rfl

lemma padMatrix_isHermitian {Γ : Matrix (ι₀ → Bool) (ι₀ → Bool) ℝ}
    (hΓ : Γ.IsHermitian) : (padMatrix (γ := γ) Γ).IsHermitian := by
  show (padMatrix (γ := γ) Γ)ᴴ = _
  ext x y
  simp only [Matrix.conjTranspose_apply, padMatrix_apply, star_trivial]
  by_cases h : outPart x = outPart y
  · rw [if_pos h, if_pos h.symm, isHermitian_apply_symm hΓ]
  · rw [if_neg h, if_neg fun h' => h h'.symm]

/-- The bilinear form of a padded matrix splits over the dummy blocks. -/
lemma padMatrix_bilinear (Γ : Matrix (ι₀ → Bool) (ι₀ → Bool) ℝ)
    (x y : ((ι₀ ⊕ γ) → Bool) → ℝ) :
    x ⬝ᵥ (padMatrix (γ := γ) Γ) *ᵥ y
      = ∑ r : γ → Bool, ((fun a => x (Sum.elim a r)) ⬝ᵥ
          Γ *ᵥ (fun b => y (Sum.elim b r))) := by
  rw [dotProduct_mulVec_eq_sum, sum_sumArrow]
  have hstep : ∀ (a : ι₀ → Bool) (r : γ → Bool),
      (∑ v : (ι₀ ⊕ γ) → Bool, x (Sum.elim a r) *
          (padMatrix (γ := γ) Γ) (Sum.elim a r) v * y v)
      = ∑ b : ι₀ → Bool, x (Sum.elim a r) * Γ a b * y (Sum.elim b r) := by
    intro a r
    rw [sum_sumArrow]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_eq_single r]
    · rw [padMatrix_apply, outPart_elim, outPart_elim, if_pos rfl,
        inPart_elim, inPart_elim]
    · intro s _ hs
      rw [padMatrix_apply, outPart_elim, outPart_elim,
        if_neg fun h => hs h.symm, mul_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) =>
    Finset.sum_congr rfl fun r (_ : r ∈ Finset.univ) => hstep a r]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [dotProduct_mulVec_eq_sum]

lemma sum_dotProduct_blocks (x : ((ι₀ ⊕ γ) → Bool) → ℝ) :
    (∑ r : γ → Bool, ((fun a => x (Sum.elim a r)) ⬝ᵥ
      (fun a => x (Sum.elim a r)))) = x ⬝ᵥ x := by
  show (∑ r : γ → Bool, ∑ a : ι₀ → Bool, _) = ∑ u, x u * x u
  rw [sum_sumArrow, Finset.sum_comm]

lemma norm_padMatrix_le (Γ : Matrix (ι₀ → Bool) (ι₀ → Bool) ℝ) :
    ‖padMatrix (γ := γ) Γ‖ ≤ ‖Γ‖ := by
  refine l2_opNorm_le_of_forall_dotProduct _ (norm_nonneg Γ) fun x y => ?_
  rw [padMatrix_bilinear]
  calc |∑ r : γ → Bool, ((fun a => x (Sum.elim a r)) ⬝ᵥ
        Γ *ᵥ (fun b => y (Sum.elim b r)))|
      ≤ ∑ r : γ → Bool, |(fun a => x (Sum.elim a r)) ⬝ᵥ
          Γ *ᵥ (fun b => y (Sum.elim b r))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : γ → Bool, ‖Γ‖ *
          (Real.sqrt ((fun a => x (Sum.elim a r)) ⬝ᵥ (fun a => x (Sum.elim a r)))
            * Real.sqrt ((fun b => y (Sum.elim b r)) ⬝ᵥ
              (fun b => y (Sum.elim b r)))) := by
        refine Finset.sum_le_sum fun r _ => ?_
        rw [← mul_assoc]
        exact abs_dotProduct_mulVec_le _ _ _
    _ = ‖Γ‖ * ∑ r : γ → Bool,
          (Real.sqrt ((fun a => x (Sum.elim a r)) ⬝ᵥ (fun a => x (Sum.elim a r)))
            * Real.sqrt ((fun b => y (Sum.elim b r)) ⬝ᵥ
              (fun b => y (Sum.elim b r)))) := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖Γ‖ * (Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y)) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg Γ)
        have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun r : γ → Bool => Real.sqrt ((fun a => x (Sum.elim a r)) ⬝ᵥ
            (fun a => x (Sum.elim a r))))
          (fun r : γ → Bool => Real.sqrt ((fun b => y (Sum.elim b r)) ⬝ᵥ
            (fun b => y (Sum.elim b r))))
        simpa [Real.sq_sqrt (dotProduct_self_nonneg _),
          sum_dotProduct_blocks] using hcs
    _ = ‖Γ‖ * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := (mul_assoc _ _ _).symm

lemma le_norm_padMatrix (Γ : Matrix (ι₀ → Bool) (ι₀ → Bool) ℝ) :
    ‖Γ‖ ≤ ‖padMatrix (γ := γ) Γ‖ := by
  classical
  refine l2_opNorm_le_of_forall_dotProduct _ (norm_nonneg _) fun a b => ?_
  set r₀ : γ → Bool := fun _ => false with hr₀
  set a' : ((ι₀ ⊕ γ) → Bool) → ℝ :=
    fun u => if outPart u = r₀ then a (inPart u) else 0 with ha'
  set b' : ((ι₀ ⊕ γ) → Bool) → ℝ :=
    fun u => if outPart u = r₀ then b (inPart u) else 0 with hb'
  have hblockA : ∀ r : γ → Bool, (fun c => a' (Sum.elim c r))
      = if r = r₀ then a else 0 := by
    intro r
    funext c
    by_cases h : r = r₀
    · rw [ha']
      simp [h]
    · rw [ha']
      simp [h]
  have hblockB : ∀ r : γ → Bool, (fun c => b' (Sum.elim c r))
      = if r = r₀ then b else 0 := by
    intro r
    funext c
    by_cases h : r = r₀
    · rw [hb']
      simp [h]
    · rw [hb']
      simp [h]
  have hbil : a' ⬝ᵥ (padMatrix (γ := γ) Γ) *ᵥ b' = a ⬝ᵥ Γ *ᵥ b := by
    rw [padMatrix_bilinear]
    rw [Finset.sum_eq_single r₀]
    · rw [hblockA, hblockB, if_pos rfl, if_pos rfl]
    · intro r _ hr
      rw [hblockA, if_neg hr]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hnormA : a' ⬝ᵥ a' = a ⬝ᵥ a := by
    rw [← sum_dotProduct_blocks a', Finset.sum_eq_single r₀]
    · rw [hblockA, if_pos rfl]
    · intro r _ hr
      rw [hblockA, if_neg hr]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hnormB : b' ⬝ᵥ b' = b ⬝ᵥ b := by
    rw [← sum_dotProduct_blocks b', Finset.sum_eq_single r₀]
    · rw [hblockB, if_pos rfl]
    · intro r _ hr
      rw [hblockB, if_neg hr]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  have h := abs_dotProduct_mulVec_le (padMatrix (γ := γ) Γ) a' b'
  rw [hbil, hnormA, hnormB] at h
  exact h

theorem norm_padMatrix (Γ : Matrix (ι₀ → Bool) (ι₀ → Bool) ℝ) :
    ‖padMatrix (γ := γ) Γ‖ = ‖Γ‖ :=
  le_antisymm (norm_padMatrix_le Γ) (le_norm_padMatrix Γ)

/-! ## Masks -/

lemma padMatrix_hadamard_inl (Γ : Matrix (ι₀ → Bool) (ι₀ → Bool) ℝ) (i : ι₀) :
    (padMatrix (γ := γ) Γ) ⊙ advD (Sum.inl i) = padMatrix (γ := γ) (Γ ⊙ advD i) := by
  ext x y
  simp only [Matrix.hadamard_apply, padMatrix_apply, advD_apply]
  by_cases h : outPart x = outPart y
  · by_cases hi : x (Sum.inl i) = y (Sum.inl i) <;>
      simp [h, hi, inPart]
  · simp [h]

lemma padMatrix_hadamard_inr (Γ : Matrix (ι₀ → Bool) (ι₀ → Bool) ℝ) (j : γ) :
    (padMatrix (γ := γ) Γ) ⊙ advD (Sum.inr j) = 0 := by
  ext x y
  simp only [Matrix.hadamard_apply, padMatrix_apply, advD_apply,
    Matrix.zero_apply]
  by_cases h : outPart x = outPart y
  · rw [if_pos (show x (Sum.inr j) = y (Sum.inr j) from congrFun h j), mul_zero]
  · rw [if_neg h, zero_mul]

lemma padMatrix_isAdvMatrix {f : (ι₀ → Bool) → Bool}
    {Γ : Matrix (ι₀ → Bool) (ι₀ → Bool) ℝ} (h : IsAdvMatrix f Γ) :
    IsAdvMatrix (padFun (γ := γ) f) (padMatrix (γ := γ) Γ) := by
  refine ⟨padMatrix_isHermitian h.isHermitian, fun x y hxy => ?_⟩
  rw [padMatrix_apply]
  by_cases hr : outPart x = outPart y
  · rw [if_pos hr]
    exact h.apply_eq_zero hxy
  · rw [if_neg hr]

theorem advPM_le_advPM_padFun (f : (ι₀ → Bool) → Bool) :
    advPM f ≤ advPM (padFun (γ := γ) f) := by
  refine advPM_le fun Γ h1 h2 => ?_
  have hfeas : ∀ ℓ : ι₀ ⊕ γ, ‖(padMatrix (γ := γ) Γ) ⊙ advD ℓ‖ ≤ 1 := by
    rintro (i | j)
    · rw [padMatrix_hadamard_inl, norm_padMatrix]
      exact h2 i
    · rw [padMatrix_hadamard_inr, norm_zero]
      exact zero_le_one
  have h := le_advPM (padMatrix_isAdvMatrix h1) hfeas
  rwa [norm_padMatrix] at h

/-! ## Padding a dual solution -/

/-- A dual solution extends to the padded function by zero on the dummy
coordinates. -/
def DualPair.pad {K : Type*} [Fintype K] {f : (ι₀ → Bool) → Bool}
    (P : DualPair K f) : DualPair K (padFun (γ := γ) f) where
  u x ℓ k := Sum.elim (fun i => P.u (inPart x) i k) (fun _ => 0) ℓ
  v x ℓ k := Sum.elim (fun i => P.v (inPart x) i k) (fun _ => 0) ℓ
  constraint x y := by
    trans (if f (inPart x) = f (inPart y) then (0:ℝ) else 1)
    · rw [← P.constraint (inPart x) (inPart y), Fintype.sum_sum_type]
      have hright : ∀ j : γ,
          (if x (Sum.inr j) = y (Sum.inr j) then (0:ℝ)
            else ∑ k : K, Sum.elim (fun i' : ι₀ => P.u (inPart x) i' k)
                (fun _ : γ => (0:ℝ)) (Sum.inr j) *
              Sum.elim (fun i' : ι₀ => P.v (inPart y) i' k)
                (fun _ : γ => (0:ℝ)) (Sum.inr j)) = 0 := by
        intro j
        by_cases h : x (Sum.inr j) = y (Sum.inr j) <;> simp [h]
      rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hright j,
        Finset.sum_const_zero, add_zero]
      exact Finset.sum_congr rfl fun i _ => rfl
    · rfl

lemma DualPair.pad_isCostLe {K : Type*} [Fintype K] {f : (ι₀ → Bool) → Bool}
    {P : DualPair K f} {c : ℝ} (hc : 0 ≤ c) (h : P.IsCostLe c) :
    (P.pad (γ := γ)).IsCostLe c := by
  constructor
  · intro x
    have hsplit : (∑ ℓ : ι₀ ⊕ γ, ∑ k : K,
        (P.pad (γ := γ)).u x ℓ k * (P.pad (γ := γ)).u x ℓ k)
        = ∑ i : ι₀, ∑ k : K, P.u (inPart x) i k * P.u (inPart x) i k := by
      rw [Fintype.sum_sum_type]
      simp [DualPair.pad]
    show (∑ ℓ : ι₀ ⊕ γ, ∑ k : K, _) ≤ c
    rw [hsplit]
    exact h.1 (inPart x)
  · intro x
    have hsplit : (∑ ℓ : ι₀ ⊕ γ, ∑ k : K,
        (P.pad (γ := γ)).v x ℓ k * (P.pad (γ := γ)).v x ℓ k)
        = ∑ i : ι₀, ∑ k : K, P.v (inPart x) i k * P.v (inPart x) i k := by
      rw [Fintype.sum_sum_type]
      simp [DualPair.pad]
    show (∑ ℓ : ι₀ ⊕ γ, ∑ k : K, _) ≤ c
    rw [hsplit]
    exact h.2 (inPart x)

theorem advDual_padFun_le (f : (ι₀ → Bool) → Bool) :
    advDual (padFun (γ := γ) f) ≤ advDual f := by
  refine le_csInf (dualCosts_nonempty f) ?_
  rintro c ⟨hc, n, P, hP⟩
  exact advDual_le_of_dualPair (P.pad (γ := γ)) hc (P.pad_isCostLe hc hP)

/-- **Padding preserves a certified adversary value.** -/
theorem HasAdvValue.pad {f : (ι₀ → Bool) → Bool} {c : ℝ}
    (h : HasAdvValue f c) : HasAdvValue (padFun (γ := γ) f) c :=
  hasAdvValue_of_le (h.1 ▸ advPM_le_advPM_padFun f)
    (le_of_le_of_eq (advDual_padFun_le f) h.2)

end QuantumQueryComplexity
