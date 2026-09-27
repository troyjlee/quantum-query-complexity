import QuantumQueryComplexity.OrAnd
import QuantumQueryComplexity.Weighted
set_option linter.style.header false

/-!
# The weighted `OR` witness and weighted `OR`-composition

The weighted star centred at the all-zero input, with weight `c i` on the
edge to the `i`-th unit input, is the optimal cost-`c` witness for `OR_n`:
its norm is `√(∑ cᵢ²)` and its `i`-th masked norm is `cᵢ`
(`norm_orWStar`, `norm_orWStar_hadamard`).

Feeding it into the weighted composition theorem gives the key inductive step
for read-once formulas:

  `ADV±(OR_k ∘ (g₁, …, g_k)) ≥ √(∑ᵢ ADV±(gᵢ)²)`

(`sqrt_sum_sq_le_advPM_composeFunFam_orN`), and the same for `AND_k` by
De Morgan.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weight function attaching `c i` to the `i`-th unit input. -/
def wOf (c : ι → ℝ) (z : ι → Bool) : ℝ := ∑ i, if z i then c i else 0

lemma wOf_unitVec (c : ι → ℝ) (i : ι) : wOf c (unitVec i) = c i := by
  rw [wOf, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [unitVec_apply, hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The weighted star witness for `OR_n` with costs `c`. -/
noncomputable def orWStar (c : ι → ℝ) : Matrix (ι → Bool) (ι → Bool) ℝ :=
  wStarMatrix unitSet zeroVec (wOf c)

lemma orWStar_isHermitian (c : ι → ℝ) : (orWStar c).IsHermitian :=
  wStarMatrix_isHermitian _ _ _

lemma starWeight_unitSet (c : ι → ℝ) :
    starWeight (unitSet : Finset (ι → Bool)) (wOf c) = ∑ i, c i * c i := by
  rw [starWeight, unitSet,
    Finset.sum_image fun i _ j _ h => unitVec_injective h]
  exact Finset.sum_congr rfl fun i _ => by rw [wOf_unitVec]

lemma orWStar_isAdvMatrix (c : ι → ℝ) :
    IsAdvMatrix (orN : (ι → Bool) → Bool) (orWStar c) := by
  refine ⟨wStarMatrix_isHermitian _ _ _, fun x y hxy => ?_⟩
  rw [orWStar, wStarMatrix, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun z hz => ?_
  obtain ⟨i, rfl⟩ := mem_unitSet.mp hz
  rw [Matrix.smul_apply, smul_eq_mul]
  refine mul_eq_zero_of_right _ (pairMatrix_apply_eq_zero ?_ ?_)
  · rintro ⟨rfl, rfl⟩
    rw [orN_unitVec, orN_zeroVec] at hxy
    exact Bool.noConfusion hxy
  · rintro ⟨rfl, rfl⟩
    rw [orN_unitVec, orN_zeroVec] at hxy
    exact Bool.noConfusion hxy

theorem norm_orWStar {c : ι → ℝ} (hc : 0 < ∑ i, c i * c i) :
    ‖orWStar c‖ = Real.sqrt (∑ i, c i * c i) := by
  rw [orWStar, norm_wStarMatrix zeroVec_notMem_unitSet
    (by rw [starWeight_unitSet]; exact hc), starWeight_unitSet]

theorem norm_orWStar_hadamard (c : ι → ℝ) (j : ι) :
    ‖orWStar c ⊙ advD j‖ = |c j| := by
  rw [orWStar, wStarMatrix_hadamard_advD, unitSet_filter, wStarMatrix,
    Finset.sum_singleton, norm_smul, Real.norm_eq_abs, wOf_unitVec,
    norm_pairMatrix, mul_one]
  intro h
  have := congrFun h j
  simp at this

/-- **The weighted `OR`-composition lower bound.**  Composing `OR_k` with
inner functions certified by witnesses `M i` gives at least
`√(∑ᵢ ‖M i‖²)`. -/
theorem sqrt_sum_sq_le_advPM_composeFunFam_orN {β : Type*} [Fintype β]
    [DecidableEq β] {g : ι → (β → Bool) → Bool}
    {M : ι → Matrix (β → Bool) (β → Bool) ℝ}
    (hM : ∀ i, IsAdvMatrix (g i) (M i))
    (hMfeas : ∀ i q, ‖M i ⊙ advD q‖ ≤ 1) (hMpos : ∀ i, 0 < ‖M i‖)
    [Nonempty ι] :
    Real.sqrt (∑ i, ‖M i‖ * ‖M i‖)
      ≤ advPM (composeFunFam (orN : (ι → Bool) → Bool) g) := by
  classical
  set c : ι → ℝ := fun i => ‖M i‖ with hcdef
  have hcpos : 0 < ∑ i, c i * c i := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    refine Finset.sum_pos' (fun i _ => mul_self_nonneg _) ⟨i₀, Finset.mem_univ _, ?_⟩
    exact mul_pos (hMpos i₀) (hMpos i₀)
  have hVpos : 0 < Real.sqrt (∑ i, c i * c i) := Real.sqrt_pos.mpr hcpos
  have hnorm : ‖orWStar c‖ = Real.sqrt (∑ i, c i * c i) := norm_orWStar hcpos
  refine advPM_composeFunFam_ge (orWStar_isAdvMatrix c) hM hMfeas hMpos
    hVpos (by rw [hnorm]; exact hVpos) fun p => ?_
  -- `‖Γf ⊙ D_p‖ · V = c_p · V = V · ‖M p‖ = ‖Γf‖ · ‖M p‖`
  rw [norm_orWStar_hadamard, hnorm, abs_of_pos (hMpos p)]
  exact le_of_eq (mul_comm _ _)

/-- Composing `AND` is composing `OR` with negated inner functions, up to
negating the output. -/
lemma composeFunFam_andN_eq {β : Type*} [Fintype β] [DecidableEq β]
    {g : ι → (β → Bool) → Bool} :
    composeFunFam (andN : (ι → Bool) → Bool) g
      = fun x => !(composeFunFam (orN : (ι → Bool) → Bool)
          (fun i u => !(g i u)) x) := by
  funext x
  show andN (tilde g x) = !(orN (tilde (fun i u => !(g i u)) x))
  rw [andN_eq]
  rfl

/-- The same bound for `AND_k`, by De Morgan. -/
theorem sqrt_sum_sq_le_advPM_composeFunFam_andN {β : Type*} [Fintype β]
    [DecidableEq β] {g : ι → (β → Bool) → Bool}
    {M : ι → Matrix (β → Bool) (β → Bool) ℝ}
    (hM : ∀ i, IsAdvMatrix (g i) (M i))
    (hMfeas : ∀ i q, ‖M i ⊙ advD q‖ ≤ 1) (hMpos : ∀ i, 0 < ‖M i‖)
    [Nonempty ι] :
    Real.sqrt (∑ i, ‖M i‖ * ‖M i‖)
      ≤ advPM (composeFunFam (andN : (ι → Bool) → Bool) g) := by
  have hg' : ∀ i, IsAdvMatrix (fun u => !(g i u)) (M i) := fun i =>
    isAdvMatrix_not.mpr (hM i)
  have h := sqrt_sum_sq_le_advPM_composeFunFam_orN hg' hMfeas hMpos
  rw [composeFunFam_andN_eq, advPM_not]
  exact h

end QuantumQueryComplexity
