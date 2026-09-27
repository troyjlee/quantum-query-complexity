import QuantumQueryComplexity.WeightedOr
set_option linter.style.header false

/-!
# The weighted dual and weighted dual composition

The cost side of the weighted composition theorem.  Composing an outer dual
solution with inner ones of costs `c i` gives a composed cost

  `∑_p c_p ‖ψ_{x̃,p}‖²`,

which is the **`c`-weighted** cost of the outer solution
(`DualPair.IsWeightedCostLe`).  So `DualPair.compose_isWeightedCostLe` turns
a weighted outer bound into an ordinary bound on the composition.

For `OR_n` with costs `c` the optimal weighted dual is one-dimensional, with
`δₚ = √cₚ / √V` at the all-zero input (where `V = √(∑ cᵢ²)`) and
`1 / (∑_{p ∈ supp x} δₚ)` on the support of each nonzero `x`; its `c`-weighted
cost is exactly `V` (`orWDual_isWeightedCostLe`).  Composing gives

  `advDual (OR_k ∘ (g₁, …, g_k)) ≤ √(∑ᵢ cᵢ²)`

whenever the inner functions have dual solutions of cost `cᵢ`
(`advDual_composeFunFam_orN_le`), matching the primal bound of
`QuantumQueryComplexity/WeightedOr.lean`.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-! ## The weighted cost of a dual solution -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `c`-weighted cost of a dual solution is bounded by `V`.

Stated for a general alphabet and output type: the weighted cost is what the
outer solution of a composition must control, and in
`QuantumQueryComplexity/ComposeShared.lean` the outer function is a non-Boolean maximum. -/
def DualPair.IsWeightedCostLe {K : Type*} [Fintype K] {σ : Type*} [DecidableEq σ]
    {O : Type*} [DecidableEq O] {f : (ι → σ) → O}
    (P : DualPair K f) (c : ι → ℝ) (V : ℝ) : Prop :=
  (∀ x, ∑ i, c i * ∑ k, P.u x i k * P.u x i k ≤ V) ∧
  (∀ x, ∑ i, c i * ∑ k, P.v x i k * P.v x i k ≤ V)

section Compose

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  {f : (α → Bool) → Bool} {g : α → (β → Bool) → Bool}
  {K₁ K₂ : Type*} [Fintype K₁] [Fintype K₂]

/-- **Weighted dual composition**: a `c`-weighted outer bound composes with
inner solutions of costs `c i` to an ordinary bound. -/
lemma DualPair.compose_isWeightedCostLe {Pf : DualPair K₁ f}
    {Pg : ∀ i, DualPair K₂ (g i)} {c : α → ℝ} {V : ℝ}
    (hf : Pf.IsWeightedCostLe c V) (hg : ∀ i, (Pg i).IsCostLe (c i)) :
    (Pf.compose Pg).IsCostLe V := by
  constructor
  · intro x
    show (∑ ℓ : α × β, ∑ k : K₁ × K₂,
      (Pf.u (tilde g x) ℓ.1 k.1 * (Pg ℓ.1).u (slice x ℓ.1) ℓ.2 k.2) *
      (Pf.u (tilde g x) ℓ.1 k.1 * (Pg ℓ.1).u (slice x ℓ.1) ℓ.2 k.2)) ≤ V
    rw [Fintype.sum_prod_type]
    have hin : ∀ (p : α) (q : β),
        (∑ k : K₁ × K₂,
          (Pf.u (tilde g x) p k.1 * (Pg p).u (slice x p) q k.2) *
          (Pf.u (tilde g x) p k.1 * (Pg p).u (slice x p) q k.2))
        = (∑ k₁, Pf.u (tilde g x) p k₁ * Pf.u (tilde g x) p k₁) *
          (∑ k₂, (Pg p).u (slice x p) q k₂ * (Pg p).u (slice x p) q k₂) := by
      intro p q
      rw [Fintype.sum_prod_type]
      show (∑ k₁, ∑ k₂,
          (Pf.u (tilde g x) p k₁ * (Pg p).u (slice x p) q k₂) *
          (Pf.u (tilde g x) p k₁ * (Pg p).u (slice x p) q k₂)) = _
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun k₁ _ =>
        Finset.sum_congr rfl fun k₂ _ => by ring
    have hSnn : ∀ p : α,
        0 ≤ ∑ k₁, Pf.u (tilde g x) p k₁ * Pf.u (tilde g x) p k₁ :=
      fun p => Finset.sum_nonneg fun k₁ _ => mul_self_nonneg _
    calc (∑ p : α, ∑ q : β, ∑ k : K₁ × K₂,
          (Pf.u (tilde g x) p k.1 * (Pg p).u (slice x p) q k.2) *
          (Pf.u (tilde g x) p k.1 * (Pg p).u (slice x p) q k.2))
        = ∑ p : α, (∑ k₁, Pf.u (tilde g x) p k₁ * Pf.u (tilde g x) p k₁) *
            (∑ q : β, ∑ k₂, (Pg p).u (slice x p) q k₂ *
              (Pg p).u (slice x p) q k₂) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun q _ => hin p q
      _ ≤ ∑ p : α, (∑ k₁, Pf.u (tilde g x) p k₁ * Pf.u (tilde g x) p k₁) * c p :=
          Finset.sum_le_sum fun p _ =>
            mul_le_mul_of_nonneg_left ((hg p).1 (slice x p)) (hSnn p)
      _ = ∑ p : α, c p *
            ∑ k₁, Pf.u (tilde g x) p k₁ * Pf.u (tilde g x) p k₁ :=
          Finset.sum_congr rfl fun p _ => mul_comm _ _
      _ ≤ V := hf.1 (tilde g x)
  · intro x
    show (∑ ℓ : α × β, ∑ k : K₁ × K₂,
      (Pf.v (tilde g x) ℓ.1 k.1 * (Pg ℓ.1).v (slice x ℓ.1) ℓ.2 k.2) *
      (Pf.v (tilde g x) ℓ.1 k.1 * (Pg ℓ.1).v (slice x ℓ.1) ℓ.2 k.2)) ≤ V
    rw [Fintype.sum_prod_type]
    have hin : ∀ (p : α) (q : β),
        (∑ k : K₁ × K₂,
          (Pf.v (tilde g x) p k.1 * (Pg p).v (slice x p) q k.2) *
          (Pf.v (tilde g x) p k.1 * (Pg p).v (slice x p) q k.2))
        = (∑ k₁, Pf.v (tilde g x) p k₁ * Pf.v (tilde g x) p k₁) *
          (∑ k₂, (Pg p).v (slice x p) q k₂ * (Pg p).v (slice x p) q k₂) := by
      intro p q
      rw [Fintype.sum_prod_type]
      show (∑ k₁, ∑ k₂,
          (Pf.v (tilde g x) p k₁ * (Pg p).v (slice x p) q k₂) *
          (Pf.v (tilde g x) p k₁ * (Pg p).v (slice x p) q k₂)) = _
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun k₁ _ =>
        Finset.sum_congr rfl fun k₂ _ => by ring
    have hSnn : ∀ p : α,
        0 ≤ ∑ k₁, Pf.v (tilde g x) p k₁ * Pf.v (tilde g x) p k₁ :=
      fun p => Finset.sum_nonneg fun k₁ _ => mul_self_nonneg _
    calc (∑ p : α, ∑ q : β, ∑ k : K₁ × K₂,
          (Pf.v (tilde g x) p k.1 * (Pg p).v (slice x p) q k.2) *
          (Pf.v (tilde g x) p k.1 * (Pg p).v (slice x p) q k.2))
        = ∑ p : α, (∑ k₁, Pf.v (tilde g x) p k₁ * Pf.v (tilde g x) p k₁) *
            (∑ q : β, ∑ k₂, (Pg p).v (slice x p) q k₂ *
              (Pg p).v (slice x p) q k₂) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun q _ => hin p q
      _ ≤ ∑ p : α, (∑ k₁, Pf.v (tilde g x) p k₁ * Pf.v (tilde g x) p k₁) * c p :=
          Finset.sum_le_sum fun p _ =>
            mul_le_mul_of_nonneg_left ((hg p).2 (slice x p)) (hSnn p)
      _ = ∑ p : α, c p *
            ∑ k₁, Pf.v (tilde g x) p k₁ * Pf.v (tilde g x) p k₁ :=
          Finset.sum_congr rfl fun p _ => mul_comm _ _
      _ ≤ V := hf.2 (tilde g x)

end Compose

/-! ## The weighted `OR` dual -/

lemma sum_sq_le_sq_sum {S : Finset ι} {a : ι → ℝ} (ha : ∀ i ∈ S, 0 ≤ a i) :
    ∑ i ∈ S, a i * a i ≤ (∑ i ∈ S, a i) * ∑ i ∈ S, a i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  exact Finset.single_le_sum (fun j hj => mul_nonneg (ha i hi) (ha j hj)) hi

variable (c : ι → ℝ)

/-- The target value `V = √(∑ cᵢ²)`. -/
noncomputable def orWVal : ℝ := Real.sqrt (∑ i, c i * c i)

lemma orWVal_sq : orWVal c * orWVal c = ∑ i, c i * c i :=
  Real.mul_self_sqrt (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)

lemma orWVal_pos [Nonempty ι] (hc : ∀ i, 0 < c i) : 0 < orWVal c := by
  rw [orWVal]
  refine Real.sqrt_pos.mpr ?_
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  exact Finset.sum_pos' (fun i _ => (mul_pos (hc i) (hc i)).le)
    ⟨i₀, Finset.mem_univ _, mul_pos (hc i₀) (hc i₀)⟩

/-- `δₚ = √cₚ / √V`. -/
noncomputable def orWDelta (p : ι) : ℝ :=
  Real.sqrt (c p) / Real.sqrt (orWVal c)

/-- `D x = ∑_{p ∈ supp x} δₚ`. -/
noncomputable def orWSupp (x : ι → Bool) : ℝ :=
  ∑ p, if x p then orWDelta c p else 0

/-- The support sum of square roots, `∑_{p ∈ supp x} √cₚ`. -/
noncomputable def orWSqrtSupp (x : ι → Bool) : ℝ :=
  ∑ p, if x p then Real.sqrt (c p) else 0

variable {c}

lemma orWDelta_pos [Nonempty ι] (hc : ∀ i, 0 < c i) (p : ι) :
    0 < orWDelta c p :=
  div_pos (Real.sqrt_pos.mpr (hc p)) (Real.sqrt_pos.mpr (orWVal_pos c hc))

lemma exists_true_of_ne_zeroVec {x : ι → Bool} (hx : x ≠ zeroVec) :
    ∃ p, x p = true := by
  by_contra h
  push_neg at h
  exact hx (funext fun p => by simpa using h p)

lemma orWSqrtSupp_pos [Nonempty ι] (hc : ∀ i, 0 < c i) {x : ι → Bool}
    (hx : x ≠ zeroVec) : 0 < orWSqrtSupp c x := by
  obtain ⟨p₀, hp₀⟩ := exists_true_of_ne_zeroVec hx
  rw [orWSqrtSupp]
  refine Finset.sum_pos' (fun p _ => ?_) ⟨p₀, Finset.mem_univ _, ?_⟩
  · by_cases h : x p
    · rw [if_pos h]
      exact Real.sqrt_nonneg _
    · rw [if_neg h]
  · rw [if_pos hp₀]
    exact Real.sqrt_pos.mpr (hc p₀)

lemma orWSupp_eq [Nonempty ι] (hc : ∀ i, 0 < c i) (x : ι → Bool) :
    orWSupp c x = orWSqrtSupp c x / Real.sqrt (orWVal c) := by
  rw [orWSupp, orWSqrtSupp, Finset.sum_div]
  exact Finset.sum_congr rfl fun p _ => by
    by_cases h : x p <;> simp [h, orWDelta]

lemma orWSupp_pos [Nonempty ι] (hc : ∀ i, 0 < c i) {x : ι → Bool}
    (hx : x ≠ zeroVec) : 0 < orWSupp c x := by
  rw [orWSupp_eq hc]
  exact div_pos (orWSqrtSupp_pos hc hx)
    (Real.sqrt_pos.mpr (orWVal_pos c hc))

/-- The one-dimensional weighted dual weights for `OR_n`. -/
noncomputable def orWDualVec (c : ι → ℝ) (x : ι → Bool) (p : ι) : ℝ :=
  if x = zeroVec then orWDelta c p
  else if x p then 1 / orWSupp c x else 0

/-- The weighted dual solution for `OR_n`. -/
noncomputable def orWDual [Nonempty ι] (hc : ∀ i, 0 < c i) :
    DualPair Unit (orN : (ι → Bool) → Bool) where
  u x p _ := orWDualVec c x p
  v x p _ := orWDualVec c x p
  constraint x y := by
    by_cases hx : x = zeroVec <;> by_cases hy : y = zeroVec
    · subst hx; subst hy
      rw [if_pos rfl]
      exact Finset.sum_eq_zero fun p _ => if_pos rfl
    · subst hx
      have hne : ¬(orN (zeroVec : ι → Bool) = orN y) := by
        rw [orN_zeroVec, orN_eq_true_iff.mpr hy]
        simp
      rw [if_neg hne]
      have hstep : ∀ p : ι,
          (if (zeroVec : ι → Bool) p = y p then (0:ℝ)
            else ∑ _k : Unit, orWDualVec c zeroVec p * orWDualVec c y p)
          = if y p = true then orWDelta c p * (1 / orWSupp c y) else 0 := by
        intro p
        by_cases hyp : y p = true
        · rw [if_neg (by rw [zeroVec_apply, hyp]; exact Bool.noConfusion),
            if_pos hyp]
          simp [orWDualVec, hy, hyp]
        · simp only [Bool.not_eq_true] at hyp
          rw [if_pos (by rw [zeroVec_apply, hyp]), if_neg (by simp [hyp])]
      rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) => hstep p]
      rw [show (∑ p : ι, if y p = true then
            orWDelta c p * (1 / orWSupp c y) else 0)
          = (∑ p : ι, if y p = true then orWDelta c p else 0) *
            (1 / orWSupp c y) from by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => by
          by_cases h : y p <;> simp [h]]
      rw [← orWSupp]
      have hDpos : 0 < orWSupp c y := orWSupp_pos hc hy
      field_simp
    · subst hy
      have hne : ¬(orN x = orN (zeroVec : ι → Bool)) := by
        rw [orN_zeroVec, orN_eq_true_iff.mpr hx]
        simp
      rw [if_neg hne]
      have hstep : ∀ p : ι,
          (if x p = (zeroVec : ι → Bool) p then (0:ℝ)
            else ∑ _k : Unit, orWDualVec c x p * orWDualVec c zeroVec p)
          = if x p = true then (1 / orWSupp c x) * orWDelta c p else 0 := by
        intro p
        by_cases hxp : x p = true
        · rw [if_neg (by rw [zeroVec_apply, hxp]; exact Bool.noConfusion),
            if_pos hxp]
          simp [orWDualVec, hx, hxp]
        · simp only [Bool.not_eq_true] at hxp
          rw [if_pos (by rw [zeroVec_apply, hxp]), if_neg (by simp [hxp])]
      rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) => hstep p]
      rw [show (∑ p : ι, if x p = true then
            (1 / orWSupp c x) * orWDelta c p else 0)
          = (1 / orWSupp c x) *
            ∑ p : ι, (if x p = true then orWDelta c p else 0) from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by
          by_cases h : x p <;> simp [h]]
      rw [← orWSupp]
      have hDpos : 0 < orWSupp c x := orWSupp_pos hc hx
      field_simp
    · rw [if_pos (by rw [orN_eq_true_iff.mpr hx, orN_eq_true_iff.mpr hy])]
      refine Finset.sum_eq_zero fun p _ => ?_
      by_cases hp : x p = y p
      · rw [if_pos hp]
      · rw [if_neg hp]
        have hzero : orWDualVec c x p * orWDualVec c y p = 0 := by
          rcases Bool.eq_false_or_eq_true (x p) with hxp | hxp
          · have hyp : y p = false := by
              rcases Bool.eq_false_or_eq_true (y p) with h | h
              · exact absurd (hxp.trans h.symm) hp
              · exact h
            have h0 : orWDualVec c y p = 0 := by
              rw [orWDualVec, if_neg hy, if_neg (by simp [hyp] : ¬(y p = true))]
            rw [h0, mul_zero]
          · have h0 : orWDualVec c x p = 0 := by
              rw [orWDualVec, if_neg hx, if_neg (by simp [hxp] : ¬(x p = true))]
            rw [h0, zero_mul]
        simpa using hzero

theorem orWDual_isWeightedCostLe [Nonempty ι] (hc : ∀ i, 0 < c i) :
    (orWDual hc).IsWeightedCostLe c (orWVal c) := by
  have hV : 0 < orWVal c := orWVal_pos c hc
  have hsV : 0 < Real.sqrt (orWVal c) := Real.sqrt_pos.mpr hV
  have key : ∀ x : ι → Bool,
      (∑ p, c p * ∑ _k : Unit, orWDualVec c x p * orWDualVec c x p)
        ≤ orWVal c := by
    intro x
    by_cases hx : x = zeroVec
    · subst hx
      have hval : (∑ p, c p * ∑ _k : Unit,
          orWDualVec c (zeroVec : ι → Bool) p *
            orWDualVec c (zeroVec : ι → Bool) p)
          = (∑ p, c p * c p) / orWVal c := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun p _ => ?_
        have hδ : orWDelta c p * orWDelta c p = c p / orWVal c := by
          rw [orWDelta, div_mul_div_comm, Real.mul_self_sqrt (hc p).le,
            Real.mul_self_sqrt hV.le]
        rw [orWDualVec, if_pos rfl]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_unit,
          one_smul]
        rw [hδ]
        field_simp
      have hVne : orWVal c ≠ 0 := ne_of_gt hV
      rw [hval, ← orWVal_sq c, mul_div_assoc, div_self hVne, mul_one]
    · have hDpos : 0 < orWSupp c x := orWSupp_pos hc hx
      have hSpos : 0 < orWSqrtSupp c x := orWSqrtSupp_pos hc hx
      have hval : (∑ p, c p * ∑ _k : Unit, orWDualVec c x p * orWDualVec c x p)
          = (1 / orWSupp c x) * (1 / orWSupp c x) *
            ∑ p, (if x p then c p else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_unit,
          one_smul, orWDualVec, if_neg hx]
        by_cases hxp : x p
        · rw [if_pos hxp, if_pos hxp]
          ring
        · rw [if_neg hxp, if_neg hxp]
          ring
      rw [hval]
      -- `∑_{supp} c ≤ (∑_{supp} √c)²`
      have hsum : (∑ p, if x p then c p else 0)
          ≤ orWSqrtSupp c x * orWSqrtSupp c x := by
        have h := sum_sq_le_sq_sum (S := (Finset.univ : Finset ι))
          (a := fun p => if x p then Real.sqrt (c p) else 0)
          (fun p _ => by by_cases h : x p <;> simp [h, Real.sqrt_nonneg])
        rw [orWSqrtSupp]
        refine le_trans (le_of_eq ?_) h
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases h : x p
        · rw [if_pos h, if_pos h, Real.mul_self_sqrt (hc p).le]
        · rw [if_neg h, if_neg h, mul_zero]
      -- `D = S/√V`, so `(1/D)² = V/S²`
      have hDS : orWSupp c x * orWSupp c x
          = orWSqrtSupp c x * orWSqrtSupp c x / orWVal c := by
        rw [orWSupp_eq hc, div_mul_div_comm, Real.mul_self_sqrt hV.le]
      have hVne : orWVal c ≠ 0 := ne_of_gt hV
      rw [show (1 / orWSupp c x) * (1 / orWSupp c x) *
            (∑ p, if x p then c p else 0)
          = (∑ p, if x p then c p else 0) /
            (orWSupp c x * orWSupp c x) from by ring]
      rw [div_le_iff₀ (mul_pos hDpos hDpos), hDS,
        show orWVal c * (orWSqrtSupp c x * orWSqrtSupp c x / orWVal c)
          = orWSqrtSupp c x * orWSqrtSupp c x from by field_simp]
      exact hsum
  exact ⟨key, key⟩

/-! ## The weighted `OR`-composition upper bound -/

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- **The weighted `OR`-composition upper bound**, matching the primal bound
`sqrt_sum_sq_le_advPM_composeFunFam_orN`. -/
theorem advDual_composeFunFam_orN_le [Nonempty ι] {g : ι → (β → Bool) → Bool}
    {K₂ : Type*} [Fintype K₂] {Pg : ∀ i, DualPair K₂ (g i)} {c : ι → ℝ}
    (hc : ∀ i, 0 < c i) (hg : ∀ i, (Pg i).IsCostLe (c i)) :
    advDual (composeFunFam (orN : (ι → Bool) → Bool) g)
      ≤ Real.sqrt (∑ i, c i * c i) :=
  advDual_le_of_dualPair ((orWDual hc).compose Pg)
    (Real.sqrt_nonneg _)
    ((orWDual hc).compose_isWeightedCostLe (orWDual_isWeightedCostLe hc) hg)

end QuantumQueryComplexity
