import QuantumQueryComplexity.TreeSearch.Cost

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
# Optimal weights and the exact tree-search certificate

For positive cell costs `t` the weights

    λ_w = b · (t_w / C_w) · ∏_{a strict ancestor of w in the subtree} (R_a / C_a),
    R_a = √(∑_{u child of a} C_u²),   C_a = t_a + R_a                     (`optW`)

give every local root path of the subtree of `v` weight at most `b`, one leaf path weight
exactly `b`, and subtree energy `∑ t_w²/λ_w = C_v²/b` (`optW_spec`).  Each child subtree gets
the *same* residual budget `b R_v / C_v` — a root path visits only one child subtree.

Conversely, for arbitrary positive weights with local path sums at most `b`, the subtree
energy is at least `C_v²/b` (`energy_lower`): the scalar inequality
`t²/s + R²/(b−s) ≥ (t+R)²/b` at each internal vertex.  Hence

    C_ρ² ≤ P(λ)·E(λ),   P(λ) = max_v ∑_{w ∈ path v} λ_w,   E(λ) = ∑_w t_w²/λ_w,

with equality attained (`recCost_sq_le_pathMax_mul_energy`, `exists_weights_optimal`,
`optValue_eq`).  Setting the vector parameter `β_w = √(t_w / (C_ρ λ_w))` in the
first-difference dual gives **`HasWeightedDual (treeSearch mark) t C_ρ`** with coefficient
one (`hasWeightedDual_treeSearch_recCost`); the all-ones weights give the depth bound
`C_ρ ≤ √((d+1) ∑ t²)` (`recCost_le_sqrt_depth_sqSum`).  The optimization is over the weights
of this construction; it is not a lower bound on query complexity.
-/

namespace QuantumQueryComplexity

namespace AncTree

open Finset

variable {V : Type} [DecidableEq V] [Fintype V] (T : AncTree V)

/-! ## The optimal weights -/

/-- The weights of the subtree of `v` with path budget `b`. -/
noncomputable def optW (t : V → ℝ) (b : ℝ) (v w : V) : ℝ :=
  b * (t w / T.recCost t w) * ∏ a ∈ (T.localPath v w).erase w, T.resid t a / T.recCost t a

lemma optW_self (t : V → ℝ) (b : ℝ) (v : V) : T.optW t b v v = b * (t v / T.recCost t v) := by
  rw [optW, localPath_self, Finset.erase_singleton, Finset.prod_empty, mul_one]

lemma ne_of_mem_descendants_child {v u w : V} (hu : u ∈ T.children v) (hw : w ∈ T.descendants u) :
    w ≠ v := by
  rintro rfl
  exact T.notMem_descendants_child hu hw

lemma optW_child (t : V → ℝ) (b : ℝ) {v u w : V} (hu : u ∈ T.children v)
    (hw : w ∈ T.descendants u) :
    T.optW t b v w = T.resid t v / T.recCost t v * T.optW t b u w := by
  obtain ⟨h1, h2⟩ := T.localPath_succ hu hw
  have hwv := T.ne_of_mem_descendants_child hu hw
  rw [optW, optW, h1, Finset.erase_insert_of_ne hwv.symm, Finset.prod_insert]
  · ring
  · intro h; exact h2 (Finset.mem_of_mem_erase h)

lemma optW_child_budget (t : V → ℝ) (b : ℝ) {v u w : V} (hu : u ∈ T.children v)
    (hw : w ∈ T.descendants u) :
    T.optW t b v w = T.optW t (b * T.resid t v / T.recCost t v) u w := by
  rw [T.optW_child t b hu hw, optW, optW]; ring

lemma mem_descendants_of_mem_localPath {u w a : V} (hw : w ∈ T.descendants u)
    (ha : a ∈ T.localPath u w) : a ∈ T.descendants u := by
  rw [localPath, mem_filter, mem_path_iff] at ha
  obtain ⟨⟨hd, hanc⟩, hdu⟩ := ha
  rw [mem_descendants, mem_path_iff] at hw ⊢
  refine ⟨hdu, ?_⟩
  rw [← hanc, T.ancAt_ancAt w _ _ hdu hd, hw.2]

variable {t : V → ℝ} (ht : ∀ v, 0 < t v)
include ht

/-- **The optimal weights of a subtree**: positive, every local path at most `b`, one path
exactly `b`, energy `C_v²/b`. -/
theorem optW_spec (v : V) : ∀ b : ℝ, 0 < b →
    (∀ w ∈ T.descendants v, 0 < T.optW t b v w)
    ∧ (∀ w ∈ T.descendants v, ∑ a ∈ T.localPath v w, T.optW t b v a ≤ b)
    ∧ (∃ w ∈ T.descendants v, ∑ a ∈ T.localPath v w, T.optW t b v a = b)
    ∧ ∑ w ∈ T.descendants v, t w ^ 2 / T.optW t b v w = T.recCost t v ^ 2 / b := by
  induction v using T.induction_children with
  | step v ih =>
    intro b hb
    have hC := T.recCost_pos ht v
    have hself : T.optW t b v v = b * (t v / T.recCost t v) := T.optW_self t b v
    have hself_pos : 0 < T.optW t b v v := by rw [hself]; exact mul_pos hb (div_pos (ht v) hC)
    have hself_le : T.optW t b v v ≤ b := by
      rw [hself]
      have : t v / T.recCost t v ≤ 1 := (div_le_one hC).2 (T.le_recCost v)
      nlinarith
    by_cases hch : T.children v = ∅
    · -- a leaf
      have hleaf : T.recCost t v = t v := T.recCost_leaf hch
      have hdesc : T.descendants v = {v} := by rw [descendants_eq, hch, biUnion_empty]; rfl
      refine ⟨?_, ?_, ⟨v, T.self_mem_descendants v, ?_⟩, ?_⟩
      · intro w hw; rw [hdesc, mem_singleton] at hw; subst hw; exact hself_pos
      · intro w hw; rw [hdesc, mem_singleton] at hw; subst hw
        rw [localPath_self, sum_singleton]; exact hself_le
      · rw [localPath_self, sum_singleton, hself, hleaf, div_self (ht v).ne', mul_one]
      · rw [hdesc, sum_singleton, hself, hleaf]
        have := (ht v).ne'
        field_simp
    · -- an internal vertex
      have hne : (T.children v).Nonempty := Finset.nonempty_iff_ne_empty.2 hch
      have hR := T.resid_pos ht hne
      set b' := b * T.resid t v / T.recCost t v with hb'
      have hb'0 : 0 < b' := by positivity
      have hCe : T.recCost t v = t v + T.resid t v := T.recCost_eq_resid t v
      have e : b * (t v / T.recCost t v) + b * T.resid t v / T.recCost t v = b := by
        rw [mul_div_assoc', ← add_div, ← mul_add, ← hCe, mul_div_assoc, div_self hC.ne', mul_one]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro w hw
        by_cases hwv : w = v
        · subst hwv; exact hself_pos
        · obtain ⟨u, hu, hwu⟩ := T.exists_child_of_mem_descendants hw hwv
          rw [T.optW_child_budget t b hu hwu]
          exact (ih u hu b' hb'0).1 w hwu
      · intro w hw
        by_cases hwv : w = v
        · subst hwv; rw [localPath_self, sum_singleton]; exact hself_le
        · obtain ⟨u, hu, hwu⟩ := T.exists_child_of_mem_descendants hw hwv
          rw [T.sum_localPath_succ hu hwu, hself]
          have hsum : ∑ a ∈ T.localPath u w, T.optW t b v a
              = ∑ a ∈ T.localPath u w, T.optW t b' u a :=
            Finset.sum_congr rfl fun a ha =>
              T.optW_child_budget t b hu (T.mem_descendants_of_mem_localPath hwu ha)
          rw [hsum]
          have := (ih u hu b' hb'0).2.1 w hwu
          linarith
      · obtain ⟨u, hu⟩ := hne
        obtain ⟨w, hw, hwsum⟩ := (ih u hu b' hb'0).2.2.1
        refine ⟨w, T.descendants_child_subset hu hw, ?_⟩
        rw [T.sum_localPath_succ hu hw, hself]
        have hsum : ∑ a ∈ T.localPath u w, T.optW t b v a
            = ∑ a ∈ T.localPath u w, T.optW t b' u a :=
          Finset.sum_congr rfl fun a ha =>
            T.optW_child_budget t b hu (T.mem_descendants_of_mem_localPath hw ha)
        rw [hsum, hwsum]
        exact e
      · rw [T.sum_descendants v, hself]
        have hin : ∀ u ∈ T.children v, ∑ w ∈ T.descendants u, t w ^ 2 / T.optW t b v w
            = T.recCost t u ^ 2 / b' := fun u hu => by
          rw [← (ih u hu b' hb'0).2.2.2]
          exact Finset.sum_congr rfl fun w hw => by rw [T.optW_child_budget t b hu hw]
        rw [Finset.sum_congr rfl hin, ← Finset.sum_div, ← T.resid_sq t v, hb', hCe]
        have htv := (ht v).ne'
        field_simp
        try ring

/-! ## Optimality within the construction -/

omit ht in
/-- The scalar step: `t²/s + R²/(b−s) ≥ (t+R)²/b`. -/
lemma sq_div_add_sq_div_ge (tv R s b : ℝ) (hs : 0 < s) (hsb : s < b) :
    (tv + R) ^ 2 / b ≤ tv ^ 2 / s + R ^ 2 / (b - s) := by
  have hb : 0 < b := by linarith
  have hbs : 0 < b - s := by linarith
  rw [div_add_div _ _ hs.ne' hbs.ne', div_le_div_iff₀ hb (mul_pos hs hbs)]
  nlinarith [sq_nonneg ((b - s) * tv - s * R), hb, hs, hbs]

/-- **The subtree energy of arbitrary positive weights** with local path sums at most `b` is
at least `C_v²/b`. -/
theorem energy_lower (v : V) : ∀ (lam : V → ℝ) (b : ℝ), 0 < b →
    (∀ w ∈ T.descendants v, 0 < lam w) →
    (∀ w ∈ T.descendants v, ∑ a ∈ T.localPath v w, lam a ≤ b) →
    T.recCost t v ^ 2 / b ≤ ∑ w ∈ T.descendants v, t w ^ 2 / lam w := by
  induction v using T.induction_children with
  | step v ih =>
    intro lam b hb hpos hpath
    have hs : 0 < lam v := hpos v (T.self_mem_descendants v)
    have hsb : lam v ≤ b := by
      have := hpath v (T.self_mem_descendants v)
      rwa [localPath_self, sum_singleton] at this
    by_cases hch : T.children v = ∅
    · have hleaf : T.recCost t v = t v := T.recCost_leaf hch
      have hdesc : T.descendants v = {v} := by rw [descendants_eq, hch, biUnion_empty]; rfl
      rw [hdesc, sum_singleton, hleaf]
      exact div_le_div_of_nonneg_left (sq_nonneg _) hs hsb
    · have hne : (T.children v).Nonempty := Finset.nonempty_iff_ne_empty.2 hch
      have hCe : T.recCost t v = t v + T.resid t v := T.recCost_eq_resid t v
      -- the residual budget is positive
      obtain ⟨u₀, hu₀⟩ := hne
      have hlt : lam v < b := by
        have h1 := hpath u₀ (T.descendants_child_subset hu₀ (T.self_mem_descendants u₀))
        rw [T.sum_localPath_succ hu₀ (T.self_mem_descendants u₀), localPath_self,
          sum_singleton] at h1
        have := hpos u₀ (T.descendants_child_subset hu₀ (T.self_mem_descendants u₀))
        linarith
      have hchild : ∀ u ∈ T.children v,
          T.recCost t u ^ 2 / (b - lam v) ≤ ∑ w ∈ T.descendants u, t w ^ 2 / lam w := by
        intro u hu
        refine ih u hu lam (b - lam v) (by linarith)
          (fun w hw => hpos w (T.descendants_child_subset hu hw)) fun w hw => ?_
        have := hpath w (T.descendants_child_subset hu hw)
        rw [T.sum_localPath_succ hu hw] at this
        linarith
      rw [T.sum_descendants v]
      have hsum := Finset.sum_le_sum hchild
      rw [← Finset.sum_div, ← T.resid_sq t v] at hsum
      rw [hCe]
      have := sq_div_add_sq_div_ge (t v) (T.resid t v) (lam v) b hs hlt
      linarith

/-! ## The root statements -/

/-- The maximal root-path weight (the root `ρ` witnesses nonemptiness). -/
noncomputable def pathMax (ρ : V) (lam : V → ℝ) : ℝ :=
  univ.sup' ⟨ρ, mem_univ ρ⟩ fun v => ∑ w ∈ T.path v, lam w

omit ht in
lemma sum_path_le_pathMax (ρ : V) (lam : V → ℝ) (v : V) :
    ∑ w ∈ T.path v, lam w ≤ T.pathMax ρ lam :=
  Finset.le_sup' (fun v => ∑ w ∈ T.path v, lam w) (mem_univ v)

omit ht in
lemma pathMax_le (ρ : V) (lam : V → ℝ) {b : ℝ} (h : ∀ v, ∑ w ∈ T.path v, lam w ≤ b) :
    T.pathMax ρ lam ≤ b :=
  Finset.sup'_le _ _ fun v _ => h v

/-- The energy. -/
noncomputable def energy (t lam : V → ℝ) : ℝ := ∑ w, t w ^ 2 / lam w

/-- The normalized optimal weights. -/
noncomputable def optWeights (t : V → ℝ) (ρ : V) : V → ℝ := T.optW t 1 ρ

/-- The optimal value of `P(λ)·E(λ)` over positive weights. -/
noncomputable def optValue (ρ : V) (t : V → ℝ) : ℝ :=
  sInf ((fun lam => T.pathMax ρ lam * energy t lam) '' {lam | ∀ w, 0 < lam w})

variable {ρ : V} (hρ : T.IsRoot ρ)
include hρ

/-- **`C_ρ² ≤ b · E(λ)`** whenever every root path has weight at most `b`. -/
theorem recCost_sq_le_mul_energy (lam : V → ℝ) (hpos : ∀ w, 0 < lam w) {b : ℝ} (hb : 0 < b)
    (hpath : ∀ v, ∑ w ∈ T.path v, lam w ≤ b) :
    T.recCost t ρ ^ 2 ≤ b * energy t lam := by
  have h := T.energy_lower ht ρ lam b hb (fun w _ => hpos w) fun w _ => by
    rw [T.localPath_eq_path hρ]; exact hpath w
  rw [T.descendants_eq_univ hρ] at h
  rw [div_le_iff₀ hb] at h
  rw [energy, mul_comm]; exact h

/-- **`C_ρ² ≤ P(λ)·E(λ)`** for every positive weight assignment. -/
theorem recCost_sq_le_pathMax_mul_energy (lam : V → ℝ) (hpos : ∀ w, 0 < lam w) :
    T.recCost t ρ ^ 2 ≤ T.pathMax ρ lam * energy t lam :=
  T.recCost_sq_le_mul_energy ht hρ lam hpos
    (lt_of_lt_of_le (Finset.sum_pos (fun w _ => hpos w) ⟨ρ, T.self_mem_path ρ⟩)
      (T.sum_path_le_pathMax ρ lam ρ))
    (T.sum_path_le_pathMax ρ lam)

/-- **Attainment**: positive weights with `P(λ) = 1` and `E(λ) = C_ρ²`. -/
theorem optWeights_spec :
    (∀ w, 0 < T.optWeights t ρ w) ∧ T.pathMax ρ (T.optWeights t ρ) = 1
      ∧ energy t (T.optWeights t ρ) = T.recCost t ρ ^ 2 := by
  obtain ⟨h1, h2, ⟨w₀, _, h3⟩, h4⟩ := T.optW_spec ht ρ 1 one_pos
  rw [T.descendants_eq_univ hρ] at h1 h2 h4
  simp only [optWeights]
  refine ⟨fun w => h1 w (mem_univ w), le_antisymm ?_ ?_, ?_⟩
  · exact T.pathMax_le ρ _ fun v => by
      rw [← T.localPath_eq_path hρ]; exact h2 v (mem_univ v)
  · refine h3.symm.le.trans ?_
    rw [T.localPath_eq_path hρ]
    exact T.sum_path_le_pathMax ρ _ w₀
  · rw [energy, h4, div_one]

theorem exists_weights_optimal :
    ∃ lam : V → ℝ, (∀ w, 0 < lam w) ∧ T.pathMax ρ lam * energy t lam = T.recCost t ρ ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := T.optWeights_spec ht hρ
  exact ⟨_, h1, by rw [h2, h3, one_mul]⟩

/-- **The infimum identity** `inf_λ P(λ)E(λ) = C_ρ²`, attained. -/
theorem optValue_eq : T.optValue ρ t = T.recCost t ρ ^ 2 := by
  obtain ⟨lam, hpos, hval⟩ := T.exists_weights_optimal ht hρ
  set S : Set ℝ := (fun lam => T.pathMax ρ lam * energy t lam) '' {lam | ∀ w, 0 < lam w} with hS
  have hbdd : BddBelow S := ⟨T.recCost t ρ ^ 2, by
    rintro _ ⟨lam', hpos', rfl⟩
    exact T.recCost_sq_le_pathMax_mul_energy ht hρ lam' hpos'⟩
  have hmem : T.pathMax ρ lam * energy t lam ∈ S := ⟨lam, hpos, rfl⟩
  refine le_antisymm ((csInf_le hbdd hmem).trans hval.le) ?_
  refine le_csInf ⟨_, hmem⟩ ?_
  rintro _ ⟨lam', hpos', rfl⟩
  exact T.recCost_sq_le_pathMax_mul_energy ht hρ lam' hpos'

/-! ## The exact weighted certificate -/

variable {E : Type} [Fintype E] [DecidableEq E] (mark : V → (V → E) → Prop)
variable (hloc : ∀ v (x y : V → E),
  (∀ i ≤ T.depth v, x (T.ancAt v i) = y (T.ancAt v i)) → (mark v x ↔ mark v y))
include hloc

/-- **The optimized weighted tree-search dual**: cost exactly `C_ρ`, coefficient one. -/
theorem hasWeightedDual_treeSearch_recCost :
    HasWeightedDual (treeSearch mark) t (T.recCost t ρ) := by
  obtain ⟨hpos, hP, hE⟩ := T.optWeights_spec ht hρ
  have hC := T.recCost_pos ht ρ
  set lam := T.optWeights t ρ with hlam
  set β : V → ℝ := fun w => Real.sqrt (t w / (T.recCost t ρ * lam w)) with hβdef
  have hβ2 : ∀ w, β w ^ 2 = t w / (T.recCost t ρ * lam w) := fun w =>
    Real.sq_sqrt (by have := ht w; have := hpos w; positivity)
  have hβ : ∀ w, β w ≠ 0 := fun w => by
    have := ht w; have := hpos w
    exact Real.sqrt_ne_zero'.2 (by positivity)
  have hpath : ∀ v, ∑ w ∈ T.path v, t w / (β w) ^ 2 ≤ T.recCost t ρ := by
    intro v
    have hterm : ∀ w ∈ T.path v, t w / (β w) ^ 2 = T.recCost t ρ * lam w := fun w _ => by
      rw [hβ2]; have := (ht w).ne'; have := (hpos w).ne'; field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have := T.sum_path_le_pathMax ρ lam v
    rw [hP] at this
    nlinarith
  have hall : ∑ w, t w * (β w) ^ 2 ≤ T.recCost t ρ := by
    have hterm : ∀ w ∈ (univ : Finset V), t w * (β w) ^ 2 = (t w ^ 2 / lam w) / T.recCost t ρ :=
      fun w _ => by rw [hβ2]; have := (hpos w).ne'; field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← energy, hE]
    rw [div_le_iff₀ hC]
    nlinarith
  exact T.hasWeightedDual_treeSearch T.maxDepth mark hβ T.depth_le_maxDepth hloc t _ hpath hall

omit hloc in
/-- **The depth bound** `C_ρ ≤ √((d+1)·∑ t²)`, from the all-ones weights. -/
theorem recCost_le_sqrt_depth_sqSum {d : ℕ} (hd : ∀ v, T.depth v ≤ d) :
    T.recCost t ρ ≤ Real.sqrt (((d : ℝ) + 1) * ∑ w, t w ^ 2) := by
  have h := T.recCost_sq_le_mul_energy ht hρ (fun _ => 1) (fun _ => one_pos) (b := (d : ℝ) + 1)
    (by positivity) fun v => by
      rw [Finset.sum_const, T.card_path, nsmul_eq_mul, mul_one]
      exact_mod_cast Nat.succ_le_succ (hd v)
  rw [energy] at h
  simp only [div_one] at h
  exact Real.le_sqrt_of_sq_le h

end AncTree

end QuantumQueryComplexity
