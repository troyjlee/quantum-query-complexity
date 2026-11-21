import QuantumQueryComplexity.Quantum.JointState.Basic

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Conditioning, labelled mixtures, and uniform distributions

Constructions on finite distributions used to build input distributions:

* `FinDist.condOn ρ s hs` — `ρ` conditioned on an event `s` of positive probability;
* `FinDist.mixture π ρ` — draw a label `l ∼ π`, then `ω ∼ ρ l`, keeping the label.  With an
  observation map that ignores the label, the label is hidden from the algorithm (the hidden
  computational problems of Belovs, and the planted triangle of Cornelissen–Gilani–Zhou);
* `FinDist.uniform` — the uniform distribution on a nonempty finite type.

## Main results

* `FinDist.mass_pos_condOn_iff`, `FinDist.probOf_condOn` — support and event probabilities of a
  conditioned distribution.
* `FinDist.mass_pos_mixture_iff` — the support of a mixture.
-/

namespace QuantumQueryComplexity

namespace FinDist

variable {Ω L : Type} [Fintype Ω] [DecidableEq Ω] [Fintype L] [DecidableEq L]

/-! ## Events and conditioning -/

/-- The probability of an event given as a predicate. -/
noncomputable def probOf (ρ : FinDist Ω) (s : Ω → Prop) [DecidablePred s] : ℝ :=
  ∑ ω, if s ω then ρ.mass ω else 0

lemma probOf_nonneg (ρ : FinDist Ω) (s : Ω → Prop) [DecidablePred s] : 0 ≤ ρ.probOf s := by
  refine Finset.sum_nonneg fun ω _ => ?_
  split_ifs
  · exact ρ.mass_nonneg ω
  · exact le_rfl

lemma probOf_le_one (ρ : FinDist Ω) (s : Ω → Prop) [DecidablePred s] : ρ.probOf s ≤ 1 := by
  rw [← ρ.sum_mass]
  refine Finset.sum_le_sum fun ω _ => ?_
  split_ifs
  · exact le_rfl
  · exact ρ.mass_nonneg ω

/-- The probability of a set of support points (`FinDist.prob`) is the probability of the
corresponding event. -/
theorem prob_filter_eq_probOf (ρ : FinDist Ω) (s : Ω → Prop) [DecidablePred s] :
    ρ.prob (Finset.univ.filter fun x : ρ.Supp => s x.1) = ρ.probOf s := by
  classical
  rw [prob, Finset.sum_filter, probOf]
  rw [← Finset.sum_subtype (Finset.univ.filter fun ω => 0 < ρ.mass ω)
    (p := fun ω => 0 < ρ.mass ω) (fun ω => by simp)
    (fun ω => if s ω then ρ.mass ω else 0)]
  refine Finset.sum_filter_of_ne fun ω _ hω => ?_
  have hne : ρ.mass ω ≠ 0 := by
    intro h0
    apply hω
    simp [h0]
  exact lt_of_le_of_ne (ρ.mass_nonneg ω) (Ne.symm hne)

/-- The conditioned mass `ρ(ω | s)`. -/
noncomputable def condMass (ρ : FinDist Ω) (s : Ω → Prop) [DecidablePred s] (ω : Ω) : ℝ :=
  if s ω then ρ.mass ω / ρ.probOf s else 0

lemma condMass_nonneg (ρ : FinDist Ω) (s : Ω → Prop) [DecidablePred s] (ω : Ω) :
    0 ≤ ρ.condMass s ω := by
  unfold condMass
  split_ifs
  · exact div_nonneg (ρ.mass_nonneg ω) (ρ.probOf_nonneg s)
  · exact le_rfl

lemma sum_condMass (ρ : FinDist Ω) (s : Ω → Prop) [DecidablePred s] (hs : 0 < ρ.probOf s) :
    ∑ ω, ρ.condMass s ω = 1 := by
  have h : ∀ ω, ρ.condMass s ω = (if s ω then ρ.mass ω else 0) / ρ.probOf s := by
    intro ω
    unfold condMass
    split_ifs <;> simp
  simp_rw [h]
  rw [← Finset.sum_div]
  exact div_self hs.ne'

/-- **Conditioning** `ρ( · | s)` on an event of positive probability. -/
noncomputable def condOn (ρ : FinDist Ω) (s : Ω → Prop) [DecidablePred s]
    (hs : 0 < ρ.probOf s) : FinDist Ω :=
  ⟨ρ.condMass s, ρ.condMass_nonneg s, ρ.sum_condMass s hs⟩

@[simp] lemma condOn_mass (ρ : FinDist Ω) (s : Ω → Prop) [DecidablePred s]
    (hs : 0 < ρ.probOf s) (ω : Ω) :
    (ρ.condOn s hs).mass ω = if s ω then ρ.mass ω / ρ.probOf s else 0 := rfl

/-- The support of `ρ( · | s)` is the part of the support of `ρ` inside `s`. -/
theorem mass_pos_condOn_iff (ρ : FinDist Ω) (s : Ω → Prop) [DecidablePred s]
    (hs : 0 < ρ.probOf s) (ω : Ω) :
    0 < (ρ.condOn s hs).mass ω ↔ s ω ∧ 0 < ρ.mass ω := by
  rw [condOn_mass]
  by_cases h : s ω
  · simp [h, div_pos_iff_of_pos_right hs]
  · simp [h]

/-- `ρ(t | s) = ρ(s ∧ t) / ρ(s)`. -/
theorem probOf_condOn (ρ : FinDist Ω) (s : Ω → Prop) [DecidablePred s]
    (hs : 0 < ρ.probOf s) (t : Ω → Prop) [DecidablePred t] :
    (ρ.condOn s hs).probOf t = ρ.probOf (fun ω => s ω ∧ t ω) / ρ.probOf s := by
  change (∑ ω, if t ω then (ρ.condOn s hs).mass ω else 0) =
    (∑ ω, if s ω ∧ t ω then ρ.mass ω else 0) / ρ.probOf s
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [condOn_mass]
  by_cases hs' : s ω <;> by_cases ht : t ω <;> simp [hs', ht]

/-! ## Labelled mixtures -/

/-- The mass of a labelled mixture. -/
noncomputable def mixMass (π : FinDist L) (ρ : L → FinDist Ω) (lω : L × Ω) : ℝ :=
  π.mass lω.1 * (ρ lω.1).mass lω.2

lemma mixMass_nonneg (π : FinDist L) (ρ : L → FinDist Ω) (lω : L × Ω) :
    0 ≤ mixMass π ρ lω := by
  exact mul_nonneg (π.mass_nonneg _) ((ρ _).mass_nonneg _)

lemma sum_mixMass (π : FinDist L) (ρ : L → FinDist Ω) : ∑ lω, mixMass π ρ lω = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [mixMass, ← Finset.mul_sum, sum_mass, mul_one]

/-- **The labelled mixture**: draw `l ∼ π`, then `ω ∼ ρ l`, and keep the pair. -/
noncomputable def mixture (π : FinDist L) (ρ : L → FinDist Ω) : FinDist (L × Ω) :=
  ⟨mixMass π ρ, mixMass_nonneg π ρ, sum_mixMass π ρ⟩

@[simp] lemma mixture_mass (π : FinDist L) (ρ : L → FinDist Ω) (l : L) (ω : Ω) :
    (mixture π ρ).mass (l, ω) = π.mass l * (ρ l).mass ω := rfl

/-- The support of a mixture: a positive-probability label with a point of its support. -/
theorem mass_pos_mixture_iff (π : FinDist L) (ρ : L → FinDist Ω) (l : L) (ω : Ω) :
    0 < (mixture π ρ).mass (l, ω) ↔ 0 < π.mass l ∧ 0 < (ρ l).mass ω := by
  rw [mixture_mass]
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => mul_pos h.1 h.2⟩
  · exact lt_of_le_of_ne (π.mass_nonneg l) fun h0 => by rw [← h0, zero_mul] at h; exact h.false
  · exact lt_of_le_of_ne ((ρ l).mass_nonneg ω) fun h0 => by
      rw [← h0, mul_zero] at h; exact h.false

end FinDist

/-! ## The uniform distribution -/

namespace FinDist

lemma sum_uniformMass (L : Type) [Fintype L] [Nonempty L] :
    ∑ _l : L, (1 / (Fintype.card L : ℝ)) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card L : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  field_simp

/-- **The uniform distribution** on a nonempty finite type. -/
noncomputable def uniform (L : Type) [Fintype L] [Nonempty L] : FinDist L :=
  ⟨fun _ => 1 / (Fintype.card L : ℝ), fun _ => by positivity, sum_uniformMass L⟩

@[simp] lemma uniform_mass {L : Type} [Fintype L] [Nonempty L] (l : L) :
    (uniform L).mass l = 1 / (Fintype.card L : ℝ) := rfl

end FinDist

/-! ## Elementary event probabilities -/

section Events

variable {Ω J : Type} [Fintype Ω] [DecidableEq Ω]

/-- Events that hold at the same points have the same probability. -/
theorem FinDist.probOf_congr (ρ : FinDist Ω) {s t : Ω → Prop} [DecidablePred s] [DecidablePred t]
    (h : ∀ ω, s ω ↔ t ω) : ρ.probOf s = ρ.probOf t := by
  unfold FinDist.probOf
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hs : s ω
  · rw [ite_eq_left hs, ite_eq_left ((h ω).mp hs)]
  · rw [ite_eq_right hs, ite_eq_right (mt (h ω).mpr hs)]

/-- An event that holds at a point of positive mass has positive probability. -/
theorem FinDist.probOf_pos_of_mem (ρ : FinDist Ω) {s : Ω → Prop} [DecidablePred s] {ω : Ω}
    (hs : s ω) (hω : 0 < ρ.mass ω) : 0 < ρ.probOf s := by
  refine Finset.sum_pos' (fun ω' _ => ?_) ⟨ω, Finset.mem_univ _, by rwa [ite_eq_left hs]⟩
  split_ifs
  exacts [ρ.mass_nonneg ω', le_rfl]

/-- The probability of the complementary event: `ρ(¬s) = 1 − ρ(s)`. -/
theorem FinDist.probOf_not (ρ : FinDist Ω) (s : Ω → Prop) [DecidablePred s] :
    ρ.probOf (fun ω => ¬ s ω) = 1 - ρ.probOf s := by
  rw [eq_sub_iff_add_eq, ← ρ.sum_mass]
  unfold FinDist.probOf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hs : s ω <;> simp [hs]

/-- Monotonicity of probabilities, on the support. -/
theorem FinDist.probOf_le_of_imp (ρ : FinDist Ω) {s t : Ω → Prop} [DecidablePred s]
    [DecidablePred t] (h : ∀ ω, 0 < ρ.mass ω → s ω → t ω) : ρ.probOf s ≤ ρ.probOf t := by
  unfold FinDist.probOf
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hs : s ω
  · rcases (ρ.mass_nonneg ω).eq_or_lt with h0 | h0
    · rw [ite_eq_left hs, ← h0]
      split_ifs <;> exact le_rfl
    · rw [ite_eq_left hs, ite_eq_left (h ω h0 hs)]
  · rw [ite_eq_right hs]
    split_ifs
    exacts [ρ.mass_nonneg ω, le_rfl]

/-- The union bound. -/
theorem FinDist.probOf_le_sum (ρ : FinDist Ω) (N : Finset J) (E : J → Ω → Prop)
    [∀ j, DecidablePred (E j)] {s : Ω → Prop} [DecidablePred s]
    (hs : ∀ ω, s ω → ∃ j ∈ N, E j ω) : ρ.probOf s ≤ ∑ j ∈ N, ρ.probOf (E j) := by
  unfold FinDist.probOf
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun ω _ => ?_
  have hnn : ∀ j ∈ N, 0 ≤ if E j ω then ρ.mass ω else 0 := fun j _ => by
    split_ifs
    exacts [ρ.mass_nonneg ω, le_rfl]
  split_ifs with h
  · obtain ⟨j, hj, hE⟩ := hs ω h
    calc ρ.mass ω = if E j ω then ρ.mass ω else 0 := (ite_eq_left hE).symm
      _ ≤ _ := Finset.single_le_sum hnn hj
  · exact Finset.sum_nonneg hnn

end Events

end QuantumQueryComplexity
