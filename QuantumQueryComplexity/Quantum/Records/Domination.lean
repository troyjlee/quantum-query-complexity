import QuantumQueryComplexity.Quantum.Records.CondBern
import QuantumQueryComplexity.Quantum.JointState.Conditioning
import Mathlib.Combinatorics.SetFamily.FourFunctions

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Domination of increasing events under downward conditioning

Let `ν = Bernoulli(p)^{⊗ι}` and let `Ω ⊆ {0,1}^ι` be downward closed with `ν(Ω) > 0`.  Every
increasing event `U` satisfies

  `ν(U | Ω) ≤ ν(U)`   (`FinDist.probOf_condOn_bern_le`).

This is the consequence of Lemma 5.2 of Cornelissen–Gilani–Zhou [CGZ] that the rest of their
proof uses.

**Difference from the paper's proof.**  CGZ construct a monotone coupling `X ≤ Y` with `X ∼ ν(·|Ω)`
and `Y ∼ ν`, from the bound `Pr[Zᵢ = 1 | Z_J] ≤ p` (5.4).  This file does not construct the
coupling.  It uses Mathlib's FKG inequality (`fkg`) instead.  The product weight `bernMass p` is
log-modular on the distributive lattice `ι → Bool`, so the increasing indicators of `U` and of
the complement of `Ω` are positively correlated (Harris's inequality, `FinDist.bern_harris`).
That is, `ν(U ∩ Ω) ≤ ν(U) ν(Ω)`.  Only this consequence is formalized; the coupling itself is
not.

The order on `ι → Bool` is the pointwise order with `false < true`.  An event is increasing when
its set is an `IsUpperSet`, and downward closed when it is an `IsLowerSet`.

## Main definitions

* `FinDist.bern p` — the product Bernoulli(p) distribution on `ι → Bool`.
* `CondBern.prior` — the unconditioned product distribution of a conditioned Bernoulli
  distribution.

## Main results

* `FinDist.bern_harris` — Harris's inequality for increasing events.
* `FinDist.probOf_and_le_of_isUpperSet_of_isLowerSet` — an increasing and a decreasing event
  are negatively correlated.
* `FinDist.probOf_condOn_bern_le` — **domination**.
* `CondBern.dist_eq_condOn`, `CondBern.probOf_le_prior` — the same for `CondBern.dist`.
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The product Bernoulli distribution -/

lemma bernMass_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ι → Bool) :
    0 ≤ bernMass p x :=
  Finset.prod_nonneg fun i _ => by split_ifs <;> linarith

/-- The product Bernoulli masses sum to one, for every real `p`. -/
lemma sum_bernMass (p : ℝ) : ∑ x : ι → Bool, bernMass p x = 1 := by
  unfold bernMass
  rw [← Fintype.prod_sum (fun (_ : ι) (b : Bool) => if b then p else 1 - p)]
  simp

/-- The product weight is log-modular on the lattice `ι → Bool`. -/
private lemma bernMass_mul_inf_sup (p : ℝ) (a b : ι → Bool) :
    bernMass p a * bernMass p b = bernMass p (a ⊓ b) * bernMass p (a ⊔ b) := by
  unfold bernMass
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Pi.inf_apply, Pi.sup_apply]
  rcases Bool.eq_false_or_eq_true (a i) with ha | ha <;>
    rcases Bool.eq_false_or_eq_true (b i) with hb | hb <;> simp [ha, hb, mul_comm]

private lemma monotone_indicator (u : (ι → Bool) → Prop) [DecidablePred u]
    (hu : IsUpperSet {x | u x}) : Monotone fun x => if u x then (1 : ℝ) else 0 := by
  intro a b hab
  by_cases ha : u a
  · have hb : u b := hu hab ha
    simp [ha, hb]
  · simp only [ha, ↓reduceIte]
    split_ifs <;> norm_num

namespace FinDist

/-- **The product Bernoulli(p) distribution** `ν = Bernoulli(p)^{⊗ι}`. -/
noncomputable def bern (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FinDist (ι → Bool) :=
  ⟨bernMass p, bernMass_nonneg hp0 hp1, sum_bernMass p⟩

@[simp] lemma bern_mass {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ι → Bool) :
    (bern p hp0 hp1).mass x = bernMass p x := rfl

variable {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)

/-- **Harris's inequality**: increasing events are positively correlated under `ν`. -/
theorem bern_harris (u w : (ι → Bool) → Prop) [DecidablePred u] [DecidablePred w]
    (hu : IsUpperSet {x | u x}) (hw : IsUpperSet {x | w x}) :
    (bern p hp0 hp1).probOf u * (bern p hp0 hp1).probOf w
      ≤ (bern p hp0 hp1).probOf (fun x => u x ∧ w x) := by
  have h := fkg (μ := bernMass p) (f := fun x => if u x then (1 : ℝ) else 0)
    (g := fun x => if w x then (1 : ℝ) else 0) (fun x => bernMass_nonneg hp0 hp1 x)
    (fun x => by dsimp; split_ifs <;> norm_num) (fun x => by dsimp; split_ifs <;> norm_num)
    (monotone_indicator u hu) (monotone_indicator w hw)
    (fun a b => (bernMass_mul_inf_sup p a b).le)
  rw [sum_bernMass, one_mul] at h
  simp only [ite_zero_mul_ite_zero, mul_one] at h
  simp only [mul_ite, mul_one, mul_zero] at h
  simpa only [probOf, bern_mass] using h

/-- An increasing event and a downward-closed event are negatively correlated:
`ν(U ∩ Ω) ≤ ν(U) ν(Ω)`. -/
theorem probOf_and_le_of_isUpperSet_of_isLowerSet (u s : (ι → Bool) → Prop) [DecidablePred u]
    [DecidablePred s] (hu : IsUpperSet {x | u x}) (hs : IsLowerSet {x | s x}) :
    (bern p hp0 hp1).probOf (fun x => s x ∧ u x)
      ≤ (bern p hp0 hp1).probOf u * (bern p hp0 hp1).probOf s := by
  set ν : FinDist (ι → Bool) := bern p hp0 hp1
  have hw : IsUpperSet {x | ¬ s x} := hs.compl
  have h := bern_harris hp0 hp1 u (fun x => ¬ s x) hu hw
  have hsplit : ν.probOf u = ν.probOf (fun x => s x ∧ u x) + ν.probOf (fun x => u x ∧ ¬ s x) := by
    unfold probOf
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hsx : s x <;> by_cases hux : u x <;> simp [hsx, hux]
  have hcompl : ν.probOf (fun x => ¬ s x) = 1 - ν.probOf s := by
    rw [← ν.sum_mass]
    unfold probOf
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hsx : s x <;> simp [hsx]
  rw [hcompl] at h
  nlinarith

/-- **Domination** (the consequence of CGZ Lemma 5.2): conditioning `ν` on a downward-closed
event of positive probability does not increase the probability of any increasing event. -/
theorem probOf_condOn_bern_le (s : (ι → Bool) → Prop) [DecidablePred s]
    (hs : IsLowerSet {x | s x}) (hpos : 0 < (bern p hp0 hp1).probOf s)
    (u : (ι → Bool) → Prop) [DecidablePred u] (hu : IsUpperSet {x | u x}) :
    ((bern p hp0 hp1).condOn s hpos).probOf u ≤ (bern p hp0 hp1).probOf u := by
  rw [probOf_condOn, div_le_iff₀ hpos]
  exact probOf_and_le_of_isUpperSet_of_isLowerSet hp0 hp1 u s hu hs

end FinDist

/-! ## Conditioned Bernoulli bits -/

namespace CondBern

variable (μ : CondBern ι)

/-- The unconditioned product distribution `ν = Bernoulli(p)^{⊗ι}` of `μ`. -/
noncomputable def prior : FinDist (ι → Bool) :=
  FinDist.bern μ.p μ.p_pos.le (by linarith [μ.p_le_half])

/-- The normalizing constant is the prior probability of the allowed set. -/
theorem normConst_eq_probOf : μ.normConst = μ.prior.probOf (Avoids μ.forbidden) := rfl

theorem probOf_avoids_pos : 0 < μ.prior.probOf (Avoids μ.forbidden) :=
  μ.normConst_eq_probOf ▸ μ.normConst_pos

/-- `μ` is the prior conditioned on the allowed set. -/
theorem dist_eq_condOn : μ.dist = μ.prior.condOn (Avoids μ.forbidden) μ.probOf_avoids_pos := by
  unfold dist FinDist.condOn
  congr 1

/-- **Domination for conditioned Bernoulli bits**: `μ(U) ≤ ν(U)` for every increasing event. -/
theorem probOf_le_prior (u : (ι → Bool) → Prop) [DecidablePred u]
    (hu : IsUpperSet {x | u x}) : μ.dist.probOf u ≤ μ.prior.probOf u := by
  have hlow : IsLowerSet {x | Avoids μ.forbidden x} := fun a b hba ha =>
    Avoids.mono ha fun k hk => by
      have := hba k
      rw [hk] at this
      exact top_le_iff.mp this
  rw [dist_eq_condOn]
  exact FinDist.probOf_condOn_bern_le (p := μ.p) μ.p_pos.le _ (Avoids μ.forbidden) hlow
    μ.probOf_avoids_pos u hu

end CondBern

/-! ## Independence and full products under the product measure -/

/-- **Independence** under the product measure: an event depending only on the coordinates in
`S` and an event depending only on the coordinates outside `S` are independent. The proof
reindexes pairs of strings by swapping their coordinates outside `S`. -/
theorem sum_bernMass_and_eq_mul (p : ℝ) (S : Finset ι) (a b : (ι → Bool) → Prop)
    [DecidablePred a] [DecidablePred b]
    (ha : ∀ x y, (∀ i ∈ S, x i = y i) → (a x ↔ a y))
    (hb : ∀ x y, (∀ i ∉ S, x i = y i) → (b x ↔ b y)) :
    (∑ x, if a x ∧ b x then bernMass p x else 0)
      = (∑ x, if a x then bernMass p x else 0) * ∑ x, if b x then bernMass p x else 0 := by
  let σ : (ι → Bool) × (ι → Bool) → (ι → Bool) × (ι → Bool) := fun z =>
    (fun i => if i ∈ S then z.1 i else z.2 i, fun i => if i ∈ S then z.2 i else z.1 i)
  have hσ : Function.Involutive σ := fun z => by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
      by_cases hi : i ∈ S <;> simp [σ, hi]
  have hm : ∀ z, bernMass p (σ z).1 * bernMass p (σ z).2 = bernMass p z.1 * bernMass p z.2 := by
    intro z
    simp only [bernMass, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i ∈ S
    · simp [σ, hi]
    · simp [σ, hi, mul_comm]
  have key : ∀ z, ((if a (σ z).1 then bernMass p (σ z).1 else 0) *
      if b (σ z).2 then bernMass p (σ z).2 else 0)
      = (if a z.1 ∧ b z.1 then bernMass p z.1 else 0) * bernMass p z.2 := by
    intro z
    have h1 : a (σ z).1 ↔ a z.1 := ha _ _ fun i hi => by simp [σ, hi]
    have h2 : b (σ z).2 ↔ b z.1 := hb _ _ fun i hi => by simp [σ, hi]
    by_cases ha' : a z.1 <;> by_cases hb' : b z.1 <;> simp [h1, h2, ha', hb', hm z]
  calc (∑ x, if a x ∧ b x then bernMass p x else 0)
      = ∑ x, ∑ y, (if a x ∧ b x then bernMass p x else 0) * bernMass p y := by
        simp [← Finset.mul_sum, sum_bernMass]
    _ = ∑ z : (ι → Bool) × (ι → Bool),
          (if a z.1 ∧ b z.1 then bernMass p z.1 else 0) * bernMass p z.2 :=
        (Fintype.sum_prod_type' (fun x y =>
          (if a x ∧ b x then bernMass p x else 0) * bernMass p y)).symm
    _ = ∑ z : (ι → Bool) × (ι → Bool), ((if a (σ z).1 then bernMass p (σ z).1 else 0) *
          if b (σ z).2 then bernMass p (σ z).2 else 0) :=
        Finset.sum_congr rfl fun z _ => (key z).symm
    _ = ∑ z : (ι → Bool) × (ι → Bool), ((if a z.1 then bernMass p z.1 else 0) *
          if b z.2 then bernMass p z.2 else 0) :=
        Equiv.sum_comp hσ.toPerm (fun z => (if a z.1 then bernMass p z.1 else 0) *
          if b z.2 then bernMass p z.2 else 0)
    _ = _ := by
        rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type' (fun x y =>
          (if a x then bernMass p x else 0) * if b y then bernMass p y else 0)]

/-- Under the product measure, all coordinates of `S` are present with probability `p^|S|`. -/
theorem sum_bernMass_eq_pow_card (p : ℝ) (S : Finset ι) (s : (ι → Bool) → Prop)
    [DecidablePred s] (hs : ∀ x, s x ↔ ∀ i ∈ S, x i = true) :
    (∑ x, if s x then bernMass p x else 0) = p ^ S.card := by
  have h : ∀ x : ι → Bool, (if s x then bernMass p x else 0)
      = ∏ i, if i ∈ S then (if x i then p else 0) else (if x i then p else 1 - p) := by
    intro x
    by_cases hx : s x
    · rw [ite_eq_left hx, bernMass]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i ∈ S
      · simp [hi, (hs x).mp hx i hi]
      · simp [hi]
    · rw [ite_eq_right hx]
      obtain ⟨i, hi, hxi⟩ : ∃ i ∈ S, x i = false := by
        by_contra! hcon
        exact hx ((hs x).mpr fun i hi => by simpa using hcon i hi)
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, hxi])).symm
  have h2 : ∀ i, (∑ b : Bool, if i ∈ S then (if b then p else 0) else (if b then p else 1 - p))
      = if i ∈ S then p else 1 := by
    intro i
    by_cases hi : i ∈ S <;> simp [hi]
  rw [Finset.sum_congr rfl fun x _ => h x, ← Fintype.prod_sum
    (fun i (b : Bool) => if i ∈ S then (if b then p else 0) else (if b then p else 1 - p)),
    Finset.prod_congr rfl fun i _ => h2 i, Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_const]

end QuantumQueryComplexity
