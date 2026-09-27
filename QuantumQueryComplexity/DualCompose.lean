import QuantumQueryComplexity.Dual
import QuantumQueryComplexity.Composition.Main
set_option linter.style.header false

/-!
# Composition of dual solutions and the composition upper bound

Dual solutions compose multiplicatively (Belovs–Lee, arXiv:2004.06439,
Theorem 24; the construction is from LMRSS): tensoring an outer dual solution
with an inner one,

  `u_{x,(p,q)} = ψ_{x̃,p} ⊗ u_{x·ₚ,q}`,  `v_{x,(p,q)} = φ_{x̃,p} ⊗ v_{x·ₚ,q}`,

produces a feasible dual solution for `f ∘ gᵏ` of cost the product of the
costs (`DualPair.compose`).  This is exactly where the LMRSS constraints on
pairs with `g x = g y` are used: they kill the blocks where the inner
function values agree.

Consequently `advDual (f ∘ gᵏ) ≤ advDual f * advDual g`, and by weak duality

  `ADV±(f ∘ gᵏ) ≤ advDual f * advDual g`   (`advPM_composeFun_le_advDual_mul`)

unconditionally.  Combined with the lower bound
`advPM_mul_le_advPM_composeFun` this sandwiches the composed value.  The
perfect composition theorem `ADV±(f ∘ gᵏ) = ADV±(f) · ADV±(g)` follows the
moment strong duality `advDual = advPM` is available
(`advPM_composeFun_eq_of_dual_eq`); strong duality is the single missing
ingredient, and is genuine SDP duality, absent from mathlib.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  {f : (α → Bool) → Bool} {g : α → (β → Bool) → Bool}
  {K₁ K₂ : Type*} [Fintype K₁] [Fintype K₂]

/-- **Composition of dual solutions** (BL Theorem 24 construction). -/
def DualPair.compose (Pf : DualPair K₁ f) (Pg : ∀ i, DualPair K₂ (g i)) :
    DualPair (K₁ × K₂) (composeFunFam f g) where
  u x ℓ k := Pf.u (tilde g x) ℓ.1 k.1 * (Pg ℓ.1).u (slice x ℓ.1) ℓ.2 k.2
  v y ℓ k := Pf.v (tilde g y) ℓ.1 k.1 * (Pg ℓ.1).v (slice y ℓ.1) ℓ.2 k.2
  constraint x y := by
    -- The inner sum factorises as (outer inner product) * (inner one).
    have hinner : ∀ (p : α) (q : β),
        (∑ k : K₁ × K₂,
          (Pf.u (tilde g x) p k.1 * (Pg p).u (slice x p) q k.2) *
          (Pf.v (tilde g y) p k.1 * (Pg p).v (slice y p) q k.2))
        = (∑ k₁, Pf.u (tilde g x) p k₁ * Pf.v (tilde g y) p k₁) *
          (∑ k₂, (Pg p).u (slice x p) q k₂ * (Pg p).v (slice y p) q k₂) := by
      intro p q
      rw [Fintype.sum_prod_type]
      show (∑ k₁, ∑ k₂,
          (Pf.u (tilde g x) p k₁ * (Pg p).u (slice x p) q k₂) *
          (Pf.v (tilde g y) p k₁ * (Pg p).v (slice y p) q k₂)) = _
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun k₁ _ =>
        Finset.sum_congr rfl fun k₂ _ => by ring
    -- Summing over the `p`-th block uses the inner constraint (both cases!).
    have hp : ∀ p : α,
        (∑ q : β, if slice x p q = slice y p q then (0:ℝ) else
          ∑ k : K₁ × K₂,
            (Pf.u (tilde g x) p k.1 * (Pg p).u (slice x p) q k.2) *
            (Pf.v (tilde g y) p k.1 * (Pg p).v (slice y p) q k.2))
        = if g p (slice x p) = g p (slice y p) then (0:ℝ) else
            ∑ k₁, Pf.u (tilde g x) p k₁ * Pf.v (tilde g y) p k₁ := by
      intro p
      have h1 : ∀ q : β,
          (if slice x p q = slice y p q then (0:ℝ) else
            ∑ k : K₁ × K₂,
              (Pf.u (tilde g x) p k.1 * (Pg p).u (slice x p) q k.2) *
              (Pf.v (tilde g y) p k.1 * (Pg p).v (slice y p) q k.2))
          = (∑ k₁, Pf.u (tilde g x) p k₁ * Pf.v (tilde g y) p k₁) *
            (if slice x p q = slice y p q then (0:ℝ) else
              ∑ k₂, (Pg p).u (slice x p) q k₂ * (Pg p).v (slice y p) q k₂) := by
        intro q
        by_cases hq : slice x p q = slice y p q
        · rw [if_pos hq, if_pos hq, mul_zero]
        · rw [if_neg hq, if_neg hq, hinner p q]
      rw [Finset.sum_congr rfl fun q (_ : q ∈ Finset.univ) => h1 q,
        ← Finset.mul_sum, (Pg p).constraint (slice x p) (slice y p)]
      by_cases hgp : g p (slice x p) = g p (slice y p)
      · rw [if_pos hgp, if_pos hgp, mul_zero]
      · rw [if_neg hgp, if_neg hgp, mul_one]
    -- The outer constraint finishes the computation.
    show (∑ ℓ : α × β, if x ℓ = y ℓ then (0:ℝ) else
      ∑ k : K₁ × K₂,
        (Pf.u (tilde g x) ℓ.1 k.1 * (Pg ℓ.1).u (slice x ℓ.1) ℓ.2 k.2) *
        (Pf.v (tilde g y) ℓ.1 k.1 * (Pg ℓ.1).v (slice y ℓ.1) ℓ.2 k.2))
      = if f (tilde g x) = f (tilde g y) then (0:ℝ) else 1
    trans (∑ p : α, if g p (slice x p) = g p (slice y p) then (0:ℝ) else
        ∑ k₁, Pf.u (tilde g x) p k₁ * Pf.v (tilde g y) p k₁)
    · rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun p _ => hp p
    · exact Pf.constraint (tilde g x) (tilde g y)

/-- The cost of a composed dual solution is the product of the costs. -/
lemma DualPair.compose_isCostLe {Pf : DualPair K₁ f} {Pg : ∀ i, DualPair K₂ (g i)}
    {c₁ c₂ : ℝ} (hf : Pf.IsCostLe c₁) (hg : ∀ i, (Pg i).IsCostLe c₂)
    (hc₂ : 0 ≤ c₂) :
    (Pf.compose Pg).IsCostLe (c₁ * c₂) := by
  constructor
  · intro x
    show (∑ ℓ : α × β, ∑ k : K₁ × K₂,
      (Pf.u (tilde g x) ℓ.1 k.1 * (Pg ℓ.1).u (slice x ℓ.1) ℓ.2 k.2) *
      (Pf.u (tilde g x) ℓ.1 k.1 * (Pg ℓ.1).u (slice x ℓ.1) ℓ.2 k.2)) ≤ c₁ * c₂
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
            (∑ q : β, ∑ k₂, (Pg p).u (slice x p) q k₂ * (Pg p).u (slice x p) q k₂) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun q _ => hin p q
      _ ≤ ∑ p : α, (∑ k₁, Pf.u (tilde g x) p k₁ * Pf.u (tilde g x) p k₁) * c₂ :=
          Finset.sum_le_sum fun p _ =>
            mul_le_mul_of_nonneg_left ((hg p).1 (slice x p)) (hSnn p)
      _ = (∑ p : α, ∑ k₁, Pf.u (tilde g x) p k₁ * Pf.u (tilde g x) p k₁) * c₂ :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ c₁ * c₂ := mul_le_mul_of_nonneg_right (hf.1 (tilde g x)) hc₂
  · intro x
    show (∑ ℓ : α × β, ∑ k : K₁ × K₂,
      (Pf.v (tilde g x) ℓ.1 k.1 * (Pg ℓ.1).v (slice x ℓ.1) ℓ.2 k.2) *
      (Pf.v (tilde g x) ℓ.1 k.1 * (Pg ℓ.1).v (slice x ℓ.1) ℓ.2 k.2)) ≤ c₁ * c₂
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
            (∑ q : β, ∑ k₂, (Pg p).v (slice x p) q k₂ * (Pg p).v (slice x p) q k₂) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun q _ => hin p q
      _ ≤ ∑ p : α, (∑ k₁, Pf.v (tilde g x) p k₁ * Pf.v (tilde g x) p k₁) * c₂ :=
          Finset.sum_le_sum fun p _ =>
            mul_le_mul_of_nonneg_left ((hg p).2 (slice x p)) (hSnn p)
      _ = (∑ p : α, ∑ k₁, Pf.v (tilde g x) p k₁ * Pf.v (tilde g x) p k₁) * c₂ :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ c₁ * c₂ := mul_le_mul_of_nonneg_right (hf.2 (tilde g x)) hc₂

/-- **The dual value is submultiplicative under composition.** -/
theorem advDual_composeFun_le (f : (α → Bool) → Bool)
    (g : (β → Bool) → Bool) :
    advDual (composeFun f g) ≤ advDual f * advDual g := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hA : 0 ≤ advDual f := advDual_nonneg f
  have hB : 0 ≤ advDual g := advDual_nonneg g
  have hden : (0:ℝ) < advDual f + advDual g + 1 := by linarith
  set δ := min 1 (ε / (advDual f + advDual g + 1)) with hδdef
  have hδpos : 0 < δ := lt_min one_pos (div_pos hε hden)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ * (advDual f + advDual g + 1) ≤ ε := by
    have h2 : δ ≤ ε / (advDual f + advDual g + 1) := min_le_right _ _
    calc δ * (advDual f + advDual g + 1)
        ≤ (ε / (advDual f + advDual g + 1)) * (advDual f + advDual g + 1) :=
          mul_le_mul_of_nonneg_right h2 hden.le
      _ = ε := div_mul_cancel₀ _ hden.ne'
  obtain ⟨n₁, P₁, hP₁⟩ :=
    exists_dualPair_of_lt (g := f) (c := advDual f + δ) (by linarith)
  obtain ⟨n₂, P₂, hP₂⟩ :=
    exists_dualPair_of_lt (g := g) (c := advDual g + δ) (by linarith)
  have hcost : (P₁.compose (g := constFam g) (fun _ => P₂)).IsCostLe
      ((advDual f + δ) * (advDual g + δ)) :=
    DualPair.compose_isCostLe hP₁ (fun _ => hP₂) (by linarith)
  have hle := advDual_le_of_dualPair
    (P₁.compose (g := constFam g) (fun _ => P₂)) (by nlinarith) hcost
  refine hle.trans ?_
  nlinarith [mul_le_of_le_one_right hδpos.le hδ1]

/-- **The composition upper bound**, unconditional: the adversary bound of a
composed function is at most the product of the *dual* values. -/
theorem advPM_composeFun_le_advDual_mul (f : (α → Bool) → Bool)
    (g : (β → Bool) → Bool) :
    advPM (composeFun f g) ≤ advDual f * advDual g :=
  (advPM_le_advDual _).trans (advDual_composeFun_le f g)

/-- The composed adversary bound is sandwiched between the product of the
primal values and the product of the dual values. -/
theorem advPM_composeFun_sandwich (f : (α → Bool) → Bool)
    (g : (β → Bool) → Bool) :
    advPM f * advPM g ≤ advPM (composeFun f g) ∧
      advPM (composeFun f g) ≤ advDual f * advDual g :=
  ⟨advPM_mul_le_advPM_composeFun f g, advPM_composeFun_le_advDual_mul f g⟩

/-- **Perfect composition, conditional on strong duality.**  Strong duality
(`advDual = advPM`) is the only missing ingredient for the exact composition
theorem `ADV±(f ∘ gᵏ) = ADV±(f) · ADV±(g)`. -/
theorem advPM_composeFun_eq_of_dual_eq (f : (α → Bool) → Bool)
    (g : (β → Bool) → Bool) (hf : advDual f = advPM f)
    (hg : advDual g = advPM g) :
    advPM (composeFun f g) = advPM f * advPM g := by
  refine le_antisymm ?_ (advPM_mul_le_advPM_composeFun f g)
  rw [← hf, ← hg]
  exact advPM_composeFun_le_advDual_mul f g

/-! ## Functions whose adversary bound is certified on both sides -/

/-- `HasAdvValue f c` records that the adversary bound of `f` equals `c` *and*
that this value is certified by a dual solution — i.e. strong duality holds at
`f`.  This is exactly the hypothesis needed for perfect composition, and it is
established for concrete functions by exhibiting a matching primal/dual pair. -/
def HasAdvValue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → Bool) (c : ℝ) : Prop :=
  advPM f = c ∧ advDual f = c

/-- Building a `HasAdvValue` from a primal lower bound and a dual upper bound:
weak duality squeezes them together. -/
theorem hasAdvValue_of_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → Bool) → Bool} {c : ℝ} (hprimal : c ≤ advPM f)
    (hdual : advDual f ≤ c) : HasAdvValue f c :=
  ⟨le_antisymm ((advPM_le_advDual f).trans hdual) hprimal,
    le_antisymm hdual (hprimal.trans (advPM_le_advDual f))⟩

/-- **Certified values compose exactly.**  If strong duality holds at `f` and
at `g`, then it holds at `f ∘ gᵏ`, with the product value. -/
theorem HasAdvValue.compose {g : (β → Bool) → Bool} {a b : ℝ}
    (hf : HasAdvValue f a) (hg : HasAdvValue g b) :
    HasAdvValue (composeFun f g) (a * b) := by
  have hprimal : a * b ≤ advPM (composeFun f g) := by
    rw [← hf.1, ← hg.1]
    exact advPM_mul_le_advPM_composeFun f g
  have hdual : advDual (composeFun f g) ≤ a * b := by
    rw [← hf.2, ← hg.2]
    exact advDual_composeFun_le f g
  exact hasAdvValue_of_le hprimal hdual

end QuantumQueryComplexity
