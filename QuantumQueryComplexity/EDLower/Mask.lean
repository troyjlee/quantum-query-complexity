import QuantumQueryComplexity.EDLower.Gram
import QuantumQueryComplexity.Defs
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The `Δ_i`-modification and the Gram-level mask bounds

Two halves.

**Replacement.**  The assembled block of a pair `(a, b)` with coefficient
sequence `α` is `edBlock a b α = ∑_{T ⊆ {a,b}ᶜ} α_{|T|} • blockTerm a b edF T`.
Masking by `advD i` lets the block be replaced entrywise:

* `i = a` — the pair factor becomes `edF'` (`edBlockA`);
* `i = b` — it becomes `edF''` (`edBlockB`);
* `i ∉ {a,b}` — the cell-`i` factor `E₁ ↦ −E₀` telescopes the coefficients:
  `edBlockC` carries `α_k − α_{k+1}` on the patterns avoiding `i`.

**Quadratic forms.**  `norm_le_sqrt_of_rows`: a matrix each of whose rows is
a masked row of one of a family `G p` has `‖·‖² ≤ ‖∑_p Gram (G p)‖`.
`sum_gram_hadamard_advD_le`: masking every member of a family by `advD i`
at most quadruples the summed Gram bound (the LMRSS factor-2 trick, done by
pinching on the value at cell `i` — no stacked matrix is ever formed).
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-! ## Masked equality from entrywise agreement -/

lemma hadamard_advD_congr {A B : Matrix (ι → σ) (ι → σ) ℝ} {i : ι}
    (h : ∀ x y : ι → σ, x i ≠ y i → A x y = B x y) :
    A ⊙ advD i = B ⊙ advD i := by
  ext x y
  rw [hadamard_advD_apply, hadamard_advD_apply]
  by_cases hxy : x i = y i
  · rw [if_pos hxy, if_pos hxy]
  · rw [if_neg hxy, if_neg hxy]
    exact h x y hxy

/-! ## The assembled blocks and their replacements -/

/-- The block of the ordered pair `(a, b)`. -/
noncomputable def edBlock (a b : ι) (α : ℕ → ℝ) :
    Matrix (ι → σ) (ι → σ) ℝ :=
  ∑ T ∈ ({a, b} : Finset ι)ᶜ.powerset, α T.card • blockTerm a b edF T

/-- The replacement when the queried cell is `a`. -/
noncomputable def edBlockA (a b : ι) (α : ℕ → ℝ) :
    Matrix (ι → σ) (ι → σ) ℝ :=
  ∑ T ∈ ({a, b} : Finset ι)ᶜ.powerset, α T.card • blockTerm a b edF' T

/-- The replacement when the queried cell is `b`. -/
noncomputable def edBlockB (a b : ι) (α : ℕ → ℝ) :
    Matrix (ι → σ) (ι → σ) ℝ :=
  ∑ T ∈ ({a, b} : Finset ι)ᶜ.powerset, α T.card • blockTerm a b edF'' T

/-- The replacement for a queried cell `i ∉ {a, b}`: telescoped coefficients
on the patterns avoiding `i`. -/
noncomputable def edBlockC (a b i : ι) (α : ℕ → ℝ) :
    Matrix (ι → σ) (ι → σ) ℝ :=
  ∑ T ∈ (({a, b} : Finset ι)ᶜ.erase i).powerset,
    (α T.card - α (T.card + 1)) • blockTerm a b edF T

lemma edBlock_hadamard_left (a b : ι) (α : ℕ → ℝ) :
    edBlock (σ := σ) a b α ⊙ advD a = edBlockA a b α ⊙ advD a := by
  refine hadamard_advD_congr fun x y hxy => ?_
  rw [edBlock, edBlockA, Matrix.sum_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Matrix.smul_apply, Matrix.smul_apply]
  congr 1
  show (blockTerm a b edF T : Matrix (ι → σ) (ι → σ) ℝ) x y
    = blockTerm a b edF' T x y
  rw [blockTerm, blockTerm, Matrix.of_apply, Matrix.of_apply,
    edF_eq_edF' hxy]

lemma edBlock_hadamard_right {a b : ι} (hab : a ≠ b) (α : ℕ → ℝ) :
    edBlock (σ := σ) a b α ⊙ advD b = edBlockB a b α ⊙ advD b := by
  refine hadamard_advD_congr fun x y hxy => ?_
  rw [edBlock, edBlockB, Matrix.sum_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Matrix.smul_apply, Matrix.smul_apply]
  congr 1
  show (blockTerm a b edF T : Matrix (ι → σ) (ι → σ) ℝ) x y
    = blockTerm a b edF'' T x y
  rw [blockTerm, blockTerm, Matrix.of_apply, Matrix.of_apply]
  by_cases hguard : x a = x b
  · rw [edF_eq_edF'' (show x a ≠ y b from hguard ▸ hxy)]
  · rw [if_neg hguard]
    ring

/-- On the mask support, a pattern containing `i` flips sign against the
pattern with `i` removed. -/
lemma blockTerm_insert_cell {a b i : ι} (hia : i ≠ a) (hib : i ≠ b)
    {T : Finset ι} (hT : T ⊆ ({a, b} : Finset ι)ᶜ.erase i)
    {x y : ι → σ} (hxy : x i ≠ y i) :
    (blockTerm a b (edF (σ := σ)) (insert i T)) x y
      = -(blockTerm a b edF T x y) := by
  have hiT : i ∉ T := fun h => Finset.notMem_erase i _ (hT h)
  have hipair : i ∈ ({a, b} : Finset ι)ᶜ := by
    refine Finset.mem_compl.mpr fun h => ?_
    rcases Finset.mem_insert.mp h with h | h
    · exact hia h
    · exact hib (Finset.mem_singleton.mp h)
  rw [blockTerm, blockTerm, Matrix.of_apply, Matrix.of_apply,
    ← Finset.mul_prod_erase _ _ hipair, ← Finset.mul_prod_erase _ _ hipair,
    if_pos (Finset.mem_insert_self i T), if_neg hiT]
  have hcell : (cellE1 (x i) (y i) : ℝ) = -(cellE0 (x i) (y i)) := by
    rw [cellE1, cellE0, Matrix.of_apply, Matrix.of_apply, if_neg hxy]
    ring
  rw [hcell,
    Finset.prod_congr rfl fun c hc =>
      show (if c ∈ insert i T then cellE1 (x c) (y c)
            else cellE0 (x c) (y c))
        = (if c ∈ T then cellE1 (x c) (y c) else cellE0 (x c) (y c))
        from by
        have hci : c ≠ i := (Finset.mem_erase.mp hc).1
        by_cases hcT : c ∈ T
        · rw [if_pos (Finset.mem_insert_of_mem hcT), if_pos hcT]
        · rw [if_neg (fun h => by
            rcases Finset.mem_insert.mp h with h | h
            · exact hci h
            · exact hcT h), if_neg hcT]]
  ring

lemma edBlock_hadamard_out {a b i : ι} (hab : a ≠ b) (hia : i ≠ a)
    (hib : i ≠ b) (α : ℕ → ℝ) :
    edBlock (σ := σ) a b α ⊙ advD i = edBlockC a b i α ⊙ advD i := by
  have hipair : i ∈ ({a, b} : Finset ι)ᶜ := by
    refine Finset.mem_compl.mpr fun h => ?_
    rcases Finset.mem_insert.mp h with h | h
    · exact hia h
    · exact hib (Finset.mem_singleton.mp h)
  have hins : insert i (({a, b} : Finset ι)ᶜ.erase i)
      = ({a, b} : Finset ι)ᶜ := Finset.insert_erase hipair
  refine hadamard_advD_congr fun x y hxy => ?_
  rw [edBlock, edBlockC, Matrix.sum_apply, Matrix.sum_apply]
  rw [show (∑ T ∈ ({a, b} : Finset ι)ᶜ.powerset,
        (α T.card • blockTerm a b (edF (σ := σ)) T) x y)
      = ∑ T ∈ (insert i (({a, b} : Finset ι)ᶜ.erase i)).powerset,
        (α T.card • blockTerm a b edF T) x y from by rw [hins],
    Finset.sum_powerset_insert (Finset.notMem_erase i _)]
  rw [Finset.sum_congr rfl fun T (hT : T ∈ (({a, b} : Finset ι)ᶜ.erase i).powerset) =>
    show (α (insert i T).card • blockTerm a b (edF (σ := σ)) (insert i T)) x y
      = -(α (T.card + 1) * blockTerm a b edF T x y) from by
      have hiT : i ∉ T := fun h =>
        Finset.notMem_erase i _ (Finset.mem_powerset.mp hT h)
      rw [Matrix.smul_apply, Finset.card_insert_of_notMem hiT,
        blockTerm_insert_cell hia hib (Finset.mem_powerset.mp hT) hxy,
        smul_eq_mul]
      ring]
  rw [Finset.sum_neg_distrib]
  rw [Finset.sum_congr rfl fun T _ =>
    show (α T.card • blockTerm a b (edF (σ := σ)) T) x y
      = α T.card * blockTerm a b edF T x y from by
      rw [Matrix.smul_apply, smul_eq_mul]]
  rw [Finset.sum_congr rfl fun T _ =>
    show ((α T.card - α (T.card + 1)) • blockTerm a b (edF (σ := σ)) T) x y
      = (α T.card - α (T.card + 1)) * blockTerm a b edF T x y from by
      rw [Matrix.smul_apply, smul_eq_mul]]
  rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun T _ => ?_
  ring

/-! ## Quadratic-form machinery -/

private lemma abs_dotProduct_le {X : Type*} [Fintype X] (v w : X → ℝ) :
    |v ⬝ᵥ w| ≤ Real.sqrt (v ⬝ᵥ v) * Real.sqrt (w ⬝ᵥ w) := by
  rw [abs_le]
  constructor
  · have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun t => -v t) w
    have hrw : (∑ t, -v t * w t) = -(v ⬝ᵥ w) := by
      rw [dotProduct, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun t _ => by ring
    have hsq : (∑ t, (-v t) ^ 2) = v ⬝ᵥ v := by
      rw [dotProduct]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [hrw, hsq] at h
    have hw : (∑ t, w t ^ 2) = w ⬝ᵥ w := by
      rw [dotProduct]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [hw] at h
    linarith
  · have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ v w
    have hv : (∑ t, v t ^ 2) = v ⬝ᵥ v := by
      rw [dotProduct]
      exact Finset.sum_congr rfl fun t _ => by ring
    have hw : (∑ t, w t ^ 2) = w ⬝ᵥ w := by
      rw [dotProduct]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [hv, hw] at h
    exact h

/-- **Row domination**: if every row of `Γ` is a masked row of some `G p`
(or zero), then `‖Γ‖² ≤ ‖∑_p Gram (G p)‖`, in the quadratic-form form. -/
theorem norm_le_sqrt_of_rows {X : Type*} [Fintype X] [DecidableEq X]
    {P : Type*} [Fintype P] (Γ : Matrix X X ℝ) (G : P → Matrix X X ℝ)
    (m : X → ℝ) (hm : ∀ y, |m y| ≤ 1)
    (hrow : ∀ x, (∀ y, Γ x y = 0) ∨ ∃ p, ∀ y, Γ x y = G p x y * m y)
    {W : ℝ} (hW0 : 0 ≤ W)
    (hquad : ∀ v : X → ℝ,
      (∑ p, (G p *ᵥ v) ⬝ᵥ (G p *ᵥ v)) ≤ W * (v ⬝ᵥ v)) :
    ‖Γ‖ ≤ Real.sqrt W := by
  refine l2_opNorm_le_of_forall_dotProduct _ (Real.sqrt_nonneg W)
    fun u v => ?_
  set mv : X → ℝ := fun y => m y * v y with hmv
  have hrowval : ∀ x, Γ.mulVec v x = 0 ∨ ∃ p, Γ.mulVec v x = (G p *ᵥ mv) x := by
    intro x
    rcases hrow x with h | ⟨p, hp⟩
    · left
      rw [Matrix.mulVec, dotProduct]
      exact Finset.sum_eq_zero fun y _ => by rw [h y, zero_mul]
    · right
      refine ⟨p, ?_⟩
      rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hp y, hmv]
      ring
  have hquadΓ : (Γ *ᵥ v) ⬝ᵥ (Γ *ᵥ v) ≤ W * (v ⬝ᵥ v) := by
    have hmvle : mv ⬝ᵥ mv ≤ v ⬝ᵥ v := by
      rw [dotProduct, dotProduct]
      refine Finset.sum_le_sum fun y _ => ?_
      rw [hmv]
      have h1 : (m y * v y) * (m y * v y) = (m y * m y) * (v y * v y) := by
        ring
      rw [h1]
      have h2 : m y * m y ≤ 1 := by
        have := abs_mul_abs_self (m y)
        nlinarith [hm y, abs_nonneg (m y)]
      nlinarith [mul_self_nonneg (v y), mul_self_nonneg (m y)]
    calc (Γ *ᵥ v) ⬝ᵥ (Γ *ᵥ v)
        = ∑ x, (Γ.mulVec v x) * (Γ.mulVec v x) := rfl
      _ ≤ ∑ x, ∑ p, ((G p *ᵥ mv) x) * ((G p *ᵥ mv) x) := by
          refine Finset.sum_le_sum fun x _ => ?_
          rcases hrowval x with h | ⟨p, hp⟩
          · rw [h, mul_zero]
            exact Finset.sum_nonneg fun p _ => mul_self_nonneg _
          · rw [hp]
            exact Finset.single_le_sum
              (fun p _ => mul_self_nonneg ((G p *ᵥ mv) x))
              (Finset.mem_univ p)
      _ = ∑ p, (G p *ᵥ mv) ⬝ᵥ (G p *ᵥ mv) := by
          rw [Finset.sum_comm]
          rfl
      _ ≤ W * (mv ⬝ᵥ mv) := hquad mv
      _ ≤ W * (v ⬝ᵥ v) := mul_le_mul_of_nonneg_left hmvle hW0
  calc |u ⬝ᵥ Γ *ᵥ v|
      ≤ Real.sqrt (u ⬝ᵥ u) * Real.sqrt ((Γ *ᵥ v) ⬝ᵥ (Γ *ᵥ v)) :=
        abs_dotProduct_le u (Γ *ᵥ v)
    _ ≤ Real.sqrt (u ⬝ᵥ u) * Real.sqrt (W * (v ⬝ᵥ v)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hquadΓ)
          (Real.sqrt_nonneg _)
    _ = Real.sqrt W * Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v) := by
        rw [Real.sqrt_mul hW0]
        ring

/-- **Pinching + the factor-2 trick**: masking a family by `advD i` at most
quadruples the summed Gram bound. -/
theorem sum_gram_hadamard_advD_le {P : Type*} [Fintype P] (i : ι)
    (A : P → Matrix (ι → σ) (ι → σ) ℝ) {W : ℝ} (hW0 : 0 ≤ W)
    (hquad : ∀ v : (ι → σ) → ℝ,
      (∑ p, (A p *ᵥ v) ⬝ᵥ (A p *ᵥ v)) ≤ W * (v ⬝ᵥ v))
    (v : (ι → σ) → ℝ) :
    (∑ p, ((A p ⊙ advD i) *ᵥ v) ⬝ᵥ ((A p ⊙ advD i) *ᵥ v))
      ≤ 4 * W * (v ⬝ᵥ v) := by
  classical
  have hmasksum : (∑ s : σ, (fun y : ι → σ => if y i = s then v y else 0)
      ⬝ᵥ (fun y : ι → σ => if y i = s then v y else 0)) = v ⬝ᵥ v := by
    show (∑ s : σ, ∑ y : ι → σ,
        (if y i = s then v y else 0) * (if y i = s then v y else 0))
      = ∑ y : ι → σ, v y * v y
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_congr rfl fun s (_ : s ∈ Finset.univ) =>
      show (if y i = s then v y else 0) * (if y i = s then v y else 0)
        = if y i = s then v y * v y else 0 from by
        by_cases h : y i = s
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h, zero_mul],
      Finset.sum_ite_eq Finset.univ (y i) fun _ => v y * v y,
      if_pos (Finset.mem_univ _)]
  have hpinch : (∑ p, ∑ x : ι → σ,
      ((A p *ᵥ fun y => if y i = x i then v y else 0) x)
        * ((A p *ᵥ fun y => if y i = x i then v y else 0) x))
      ≤ W * (v ⬝ᵥ v) := by
    have hfiber : ∀ p : P, (∑ x : ι → σ,
        ((A p *ᵥ fun y => if y i = x i then v y else 0) x)
          * ((A p *ᵥ fun y => if y i = x i then v y else 0) x))
        ≤ ∑ s : σ, ∑ x : ι → σ,
            ((A p *ᵥ fun y => if y i = s then v y else 0) x)
              * ((A p *ᵥ fun y => if y i = s then v y else 0) x) := by
      intro p
      calc (∑ x : ι → σ,
          ((A p *ᵥ fun y => if y i = x i then v y else 0) x)
            * ((A p *ᵥ fun y => if y i = x i then v y else 0) x))
          = ∑ x ∈ Finset.univ.filter
              (fun x : ι → σ => x i ∈ (Finset.univ : Finset σ)),
              ((A p *ᵥ fun y => if y i = x i then v y else 0) x)
                * ((A p *ᵥ fun y => if y i = x i then v y else 0) x) := by
            rw [Finset.filter_true_of_mem fun x _ => Finset.mem_univ (x i)]
        _ = ∑ s : σ, ∑ x ∈ Finset.univ.filter fun x : ι → σ => x i = s,
              ((A p *ᵥ fun y => if y i = x i then v y else 0) x)
                * ((A p *ᵥ fun y => if y i = x i then v y else 0) x) :=
            (Finset.sum_fiberwise_eq_sum_filter Finset.univ Finset.univ
              (fun x : ι → σ => x i) _).symm
        _ ≤ ∑ s : σ, ∑ x : ι → σ,
              ((A p *ᵥ fun y => if y i = s then v y else 0) x)
                * ((A p *ᵥ fun y => if y i = s then v y else 0) x) := by
            refine Finset.sum_le_sum fun s _ => ?_
            refine le_trans (le_of_eq (Finset.sum_congr rfl fun x hx => ?_))
              (Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.filter_subset _ _)
                fun x _ _ => mul_self_nonneg _)
            have hxs : x i = s := (Finset.mem_filter.mp hx).2
            rw [hxs]
    calc (∑ p, ∑ x : ι → σ,
        ((A p *ᵥ fun y => if y i = x i then v y else 0) x)
          * ((A p *ᵥ fun y => if y i = x i then v y else 0) x))
        ≤ ∑ p, ∑ s : σ, ∑ x : ι → σ,
            ((A p *ᵥ fun y => if y i = s then v y else 0) x)
              * ((A p *ᵥ fun y => if y i = s then v y else 0) x) :=
          Finset.sum_le_sum fun p _ => hfiber p
      _ = ∑ s : σ, ∑ p, ((A p *ᵥ fun y => if y i = s then v y else 0)
            ⬝ᵥ (A p *ᵥ fun y => if y i = s then v y else 0)) :=
          Finset.sum_comm
      _ ≤ ∑ s : σ, W * ((fun y : ι → σ => if y i = s then v y else 0)
            ⬝ᵥ (fun y : ι → σ => if y i = s then v y else 0)) :=
          Finset.sum_le_sum fun s _ => hquad _
      _ = W * (v ⬝ᵥ v) := by rw [← Finset.mul_sum, hmasksum]
  have hsplit : ∀ (p : P) (x : ι → σ),
      ((A p ⊙ advD i) *ᵥ v) x
        = (A p *ᵥ v) x
          - (A p *ᵥ fun y => if y i = x i then v y else 0) x := by
    intro p x
    show (∑ y, (A p ⊙ advD i) x y * v y)
      = (∑ y, A p x y * v y)
        - ∑ y, A p x y * (if y i = x i then v y else 0)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hadamard_advD_apply]
    by_cases h : x i = y i
    · rw [if_pos h, if_pos h.symm]
      ring
    · rw [if_neg h, if_neg fun hc => h hc.symm]
      ring
  calc (∑ p, ((A p ⊙ advD i) *ᵥ v) ⬝ᵥ ((A p ⊙ advD i) *ᵥ v))
      = ∑ p, ∑ x : ι → σ,
          ((A p *ᵥ v) x - (A p *ᵥ fun y => if y i = x i then v y else 0) x)
            * ((A p *ᵥ v) x
              - (A p *ᵥ fun y => if y i = x i then v y else 0) x) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        show (∑ x, ((A p ⊙ advD i) *ᵥ v) x * (((A p ⊙ advD i) *ᵥ v) x)) = _
        exact Finset.sum_congr rfl fun x _ => by rw [hsplit p x]
    _ ≤ ∑ p, ∑ x : ι → σ,
          (2 * ((A p *ᵥ v) x * (A p *ᵥ v) x)
            + 2 * ((A p *ᵥ fun y => if y i = x i then v y else 0) x
              * (A p *ᵥ fun y => if y i = x i then v y else 0) x)) := by
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun x _ => ?_
        nlinarith [sq_nonneg ((A p *ᵥ v) x
          + (A p *ᵥ fun y => if y i = x i then v y else 0) x)]
    _ = 2 * (∑ p, (A p *ᵥ v) ⬝ᵥ (A p *ᵥ v))
          + 2 * ∑ p, ∑ x : ι → σ,
            ((A p *ᵥ fun y => if y i = x i then v y else 0) x
              * (A p *ᵥ fun y => if y i = x i then v y else 0) x) := by
        rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) =>
          show (∑ x : ι → σ,
              (2 * ((A p *ᵥ v) x * (A p *ᵥ v) x)
                + 2 * ((A p *ᵥ fun y => if y i = x i then v y else 0) x
                  * (A p *ᵥ fun y => if y i = x i then v y else 0) x)))
            = 2 * ((A p *ᵥ v) ⬝ᵥ (A p *ᵥ v))
              + 2 * ∑ x : ι → σ,
                ((A p *ᵥ fun y => if y i = x i then v y else 0) x
                  * (A p *ᵥ fun y => if y i = x i then v y else 0) x) from by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
            rfl,
          Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (W * (v ⬝ᵥ v)) + 2 * (W * (v ⬝ᵥ v)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hquad v) (by norm_num))
          (mul_le_mul_of_nonneg_left hpinch (by norm_num))
    _ = 4 * W * (v ⬝ᵥ v) := by ring

end QuantumQueryComplexity
