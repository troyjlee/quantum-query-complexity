import QuantumQueryComplexity.TreeSearch.Optimal
import QuantumQueryComplexity.Promise.ComposeShared

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Tree search on a promise with vertex-dependent cell outputs

The public certificate: finite promise inputs `X`, an arbitrary observation map
`read : X → ι → σ`, cell outputs `cell v : X → Γ v` in vertex-dependent finite alphabets, each
with a promise dual of cost `t v`, and a marking `mark v : X → Prop` that is local on actual
inputs: it depends on `x` only through the cells along the root path of `v`.  Then

    HasDualOn read (fun x => decide (∃ v, mark v x)) (recCost T t ρ)     (`hasDualOn_treeSearch_recCost`)

with coefficient one.  The construction encodes every cell in the common alphabet `Σ v, Γ v`
(`cellE`, an injective recoding for fixed `v`, so `HasDualOn.ofKer` keeps the cost), marks a
virtual table `z` at `v` when some actual input `x` is marked at `v` and has the same cells
along the path of `v` (`markE`, root-path local by definition, and equal to `mark v x` on the
table of `x` by locality), applies the optimized weighted dual of `Optimal.lean` on total
virtual tables, composes with the encoded cell duals by `hasDualOn_sharedFunOn`, and recodes.
No default element of any `Γ v` is needed, and an empty promise is allowed.

Also: the common-output wrapper `hasDualOn_treeSearch_recCost'`, the total-input
specialization `hasDual_treeSearch_recCost`, and the general fact `HasDualOn.one_le_of_ne`
(a certificate of cost below one forces constancy on the promise).
-/

namespace QuantumQueryComplexity

/-! ## A certificate of cost below one forces constancy -/

section OneLe

variable {ι σ X O : Type} [Fintype ι] [DecidableEq ι] [DecidableEq σ] [Fintype X]
  [DecidableEq O]

/-- **Two inputs with different values force cost at least one**: the constraint pays `1`
along a Cauchy–Schwarz pair of vectors of squared norms at most `c`. -/
theorem HasDualOn.one_le_of_ne {read : X → ι → σ} {f : X → O} {c : ℝ}
    (h : HasDualOn read f c) {x y : X} (hxy : f x ≠ f y) : 1 ≤ c := by
  classical
  obtain ⟨K, hK, P, hP⟩ := h
  have hcon := P.constraint x y
  rw [if_neg hxy] at hcon
  set F : ι × K → ℝ := fun p => if read x p.1 = read y p.1 then 0 else P.u x p.1 p.2 with hF
  set G : ι × K → ℝ := fun p => P.v y p.1 p.2 with hG
  have hFG : ∑ p, F p * G p = 1 := by
    rw [← hcon, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : read x i = read y i
    · simp [hF, hG, hi]
    · simp [hF, hG, hi]
  have hF2 : ∑ p, F p ^ 2 ≤ c := by
    refine le_trans ?_ (hP.1 x)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_
    by_cases hi : read x i = read y i
    · simp [hF, hi]; exact mul_self_nonneg _
    · simp [hF, hi, sq]
  have hG2 : ∑ p, G p ^ 2 ≤ c := by
    refine le_trans (le_of_eq ?_) (hP.2 y)
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by simp [hG, sq]
  have hc0 : 0 ≤ c := le_trans (Finset.sum_nonneg fun p _ => sq_nonneg (G p)) hG2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ F G
  rw [hFG, one_pow] at hcs
  have hF0 : 0 ≤ ∑ p, F p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  have : 1 ≤ c * c := hcs.trans (mul_le_mul hF2 hG2 (Finset.sum_nonneg fun p _ => sq_nonneg _) hc0)
  nlinarith

end OneLe

namespace AncTree

open Finset

variable {V : Type} [DecidableEq V] [Fintype V] (T : AncTree V)
variable {ι σ X : Type} [Fintype ι] [DecidableEq ι] [DecidableEq σ] [Fintype X] [DecidableEq X]
variable {Γ : V → Type} [∀ v, Fintype (Γ v)] [∀ v, DecidableEq (Γ v)]

/-- The cell `v`, encoded in the common alphabet `Σ v, Γ v`. -/
def cellE (cell : ∀ v, X → Γ v) (v : V) (x : X) : Σ v, Γ v := ⟨v, cell v x⟩

/-- The marking of a virtual table: some actual marked input has the same cells on the path. -/
def markE (cell : ∀ v, X → Γ v) (mark : V → X → Prop) (v : V) (z : V → Σ v, Γ v) : Prop :=
  ∃ x, mark v x ∧ ∀ w ∈ T.path v, z w = cellE cell w x

lemma markE_local (cell : ∀ v, X → Γ v) (mark : V → X → Prop) (v : V) (z z' : V → Σ v, Γ v)
    (h : ∀ i ≤ T.depth v, z (T.ancAt v i) = z' (T.ancAt v i)) :
    T.markE cell mark v z ↔ T.markE cell mark v z' := by
  have hagree : ∀ w ∈ T.path v, z w = z' w := fun w hw => by
    obtain ⟨i, hi, rfl⟩ := T.mem_path.1 hw
    exact h i hi
  constructor
  · rintro ⟨x, hm, hz⟩; exact ⟨x, hm, fun w hw => (hagree w hw).symm.trans (hz w hw)⟩
  · rintro ⟨x, hm, hz⟩; exact ⟨x, hm, fun w hw => (hagree w hw).trans (hz w hw)⟩

/-- On the table of an actual input, the virtual marking is the actual marking. -/
lemma markE_table (cell : ∀ v, X → Γ v) (mark : V → X → Prop)
    (hloc : ∀ v x y, (∀ w ∈ T.path v, cell w x = cell w y) → (mark v x ↔ mark v y))
    (v : V) (x : X) : T.markE cell mark v (fun w => cellE cell w x) ↔ mark v x := by
  constructor
  · rintro ⟨x', hm, hz⟩
    refine (hloc v x x' fun w hw => ?_).2 hm
    have := hz w hw
    simp only [cellE, Sigma.mk.injEq, heq_eq_eq, true_and] at this
    exact this
  · intro hm
    exact ⟨x, hm, fun w _ => rfl⟩

/-- **Tree search on a promise with vertex-dependent cell outputs**: cost exactly `C_ρ`. -/
theorem hasDualOn_treeSearch_recCost {ρ : V} (hρ : T.IsRoot ρ) {t : V → ℝ} (ht : ∀ v, 0 < t v)
    (read : X → ι → σ) (cell : ∀ v, X → Γ v) (mark : V → X → Prop)
    [DecidablePred fun x : X => ∃ v, mark v x]
    (hcell : ∀ v, HasDualOn read (cell v) (t v))
    (hloc : ∀ v x y, (∀ w ∈ T.path v, cell w x = cell w y) → (mark v x ↔ mark v y)) :
    HasDualOn read (fun x => decide (∃ v, mark v x)) (T.recCost t ρ) := by
  have hW := T.hasWeightedDual_treeSearch_recCost ht hρ (T.markE cell mark)
    (fun v z z' h => T.markE_local cell mark v z z' h)
  obtain ⟨K, hK, Q, hQ⟩ := hW
  have hR : ∀ v, HasDualOn read (cellE cell v) (t v) := fun v =>
    (hcell v).ofKer fun x y => by simp [cellE]
  refine (hasDualOn_sharedFunOn Q hQ hR).ofEq fun x => ?_
  rw [sharedFunOn_apply, treeSearch]
  exact decide_eq_decide.2 (exists_congr fun v => T.markE_table cell mark hloc v x)

/-- The common-output convenience wrapper. -/
theorem hasDualOn_treeSearch_recCost' {E : Type} [Fintype E] [DecidableEq E] {ρ : V}
    (hρ : T.IsRoot ρ) {t : V → ℝ} (ht : ∀ v, 0 < t v) (read : X → ι → σ) (cell : V → X → E)
    (mark : V → X → Prop) [DecidablePred fun x : X => ∃ v, mark v x]
    (hcell : ∀ v, HasDualOn read (cell v) (t v))
    (hloc : ∀ v x y, (∀ w ∈ T.path v, cell w x = cell w y) → (mark v x ↔ mark v y)) :
    HasDualOn read (fun x => decide (∃ v, mark v x)) (T.recCost t ρ) :=
  T.hasDualOn_treeSearch_recCost (Γ := fun _ => E) hρ ht read cell mark hcell hloc

/-- The total-input specialization `X = ι → σ`, `read = id`. -/
theorem hasDual_treeSearch_recCost [Fintype σ] {E : Type} [Fintype E] [DecidableEq E] {ρ : V}
    (hρ : T.IsRoot ρ) {t : V → ℝ} (ht : ∀ v, 0 < t v) (cell : V → (ι → σ) → E)
    (mark : V → (ι → σ) → Prop) [DecidablePred fun x : ι → σ => ∃ v, mark v x]
    (hcell : ∀ v, HasDual (cell v) (t v))
    (hloc : ∀ v x y, (∀ w ∈ T.path v, cell w x = cell w y) → (mark v x ↔ mark v y)) :
    HasDual (fun x : ι → σ => decide (∃ v, mark v x)) (T.recCost t ρ) :=
  HasDual.of_hasDualOn_id (T.hasDualOn_treeSearch_recCost' hρ ht id cell mark
    (fun v => (hcell v).hasDualOn) hloc)

end AncTree

end QuantumQueryComplexity
