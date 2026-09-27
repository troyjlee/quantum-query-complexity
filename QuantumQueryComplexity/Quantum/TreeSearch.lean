import QuantumQueryComplexity.Promise.TreeSearch
import QuantumQueryComplexity.Quantum.UniformHasDual

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Tree search: the bounded-error quantum endpoints

A cross-stream integration module (classical dual construction + `Quantum/UniformHasDual`);
it is **not** part of `QuantumQueryComplexity.Quantum` and is built explicitly.

* `qQueryOn_third_treeSearch` — `Q_{1/3}(F) ≤ 8192·(1 + C_ρ)`;
* `qQueryOn_third_treeSearch_hom` — the homogeneous form `Q_{1/3}(F) ≤ 16384·C_ρ`: if `F` is
  constant on the promise (an empty promise included) a constant algorithm uses no queries;
  otherwise the certificate itself forces `1 ≤ C_ρ` (`HasDualOn.one_le_of_ne`) and the additive
  one is absorbed;
* `qQuery_third_treeSearch`, `qQuery_third_treeSearch_hom` — the total-input forms.

These are decision bounds with bounded error; nothing is claimed about finding a marked
vertex.
-/

namespace QuantumQueryComplexity

variable {ι σ X : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype X]
  [DecidableEq X]

/-- A function constant on the (possibly empty) promise needs no queries. -/
lemma qQueryOn_eq_zero_of_const {O : Type} [DecidableEq O] [Nonempty O] (read : X → ι → σ)
    {f : X → O} (hf : ∀ x y, f x = f y) {ε : ℝ} (hε : 0 ≤ ε) : qQueryOn read f ε = 0 := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact qQueryOn_const_eq_zero read (c := Classical.arbitrary O) (fun x => (hX.false x).elim) hε
  · exact qQueryOn_const_eq_zero read (c := f x₀) (fun x => hf x x₀) hε

/-- **The homogeneous absorption**: a certificate of cost `c` gives `Q_{1/3} ≤ 16384·c`. -/
theorem qQueryOn_third_le_of_hasDualOn_hom {O : Type} [DecidableEq O] [Nonempty O]
    {read : X → ι → σ} {f : X → O} {c : ℝ} (h : HasDualOn read f c) (hc : 0 ≤ c) :
    (qQueryOn read f (1 / 3) : ℝ) ≤ 16384 * c := by
  by_cases hconst : ∀ x y, f x = f y
  · rw [qQueryOn_eq_zero_of_const read hconst (by norm_num)]
    simp only [Nat.cast_zero]
    positivity
  · push Not at hconst
    obtain ⟨x, y, hxy⟩ := hconst
    have h1 := h.one_le_of_ne hxy
    have h2 := qQueryOn_third_le_of_hasDualOn_uniform h hc
    rw [uniformExtractionConstant] at h2
    linarith

namespace AncTree

variable {V : Type} [DecidableEq V] [Fintype V] (T : AncTree V)
variable {Γ : V → Type} [∀ v, Fintype (Γ v)] [∀ v, DecidableEq (Γ v)]

/-- **`Q_{1/3}(F) ≤ 8192·(1 + C_ρ)`** for the tree-search decision on a promise. -/
theorem qQueryOn_third_treeSearch {ρ : V} (hρ : T.IsRoot ρ) {t : V → ℝ} (ht : ∀ v, 0 < t v)
    (read : X → ι → σ) (cell : ∀ v, X → Γ v) (mark : V → X → Prop)
    [DecidablePred fun x : X => ∃ v, mark v x] (hcell : ∀ v, HasDualOn read (cell v) (t v))
    (hloc : ∀ v x y, (∀ w ∈ T.path v, cell w x = cell w y) → (mark v x ↔ mark v y)) :
    (qQueryOn read (fun x => decide (∃ v, mark v x)) (1 / 3) : ℝ)
      ≤ 8192 * (1 + T.recCost t ρ) := by
  have h := qQueryOn_third_le_of_hasDualOn_uniform
    (T.hasDualOn_treeSearch_recCost hρ ht read cell mark hcell hloc) (T.recCost_pos ht ρ).le
  rwa [uniformExtractionConstant] at h

/-- **`Q_{1/3}(F) ≤ 16384·C_ρ`**, the paper's homogeneous form. -/
theorem qQueryOn_third_treeSearch_hom {ρ : V} (hρ : T.IsRoot ρ) {t : V → ℝ} (ht : ∀ v, 0 < t v)
    (read : X → ι → σ) (cell : ∀ v, X → Γ v) (mark : V → X → Prop)
    [DecidablePred fun x : X => ∃ v, mark v x] (hcell : ∀ v, HasDualOn read (cell v) (t v))
    (hloc : ∀ v x y, (∀ w ∈ T.path v, cell w x = cell w y) → (mark v x ↔ mark v y)) :
    (qQueryOn read (fun x => decide (∃ v, mark v x)) (1 / 3) : ℝ) ≤ 16384 * T.recCost t ρ :=
  qQueryOn_third_le_of_hasDualOn_hom
    (T.hasDualOn_treeSearch_recCost hρ ht read cell mark hcell hloc) (T.recCost_pos ht ρ).le

/-- The total-input form, `read = id`. -/
theorem qQuery_third_treeSearch {E : Type} [Fintype E] [DecidableEq E] {ρ : V} (hρ : T.IsRoot ρ)
    {t : V → ℝ} (ht : ∀ v, 0 < t v) (cell : V → (ι → σ) → E) (mark : V → (ι → σ) → Prop)
    [DecidablePred fun x : ι → σ => ∃ v, mark v x] (hcell : ∀ v, HasDual (cell v) (t v))
    (hloc : ∀ v x y, (∀ w ∈ T.path v, cell w x = cell w y) → (mark v x ↔ mark v y)) :
    (qQuery (fun x : ι → σ => decide (∃ v, mark v x)) (1 / 3) : ℝ)
      ≤ 8192 * (1 + T.recCost t ρ) :=
  T.qQueryOn_third_treeSearch (Γ := fun _ => E) hρ ht id cell mark
    (fun v => (hcell v).hasDualOn) hloc

theorem qQuery_third_treeSearch_hom {E : Type} [Fintype E] [DecidableEq E] {ρ : V}
    (hρ : T.IsRoot ρ) {t : V → ℝ} (ht : ∀ v, 0 < t v) (cell : V → (ι → σ) → E)
    (mark : V → (ι → σ) → Prop) [DecidablePred fun x : ι → σ => ∃ v, mark v x]
    (hcell : ∀ v, HasDual (cell v) (t v))
    (hloc : ∀ v x y, (∀ w ∈ T.path v, cell w x = cell w y) → (mark v x ↔ mark v y)) :
    (qQuery (fun x : ι → σ => decide (∃ v, mark v x)) (1 / 3) : ℝ)
      ≤ 16384 * T.recCost t ρ :=
  T.qQueryOn_third_treeSearch_hom (Γ := fun _ => E) hρ ht id cell mark
    (fun v => (hcell v).hasDualOn) hloc

end AncTree

end QuantumQueryComplexity
