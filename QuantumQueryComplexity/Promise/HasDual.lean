import QuantumQueryComplexity.Promise.Defs
import QuantumQueryComplexity.HasDual
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# Bundled dual solutions on a promise domain

`QuantumQueryComplexity/HasDual.lean` hides the dimension type of a dual solution for a
*total* function; a divide-and-conquer recursion whose subproblems live on
input-dependent promises needs the same service on `DualPairOn`.  This file
is that layer, plus the two structural moves every promise construction
needs:

* `DualPairOn.ofKer` — the constraint sees the output only through the
  equality pattern `f x = f y`, so a solution for `f` is a solution for any
  `f'` with the same kernel, *at the same vectors*.  This is what lets a
  descriptor chain be repackaged as a transcript without paying anything.
* `HasDual.restrictToOn` — a total solution restricts to a promise for free
  (`DualPair.restrictTo`), which is how the windowed element-distinctness
  duals of `ED/*` become the leaves of the LDS recursion.

Cost-`0` solutions exist exactly for functions that are constant on the
promise (`hasDualOn_of_const`): on such a promise the constraint's right-hand
side is identically `0`, so the zero vectors are feasible.  That is the
"value determined by the transcript" case of descriptor composition.
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} [DecidableEq σ]
variable {X : Type} [Fintype X] [DecidableEq X]
variable {O O' : Type} [DecidableEq O] [DecidableEq O']

/-! ## Recoding the output -/

namespace DualPairOn

variable {K : Type} [Fintype K] {read : X → ι → σ} {f : X → O} {f' : X → O'}

/-- **Output recoding.**  A dual solution for `f` is a dual solution for any
`f'` with the same kernel on the promise — same vectors, same cost. -/
def ofKer (P : DualPairOn read K f) (h : ∀ x y, f x = f y ↔ f' x = f' y) :
    DualPairOn read K f' where
  u := P.u
  v := P.v
  constraint x y := by
    rw [P.constraint x y]
    by_cases hxy : f x = f y
    · rw [if_pos hxy, if_pos ((h x y).mp hxy)]
    · rw [if_neg hxy, if_neg fun hc => hxy ((h x y).mpr hc)]

@[simp] lemma ofKer_u (P : DualPairOn read K f)
    (h : ∀ x y, f x = f y ↔ f' x = f' y) : (P.ofKer h).u = P.u := rfl

@[simp] lemma ofKer_v (P : DualPairOn read K f)
    (h : ∀ x y, f x = f y ↔ f' x = f' y) : (P.ofKer h).v = P.v := rfl

lemma ofKer_isCostLe {c : ℝ} {P : DualPairOn read K f}
    {h : ∀ x y, f x = f y ↔ f' x = f' y} (hP : P.IsCostLe c) :
    (P.ofKer h).IsCostLe c := hP

/-- **Pulling a promise solution back along a map of promises.**  Every
sub-promise — in particular every fiber of a descriptor — inherits the
ambient solution at the same cost, since the constraint at `(y, y')` *is* the
constraint at `(e y, e y')`. -/
def comap {Y : Type} [Fintype Y] (P : DualPairOn read K f) (e : Y → X) :
    DualPairOn (fun y => read (e y)) K (fun y => f (e y)) where
  u y := P.u (e y)
  v y := P.v (e y)
  constraint y y' := P.constraint (e y) (e y')

/-- The zero solution is feasible for a function that is constant on the
promise. -/
def const (read : X → ι → σ) (f : X → O) (hf : ∀ x y, f x = f y) :
    DualPairOn read Empty f where
  u _ _ _ := 0
  v _ _ _ := 0
  constraint x y := by simp [hf x y]

lemma const_isCostLe {read : X → ι → σ} {f : X → O} (hf : ∀ x y, f x = f y) :
    (const read f hf).IsCostLe 0 := by
  constructor <;> intro x <;> simp [const]

end DualPairOn

/-! ## The bundled predicate -/

/-- `f` has a feasible dual solution of cost at most `c` on the promise
domain `read`. -/
def HasDualOn {ι : Type} [Fintype ι] {σ : Type} [DecidableEq σ] {X : Type}
    [Fintype X] {O : Type} [DecidableEq O] (read : X → ι → σ) (f : X → O)
    (c : ℝ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (P : DualPairOn read K f), P.IsCostLe c

variable {read : X → ι → σ} {f : X → O} {f' : X → O'} {c d : ℝ}

lemma hasDualOn_of_dualPairOn {K : Type} [Fintype K] (P : DualPairOn read K f)
    (h : P.IsCostLe c) : HasDualOn read f c := ⟨K, inferInstance, P, h⟩

lemma HasDualOn.mono (h : HasDualOn read f c) (hcd : c ≤ d) :
    HasDualOn read f d := by
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P, hP.mono hcd⟩

/-- **Weak duality on a promise, bundled.** -/
theorem advPMOn_le_of_hasDualOn (hc : 0 ≤ c) (h : HasDualOn read f c) :
    advPMOn read f ≤ c := by
  obtain ⟨K, hK, P, hP⟩ := h
  exact advPMOn_le_of_dualPairOn P hc hP

/-! ## Total solutions as promise solutions

A total function is the promise problem over `read = id`, and a `DualPair`
is literally a `DualPairOn` there — the constraint's mask `id x i = id y i`
is definitionally `x i = y i`. -/

section Total

variable [Fintype σ] {g : (ι → σ) → O}

/-- A total dual solution, read as a promise solution over `read = id`. -/
def DualPair.toOn {K : Type} [Fintype K] (P : DualPair K g) :
    DualPairOn (id : (ι → σ) → ι → σ) K g where
  u := P.u
  v := P.v
  constraint := P.constraint

lemma DualPair.toOn_isCostLe {K : Type} [Fintype K] (P : DualPair K g)
    (h : P.IsCostLe c) : P.toOn.IsCostLe c := h

/-- **A total bundled dual is a bundled promise dual over `read = id`.** -/
lemma HasDual.hasDualOn (h : HasDual g c) :
    HasDualOn (id : (ι → σ) → ι → σ) g c := by
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P.toOn, hP⟩

/-- The other direction: a promise solution over `read = id` is a total
solution.  Same vectors, same constraint. -/
def DualPairOn.toTotal {K : Type} [Fintype K]
    (P : DualPairOn (id : (ι → σ) → ι → σ) K g) : DualPair K g where
  u := P.u
  v := P.v
  constraint := P.constraint

lemma DualPairOn.toTotal_isCostLe {K : Type} [Fintype K]
    {P : DualPairOn (id : (ι → σ) → ι → σ) K g} (h : P.IsCostLe c) :
    P.toTotal.IsCostLe c := h

/-- **The converse of `HasDual.hasDualOn`.**  With both directions available
the promise-side calculus — descriptor composition in particular — can be run
inside a total development and handed back as a `HasDual`. -/
theorem HasDual.of_hasDualOn_id (h : HasDualOn (id : (ι → σ) → ι → σ) g c) :
    HasDual g c := by
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P.toTotal, DualPairOn.toTotal_isCostLe hP⟩

end Total

/-- Recoding the output of a bundled solution. -/
lemma HasDualOn.ofKer (h : HasDualOn read f c)
    (hker : ∀ x y, f x = f y ↔ f' x = f' y) : HasDualOn read f' c := by
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P.ofKer hker, DualPairOn.ofKer_isCostLe hP⟩

/-- Replacing the function by a pointwise equal one. -/
lemma HasDualOn.ofEq (h : HasDualOn read f c) {g : X → O}
    (hg : ∀ x, f x = g x) : HasDualOn read g c :=
  h.ofKer fun x y => by rw [hg x, hg y]

/-- Restricting a bundled promise solution to a sub-promise, at the same
cost. -/
theorem HasDualOn.comap {Y : Type} [Fintype Y] (h : HasDualOn read f c)
    (e : Y → X) : HasDualOn (fun y => read (e y)) (fun y => f (e y)) c := by
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P.comap e, fun y => hP.1 (e y), fun y => hP.2 (e y)⟩

/-- A function constant on the promise costs nothing. -/
lemma hasDualOn_of_const (read : X → ι → σ) {f : X → O} (hf : ∀ x y, f x = f y) :
    HasDualOn read f 0 :=
  hasDualOn_of_dualPairOn (DualPairOn.const read f hf)
    (DualPairOn.const_isCostLe hf)

/-! ## Moving between query index types -/

namespace DualPairOn

variable {K : Type} [Fintype K] {read : X → ι → σ} {f : X → O}

/-- **A solution that only queries a sub-family of coordinates.**  If the
promise is observed through `ι' ↪ ι` — the arena of a divide-and-conquer node
is such a sub-family of the word's positions — a solution written in arena
coordinates becomes one in the ambient coordinates, at the same cost: the
`ℓ²` mass moves to the image of the injection without accumulating
(`spread`). -/
noncomputable def pullbackCoord {ι' : Type} [Fintype ι'] [DecidableEq ι']
    {e : ι' → ι} (he : Function.Injective e)
    (P : DualPairOn (fun x k => read x (e k)) K f) : DualPairOn read K f where
  u x i := fun k => spread e (fun j => P.u x j k) i
  v y i := fun k => spread e (fun j => P.v y j k) i
  constraint x y := by
    set T : ι' → ℝ := fun j => ∑ k : K, P.u x j k * P.v y j k with hT
    have hpt : ∀ i : ι,
        (∑ k : K, spread e (fun j => P.u x j k) i
            * spread e (fun j => P.v y j k) i) = spread e T i := by
      intro i
      rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
        spread_mul_spread he i (fun j => P.u x j k) (fun j => P.v y j k)]
      simp only [spread, hT]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    simp only [hpt]
    have hmask : ∀ i : ι,
        (if read x i = read y i then (0 : ℝ) else spread e T i)
        = spread e (fun j => if read x (e j) = read y (e j) then (0 : ℝ)
            else T j) i := by
      intro i
      by_cases h : ∃ j, e j = i
      · obtain ⟨j₀, hj⟩ := h
        rw [spread_eq_of_mem he hj, spread_eq_of_mem he hj, hj]
      · push_neg at h
        rw [spread_eq_zero h, spread_eq_zero h, ite_self]
    simp only [hmask]
    rw [sum_spread he]
    exact P.constraint x y

theorem pullbackCoord_isCostLe {ι' : Type} [Fintype ι'] [DecidableEq ι']
    {e : ι' → ι} (he : Function.Injective e)
    (P : DualPairOn (fun x k => read x (e k)) K f) {c : ℝ} (hP : P.IsCostLe c) :
    (P.pullbackCoord he).IsCostLe c := by
  constructor
  · intro x
    have h : ∀ i : ι,
        (∑ k : K, (P.pullbackCoord he).u x i k * (P.pullbackCoord he).u x i k)
          = spread e (fun j => ∑ k : K, P.u x j k * P.u x j k) i := by
      intro i
      show (∑ k : K, spread e (fun j => P.u x j k) i
          * spread e (fun j => P.u x j k) i) = _
      rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
        spread_mul_spread he i (fun j => P.u x j k) (fun j => P.u x j k)]
      simp only [spread]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    simp only [h]
    rw [sum_spread he]
    exact hP.1 x
  · intro y
    have h : ∀ i : ι,
        (∑ k : K, (P.pullbackCoord he).v y i k * (P.pullbackCoord he).v y i k)
          = spread e (fun j => ∑ k : K, P.v y j k * P.v y j k) i := by
      intro i
      show (∑ k : K, spread e (fun j => P.v y j k) i
          * spread e (fun j => P.v y j k) i) = _
      rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
        spread_mul_spread he i (fun j => P.v y j k) (fun j => P.v y j k)]
      simp only [spread]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    simp only [h]
    rw [sum_spread he]
    exact hP.2 y

end DualPairOn

/-- **Arena coordinates, bundled**: a promise solution written in the
coordinates of a sub-family costs the same in the ambient coordinates. -/
theorem HasDualOn.pullbackCoord {ι' : Type} [Fintype ι'] [DecidableEq ι']
    {e : ι' → ι} (he : Function.Injective e)
    (h : HasDualOn (fun x k => read x (e k)) f c) : HasDualOn read f c := by
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P.pullbackCoord he, DualPairOn.pullbackCoord_isCostLe he P hP⟩

/-! ## Restricting a total solution -/

/-- **A total dual solution restricted to a promise domain**, bundled: the
vectors are unchanged, so the cost is inherited.  This is how the windowed
`ED` duals enter a promise-relativized recursion. -/
theorem HasDual.restrictToOn [Fintype σ] {g : (ι → σ) → O} (h : HasDual g c)
    (read : X → ι → σ) : HasDualOn read (fun x => g (read x)) c := by
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P.restrictTo read, fun x => hP.1 (read x), fun x => hP.2 (read x)⟩

end QuantumQueryComplexity
