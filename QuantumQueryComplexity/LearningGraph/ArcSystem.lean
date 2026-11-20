import QuantumQueryComplexity.LearningGraph.Dual
import QuantumQueryComplexity.Promise.HasDual
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Arc-system duals

A dual adversary solution for a Boolean function on a promise, built from **arcs** with
input-dependent states and small blocks. This generalizes the learning-graph construction
(`LGFlow.hasDual`): there the state of an input on an edge `(S, j)` is its assignment on `S` and
each edge carries one scalar; here each arc `e` has

* the index `load e` it queries,
* a state `state e x` of the input `x` on `e`, in an arbitrary finite type `K`, and
* an amplitude vector `amp e x : C → ℝ` with finitely many components.

Two inputs interact on an arc only when the arc queries a position where they differ and their
states on it agree; their interaction is the inner product of their amplitude vectors. An arc
system is **feasible** (`ArcSystem.Feasible`) when, for every positive input `x` and every
negative input `y`, these interactions sum to `1` (`ArcSystem.cross x y = 1`). This is a
hypothesis, not a consequence of the structure: zero amplitudes would otherwise give a "dual" for
every function.

`ArcSystem.hasDualOn`: a feasible arc system with `ArcSystem.cost x = ∑_e ∑_c (amp e x c)² ≤ b`
for every input gives `HasDualOn read f b`. The dual vectors live on `Bool × A × K × C` (a side
bit, an arc, a state and a component): `u x` uses the side `!(f x)` and `v y` the side `f y`, so
pairings of inputs with equal outputs vanish, and the pairing of a negative with a positive input
is the cross sum read backwards (`cross_comm`). The cost is a sum of squares over the components,
which is what `DualPairOn.IsCostLe` measures (not the sup norm Lean puts on `C → ℝ`).
`cost_le_sum_stages` bounds the cost stage by stage over any partition of the arcs.

`LGFlow.toArcSystem` and `LGFlow.hasDual_of_arcSystem` re-derive the learning-graph complexity
theorem from `ArcSystem.hasDualOn`, with the same statement as `LGFlow.hasDual`: arcs are the
edges `(S, j)`, the state is `setMask x S`, there is one component, the amplitude is
`LGFlow.scal λ x e`, feasibility is the cut identity `LGFlow.sum_cut`, and
`HasDual.of_hasDualOn_id` returns to the total function.

The intended application is the k-distinctness dual of Belovs, *Learning-graph-based quantum
algorithm for k-distinctness* (FOCS 2012), Section 6. A learning-graph flow has one component per
arc, its state is the whole restriction `setMask x S`, and the amplitude `λ⁻¹ ω e` of a negative
input does not depend on the input (signs can occur, but they are the same for every negative
input). The k-distinctness arcs need more: their states are assignments that hide some values,
the amplitudes of a negative input depend on that input, signs included, and the rank-2 blocks
need two components.
-/

namespace QuantumQueryComplexity

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} [DecidableEq σ]
variable {X : Type} [Fintype X]

/-- **An arc system** for a Boolean function `f` on the promise `read : X → ι → σ`, with arcs
`A`, states `K` and amplitude components `C`. -/
structure ArcSystem (read : X → ι → σ) (f : X → Bool) (A K C : Type) where
  /-- The index an arc queries. -/
  load : A → ι
  /-- The state of an input on an arc. -/
  state : A → X → K
  /-- The amplitude vector of an input on an arc. -/
  amp : A → X → C → ℝ

namespace ArcSystem

variable {read : X → ι → σ} {f : X → Bool} {A K C : Type}
variable [Fintype A] [Fintype K] [DecidableEq K] [Fintype C]

/-- **The cross sum** of two inputs: over the arcs that query a position where they differ and on
which their states agree, the inner products of their amplitude vectors. -/
def cross (S : ArcSystem read f A K C) (x y : X) : ℝ :=
  ∑ e : A, if read x (S.load e) = read y (S.load e) then 0
    else if S.state e x = S.state e y then ∑ c : C, S.amp e x c * S.amp e y c else 0

/-- **Feasibility**: every positive input and every negative input have cross sum `1`. -/
def Feasible (S : ArcSystem read f A K C) : Prop :=
  ∀ x y : X, f x = true → f y = false → S.cross x y = 1

/-- **The cost of an input**: the sum over the arcs and the components of the squared
amplitudes. -/
def cost (S : ArcSystem read f A K C) (x : X) : ℝ :=
  ∑ e : A, ∑ c : C, S.amp e x c * S.amp e x c

/-- The cross sum is symmetric. -/
lemma cross_comm (S : ArcSystem read f A K C) (x y : X) : S.cross x y = S.cross y x := by
  unfold cross
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h1 : read x (S.load e) = read y (S.load e)
  · simp [h1]
  · have h1' : ¬ read y (S.load e) = read x (S.load e) := fun h => h1 h.symm
    by_cases h2 : S.state e x = S.state e y
    · simp [h1, h1', h2, mul_comm]
    · have h2' : ¬ S.state e y = S.state e x := fun h => h2 h.symm
      simp [h1, h1', h2, h2']

/-- The dual vector of `x` on the side `b`, at the query index `i` and the coordinate
`(side, arc, state, component)`. -/
def vec (S : ArcSystem read f A K C) (b : Bool) (x : X) (i : ι) (k : Bool × A × K × C) : ℝ :=
  if k.1 = b ∧ i = S.load k.2.1 ∧ k.2.2.1 = S.state k.2.1 x then S.amp k.2.1 x k.2.2.2 else 0

/-- The pairing of two dual vectors at one query index: the sides must agree, and then each arc
loading that index contributes the inner product of the amplitude vectors when the states
agree. -/
lemma sum_vec_mul_vec (S : ArcSystem read f A K C) (b b' : Bool) (x y : X) (i : ι) :
    (∑ k : Bool × A × K × C, S.vec b x i k * S.vec b' y i k)
      = ∑ e : A, if b = b' ∧ i = S.load e ∧ S.state e x = S.state e y then
          ∑ c : C, S.amp e x c * S.amp e y c else 0 := by
  have hpt : ∀ k : Bool × A × K × C, S.vec b x i k * S.vec b' y i k
      = if k.1 = b then (if k.2.2.1 = S.state k.2.1 x then
          (if b = b' ∧ i = S.load k.2.1 ∧ S.state k.2.1 x = S.state k.2.1 y then
            S.amp k.2.1 x k.2.2.2 * S.amp k.2.1 y k.2.2.2 else 0) else 0) else 0 := by
    rintro ⟨t, e, s, c⟩
    simp only [vec]
    by_cases ht : t = b <;> by_cases hb : b = b' <;> by_cases hi : i = S.load e <;>
      by_cases hs : s = S.state e x <;> by_cases hst : S.state e x = S.state e y <;>
      simp_all
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single b fun t ht => by simp [hpt, ht],
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Fintype.sum_prod_type,
    Fintype.sum_eq_single (S.state e x) fun s hs => by simp [hpt, hs]]
  simp only [hpt, ite_true]
  split_ifs <;> simp

/-- The constraint sum of the dual vectors on equal sides is the cross sum. -/
lemma constraint_sum_eq_cross (S : ArcSystem read f A K C) (b : Bool) (x y : X) :
    (∑ i : ι, if read x i = read y i then 0
      else ∑ k : Bool × A × K × C, S.vec b x i k * S.vec b y i k) = S.cross x y := by
  simp only [sum_vec_mul_vec, true_and]
  have hpush : ∀ i : ι, (if read x i = read y i then (0 : ℝ) else ∑ e : A,
      if i = S.load e ∧ S.state e x = S.state e y then ∑ c : C, S.amp e x c * S.amp e y c
        else 0)
      = ∑ e : A, if i = S.load e then (if read x (S.load e) = read y (S.load e) then 0 else
        if S.state e x = S.state e y then ∑ c : C, S.amp e x c * S.amp e y c else 0)
        else 0 := by
    intro i
    by_cases hxy : read x i = read y i
    · simp only [hxy, ite_true]
      refine (Finset.sum_eq_zero fun e _ => ?_).symm
      by_cases hi : i = S.load e
      · rw [hi] at hxy
        simp [hi, hxy]
      · simp [hi]
    · simp only [hxy, ite_false]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases hi : i = S.load e
      · rw [hi] at hxy
        simp [hi, hxy]
      · simp [hi]
  rw [Finset.sum_congr rfl fun i _ => hpush i, Finset.sum_comm]
  unfold cross
  refine Finset.sum_congr rfl fun e _ => ?_
  simp

/-- The constraint sum of the dual vectors on different sides vanishes. -/
lemma constraint_sum_eq_zero (S : ArcSystem read f A K C) {b b' : Bool} (hb : b ≠ b')
    (x y : X) :
    (∑ i : ι, if read x i = read y i then 0
      else ∑ k : Bool × A × K × C, S.vec b x i k * S.vec b' y i k) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  simp [sum_vec_mul_vec, hb]

/-- The cost sum of a dual vector is the cost of the input, on either side. -/
lemma sum_sum_vec_sq (S : ArcSystem read f A K C) (b : Bool) (x : X) :
    (∑ i : ι, ∑ k : Bool × A × K × C, S.vec b x i k * S.vec b x i k) = S.cost x := by
  simp only [sum_vec_mul_vec, true_and, and_true]
  rw [Finset.sum_comm]
  unfold cost
  refine Finset.sum_congr rfl fun e _ => ?_
  simp

/-- **The dual solution of a feasible arc system.** -/
def dualPairOn (S : ArcSystem read f A K C) (h : S.Feasible) :
    DualPairOn read (Bool × A × K × C) f where
  u x := S.vec (!(f x)) x
  v y := S.vec (f y) y
  constraint x y := by
    cases hfx : f x <;> cases hfy : f y
    · simp only [ite_true]
      exact S.constraint_sum_eq_zero (by decide) x y
    · simp only [Bool.false_eq_true, ite_false]
      show (∑ i : ι, if read x i = read y i then 0
        else ∑ k : Bool × A × K × C, S.vec (!false) x i k * S.vec true y i k) = 1
      rw [show (!false) = true from rfl, S.constraint_sum_eq_cross, S.cross_comm]
      exact h y x hfy hfx
    · simp only [Bool.true_eq_false, ite_false]
      show (∑ i : ι, if read x i = read y i then 0
        else ∑ k : Bool × A × K × C, S.vec (!true) x i k * S.vec false y i k) = 1
      rw [show (!true) = false from rfl, S.constraint_sum_eq_cross]
      exact h x y hfx hfy
    · simp only [ite_true]
      exact S.constraint_sum_eq_zero (by decide) x y

/-- A bound `b` on the cost of every input bounds the cost of both families of dual vectors of an
arc system. -/
lemma dualPairOn_isCostLe (S : ArcSystem read f A K C) (h : S.Feasible) {b : ℝ}
    (hb : ∀ x, S.cost x ≤ b) : (S.dualPairOn h).IsCostLe b :=
  ⟨fun x => (S.sum_sum_vec_sq (!(f x)) x).le.trans (hb x),
    fun x => (S.sum_sum_vec_sq (f x) x).le.trans (hb x)⟩

/-- **The arc-system dual**: a feasible arc system in which every input has cost at most `b`
gives a dual adversary solution of cost at most `b` on the promise. -/
theorem hasDualOn (S : ArcSystem read f A K C) (h : S.Feasible) {b : ℝ}
    (hb : ∀ x, S.cost x ≤ b) : HasDualOn read f b :=
  ⟨Bool × A × K × C, inferInstance, S.dualPairOn h, S.dualPairOn_isCostLe h hb⟩

/-- **The cost stage by stage**: for any partition of the arcs into stages, an input whose cost
on each stage `t` is at most `bnd t` has cost at most `∑_t bnd t`. -/
theorem cost_le_sum_stages (S : ArcSystem read f A K C) {T : Type} [Fintype T] [DecidableEq T]
    (stage : A → T) (bnd : T → ℝ) {x : X}
    (h : ∀ t, (∑ e ∈ univ.filter (fun e => stage e = t), ∑ c : C, S.amp e x c * S.amp e x c)
      ≤ bnd t) :
    S.cost x ≤ ∑ t, bnd t := by
  unfold cost
  rw [← Finset.sum_fiberwise univ stage]
  exact Finset.sum_le_sum fun t _ => h t

end ArcSystem

/-! ## Learning-graph flows as arc systems -/

section LearningGraph

-- Fresh alphabet variable, so that the instance order `[Fintype σ'] [DecidableEq σ']` matches
-- `LGFlow.hasDual` and the two theorems have definitionally equal types.
variable {σ' : Type} [Fintype σ'] [DecidableEq σ'] {g : (ι → σ') → Bool}

/-- **The arc system of a learning-graph flow**: arcs are the edges `(S, j)`, loading `j`; the
state of `x` is its assignment `setMask x S` on `S`; there is one component, carrying the scalar
`LGFlow.scal λ x e`. -/
noncomputable def LGFlow.toArcSystem (L : LGFlow g) (lam : ℝ) :
    ArcSystem (id : (ι → σ') → ι → σ') g (Finset ι × ι) (ι → Option σ') Unit where
  load e := e.2
  state e x := setMask x e.1
  amp e x _ := L.scal lam x e

/-- The arc system of a flow is feasible: its cross sum is the cut sum `LGFlow.sum_cut`. -/
theorem LGFlow.toArcSystem_feasible (L : LGFlow g) {lam : ℝ} (hlam : lam ≠ 0) :
    (L.toArcSystem lam).Feasible := by
  intro x y hx hy
  rw [← L.sum_cut hx hy]
  unfold ArcSystem.cross
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [LGFlow.toArcSystem, id, Finset.univ_unique, Finset.sum_singleton]
  rw [L.scal_mul_scal hlam hx hy e]

/-- The cost of an input in the arc system of a flow: `λ²𝒞₁(x)` if it is positive, `λ⁻²𝒞₀` if
it is negative. -/
theorem LGFlow.toArcSystem_cost (L : LGFlow g) (lam : ℝ) (x : ι → σ') :
    (L.toArcSystem lam).cost x
      = if g x = true then lam ^ 2 * ∑ e : Finset ι × ι, (L.p x e / L.ω e) ^ 2
        else lam⁻¹ ^ 2 * ∑ e : Finset ι × ι, L.ω e ^ 2 := by
  rw [← L.sum_scal_sq lam x]
  unfold ArcSystem.cost
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [LGFlow.toArcSystem, Finset.univ_unique, Finset.sum_singleton]

/-- **The learning-graph complexity theorem through arc systems**: a flow of negative complexity
`𝒞₀` and positive complexity `𝒞₁` gives a dual solution of cost `√(𝒞₀ 𝒞₁)`. Same statement as
`LGFlow.hasDual`, derived from `ArcSystem.hasDualOn` with `λ = (𝒞₀/𝒞₁)^{1/4}`. -/
theorem LGFlow.hasDual_of_arcSystem (L : LGFlow g) {C₀ C₁ : ℝ} (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hω : (∑ e : Finset ι × ι, L.ω e ^ 2) ≤ C₀)
    (hp : ∀ x, g x = true → (∑ e : Finset ι × ι, (L.p x e / L.ω e) ^ 2) ≤ C₁) :
    HasDual g (Real.sqrt (C₀ * C₁)) := by
  set lam := Real.sqrt (Real.sqrt (C₀ / C₁)) with hlam_def
  have hlampos : (0 : ℝ) < lam :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (div_pos hC₀ hC₁))
  have hlamsq : lam ^ 2 = Real.sqrt (C₀ / C₁) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hkey1 : Real.sqrt (C₀ / C₁) * C₁ = Real.sqrt (C₀ * C₁) := by
    rw [show C₀ * C₁ = C₀ / C₁ * C₁ ^ 2 from by field_simp,
      Real.sqrt_mul (div_nonneg hC₀.le hC₁.le), Real.sqrt_sq hC₁.le]
  have hkey2 : Real.sqrt (C₁ / C₀) * C₀ = Real.sqrt (C₀ * C₁) := by
    rw [show C₀ * C₁ = C₁ / C₀ * C₀ ^ 2 from by field_simp,
      Real.sqrt_mul (div_nonneg hC₁.le hC₀.le), Real.sqrt_sq hC₀.le]
  have hlaminv : lam⁻¹ ^ 2 = Real.sqrt (C₁ / C₀) := by
    rw [inv_pow, hlamsq, ← Real.sqrt_inv, inv_div]
  refine HasDual.of_hasDualOn_id
    ((L.toArcSystem lam).hasDualOn (L.toArcSystem_feasible hlampos.ne') fun x => ?_)
  rw [L.toArcSystem_cost lam x]
  by_cases hx : g x = true
  · simp only [hx, ite_true]
    rw [hlamsq, ← hkey1]
    exact mul_le_mul_of_nonneg_left (hp x hx) (Real.sqrt_nonneg _)
  · simp only [hx]
    rw [hlaminv, ← hkey2]
    exact mul_le_mul_of_nonneg_left hω (Real.sqrt_nonneg _)

end LearningGraph

end QuantumQueryComplexity
