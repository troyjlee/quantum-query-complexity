import QuantumQueryComplexity.Dual
set_option linter.style.header false

/-!
# Learning-graph flows

A *learning graph* (Belovs, arXiv:1105.4024) for a decision problem
`f : (ι → σ) → Bool` lives on the vertex set `Finset ι` — the set of
coordinates loaded so far — with edges `e = (S, j)` meaning "query `j` on top
of `S`".  Its data is an input-independent weight on the edges and, for every
positive input, a unit flow from `∅` to sets containing a 1-certificate.

Here the weight is carried as a *half-weight* `ω e = √(w e)`, which is the
quantity the dual vectors actually use, and the flow `p` is required to
satisfy conservation away from `∅` and the sinks.  Nothing requires the flow
to be nonnegative.

`QuantumQueryComplexity/LearningGraph/Cut.lean` proves the cut identity that makes a flow
a dual constraint, and `QuantumQueryComplexity/LearningGraph/Dual.lean` converts the whole
package into a feasible `DualPair` of cost `√(𝒞₀ 𝒞₁)` — the learning-graph
complexity theorem, with no span programs anywhere.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [DecidableEq σ]

/-- The record of what has been seen after loading the set `S` on input `x`:
`some (x i)` on `S`, `none` elsewhere.  Two inputs produce the same record
exactly when they agree on `S`. -/
def setMask (x : ι → σ) (S : Finset ι) : ι → Option σ :=
  fun i => if i ∈ S then some (x i) else none

lemma setMask_eq_iff {x y : ι → σ} {S : Finset ι} :
    setMask x S = setMask y S ↔ ∀ i ∈ S, x i = y i := by
  constructor
  · intro h i hi
    have hi' := congrFun h i
    simp only [setMask, if_pos hi, Option.some.injEq] at hi'
    exact hi'
  · intro h
    funext i
    simp only [setMask]
    by_cases hi : i ∈ S
    · rw [if_pos hi, if_pos hi, h i hi]
    · rw [if_neg hi, if_neg hi]

/-- A learning-graph flow for `f`: half-weights `ω` on the edges `(S, j)`
(input-independent; edges with `j ∈ S` should carry `ω = 0`), a flow `p x`
for every positive input `x`, and a sink predicate.

* `supp` — the flow lives on weighted edges;
* `source` — unit flow leaves `∅`;
* `conserve` — flow is conserved at every nonempty non-sink vertex;
* `sinkCert` — a sink certifies the positive input: no negative input agrees
  with `x` there.

The flow at negative inputs and the values of `sink` there are irrelevant. -/
structure LGFlow {ι : Type*} [Fintype ι] [DecidableEq ι] {σ : Type*}
    [DecidableEq σ] (f : (ι → σ) → Bool) where
  /-- The half-weight `√(w e)` of an edge. -/
  ω : Finset ι × ι → ℝ
  /-- The unit flow routed by a positive input. -/
  p : (ι → σ) → Finset ι × ι → ℝ
  /-- The vertices at which the flow of a positive input may terminate. -/
  sink : (ι → σ) → Finset ι → Prop
  /-- The flow only uses weighted edges. -/
  supp : ∀ (x : ι → σ) (e : Finset ι × ι), f x = true → p x e ≠ 0 → ω e ≠ 0
  /-- Unit flow out of the empty set. -/
  source : ∀ x : ι → σ, f x = true → (∑ j : ι, p x (∅, j)) = 1
  /-- Conservation at every nonempty vertex that is not a sink. -/
  conserve : ∀ x : ι → σ, f x = true → ∀ S : Finset ι, S ≠ ∅ → ¬ sink x S →
    (∑ j ∈ Sᶜ, p x (S, j)) = ∑ j ∈ S, p x (S.erase j, j)
  /-- A sink contains a 1-certificate: every negative input differs there. -/
  sinkCert : ∀ x y : ι → σ, f x = true → f y = false →
    ∀ S : Finset ι, sink x S → ∃ i ∈ S, x i ≠ y i

end QuantumQueryComplexity
