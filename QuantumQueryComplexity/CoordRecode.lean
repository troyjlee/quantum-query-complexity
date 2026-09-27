import QuantumQueryComplexity.WeightedDual
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# Recoding letters coordinate by coordinate

`QuantumQueryComplexity/Pullback.lean`'s `alphaMap` recodes the input alphabet along one
injection `σ ↪ σ'`, the same at every coordinate.  Divide-and-conquer needs
the coordinate-dependent version: coordinate `i` recodes along its own
injection `Ψ i`.  Nothing changes in the argument — the constraint sees the
input only through the mask `x i = y i`, and an injection at `i` preserves
that mask — so the vectors, the cost and the *weighted* cost all transfer
verbatim.

The use is `QuantumQueryComplexity/Scan/PerCoord.lean`: a maximum whose value map differs
per coordinate, `max_j m_j (x_j)`, is an ordinary single-map maximum over the
enlarged alphabet `ι × σ` under the tagging injection `Ψ i s = (i, s)`.  The
enlargement is free precisely because the tag is determined by the
coordinate.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ σ' : Type*} [DecidableEq σ] [DecidableEq σ']
variable {O : Type*} [DecidableEq O]
variable {K : Type*} [Fintype K]

/-- The function obtained by recoding each letter along `Ψ`. -/
def coordFun (Ψ : ι → σ → σ') (F : (ι → σ') → O) : (ι → σ) → O :=
  fun x => F fun i => Ψ i (x i)

@[simp] lemma coordFun_apply (Ψ : ι → σ → σ') (F : (ι → σ') → O) (x : ι → σ) :
    coordFun Ψ F x = F (fun i => Ψ i (x i)) := rfl

namespace DualPair

/-- **A dual solution recoded coordinate by coordinate.** -/
def coordRecode {Ψ : ι → σ → σ'} (hΨ : ∀ i, Function.Injective (Ψ i))
    {F : (ι → σ') → O} (P : DualPair K F) : DualPair K (coordFun Ψ F) where
  u x i := P.u (fun j => Ψ j (x j)) i
  v y i := P.v (fun j => Ψ j (y j)) i
  constraint x y := by
    rw [coordFun_apply, coordFun_apply,
      ← P.constraint (fun j => Ψ j (x j)) (fun j => Ψ j (y j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : x i = y i
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg fun hc => h (hΨ i hc)]

@[simp] lemma coordRecode_u {Ψ : ι → σ → σ'} (hΨ : ∀ i, Function.Injective (Ψ i))
    {F : (ι → σ') → O} (P : DualPair K F) (x : ι → σ) (i : ι) :
    (P.coordRecode hΨ).u x i = P.u (fun j => Ψ j (x j)) i := rfl

@[simp] lemma coordRecode_v {Ψ : ι → σ → σ'} (hΨ : ∀ i, Function.Injective (Ψ i))
    {F : (ι → σ') → O} (P : DualPair K F) (y : ι → σ) (i : ι) :
    (P.coordRecode hΨ).v y i = P.v (fun j => Ψ j (y j)) i := rfl

theorem coordRecode_isCostLe {Ψ : ι → σ → σ'}
    (hΨ : ∀ i, Function.Injective (Ψ i)) {F : (ι → σ') → O} {c : ℝ}
    (P : DualPair K F) (hP : P.IsCostLe c) : (P.coordRecode hΨ).IsCostLe c :=
  ⟨fun x => hP.1 _, fun y => hP.2 _⟩

/-- The weighted cost transfers too — the weights are indexed by coordinates,
which the recoding does not touch. -/
theorem coordRecode_isWeightedCostLe {Ψ : ι → σ → σ'}
    (hΨ : ∀ i, Function.Injective (Ψ i)) {F : (ι → σ') → O} {w : ι → ℝ} {V : ℝ}
    (P : DualPair K F) (hP : P.IsWeightedCostLe w V) :
    (P.coordRecode hΨ).IsWeightedCostLe w V :=
  ⟨fun x => hP.1 _, fun y => hP.2 _⟩

end DualPair

end QuantumQueryComplexity
