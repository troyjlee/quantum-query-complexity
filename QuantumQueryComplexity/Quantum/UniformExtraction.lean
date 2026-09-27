import QuantumQueryComplexity.Quantum.UniformConversion
set_option synthInstance.maxSize 2000

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Milestone D: the uniform extraction

The packaging of the cardinality-free construction: the detector run on the
clocked input-independent `common` state, with the readout announcing the
label held in the target register, is an algorithm computing `f` on the
promise with error `1/16` — within `8192(1 + c)` queries.

The acceptance statement `exists_algorithm_of_dualPairOn_uniform` has the
required scope, every clause load-bearing:

* arbitrary **decidable** output `O`, no `[Fintype O]`;
* `uniformExtractionConstant = 8192`, one fixed absolute constant —
  independent of `|σ|`, `|O|`, `|range f|`;
* `[Nonempty O]` (the readout needs a junk label off the target register)
  and `0 ≤ c` are genuine hypotheses;
* promise-native, and no appeal to general-output strong duality.

The correctness chain is three moves: the algorithm's final state is
`D·clock(common)`, which is within squared distance `1/16` of
`clock(out(f x))` (`qNormSq_uniformConvError_le_sixteenth`); the clocked
output state announces `f x` **surely** (its support carries the label in
the target register — `realizedOut_apply_of_ne` through
`uniformClock_apply_eq_zero`); and the distance-to-success bridge
(`le_qProb_of_qNormSq_sub_le`, output-cardinality-free by design) converts
the distance into the success probability `≥ 1 − 1/16`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ K X O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [DecidableEq σ] [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq O]
  {read : X → ι → σ} {f : X → O}

/-- **The uniform extraction constant** — one fixed absolute constant, never
a free variable. -/
def uniformExtractionConstant : ℝ := 8192

/-! ## The readout -/

/-- The label of one workspace coordinate: the output held in the target
register, or the junk label `o₀` anywhere else. -/
def uniformLabel (f : X → O) (o₀ : O) :
    UWork ↥(Set.range f) ι K → O
  | Sum.inl (some r) => (r : O)
  | Sum.inl none => o₀
  | Sum.inr _ => o₀

@[simp] lemma uniformLabel_inl_some (f : X → O) (o₀ : O)
    (r : ↥(Set.range f)) :
    uniformLabel (ι := ι) (K := K) f o₀ (Sum.inl (some r)) = (r : O) := rfl

/-- **The readout**: announce the label held in the target register of the
clocked workspace. -/
def uniformReadout (f : X → O) (o₀ : O) (T : ℕ) :
    QBasis ι σ (ClockWork ι T (UWork ↥(Set.range f) ι K)) → O :=
  fun b => uniformLabel f o₀ b.2.2.2.2.2

lemma uniformReadout_apply (f : X → O) (o₀ : O) (T : ℕ)
    (b : QBasis ι σ (ClockWork ι T (UWork ↥(Set.range f) ι K))) :
    uniformReadout f o₀ T b = uniformLabel f o₀ b.2.2.2.2.2 := rfl

/-- **The clocked output state announces its label surely**: it is its own
restriction to the `f x`-sector of the readout. -/
theorem qRestrict_uniformClock_realizedOut (o₀ : O) (T : ℕ) (x : X) :
    qRestrict (uniformReadout (ι := ι) (σ := σ) (K := K) f o₀ T) (f x)
        (uniformClock T (realizedOut (K := K) f x))
      = uniformClock T (realizedOut (K := K) f x) := by
  funext b
  rw [qRestrict]
  by_cases hb : uniformReadout (ι := ι) (σ := σ) (K := K) f o₀ T b = f x
  · rw [if_pos hb]
  · rw [if_neg hb]
    refine ((uniformClock_apply_eq_zero T _ ?_)).symm
    refine realizedOut_apply_of_ne f x ?_
    intro hw
    apply hb
    rw [uniformReadout_apply, hw, uniformLabel_inl_some, rangeElem_val]

/-! ## The algorithm -/

/-- **The uniform extraction algorithm**: prepare the clocked common state,
run the detector, read the target register. -/
noncomputable def uniformAlg (P : DualPairOn read K f) (α : ℝ) (o₀ : O)
    (T : ℕ) (hT : 0 < T) :
    QAlg ι σ O (ClockWork ι T (UWork ↥(Set.range f) ι K)) :=
  (uniformDetector P α T).toAlg
    (uniformClock T (realizedCommon (K := K) f))
    (by rw [IsQState, qNormSq_uniformClock hT, qNormSq_realizedCommon])
    (uniformReadout f o₀ T)

/-- **The uniform algorithm computes `f`** at the chosen parameters: error
`1/16` on the promise, in exactly `4(T − 1)` queries. -/
theorem uniformAlg_computes (P : DualPairOn read K f) {c : ℝ}
    (hP : P.IsCostLe c) (hc : 0 ≤ c) (o₀ : O) :
    ComputesWithErrorOn
      (uniformAlg P (uniformAlpha c) o₀ (uniformT c) (uniformT_pos hc))
      (4 * (uniformT c - 1)) read f (1 / 16) := by
  intro x
  have hT : 0 < uniformT c := uniformT_pos hc
  -- the final state is the detector on the clocked common state
  have hlen : (uniformDetector P (uniformAlpha c) (uniformT c)).len
      = 4 * (uniformT c - 1) := uniformDetector_len P (uniformAlpha c) _
  have hstate : (uniformAlg P (uniformAlpha c) o₀ (uniformT c) hT).state
        (read x) (4 * (uniformT c - 1))
      = (uniformDetector P (uniformAlpha c) (uniformT c)).run (read x)
          *ᵥ uniformClock (uniformT c) (realizedCommon (K := K) f) := by
    rw [uniformAlg, ← hlen]
    exact QRoutine.toAlg_state_len _ _ _ _ _
  -- it is within squared distance 1/16 of the clocked output state
  have hdist : qNormSq ((uniformAlg P (uniformAlpha c) o₀ (uniformT c)
          hT).state (read x) (4 * (uniformT c - 1))
        - uniformClock (uniformT c) (realizedOut (K := K) f x))
      ≤ 1 / 16 := by
    rw [hstate]
    exact qNormSq_uniformConvError_le_sixteenth P hP hc x
  -- the final state is a unit vector
  have hone : qNormSq ((uniformAlg P (uniformAlpha c) o₀ (uniformT c)
        hT).state (read x) (4 * (uniformT c - 1))) = 1 :=
    (uniformAlg P (uniformAlpha c) o₀ (uniformT c) hT).state_isQState
      (read x) _
  -- the bridge to the announced probability
  have hbridge := le_qProb_of_qNormSq_sub_le
    (uniformReadout (ι := ι) (σ := σ) (K := K) f o₀ (uniformT c)) (f x)
    (qRestrict_uniformClock_realizedOut (K := K) o₀ (uniformT c) x) hdist
  have hgoal : 1 - 1 / 16
      ≤ qProb (uniformReadout (ι := ι) (σ := σ) (K := K) f o₀ (uniformT c))
          ((uniformAlg P (uniformAlpha c) o₀ (uniformT c) hT).state (read x)
            (4 * (uniformT c - 1))) (f x) := by
    linarith
  exact hgoal

/-! ## The acceptance statement -/

/-- **A dual solution is an algorithm, with no cardinality anywhere**: cost
`c` yields error `1/16` within `uniformExtractionConstant·(1 + c)` queries —
independent of `|σ|`, `|O|` and `|range f|`, for any decidable output type. -/
theorem exists_algorithm_of_dualPairOn_uniform [Nonempty O]
    (P : DualPairOn read K f) {c : ℝ} (hP : P.IsCostLe c) (hc : 0 ≤ c) :
    ∃ q ∈ QueryCounts read f (1 / 16),
      (q : ℝ) ≤ uniformExtractionConstant * (1 + c) := by
  obtain ⟨o₀⟩ := (inferInstance : Nonempty O)
  refine ⟨4 * (uniformT c - 1),
    mem_queryCounts (uniformAlg_computes P hP hc o₀), ?_⟩
  have h := uniformDetector_len_uniformT_le P (uniformAlpha c) hc
  rw [uniformDetector_len] at h
  rw [uniformExtractionConstant]
  exact h

end QuantumQueryComplexity
