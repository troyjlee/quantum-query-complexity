import QuantumQueryComplexity.Quantum.UniformHasDual
import QuantumQueryComplexity.Quantum.Plurality
import QuantumQueryComplexity.Quantum.Padding
import QuantumQueryComplexity.Quantum.Postcomp
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Algorithms from promise duals, at a fixed budget, and their amplification

Two wrappers that upper-bound developments use to turn a dual adversary solution into an
algorithm with an explicit query budget and then lower its error.

* `exists_alg_of_hasDualOn`: a promise dual of cost `c ≥ 0` gives one algorithm on a finite
  workspace computing `f` with error at most `1/16` on every promise input, with exactly the
  budget `⌊8192 (1 + c)⌋` (the uniform extraction `exists_algorithm_of_dualPairOn_uniform`,
  padded upward by `queryCounts_upward`).
* `exists_alg_amplify`: an algorithm with error `1/16` and `q` queries gives one with error
  `2^{-s}` and `4 s q` queries, for every `s ≥ 1` and every output type with an element. The
  outputs are recoded into the finite range of `f` (an `Option` of a subtype), where the
  plurality amplification `amplify_plurality` applies, and decoded afterwards.

Both were first written for the minimum-cut upper bound of the companion problems repository
(`MinimumCut/Upper/Enumeration.lean`) and are moved here unchanged in statement, so that other
upper bounds (k-distinctness after Belovs) can use them.
-/

namespace QuantumQueryComplexity

open Finset

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

/-- **An algorithm from a promise dual**: a dual of cost `c ≥ 0` gives an algorithm with error
`1/16` and `⌊8192 (1 + c)⌋` queries (the uniform extraction, padded to this budget). -/
theorem exists_alg_of_hasDualOn {X O : Type} [Fintype X] [DecidableEq O] [Nonempty O]
    {read : X → ι → σ} {f : X → O} {c : ℝ} (h : HasDualOn read f c) (hc : 0 ≤ c) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (A : QAlg ι σ O W),
      ComputesWithErrorOn A ⌊8192 * (1 + c)⌋₊ read f (1 / 16) := by
  obtain ⟨K, hK, P, hP⟩ := h
  let _ := hK
  let _ := Classical.decEq K
  obtain ⟨q, hq, hqle⟩ := exists_algorithm_of_dualPairOn_uniform P hP hc
  have hle : q ≤ ⌊8192 * (1 + c)⌋₊ := by
    apply Nat.le_floor
    simpa [uniformExtractionConstant] using hqle
  exact queryCounts_upward hq hle

private lemma amplify_error_le (s : ℕ) :
    (1 + 1 / 16 : ℝ) ^ (4 * s) / 2 ^ ((4 * s - 1 + 2) / 2) ≤ (1 / 2) ^ s := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · norm_num
  have hexp : (4 * s - 1 + 2) / 2 = 2 * s := by omega
  rw [hexp, pow_mul, pow_mul, ← div_pow]
  exact pow_le_pow_left₀ (by positivity) (by norm_num) s

/-- **Plurality amplification, for any output type**: an algorithm with error `1/16` and `q`
queries gives one with error `2^{-s}` and `4 s q` queries, `s ≥ 1`. The outputs are first
recoded into the finite range of `f`, where the library's plurality amplification applies. -/
theorem exists_alg_amplify {X O : Type} [Fintype X] [DecidableEq O] [Nonempty O]
    {read : X → ι → σ} {f : X → O} {q : ℕ}
    (h : ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (A : QAlg ι σ O W),
      ComputesWithErrorOn A q read f (1 / 16))
    {s : ℕ} (hs : 1 ≤ s) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (A : QAlg ι σ O W),
      ComputesWithErrorOn A (4 * s * q) read f ((1 / 2) ^ s) := by
  classical
  obtain ⟨W, hW, hW', A, hA⟩ := h
  set S : Finset O := univ.image f with hS
  let r : O → Option {o // o ∈ S} := fun o => if h : o ∈ S then some ⟨o, h⟩ else none
  let b : Option {o // o ∈ S} → O := fun z => z.elim (Classical.arbitrary O) Subtype.val
  have hbr : ∀ x, b (r (f x)) = f x := by
    intro x
    have hx : f x ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ x)
    simp [r, b, hx]
  have h1 : ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : QAlg ι σ (Option {o // o ∈ S}) W),
      ComputesWithErrorOn A q read (fun x => r (f x)) (1 / 16) :=
    ⟨W, hW, hW', A.postcomp r, hA.postcomp r⟩
  obtain ⟨W₂, hW₂, hW₂', A₂, hA₂⟩ := amplify_plurality h1 (4 * s - 1)
  have hk : 4 * s - 1 + 1 = 4 * s := by omega
  rw [hk] at hA₂
  have hA₃ := (hA₂.postcomp b).mono (amplify_error_le s)
  refine ⟨W₂, hW₂, hW₂', A₂.postcomp b, ?_⟩
  rw [mul_comm (4 * s) q] at hA₃ ⊢
  simpa only [hbr] using hA₃

end QuantumQueryComplexity
