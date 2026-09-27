import QuantumQueryComplexity.LDS.Defs
import QuantumQueryComplexity.EDLower.Main
import QuantumQueryComplexity.Promise.Transport
import QuantumQueryComplexity.HasDual
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
# Longest distinct substring: the `n^{2/3}` lower bound and the sandwich

Element distinctness is a postprocessing of `ldsFun`: a word repeats a
value iff its longest distinct window is shorter than the whole word,

  `edFun α = decide (ldsFun α < n)`.

So `advPM_postcompose_le` transfers Belovs' lower bound wholesale
: any adversary matrix feasible for `edFun` is feasible for
`ldsFun`, giving `n^{2/3}/128 ≤ ADV±(ldsFun)` under the `EDLower`
alphabet hypothesis `4n² ≤ |σ|`.  Together with the read-everything
`2n` dual this is the two-sided sandwich whose upper half M4–M6 will
tighten to `Õ(n^{2/3})`.
-/

namespace QuantumQueryComplexity

variable {n : ℕ} {σ : Type} [Fintype σ] [DecidableEq σ]

/-- A word repeats a value iff its longest distinct window is shorter than
the whole word: `edFun` is a Boolean postprocessing of `ldsFun`. -/
lemma edFun_eq_decide_ldsFun (α : Fin n → σ) :
    edFun α = decide (ldsFun α < n) := by
  by_cases h : Function.Injective α
  · have h1 : edFun α = false :=
      edFun_eq_false_iff.mpr fun i j hij => h hij
    rw [h1, ldsFun_eq_of_injective h]
    exact (decide_eq_false (lt_irrefl n)).symm
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp h
    have h1 : edFun α = true := edFun_eq_true_iff.mpr ⟨(a, b), hne, hab⟩
    have h2 : ldsFun α < n :=
      lt_of_le_of_ne (ldsFun_le α) fun he => h (injective_of_ldsFun_eq he)
    rw [h1]
    exact (decide_eq_true h2).symm

/-- **Lower-bound transfer** (plan §2): postprocessing cannot increase the
adversary bound, so `ADV±(edFun) ≤ ADV±(ldsFun)`. -/
theorem advPM_edFun_le_advPM_ldsFun :
    advPM (edFun (ι := Fin n) (σ := σ)) ≤ advPM (ldsFun (n := n) (σ := σ)) := by
  have h := advPM_postcompose_le (g := ldsFun (n := n) (σ := σ))
    fun v => decide (v < n)
  have he : edFun (ι := Fin n) (σ := σ) = fun α => decide (ldsFun α < n) :=
    funext edFun_eq_decide_ldsFun
  rw [he]
  exact h

/-- **The `n^{2/3}` lower bound for longest distinct substring**: Belovs'
element-distinctness bound rides through the transfer. -/
theorem advPM_ldsFun_ge (hn : 2 ≤ n)
    (hq : 4 * (n * n) ≤ Fintype.card σ) :
    (n : ℝ) ^ ((2 : ℝ) / 3) / 128 ≤ advPM (ldsFun (n := n) (σ := σ)) := by
  have h1 := advPM_edFun_ge (ι := Fin n) (σ := σ)
    (by simpa using hn) (by simpa using hq)
  simpa using h1.trans advPM_edFun_le_advPM_ldsFun

/-- The trivial read-everything upper bound `ADV±(ldsFun) ≤ 2n`. -/
theorem advPM_ldsFun_le_two_mul :
    advPM (ldsFun (n := n) (σ := σ)) ≤ 2 * (n : ℝ) := by
  have h := advPM_le_of_hasDual (c := 2 * (Fintype.card (Fin n) : ℝ))
    (by positivity) (hasDual_two_mul_card (ldsFun (n := n) (σ := σ)))
  simpa using h

/-- **The sandwich skeleton** (plan §2): for `n ≥ 2` and alphabet size at
least `4n²`, `n^{2/3}/128 ≤ ADV±(ldsFun) ≤ 2n`.  M6 replaces the upper
half by `C·n^{2/3}(1 + log₂ n)`. -/
theorem advPM_ldsFun_sandwich (hn : 2 ≤ n)
    (hq : 4 * (n * n) ≤ Fintype.card σ) :
    (n : ℝ) ^ ((2 : ℝ) / 3) / 128 ≤ advPM (ldsFun (n := n) (σ := σ)) ∧
      advPM (ldsFun (n := n) (σ := σ)) ≤ 2 * (n : ℝ) :=
  ⟨advPM_ldsFun_ge hn hq, advPM_ldsFun_le_two_mul⟩

end QuantumQueryComplexity
