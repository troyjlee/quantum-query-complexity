import QuantumQueryComplexity.Quantum.Complexity
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The uniform alphabet factorization

Milestone D's first component, and the one that removes the `√|σ|` loss.

A dual solution has to realise the *inequality indicator* `[a ≠ b]` as an
inner product of vectors attached to the two letters.  The construction used
so far copies a value onto every letter that differs, so its norms grow like
`√|σ|`.  The uniform replacement lives on `Option σ` — one extra "constant"
coordinate beside the `σ`-indexed ones.  The vectors live in an ambient space
of dimension `|σ| + 1`, but each is supported on exactly two coordinates;
they are **two-sparse independently of the alphabet size**:

    μ a = (1,  e a)          ν b = (1, − e b)

    ⟨μ a, ν b⟩ = 1 − δ_{ab} = [a ≠ b]
    ‖μ a‖² = ‖ν b‖² = 2

The constant coordinate contributes `1` to every pairing; the letter
coordinates contribute `−1` exactly when the letters agree, cancelling it.
Both **squared** norms are `2` — equivalently both norms are `√2` —
**independently of the alphabet size**, which is the whole point.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- The left vector of the factorization: `1` on the constant coordinate and
`1` at its own letter. -/
def uniformLeft (a : σ) : Option σ → ℝ
  | none => 1
  | some x => if x = a then 1 else 0

/-- The right vector: `1` on the constant coordinate and `−1` at its own
letter. -/
def uniformRight (b : σ) : Option σ → ℝ
  | none => 1
  | some x => if x = b then -1 else 0

@[simp] lemma uniformLeft_none (a : σ) : uniformLeft a none = 1 := rfl

@[simp] lemma uniformLeft_some (a x : σ) :
    uniformLeft a (some x) = if x = a then 1 else 0 := rfl

@[simp] lemma uniformRight_none (b : σ) : uniformRight b none = 1 := rfl

@[simp] lemma uniformRight_some (b x : σ) :
    uniformRight b (some x) = if x = b then -1 else 0 := rfl

/-- **The factorization**: the pairing is the inequality indicator. -/
theorem uniform_dotProduct (a b : σ) :
    uniformLeft a ⬝ᵥ uniformRight b = if a = b then 0 else 1 := by
  classical
  rw [dotProduct, Fintype.sum_option]
  have hterm : ∀ x : σ, uniformLeft a (some x) * uniformRight b (some x)
      = if a = b then (if x = a then (-1 : ℝ) else 0) else 0 := by
    intro x
    simp only [uniformLeft_some, uniformRight_some]
    by_cases hxa : x = a
    · subst hxa
      simp
    · simp [hxa]
  rw [Finset.sum_congr rfl fun x _ => hterm x]
  by_cases hab : a = b
  · subst hab
    simp
  · simp [hab]

/-- **Both squared norms are `2`** — equivalently both norms are `√2` —
independently of the alphabet size. -/
theorem uniformLeft_normSq (a : σ) : uniformLeft a ⬝ᵥ uniformLeft a = 2 := by
  classical
  rw [dotProduct, Fintype.sum_option]
  have hterm : ∀ x : σ, uniformLeft a (some x) * uniformLeft a (some x)
      = if x = a then (1 : ℝ) else 0 := by
    intro x
    simp only [uniformLeft_some]
    by_cases hxa : x = a <;> simp [hxa]
  rw [Finset.sum_congr rfl fun x _ => hterm x]
  simp
  norm_num

theorem uniformRight_normSq (b : σ) :
    uniformRight b ⬝ᵥ uniformRight b = 2 := by
  classical
  rw [dotProduct, Fintype.sum_option]
  have hterm : ∀ x : σ, uniformRight b (some x) * uniformRight b (some x)
      = if x = b then (1 : ℝ) else 0 := by
    intro x
    simp only [uniformRight_some]
    by_cases hxb : x = b <;> simp [hxb]
  rw [Finset.sum_congr rfl fun x _ => hterm x]
  simp
  norm_num

/-- The factorization in the form the dual constraint consumes: the pairing
vanishes exactly when the letters agree, i.e. when the query does not
distinguish the two inputs. -/
theorem uniform_dotProduct_eq_zero_iff (a b : σ) :
    uniformLeft a ⬝ᵥ uniformRight b = 0 ↔ a = b := by
  rw [uniform_dotProduct]
  by_cases hab : a = b
  · rw [if_pos hab]
    exact ⟨fun _ => hab, fun _ => rfl⟩
  · rw [if_neg hab]
    exact ⟨fun h => absurd h (by norm_num), fun h => absurd h hab⟩

end QuantumQueryComplexity
