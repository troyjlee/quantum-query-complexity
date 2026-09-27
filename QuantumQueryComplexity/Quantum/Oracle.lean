import QuantumQueryComplexity.Quantum.FiniteHilbert
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The value oracle

The basis of a query algorithm is

  `QBasis ι σ W = Option ι × Option σ × W`

— a query-index register (`none` = *idle*, no query is made), an answer register
(`none` = *blank*), and a workspace.  On input `a : ι → σ` the oracle acts as the
identity on the idle sector and, on the index `some i`, **swaps the blank answer
with the answer `some (a i)`**:

  `|i⟩|⊥⟩|w⟩ ↦ |i⟩|a i⟩|w⟩`,  `|i⟩|a i⟩|w⟩ ↦ |i⟩|⊥⟩|w⟩`,

leaving `|i⟩|s⟩|w⟩` alone for every other answer `s`.

Why this oracle rather than `|i⟩|s⟩ ↦ |i⟩|s ⊕ a i⟩`:

* it is defined for **any** finite alphabet, with no group structure on `σ`;
* it is a permutation of the basis, hence unitary for free, and an
  **involution**, so query and unquery are literally the same matrix;
* the idle index gives controlled queries at no extra cost, which is what the
  phase-detection circuit of the upper bound will need;
* on a blank answer register it returns the value coherently, which is all the
  lower bound's query decomposition uses.

It is equivalent to the Boolean XOR oracle at two queries per query, in both
directions: `XorOracle.lean` defines that oracle (with explicit idle-index
and blank-answer sectors) and `Simulation.lean` proves the equivalence.

The two lemmas that carry the whole development are `oracleMap_none` and
`oracleMap_some`: the oracle's action at a basis state with index `some i`
depends on the input **only through `a i`**.  That is the source of the
adversary lower bound's query decomposition.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

/-- The basis of a query algorithm: query index (`none` = idle), answer register
(`none` = blank), and workspace. -/
abbrev QBasis (ι σ W : Type*) : Type _ := Option ι × Option σ × W

variable {ι σ W : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-- The oracle's action on the computational basis. -/
def oracleMap (a : ι → σ) : QBasis ι σ W → QBasis ι σ W
  | (none, t, w) => (none, t, w)
  | (some i, t, w) => (some i, Equiv.swap none (some (a i)) t, w)

@[simp] lemma oracleMap_none (a : ι → σ) (t : Option σ) (w : W) :
    oracleMap a ((none, t, w) : QBasis ι σ W) = (none, t, w) := rfl

/-- **The oracle reads the input only at the queried index.** -/
@[simp] lemma oracleMap_some (a : ι → σ) (i : ι) (t : Option σ) (w : W) :
    oracleMap a ((some i, t, w) : QBasis ι σ W)
      = (some i, Equiv.swap none (some (a i)) t, w) := rfl

/-- The oracle never moves the index register. -/
lemma oracleMap_fst (a : ι → σ) (p : QBasis ι σ W) : (oracleMap a p).1 = p.1 := by
  obtain ⟨(_ | i), t, w⟩ := p <;> rfl

lemma oracleMap_snd_of_fst_none {a : ι → σ} {p : QBasis ι σ W}
    (h : p.1 = none) : (oracleMap a p).2.1 = p.2.1 := by
  obtain ⟨(_ | i), t, w⟩ := p
  · rfl
  · exact absurd h (by simp)

lemma oracleMap_snd_of_fst_some {a : ι → σ} {p : QBasis ι σ W} {i : ι}
    (h : p.1 = some i) :
    (oracleMap a p).2.1 = Equiv.swap none (some (a i)) p.2.1 := by
  obtain ⟨(_ | j), t, w⟩ := p
  · exact absurd h (by simp)
  · have hj : j = i := Option.some_injective _ h
    subst hj
    rfl

lemma oracleMap_blank (a : ι → σ) (i : ι) (w : W) :
    oracleMap a ((some i, none, w) : QBasis ι σ W) = (some i, some (a i), w) := by
  simp

lemma oracleMap_involutive (a : ι → σ) :
    Function.Involutive (oracleMap (W := W) a) := by
  rintro ⟨(_ | i), t, w⟩
  · rfl
  · simp

/-- The oracle as a permutation of the basis. -/
def oraclePerm (a : ι → σ) : Equiv.Perm (QBasis ι σ W) :=
  Function.Involutive.toPerm _ (oracleMap_involutive a)

@[simp] lemma oraclePerm_apply (a : ι → σ) (p : QBasis ι σ W) :
    oraclePerm a p = oracleMap a p := rfl

lemma oraclePerm_involutive (a : ι → σ) :
    Function.Involutive (oraclePerm (W := W) a) := oracleMap_involutive a

/-- **The oracle unitary.** -/
def oracleMat (a : ι → σ) : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ :=
  qPerm (oraclePerm a)

theorem oracleMat_mem_unitaryGroup (a : ι → σ) :
    oracleMat (W := W) a ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ :=
  qPerm_mem_unitaryGroup _

/-- **Query = unquery.** -/
theorem oracleMat_mul_self (a : ι → σ) :
    oracleMat (W := W) a * oracleMat a = 1 :=
  qPerm_mul_self_of_involutive (oraclePerm_involutive a)

lemma oracleMat_mulVec_apply (a : ι → σ) (ψ : QBasis ι σ W → ℂ) (p : QBasis ι σ W) :
    (oracleMat a *ᵥ ψ) p = ψ (oracleMap a p) := by
  rw [oracleMat, qPerm_mulVec_apply]
  -- `(oraclePerm a).symm` is the same function as `oracleMap a`, by construction
  rfl

/-- On the idle sector the oracle does nothing: this is what makes a query
*controlled*. -/
@[simp] lemma oracleMat_mulVec_apply_none (a : ι → σ) (ψ : QBasis ι σ W → ℂ)
    (t : Option σ) (w : W) :
    (oracleMat a *ᵥ ψ) ((none, t, w) : QBasis ι σ W) = ψ (none, t, w) := by
  rw [oracleMat_mulVec_apply, oracleMap_none]

/-- **The query decomposition.**  At a basis state with query index `some i` the
queried state depends on the input only through `a i`. -/
@[simp] lemma oracleMat_mulVec_apply_some (a : ι → σ) (ψ : QBasis ι σ W → ℂ)
    (i : ι) (t : Option σ) (w : W) :
    (oracleMat a *ᵥ ψ) ((some i, t, w) : QBasis ι σ W)
      = ψ (some i, Equiv.swap none (some (a i)) t, w) := by
  rw [oracleMat_mulVec_apply, oracleMap_some]

/-- Two inputs that agree at the index `i` give the same amplitude at every
basis state querying `i`; two inputs always agree on the idle sector. -/
theorem oracleMat_mulVec_congr {a b : ι → σ} (ψ : QBasis ι σ W → ℂ)
    {p : QBasis ι σ W} (hp : ∀ i, p.1 = some i → a i = b i) :
    (oracleMat a *ᵥ ψ) p = (oracleMat b *ᵥ ψ) p := by
  obtain ⟨(_ | i), t, w⟩ := p
  · simp
  · rw [oracleMat_mulVec_apply_some, oracleMat_mulVec_apply_some, hp i rfl]

lemma oracleMat_mulVec_qBasis (a : ι → σ) (p : QBasis ι σ W) :
    oracleMat a *ᵥ qBasis p = qBasis (oracleMap a p) := by
  rw [oracleMat, qPerm_mulVec_qBasis]
  rfl

end QuantumQueryComplexity
