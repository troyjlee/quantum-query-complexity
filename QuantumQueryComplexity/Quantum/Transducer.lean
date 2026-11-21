import QuantumQueryComplexity.Quantum.Amplitude.PhaseEstimation
import QuantumQueryComplexity.Quantum.Approximation

set_option linter.style.header false
-- The clocked workspace nests five products deep; instance search on its basis needs a larger
-- size budget (as in `Clock.lean` and `Amplitude/PhaseEstimation.lean`).
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Transducers: from a catalyst identity to an algorithm

Belovs, Jeffery and Yolcu [BJY23] (*Taming Quantum Time Complexity*, arXiv:2311.15873v3, §5)
call a unitary `S` on `H ⊕ L` a **transducer**. `H` is the *public* space and `L` the *private*
one. `S` *transduces* `ξ ∈ H` into `τ ∈ H` when some `v ∈ L`, a *catalyst*, satisfies

  `S (ξ ⊕ v) = τ ⊕ v`                                                    [BJY23, (5.1)].

[BJY23, Theorem 5.5] turns this into an algorithm that never reads the private space. With a
clock register of size `K`:

1. map the clock state `|0⟩` to the uniform superposition `K^{-1/2} ∑_t |t⟩`;
2. for `t = 0, …, K − 1`: (a) apply `S` controlled on the clock value `t`; (b) on the private
   part, advance the clock by one, cyclically;
3. undo step 1.

The algorithm maps `|0⟩ ⊗ ξ` to within `2‖v‖/√K` of `|0⟩ ⊗ τ`, for **every** catalyst `v`. The
proof adds `K^{-1/2} |0⟩ ⊗ v` after step 1 (a perturbation of norm `‖v‖/√K`) and runs the loop
exactly. On the clock branch `t` the catalyst meets `ξ` exactly when `S` is applied there, and
the advance carries it on to branch `t + 1` (`Transducer.loop_catalyst`). At the end the
catalyst is back on branch `0` and is removed again. Unitarity carries both errors to the end.

## Conventions

* **Privacy is a predicate on basis states**: `priv h` says the basis state `h` is private, as
  the privacy qubit `P` of [BJY23, (5.4)] does. `H` is the span of the public basis states and
  `L` that of the private ones. A vector is public if it vanishes on every private basis state,
  and private if it vanishes on every public one (`Transduces`).
* `S` is a unitary on the **whole** space; no block form is assumed. The minimal catalyst of
  [BJY23, Theorem 5.1] is never needed, so neither the existence nor the uniqueness of
  catalysts is stated: the hypotheses take a catalyst as given.
* Step 2(b) is the **same** basis permutation in every round: on every private basis state,
  advance the clock cyclically, `c ↦ c + 1 mod K` (`finRotate K`; `Transducer.tick`).
  [BJY23] writes "replace `|t⟩_K` by `|t + 1⟩_K`"; the cyclic advance is a unitary that does
  this on the only clock branch that carries the catalyst.
* Step 1 is the fixed unitary `fourierMat K` on the clock, whose column `0` is uniform. It costs
  no queries. A basis permutation could not prepare the uniform clock for `K > 1`.
* Vectors are unnormalized and errors are norms (`qNorm`). `sqrt_qProb_le_add` turns a norm
  error into a bound on outcome probabilities.

## Main statements

* `Transduces priv S ξ τ v`: the catalyst identity with its public and private side conditions.
* `Transducer.circuit K S priv`: the algorithm of [BJY23, Theorem 5.5] as a matrix on
  `Fin K × H`, with `K` controlled applications of `S`. `Transducer.circuit_close` is the
  theorem: `‖circuit (|0⟩ ⊗ ξ) − |0⟩ ⊗ τ‖ ≤ 2‖v‖/√K`.
* `exists_transducerRoutine`: **the routine form**. For a routine `R` (with queries), a privacy
  predicate on its basis states and `0 < K`, there is one routine, fixed before the input, with
  exactly `K · R.len` queries on the clocked workspace `ClockWork ι K W`, such that on every
  input `a` and for every transduction `R.run a : ξ + v ↦ τ + v` its run maps the clock-`0`
  embedding of `ξ` to within `2‖v‖/√K` of the clock-`0` embedding of `τ`.
* `exists_transducerRoutine_of_realizes`: the same when, on each input `a`, `R` realizes a
  matrix `S` on a smaller basis `V` embedded injectively into its basis (`Transducer.embedVia`).
  This is the form for a walk register `V` whose other registers are clean scratch.
* `exists_transducerRoutine_encoded`: the exact statement behind the routine form. On the
  clocked sector the routine acts as `Transducer.circuit K (R.run a) priv`.

The intended routine runs `QRoutine.control` of `R` lifted to the clock once per clock value
(as `clockRound` in `Clock.lean`, but on the branch `c = t`), each round followed by the
permutation `tick`, between `clockOp K (fourierMat K)` and its adjoint. Only the theorems are
stated here; the construction is left to the proofs.

`Test/Transducer.lean` checks [BJY23, Example 5.3] and a transducer that makes a query.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

/-! ## Transductions -/

/-- **`S` transduces `ξ` into `τ` with catalyst `v`**, relative to the privacy predicate `priv`
on basis states ([BJY23, (5.1)], with the privacy flag of [BJY23, (5.4)]):

* `ξ` and `τ` are public: they vanish on every private basis state;
* `v` is private: it vanishes on every public basis state;
* `S (ξ + v) = τ + v`.

Nothing else is assumed: no normalization, no minimality of `v` (the catalyst of
[BJY23, Theorem 5.1(b)]), and no unitarity of `S`. The theorems that use it assume unitarity
where they need it. The transduction complexity `W(S, ξ)` of [BJY23] is at most `‖v‖²` for
every catalyst `v` [BJY23, Claim 5.2]. -/
structure Transduces {H : Type} [Fintype H] (priv : H → Prop) (S : Matrix H H ℂ)
    (ξ τ v : H → ℂ) : Prop where
  /-- The initial vector `ξ` is public. -/
  source_public : ∀ h, priv h → ξ h = 0
  /-- The final vector `τ` is public. -/
  target_public : ∀ h, priv h → τ h = 0
  /-- The catalyst `v` is private. -/
  catalyst_private : ∀ h, ¬ priv h → v h = 0
  /-- The catalyst identity `S (ξ + v) = τ + v`. -/
  mulVec_eq : S *ᵥ (ξ + v) = τ + v

namespace Transducer

/-! ## The algorithm as a matrix -/

section Circuit

variable {H : Type} [Fintype H] [DecidableEq H]

/-- The vector `|c⟩ ⊗ ψ` on `Fin K × H`: `ψ` on the clock branch `c`, zero on every other
branch. -/
def clockVec {K : ℕ} (c : Fin K) (ψ : H → ℂ) : Fin K × H → ℂ :=
  fun x => if x.1 = c then ψ x.2 else 0

/-- **`S` controlled on the clock value `t`** ([BJY23, Theorem 5.5], step 2(a)): on the clock
branch `c` it acts as `S` if `c = t` and as the identity otherwise. It never moves the clock.
For `t ≥ K` it is the identity. -/
def ctrlAt (K t : ℕ) (S : Matrix H H ℂ) : Matrix (Fin K × H) (Fin K × H) ℂ :=
  Matrix.of fun x y =>
    if x.1 = y.1 then (if (x.1 : ℕ) = t then S x.2 y.2 else (1 : Matrix H H ℂ) x.2 y.2)
    else 0

/-- **Advance the clock on the private part** ([BJY23, Theorem 5.5], step 2(b)): the basis
permutation `(c, h) ↦ (c + 1 mod K, h)` when `h` is private, and `(c, h) ↦ (c, h)` when `h` is
public. It is the same permutation in every round, and it depends on `K` and `priv` only. -/
def tick (K : ℕ) (priv : H → Prop) [DecidablePred priv] : Equiv.Perm (Fin K × H) where
  toFun x := (if priv x.2 then finRotate K x.1 else x.1, x.2)
  invFun x := (if priv x.2 then (finRotate K).symm x.1 else x.1, x.2)
  left_inv := by
    rintro ⟨c, h⟩
    by_cases hp : priv h <;> simp only [hp, ↓reduceIte, Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨c, h⟩
    by_cases hp : priv h <;> simp only [hp, ↓reduceIte, Equiv.apply_symm_apply]

/-- **The clock preparation** `fourierMat K ⊗ 1` ([BJY23, Theorem 5.5], step 1). For `0 < K`
its column `(0, h)` is `K^{-1/2} ∑_t |t⟩ ⊗ |h⟩`: it maps `|0⟩ ⊗ ψ` to the uniform clock over
`ψ`. It is unitary for `0 < K` (`fourierMat_mem_unitaryGroup`), and fixed: it depends on `K`
only. -/
noncomputable def prep (K : ℕ) : Matrix (Fin K × H) (Fin K × H) ℂ :=
  Matrix.kroneckerMap (· * ·) (fourierMat K) (1 : Matrix H H ℂ)

/-- **The first `n` rounds of the loop** ([BJY23, Theorem 5.5], step 2). Round `t` (for
`t = 0, …, n − 1`, in this order) applies `ctrlAt K t S` and then the permutation `tick K priv`.
For `n ≤ K` (in `circuit`, `n = K`) each round applies `S` on exactly one clock branch, so `S`
is used `n` times; a round with `t ≥ K` applies only `tick`, since `ctrlAt K t S = 1`. -/
noncomputable def loop (K : ℕ) (S : Matrix H H ℂ) (priv : H → Prop) [DecidablePred priv] :
    ℕ → Matrix (Fin K × H) (Fin K × H) ℂ
  | 0 => 1
  | n + 1 => qPerm (tick K priv) * (ctrlAt K n S * loop K S priv n)

/-- **The algorithm of [BJY23, Theorem 5.5]**, as a matrix on `Fin K × H`: prepare the uniform
clock (`prep`), run the `K` rounds (`loop`), and undo the preparation (`(prep K)ᴴ`). It uses `S`
exactly `K` times, each time controlled on a clock value; its other factors are fixed
unitaries that depend on `K` and `priv` only. -/
noncomputable def circuit (K : ℕ) (S : Matrix H H ℂ) (priv : H → Prop) [DecidablePred priv] :
    Matrix (Fin K × H) (Fin K × H) ℂ :=
  (prep K)ᴴ * (loop K S priv K * prep K)

/-- The algorithm is unitary when `S` is unitary. (For `K = 0` the index type `Fin 0 × H` is
empty and the statement is trivial; for `0 < K` it uses `fourierMat_mem_unitaryGroup`.) -/
theorem circuit_mem_unitaryGroup {K : ℕ} {S : Matrix H H ℂ}
    (hS : S ∈ Matrix.unitaryGroup H ℂ) (priv : H → Prop) [DecidablePred priv] :
    circuit K S priv ∈ Matrix.unitaryGroup (Fin K × H) ℂ := by
  sorry

/-- **The catalyst run** ([BJY23, proof of Theorem 5.5], from (5.6) to (5.8), without the
normalization `K^{-1/2}`). If `S` transduces `ξ` into `τ` with catalyst `v`, the `K` rounds map
`ξ` on every clock branch plus `v` on branch `0` to `τ` on every clock branch plus `v` on
branch `0`, exactly. After `t` rounds the state is `τ` on the branches `c < t`, `ξ` on the
branches `c ≥ t`, and `v` on branch `t mod K`. Unitarity of `S` is not needed. -/
theorem loop_catalyst {K : ℕ} (hK : 0 < K) {S : Matrix H H ℂ} {priv : H → Prop}
    [DecidablePred priv] {ξ τ v : H → ℂ} (h : Transduces priv S ξ τ v) :
    loop K S priv K *ᵥ ((∑ c : Fin K, clockVec c ξ) + clockVec ⟨0, hK⟩ v)
      = (∑ c : Fin K, clockVec c τ) + clockVec ⟨0, hK⟩ v := by
  sorry

/-- **[BJY23, Theorem 5.5], as linear algebra.** Let `S` be a unitary on `H`, `priv` a privacy
predicate on the basis of `H`, and `0 < K`. If `S` transduces `ξ` into `τ` with catalyst `v`
(`Transduces`), then the algorithm `circuit K S priv`, which applies `S` `K` times under control,
maps `|0⟩ ⊗ ξ` to within `2‖v‖/√K` of `|0⟩ ⊗ τ`:

  `‖circuit K S priv (|0⟩ ⊗ ξ) − |0⟩ ⊗ τ‖ ≤ 2‖v‖/√K`.

The catalyst `v` is arbitrary (any `v` satisfying the hypotheses); in [BJY23] the bound is stated
with `W(S, ξ) = ‖v‖²` for the minimal catalyst. -/
theorem circuit_close {K : ℕ} (hK : 0 < K) {S : Matrix H H ℂ}
    (hS : S ∈ Matrix.unitaryGroup H ℂ) (priv : H → Prop) [DecidablePred priv]
    {ξ τ v : H → ℂ} (h : Transduces priv S ξ τ v) :
    qNorm (circuit K S priv *ᵥ clockVec ⟨0, hK⟩ ξ - clockVec ⟨0, hK⟩ τ)
      ≤ 2 * qNorm v / Real.sqrt K := by
  sorry

end Circuit

/-! ## Embedding a smaller basis -/

/-- A vector on a basis `V`, carried into a basis `B` along a map `e : V → B`:
`embedVia e ψ = ∑ₓ ψ x · |e x⟩`. For injective `e` it is a linear isometry onto the span of the
image of `e`. Typically `V` is a logical register and `e x` is the basis state that holds `x`
there, with every other register in a fixed clean state. -/
noncomputable def embedVia {V B : Type} [Fintype V] [DecidableEq B] (e : V → B) (ψ : V → ℂ) :
    B → ℂ :=
  ∑ x, ψ x • qBasis (e x)

section EmbedVia

variable {V B : Type} [Fintype V] [DecidableEq B]

/-- A basis vector is carried to the basis vector of its image: `embedVia e |x⟩ = |e x⟩`. -/
theorem embedVia_qBasis [DecidableEq V] (e : V → B) (x : V) :
    embedVia e (qBasis x) = qBasis (e x) := by
  sorry

/-- `embedVia e` is linear: it commutes with scalar multiplication. -/
theorem embedVia_smul (e : V → B) (z : ℂ) (ψ : V → ℂ) :
    embedVia e (z • ψ) = z • embedVia e ψ := by
  sorry

/-- `embedVia e` is linear: it commutes with addition. -/
theorem embedVia_add (e : V → B) (ψ φ : V → ℂ) :
    embedVia e (ψ + φ) = embedVia e ψ + embedVia e φ := by
  sorry

/-- For injective `e`, `embedVia e ψ` has the amplitude `ψ x` at `e x`. -/
theorem embedVia_apply_self {e : V → B} (he : Function.Injective e) (ψ : V → ℂ) (x : V) :
    embedVia e ψ (e x) = ψ x := by
  sorry

/-- `embedVia e ψ` vanishes off the image of `e`. -/
theorem embedVia_apply_of_forall_ne (e : V → B) (ψ : V → ℂ) {b : B} (hb : ∀ x, e x ≠ b) :
    embedVia e ψ b = 0 := by
  sorry

/-- For injective `e`, `embedVia e` is an isometry: `‖embedVia e ψ‖ = ‖ψ‖`. -/
theorem qNorm_embedVia [Fintype B] {e : V → B} (he : Function.Injective e) (ψ : V → ℂ) :
    qNorm (embedVia e ψ) = qNorm ψ := by
  sorry

end EmbedVia

end Transducer

/-! ## The routine form -/

section Routine

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-- **The routine runs the algorithm of [BJY23, Theorem 5.5] on the clocked sector.** For a
routine `R`, a privacy predicate `priv` on its basis states and a clock size `K`, there is one
routine `T` on the clocked workspace `ClockWork ι K W` (control bit, parking slot, clock register
`Fin K`, then `W`), fixed before the input, with exactly `K · R.len` queries, such that on every
input `a` it acts on the clocked sector (control bit `false`, parking slot blank) as
`Transducer.circuit K (R.run a) priv`: a vector `Φ` on `Fin K × QBasis ι σ W`, packed into the
clock branches by `clockPack`, is mapped to the packing of `circuit K (R.run a) priv *ᵥ Φ`.

The statement fixes only the length of `T` and its action on the clocked sector. The proof is
expected to build `T` as `clockOp K (fourierMat K)`, then `K` rounds, then the adjoint
`clockOp`. Round `t` runs `QRoutine.control` of `R` lifted to the clock register
(`QRoutine.liftReg`; no extra query) between two free basis permutations that flip the control
bit on the clock branch `t`, and then the free basis permutation that advances the clock as
`Transducer.tick` does, reading `priv` on the rest of the basis state. For `K = 0` both sides
are `0`. -/
theorem exists_transducerRoutine_encoded (R : QRoutine ι σ W) (priv : QBasis ι σ W → Prop)
    [DecidablePred priv] (K : ℕ) :
    ∃ T : QRoutine ι σ (ClockWork ι K W), T.len = K * R.len ∧
      ∀ (a : ι → σ) (Φ : Fin K × QBasis ι σ W → ℂ),
        T.run a *ᵥ clockPack (fun c p => Φ (c, p))
          = clockPack (fun c p => (Transducer.circuit K (R.run a) priv *ᵥ Φ) (c, p)) := by
  sorry

/-- **[BJY23, Theorem 5.5], routine form.** Let `R` be a routine with `R.len` queries, `priv` a
privacy predicate on its basis states, and `0 < K`. There is one routine `T`, fixed before the
input, on the clocked workspace `ClockWork ι K W` (control bit, parking slot, clock register
`Fin K`, then `W`), with exactly `K · R.len` queries, such that for every input `a` and all
vectors `ξ`, `τ`, `v` on the basis of `R` with `ξ`, `τ` public, `v` private and
`R.run a (ξ + v) = τ + v` (`Transduces`),

  `‖T.run a (|0⟩ ⊗ ξ) − |0⟩ ⊗ τ‖ ≤ 2‖v‖/√K`,

where `|0⟩ ⊗ ψ` is `embedClock ⟨0, hK⟩ false ψ`: clock `0`, control bit `false`, parking slot
blank.

The catalyst `v` may depend on the input and need not be minimal. `R.run a` is unitary on the
whole basis, so no unitarity hypothesis is needed, and no decidability of `priv` is assumed (the
proof may decide it classically). Only the length of `T` and the bound are stated;
`exists_transducerRoutine_encoded` describes the intended construction.
`sqrt_qProb_le_add` turns the bound into a lower bound on outcome probabilities. -/
theorem exists_transducerRoutine (R : QRoutine ι σ W) (priv : QBasis ι σ W → Prop)
    {K : ℕ} (hK : 0 < K) :
    ∃ T : QRoutine ι σ (ClockWork ι K W), T.len = K * R.len ∧
      ∀ (a : ι → σ) (ξ τ v : QBasis ι σ W → ℂ), Transduces priv (R.run a) ξ τ v →
        qNorm (T.run a *ᵥ embedClock ⟨0, hK⟩ false ξ - embedClock ⟨0, hK⟩ false τ)
          ≤ 2 * qNorm v / Real.sqrt K := by
  sorry

/-- **[BJY23, Theorem 5.5] for a realized transducer.** Let `R` be a routine with `R.len`
queries, `e : V → QBasis ι σ W` an injective map from a smaller basis `V` into the routine's
basis, `priv` a privacy predicate on `V`, and `0 < K`. There is one routine `T`, fixed before the
input, on the clocked workspace `ClockWork ι K W`, with exactly `K · R.len` queries, such that
for every input `a` and every matrix `S` on `V` that `R` realizes on that input along `e`
(`R.run a (embedVia e ψ) = embedVia e (S ψ)` for every `ψ`), and every transduction
`S (ξ + v) = τ + v` on `V` (`Transduces priv S ξ τ v`),

  `‖T.run a (|0⟩ ⊗ e ξ) − |0⟩ ⊗ e τ‖ ≤ 2‖v‖/√K`,

where `|0⟩ ⊗ e ψ` is `embedClock ⟨0, hK⟩ false (embedVia e ψ)`.

`S` may depend on the input; it need not be assumed unitary, since `R.run a` is unitary and
`e` is injective. No decidability of `priv` is assumed. `T` is chosen before the input and
before `S`: it depends on `R`, `e`, `priv` and `K` only. -/
theorem exists_transducerRoutine_of_realizes (R : QRoutine ι σ W) {V : Type} [Fintype V]
    (e : V → QBasis ι σ W) (he : Function.Injective e) (priv : V → Prop) {K : ℕ} (hK : 0 < K) :
    ∃ T : QRoutine ι σ (ClockWork ι K W), T.len = K * R.len ∧
      ∀ (a : ι → σ) (S : Matrix V V ℂ),
        (∀ ψ : V → ℂ, R.run a *ᵥ Transducer.embedVia e ψ = Transducer.embedVia e (S *ᵥ ψ)) →
        ∀ ξ τ v : V → ℂ, Transduces priv S ξ τ v →
          qNorm (T.run a *ᵥ embedClock ⟨0, hK⟩ false (Transducer.embedVia e ξ)
              - embedClock ⟨0, hK⟩ false (Transducer.embedVia e τ))
            ≤ 2 * qNorm v / Real.sqrt K := by
  sorry

end Routine

end QuantumQueryComplexity
