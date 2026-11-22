import QuantumQueryComplexity.Quantum.Amplitude.PhaseEstimation
import QuantumQueryComplexity.Quantum.Approximation
import QuantumQueryComplexity.Quantum.KronLift

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

The routine is `Transducer.routine R priv K`. It runs `QRoutine.control` of `R` lifted to the
clock once per clock value (`Transducer.ctrlRound`: as `clockRound` in `Clock.lean`, but on the
branch `c = t`), each round followed by the permutation `tick` (`Transducer.loopRoutine`),
between `clockOp K (fourierMat K)` and its adjoint. `Transducer.ActsOnClock` records how a
routine acts on the clocked sector; the proof of `exists_transducerRoutine_encoded` composes
these actions, and the routine form then follows from `Transducer.circuit_close`.

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

/-! ### Unitarity -/

/-- `ctrlAt K t S` is block diagonal over the clock: on branch `c` it applies `S` if `c = t`
and the identity otherwise. -/
theorem ctrlAt_mulVec_apply {K : ℕ} (t : ℕ) (S : Matrix H H ℂ) (f : Fin K × H → ℂ)
    (c : Fin K) (h : H) :
    (ctrlAt K t S *ᵥ f) (c, h) =
      if (c : ℕ) = t then (S *ᵥ fun j => f (c, j)) h else f (c, h) := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_eq_single c]
  · by_cases hc : (c : ℕ) = t
    · simp [ctrlAt, hc, Matrix.mulVec, dotProduct]
    · simp [ctrlAt, hc, Matrix.one_apply, ite_mul]
  · intro d _ hd
    simp [ctrlAt, Ne.symm hd]
  · simp

/-- `ctrlAt K t S` is unitary when `S` is: it is a block diagonal of copies of `S` and `1`. -/
theorem ctrlAt_mem_unitaryGroup (K t : ℕ) {S : Matrix H H ℂ}
    (hS : S ∈ Matrix.unitaryGroup H ℂ) :
    ctrlAt K t S ∈ Matrix.unitaryGroup (Fin K × H) ℂ := by
  let f (c : Fin K) : Matrix H H ℂ := if (c : ℕ) = t then S else 1
  have hf (c : Fin K) : f c ∈ Matrix.unitaryGroup H ℂ := by
    dsimp only [f]
    split_ifs
    · exact hS
    · exact one_mem _
  have hblocks : ctrlAt K t S =
      (Matrix.blockDiagonal f).submatrix (Equiv.prodComm (Fin K) H)
        (Equiv.prodComm (Fin K) H) := by
    ext ⟨c, i⟩ ⟨d, j⟩
    by_cases hcd : c = d
    · subst d
      by_cases ht : (c : ℕ) = t <;> simp [ctrlAt, Matrix.blockDiagonal_apply, f, ht]
    · simp [ctrlAt, Matrix.blockDiagonal_apply, hcd]
  rw [hblocks, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
  have hprod : (fun c => (f c)ᴴ * f c) = (1 : Fin K → Matrix H H ℂ) :=
    funext fun c => conjTranspose_mul_self_of_unitary (hf c)
  rw [hprod, Matrix.blockDiagonal_one, Matrix.submatrix_one_equiv]

/-- The first `n` rounds are unitary when `S` is. -/
theorem loop_mem_unitaryGroup (K : ℕ) {S : Matrix H H ℂ} (hS : S ∈ Matrix.unitaryGroup H ℂ)
    (priv : H → Prop) [DecidablePred priv] (n : ℕ) :
    loop K S priv n ∈ Matrix.unitaryGroup (Fin K × H) ℂ := by
  induction n with
  | zero => exact one_mem _
  | succ n ih =>
    exact mul_mem (qPerm_mem_unitaryGroup _) (mul_mem (ctrlAt_mem_unitaryGroup _ _ hS) ih)

omit [Fintype H] [DecidableEq H] in
/-- `fourierMat K` is unitary for every `K` (for `K = 0` the index type is empty). -/
theorem fourierMat_mem_unitaryGroup_nat (K : ℕ) :
    fourierMat K ∈ Matrix.unitaryGroup (Fin K) ℂ := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · rw [Subsingleton.elim (fourierMat 0) 1]
    exact one_mem _
  · exact fourierMat_mem_unitaryGroup hK

/-- The clock preparation is unitary. -/
theorem prep_mem_unitaryGroup (K : ℕ) :
    prep (H := H) K ∈ Matrix.unitaryGroup (Fin K × H) ℂ :=
  kronLift_mem_unitaryGroup (Equiv.refl _) (fourierMat_mem_unitaryGroup_nat K)

/-- The algorithm is unitary when `S` is unitary. (For `K = 0` the index type `Fin 0 × H` is
empty and the statement is trivial; for `0 < K` it uses `fourierMat_mem_unitaryGroup`.) -/
theorem circuit_mem_unitaryGroup {K : ℕ} {S : Matrix H H ℂ}
    (hS : S ∈ Matrix.unitaryGroup H ℂ) (priv : H → Prop) [DecidablePred priv] :
    circuit K S priv ∈ Matrix.unitaryGroup (Fin K × H) ℂ :=
  mul_mem (conjTranspose_mem_qUnitary (prep_mem_unitaryGroup K))
    (mul_mem (loop_mem_unitaryGroup K hS priv K) (prep_mem_unitaryGroup K))

/-! ### The catalyst run -/

/-- **The state of the catalyst run** after `n` rounds, with the catalyst on clock branch `k`:
`τ` on the branches `c < n`, `ξ` on the branches `c ≥ n`, plus `v` on branch `k`. -/
def catalystStage {K : ℕ} (n : ℕ) (k : Fin K) (ξ τ v : H → ℂ) : Fin K × H → ℂ :=
  fun x => (if (x.1 : ℕ) < n then τ x.2 else ξ x.2) + clockVec k v x

/-- Step 2(a) of round `k` on the catalyst run: the catalyst sits on branch `k` together with
`ξ`, and `S` turns `ξ + v` into `τ + v` there. -/
theorem ctrlAt_mulVec_catalystStage {K : ℕ} {S : Matrix H H ℂ} {priv : H → Prop}
    {ξ τ v : H → ℂ} (h : Transduces priv S ξ τ v) (k : Fin K) :
    ctrlAt K k S *ᵥ catalystStage k k ξ τ v = catalystStage (k + 1) k ξ τ v := by
  funext ⟨c, j⟩
  rw [ctrlAt_mulVec_apply]
  by_cases hc : c = k
  · subst c
    simpa [catalystStage, clockVec, Pi.add_def] using congrFun h.mulVec_eq j
  · have hne : (c : ℕ) ≠ k := fun eq => hc (Fin.ext eq)
    have hlt : (c : ℕ) < k + 1 ↔ (c : ℕ) < k := by omega
    simp [catalystStage, clockVec, hc, hne, hlt]

/-- Step 2(b) on the catalyst run: the advance moves the private catalyst from branch `k` to
branch `k + 1 mod K` and leaves the public `ξ` and `τ` in place. -/
theorem tick_mulVec_catalystStage {K : ℕ} {S : Matrix H H ℂ} {priv : H → Prop}
    [DecidablePred priv] {ξ τ v : H → ℂ} (h : Transduces priv S ξ τ v) (n : ℕ) (k : Fin K) :
    qPerm (tick K priv) *ᵥ catalystStage n k ξ τ v = catalystStage n (finRotate K k) ξ τ v := by
  funext ⟨c, j⟩
  rw [qPerm_mulVec_apply]
  by_cases hp : priv j
  · have heq : (finRotate K).symm c = k ↔ c = finRotate K k := (finRotate K).symm_apply_eq
    simp only [tick, catalystStage, clockVec, Equiv.coe_fn_symm_mk, hp, ite_true,
      h.source_public j hp, h.target_public j hp, ite_self, zero_add, heq]
  · simp [tick, catalystStage, clockVec, hp, h.catalyst_private j hp]

open scoped Fin.NatCast in
/-- **The invariant of the catalyst run**: after `n ≤ K` rounds the state is `τ` on the
branches `c < n`, `ξ` on the others, and `v` on branch `n mod K`. -/
theorem loop_mulVec_catalystStage {K : ℕ} [NeZero K] {S : Matrix H H ℂ} {priv : H → Prop}
    [DecidablePred priv] {ξ τ v : H → ℂ} (h : Transduces priv S ξ τ v) (n : ℕ) (hn : n ≤ K) :
    loop K S priv n *ᵥ catalystStage 0 ((0 : ℕ) : Fin K) ξ τ v
      = catalystStage n (n : Fin K) ξ τ v := by
  induction n with
  | zero => simp [loop]
  | succ n ih =>
    have hn' : n < K := by omega
    have hval : ((n : Fin K) : ℕ) = n := by simp [Nat.mod_eq_of_lt hn']
    have hstep := ctrlAt_mulVec_catalystStage h (n : Fin K)
    rw [hval] at hstep
    rw [loop, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih hn'.le, hstep,
      tick_mulVec_catalystStage h]
    simp

open scoped Fin.NatCast in
/-- The whole catalyst run: after the `K` rounds the catalyst is back on clock branch `0`. -/
theorem loop_mulVec_catalystStage_self {K : ℕ} (hK : 0 < K) {S : Matrix H H ℂ}
    {priv : H → Prop} [DecidablePred priv] {ξ τ v : H → ℂ} (h : Transduces priv S ξ τ v) :
    loop K S priv K *ᵥ catalystStage 0 ⟨0, hK⟩ ξ τ v = catalystStage K ⟨0, hK⟩ ξ τ v := by
  have : NeZero K := ⟨hK.ne'⟩
  have h0 : ((0 : ℕ) : Fin K) = ⟨0, hK⟩ := Fin.ext (by simp)
  have hK' : ((K : ℕ) : Fin K) = ⟨0, hK⟩ := Fin.ext (by simp)
  rw [← h0, loop_mulVec_catalystStage h K le_rfl, hK', h0]

/-- **The catalyst run** ([BJY23, proof of Theorem 5.5], from (5.6) to (5.8), without the
normalization `K^{-1/2}`). If `S` transduces `ξ` into `τ` with catalyst `v`, the `K` rounds map
`ξ` on every clock branch plus `v` on branch `0` to `τ` on every clock branch plus `v` on
branch `0`, exactly. After `t` rounds the state is `τ` on the branches `c < t`, `ξ` on the
branches `c ≥ t`, and `v` on branch `t mod K`. Unitarity of `S` is not needed. -/
theorem loop_catalyst {K : ℕ} (hK : 0 < K) {S : Matrix H H ℂ} {priv : H → Prop}
    [DecidablePred priv] {ξ τ v : H → ℂ} (h : Transduces priv S ξ τ v) :
    loop K S priv K *ᵥ ((∑ c : Fin K, clockVec c ξ) + clockVec ⟨0, hK⟩ v)
      = (∑ c : Fin K, clockVec c τ) + clockVec ⟨0, hK⟩ v := by
  have hstart : (∑ c : Fin K, clockVec c ξ) + clockVec ⟨0, hK⟩ v
      = catalystStage 0 ⟨0, hK⟩ ξ τ v := by
    funext ⟨c, j⟩
    simp only [catalystStage, Pi.add_apply]
    congr 1
    simp [Finset.sum_apply, clockVec]
  have hfinish : (∑ c : Fin K, clockVec c τ) + clockVec ⟨0, hK⟩ v
      = catalystStage K ⟨0, hK⟩ ξ τ v := by
    funext ⟨c, j⟩
    simp only [catalystStage, Pi.add_apply]
    congr 1
    simp [Finset.sum_apply, clockVec, c.isLt]
  rw [hstart, hfinish]
  exact loop_mulVec_catalystStage_self hK h

/-! ### The error bound -/

/-- The clock preparation maps `|0⟩ ⊗ ψ` to `K^{-1/2} ∑_c |c⟩ ⊗ ψ`. -/
theorem prep_mulVec_clockVec_zero {K : ℕ} (hK : 0 < K) (ψ : H → ℂ) :
    prep K *ᵥ clockVec ⟨0, hK⟩ ψ =
      (((Real.sqrt K)⁻¹ : ℝ) : ℂ) • ∑ c : Fin K, clockVec c ψ := by
  funext ⟨c, h⟩
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Finset.sum_eq_single (⟨0, hK⟩ : Fin K)]
  · simp [prep, clockVec, Matrix.one_apply, fourierMat_apply, ite_mul, mul_ite,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  · intro d _ hd
    simp [clockVec, hd]
  · simp

/-- `|c⟩ ⊗ ψ` has the norm of `ψ`. -/
theorem qNorm_clockVec {K : ℕ} (c : Fin K) (ψ : H → ℂ) :
    qNorm (clockVec c ψ) = qNorm ψ := by
  unfold qNorm
  congr 1
  rw [qNormSq_def, Fintype.sum_prod_type, Finset.sum_eq_single c]
  · simp [clockVec, qNormSq_def]
  · intro d _ hd
    simp [clockVec, hd]
  · simp

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
  let P := prep (H := H) K
  let U := loop K S priv K
  let α : ℂ := (((Real.sqrt K)⁻¹ : ℝ) : ℂ)
  let x := clockVec ⟨0, hK⟩ ξ
  let y := clockVec ⟨0, hK⟩ τ
  -- The perturbation: the catalyst on clock branch `0`, scaled as the prepared clock.
  let d := α • clockVec ⟨0, hK⟩ v
  have hP : P ∈ Matrix.unitaryGroup _ ℂ := prep_mem_unitaryGroup K
  have hU : U ∈ Matrix.unitaryGroup _ ℂ := loop_mem_unitaryGroup K hS priv K
  -- With the perturbation added, the loop runs exactly (`loop_catalyst`).
  have hexact : U *ᵥ (P *ᵥ x) + U *ᵥ d = P *ᵥ y + d := by
    rw [← Matrix.mulVec_add]
    dsimp only [P, U, x, y, d, α]
    rw [prep_mulVec_clockVec_zero hK, prep_mulVec_clockVec_zero hK, ← smul_add,
      Matrix.mulVec_smul, loop_catalyst hK h, smul_add]
  have hdiff : U *ᵥ (P *ᵥ x) - P *ᵥ y = d - U *ᵥ d := by
    calc
      _ = (U *ᵥ (P *ᵥ x) + U *ᵥ d) - (P *ᵥ y + U *ᵥ d) := by abel
      _ = _ := by rw [hexact]; abel
  have hreturn : circuit K S priv *ᵥ x - y = Pᴴ *ᵥ (d - U *ᵥ d) := by
    rw [← hdiff, Matrix.mulVec_sub, Matrix.mulVec_mulVec y Pᴴ P,
      conjTranspose_mul_self_of_unitary hP, Matrix.one_mulVec, circuit,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hd : qNorm d = qNorm v / Real.sqrt K := by
    dsimp only [d, α]
    rw [qNorm_smul, qNorm_clockVec, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), div_eq_mul_inv, mul_comm]
  change qNorm (circuit K S priv *ᵥ x - y) ≤ _
  rw [hreturn, qNorm_mulVec (conjTranspose_mem_qUnitary hP)]
  calc
    _ ≤ qNorm d + qNorm (U *ᵥ d) := qNorm_sub_le _ _
    _ = _ := by rw [qNorm_mulVec hU, hd]; ring

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
  unfold embedVia
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

/-- `embedVia e` is linear: it commutes with scalar multiplication. -/
theorem embedVia_smul (e : V → B) (z : ℂ) (ψ : V → ℂ) :
    embedVia e (z • ψ) = z • embedVia e ψ := by
  simp only [embedVia, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]

/-- `embedVia e` is linear: it commutes with addition. -/
theorem embedVia_add (e : V → B) (ψ φ : V → ℂ) :
    embedVia e (ψ + φ) = embedVia e ψ + embedVia e φ := by
  simp only [embedVia, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- For injective `e`, `embedVia e ψ` has the amplitude `ψ x` at `e x`. -/
theorem embedVia_apply_self {e : V → B} (he : Function.Injective e) (ψ : V → ℂ) (x : V) :
    embedVia e ψ (e x) = ψ x := by
  classical
  simp [embedVia, Finset.sum_apply, qBasis, Pi.single_apply, he.eq_iff, mul_ite]

/-- `embedVia e ψ` vanishes off the image of `e`. -/
theorem embedVia_apply_of_forall_ne (e : V → B) (ψ : V → ℂ) {b : B} (hb : ∀ x, e x ≠ b) :
    embedVia e ψ b = 0 := by
  simp [embedVia, Finset.sum_apply, qBasis, fun x => (hb x).symm]

/-- For injective `e`, `embedVia e` is an isometry: `‖embedVia e ψ‖ = ‖ψ‖`. -/
theorem qNorm_embedVia [Fintype B] {e : V → B} (he : Function.Injective e) (ψ : V → ℂ) :
    qNorm (embedVia e ψ) = qNorm ψ := by
  classical
  unfold qNorm
  congr 1
  rw [qNormSq_def, qNormSq_def]
  calc
    _ = ∑ b ∈ Finset.univ.image e, Complex.normSq (embedVia e ψ b) := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) ?_
      intro b _ hb
      have hne : ∀ x, e x ≠ b := by
        rintro x rfl
        exact hb (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
      rw [embedVia_apply_of_forall_ne e ψ hne, Complex.normSq_zero]
    _ = _ := by
      rw [Finset.sum_image (fun _ _ _ _ eq => he eq)]
      simp only [embedVia_apply_self he]

end EmbedVia

end Transducer

/-! ## The routine form -/

section Routine

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

namespace Transducer

/-! ### The clocked sector -/

/-- The basis of the clocked workspace, split into the basis `Fin K × QBasis ι σ W` of the
clocked sector (clock, then the routine's basis) and the control bit with the parking slot. -/
def clockSplit (K : ℕ) :
    QBasis ι σ (ClockWork ι K W) ≃ (Fin K × QBasis ι σ W) × (Bool × Option ι) where
  toFun | (i, z, b, s, c, w) => ((c, i, z, w), b, s)
  invFun | ((c, i, z, w), b, s) => (i, z, b, s, c, w)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A packed vector is the clocked-sector vector next to control bit `false` and a blank
parking slot. -/
theorem clockPack_eq_splitVec {K : ℕ} (Φ : Fin K × QBasis ι σ W → ℂ) :
    clockPack (fun c p => Φ (c, p)) = splitVec (clockSplit K) Φ (qBasis (false, none)) := by
  funext ⟨i, z, b, s, c, w⟩
  by_cases hb : b = false <;> by_cases hs : s = none <;>
    simp [clockPack, Finset.sum_apply, embedClock_apply, splitVec, clockSplit, hb, hs]

/-- Packing preserves distances. -/
theorem qNorm_clockPack_sub {K : ℕ} (Φ Ψ : Fin K × QBasis ι σ W → ℂ) :
    qNorm (clockPack (fun c p => Φ (c, p)) - clockPack (fun c p => Ψ (c, p))) =
      qNorm (Φ - Ψ) := by
  rw [clockPack_eq_splitVec, clockPack_eq_splitVec]
  have hsub : splitVec (clockSplit K) Φ (qBasis (false, none))
      - splitVec (clockSplit K) Ψ (qBasis (false, none))
      = splitVec (clockSplit K) (Φ - Ψ) (qBasis (false, none)) := by
    funext p
    simp only [splitVec_apply, Pi.sub_apply, sub_mul]
  rw [hsub, qNorm, qNormSq_splitVec, qNormSq_qBasis, mul_one, qNorm]

/-- The packing of `|c⟩ ⊗ ψ` is the clock-`c` embedding of `ψ`. -/
theorem clockPack_clockVec {K : ℕ} (c : Fin K) (ψ : QBasis ι σ W → ℂ) :
    clockPack (fun d p => clockVec c ψ (d, p)) = embedClock c false ψ := by
  unfold clockPack
  rw [Finset.sum_eq_single c]
  · simp [clockVec]
  · intro d _ hd
    funext p
    simp [embedClock_apply, clockVec, hd]
  · simp

/-- **`T` acts on the clocked sector as `F a`** on every input `a`: it maps the packing of
every `Φ` on `Fin K × QBasis ι σ W` to the packing of `F a *ᵥ Φ`. -/
def ActsOnClock {K : ℕ} (T : QRoutine ι σ (ClockWork ι K W))
    (F : (ι → σ) → Matrix (Fin K × QBasis ι σ W) (Fin K × QBasis ι σ W) ℂ) : Prop :=
  ∀ a Φ, T.run a *ᵥ clockPack (fun c p => Φ (c, p)) =
    clockPack (fun c p => (F a *ᵥ Φ) (c, p))

/-- Running `T` and then `T'` acts as the product of their actions. -/
theorem ActsOnClock.comp {K : ℕ} {T T' : QRoutine ι σ (ClockWork ι K W)} {F G}
    (hT : ActsOnClock T F) (hT' : ActsOnClock T' G) :
    ActsOnClock (T.comp T') (fun a => G a * F a) := by
  intro a Φ
  rw [QRoutine.comp_run, ← Matrix.mulVec_mulVec, hT a Φ, hT' a (F a *ᵥ Φ),
    ← Matrix.mulVec_mulVec]

/-- **A free gate on the clocked sector**: the zero-query routine that applies the unitary `A`
to the clock and the routine's basis, and the identity to the control bit and the parking
slot. -/
noncomputable def clockGate {K : ℕ}
    (A : Matrix (Fin K × QBasis ι σ W) (Fin K × QBasis ι σ W) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin K × QBasis ι σ W) ℂ) :
    QRoutine ι σ (ClockWork ι K W) :=
  QRoutine.ofUnitary (kronLift (clockSplit K) A) (kronLift_mem_unitaryGroup (clockSplit K) hA)

/-- A free gate makes no query. -/
theorem clockGate_len {K : ℕ} (A : Matrix (Fin K × QBasis ι σ W) (Fin K × QBasis ι σ W) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin K × QBasis ι σ W) ℂ) :
    (clockGate A hA).len = 0 := rfl

/-- A free gate acts on the clocked sector as its matrix. -/
theorem clockGate_acts {K : ℕ}
    (A : Matrix (Fin K × QBasis ι σ W) (Fin K × QBasis ι σ W) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin K × QBasis ι σ W) ℂ) :
    ActsOnClock (clockGate A hA) (fun _ => A) := by
  intro a Φ
  rw [clockGate, QRoutine.ofUnitary_run, clockPack_eq_splitVec, kronLift_mulVec_splitVec,
    clockPack_eq_splitVec]

/-- **The clock preparation as a routine**: `clockOp K A` (the operator `A` on the clock
register alone) acts on the clocked sector as `A ⊗ 1`, the shape of `prep K`. -/
theorem clockOp_acts {K : ℕ} (A : Matrix (Fin K) (Fin K) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin K) ℂ) :
    ActsOnClock (QRoutine.ofUnitary (clockOp (ι := ι) (σ := σ) (W := W) K A)
        (clockOp_mem_unitaryGroup hA))
      (fun _ => Matrix.kroneckerMap (· * ·) A (1 : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)) := by
  intro a Φ
  rw [QRoutine.ofUnitary_run, clockOp_mulVec_clockPack]
  congr 1
  funext c p
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [Matrix.one_apply, mul_ite, ite_mul]

/-! ### One round -/

/-- Flip the control bit exactly on the branch whose clock reads `t`. -/
def ctrlFlipMap {K : ℕ} (t : ℕ) :
    QBasis ι σ (ClockWork ι K W) → QBasis ι σ (ClockWork ι K W)
  | (i, z, b, s, c, w) => (i, z, xor b (decide ((c : ℕ) = t)), s, c, w)

/-- Flipping twice restores the control bit. -/
theorem ctrlFlipMap_involutive {K : ℕ} (t : ℕ) :
    Function.Involutive (ctrlFlipMap (ι := ι) (σ := σ) (W := W) (K := K) t) := by
  rintro ⟨i, z, b, s, c, w⟩
  change ((i, z, xor (xor b (decide ((c : ℕ) = t))) (decide ((c : ℕ) = t)), s, c, w) :
    QBasis ι σ (ClockWork ι K W)) = (i, z, b, s, c, w)
  rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The control-bit flip on clock branch `t`, as a zero-query routine (a basis permutation). -/
def ctrlFlip {K : ℕ} (t : ℕ) : QRoutine ι σ (ClockWork ι K W) :=
  QRoutine.ofUnitary (qPerm ((ctrlFlipMap_involutive t).toPerm _)) (qPerm_mem_unitaryGroup _)

/-- The flip reads the clock and touches nothing else. -/
theorem ctrlFlip_run_embedClock {K : ℕ} (t : ℕ) (a : ι → σ) (c : Fin K) (b : Bool)
    (ψ : QBasis ι σ W → ℂ) :
    (ctrlFlip t).run a *ᵥ embedClock c b ψ = embedClock c (xor b (decide ((c : ℕ) = t))) ψ := by
  funext ⟨i, z, d, s, c', w⟩
  rw [ctrlFlip, QRoutine.ofUnitary_run, qPerm_mulVec_apply, embedClock_apply, embedClock_apply]
  change (if xor d (decide ((c' : ℕ) = t)) = b ∧ s = none ∧ c' = c then ψ (i, z, w) else 0) =
    (if d = xor b (decide ((c : ℕ) = t)) ∧ s = none ∧ c' = c then ψ (i, z, w) else 0)
  by_cases hc : c' = c
  · subst c'
    cases b <;> cases d <;> cases (decide ((c : ℕ) = t)) <;> simp
  · simp [hc]

/-- **Step 2(a) as a routine**: `R`, controlled on the clock value `t`. It runs
`QRoutine.control` of `R` lifted to the clock register between two flips of the control bit
on clock branch `t`, so it costs exactly `R.len` queries. -/
noncomputable def ctrlRound (R : QRoutine ι σ W) (K t : ℕ) : QRoutine ι σ (ClockWork ι K W) :=
  ((ctrlFlip t).comp (R.liftReg (Fin K)).control).comp (ctrlFlip t)

/-- One round costs exactly the queries of `R`. -/
theorem ctrlRound_len (R : QRoutine ι σ W) (K t : ℕ) : (ctrlRound R K t).len = R.len := by
  simp [ctrlRound, ctrlFlip, control_len]

/-- `ctrlRound R K t` runs `R` on the clock branch `t` and leaves the other branches alone. -/
theorem ctrlRound_run_embedClock (R : QRoutine ι σ W) (a : ι → σ) {K : ℕ} (t : ℕ) (c : Fin K)
    (ψ : QBasis ι σ W → ℂ) :
    (ctrlRound R K t).run a *ᵥ embedClock c false ψ =
      embedClock c false (if (c : ℕ) = t then R.run a *ᵥ ψ else ψ) := by
  rw [ctrlRound, QRoutine.comp_run, QRoutine.comp_run, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ctrlFlip_run_embedClock, Bool.false_xor]
  by_cases hc : (c : ℕ) = t
  · simp only [hc, decide_true, ite_true]
    rw [embedClock, control_run_true, QRoutine.liftReg_run_embed]
    change (ctrlFlip t).run a *ᵥ embedClock c true (R.run a *ᵥ ψ) = _
    rw [ctrlFlip_run_embedClock]
    simp [hc]
  · simp only [hc, decide_false, ite_false]
    rw [embedClock, control_run_false]
    change (ctrlFlip t).run a *ᵥ embedClock c false ψ = _
    rw [ctrlFlip_run_embedClock]
    simp [hc, embedClock]

/-- On the clocked sector, `ctrlRound R K t` acts as `ctrlAt K t (R.run a)`. -/
theorem ctrlRound_acts (R : QRoutine ι σ W) (K t : ℕ) :
    ActsOnClock (ctrlRound R K t) (fun a => ctrlAt K t (R.run a)) := by
  intro a Φ
  unfold clockPack
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ctrlRound_run_embedClock]
  congr 1
  funext h
  dsimp only
  rw [ctrlAt_mulVec_apply]
  split <;> rfl

/-! ### The whole routine -/

/-- **The first `n` rounds as a routine**: round `t` is `ctrlRound R K t` followed by the free
basis permutation `tick K priv` on the clocked sector. It costs exactly `n · R.len` queries. -/
noncomputable def loopRoutine (R : QRoutine ι σ W) (priv : QBasis ι σ W → Prop)
    [DecidablePred priv] (K : ℕ) : ℕ → QRoutine ι σ (ClockWork ι K W)
  | 0 => QRoutine.identity
  | n + 1 => ((loopRoutine R priv K n).comp (ctrlRound R K n)).comp
      (clockGate (qPerm (tick K priv)) (qPerm_mem_unitaryGroup _))

/-- `n` rounds cost exactly `n · R.len` queries. -/
theorem loopRoutine_len (R : QRoutine ι σ W) (priv : QBasis ι σ W → Prop) [DecidablePred priv]
    (K n : ℕ) : (loopRoutine R priv K n).len = n * R.len := by
  induction n with
  | zero => simp [loopRoutine]
  | succ n ih => simp [loopRoutine, ih, ctrlRound_len, clockGate_len, Nat.succ_mul]

/-- On the clocked sector, `loopRoutine R priv K n` acts as `loop K (R.run a) priv n`. -/
theorem loopRoutine_acts (R : QRoutine ι σ W) (priv : QBasis ι σ W → Prop) [DecidablePred priv]
    (K n : ℕ) : ActsOnClock (loopRoutine R priv K n) (fun a => loop K (R.run a) priv n) := by
  induction n with
  | zero => exact fun _ Φ => by simp [loopRoutine, loop]
  | succ n ih => exact (ih.comp (ctrlRound_acts R K n)).comp (clockGate_acts _ _)

/-- **The routine of [BJY23, Theorem 5.5]**: the clock preparation `clockOp K (fourierMat K)`,
the `K` rounds of `loopRoutine`, then the adjoint preparation. It is fixed before the input:
it depends on `R`, `priv` and `K` only. For `K = 0` the clock register is empty. -/
noncomputable def routine (R : QRoutine ι σ W) (priv : QBasis ι σ W → Prop)
    [DecidablePred priv] (K : ℕ) : QRoutine ι σ (ClockWork ι K W) :=
  ((QRoutine.ofUnitary (clockOp K (fourierMat K)) (clockOp_mem_unitaryGroup
      (fourierMat_mem_unitaryGroup_nat K))).comp (loopRoutine R priv K K)).comp
    (QRoutine.ofUnitary (clockOp K (fourierMat K)ᴴ) (clockOp_mem_unitaryGroup
      (conjTranspose_mem_qUnitary (fourierMat_mem_unitaryGroup_nat K))))

end Transducer

/-- **The routine runs the algorithm of [BJY23, Theorem 5.5] on the clocked sector.** For a
routine `R`, a privacy predicate `priv` on its basis states and a clock size `K`, there is one
routine `T` on the clocked workspace `ClockWork ι K W` (control bit, parking slot, clock register
`Fin K`, then `W`), fixed before the input, with exactly `K · R.len` queries, such that on every
input `a` it acts on the clocked sector (control bit `false`, parking slot blank) as
`Transducer.circuit K (R.run a) priv`: a vector `Φ` on `Fin K × QBasis ι σ W`, packed into the
clock branches by `clockPack`, is mapped to the packing of `circuit K (R.run a) priv *ᵥ Φ`.

The statement fixes only the length of `T` and its action on the clocked sector. The proof
builds `T` (`Transducer.routine`) as `clockOp K (fourierMat K)`, then `K` rounds, then the
adjoint `clockOp`. Round `t` runs `QRoutine.control` of `R` lifted to the clock register
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
  refine ⟨Transducer.routine R priv K, ?_, ?_⟩
  · simp [Transducer.routine, Transducer.loopRoutine_len]
  · have hacts := ((Transducer.clockOp_acts (ι := ι) (σ := σ) (W := W) _
      (Transducer.fourierMat_mem_unitaryGroup_nat K)).comp
      (Transducer.loopRoutine_acts R priv K K)).comp (Transducer.clockOp_acts _
        (conjTranspose_mem_qUnitary (Transducer.fourierMat_mem_unitaryGroup_nat K)))
    intro a Φ
    rw [Transducer.routine, hacts a Φ, Transducer.circuit, Transducer.prep,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

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
  classical
  obtain ⟨T, hlen, hact⟩ := exists_transducerRoutine_encoded R priv K
  refine ⟨T, hlen, fun a ξ τ v h => ?_⟩
  rw [← Transducer.clockPack_clockVec ⟨0, hK⟩ ξ, ← Transducer.clockPack_clockVec ⟨0, hK⟩ τ,
    hact a (Transducer.clockVec ⟨0, hK⟩ ξ), Transducer.qNorm_clockPack_sub]
  exact Transducer.circuit_close hK (R.run_mem_unitaryGroup a) priv h

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
  classical
  -- A basis state of `R` is private when it is the image of a private basis state of `V`.
  obtain ⟨T, hlen, hT⟩ := exists_transducerRoutine R (fun b => ∃ x, e x = b ∧ priv x) hK
  refine ⟨T, hlen, fun a S hreal ξ τ v h => ?_⟩
  rw [← Transducer.qNorm_embedVia he v]
  apply hT
  constructor
  · rintro b ⟨x, rfl, hx⟩
    rw [Transducer.embedVia_apply_self he, h.source_public x hx]
  · rintro b ⟨x, rfl, hx⟩
    rw [Transducer.embedVia_apply_self he, h.target_public x hx]
  · intro b hb
    by_cases hrange : ∃ x, e x = b
    · obtain ⟨x, rfl⟩ := hrange
      exact (Transducer.embedVia_apply_self he v x).trans
        (h.catalyst_private x fun hx => hb ⟨x, rfl, hx⟩)
    · exact Transducer.embedVia_apply_of_forall_ne e v fun x hx => hrange ⟨x, hx⟩
  · rw [← Transducer.embedVia_add, hreal, h.mulVec_eq, Transducer.embedVia_add]

end Routine

end QuantumQueryComplexity
