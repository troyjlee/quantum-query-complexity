import QuantumQueryComplexity.Quantum.Algorithm
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Bounded-error quantum query complexity

`qQueryOn read f ε` is the least number of queries with which some algorithm
computes `f` on the promise `read` with error at most `ε`, and
`boundedErrorQQueryOn` fixes the conventional `ε = 1/3`.

Two API shapes matter downstream and they are not symmetric:

* **Upper bounds** (`qQueryOn_le`) are unconditional: exhibiting one algorithm
  bounds the infimum.
* **Lower bounds** (`le_qQueryOn`) need the achievable set to be *nonempty*,
  because `sInf ∅ = 0` in `ℕ`.  The hypothesis is discharged once and for all by
  an exact algorithm for every observationally determined problem; until that is
  in place every lower bound carries `hne` explicitly rather than hiding the
  gap.
-/

namespace QuantumQueryComplexity

variable {ι σ O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [DecidableEq O]
variable {X : Type} [Fintype X]

/-- The set of query counts at which `f` is computable with error `≤ ε`.  The
workspace is existentially quantified here — this is the one place where that
costs anything, and it keeps `QAlg` free of a bundled type field. -/
def QueryCounts (read : X → ι → σ) (f : X → O) (ε : ℝ) : Set ℕ :=
  {q | ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (A : QAlg ι σ O W),
    ComputesWithErrorOn A q read f ε}

/-- **Bounded-error quantum query complexity on a promise.** -/
noncomputable def qQueryOn (read : X → ι → σ) (f : X → O) (ε : ℝ) : ℕ :=
  sInf (QueryCounts read f ε)

/-- The conventional error convention. -/
noncomputable abbrev boundedErrorQQueryOn (read : X → ι → σ) (f : X → O) : ℕ :=
  qQueryOn read f (1 / 3)

/-- Quantum query complexity of a total function. -/
noncomputable abbrev qQuery (f : (ι → σ) → O) (ε : ℝ) : ℕ :=
  qQueryOn (X := ι → σ) id f ε

/-- The conventional error convention, for a total function. -/
noncomputable abbrev boundedErrorQQuery (f : (ι → σ) → O) : ℕ :=
  qQuery f (1 / 3)

/-! ## Upper bounds

Trap: in the existential above the two instance components **must** be supplied
with `inferInstance`.  Writing `⟨W, _, _, A, h⟩` and letting unification solve
them from `A`'s type sends `isDefEq` into a loop (it does not terminate even at
2·10⁶ heartbeats). -/

theorem mem_queryCounts {read : X → ι → σ} {f : X → O} {ε : ℝ} {q : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {A : QAlg ι σ O W}
    (h : ComputesWithErrorOn A q read f ε) :
    q ∈ QueryCounts read f ε :=
  ⟨W, inferInstance, inferInstance, A, h⟩

/-- **One algorithm bounds the complexity.** -/
theorem qQueryOn_le {read : X → ι → σ} {f : X → O} {ε : ℝ} {q : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {A : QAlg ι σ O W}
    (h : ComputesWithErrorOn A q read f ε) :
    qQueryOn read f ε ≤ q :=
  Nat.sInf_le (mem_queryCounts h)

/-! ## Lower bounds and the optimal witness -/

/-- **The infimum is attained**: an optimal algorithm exists as soon as any
algorithm does. -/
theorem exists_computes_qQueryOn {read : X → ι → σ} {f : X → O} {ε : ℝ}
    (hne : (QueryCounts read f ε).Nonempty) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (A : QAlg ι σ O W),
      ComputesWithErrorOn A (qQueryOn read f ε) read f ε :=
  Nat.sInf_mem hne

/-- **A bound valid for every algorithm bounds the complexity from below.** -/
theorem le_qQueryOn {read : X → ι → σ} {f : X → O} {ε : ℝ} {c : ℕ}
    (hne : (QueryCounts read f ε).Nonempty)
    (h : ∀ (q : ℕ) (W : Type) (_ : Fintype W) (_ : DecidableEq W) (A : QAlg ι σ O W),
      ComputesWithErrorOn A q read f ε → c ≤ q) :
    c ≤ qQueryOn read f ε := by
  obtain ⟨W, hW, hW', A, hA⟩ := exists_computes_qQueryOn hne
  exact h _ W hW hW' A hA

/-- The real-valued form, which is what the adversary lower bound produces. -/
theorem le_qQueryOn_real {read : X → ι → σ} {f : X → O} {ε : ℝ} {c : ℝ}
    (hne : (QueryCounts read f ε).Nonempty)
    (h : ∀ (q : ℕ) (W : Type) (_ : Fintype W) (_ : DecidableEq W) (A : QAlg ι σ O W),
      ComputesWithErrorOn A q read f ε → c ≤ (q : ℝ)) :
    c ≤ (qQueryOn read f ε : ℝ) := by
  obtain ⟨W, hW, hW', A, hA⟩ := exists_computes_qQueryOn hne
  exact h _ W hW hW' A hA

/-! ## Monotonicity in the error -/

theorem queryCounts_mono {read : X → ι → σ} {f : X → O} {ε ε' : ℝ} (hε : ε ≤ ε') :
    QueryCounts read f ε ⊆ QueryCounts read f ε' := by
  rintro q ⟨W, hW, hW', A, hA⟩
  exact ⟨W, hW, hW', A, hA.mono hε⟩

theorem qQueryOn_mono {read : X → ι → σ} {f : X → O} {ε ε' : ℝ} (hε : ε ≤ ε')
    (hne : (QueryCounts read f ε).Nonempty) :
    qQueryOn read f ε' ≤ qQueryOn read f ε :=
  Nat.sInf_le (queryCounts_mono hε (Nat.sInf_mem hne))

/-! ## Restriction to a promise

A promise problem whose output is a function *of the observations* is no
harder than the total problem: run the total algorithm on the promised
observations.  No injectivity and no structure on `read` are needed. -/

/-- A total algorithm, run on the promised observations. -/
theorem computesWithErrorOn_comp_read {W : Type} [Fintype W] [DecidableEq W]
    {A : QAlg ι σ O W} {q : ℕ} {f : (ι → σ) → O} {ε : ℝ}
    (h : ComputesWithErrorOn A q (id : (ι → σ) → ι → σ) f ε)
    (read : X → ι → σ) :
    ComputesWithErrorOn A q read (fun x => f (read x)) ε :=
  fun x => h (read x)

theorem queryCounts_subset_of_read (read : X → ι → σ) (f : (ι → σ) → O)
    (ε : ℝ) :
    QueryCounts (X := ι → σ) id f ε
      ⊆ QueryCounts read (fun x => f (read x)) ε := by
  rintro q ⟨W, hW, hW', A, hA⟩
  exact ⟨W, hW, hW', A, computesWithErrorOn_comp_read hA read⟩

/-- **The restriction bound**: `Q_ε(f ∘ read on the promise) ≤ Q_ε(f)`.  This
is what turns a promise lower bound into a lower bound on the honest total
function. -/
theorem qQueryOn_comp_read_le_qQuery (read : X → ι → σ) (f : (ι → σ) → O)
    {ε : ℝ} (hne : (QueryCounts (X := ι → σ) id f ε).Nonempty) :
    qQueryOn read (fun x => f (read x)) ε ≤ qQuery f ε :=
  Nat.sInf_le (queryCounts_subset_of_read read f ε (Nat.sInf_mem hne))

/-! ## The constant case -/

/-- A constant function has quantum query complexity zero. -/
theorem qQueryOn_const_eq_zero (read : X → ι → σ) {f : X → O} {c : O}
    (hf : ∀ x, f x = c) {ε : ℝ} (hε : 0 ≤ ε) : qQueryOn read f ε = 0 :=
  Nat.le_zero.mp (qQueryOn_le (computesWithErrorOn_const read c hf hε))

end QuantumQueryComplexity
