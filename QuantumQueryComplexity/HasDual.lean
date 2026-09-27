import QuantumQueryComplexity.ComposeShared
import QuantumQueryComplexity.Pullback
import QuantumQueryComplexity.Scan.Final
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Bundled dual solutions

A divide-and-conquer construction builds one dual solution out of many, and the
dimension types of the pieces are all different: a maximum over a block of `q`
positions carries `Order` and `ScanDim` types built from that block, a
first-difference combination carries prefix and output gadgets, and a recursive
call carries whatever its own subtree produced.  Threading those types through a
recursion requires a `Sigma` type and `DualPair.embedDim` to combine the
different finite dimensions.

So we hide the dimension:

  `HasDual f c` — *some* feasible dual solution for `f` has cost at most `c`;
  `HasWeightedDual f c V` — *some* solution has `c`-weighted cost at most `V`.

Every construction of `QuantumQueryComplexity/{Pullback, FirstDiff, ComposeShared}.lean` is
restated at this level, and the `Sigma`-plus-`embedDim` step happens exactly once,
inside `HasWeightedDual.composeShared`.  What is left are two combinators that
say what divide-and-conquer actually does:

* `HasDual.combine` — evaluate finitely many subproblems and feed the results to
  an **arbitrary** outer function, at cost `2 ∑ₚ cₚ`;
* `HasDual.max` — take the maximum of `q` equally expensive subproblems, at cost
  `24 √q · c`, with no dependence on the alphabet of values.

Dimension types are pinned to `Type`; every construction in this development
produces one (`Fin`, `Order`, `ScanDim`, products, sums and sigmas of these).
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {O : Type} [DecidableEq O]

/-! ## The two predicates -/

/-- `f` has a feasible dual solution of cost at most `c`. -/
def HasDual {ι : Type} [Fintype ι] {σ : Type} [DecidableEq σ] {O : Type}
    [DecidableEq O] (f : (ι → σ) → O) (c : ℝ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (P : DualPair K f), P.IsCostLe c

/-- `f` has a feasible dual solution of `c`-weighted cost at most `V`. -/
def HasWeightedDual {ι : Type} [Fintype ι] {σ : Type} [DecidableEq σ] {O : Type}
    [DecidableEq O] (f : (ι → σ) → O) (c : ι → ℝ) (V : ℝ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (P : DualPair K f), P.IsWeightedCostLe c V

variable {f g : (ι → σ) → O} {c d : ℝ}

lemma hasDual_of_dualPair {K : Type} [Fintype K] (P : DualPair K f)
    (h : P.IsCostLe c) : HasDual f c := ⟨K, inferInstance, P, h⟩

lemma hasWeightedDual_of_dualPair {K : Type} [Fintype K] {w : ι → ℝ} {V : ℝ}
    (P : DualPair K f) (h : P.IsWeightedCostLe w V) : HasWeightedDual f w V :=
  ⟨K, inferInstance, P, h⟩

lemma HasDual.mono (h : HasDual f c) (hcd : c ≤ d) : HasDual f d := by
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P, hP.mono hcd⟩

lemma HasWeightedDual.mono {w : ι → ℝ} {V V' : ℝ} (h : HasWeightedDual f w V)
    (hV : V ≤ V') : HasWeightedDual f w V' := by
  obtain ⟨K, hK, P, hP⟩ := h
  refine ⟨K, hK, P, fun x => ?_, fun x => ?_⟩
  · exact (hP.1 x).trans hV
  · exact (hP.2 x).trans hV

lemma HasDual.nonneg [Nonempty σ] (h : HasDual f c) : 0 ≤ c := by
  obtain ⟨K, hK, P, hP⟩ := h
  exact DualPair.isCostLe_nonneg hP

/-- **Weak duality, bundled.** -/
theorem advPM_le_of_hasDual (hc : 0 ≤ c) (h : HasDual f c) :
    advPM f ≤ c := by
  obtain ⟨K, hK, P, hP⟩ := h
  exact advPM_le_of_dualPair P hc hP

/-! ## Constant weights

The one quantitative fact linking the two predicates: an ordinary bound `V`
*is* a constant-weight bound `c₀ V`.  This is what lets a family of equally
expensive subproblems be fed to an outer solution whose cost was measured
without weights. -/

lemma DualPair.isWeightedCostLe_const {K : Type} [Fintype K] {P : DualPair K f}
    {V c₀ : ℝ} (hc₀ : 0 ≤ c₀) (h : P.IsCostLe V) :
    P.IsWeightedCostLe (fun _ => c₀) (c₀ * V) := by
  constructor
  · intro x
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (h.1 x) hc₀
  · intro x
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (h.2 x) hc₀

lemma HasDual.weighted_const {c₀ : ℝ} (hc₀ : 0 ≤ c₀) (h : HasDual f c) :
    HasWeightedDual f (fun _ => c₀) (c₀ * c) := by
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P, DualPair.isWeightedCostLe_const hc₀ hP⟩

lemma DualPair.isCostLe_of_isWeightedCostLe_one {K : Type} [Fintype K]
    {P : DualPair K f} {V : ℝ} (h : P.IsWeightedCostLe (fun _ => 1) V) :
    P.IsCostLe V :=
  ⟨fun x => by simpa using h.1 x, fun x => by simpa using h.2 x⟩

/-! ## Transport -/

lemma HasDual.ofEq (hfg : ∀ x, f x = g x) (h : HasDual f c) : HasDual g c := by
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P.ofEq hfg, DualPair.ofEq_isCostLe hfg hP⟩

/-- **A dual solution only sees which inputs share an output value.**

The feasibility constraint reads `= if f x = f y then 0 else 1`, so nothing but
the partition of inputs into level sets enters.  Two functions inducing the same
partition therefore have the same dual solutions, at the same cost — even when
their output *types* are different.  This is what makes it harmless to recode an
output into a finite type. -/
lemma HasDual.ofKer {O' : Type} [DecidableEq O'] {f' : (ι → σ) → O'}
    (hker : ∀ x y, f x = f y ↔ f' x = f' y) (h : HasDual f c) : HasDual f' c := by
  obtain ⟨K, hK, P, hP⟩ := h
  have hcon : ∀ x y : ι → σ,
      (∑ i, if x i = y i then (0 : ℝ) else ∑ k, P.u x i k * P.v y i k)
        = if f' x = f' y then 0 else 1 := by
    intro x y
    rw [P.constraint x y]
    by_cases hxy : f x = f y
    · rw [if_pos hxy, if_pos ((hker x y).1 hxy)]
    · rw [if_neg hxy, if_neg fun hc => hxy ((hker x y).2 hc)]
  exact ⟨K, hK, ⟨P.u, P.v, hcon⟩, hP.1, hP.2⟩

/-- A dual solution restricted to a block of coordinates: injectivity of the
inclusion is what keeps the cost unchanged. -/
lemma HasDual.pullback {κ : Type} [Fintype κ] [DecidableEq κ] {e : κ → ι}
    (he : Function.Injective e) {f : (κ → σ) → O} (h : HasDual f c) :
    HasDual (pullbackFun e f) c := by
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P.pullback he, DualPair.pullback_isCostLe he P hP⟩

/-- **A dual solution restricted along a padding.**  A function of `n` letters is
a function of `N ≥ n` letters whose last `N - n` are frozen at known values, and
freezing costs nothing. -/
lemma HasDual.restrict {κ σ' : Type} [Fintype κ] [DecidableEq κ] [DecidableEq σ']
    {e : ι → κ} (he : Function.Injective e) {Φ : (ι → σ) → κ → σ'}
    (hin : ∀ (x y : ι → σ) (i : ι), Φ x (e i) = Φ y (e i) ↔ x i = y i)
    (hout : ∀ (x y : ι → σ) (j : κ), (∀ i, e i ≠ j) → Φ x j = Φ y j)
    {F : (κ → σ') → O} (h : HasDual F c) : HasDual (fun x => F (Φ x)) c := by
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P.restrict he hin hout,
    DualPair.restrict_isCostLe he hin hout P hP⟩

/-- Recoding the input alphabet along an injection. -/
lemma HasDual.alphaMap {σ' : Type} [DecidableEq σ'] {m : σ → σ'}
    (hm : Function.Injective m) {f : (ι → σ') → O} (h : HasDual f c) :
    HasDual (alphaFun m f) c := by
  obtain ⟨K, hK, P, hP⟩ := h
  exact ⟨K, hK, P.alphaMap hm, DualPair.alphaMap_isCostLe hm P hP⟩

/-- A function that never changes value costs nothing: both vector families are
zero, and every dual constraint reads `0 = 0`. -/
lemma hasDual_const (hf : ∀ x y, f x = f y) : HasDual f 0 := by
  refine ⟨Unit, inferInstance, ⟨fun _ _ _ => 0, fun _ _ _ => 0, fun x y => ?_⟩,
    ⟨fun x => ?_, fun x => ?_⟩⟩
  · rw [if_pos (hf x y)]
    exact Finset.sum_eq_zero fun i _ => by
      by_cases h : x i = y i
      · rw [if_pos h]
      · rw [if_neg h]
        exact Finset.sum_eq_zero fun k _ => by ring
  · exact le_of_eq (Finset.sum_eq_zero fun i _ =>
      Finset.sum_eq_zero fun k _ => by ring)
  · exact le_of_eq (Finset.sum_eq_zero fun i _ =>
      Finset.sum_eq_zero fun k _ => by ring)

/-- The zero solution has weighted cost zero for *every* weight vector, whatever
its sign. -/
lemma hasWeightedDual_const {w : ι → ℝ} (hf : ∀ x y, f x = f y) :
    HasWeightedDual f w 0 := by
  refine ⟨Unit, inferInstance, ⟨fun _ _ _ => 0, fun _ _ _ => 0, fun x y => ?_⟩,
    fun x => ?_, fun x => ?_⟩
  · rw [if_pos (hf x y)]
    exact Finset.sum_eq_zero fun i _ => by
      by_cases h : x i = y i
      · rw [if_pos h]
      · rw [if_neg h]
        exact Finset.sum_eq_zero fun k _ => by ring
  · exact le_of_eq (Finset.sum_eq_zero fun i _ => by
      rw [Finset.sum_eq_zero fun k _ => by ring, mul_zero])
  · exact le_of_eq (Finset.sum_eq_zero fun i _ => by
      rw [Finset.sum_eq_zero fun k _ => by ring, mul_zero])

/-- `HasDual.ofKer` for the weighted predicate: recoding the output changes
neither the feasible solutions nor their cost. -/
lemma HasWeightedDual.ofKer {O' : Type} [DecidableEq O'] {f' : (ι → σ) → O'}
    {w : ι → ℝ} {V : ℝ} (hker : ∀ x y, f x = f y ↔ f' x = f' y)
    (h : HasWeightedDual f w V) : HasWeightedDual f' w V := by
  obtain ⟨K, hK, P, hP⟩ := h
  have hcon : ∀ x y : ι → σ,
      (∑ i, if x i = y i then (0 : ℝ) else ∑ k, P.u x i k * P.v y i k)
        = if f' x = f' y then 0 else 1 := by
    intro x y
    rw [P.constraint x y]
    by_cases hxy : f x = f y
    · rw [if_pos hxy, if_pos ((hker x y).1 hxy)]
    · rw [if_neg hxy, if_neg fun hc => hxy ((hker x y).2 hc)]
  exact ⟨K, hK, ⟨P.u, P.v, hcon⟩, hP.1, hP.2⟩

/-! ## Composition with shared inputs

This is the only place where dimension types are unified.  The subproblems'
solutions live in types `K p` depending on `p`; the sigma type `Σ p, K p` holds
them all, and `DualPair.embedDim` moves each into it by padding with zeros, at
no cost. -/

section Shared

variable {P V : Type} [Fintype P] [DecidableEq P] [DecidableEq V]
variable {h : (P → V) → O} {g : P → (ι → σ) → V}

/-- **Shared-input composition, bundled.**  An outer solution of `c`-weighted
cost `Vout` and subproblem solutions of costs `c p` compose to cost `Vout`. -/
theorem HasWeightedDual.composeShared {c : P → ℝ} {Vout : ℝ}
    (hQ : HasWeightedDual h c Vout) (hc : ∀ p, 0 ≤ c p)
    (hg : ∀ p, HasDual (g p) (c p)) : HasDual (sharedFun h g) Vout := by
  classical
  obtain ⟨K, hK, Q, hQ'⟩ := hQ
  choose Kp instKp R hR using hg
  letI : ∀ p, Fintype (Kp p) := instKp
  letI : ∀ p, DecidableEq (Kp p) := fun p => Classical.decEq _
  letI : DecidableEq ((p : P) × Kp p) := Classical.decEq _
  refine ⟨P × K × ((p : P) × Kp p), inferInstance,
    Q.composeShared fun p => (R p).embedDim (sigma_mk_injective (i := p)), ?_⟩
  exact DualPair.composeShared_isCostLe _ _ hc hQ' fun p =>
    DualPair.embedDim_isCostLe _ _ (hR p)

end Shared

/-! ## The two combinators -/

/-- **Feed finitely many subproblems to an arbitrary outer function.**

The first-difference dual is feasible for *any* outer function, so nothing about
`h` is assumed: it may add two tropical path weights, take a maximum of level
summaries, or assemble a whole matrix out of its entries.  The price is a factor
`2` on the total of the subproblem costs. -/
theorem HasDual.combine {P V : Type} [Fintype P] [DecidableEq P] [Fintype V]
    [DecidableEq V] [Fintype O] (h : (P → V) → O) {g : P → (ι → σ) → V}
    {c : P → ℝ} (hc : ∀ p, 0 ≤ c p) (hg : ∀ p, HasDual (g p) (c p)) :
    HasDual (fun x => h fun p => g p x) (2 * ∑ p, c p) :=
  HasWeightedDual.composeShared
    (hasWeightedDual_of_dualPair (firstDiffDual h)
      (firstDiffDual_isWeightedCostLe h c)) hc hg

/-- **The maximum of equally expensive subproblems.**

`24 √q` is the alphabet-free cost of maximum finding on `q` coordinates
(`QuantumQueryComplexity/Scan/Final.lean`); with constant weights it turns `q` subproblems of
cost `c₀` into their maximum at cost `24 √q · c₀`.  The values compared may range
over any finite linear order, and the bound does not see how large it is. -/
theorem HasDual.max {P A : Type} [Fintype P] [DecidableEq P] [Nonempty P]
    [Fintype A] [DecidableEq A] [LinearOrder A] {g : P → (ι → σ) → A} {c₀ : ℝ}
    (hc₀ : 0 ≤ c₀) (hg : ∀ p, HasDual (g p) c₀) :
    HasDual (fun x => maxFun fun p => g p x)
      (c₀ * (24 * Real.sqrt (Fintype.card P))) := by
  obtain ⟨Q, hQ⟩ := exists_maxFun_dual_isCostLe (ι := P) (A := A)
  exact HasWeightedDual.composeShared
    (hasWeightedDual_of_dualPair Q (DualPair.isWeightedCostLe_const hc₀ hQ))
    (fun _ => hc₀) hg

/-! ## Maximum of a value map over a block of coordinates

The base case of every divide-and-conquer over letters: a query returns a whole
letter, and the quantity wanted is the largest value of some map on the letters
read in a given block. -/

/-- The maximum of `m` over the letters, as a bundled dual. -/
theorem hasDual_maxMap {A : Type} [Nonempty ι] [Fintype A]
    [DecidableEq A] [LinearOrder A] (m : σ → A) :
    HasDual (fun x : ι → σ => maxFun fun j => m (x j))
      (24 * Real.sqrt (Fintype.card ι)) := by
  obtain ⟨P, hP⟩ := exists_maxMap_dual_isCostLe (ι := ι) (A := A) (σ := σ) m
  exact ⟨_, inferInstance, P, hP⟩

/-- `MAX` itself, as a bundled dual: `hasDual_maxMap` at the identity value
map, with the alphabet the finite linear order being maximized.  The
operational `Θ(√n)` endpoints extracted from these certificates live in
`QuantumQueryComplexity/Quantum/MaxApplications.lean`. -/
theorem hasDual_maxFun {A : Type} [Nonempty ι] [Fintype A]
    [DecidableEq A] [LinearOrder A] :
    HasDual (maxFun : (ι → A) → A) (24 * Real.sqrt (Fintype.card ι)) := by
  obtain ⟨P, hP⟩ := exists_maxFun_dual_isCostLe (ι := ι) (A := A)
  exact ⟨_, inferInstance, P, hP⟩

/-- The maximum of `m` over the letters in a block, at a cost governed by the
size of the block. -/
theorem hasDual_maxMap_block {κ A : Type} [Fintype κ] [DecidableEq κ]
    [Nonempty κ] [Fintype A] [DecidableEq A] [LinearOrder A] {e : κ → ι}
    (he : Function.Injective e) (m : σ → A) :
    HasDual (fun x : ι → σ => maxFun fun j : κ => m (x (e j)))
      (24 * Real.sqrt (Fintype.card κ)) :=
  (hasDual_maxMap (ι := κ) (σ := σ) m).pullback he

/-! ## Infinite value types

The scan and the first-difference gadget both need *finite* branch and output
types, while the values a divide-and-conquer computes naturally live somewhere
infinite — tropical path weights are elements of `ℝ ∪ {-∞}`.

Nothing is lost.  The input space `ι → σ` is finite, so every function on it has
finite range; restricting to that range changes neither the level sets nor, by
`HasDual.ofKer`, the dual solutions.  The three combinators are therefore
restated with no finiteness assumption on the values at all, and it is these
versions that a recursion over tropical matrices consumes. -/

section FiniteRange


/-- A strictly monotone map commutes with `maxFun`.  Used to compare a maximum
computed inside a finite subtype of values with the same maximum computed
outside it. -/
lemma maxFun_strictMono {κ A B : Type} [Fintype κ] [Nonempty κ] [LinearOrder A]
    [LinearOrder B] {φ : A → B} (hφ : StrictMono φ) (G : κ → A) :
    (maxFun fun j => φ (G j)) = φ (maxFun G) := by
  obtain ⟨j, hj⟩ := exists_eq_maxFun G
  exact maxFun_eq_iff.2 ⟨⟨j, by rw [hj]⟩, fun j => hφ.monotone (le_maxFun G j)⟩

/-- **The maximum of equally expensive subproblems, over any linear order of
values.** -/
theorem HasDual.max' {Pi A : Type} [Fintype Pi] [DecidableEq Pi] [Nonempty Pi]
    [DecidableEq A] [LinearOrder A] {g : Pi → (ι → σ) → A} {c₀ : ℝ}
    (hc₀ : 0 ≤ c₀) (hg : ∀ p, HasDual (g p) c₀) :
    HasDual (fun x => maxFun fun p => g p x)
      (c₀ * (24 * Real.sqrt (Fintype.card Pi))) := by
  classical
  set S : Finset A :=
    Finset.image (fun q : Pi × (ι → σ) => g q.1 q.2) Finset.univ with hSdef
  have hmem : ∀ (p : Pi) (x : ι → σ), g p x ∈ S := fun p x =>
    Finset.mem_image_of_mem _ (Finset.mem_univ (p, x))
  set g₀ : Pi → (ι → σ) → {a // a ∈ S} := fun p x => ⟨g p x, hmem p x⟩ with hg₀def
  have hstrict : StrictMono (fun a : {a // a ∈ S} => (a : A)) := fun _ _ hab => hab
  have hcoe : ∀ x : ι → σ,
      ((maxFun fun p => g₀ p x : {a // a ∈ S}) : A) = maxFun fun p => g p x := by
    intro x
    exact (maxFun_strictMono hstrict fun p => g₀ p x).symm
  have hbase : HasDual (fun x => maxFun fun p => g₀ p x)
      (c₀ * (24 * Real.sqrt (Fintype.card Pi))) :=
    HasDual.max hc₀ fun p => (hg p).ofKer fun x y => by
      simp [hg₀def, Subtype.ext_iff]
  refine hbase.ofKer fun x y => ⟨fun hxy => ?_, fun hxy => Subtype.ext ?_⟩
  · rw [← hcoe x, ← hcoe y, hxy]
  · rw [hcoe x, hcoe y, hxy]

/-- **An arbitrary outer function of finitely many subproblems, over any value
and output types.** -/
theorem HasDual.combine' {Pi V O' : Type} [Fintype Pi] [DecidableEq Pi]
    [DecidableEq V] [DecidableEq O'] (h : (Pi → V) → O') {g : Pi → (ι → σ) → V}
    {c : Pi → ℝ} (hc : ∀ p, 0 ≤ c p) (hg : ∀ p, HasDual (g p) (c p)) :
    HasDual (fun x => h fun p => g p x) (2 * ∑ p, c p) := by
  classical
  set SV : Finset V :=
    Finset.image (fun q : Pi × (ι → σ) => g q.1 q.2) Finset.univ with hSVdef
  have hmemV : ∀ (p : Pi) (x : ι → σ), g p x ∈ SV := fun p x =>
    Finset.mem_image_of_mem _ (Finset.mem_univ (p, x))
  set g₀ : Pi → (ι → σ) → {v // v ∈ SV} := fun p x => ⟨g p x, hmemV p x⟩ with hg₀def
  set SO : Finset O' :=
    Finset.image (fun z : Pi → {v // v ∈ SV} => h fun p => (z p : V))
      Finset.univ with hSOdef
  have hmemO : ∀ z : Pi → {v // v ∈ SV}, (h fun p => (z p : V)) ∈ SO := fun z =>
    Finset.mem_image_of_mem _ (Finset.mem_univ z)
  set h₀ : (Pi → {v // v ∈ SV}) → {o // o ∈ SO} := fun z =>
    ⟨h fun p => (z p : V), hmemO z⟩ with hh₀def
  have hbase : HasDual (fun x => h₀ fun p => g₀ p x) (2 * ∑ p, c p) :=
    HasDual.combine h₀ hc fun p => (hg p).ofKer fun x y => by
      simp [hg₀def, Subtype.ext_iff]
  exact hbase.ofKer fun x y =>
    ⟨fun hxy => congrArg Subtype.val hxy, fun hxy => Subtype.ext hxy⟩

/-- **Postcomposition is available within a factor two.**  `combine'` with a
one-element index set: its outer function is arbitrary, so *any* recoding of
the output — a coarsening included — costs at most twice the original.  It is
not free in general: a dual for `f` satisfies an equality constraint keyed to
`f`'s level sets, and merging two of them turns a required `1` into a
required `0`.  Two is an upper bound obtained this way, not a lower bound on
what a coarsening must cost — a particular recoding may well be cheaper, and
an injective one is free (`HasDual.ofKer`).  This is the priced form of the
joint-output discipline. -/
theorem HasDual.postcomp {V O' : Type} [DecidableEq V] [DecidableEq O']
    {f : (ι → σ) → V} {c : ℝ} (hc : 0 ≤ c) (h : HasDual f c) (H : V → O') :
    HasDual (fun x => H (f x)) (2 * c) := by
  have hcomb := HasDual.combine' (ι := ι) (σ := σ) (Pi := Unit) (V := V)
    (O' := O') (fun z : Unit → V => H (z ())) (g := fun _ => f)
    (c := fun _ => c) (fun _ => hc) fun _ => h
  simpa using hcomb

/-- **A joint may be collapsed onto anything it determines**, within the same
factor two — with the collapsing map obtained from the determination rather
than supplied.  This is the form a transcript compiler needs: it builds a
joint and reads off the answer that the joint determines. -/
theorem HasDual.postcomp_of_determined {V O' : Type} [DecidableEq V] [DecidableEq O']
    [Nonempty O'] {f : (ι → σ) → V} {g : (ι → σ) → O'} {c : ℝ} (hc : 0 ≤ c)
    (h : HasDual f c) (hdet : ∀ x y, f x = f y → g x = g y) :
    HasDual g (2 * c) := by
  classical
  refine (h.postcomp hc (fun v => if hv : ∃ x, f x = v then g hv.choose
    else Classical.arbitrary O')).ofEq fun x => ?_
  have hv : ∃ z, f z = f x := ⟨x, rfl⟩
  rw [dif_pos hv]
  exact hdet _ _ hv.choose_spec

/-- **Every function of `n` letters costs `2n`**, whatever its output type.  The
first-difference dual with the output recoded into its finite range. -/
theorem hasDual_two_mul_card (f : (ι → σ) → O) :
    HasDual f (2 * (Fintype.card ι : ℝ)) := by
  classical
  set S : Finset O := Finset.image f Finset.univ with hSdef
  have hmem : ∀ x, f x ∈ S := fun x =>
    Finset.mem_image_of_mem _ (Finset.mem_univ x)
  set f₀ : (ι → σ) → {o // o ∈ S} := fun x => ⟨f x, hmem x⟩ with hf₀def
  have hw := firstDiffDual_isWeightedCostLe f₀ (fun _ => 1)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hw
  refine (hasDual_of_dualPair (firstDiffDual f₀)
    (DualPair.isCostLe_of_isWeightedCostLe_one hw)).ofKer fun x y => ?_
  exact ⟨fun hxy => congrArg Subtype.val hxy, fun hxy => Subtype.ext hxy⟩

/-- **A function of a single letter costs `2`.**  Both the letter alphabet and
the output type are arbitrary. -/
theorem hasDual_ofCoord (i₀ : ι) (m : σ → O) :
    HasDual (fun x : ι → σ => m (x i₀)) 2 := by
  have he : Function.Injective (fun _ : Unit => i₀) := fun a b _ =>
    Subsingleton.elim a b
  have h := (hasDual_two_mul_card (ι := Unit) (σ := σ)
    (fun z : Unit → σ => m (z ()))).pullback he
  have h2 : HasDual (fun x : ι → σ => m (x i₀)) (2 * (Fintype.card Unit : ℝ)) :=
    h.ofEq fun _ => rfl
  simpa using h2

/-- **A finite supremum, as a maximum over a nonempty index.**  Padding the index
set with a `none` carrying `⊥` makes an empty supremum legal, so no nonemptiness
hypothesis has to be threaded through a recursion. -/
lemma finsetSup_eq_maxFun {α : Type} [DecidableEq α] {A : Type} [LinearOrder A]
    [OrderBot A] (S : Finset α) (F : α → A) :
    S.sup F = maxFun fun c : Option {i // i ∈ S} => c.elim ⊥ fun i => F i := by
  refine le_antisymm (Finset.sup_le fun i hi => ?_) (maxFun_le fun c => ?_)
  · exact le_maxFun (fun c : Option {i // i ∈ S} => c.elim ⊥ fun i => F i)
      (some ⟨i, hi⟩)
  · cases c with
    | none => exact bot_le
    | some i => exact Finset.le_sup i.2

/-- **The supremum of a finite family of equally expensive subproblems.**

The workhorse of the divide-and-conquer: `q` candidates each solved at cost `c₀`
give their maximum at cost `24 √(q+1) · c₀`.  Stated for `Finset.sup` rather than
`maxFun`, so that an empty candidate set — the maximum of nothing is `⊥` — is
allowed and costs nothing extra. -/
theorem HasDual.finsetSup {α A : Type} [DecidableEq α] [DecidableEq A]
    [LinearOrder A] [OrderBot A] (S : Finset α) {g : α → (ι → σ) → A} {c₀ : ℝ}
    (hc₀ : 0 ≤ c₀) (hg : ∀ i ∈ S, HasDual (g i) c₀) :
    HasDual (fun x => S.sup fun i => g i x)
      (c₀ * (24 * Real.sqrt ((S.card : ℝ) + 1))) := by
  classical
  have hcard : (Fintype.card (Option {i // i ∈ S}) : ℝ) = (S.card : ℝ) + 1 := by
    rw [Fintype.card_option, Fintype.card_coe]
    push_cast
    ring
  have hmax : HasDual (fun x => maxFun fun c : Option {i // i ∈ S} =>
      c.elim ⊥ fun i => g (i : α) x)
      (c₀ * (24 * Real.sqrt (Fintype.card (Option {i // i ∈ S})))) := by
    refine HasDual.max' hc₀ fun c => ?_
    cases c with
    | none => exact (hasDual_const (f := fun _ : ι → σ => (⊥ : A))
        fun _ _ => rfl).mono hc₀
    | some i => exact hg (i : α) i.2
  rw [hcard] at hmax
  exact hmax.ofEq fun x => (finsetSup_eq_maxFun S fun i => g i x).symm

/-- **Two subproblems fed to an arbitrary binary outer function.**  This is how
two tropical path weights are multiplied — `h` is `(+)` on `ℝ ∪ {-∞}` — and
nothing about `h` is used. -/
theorem HasDual.combine₂ {V O' : Type} [DecidableEq V] [DecidableEq O']
    (h : V → V → O') {g₀ g₁ : (ι → σ) → V} {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (hg₀ : HasDual g₀ c₀) (hg₁ : HasDual g₁ c₁) :
    HasDual (fun x => h (g₀ x) (g₁ x)) (2 * (c₀ + c₁)) := by
  have hsum : (∑ b : Bool, bif b then c₁ else c₀) = c₀ + c₁ := by
    rw [Fintype.sum_bool]
    exact add_comm _ _
  have hc : ∀ b : Bool, 0 ≤ (bif b then c₁ else c₀) := by
    intro b; cases b
    · exact hc₀
    · exact hc₁
  have hgb : ∀ b : Bool,
      HasDual (bif b then g₁ else g₀) (bif b then c₁ else c₀) := by
    intro b; cases b
    · exact hg₀
    · exact hg₁
  have := HasDual.combine' (Pi := Bool) (fun z : Bool → V => h (z false) (z true))
    (g := fun b => bif b then g₁ else g₀) (c := fun b => bif b then c₁ else c₀)
    hc hgb
  rwa [hsum] at this

/-- **The maximum of a value map over a block of letters, over any linear order
of values.**  This is the base case of the tropical recursion: the largest
`(s,t)` entry among the letters read in a block. -/
theorem hasDual_maxMap_block' {κ A : Type} [Fintype κ] [DecidableEq κ]
    [Nonempty κ] [DecidableEq A] [LinearOrder A] {e : κ → ι}
    (he : Function.Injective e) (m : σ → A) :
    HasDual (fun x : ι → σ => maxFun fun j : κ => m (x (e j)))
      (24 * Real.sqrt (Fintype.card κ)) := by
  classical
  set S : Finset A := Finset.image m Finset.univ with hSdef
  have hmem : ∀ s : σ, m s ∈ S := fun s =>
    Finset.mem_image_of_mem _ (Finset.mem_univ s)
  set m₀ : σ → {a // a ∈ S} := fun s => ⟨m s, hmem s⟩ with hm₀def
  have hstrict : StrictMono (fun a : {a // a ∈ S} => (a : A)) := fun _ _ hab => hab
  have hcoe : ∀ x : ι → σ,
      ((maxFun fun j : κ => m₀ (x (e j)) : {a // a ∈ S}) : A)
        = maxFun fun j : κ => m (x (e j)) := fun x =>
    (maxFun_strictMono hstrict fun j : κ => m₀ (x (e j))).symm
  exact (hasDual_maxMap_block (ι := ι) (σ := σ) he m₀).ofKer fun x y =>
    ⟨fun hxy => by rw [← hcoe x, ← hcoe y, hxy],
     fun hxy => Subtype.ext (by rw [hcoe x, hcoe y, hxy])⟩

end FiniteRange

end QuantumQueryComplexity
