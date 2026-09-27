import QuantumQueryComplexity.Dual
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Pulling a dual solution back along an embedding of coordinates

A subproblem of a divide-and-conquer algorithm reads only a *block* of the
input.  Formally it is `pullbackFun e f x = f (x ∘ e)` for an injection
`e : κ → ι` of the block into the full coordinate set.

A dual solution for `f` transports to one for `pullbackFun e f` **at the same
cost**: place the `j`-th vector of the original solution at coordinate `e j` and
zero elsewhere.  Injectivity is what makes this work — each coordinate of `ι`
receives at most one vector, so the `ℓ²` masses simply move rather than adding
up, and the masked sum over `ι` restricts to the masked sum over `κ`.

This is how `QuantumQueryComplexity/Max/Staircase.lean`'s bound for `maxFun` on a `κ`-indexed
input becomes a bound for "the maximum over a block" as a function of the whole
array, with cost governed by the block size `|κ|` and not by `|ι|`.
-/

namespace QuantumQueryComplexity

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {σ : Type*} [DecidableEq σ]
variable {O : Type*} [DecidableEq O]

/-- Restricting a function to a block of coordinates. -/
def pullbackFun (e : κ → ι) (f : (κ → σ) → O) : (ι → σ) → O :=
  fun x => f fun j => x (e j)

@[simp] lemma pullbackFun_apply (e : κ → ι) (f : (κ → σ) → O) (x : ι → σ) :
    pullbackFun e f x = f (fun j => x (e j)) := rfl

/-! ## Spreading a `κ`-indexed family over `ι` -/

/-- The value placed at coordinate `i` by a `κ`-indexed family. -/
noncomputable def spread (e : κ → ι) (F : κ → ℝ) (i : ι) : ℝ :=
  ∑ j : κ, (if e j = i then (1 : ℝ) else 0) * F j

lemma spread_eq_of_mem {e : κ → ι} (he : Function.Injective e) {i : ι} {j₀ : κ}
    (hj : e j₀ = i) (F : κ → ℝ) : spread e F i = F j₀ := by
  rw [spread, Finset.sum_eq_single j₀]
  · rw [if_pos hj, one_mul]
  · intro j _ hne
    rw [if_neg fun h => hne (he (h.trans hj.symm)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma spread_eq_zero {e : κ → ι} {i : ι} (h : ∀ j, e j ≠ i) (F : κ → ℝ) :
    spread e F i = 0 :=
  Finset.sum_eq_zero fun j _ => by rw [if_neg (h j), zero_mul]

/-- Injectivity makes `spread` multiplicative: at most one `κ`-index lands on
any given coordinate. -/
lemma spread_mul_spread {e : κ → ι} (he : Function.Injective e) (i : ι)
    (F G : κ → ℝ) :
    spread e F i * spread e G i = spread e (fun j => F j * G j) i := by
  by_cases h : ∃ j, e j = i
  · obtain ⟨j₀, hj⟩ := h
    rw [spread_eq_of_mem he hj, spread_eq_of_mem he hj, spread_eq_of_mem he hj]
  · push_neg at h
    simp [spread_eq_zero h]

/-- Summing a spread family over `ι` recovers the sum over `κ`. -/
lemma sum_spread {e : κ → ι} (he : Function.Injective e) (F : κ → ℝ) :
    (∑ i : ι, spread e F i) = ∑ j : κ, F j := by
  simp only [spread]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (e j)]
  · rw [if_pos rfl, one_mul]
  · intro i _ hne
    rw [if_neg fun h => hne h.symm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

namespace DualPair

variable {K : Type*} [Fintype K] {e : κ → ι} {f : (κ → σ) → O}

/-- **A dual solution pulled back along an injection of coordinates.** -/
noncomputable def pullback (he : Function.Injective e) (P : DualPair K f) :
    DualPair K (pullbackFun e f) where
  u x i := fun k => spread e (fun j => P.u (fun j => x (e j)) j k) i
  v y i := fun k => spread e (fun j => P.v (fun j => y (e j)) j k) i
  constraint x y := by
    set T : κ → ℝ := fun j =>
      ∑ k : K, P.u (fun j => x (e j)) j k * P.v (fun j => y (e j)) j k with hT
    have hpt : ∀ i : ι,
        (∑ k : K, spread e (fun j => P.u (fun j => x (e j)) j k) i
            * spread e (fun j => P.v (fun j => y (e j)) j k) i)
        = spread e T i := by
      intro i
      rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
        spread_mul_spread he i (fun j => P.u (fun j => x (e j)) j k)
          (fun j => P.v (fun j => y (e j)) j k)]
      simp only [spread, hT]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    simp only [hpt]
    have hmask : ∀ i : ι,
        (if x i = y i then (0 : ℝ) else spread e T i)
        = spread e (fun j => if x (e j) = y (e j) then (0 : ℝ) else T j) i := by
      intro i
      by_cases h : ∃ j, e j = i
      · obtain ⟨j₀, hj⟩ := h
        rw [spread_eq_of_mem he hj, spread_eq_of_mem he hj, hj]
      · push_neg at h
        rw [spread_eq_zero h, spread_eq_zero h, ite_self]
    simp only [hmask]
    rw [sum_spread he]
    exact P.constraint (fun j => x (e j)) (fun j => y (e j))

/-- The pullback costs exactly what the original solution costs — the `ℓ²` mass
moves from `κ` to the image of `e` without accumulating. -/
theorem pullback_isCostLe {c : ℝ} (he : Function.Injective e) (P : DualPair K f)
    (hP : P.IsCostLe c) : (P.pullback he).IsCostLe c := by
  constructor
  · intro x
    have h : ∀ i : ι, (∑ k : K, (P.pullback he).u x i k * (P.pullback he).u x i k)
        = spread e (fun j => ∑ k : K,
            P.u (fun j => x (e j)) j k * P.u (fun j => x (e j)) j k) i := by
      intro i
      show (∑ k : K, spread e (fun j => P.u (fun j => x (e j)) j k) i
          * spread e (fun j => P.u (fun j => x (e j)) j k) i) = _
      rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
        spread_mul_spread he i (fun j => P.u (fun j => x (e j)) j k)
          (fun j => P.u (fun j => x (e j)) j k)]
      simp only [spread]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    simp only [h]
    rw [sum_spread he]
    exact hP.1 _
  · intro y
    have h : ∀ i : ι, (∑ k : K, (P.pullback he).v y i k * (P.pullback he).v y i k)
        = spread e (fun j => ∑ k : K,
            P.v (fun j => y (e j)) j k * P.v (fun j => y (e j)) j k) i := by
      intro i
      show (∑ k : K, spread e (fun j => P.v (fun j => y (e j)) j k) i
          * spread e (fun j => P.v (fun j => y (e j)) j k) i) = _
      rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
        spread_mul_spread he i (fun j => P.v (fun j => y (e j)) j k)
          (fun j => P.v (fun j => y (e j)) j k)]
      simp only [spread]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    simp only [h]
    rw [sum_spread he]
    exact hP.2 _

end DualPair

/-! ## Freezing the coordinates outside a block

The dual of padding.  A function of `n` variables can be regarded as a function
of `N ≥ n` variables in which the last `N - n` are held at fixed, known values;
that is what "append `N - n` known identity matrices to the input" means, and a
dual solution for the padded problem restricts to one for the original at
unchanged cost.

Two conditions are needed, and between them they say that the adversary mask is
transported exactly.  `hin` says the embedded coordinates are read faithfully —
two inputs agree at `i` precisely when the padded inputs agree at `e i` — and
`hout` says the frozen coordinates never depend on the input, so they contribute
nothing to the mask.  Injectivity of `e` is what stops the `ℓ²` masses from
accumulating, exactly as in `pullback`.

Unlike `alphaMap`, the alphabets on the two sides need not match: padding
typically enlarges `σ` to `Option σ` in order to name the frozen letter. -/

namespace DualPair

variable {K : Type*} [Fintype K] {σ' : Type*} [DecidableEq σ']

section Restrict

variable {e : ι → κ} {Φ : (ι → σ) → κ → σ'} {F : (κ → σ') → O}

/-- **A dual solution restricted along a padding.** -/
noncomputable def restrict (he : Function.Injective e)
    (hin : ∀ (x y : ι → σ) (i : ι), Φ x (e i) = Φ y (e i) ↔ x i = y i)
    (hout : ∀ (x y : ι → σ) (j : κ), (∀ i, e i ≠ j) → Φ x j = Φ y j)
    (P : DualPair K F) : DualPair K (fun x => F (Φ x)) where
  u x i := P.u (Φ x) (e i)
  v y i := P.v (Φ y) (e i)
  constraint x y := by
    classical
    rw [← P.constraint (Φ x) (Φ y)]
    have hzero : ∀ j ∈ (Finset.univ : Finset κ), j ∉ Finset.image e Finset.univ →
        (if Φ x j = Φ y j then (0 : ℝ)
          else ∑ c, P.u (Φ x) j c * P.v (Φ y) j c) = 0 := by
      intro j _ hj
      rw [if_pos (hout x y j fun i hi =>
        hj (Finset.mem_image.2 ⟨i, Finset.mem_univ i, hi⟩))]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.image e Finset.univ)) hzero,
      Finset.sum_image fun i _ i' _ h => he h]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : x i = y i
    · rw [if_pos h, if_pos ((hin x y i).2 h)]
    · rw [if_neg h, if_neg fun hc => h ((hin x y i).1 hc)]

/-- The restriction costs no more than the padded solution: the `ℓ²` mass at the
frozen coordinates is simply discarded. -/
theorem restrict_isCostLe {c : ℝ} (he : Function.Injective e)
    (hin : ∀ (x y : ι → σ) (i : ι), Φ x (e i) = Φ y (e i) ↔ x i = y i)
    (hout : ∀ (x y : ι → σ) (j : κ), (∀ i, e i ≠ j) → Φ x j = Φ y j)
    (P : DualPair K F) (hP : P.IsCostLe c) :
    (P.restrict he hin hout).IsCostLe c := by
  classical
  have key : ∀ (U : (κ → σ') → κ → K → ℝ) (z : κ → σ'),
      (∑ i : ι, ∑ k : K, U z (e i) k * U z (e i) k)
        ≤ ∑ j : κ, ∑ k : K, U z j k * U z j k := by
    intro U z
    have himg : (∑ j ∈ Finset.image e Finset.univ, ∑ k : K, U z j k * U z j k)
        = ∑ i : ι, ∑ k : K, U z (e i) k * U z (e i) k :=
      Finset.sum_image fun i _ i' _ h => he h
    rw [← himg]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun j _ _ => Finset.sum_nonneg fun k _ => mul_self_nonneg _
  exact ⟨fun x => (key P.u (Φ x)).trans (hP.1 (Φ x)),
    fun y => (key P.v (Φ y)).trans (hP.2 (Φ y))⟩

end Restrict

end DualPair

/-! ## Recoding the alphabet -/

variable {σ' : Type*} [DecidableEq σ']

/-- Recoding the input alphabet along a map `m`. -/
def alphaFun (m : σ → σ') (f : (ι → σ') → O) : (ι → σ) → O :=
  fun x => f fun i => m (x i)

@[simp] lemma alphaFun_apply (m : σ → σ') (f : (ι → σ') → O) (x : ι → σ) :
    alphaFun m f x = f (fun i => m (x i)) := rfl

namespace DualPair

variable {K : Type*} [Fintype K] {m : σ → σ'} {f : (ι → σ') → O}

/-- A dual solution transports along an **injective** recoding of the alphabet,
at unchanged cost.

Injectivity is exactly what is needed and no more: it keeps the adversary mask
`x i ≠ y i` in step with `m (x i) ≠ m (y i)`, so the masked sums agree term by
term.  A non-injective recoding would merge inputs and let extra coordinates
into the sum.

The use here is order-reversing: `v ↦ M - 1 - v` is a bijection of `Fin M`, so a
solution for a maximum becomes one for a minimum without any separate
development. -/
noncomputable def alphaMap (hm : Function.Injective m) (P : DualPair K f) :
    DualPair K (alphaFun m f) where
  u x i := P.u (fun i => m (x i)) i
  v y i := P.v (fun i => m (y i)) i
  constraint x y := by
    have key : (∑ i, if x i = y i then (0 : ℝ)
          else ∑ k, P.u (fun i => m (x i)) i k * P.v (fun i => m (y i)) i k)
        = ∑ i, if m (x i) = m (y i) then (0 : ℝ)
          else ∑ k, P.u (fun i => m (x i)) i k * P.v (fun i => m (y i)) i k := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : x i = y i
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg fun hc => h (hm hc)]
    rw [key]
    exact P.constraint (fun i => m (x i)) (fun i => m (y i))

theorem alphaMap_isCostLe {c : ℝ} (hm : Function.Injective m) (P : DualPair K f)
    (hP : P.IsCostLe c) : (P.alphaMap hm).IsCostLe c :=
  ⟨fun x => hP.1 _, fun y => hP.2 _⟩

end DualPair

/-! ## Transporting along an equality of functions -/

namespace DualPair

/-- A dual solution for `f` is one for any function equal to `f`.  The vector
families are unchanged, so all costs are too. -/
def ofEq {K : Type*} [Fintype K] {f g : (ι → σ) → O} (h : ∀ x, f x = g x)
    (P : DualPair K f) : DualPair K g where
  u := P.u
  v := P.v
  constraint x y := by
    rw [← h x, ← h y]
    exact P.constraint x y

theorem ofEq_isCostLe {K : Type*} [Fintype K] {f g : (ι → σ) → O} {c : ℝ}
    (h : ∀ x, f x = g x) {P : DualPair K f} (hP : P.IsCostLe c) :
    (P.ofEq h).IsCostLe c := hP

end DualPair

/-! ## Enlarging the dimension type -/

namespace DualPair

/-- Padding a dual solution with zero coordinates, along an injection of
dimension types.  Costs are unchanged.

This is what lets solutions built over *different* dimension types be fed to
`composeShared`, which needs a single type for all subproblems. -/
noncomputable def embedDim {K K' : Type*} [Fintype K] [DecidableEq K]
    [Fintype K'] [DecidableEq K'] {m : K → K'} (hm : Function.Injective m)
    {f : (ι → σ) → O} (P : DualPair K f) : DualPair K' f where
  u x i := fun k' => spread m (fun k => P.u x i k) k'
  v y i := fun k' => spread m (fun k => P.v y i k) k'
  constraint x y := by
    have hpt : ∀ i : ι,
        (∑ k' : K', spread m (fun k => P.u x i k) k'
            * spread m (fun k => P.v y i k) k')
          = ∑ k : K, P.u x i k * P.v y i k := by
      intro i
      rw [Finset.sum_congr rfl fun k' (_ : k' ∈ Finset.univ) =>
        spread_mul_spread hm k' (fun k => P.u x i k) (fun k => P.v y i k)]
      exact sum_spread hm _
    simp only [hpt]
    exact P.constraint x y

theorem embedDim_isCostLe {K K' : Type*} [Fintype K] [DecidableEq K]
    [Fintype K'] [DecidableEq K'] {m : K → K'} (hm : Function.Injective m)
    {f : (ι → σ) → O} {c : ℝ} (P : DualPair K f) (hP : P.IsCostLe c) :
    (P.embedDim hm).IsCostLe c := by
  have key : ∀ (U : (ι → σ) → ι → K → ℝ) (x : ι → σ) (i : ι),
      (∑ k' : K', spread m (fun k => U x i k) k' * spread m (fun k => U x i k) k')
        = ∑ k : K, U x i k * U x i k := by
    intro U x i
    rw [Finset.sum_congr rfl fun k' (_ : k' ∈ Finset.univ) =>
      spread_mul_spread hm k' (fun k => U x i k) (fun k => U x i k)]
    exact sum_spread hm _
  refine ⟨fun x => ?_, fun y => ?_⟩
  · show (∑ i : ι, ∑ k' : K', spread m (fun k => P.u x i k) k'
      * spread m (fun k => P.u x i k) k') ≤ c
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => key P.u x i]
    exact hP.1 x
  · show (∑ i : ι, ∑ k' : K', spread m (fun k => P.v y i k) k'
      * spread m (fun k => P.v y i k) k') ≤ c
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => key P.v y i]
    exact hP.2 y

end DualPair

end QuantumQueryComplexity
