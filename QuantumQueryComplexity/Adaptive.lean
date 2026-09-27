import QuantumQueryComplexity.Promise.HasDual
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Sigma

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Descriptor composition: adaptive branching at additive dual cost

A divide-and-conquer algorithm first computes a *descriptor* `D x` — in the
longest-distinct-substring recursion, the anchors that name the compressed
subinstance — and then solves a subproblem **whose identity depends on
`D x`**.  Algorithmically only the branch actually taken is paid for.  Every
composition tool in this development instead pays for all of them
(`combine'`/`sharedFun` cost `2 ∑ₚ cₚ` over *all* subproblems), and inside a
recursion that multiplicative loss is fatal.

The descriptor composition rule is
to condition with orthonormal descriptor tags.  With `Fiber D d` the promise
`{x // D x = d}`, given

* a dual solution for `D` on the ambient promise, of cost `g`, and
* for **every** `d`, a dual solution for the value `T` on `Fiber D d`, of
  cost `c` (dimensions may differ with `d` — they are direct-summed),

the **joint** `x ↦ (D x, T x)` has a dual solution of cost `g + c` on the
ambient promise:

  `u x i = u⁰ x i  ⊕  e_{D x} ⊗ u^{D x} ⟨x, _⟩ i`

(`tagVec`: input `x` writes only in the block tagged by its own descriptor
value).  On a descriptor-unequal pair the tags are orthogonal, so the branch
term vanishes — exactly when its constraint would have been meaningless,
the two inputs lying on different promises — and the descriptor solution
already reports `1`.  On a descriptor-equal pair the tags are invisible and
the branch solution reports `[T x ≠ T y]`.  Masses add with no constant
factor, per input and on each side separately
(`descriptorCompose_sum_u_sq`).

**The joint-output discipline.**  The construction gives a dual for the pair
`(D x, T x)` and *cannot* give one for `T` alone: on a pair with `D x ≠ D y`
but `T x = T y` it reports `1`, where a dual for `T` needs `0`.  `ofKer`
cannot repair this — the projection `(d, t) ↦ t` is not injective on the
range.  So every function in a descriptor recursion exports its full
descriptor chain, and consumers project inside *outer* functions (the
weighted scan's value map), never by recoding a joint output.
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} [DecidableEq σ]
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Δ : Type} [Fintype Δ] [DecidableEq Δ]
variable {V : Type} [DecidableEq V]

/-! ## Conditional promises -/

/-- The fiber of a descriptor over one of its values, as a promise domain. -/
abbrev Fiber (D : X → Δ) (d : Δ) : Type := {x : X // D x = d}

/-- Querying a fiber input is querying the underlying input. -/
def fiberRead (read : X → ι → σ) (D : X → Δ) (d : Δ) : Fiber D d → ι → σ :=
  fun z => read z.val

@[simp] lemma fiberRead_apply (read : X → ι → σ) (D : X → Δ) (d : Δ)
    (z : Fiber D d) (i : ι) : fiberRead read D d z i = read z.val i := rfl

/-! ## The tagged branch vectors -/

/-- The branch block of the composed solution: input `x` writes the vectors
of its own branch `D x` into the block tagged `D x`, and zero elsewhere.
The tags are what implement conditioning. -/
def tagVec (D : X → Δ) {K : Δ → Type}
    (w : ∀ d, Fiber D d → ι → K d → ℝ) (x : X) (i : ι) : (Σ d, K d) → ℝ
  | ⟨d, k⟩ => if h : D x = d then w d ⟨x, h⟩ i k else 0

variable {D : X → Δ} {K : Δ → Type} [∀ d, Fintype (K d)]

/-- **Descriptor-unequal pairs see nothing**: the two inputs write in
different blocks. -/
lemma sum_tagVec_mul_of_ne {wu wv : ∀ d, Fiber D d → ι → K d → ℝ}
    {x y : X} (hne : D x ≠ D y) (i : ι) :
    (∑ p : Σ d, K d, tagVec D wu x i p * tagVec D wv y i p) = 0 := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_eq_zero fun d _ => Finset.sum_eq_zero fun k _ => ?_
  by_cases hx : D x = d
  · have hy : D y ≠ d := fun h => hne (hx.trans h.symm)
    simp [tagVec, hy]
  · simp [tagVec, hx]

/-- **Descriptor-equal pairs see exactly their common branch.** -/
lemma sum_tagVec_mul_of_eq {wu wv : ∀ d, Fiber D d → ι → K d → ℝ}
    {x y : X} {d : Δ} (hx : D x = d) (hy : D y = d) (i : ι) :
    (∑ p : Σ d, K d, tagVec D wu x i p * tagVec D wv y i p)
      = ∑ k : K d, wu d ⟨x, hx⟩ i k * wv d ⟨y, hy⟩ i k := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Finset.sum_eq_single_of_mem d (Finset.mem_univ d)]
  · exact Finset.sum_congr rfl fun k _ => by
      simp only [tagVec, dif_pos hx, dif_pos hy]
  · intro d' _ hd'
    refine Finset.sum_eq_zero fun k _ => ?_
    have hxd : D x ≠ d' := fun h => hd' (h.symm.trans hx)
    simp [tagVec, hxd]

/-! ## The composition -/

namespace DualPairOn

variable {read : X → ι → σ} {T : X → V} {K₀ : Type} [Fintype K₀]

/-- **Descriptor composition**.  A solution for the descriptor
`D` on the ambient promise, plus a solution for the value `T` on every
fiber, give a solution for the **joint** `x ↦ (D x, T x)`. -/
def descriptorCompose (Q : DualPairOn read K₀ D)
    (R : ∀ d, DualPairOn (fiberRead read D d) (K d) (fun z => T z.val)) :
    DualPairOn read (K₀ ⊕ Σ d, K d) (fun x => (D x, T x)) where
  u x i := Sum.elim (Q.u x i) (tagVec D (fun d => (R d).u) x i)
  v y i := Sum.elim (Q.v y i) (tagVec D (fun d => (R d).v) y i)
  constraint x y := by
    classical
    -- split every masked inner product into descriptor part and branch part
    have hpt : ∀ i : ι,
        (if read x i = read y i then (0 : ℝ)
          else ∑ c : K₀ ⊕ Σ d, K d,
            Sum.elim (Q.u x i) (tagVec D (fun d => (R d).u) x i) c *
              Sum.elim (Q.v y i) (tagVec D (fun d => (R d).v) y i) c)
          = (if read x i = read y i then (0 : ℝ)
              else ∑ k : K₀, Q.u x i k * Q.v y i k)
            + (if read x i = read y i then (0 : ℝ)
                else ∑ p : Σ d, K d, tagVec D (fun d => (R d).u) x i p *
                  tagVec D (fun d => (R d).v) y i p) := by
      intro i
      by_cases hi : read x i = read y i
      · simp [hi]
      · rw [if_neg hi, if_neg hi, if_neg hi, Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hpt i,
      Finset.sum_add_distrib, Q.constraint x y]
    by_cases hD : D x = D y
    · -- same branch: the tags are invisible and the branch solution answers
      rw [if_pos hD, zero_add]
      -- the fiber promise reads exactly like the ambient one (definitionally)
      have hcon : (∑ i : ι, if read x i = read y i then (0 : ℝ)
              else ∑ k : K (D x), (R (D x)).u ⟨x, rfl⟩ i k *
                (R (D x)).v ⟨y, hD.symm⟩ i k)
            = if T x = T y then (0 : ℝ) else 1 :=
        (R (D x)).constraint ⟨x, rfl⟩ ⟨y, hD.symm⟩
      have hrw : ∀ i : ι,
          (if read x i = read y i then (0 : ℝ)
            else ∑ p : Σ d, K d, tagVec D (fun d => (R d).u) x i p *
              tagVec D (fun d => (R d).v) y i p)
            = (if read x i = read y i then (0 : ℝ)
                else ∑ k : K (D x), (R (D x)).u ⟨x, rfl⟩ i k *
                  (R (D x)).v ⟨y, hD.symm⟩ i k) := by
        intro i
        by_cases hi : read x i = read y i
        · rw [if_pos hi, if_pos hi]
        · rw [if_neg hi, if_neg hi, sum_tagVec_mul_of_eq rfl hD.symm]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hrw i, hcon]
      by_cases hT : T x = T y
      · rw [if_pos hT, if_pos (by rw [hD, hT])]
      · rw [if_neg hT, if_neg (by simp [hT])]
    · -- different branches: orthogonal tags, and the descriptor answers
      rw [if_neg hD]
      have hzero : ∀ i : ι,
          (if read x i = read y i then (0 : ℝ)
            else ∑ p : Σ d, K d, tagVec D (fun d => (R d).u) x i p *
              tagVec D (fun d => (R d).v) y i p) = 0 := by
        intro i
        by_cases hi : read x i = read y i
        · rw [if_pos hi]
        · rw [if_neg hi, sum_tagVec_mul_of_ne hD]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hzero i,
        Finset.sum_const_zero, add_zero, if_neg (by simp [hD])]

@[simp] lemma descriptorCompose_u_inl (Q : DualPairOn read K₀ D)
    (R : ∀ d, DualPairOn (fiberRead read D d) (K d) (fun z => T z.val))
    (x : X) (i : ι) (k : K₀) :
    (Q.descriptorCompose R).u x i (Sum.inl k) = Q.u x i k := rfl

@[simp] lemma descriptorCompose_u_inr (Q : DualPairOn read K₀ D)
    (R : ∀ d, DualPairOn (fiberRead read D d) (K d) (fun z => T z.val))
    (x : X) (i : ι) (p : Σ d, K d) :
    (Q.descriptorCompose R).u x i (Sum.inr p)
      = tagVec D (fun d => (R d).u) x i p := rfl

@[simp] lemma descriptorCompose_v_inl (Q : DualPairOn read K₀ D)
    (R : ∀ d, DualPairOn (fiberRead read D d) (K d) (fun z => T z.val))
    (y : X) (i : ι) (k : K₀) :
    (Q.descriptorCompose R).v y i (Sum.inl k) = Q.v y i k := rfl

@[simp] lemma descriptorCompose_v_inr (Q : DualPairOn read K₀ D)
    (R : ∀ d, DualPairOn (fiberRead read D d) (K d) (fun z => T z.val))
    (y : X) (i : ι) (p : Σ d, K d) :
    (Q.descriptorCompose R).v y i (Sum.inr p)
      = tagVec D (fun d => (R d).v) y i p := rfl

/-- **The mass at one input splits exactly**: descriptor mass plus the mass
of *its own* branch — no sum over the other branches.  This per-input form is
what weighted uses of the composition need. -/
lemma descriptorCompose_sum_u_sq (Q : DualPairOn read K₀ D)
    (R : ∀ d, DualPairOn (fiberRead read D d) (K d) (fun z => T z.val))
    (x : X) :
    (∑ i : ι, ∑ c : K₀ ⊕ Σ d, K d,
        (Q.descriptorCompose R).u x i c * (Q.descriptorCompose R).u x i c)
      = (∑ i : ι, ∑ k : K₀, Q.u x i k * Q.u x i k)
        + ∑ i : ι, ∑ k : K (D x),
            (R (D x)).u ⟨x, rfl⟩ i k * (R (D x)).u ⟨x, rfl⟩ i k := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_sum_type]
  simp only [descriptorCompose_u_inl, descriptorCompose_u_inr]
  rw [sum_tagVec_mul_of_eq rfl rfl]

/-- The `v`-side mass splits the same way. -/
lemma descriptorCompose_sum_v_sq (Q : DualPairOn read K₀ D)
    (R : ∀ d, DualPairOn (fiberRead read D d) (K d) (fun z => T z.val))
    (y : X) :
    (∑ i : ι, ∑ c : K₀ ⊕ Σ d, K d,
        (Q.descriptorCompose R).v y i c * (Q.descriptorCompose R).v y i c)
      = (∑ i : ι, ∑ k : K₀, Q.v y i k * Q.v y i k)
        + ∑ i : ι, ∑ k : K (D y),
            (R (D y)).v ⟨y, rfl⟩ i k * (R (D y)).v ⟨y, rfl⟩ i k := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_sum_type]
  simp only [descriptorCompose_v_inl, descriptorCompose_v_inr]
  rw [sum_tagVec_mul_of_eq rfl rfl]

/-- **The cost of a descriptor composition is `g + c`** — the descriptor plus
*one* branch, `max` over branches rather than `∑`, with constant `1`. -/
theorem descriptorCompose_isCostLe {g c : ℝ} (Q : DualPairOn read K₀ D)
    (R : ∀ d, DualPairOn (fiberRead read D d) (K d) (fun z => T z.val))
    (hQ : Q.IsCostLe g) (hR : ∀ d, (R d).IsCostLe c) :
    (Q.descriptorCompose R).IsCostLe (g + c) := by
  constructor
  · intro x
    rw [descriptorCompose_sum_u_sq]
    exact add_le_add (hQ.1 x) ((hR (D x)).1 ⟨x, rfl⟩)
  · intro y
    rw [descriptorCompose_sum_v_sq]
    exact add_le_add (hQ.2 y) ((hR (D y)).2 ⟨y, rfl⟩)

end DualPairOn

/-! ## The bundled form -/

/-- **Descriptor composition, bundled.**  Branch dimensions are hidden and may
differ from branch to branch; the sigma type direct-sums them. -/
theorem HasDualOn.descriptorCompose {read : X → ι → σ} {T : X → V} {g c : ℝ}
    (hQ : HasDualOn read D g)
    (hR : ∀ d : Δ, HasDualOn (fiberRead read D d) (fun z : Fiber D d => T z.val) c) :
    HasDualOn read (fun x => (D x, T x)) (g + c) := by
  obtain ⟨K₀, hK₀, Q, hQc⟩ := hQ
  choose K hK R hRc using hR
  letI := hK
  exact ⟨K₀ ⊕ Σ d, K d, inferInstance, Q.descriptorCompose R,
    DualPairOn.descriptorCompose_isCostLe Q R hQc hRc⟩

/-- **The transcript case**: when the value is determined by the descriptor,
the joint costs no more than the descriptor itself.  (Stated through the
joint output, per the joint-output discipline.) -/
theorem HasDualOn.descriptorCompose_const {read : X → ι → σ} {T : X → V}
    {g : ℝ} (hQ : HasDualOn read D g)
    (hT : ∀ x y, D x = D y → T x = T y) :
    HasDualOn read (fun x => (D x, T x)) g := by
  have h := hQ.descriptorCompose (T := T) (c := 0) fun d =>
    hasDualOn_of_const _ fun z w => hT z.val w.val (z.2.trans w.2.symm)
  rwa [add_zero] at h

/-- **The joint of two functions costs the sum.**  Descriptor composition with
the second function as the value: the first is the descriptor, and on each of
its fibers the second is solved by the ambient solution (`comap`).  Note the
absence of a factor `2` — `HasDual.combine₂` pays `2(c₀+c₁)` for the same
joint, because it cannot condition. -/
theorem HasDualOn.pair {read : X → ι → σ} {f₁ : X → Δ} {f₂ : X → V} {c₁ c₂ : ℝ}
    (h₁ : HasDualOn read f₁ c₁) (h₂ : HasDualOn read f₂ c₂) :
    HasDualOn read (fun x => (f₁ x, f₂ x)) (c₁ + c₂) :=
  h₁.descriptorCompose fun d => h₂.comap (fun z : Fiber f₁ d => z.val)

/-! ## Descriptor chains

An adaptive procedure conditions repeatedly: level `j` performs a test whose
identity depends on the outcomes of levels `< j`.  Iterating the theorem with
*the transcript so far* as the descriptor costs the sum of the level costs —
`m · g` for `m` levels of cost `g`.  With the levels instantiated as windowed
distinctness tests this is the dual-side form of noisy binary search
: `⌈log₂ s⌉` levels of cost `8 s^{2/3}`.

The transcript is padded to full length with a fixed value so that its type
stays finite; `preTrans Dfun d₀ j` is the transcript of the first `j`
levels. -/

section Chain

variable {m : ℕ}

/-- The transcript of the first `j` descriptor levels, padded with `d₀`. -/
def preTrans (Dfun : Fin m → X → Δ) (d₀ : Δ) (j : ℕ) (x : X) : Fin m → Δ :=
  fun i => if (i : ℕ) < j then Dfun i x else d₀

/-- Extending a transcript by one level is exactly taking the joint of the
transcript so far with the next descriptor. -/
lemma preTrans_succ_iff (Dfun : Fin m → X → Δ) (d₀ : Δ) {j : ℕ} (hj : j < m)
    (x y : X) :
    (preTrans Dfun d₀ j x = preTrans Dfun d₀ j y
        ∧ Dfun ⟨j, hj⟩ x = Dfun ⟨j, hj⟩ y)
      ↔ preTrans Dfun d₀ (j + 1) x = preTrans Dfun d₀ (j + 1) y := by
  constructor
  · rintro ⟨hpre, hlast⟩
    funext i
    simp only [preTrans]
    by_cases hi : (i : ℕ) < j + 1
    · rw [if_pos hi, if_pos hi]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · have hc := congrFun hpre i
        simpa [preTrans, hlt] using hc
      · have hie : i = ⟨j, hj⟩ := Fin.ext heq
        rw [hie]
        exact hlast
    · rw [if_neg hi, if_neg hi]
  · intro h
    refine ⟨?_, ?_⟩
    · funext i
      simp only [preTrans]
      by_cases hi : (i : ℕ) < j
      · rw [if_pos hi, if_pos hi]
        have hc := congrFun h i
        simpa [preTrans, Nat.lt_succ_of_lt hi] using hc
      · rw [if_neg hi, if_neg hi]
    · have hc := congrFun h ⟨j, hj⟩
      simpa [preTrans] using hc

/-- **The chain bound, by induction on the number of levels.** -/
theorem hasDualOn_preTrans {read : X → ι → σ} (Dfun : Fin m → X → Δ) (d₀ : Δ)
    {g : ℝ}
    (h : ∀ (j : Fin m) (t : Fin m → Δ),
      HasDualOn (fiberRead read (preTrans Dfun d₀ (j : ℕ)) t)
        (fun z => Dfun j z.val) g) :
    ∀ j : ℕ, j ≤ m → HasDualOn read (preTrans Dfun d₀ j) ((j : ℝ) * g) := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : HasDualOn read (preTrans Dfun d₀ 0) 0 := by
      refine hasDualOn_of_const read (f := preTrans Dfun d₀ 0) fun x y => ?_
      funext i
      simp [preTrans]
    simpa using h0
  | succ j ih =>
    intro hj
    have hjm : j < m := hj
    have hstep := (ih (Nat.le_of_succ_le hj)).descriptorCompose
      (T := fun x => Dfun ⟨j, hjm⟩ x) (c := g) fun t => h ⟨j, hjm⟩ t
    have hker : HasDualOn read (preTrans Dfun d₀ (j + 1)) ((j : ℝ) * g + g) :=
      hstep.ofKer (f' := preTrans Dfun d₀ (j + 1)) fun x y => by
        rw [Prod.mk.injEq]
        exact preTrans_succ_iff Dfun d₀ hjm x y
    exact hker.mono (le_of_eq (by push_cast; ring))

/-- **The full transcript** of `m` adaptive levels, each costing `g`, has a
dual solution of cost `m · g`. -/
theorem hasDualOn_transcript {read : X → ι → σ} (Dfun : Fin m → X → Δ)
    (d₀ : Δ) {g : ℝ}
    (h : ∀ (j : Fin m) (t : Fin m → Δ),
      HasDualOn (fiberRead read (preTrans Dfun d₀ (j : ℕ)) t)
        (fun z => Dfun j z.val) g) :
    HasDualOn read (fun x i => Dfun i x) ((m : ℝ) * g) := by
  refine (hasDualOn_preTrans Dfun d₀ h m le_rfl).ofEq fun x => ?_
  funext i
  simp [preTrans, i.isLt]

/-- **A non-adaptive family**: `m` functions, each with a dual of cost `g` on
the ambient promise, have a *joint* dual of cost `m · g`.  Iterated
`HasDualOn.pair`, with the chain machinery doing the induction; the
unconditioned `HasDual.combine'` would pay `2 ∑ c` for the same joint. -/
theorem hasDualOn_family {read : X → ι → σ} (F : Fin m → X → Δ) (d₀ : Δ) {g : ℝ}
    (h : ∀ ℓ, HasDualOn read (F ℓ) g) :
    HasDualOn read (fun x ℓ => F ℓ x) ((m : ℝ) * g) :=
  hasDualOn_transcript F d₀ fun j t =>
    (h j).comap (fun z : Fiber (preTrans F d₀ (j : ℕ)) t => z.val)

end Chain

/-! ## The total forms

The same calculus for a total development, through the identity promise
(`HasDual.of_hasDualOn_id`).  These are the forms an adaptive *algorithm*
calls: compute a descriptor, then run the sub-test its value selects. -/

section Total

variable [Fintype σ]

/-- **The adaptive call.**  A descriptor `D` of cost `g`, and for every value
`d` a branch target `T d` of cost `c`, give the joint
`x ↦ (D x, T (D x) x)` at cost `g + c` — *one* branch, not all of them, and
with no factor in the number of branches. -/
theorem HasDual.adaptiveCall {D : (ι → σ) → Δ} {T : Δ → (ι → σ) → V} {g c : ℝ}
    (hD : HasDual D g) (hT : ∀ d, HasDual (T d) c) :
    HasDual (fun x => (D x, T (D x) x)) (g + c) := by
  refine HasDual.of_hasDualOn_id (HasDualOn.descriptorCompose (D := D)
    (T := fun x => T (D x) x) hD.hasDualOn fun d => ?_)
  refine (((hT d).restrictToOn (fun z : Fiber D d => z.val)).ofEq fun z => ?_)
  rw [z.2]

/-- The special case of a branch family that does not depend on the
descriptor: the joint of two functions, at the sum of their costs.  (As
always, the conclusion is about the **joint**; the joint-output discipline
above forbids projecting the branch value back out of it.) -/
theorem HasDual.adaptiveCall_const {D : (ι → σ) → Δ} {T : (ι → σ) → V} {g c : ℝ}
    (hD : HasDual D g) (hT : HasDual T c) :
    HasDual (fun x => (D x, T x)) (g + c) :=
  HasDual.adaptiveCall (T := fun _ => T) hD fun _ => hT

/-- **A transcript of `m` adaptive levels** costs `m · g`. -/
theorem HasDual.adaptiveTranscript {m : ℕ} (Dfun : Fin m → (ι → σ) → Δ) (d₀ : Δ)
    {g : ℝ}
    (h : ∀ (j : Fin m) (t : Fin m → Δ),
      HasDualOn (fiberRead (id : (ι → σ) → ι → σ) (preTrans Dfun d₀ (j : ℕ)) t)
        (fun z => Dfun j z.val) g) :
    HasDual (fun x i => Dfun i x) ((m : ℝ) * g) :=
  HasDual.of_hasDualOn_id (hasDualOn_transcript Dfun d₀ h)

end Total

/-! ## Sanity check: adaptive indexing

`T x = x (1 + x 0)` on three bits, with descriptor `D x = x 0`: the joint
costs `2 + 2 = 4`, the descriptor being one coordinate and the value being
one coordinate *once the descriptor is fixed*.  The unconditioned tools would
pay for both candidate coordinates. -/

section Example

/-- The coordinate the value is read from, as a function of the descriptor. -/
private def idxOf (b : Bool) : Fin 3 := if b then 2 else 1

private example :
    HasDualOn (fun x : Fin 3 → Bool => x)
      (fun x => (x 0, x (idxOf (x 0)))) (2 + 2) := by
  have hD : HasDualOn (fun x : Fin 3 → Bool => x) (fun x => x 0) 2 :=
    (hasDual_ofCoord (ι := Fin 3) (σ := Bool) 0 id).restrictToOn _
  refine hD.descriptorCompose fun d => ?_
  have h := (hasDual_ofCoord (ι := Fin 3) (σ := Bool) (idxOf d) id).restrictToOn
    (fiberRead (fun x : Fin 3 → Bool => x) (fun x => x 0) d)
  refine h.ofEq fun z => ?_
  have hz : z.val 0 = d := z.2
  simp only [id_eq, fiberRead_apply, hz]

end Example

end QuantumQueryComplexity
