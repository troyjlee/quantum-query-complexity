import QuantumQueryComplexity.LearningGraph.Cut
import QuantumQueryComplexity.HasDual
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# From a learning-graph flow to a dual solution

The learning-graph complexity theorem: a flow with negative complexity
`𝒞₀ = ∑_e ω_e²` and positive complexity `𝒞₁ = max_x ∑_e (p_e/ω_e)²` yields a
feasible dual solution of cost `√(𝒞₀ 𝒞₁)`, hence `ADV± ≤ √(𝒞₀ 𝒞₁)`.

The vectors live in `Bool × (edges) × (ι → Option σ)`: a side bit, an edge,
and the loaded assignment `setMask x S`.  On edge `e` a positive input
carries `λ · p x e / ω e` on side `!true`, a negative input `λ⁻¹ · ω e` on
side `false` (`u`) — and the mirror images on the other side (`v`).  The side
bit makes every pairing between inputs with equal output vanish structurally,
so the LMRSS equality constraints are free; for a positive/negative pair the
mask factors compare the loaded assignments and the pairing telescopes, by
the cut identity, to the unit of flow leaving the source.  Balancing with
`λ² = √(𝒞₀/𝒞₁)` equalises all four cost sums at `√(𝒞₀ 𝒞₁)`.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {f : (ι → σ) → Bool}

/-- The scalar an input carries on an edge: positive inputs carry the scaled
flow `λ · p/ω`, negative inputs the scaled half-weight `λ⁻¹ · ω`. -/
noncomputable def LGFlow.scal (L : LGFlow f) (lam : ℝ) (x : ι → σ)
    (e : Finset ι × ι) : ℝ :=
  if f x = true then lam * (L.p x e / L.ω e) else lam⁻¹ * L.ω e

/-- On every edge, a positive/negative pair of scalars multiplies out to the
flow: the `λ`'s cancel and `(p/ω)·ω = p`, the latter because `supp` puts the
flow on weighted edges (and division by zero is zero in Lean). -/
lemma LGFlow.scal_mul_scal (L : LGFlow f) {lam : ℝ} (hlam : lam ≠ 0)
    {x y : ι → σ} (hx : f x = true) (hy : f y = false) (e : Finset ι × ι) :
    L.scal lam x e * L.scal lam y e = L.p x e := by
  rw [LGFlow.scal, LGFlow.scal, if_pos hx, if_neg (by rw [hy]; simp)]
  by_cases hω : L.ω e = 0
  · have hp : L.p x e = 0 := by
      by_contra hp
      exact L.supp x e hx hp hω
    rw [hω, hp]
    simp
  · field_simp

/-- The mirror image: the second input positive. -/
lemma LGFlow.scal_mul_scal' (L : LGFlow f) {lam : ℝ} (hlam : lam ≠ 0)
    {x y : ι → σ} (hx : f x = false) (hy : f y = true) (e : Finset ι × ι) :
    L.scal lam x e * L.scal lam y e = L.p y e := by
  rw [mul_comm]
  exact L.scal_mul_scal hlam hy hx e

/-- The cost of the scalars: `λ²𝒞₁` for a positive input, `λ⁻²𝒞₀` for a
negative one. -/
lemma LGFlow.sum_scal_sq (L : LGFlow f) (lam : ℝ) (x : ι → σ) :
    (∑ e : Finset ι × ι, L.scal lam x e * L.scal lam x e)
    = if f x = true then lam ^ 2 * ∑ e : Finset ι × ι, (L.p x e / L.ω e) ^ 2
      else lam⁻¹ ^ 2 * ∑ e : Finset ι × ι, L.ω e ^ 2 := by
  by_cases hx : f x = true
  · rw [if_pos hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [LGFlow.scal, if_pos hx]
    ring
  · rw [if_neg hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [LGFlow.scal, if_neg hx]
    ring

/-- The dual vector family: a side bit, an edge, and the loaded assignment.
The `u` family uses the side `!(f x)`, the `v` family the side `f y`. -/
noncomputable def LGFlow.vec (L : LGFlow f) (lam : ℝ) (b : Bool) (x : ι → σ)
    (i : ι) (k : Bool × (Finset ι × ι) × (ι → Option σ)) : ℝ :=
  (if k.1 = b then (1 : ℝ) else 0) * ((if i = k.2.1.2 then (1 : ℝ) else 0)
    * ((if k.2.2 = setMask x k.2.1.1 then (1 : ℝ) else 0) * L.scal lam x k.2.1))

/-- Collapsing a doubled delta against a function of the index. -/
private lemma sum_delta_delta {β : Type*} [Fintype β] [DecidableEq β]
    (m₁ m₂ : β) (g : β → ℝ) :
    (∑ α : β, (if α = m₁ then (1 : ℝ) else 0) * ((if α = m₂ then (1 : ℝ) else 0) * g α))
    = (if m₁ = m₂ then (1 : ℝ) else 0) * g m₁ := by
  rw [Finset.sum_congr rfl fun α (_ : α ∈ Finset.univ) =>
    show (if α = m₁ then (1 : ℝ) else 0) * ((if α = m₂ then (1 : ℝ) else 0) * g α)
      = if α = m₁ then (if m₁ = m₂ then (1 : ℝ) else 0) * g m₁ else 0 from by
      by_cases h1 : α = m₁
      · subst h1
        rw [if_pos rfl, if_pos rfl, one_mul]
      · rw [if_neg h1, if_neg h1, zero_mul],
    Finset.sum_ite_eq' Finset.univ m₁
      fun _ => (if m₁ = m₂ then (1 : ℝ) else 0) * g m₁,
    if_pos (Finset.mem_univ _)]

/-- The pairing of two dual vectors at a fixed coordinate: the side bits must
agree, the masks are compared, and the scalars multiply. -/
lemma LGFlow.sum_vec_mul_vec (L : LGFlow f) (lam : ℝ) (b c : Bool)
    (x y : ι → σ) (i : ι) :
    (∑ k : Bool × (Finset ι × ι) × (ι → Option σ),
      L.vec lam b x i k * L.vec lam c y i k)
    = (if b = c then (1 : ℝ) else 0)
        * ∑ e : Finset ι × ι, (if i = e.2 then (1 : ℝ) else 0)
          * ((if setMask x e.1 = setMask y e.1 then (1 : ℝ) else 0)
            * (L.scal lam x e * L.scal lam y e)) := by
  rw [Fintype.sum_prod_type]
  have hinner : ∀ t : Bool,
      (∑ q : (Finset ι × ι) × (ι → Option σ),
        L.vec lam b x i (t, q) * L.vec lam c y i (t, q))
      = (if t = b then (1 : ℝ) else 0) * ((if t = c then (1 : ℝ) else 0)
          * ∑ e : Finset ι × ι, (if i = e.2 then (1 : ℝ) else 0)
            * ((if setMask x e.1 = setMask y e.1 then (1 : ℝ) else 0)
              * (L.scal lam x e * L.scal lam y e))) := by
    intro t
    rw [Fintype.sum_prod_type]
    have hmask : ∀ e : Finset ι × ι,
        (∑ α : ι → Option σ,
          L.vec lam b x i (t, e, α) * L.vec lam c y i (t, e, α))
        = (if t = b then (1 : ℝ) else 0) * ((if t = c then (1 : ℝ) else 0)
            * ((if i = e.2 then (1 : ℝ) else 0)
              * ((if setMask x e.1 = setMask y e.1 then (1 : ℝ) else 0)
                * (L.scal lam x e * L.scal lam y e)))) := by
      intro e
      rw [Finset.sum_congr rfl fun α (_ : α ∈ Finset.univ) =>
        show L.vec lam b x i (t, e, α) * L.vec lam c y i (t, e, α)
          = (if α = setMask x e.1 then (1 : ℝ) else 0)
            * ((if α = setMask y e.1 then (1 : ℝ) else 0)
              * ((if t = b then (1 : ℝ) else 0) * ((if t = c then (1 : ℝ) else 0)
                * ((if i = e.2 then (1 : ℝ) else 0)
                  * (L.scal lam x e * L.scal lam y e))))) from by
          show ((if t = b then (1 : ℝ) else 0) * ((if i = e.2 then (1 : ℝ) else 0)
              * ((if α = setMask x e.1 then (1 : ℝ) else 0) * L.scal lam x e)))
            * ((if t = c then (1 : ℝ) else 0) * ((if i = e.2 then (1 : ℝ) else 0)
              * ((if α = setMask y e.1 then (1 : ℝ) else 0) * L.scal lam y e))) = _
          by_cases hie : i = e.2
          · rw [if_pos hie]
            ring
          · rw [if_neg hie]
            ring,
        sum_delta_delta (setMask x e.1) (setMask y e.1) _]
      by_cases hmm : setMask x e.1 = setMask y e.1
      · rw [if_pos hmm, one_mul]
        ring
      · rw [if_neg hmm, zero_mul]
        ring
    rw [Finset.sum_congr rfl fun e (_ : e ∈ Finset.univ) => hmask e,
      ← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun t (_ : t ∈ Finset.univ) => hinner t,
    sum_delta_delta b c
      fun _ => ∑ e : Finset ι × ι, (if i = e.2 then (1 : ℝ) else 0)
        * ((if setMask x e.1 = setMask y e.1 then (1 : ℝ) else 0)
          * (L.scal lam x e * L.scal lam y e))]

/-- The cost sums of the vector family: the deltas collapse and each edge
contributes its squared scalar, independently of the side bit. -/
lemma LGFlow.sum_sum_vec_sq (L : LGFlow f) (lam : ℝ) (b : Bool) (x : ι → σ) :
    (∑ i : ι, ∑ k : Bool × (Finset ι × ι) × (ι → Option σ),
      L.vec lam b x i k * L.vec lam b x i k)
    = ∑ e : Finset ι × ι, L.scal lam x e * L.scal lam x e := by
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by
    rw [L.sum_vec_mul_vec lam b b x x i, if_pos rfl, one_mul]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
    show (if i = e.2 then (1 : ℝ) else 0)
        * ((if setMask x e.1 = setMask x e.1 then (1 : ℝ) else 0)
          * (L.scal lam x e * L.scal lam x e))
      = if i = e.2 then L.scal lam x e * L.scal lam x e else 0 from by
      rw [if_pos rfl, one_mul]
      by_cases hie : i = e.2
      · rw [if_pos hie, if_pos hie, one_mul]
      · rw [if_neg hie, if_neg hie, zero_mul],
    Finset.sum_ite_eq' Finset.univ e.2 fun _ => L.scal lam x e * L.scal lam x e,
    if_pos (Finset.mem_univ _)]

/-- The reduced constraint sum for a positive/negative pair: pushing the
coordinate guard inside, swapping the sums and collapsing `i = e.2` leaves
exactly the cut sum. -/
lemma LGFlow.cut_reduce (L : LGFlow f) {x y : ι → σ}
    (hx : f x = true) (hy : f y = false) :
    (∑ i : ι, if x i = y i then (0 : ℝ)
      else ∑ e : Finset ι × ι, (if i = e.2 then (1 : ℝ) else 0)
        * ((if setMask x e.1 = setMask y e.1 then (1 : ℝ) else 0)
          * L.p x e)) = 1 := by
  have hpush : ∀ i : ι, (if x i = y i then (0 : ℝ)
      else ∑ e : Finset ι × ι, (if i = e.2 then (1 : ℝ) else 0)
        * ((if setMask x e.1 = setMask y e.1 then (1 : ℝ) else 0) * L.p x e))
      = ∑ e : Finset ι × ι, (if x i = y i then (0 : ℝ)
          else (if i = e.2 then (1 : ℝ) else 0)
            * ((if setMask x e.1 = setMask y e.1 then (1 : ℝ) else 0)
              * L.p x e)) := by
    intro i
    by_cases hi : x i = y i
    · rw [if_pos hi]
      exact (Finset.sum_eq_zero fun e _ => if_pos hi).symm
    · rw [if_neg hi]
      exact Finset.sum_congr rfl fun e _ => (if_neg hi).symm
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hpush i,
    Finset.sum_comm]
  have hcollapse : ∀ e : Finset ι × ι,
      (∑ i : ι, if x i = y i then (0 : ℝ)
        else (if i = e.2 then (1 : ℝ) else 0)
          * ((if setMask x e.1 = setMask y e.1 then (1 : ℝ) else 0) * L.p x e))
      = if x e.2 = y e.2 then (0 : ℝ)
          else if setMask x e.1 = setMask y e.1 then L.p x e else 0 := by
    intro e
    have hper : ∀ i : ι, (if x i = y i then (0 : ℝ)
        else (if i = e.2 then (1 : ℝ) else 0)
          * ((if setMask x e.1 = setMask y e.1 then (1 : ℝ) else 0) * L.p x e))
        = if i = e.2 then (if x e.2 = y e.2 then (0 : ℝ)
            else if setMask x e.1 = setMask y e.1 then L.p x e else 0)
          else 0 := by
      intro i
      by_cases hie : i = e.2
      · subst hie
        rw [if_pos (rfl : e.2 = e.2), one_mul, if_pos (rfl : e.2 = e.2)]
        by_cases hxy : x e.2 = y e.2
        · rw [if_pos hxy, if_pos hxy]
        · rw [if_neg hxy, if_neg hxy]
          by_cases hmm : setMask x e.1 = setMask y e.1
          · rw [if_pos hmm, if_pos hmm, one_mul]
          · rw [if_neg hmm, if_neg hmm, zero_mul]
      · rw [if_neg hie, if_neg hie]
        by_cases hxy : x i = y i
        · rw [if_pos hxy]
        · rw [if_neg hxy, zero_mul]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hper i,
      Finset.sum_ite_eq' Finset.univ e.2
        (fun _ => if x e.2 = y e.2 then (0 : ℝ)
          else if setMask x e.1 = setMask y e.1 then L.p x e else 0),
      if_pos (Finset.mem_univ _)]
  rw [Finset.sum_congr rfl fun e (_ : e ∈ Finset.univ) => hcollapse e]
  exact L.sum_cut hx hy

/-- **The dual solution attached to a learning-graph flow.** -/
noncomputable def LGFlow.dualPair (L : LGFlow f) {lam : ℝ} (hlam : lam ≠ 0) :
    DualPair (Bool × (Finset ι × ι) × (ι → Option σ)) f where
  u x i := L.vec lam (!(f x)) x i
  v y i := L.vec lam (f y) y i
  constraint x y := by
    cases hfx : f x <;> cases hfy : f y
    · -- both negative: the side bits differ, everything vanishes
      rw [if_pos rfl]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : x i = y i
      · rw [if_pos hi]
      · rw [if_neg hi, L.sum_vec_mul_vec lam (!false) false x y i,
          if_neg (by simp), zero_mul]
    · -- x negative, y positive
      rw [if_neg (by simp)]
      have hterm : ∀ i : ι,
          (∑ k : Bool × (Finset ι × ι) × (ι → Option σ),
            L.vec lam (!false) x i k * L.vec lam true y i k)
          = ∑ e : Finset ι × ι, (if i = e.2 then (1 : ℝ) else 0)
              * ((if setMask y e.1 = setMask x e.1 then (1 : ℝ) else 0)
                * L.p y e) := by
        intro i
        rw [L.sum_vec_mul_vec lam (!false) true x y i, if_pos (by simp), one_mul]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [L.scal_mul_scal' hlam hfx hfy e]
        by_cases hmm : setMask x e.1 = setMask y e.1
        · rw [if_pos hmm, if_pos hmm.symm]
        · rw [if_neg hmm, if_neg (show ¬ setMask y e.1 = setMask x e.1 from
            fun hc => hmm hc.symm)]
      have hstep : (∑ i : ι, if x i = y i then (0 : ℝ)
          else ∑ k : Bool × (Finset ι × ι) × (ι → Option σ),
            L.vec lam (!false) x i k * L.vec lam true y i k)
          = ∑ i : ι, if y i = x i then (0 : ℝ)
              else ∑ e : Finset ι × ι, (if i = e.2 then (1 : ℝ) else 0)
                * ((if setMask y e.1 = setMask x e.1 then (1 : ℝ) else 0)
                  * L.p y e) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : x i = y i
        · rw [if_pos hi, if_pos hi.symm]
        · rw [if_neg hi, if_neg fun hc => hi hc.symm, hterm i]
      rw [hstep]
      exact L.cut_reduce hfy hfx
    · -- x positive, y negative
      rw [if_neg (by simp)]
      have hterm : ∀ i : ι,
          (∑ k : Bool × (Finset ι × ι) × (ι → Option σ),
            L.vec lam (!true) x i k * L.vec lam false y i k)
          = ∑ e : Finset ι × ι, (if i = e.2 then (1 : ℝ) else 0)
              * ((if setMask x e.1 = setMask y e.1 then (1 : ℝ) else 0)
                * L.p x e) := by
        intro i
        rw [L.sum_vec_mul_vec lam (!true) false x y i, if_pos (by simp), one_mul]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [L.scal_mul_scal hlam hfx hfy e]
      have hstep : (∑ i : ι, if x i = y i then (0 : ℝ)
          else ∑ k : Bool × (Finset ι × ι) × (ι → Option σ),
            L.vec lam (!true) x i k * L.vec lam false y i k)
          = ∑ i : ι, if x i = y i then (0 : ℝ)
              else ∑ e : Finset ι × ι, (if i = e.2 then (1 : ℝ) else 0)
                * ((if setMask x e.1 = setMask y e.1 then (1 : ℝ) else 0)
                  * L.p x e) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : x i = y i
        · rw [if_pos hi, if_pos hi]
        · rw [if_neg hi, if_neg hi, hterm i]
      rw [hstep]
      exact L.cut_reduce hfx hfy
    · -- both positive: the side bits differ, everything vanishes
      rw [if_pos rfl]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : x i = y i
      · rw [if_pos hi]
      · rw [if_neg hi, L.sum_vec_mul_vec lam (!true) true x y i,
          if_neg (by simp), zero_mul]

/-- The cost of the learning-graph dual solution, before balancing. -/
lemma LGFlow.dualPair_isCostLe (L : LGFlow f) {lam : ℝ} (hlam : lam ≠ 0)
    {c : ℝ}
    (hpos : ∀ x, f x = true →
      lam ^ 2 * (∑ e : Finset ι × ι, (L.p x e / L.ω e) ^ 2) ≤ c)
    (hneg : ∀ x, f x = false →
      lam⁻¹ ^ 2 * (∑ e : Finset ι × ι, L.ω e ^ 2) ≤ c) :
    (L.dualPair hlam).IsCostLe c := by
  have hboth : ∀ x : ι → σ,
      (∑ e : Finset ι × ι, L.scal lam x e * L.scal lam x e) ≤ c := by
    intro x
    rw [L.sum_scal_sq lam x]
    cases hfx : f x
    · rw [if_neg (by simp)]
      exact hneg x hfx
    · rw [if_pos rfl]
      exact hpos x hfx
  constructor
  · intro x
    rw [show (∑ i : ι, ∑ k : Bool × (Finset ι × ι) × (ι → Option σ),
        (L.dualPair hlam).u x i k * (L.dualPair hlam).u x i k)
      = ∑ i : ι, ∑ k : Bool × (Finset ι × ι) × (ι → Option σ),
        L.vec lam (!(f x)) x i k * L.vec lam (!(f x)) x i k from rfl,
      L.sum_sum_vec_sq lam (!(f x)) x]
    exact hboth x
  · intro x
    rw [show (∑ i : ι, ∑ k : Bool × (Finset ι × ι) × (ι → Option σ),
        (L.dualPair hlam).v x i k * (L.dualPair hlam).v x i k)
      = ∑ i : ι, ∑ k : Bool × (Finset ι × ι) × (ι → Option σ),
        L.vec lam (f x) x i k * L.vec lam (f x) x i k from rfl,
      L.sum_sum_vec_sq lam (f x) x]
    exact hboth x

section TypePinned

variable {ι' : Type} [Fintype ι'] [DecidableEq ι']
variable {σ' : Type} [Fintype σ'] [DecidableEq σ']
variable {g : (ι' → σ') → Bool}

/-- **The learning-graph complexity theorem**: a flow of negative complexity
`𝒞₀` and positive complexity `𝒞₁` gives a dual solution of cost `√(𝒞₀ 𝒞₁)`. -/
theorem LGFlow.hasDual (L : LGFlow g) {C₀ C₁ : ℝ} (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hω : (∑ e : Finset ι' × ι', L.ω e ^ 2) ≤ C₀)
    (hp : ∀ x, g x = true → (∑ e : Finset ι' × ι', (L.p x e / L.ω e) ^ 2) ≤ C₁) :
    HasDual g (Real.sqrt (C₀ * C₁)) := by
  have hlampos : (0 : ℝ) < Real.sqrt (Real.sqrt (C₀ / C₁)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (div_pos hC₀ hC₁))
  have hlamsq : Real.sqrt (Real.sqrt (C₀ / C₁)) ^ 2 = Real.sqrt (C₀ / C₁) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have hkey1 : Real.sqrt (C₀ / C₁) * C₁ = Real.sqrt (C₀ * C₁) := by
    rw [show C₀ * C₁ = C₀ / C₁ * C₁ ^ 2 from by field_simp,
      Real.sqrt_mul (div_nonneg hC₀.le hC₁.le), Real.sqrt_sq hC₁.le]
  have hkey2 : Real.sqrt (C₁ / C₀) * C₀ = Real.sqrt (C₀ * C₁) := by
    rw [show C₀ * C₁ = C₁ / C₀ * C₀ ^ 2 from by field_simp,
      Real.sqrt_mul (div_nonneg hC₁.le hC₀.le), Real.sqrt_sq hC₀.le]
  have hlaminv : (Real.sqrt (Real.sqrt (C₀ / C₁)))⁻¹ ^ 2 = Real.sqrt (C₁ / C₀) := by
    rw [inv_pow, hlamsq, ← Real.sqrt_inv, inv_div]
  refine hasDual_of_dualPair (L.dualPair hlampos.ne') ?_
  refine L.dualPair_isCostLe hlampos.ne' (fun x hx => ?_) (fun x hx => ?_)
  · rw [hlamsq, ← hkey1]
    exact mul_le_mul_of_nonneg_left (hp x hx) (Real.sqrt_nonneg _)
  · rw [hlaminv, ← hkey2]
    exact mul_le_mul_of_nonneg_left hω (Real.sqrt_nonneg _)

end TypePinned

end QuantumQueryComplexity
