import QuantumQueryComplexity.Duality.MainOn
import QuantumQueryComplexity.SchurMultiplier
import QuantumQueryComplexity.Promise.HasDual

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1000000

/-!
# From a primal adversary budget to a dual certificate, for finite outputs

`Duality/MainOn.lean` proves exact strong duality on a promise domain for
**Boolean** outputs: every `c > advPMOn read f` is achieved by a feasible
`DualPairOn`.  The Boolean hypothesis enters exactly once, in the `±1`
masking trick `‖M ⊙ dualTargetOn f‖ ≤ ‖M‖`.

For an arbitrary (decidable) output type the same masking costs a factor of
two: the equal-output indicator `E_f(x, y) = [f x = f y]` is positive
semidefinite with unit diagonal (a Gram matrix of one-hot output vectors), so
the Schur-multiplier bound gives `‖M ⊙ E_f‖ ≤ ‖M‖`, and the disagreement mask
is `J − E_f`, whence `‖M ⊙ dualTargetOn f‖ ≤ 2‖M‖`.  Running the certificate
argument with this estimate, the separating certificate forces
`c < 2·advPMOn read f`, and the separation argument of `MainOn.lean` gives

    exists_dualPairOn_of_two_mul_advPMOn_lt :
      2 * advPMOn read f < c → ∃ m (P : DualPairOn read (Fin m) f), P.IsCostLe c

for **every** finite-output, read-determined promise problem — with no
`log |O|`, `√|σ|` or other cardinality factor.  No exact equality between the
all-pairs dual optimum and the primal value is claimed for nonbinary outputs.

The Boolean theorem and all its consumers are untouched; the separation body
is repeated here rather than refactored, so that nothing upstream moves.  The
bundled corollary `hasDualOn_three_mul_advPMOn` (`HasDualOn read f
(3·advPMOn read f)`, every read-determined `f`, including the constant ones)
is what the compositional prediction-tree theorem consumes.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-! ## The equal-output mask -/

section Mask

variable {X : Type*} [Fintype X] [DecidableEq X] {O : Type*} [DecidableEq O]

/-- The equal-output indicator matrix `[f x = f y]`. -/
def eqOutputOn (f : X → O) : Matrix X X ℝ :=
  Matrix.of fun x y => if f x = f y then 1 else 0

@[simp] lemma eqOutputOn_apply (f : X → O) (x y : X) :
    eqOutputOn f x y = if f x = f y then 1 else 0 := rfl

/-- `E_f` is the Gram matrix of the one-hot output vectors, hence positive
semidefinite. -/
lemma posSemidef_eqOutputOn (f : X → O) : (eqOutputOn f).PosSemidef := by
  classical
  set S : Finset O := Finset.image f Finset.univ with hS
  let W : Matrix X {o // o ∈ S} ℝ := Matrix.of fun x s => if f x = s.1 then 1 else 0
  have hW : eqOutputOn f = W * Wᴴ := by
    ext x y
    have hfx : f x ∈ S := Finset.mem_image_of_mem f (Finset.mem_univ x)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial, eqOutputOn,
      Matrix.of_apply, W]
    rw [Finset.sum_eq_single ⟨f x, hfx⟩]
    · simp only [if_true]
      by_cases h : f x = f y
      · simp [h]
      · simp [h, Ne.symm h]
    · intro s _ hs
      have hne : f x ≠ s.1 := fun h => hs (Subtype.ext h.symm)
      simp [hne]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hW]
  exact Matrix.posSemidef_self_mul_conjTranspose W

/-- Masking by the equal-output indicator does not increase the spectral
norm (Schur multiplier, unit diagonal). -/
lemma norm_hadamard_eqOutputOn_le (M : Matrix X X ℝ) (f : X → O) :
    ‖M ⊙ eqOutputOn f‖ ≤ ‖M‖ := by
  have h := norm_hadamard_posSemidef_le M (posSemidef_eqOutputOn f) (d := 1) zero_le_one
    (fun a => by simp [eqOutputOn])
  simpa using h

/-- **The finite-output masking estimate**: masking off the equal-output
pairs at most doubles the spectral norm. -/
lemma norm_hadamard_dualTargetOn_le_two (M : Matrix X X ℝ) (f : X → O) :
    ‖M ⊙ dualTargetOn f‖ ≤ 2 * ‖M‖ := by
  have hsplit : M ⊙ dualTargetOn f = M - M ⊙ eqOutputOn f := by
    ext x y
    simp only [Matrix.hadamard_apply, Matrix.sub_apply, dualTargetOn_apply, eqOutputOn_apply]
    split_ifs <;> ring
  rw [hsplit]
  have := norm_sub_le M (M ⊙ eqOutputOn f)
  linarith [norm_hadamard_eqOutputOn_le M f]

end Mask

/-! ## The target box for a general output type -/

section Box

variable {X : Type*} [Fintype X] [DecidableEq X] {O : Type*} [DecidableEq O]

/-- The target of the promise dual program for a general output type:
constraint block equal to `dualTargetOn f`, cost block in `[0, c]`
(`dualBoxOn` of `CompactOn.lean`, for any `O`). -/
def dualBoxOnGen (f : X → O) (c : ℝ) : Set (DualOmegaOn X → ℝ) :=
  {z | (∀ x y, z (Sum.inl (x, y)) = dualTargetOn f x y) ∧
    ∀ q : X × Bool, 0 ≤ z (Sum.inr q) ∧ z (Sum.inr q) ≤ c}

lemma convex_dualBoxOnGen (f : X → O) (c : ℝ) : Convex ℝ (dualBoxOnGen f c) := by
  rintro z ⟨hz1, hz2⟩ z' ⟨hz1', hz2'⟩ a b ha hb hab
  constructor
  · intro x y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz1 x y, hz1' x y]
    rw [← add_mul, hab, one_mul]
  · intro q
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · have := (hz2 q).1
      have := (hz2' q).1
      positivity
    · nlinarith [(hz2 q).2, (hz2' q).2, (hz2 q).1, (hz2' q).1]

lemma isClosed_dualBoxOnGen (f : X → O) (c : ℝ) : IsClosed (dualBoxOnGen f c) := by
  have hset : dualBoxOnGen f c =
      (⋂ (x : X) (y : X), {z : DualOmegaOn X → ℝ |
          z (Sum.inl (x, y)) = dualTargetOn f x y}) ∩
        ⋂ q : X × Bool,
          ({z : DualOmegaOn X → ℝ | 0 ≤ z (Sum.inr q)} ∩
            {z : DualOmegaOn X → ℝ | z (Sum.inr q) ≤ c}) := by
    ext z
    simp only [dualBoxOnGen, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  refine IsClosed.inter (isClosed_iInter fun x => isClosed_iInter fun y => ?_)
    (isClosed_iInter fun q => IsClosed.inter ?_ ?_)
  · exact isClosed_eq (continuous_apply _) continuous_const
  · exact isClosed_le continuous_const (continuous_apply _)
  · exact isClosed_le (continuous_apply _) continuous_const

/-- The corner of the box. -/
def dualCornerOnGen (f : X → O) (c : ℝ) : DualOmegaOn X → ℝ :=
  Sum.elim (fun q => dualTargetOn f q.1 q.2) (fun _ => c)

lemma dualCornerOnGen_mem {f : X → O} {c : ℝ} (hc : 0 ≤ c) :
    dualCornerOnGen f c ∈ dualBoxOnGen f c :=
  ⟨fun _ _ => rfl, fun _ => ⟨hc, le_refl c⟩⟩

end Box

/-! ## From a certificate to an adversary matrix, with the factor two -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {O : Type*} [DecidableEq O]

/-- **From a dual certificate to a primal witness, finite outputs.**  The
promise mirror of `lt_advPMOn_of_certificate` with the `±1` trick replaced by
the Schur-multiplier estimate; the adversary matrix is scaled by `1/4`
instead of `1/2`, and the conclusion is `c < 2·advPMOn`. -/
theorem lt_two_mul_advPMOn_of_certificate {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y)
    {Γ : Matrix X X ℝ} {p : X → ℝ} {c : ℝ}
    (hsym : ∀ x y, Γ y x = Γ x y) (hp : ∀ x, 0 < p x)
    (hquad : ∀ (i : ι) (s t : X → ℝ),
      |s ⬝ᵥ (Γ ⊙ advDOn read i) *ᵥ t|
        ≤ (∑ x, p x * (s x * s x)) + ∑ y, p y * (t y * t y))
    (hobj : 2 * c * (∑ x, p x) < ∑ x, ∑ y, Γ x y * dualTargetOn f x y) :
    c < 2 * advPMOn read f := by
  classical
  have hsum : 0 < ∑ x, p x := by
    rcases isEmpty_or_nonempty X with he | hne
    · exact absurd hobj (by simp)
    · exact Finset.sum_pos (fun x _ => hp x) Finset.univ_nonempty
  set r : X → ℝ := fun x => Real.sqrt (p x) with hr
  have hr0 : ∀ x, 0 < r x := fun x => Real.sqrt_pos.mpr (hp x)
  have hrr : ∀ x, r x * r x = p x := fun x => Real.mul_self_sqrt (hp x).le
  set Γ' : Matrix X X ℝ := Matrix.of fun x y => Γ x y / (r x * r y) with hΓ'
  have hΓ'sym : ∀ x y, Γ' y x = Γ' x y := by
    intro x y
    show Γ y x / (r y * r x) = Γ x y / (r x * r y)
    rw [hsym x y, mul_comm (r y) (r x)]
  have hmask : ∀ (i : ι) (x y : X),
      (Γ' ⊙ advDOn read i) x y = (Γ ⊙ advDOn read i) x y / (r x * r y) := by
    intro i x y
    rw [hadamard_advDOn_apply, hadamard_advDOn_apply]
    by_cases h : read x i = read y i
    · simp [h]
    · simp [h, hΓ']
  have hnorm : ∀ i : ι, ‖Γ' ⊙ advDOn read i‖ ≤ 2 := by
    intro i
    refine l2_opNorm_le_two_of_quadratic _ fun a b => ?_
    have e1 : (fun x => a x / r x) ⬝ᵥ (Γ ⊙ advDOn read i) *ᵥ (fun y => b y / r y)
        = a ⬝ᵥ (Γ' ⊙ advDOn read i) *ᵥ b := by
      simp only [dotProduct_mulVec_eq_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      rw [hmask i x y]
      have hx := (hr0 x).ne'
      have hy := (hr0 y).ne'
      field_simp
    have e2 : ∀ (w : X → ℝ),
        (∑ x, p x * ((w x / r x) * (w x / r x))) = w ⬝ᵥ w := by
      intro w
      rw [dotProduct]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hx := (hr0 x).ne'
      rw [← hrr x]
      field_simp
    have := hquad i (fun x => a x / r x) (fun y => b y / r y)
    rw [e1, e2 a, e2 b] at this
    exact this
  set Γ'' : Matrix X X ℝ := (4 : ℝ)⁻¹ • (Γ' ⊙ dualTargetOn f) with hΓ''
  have hadv : IsAdvMatrixOn f Γ'' := by
    constructor
    · ext x y
      show Γ'' y x = Γ'' x y
      simp only [hΓ'', Matrix.smul_apply, Matrix.hadamard_apply, smul_eq_mul,
        hΓ'sym x y, dualTargetOn_comm f x y]
    · intro x y hxy
      simp [hΓ'', Matrix.hadamard_apply, dualTargetOn, hxy]
  have hfeas : ∀ i : ι, ‖Γ'' ⊙ advDOn read i‖ ≤ 1 := by
    intro i
    have hswap : Γ'' ⊙ advDOn read i
        = (4 : ℝ)⁻¹ • ((Γ' ⊙ advDOn read i) ⊙ dualTargetOn f) := by
      ext x y
      simp only [hΓ'', Matrix.smul_apply, Matrix.hadamard_apply, smul_eq_mul]
      ring
    rw [hswap, norm_smul]
    have h1 : ‖(Γ' ⊙ advDOn read i) ⊙ dualTargetOn f‖ ≤ 2 * ‖Γ' ⊙ advDOn read i‖ :=
      norm_hadamard_dualTargetOn_le_two _ f
    have h2 : ‖(4 : ℝ)⁻¹‖ = (4 : ℝ)⁻¹ := by norm_num
    rw [h2]
    nlinarith [hnorm i, norm_nonneg ((Γ' ⊙ advDOn read i) ⊙ dualTargetOn f)]
  set R := Real.sqrt (∑ x, p x) with hR
  have hR0 : 0 < R := Real.sqrt_pos.mpr hsum
  have hRR : R * R = ∑ x, p x := Real.mul_self_sqrt hsum.le
  set a : X → ℝ := fun x => r x / R with ha
  have haa : a ⬝ᵥ a = 1 := by
    rw [dotProduct]
    have : ∀ x : X, a x * a x = p x / (R * R) := by
      intro x
      rw [ha]
      simp only []
      rw [div_mul_div_comm, hrr x]
    rw [Finset.sum_congr rfl fun x _ => this x, ← Finset.sum_div, hRR,
      div_self hsum.ne']
  have hval : a ⬝ᵥ Γ'' *ᵥ a
      = (∑ x, ∑ y, Γ x y * dualTargetOn f x y) / (4 * ∑ x, p x) := by
    rw [dotProduct_mulVec_eq_sum, ← hRR]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hx := (hr0 x).ne'
    have hy := (hr0 y).ne'
    have hRne := hR0.ne'
    show (r x / R) * ((4 : ℝ)⁻¹ * (Γ x y / (r x * r y) * dualTargetOn f x y)) *
        (r y / R) = _
    field_simp
  have hlt : c / 2 < a ⬝ᵥ Γ'' *ᵥ a := by
    rw [hval, lt_div_iff₀ (by positivity)]
    linarith [hobj]
  have hbound : a ⬝ᵥ Γ'' *ᵥ a ≤ ‖Γ''‖ := by
    have := abs_dotProduct_mulVec_le Γ'' a a
    rw [haa, Real.sqrt_one] at this
    simpa using (le_abs_self _).trans this
  have hfinal := lt_of_lt_of_le hlt (hbound.trans (le_advPMOn hdet hadv hfeas))
  linarith

/-- The two-weight form, by symmetrisation (the finite-output mirror of
`lt_advPMOn_of_certificate_two`). -/
theorem lt_two_mul_advPMOn_of_certificate_two {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y)
    {Ξ : Matrix X X ℝ} {p q : X → ℝ} {c : ℝ}
    (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (hquad : ∀ (i : ι) (s t : X → ℝ),
      |s ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ t|
        ≤ (∑ x, p x * (s x * s x)) + ∑ y, q y * (t y * t y))
    (hobj : c * ((∑ x, p x) + ∑ x, q x)
      < ∑ x, ∑ y, Ξ x y * dualTargetOn f x y) :
    c < 2 * advPMOn read f := by
  classical
  set Ξ' : Matrix X X ℝ := Matrix.of fun x y => (Ξ x y + Ξ y x) / 2 with hΞ'
  set p' : X → ℝ := fun x => (p x + q x) / 2 with hp'
  have hD : ∀ (i : ι) (x y : X),
      (advDOn read i) y x = advDOn read i x y := by
    intro i x y
    simp [advDOn, eq_comm]
  have hswap : ∀ (i : ι) (s t : X → ℝ),
      s ⬝ᵥ (Ξ' ⊙ advDOn read i) *ᵥ t
        = (s ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ t) / 2
          + (t ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ s) / 2 := by
    intro i s t
    simp only [dotProduct_mulVec_eq_sum]
    have hcomm : (∑ x, ∑ y, t x * (Ξ ⊙ advDOn read i) x y * s y)
        = ∑ x, ∑ y, s x * ((Ξ ⊙ advDOn read i) y x) * t y := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ =>
        Finset.sum_congr rfl fun y _ => by ring
    rw [hcomm, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Matrix.hadamard_apply, hΞ', Matrix.of_apply, hD i x y]
    ring
  have hps : ∀ w : X → ℝ, (∑ x, p' x * (w x * w x))
      = (∑ x, p x * (w x * w x)) / 2 + (∑ x, q x * (w x * w x)) / 2 := by
    intro w
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hp']
    ring
  refine lt_two_mul_advPMOn_of_certificate hdet (Γ := Ξ') (p := p') ?_ ?_ ?_ ?_
  · intro x y
    show (Ξ y x + Ξ x y) / 2 = (Ξ x y + Ξ y x) / 2
    ring
  · intro x
    have h1 := hp x
    have h2 := hq x
    simp only [hp']
    linarith
  · intro i s t
    rw [hswap i s t, hps s, hps t]
    have h1 := hquad i s t
    have h2 := hquad i t s
    have habs : |(s ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ t) / 2
          + (t ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ s) / 2|
        ≤ |s ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ t| / 2
          + |t ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ s| / 2 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_div, abs_div]
      norm_num
    linarith
  · have hS : (∑ x, ∑ y, Ξ y x * dualTargetOn f x y)
        = ∑ x, ∑ y, Ξ x y * dualTargetOn f x y := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
        rw [dualTargetOn_comm]
    have hpair : (∑ x, ∑ y, Ξ' x y * dualTargetOn f x y)
        = ∑ x, ∑ y, Ξ x y * dualTargetOn f x y := by
      have hsplit : (∑ x, ∑ y, Ξ' x y * dualTargetOn f x y)
          = (∑ x, ∑ y, Ξ x y * dualTargetOn f x y) / 2
            + (∑ x, ∑ y, Ξ y x * dualTargetOn f x y) / 2 := by
        rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun y _ => ?_
        simp only [hΞ', Matrix.of_apply]
        ring
      rw [hsplit, hS]
      ring
    rw [hpair]
    have hsum' : (∑ x, p' x) = ((∑ x, p x) + ∑ x, q x) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
    have hsump : 2 * c * (∑ x, p' x) = c * ((∑ x, p x) + ∑ x, q x) := by
      rw [hsum']
      ring
    rw [hsump]
    exact hobj

/-! ## The separation argument, finite outputs -/

/-- **The finite-output bridge, existence form.**  For a read-determined
promise problem with any decidable output type, every value above
`2·advPMOn read f` is achieved by a feasible promise dual solution.  The
proof is the separation argument of `exists_dualPairOn_of_advPMOn_lt` with
the factor-two certificate lemma in place of the Boolean one. -/
theorem exists_dualPairOn_of_two_mul_advPMOn_lt {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y) {c : ℝ}
    (hc : 2 * advPMOn read f < c) :
    ∃ (m : ℕ) (P : DualPairOn read (Fin m) f), P.IsCostLe c := by
  classical
  have hc0 : 0 < c := by
    have := advPMOn_nonneg hdet
    linarith
  by_contra hno
  push Not at hno
  -- with an empty promise domain the zero dual is vacuously feasible
  rcases isEmpty_or_nonempty X with hXe | hXn
  · exact hno 0 ⟨fun x _ _ => (hXe.false x).elim, fun x _ _ => (hXe.false x).elim,
      fun x _ => (hXe.false x).elim⟩
      ⟨fun x => (hXe.false x).elim, fun x => (hXe.false x).elim⟩
  -- with no query positions determinacy makes every pair equal-valued
  rcases isEmpty_or_nonempty ι with hιe | hιn
  · have hval : ∀ x y : X, f x = f y := fun x y =>
      hdet x y (funext fun i => (hιe.false i).elim)
    refine hno 0 ⟨fun _ _ _ => 0, fun _ _ _ => 0, fun x y => ?_⟩
      ⟨fun x => ?_, fun x => ?_⟩
    · simp [hval x y]
    · simpa using hc0.le
    · simpa using hc0.le
  obtain ⟨i₀⟩ := hιn
  have hcard : 0 < (Fintype.card X : ℝ) := by
    have h : 0 < Fintype.card X := Fintype.card_pos
    exact_mod_cast h
  set T : ℝ := 2 * c * (Fintype.card X : ℝ) with hTdef
  have hT0 : 0 < T := by positivity
  -- the two sets are disjoint
  have hdisj : Disjoint (gramImageOn read T) (dualBoxOnGen f c) := by
    rw [Set.disjoint_left]
    rintro z ⟨G, ⟨hGpsd, _⟩, rfl⟩ ⟨hz1, hz2⟩
    have hR : gramROn read G = dualTargetOn f := by
      ext x y
      exact hz1 x y
    obtain ⟨m, Q, hQ⟩ := exists_dualPairOn_of_gram hGpsd hR
      fun b x => (hz2 (x, b)).2
    exact hno m Q hQ
  obtain ⟨φ, u, v, hgram, huv, hbox⟩ :=
    geometric_hahn_banach_compact_closed (convex_gramImageOn read T)
      (isCompact_gramImageOn read T)
      (convex_dualBoxOnGen f c) (isClosed_dualBoxOnGen f c) hdisj
  have hu0 : 0 < u := by
    have h := hgram 0 (zero_mem_gramImageOn hT0.le)
    simpa using h
  set κ : ℝ := u / T with hκdef
  have hκ0 : 0 < κ := div_pos hu0 hT0
  have hkappa : T * κ = u := by
    rw [hκdef]
    field_simp
  -- the coefficients of the separating functional
  obtain ⟨Ξ, hΞ⟩ : ∃ Ξ : Matrix X X ℝ,
      ∀ x y, Ξ x y = φ (Pi.single (Sum.inl (x, y)) 1) :=
    ⟨Matrix.of fun x y => φ (Pi.single (Sum.inl (x, y)) 1), fun _ _ => rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : Bool → X → ℝ,
      ∀ b x, γ b x = φ (Pi.single (Sum.inr (x, b)) 1) :=
    ⟨fun b x => φ (Pi.single (Sum.inr (x, b)) 1), fun _ _ => rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Bool → X → ℝ, ∀ b x, P b x = κ - γ b x :=
    ⟨fun b x => κ - γ b x, fun _ _ => rfl⟩
  -- reading `φ` off a Gram matrix
  have hexpand : ∀ G : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ,
      φ (gramLOn read G) = (∑ x, ∑ y, gramROn read G x y * Ξ x y)
        + ∑ x, ∑ b, gramCostOn G b x * γ b x := by
    intro G
    rw [apply_eq_sum_single]
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, gramLOn_inl,
      gramLOn_inr, hΞ, hγ]
  -- linearity facts
  have hgramL_smul : ∀ (r : ℝ) (M : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ),
      gramLOn read (r • M) = r • gramLOn read M := by
    intro r M
    funext z
    rcases z with ⟨x, y⟩ | ⟨x, b⟩
    · simpa using congrFun₂ (gramROn_smul read r M) x y
    · simpa using gramCostOn_smul r M b x
  have hgramL_zero :
      gramLOn read (0 : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) = 0 := by
    funext z
    rcases z with ⟨x, y⟩ | ⟨x, b⟩
    · simp [gramROn]
    · simp [gramCostOn]
  -- homogeneity: the truncated cone controls every rank-one direction
  have hscale : ∀ (w : GramIdxOn X ι → ℝ) (a : ℝ),
      vecMulVec (fun z => a * w z) (fun z => a * w z)
        = (a * a) • vecMulVec w w := by
    intro w a
    ext z z'
    simp only [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hQbound : ∀ w : GramIdxOn X ι → ℝ, w ≠ 0 →
      φ (gramLOn read (vecMulVec w w)) < κ * ∑ z, w z * w z := by
    intro w hw
    have hnn : (0 : ℝ) ≤ ∑ z, w z * w z :=
      Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    have hS : 0 < ∑ z, w z * w z := by
      rcases hnn.lt_or_eq with h | h
      · exact h
      · exact absurd (dotProduct_self_eq_zero.mp
          (by simpa [dotProduct] using h.symm)) hw
    set a : ℝ := Real.sqrt (T / ∑ z, w z * w z) with hadef
    have ha2 : a * a = T / ∑ z, w z * w z :=
      Real.mul_self_sqrt (by positivity)
    have hmemnorm : (∑ z, (a * w z) * (a * w z)) = T := by
      have hfac : (∑ z, (a * w z) * (a * w z)) = (a * a) * ∑ z, w z * w z := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
      rw [hfac, ha2, div_mul_cancel₀ _ hS.ne']
    have hmem := mem_gramImageOn_vecMulVec (read := read) (fun z => a * w z)
      (le_of_eq hmemnorm)
    have hlt := hgram _ hmem
    rw [hscale w a, hgramL_smul, map_smul, smul_eq_mul, ha2] at hlt
    have hkey : T * φ (gramLOn read (vecMulVec w w)) < u * ∑ z, w z * w z := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hS] at hlt
      linarith
    rw [hκdef, div_mul_eq_mul_div, lt_div_iff₀ hT0]
    linarith
  have hQle : ∀ w : GramIdxOn X ι → ℝ,
      φ (gramLOn read (vecMulVec w w)) ≤ κ * ∑ z, w z * w z := by
    intro w
    rcases eq_or_ne w 0 with rfl | hw
    · have h0 : vecMulVec (0 : GramIdxOn X ι → ℝ) (0 : GramIdxOn X ι → ℝ)
          = (0 : Matrix (GramIdxOn X ι) (GramIdxOn X ι) ℝ) := by
        ext z z'
        simp [vecMulVec_apply]
      rw [h0, hgramL_zero, map_zero]
      simp
    · exact (hQbound w hw).le
  -- the value of `φ` on a rank-one matrix concentrated at one position
  have hconc : ∀ (i : ι) (s t : X → ℝ),
      φ (gramLOn read (vecMulVec (concVecOn i s t) (concVecOn i s t)))
        = s ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ t + ((∑ x, γ false x * (s x * s x))
          + ∑ x, γ true x * (t x * t x)) := by
    intro i s t
    rw [hexpand]
    have e1 : (∑ x, ∑ y,
          gramROn read (vecMulVec (concVecOn i s t) (concVecOn i s t)) x y
            * Ξ x y)
        = s ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ t := by
      rw [dotProduct_mulVec_eq_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      rw [gramROn_concVecOn, hadamard_advDOn_apply]
      by_cases h : read x i = read y i <;> simp [h] <;> ring
    have e2 : (∑ x, ∑ b,
          gramCostOn (vecMulVec (concVecOn i s t) (concVecOn i s t)) b x
            * γ b x)
        = (∑ x, γ false x * (s x * s x)) + ∑ x, γ true x * (t x * t x) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Fintype.sum_bool, gramCostOn_concVecOn_false, gramCostOn_concVecOn_true]
      ring
    rw [e1, e2]
  have hPsum : ∀ (b : Bool) (w : X → ℝ),
      (∑ x, P b x * (w x * w x))
        = κ * (∑ x, w x * w x) - ∑ x, γ b x * (w x * w x) := by
    intro b w
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [hP]; ring
  -- the quadratic hypothesis of the certificate
  have hquadle : ∀ (i : ι) (s t : X → ℝ),
      s ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ t
        ≤ (∑ x, P false x * (s x * s x)) + ∑ x, P true x * (t x * t x) := by
    intro i s t
    have h := hQle (concVecOn i s t)
    rw [hconc i s t, sum_sq_concVecOn] at h
    rw [hPsum false s, hPsum true t]
    have hexp : κ * ((∑ x, s x * s x) + ∑ x, t x * t x)
        = κ * (∑ x, s x * s x) + κ * (∑ x, t x * t x) := by ring
    rw [hexp] at h
    linarith
  have hquadabs : ∀ (i : ι) (s t : X → ℝ),
      |s ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ t|
        ≤ (∑ x, P false x * (s x * s x)) + ∑ x, P true x * (t x * t x) := by
    intro i s t
    have h1 := hquadle i s t
    have h2 := hquadle i (fun x => -s x) t
    have hneg : (fun x => -s x) ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ t
        = -(s ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ t) := by
      simp only [dotProduct_mulVec_eq_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      exact Finset.sum_congr rfl fun y _ => by ring
    have hsq : (∑ x, P false x * ((-s x) * (-s x)))
        = ∑ x, P false x * (s x * s x) :=
      Finset.sum_congr rfl fun x _ => by ring
    rw [hneg, hsq] at h2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- the weights are strictly positive
  have hsingle : ∀ x : X,
      (∑ y, (Pi.single x (1 : ℝ) : X → ℝ) y
        * (Pi.single x (1 : ℝ) : X → ℝ) y) = 1 := by
    intro x
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [hy]
    · intro h
      exact absurd (Finset.mem_univ x) h
  have hsingleγ : ∀ (b : Bool) (x : X),
      (∑ y, γ b y * ((Pi.single x (1 : ℝ) : X → ℝ) y
        * (Pi.single x (1 : ℝ) : X → ℝ) y)) = γ b x := by
    intro b x
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [hy]
    · intro h
      exact absurd (Finset.mem_univ x) h
  have hsingle_ne : ∀ x : X, (Pi.single x (1 : ℝ) : X → ℝ) ≠ 0 := by
    intro x h
    have := congrFun h x
    simp at this
  have hPpos : ∀ (b : Bool) (x : X), 0 < P b x := by
    intro b x
    cases b with
    | false =>
        have h := hQbound (concVecOn i₀ (Pi.single x 1) 0)
          (concVecOn_ne_zero_left (hsingle_ne x))
        rw [hconc, sum_sq_concVecOn, hsingle x, hsingleγ false x] at h
        have hz : (Pi.single x (1 : ℝ) : X → ℝ) ⬝ᵥ (Ξ ⊙ advDOn read i₀)
            *ᵥ (0 : X → ℝ) = 0 := by simp
        simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero,
          hz, zero_add] at h
        rw [hP]
        linarith
    | true =>
        have h := hQbound (concVecOn i₀ 0 (Pi.single x 1))
          (concVecOn_ne_zero_right (hsingle_ne x))
        rw [hconc, sum_sq_concVecOn, hsingle x, hsingleγ true x] at h
        have hz : (0 : X → ℝ) ⬝ᵥ (Ξ ⊙ advDOn read i₀)
            *ᵥ (Pi.single x (1 : ℝ) : X → ℝ) = 0 := by simp
        simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add,
          hz] at h
        rw [hP]
        linarith
  -- the objective hypothesis of the certificate
  have hcorner := hbox _ (dualCornerOnGen_mem (f := f) hc0.le)
  have hcornerval : φ (dualCornerOnGen f c)
      = (∑ x, ∑ y, dualTargetOn f x y * Ξ x y) + ∑ x, ∑ b, c * γ b x := by
    rw [apply_eq_sum_single]
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, dualCornerOnGen,
      Sum.elim_inl, Sum.elim_inr, hΞ, hγ]
  have hsumP : ∀ b : Bool, (∑ x, P b x)
      = κ * (Fintype.card X : ℝ) - ∑ x, γ b x := by
    intro b
    have : (∑ x, P b x) = ∑ x, (κ - γ b x) :=
      Finset.sum_congr rfl fun x _ => hP b x
    rw [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  have hcomm : (∑ x, ∑ y, dualTargetOn f x y * Ξ x y)
      = ∑ x, ∑ y, Ξ x y * dualTargetOn f x y :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => mul_comm _ _
  have hgamma : (∑ x, ∑ b, c * γ b x)
      = c * ((∑ x, γ false x) + ∑ x, γ true x) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [Fintype.sum_bool]; ring
  rw [hcornerval, hcomm, hgamma] at hcorner
  have hobj : c * ((∑ x, P false x) + ∑ x, P true x)
      < ∑ x, ∑ y, Ξ x y * dualTargetOn f x y := by
    rw [hsumP false, hsumP true]
    have hLHS : c * ((κ * (Fintype.card X : ℝ) - ∑ x, γ false x)
          + (κ * (Fintype.card X : ℝ) - ∑ x, γ true x))
        = u - c * ((∑ x, γ false x) + ∑ x, γ true x) := by
      rw [← hkappa, hTdef]
      ring
    rw [hLHS]
    linarith
  exact absurd
    (lt_two_mul_advPMOn_of_certificate_two hdet (hPpos false) (hPpos true) hquadabs hobj)
    (not_lt.mpr hc.le)

/-! ## Bundled corollaries -/

section Bundled

variable {ι' : Type} [Fintype ι'] [DecidableEq ι']
variable {σ' : Type} [Fintype σ'] [DecidableEq σ']
variable {X' : Type} [Fintype X'] [DecidableEq X']
variable {O' : Type} [DecidableEq O']
variable {read : X' → ι' → σ'} {f : X' → O'}

/-- **The finite-output bridge, bundled.** -/
theorem hasDualOn_of_two_mul_advPMOn_lt (hdet : ∀ x y, read x = read y → f x = f y)
    {c : ℝ} (hc : 2 * advPMOn read f < c) : HasDualOn read f c := by
  obtain ⟨m, P, hP⟩ := exists_dualPairOn_of_two_mul_advPMOn_lt hdet hc
  exact ⟨Fin m, inferInstance, P, hP⟩

/-- A read-determined promise problem with adversary bound `0` is constant
(contrapositive of `half_le_advPMOn`). -/
theorem eq_of_advPMOn_le_zero (hdet : ∀ x y, read x = read y → f x = f y)
    (h : advPMOn read f ≤ 0) (x y : X') : f x = f y := by
  by_contra hne
  have := half_le_advPMOn hdet hne
  linarith

/-- **Every read-determined promise problem has a certificate of cost
`3·advPMOn`**: the bridge at `c = 3·advPMOn` when the adversary bound is
positive, the zero certificate when it is zero. -/
theorem hasDualOn_three_mul_advPMOn (hdet : ∀ x y, read x = read y → f x = f y) :
    HasDualOn read f (3 * advPMOn read f) := by
  rcases (advPMOn_nonneg hdet).lt_or_eq with hpos | hzero
  · exact hasDualOn_of_two_mul_advPMOn_lt hdet (by linarith)
  · rw [← hzero, mul_zero]
    exact hasDualOn_of_const read (eq_of_advPMOn_le_zero hdet hzero.symm.le)

/-- A uniform adversary budget `T ≥ 0` gives a certificate of cost `3·T`. -/
theorem hasDualOn_of_advPMOn_le (hdet : ∀ x y, read x = read y → f x = f y) {T : ℝ}
    (hT : advPMOn read f ≤ T) : HasDualOn read f (3 * T) :=
  (hasDualOn_three_mul_advPMOn hdet).mono (by linarith)

end Bundled

end QuantumQueryComplexity
