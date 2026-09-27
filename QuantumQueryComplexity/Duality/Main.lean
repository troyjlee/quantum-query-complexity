import QuantumQueryComplexity.Duality.Compact
import QuantumQueryComplexity.Duality.Witness
import QuantumQueryComplexity.DualCompose
import Mathlib.Analysis.LocallyConvex.Separation

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1000000

/-!
# Strong duality for the adversary bound

`advDual g = advPM g`: the LMRSS dual program has no gap against the adversary
bound.  Weak duality (`advPM_le_advDual`) is proved in `QuantumQueryComplexity/Dual.lean`;
what is proved here is the converse, `advDual ≤ advPM`, which is genuine
semidefinite-programming duality.

The argument is one Hahn–Banach separation.  Fix `c > advPM g` and suppose no
dual solution of cost at most `c` exists.  Then, inside the coordinate space
`DualOmega ι σ → ℝ`, the compact convex set `gramImage ι σ T` of achievable
constraint-and-cost data (with `T = 2 c · card (ι → σ)`, a bound every dual
solution of cost `c` respects) misses the closed convex target `dualBox g c`,
so `geometric_hahn_banach_compact_closed` produces a functional `φ` strictly
separating them.  Reading off the coefficients of `φ` gives

* a matrix `Ξ`, from the constraint coordinates, and
* two weights `P false`, `P true`, from the cost coordinates,

and testing `φ` against rank-one Gram matrices `w wᵀ` concentrated on a single
query position turns the separation into the positive semidefiniteness
hypothesis of `lt_advPM_of_certificate`, while testing it against the corner of
the box turns it into that lemma's objective hypothesis.  The conclusion
`c < advPM g` contradicts the choice of `c`.

The one piece of quantitative bookkeeping is the shift `κ = u / T`, which is
what truncating the cone at trace `T` costs; choosing `T = 2 c · card` makes
that cost exactly `u`, which the separation gap `u < v` absorbs.  It also makes
the weights *strictly* positive, so no pseudo-inverses appear.

Consequences: perfect composition `ADV±(f ∘ gᵏ) = ADV±(f) · ADV±(g)` and its
iterate become unconditional, and every function satisfies `HasAdvValue`.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-! ## Rank-one test matrices concentrated on one query position -/

/-- The vector of Gram indices carrying `s` on the `u`-side and `t` on the
`v`-side of the query position `i₀`, and zero elsewhere. -/
def concVec (i₀ : ι) (s t : (ι → σ) → ℝ) : GramIdx ι σ → ℝ :=
  fun z => if z.2.1 = i₀ then (if z.2.2 then t z.1 else s z.1) else 0

lemma gramR_concVec (i₀ : ι) (s t : (ι → σ) → ℝ) (x y : ι → σ) :
    gramR (vecMulVec (concVec i₀ s t) (concVec i₀ s t)) x y
      = if x i₀ = y i₀ then 0 else s x * t y := by
  rw [gramR_vecMulVec, Finset.sum_eq_single i₀]
  · by_cases h : x i₀ = y i₀ <;> simp [h, concVec]
  · intro i _ hi
    by_cases h : x i = y i <;> simp [h, concVec, hi]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

lemma gramCost_concVec_false (i₀ : ι) (s t : (ι → σ) → ℝ) (x : ι → σ) :
    gramCost (vecMulVec (concVec i₀ s t) (concVec i₀ s t)) false x = s x * s x := by
  rw [gramCost_vecMulVec, Finset.sum_eq_single i₀]
  · simp [concVec]
  · intro i _ hi
    simp [concVec, hi]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

lemma gramCost_concVec_true (i₀ : ι) (s t : (ι → σ) → ℝ) (x : ι → σ) :
    gramCost (vecMulVec (concVec i₀ s t) (concVec i₀ s t)) true x = t x * t x := by
  rw [gramCost_vecMulVec, Finset.sum_eq_single i₀]
  · simp [concVec]
  · intro i _ hi
    simp [concVec, hi]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

lemma sum_sq_concVec (i₀ : ι) (s t : (ι → σ) → ℝ) :
    (∑ z, concVec i₀ s t z * concVec i₀ s t z)
      = (∑ x, s x * s x) + ∑ x, t x * t x := by
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i₀]
  · simp [concVec]
    ring
  · intro i _ hi
    simp [concVec, hi]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

lemma concVec_ne_zero_left {i₀ : ι} {s t : (ι → σ) → ℝ} (hs : s ≠ 0) :
    concVec i₀ s t ≠ 0 := by
  intro h
  refine hs (funext fun x => ?_)
  have := congrFun h (x, i₀, false)
  simpa [concVec] using this

lemma concVec_ne_zero_right {i₀ : ι} {s t : (ι → σ) → ℝ} (ht : t ≠ 0) :
    concVec i₀ s t ≠ 0 := by
  intro h
  refine ht (funext fun x => ?_)
  have := congrFun h (x, i₀, true)
  simpa [concVec] using this

/-! ## Symmetrising a two-weight certificate -/

/-- The certificate of `lt_advPM_of_certificate` with the two sides carrying
different weights: averaging `Ξ` with its transpose and the two weights with
each other reduces to the symmetric case, because `advD i` and `dualTarget g`
are symmetric. -/
theorem lt_advPM_of_certificate_two {g : (ι → σ) → Bool}
    {Ξ : Matrix (ι → σ) (ι → σ) ℝ} {p q : (ι → σ) → ℝ} {c : ℝ}
    (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (hquad : ∀ (i : ι) (s t : (ι → σ) → ℝ),
      |s ⬝ᵥ (Ξ ⊙ advD i) *ᵥ t|
        ≤ (∑ x, p x * (s x * s x)) + ∑ y, q y * (t y * t y))
    (hobj : c * ((∑ x, p x) + ∑ x, q x)
      < ∑ x, ∑ y, Ξ x y * dualTarget g x y) :
    c < advPM g := by
  classical
  set Ξ' : Matrix (ι → σ) (ι → σ) ℝ :=
    Matrix.of fun x y => (Ξ x y + Ξ y x) / 2 with hΞ'
  set p' : (ι → σ) → ℝ := fun x => (p x + q x) / 2 with hp'
  have hD : ∀ (i : ι) (x y : ι → σ), (advD (σ := σ) i) y x = advD i x y := by
    intro i x y
    simp [advD, eq_comm]
  have hswap : ∀ (i : ι) (s t : (ι → σ) → ℝ),
      s ⬝ᵥ (Ξ' ⊙ advD i) *ᵥ t
        = (s ⬝ᵥ (Ξ ⊙ advD i) *ᵥ t) / 2 + (t ⬝ᵥ (Ξ ⊙ advD i) *ᵥ s) / 2 := by
    intro i s t
    simp only [dotProduct_mulVec_eq_sum]
    have hcomm : (∑ x, ∑ y, t x * (Ξ ⊙ advD i) x y * s y)
        = ∑ x, ∑ y, s x * ((Ξ ⊙ advD i) y x) * t y := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ =>
        Finset.sum_congr rfl fun y _ => by ring
    rw [hcomm, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Matrix.hadamard_apply, hΞ', Matrix.of_apply, hD i x y]
    ring
  have hps : ∀ w : (ι → σ) → ℝ, (∑ x, p' x * (w x * w x))
      = (∑ x, p x * (w x * w x)) / 2 + (∑ x, q x * (w x * w x)) / 2 := by
    intro w
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hp']
    ring
  refine lt_advPM_of_certificate (Γ := Ξ') (p := p') (g := g) ?_ ?_ ?_ ?_
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
    have habs : |(s ⬝ᵥ (Ξ ⊙ advD i) *ᵥ t) / 2 + (t ⬝ᵥ (Ξ ⊙ advD i) *ᵥ s) / 2|
        ≤ |s ⬝ᵥ (Ξ ⊙ advD i) *ᵥ t| / 2 + |t ⬝ᵥ (Ξ ⊙ advD i) *ᵥ s| / 2 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_div, abs_div]
      norm_num
    linarith
  · have hS : (∑ x, ∑ y, Ξ y x * dualTarget g x y)
        = ∑ x, ∑ y, Ξ x y * dualTarget g x y := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
        rw [dualTarget_comm]
    have hpair : (∑ x, ∑ y, Ξ' x y * dualTarget g x y)
        = ∑ x, ∑ y, Ξ x y * dualTarget g x y := by
      have hsplit : (∑ x, ∑ y, Ξ' x y * dualTarget g x y)
          = (∑ x, ∑ y, Ξ x y * dualTarget g x y) / 2
            + (∑ x, ∑ y, Ξ y x * dualTarget g x y) / 2 := by
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

/-! ## The separation argument -/

/-- **Strong duality, existence form.**  Above the adversary bound every value
is achieved by a feasible dual solution. -/
theorem exists_dualPair_of_advPM_lt [Nonempty σ] {g : (ι → σ) → Bool} {c : ℝ}
    (hc : advPM g < c) : ∃ (m : ℕ) (P : DualPair (Fin m) g), P.IsCostLe c := by
  classical
  have hc0 : 0 < c := lt_of_le_of_lt (advPM_nonneg g) hc
  by_contra hno
  push_neg at hno
  -- With no query positions every input has the same value and the zero dual
  -- solution is feasible.
  rcases isEmpty_or_nonempty ι with hιe | hιn
  · have hxy : ∀ x y : ι → σ, x = y := fun x y => funext fun i => (hιe.false i).elim
    refine hno 0 ⟨fun _ _ _ => 0, fun _ _ _ => 0, fun x y => ?_⟩ ⟨fun x => ?_, fun x => ?_⟩
    · simp [hxy x y]
    · simpa using hc0.le
    · simpa using hc0.le
  obtain ⟨i₀⟩ := hιn
  have hcard : 0 < (Fintype.card (ι → σ) : ℝ) := by
    have h : 0 < Fintype.card (ι → σ) := Fintype.card_pos
    exact_mod_cast h
  set T : ℝ := 2 * c * (Fintype.card (ι → σ) : ℝ) with hTdef
  have hT0 : 0 < T := by positivity
  -- the two sets are disjoint
  have hdisj : Disjoint (gramImage ι σ T) (dualBox g c) := by
    rw [Set.disjoint_left]
    rintro z ⟨G, ⟨hGpsd, _⟩, rfl⟩ ⟨hz1, hz2⟩
    have hR : gramR G = dualTarget g := by
      ext x y
      exact hz1 x y
    obtain ⟨m, Q, hQ⟩ := exists_dualPair_of_gram hGpsd hR fun b x => (hz2 (x, b)).2
    exact hno m Q hQ
  obtain ⟨φ, u, v, hgram, huv, hbox⟩ :=
    geometric_hahn_banach_compact_closed (convex_gramImage T) (isCompact_gramImage T)
      (convex_dualBox g c) (isClosed_dualBox g c) hdisj
  have hu0 : 0 < u := by
    have h := hgram 0 (zero_mem_gramImage hT0.le)
    simpa using h
  set κ : ℝ := u / T with hκdef
  have hκ0 : 0 < κ := div_pos hu0 hT0
  have hkappa : T * κ = u := by
    rw [hκdef]
    field_simp
  -- the coefficients of the separating functional
  obtain ⟨Ξ, hΞ⟩ : ∃ Ξ : Matrix (ι → σ) (ι → σ) ℝ,
      ∀ x y, Ξ x y = φ (Pi.single (Sum.inl (x, y)) 1) :=
    ⟨Matrix.of fun x y => φ (Pi.single (Sum.inl (x, y)) 1), fun _ _ => rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : Bool → (ι → σ) → ℝ,
      ∀ b x, γ b x = φ (Pi.single (Sum.inr (x, b)) 1) :=
    ⟨fun b x => φ (Pi.single (Sum.inr (x, b)) 1), fun _ _ => rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Bool → (ι → σ) → ℝ, ∀ b x, P b x = κ - γ b x :=
    ⟨fun b x => κ - γ b x, fun _ _ => rfl⟩
  -- reading `φ` off a Gram matrix
  have hexpand : ∀ G : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ,
      φ (gramL G) = (∑ x, ∑ y, gramR G x y * Ξ x y)
        + ∑ x, ∑ b, gramCost G b x * γ b x := by
    intro G
    rw [apply_eq_sum_single]
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, gramL_inl, gramL_inr,
      hΞ, hγ]
  -- linearity facts for `gramL`
  have hgramL_smul : ∀ (r : ℝ) (M : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ),
      gramL (r • M) = r • gramL M := by
    intro r M
    funext z
    rcases z with ⟨x, y⟩ | ⟨x, b⟩
    · simpa using congrFun₂ (gramR_smul r M) x y
    · simpa using gramCost_smul r M b x
  have hgramL_zero : gramL (0 : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ) = 0 := by
    funext z
    rcases z with ⟨x, y⟩ | ⟨x, b⟩
    · simp [gramR]
    · simp [gramCost]
  -- homogeneity: the truncated cone controls every rank-one direction
  have hscale : ∀ (w : GramIdx ι σ → ℝ) (a : ℝ),
      vecMulVec (fun z => a * w z) (fun z => a * w z)
        = (a * a) • vecMulVec w w := by
    intro w a
    ext z z'
    simp only [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hQbound : ∀ w : GramIdx ι σ → ℝ, w ≠ 0 →
      φ (gramL (vecMulVec w w)) < κ * ∑ z, w z * w z := by
    intro w hw
    have hnn : (0 : ℝ) ≤ ∑ z, w z * w z :=
      Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    have hS : 0 < ∑ z, w z * w z := by
      rcases hnn.lt_or_eq with h | h
      · exact h
      · exact absurd (dotProduct_self_eq_zero.mp (by simpa [dotProduct] using h.symm)) hw
    set a : ℝ := Real.sqrt (T / ∑ z, w z * w z) with hadef
    have ha2 : a * a = T / ∑ z, w z * w z :=
      Real.mul_self_sqrt (by positivity)
    have hmemnorm : (∑ z, (a * w z) * (a * w z)) = T := by
      have hfac : (∑ z, (a * w z) * (a * w z)) = (a * a) * ∑ z, w z * w z := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
      rw [hfac, ha2, div_mul_cancel₀ _ hS.ne']
    have hmem := mem_gramImage_vecMulVec (ι := ι) (σ := σ) (fun z => a * w z)
      (le_of_eq hmemnorm)
    have hlt := hgram _ hmem
    rw [hscale w a, hgramL_smul, map_smul, smul_eq_mul, ha2] at hlt
    have hkey : T * φ (gramL (vecMulVec w w)) < u * ∑ z, w z * w z := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hS] at hlt
      linarith
    rw [hκdef, div_mul_eq_mul_div, lt_div_iff₀ hT0]
    linarith
  have hQle : ∀ w : GramIdx ι σ → ℝ,
      φ (gramL (vecMulVec w w)) ≤ κ * ∑ z, w z * w z := by
    intro w
    rcases eq_or_ne w 0 with rfl | hw
    · have h0 : vecMulVec (0 : GramIdx ι σ → ℝ) (0 : GramIdx ι σ → ℝ)
          = (0 : Matrix (GramIdx ι σ) (GramIdx ι σ) ℝ) := by
        ext z z'
        simp [vecMulVec_apply]
      rw [h0, hgramL_zero, map_zero]
      simp
    · exact (hQbound w hw).le
  -- the value of `φ` on a rank-one matrix concentrated at one position
  have hconc : ∀ (i : ι) (s t : (ι → σ) → ℝ),
      φ (gramL (vecMulVec (concVec i s t) (concVec i s t)))
        = s ⬝ᵥ (Ξ ⊙ advD i) *ᵥ t + ((∑ x, γ false x * (s x * s x))
          + ∑ x, γ true x * (t x * t x)) := by
    intro i s t
    rw [hexpand]
    have e1 : (∑ x, ∑ y,
          gramR (vecMulVec (concVec i s t) (concVec i s t)) x y * Ξ x y)
        = s ⬝ᵥ (Ξ ⊙ advD i) *ᵥ t := by
      rw [dotProduct_mulVec_eq_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      rw [gramR_concVec, hadamard_advD_apply]
      by_cases h : x i = y i <;> simp [h] <;> ring
    have e2 : (∑ x, ∑ b,
          gramCost (vecMulVec (concVec i s t) (concVec i s t)) b x * γ b x)
        = (∑ x, γ false x * (s x * s x)) + ∑ x, γ true x * (t x * t x) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Fintype.sum_bool, gramCost_concVec_false, gramCost_concVec_true]
      ring
    rw [e1, e2]
  have hPsum : ∀ (b : Bool) (w : (ι → σ) → ℝ),
      (∑ x, P b x * (w x * w x))
        = κ * (∑ x, w x * w x) - ∑ x, γ b x * (w x * w x) := by
    intro b w
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [hP]; ring
  -- the quadratic hypothesis of the certificate
  have hquadle : ∀ (i : ι) (s t : (ι → σ) → ℝ),
      s ⬝ᵥ (Ξ ⊙ advD i) *ᵥ t
        ≤ (∑ x, P false x * (s x * s x)) + ∑ x, P true x * (t x * t x) := by
    intro i s t
    have h := hQle (concVec i s t)
    rw [hconc i s t, sum_sq_concVec] at h
    rw [hPsum false s, hPsum true t]
    have hexp : κ * ((∑ x, s x * s x) + ∑ x, t x * t x)
        = κ * (∑ x, s x * s x) + κ * (∑ x, t x * t x) := by ring
    rw [hexp] at h
    linarith
  have hquadabs : ∀ (i : ι) (s t : (ι → σ) → ℝ),
      |s ⬝ᵥ (Ξ ⊙ advD i) *ᵥ t|
        ≤ (∑ x, P false x * (s x * s x)) + ∑ x, P true x * (t x * t x) := by
    intro i s t
    have h1 := hquadle i s t
    have h2 := hquadle i (fun x => -s x) t
    have hneg : (fun x => -s x) ⬝ᵥ (Ξ ⊙ advD i) *ᵥ t
        = -(s ⬝ᵥ (Ξ ⊙ advD i) *ᵥ t) := by
      simp only [dotProduct_mulVec_eq_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      exact Finset.sum_congr rfl fun y _ => by ring
    have hsq : (∑ x, P false x * ((-s x) * (-s x)))
        = ∑ x, P false x * (s x * s x) :=
      Finset.sum_congr rfl fun x _ => by ring
    rw [hneg, hsq] at h2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- the weights are strictly positive
  have hsingle : ∀ x : ι → σ,
      (∑ y, (Pi.single x (1 : ℝ) : (ι → σ) → ℝ) y
        * (Pi.single x (1 : ℝ) : (ι → σ) → ℝ) y) = 1 := by
    intro x
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [Pi.single_apply, hy]
    · intro h
      exact absurd (Finset.mem_univ x) h
  have hsingleγ : ∀ (b : Bool) (x : ι → σ),
      (∑ y, γ b y * ((Pi.single x (1 : ℝ) : (ι → σ) → ℝ) y
        * (Pi.single x (1 : ℝ) : (ι → σ) → ℝ) y)) = γ b x := by
    intro b x
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [Pi.single_apply, hy]
    · intro h
      exact absurd (Finset.mem_univ x) h
  have hsingle_ne : ∀ x : ι → σ, (Pi.single x (1 : ℝ) : (ι → σ) → ℝ) ≠ 0 := by
    intro x h
    have := congrFun h x
    simp at this
  have hPpos : ∀ (b : Bool) (x : ι → σ), 0 < P b x := by
    intro b x
    cases b with
    | false =>
        have h := hQbound (concVec i₀ (Pi.single x 1) 0)
          (concVec_ne_zero_left (hsingle_ne x))
        rw [hconc, sum_sq_concVec, hsingle x, hsingleγ false x] at h
        have hz : (Pi.single x (1 : ℝ) : (ι → σ) → ℝ) ⬝ᵥ (Ξ ⊙ advD i₀)
            *ᵥ (0 : (ι → σ) → ℝ) = 0 := by simp
        simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero,
          hz, zero_add] at h
        rw [hP]
        linarith
    | true =>
        have h := hQbound (concVec i₀ 0 (Pi.single x 1))
          (concVec_ne_zero_right (hsingle_ne x))
        rw [hconc, sum_sq_concVec, hsingle x, hsingleγ true x] at h
        have hz : (0 : (ι → σ) → ℝ) ⬝ᵥ (Ξ ⊙ advD i₀)
            *ᵥ (Pi.single x (1 : ℝ) : (ι → σ) → ℝ) = 0 := by simp
        simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add,
          hz] at h
        rw [hP]
        linarith
  -- the objective hypothesis of the certificate
  have hcorner := hbox _ (dualCorner_mem (g := g) hc0.le)
  have hcornerval : φ (dualCorner g c)
      = (∑ x, ∑ y, dualTarget g x y * Ξ x y) + ∑ x, ∑ b, c * γ b x := by
    rw [apply_eq_sum_single]
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, dualCorner,
      Sum.elim_inl, Sum.elim_inr, hΞ, hγ]
  have hsumP : ∀ b : Bool, (∑ x, P b x)
      = κ * (Fintype.card (ι → σ) : ℝ) - ∑ x, γ b x := by
    intro b
    have : (∑ x, P b x) = ∑ x, (κ - γ b x) :=
      Finset.sum_congr rfl fun x _ => hP b x
    rw [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  have hcomm : (∑ x, ∑ y, dualTarget g x y * Ξ x y)
      = ∑ x, ∑ y, Ξ x y * dualTarget g x y :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => mul_comm _ _
  have hgamma : (∑ x, ∑ b, c * γ b x)
      = c * ((∑ x, γ false x) + ∑ x, γ true x) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [Fintype.sum_bool]; ring
  rw [hcornerval, hcomm, hgamma] at hcorner
  have hobj : c * ((∑ x, P false x) + ∑ x, P true x)
      < ∑ x, ∑ y, Ξ x y * dualTarget g x y := by
    rw [hsumP false, hsumP true]
    have hLHS : c * ((κ * (Fintype.card (ι → σ) : ℝ) - ∑ x, γ false x)
          + (κ * (Fintype.card (ι → σ) : ℝ) - ∑ x, γ true x))
        = u - c * ((∑ x, γ false x) + ∑ x, γ true x) := by
      rw [← hkappa, hTdef]
      ring
    rw [hLHS]
    linarith
  exact absurd (lt_advPM_of_certificate_two (hPpos false) (hPpos true) hquadabs hobj)
    (not_lt.mpr hc.le)

/-! ## Strong duality -/

/-- **Strong duality for the adversary bound.**  The LMRSS dual program has no
gap: its value equals `ADV±`. -/
theorem advDual_eq_advPM {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → Bool) → Bool) : advDual g = advPM g := by
  refine le_antisymm ?_ (advPM_le_advDual g)
  by_contra hlt
  push_neg at hlt
  have h1 : advPM g < (advPM g + advDual g) / 2 := by linarith
  have h2 : (advPM g + advDual g) / 2 < advDual g := by linarith
  obtain ⟨m, Q, hQ⟩ := exists_dualPair_of_advPM_lt h1
  have hle : advDual g ≤ (advPM g + advDual g) / 2 :=
    advDual_le_of_dualPair Q (by linarith [advPM_nonneg g]) hQ
  linarith

/-! ## Consequences -/

section Compose

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- **Perfect composition**, unconditionally: the adversary bound is exactly
multiplicative under composition. -/
theorem advPM_composeFun_eq (f : (α → Bool) → Bool) (g : (β → Bool) → Bool) :
    advPM (composeFun f g) = advPM f * advPM g :=
  advPM_composeFun_eq_of_dual_eq f g (advDual_eq_advPM f) (advDual_eq_advPM g)

/-- Every Boolean function carries a matching primal/dual pair of witnesses. -/
theorem hasAdvValue_advPM (f : (α → Bool) → Bool) : HasAdvValue f (advPM f) :=
  ⟨rfl, advDual_eq_advPM f⟩

/-- The iterated composition value is exact. -/
theorem advPM_iterFun_eq (f : (α → Bool) → Bool) (d : ℕ) :
    advPM (iterFun f d) = advPM f ^ (d + 1) := by
  induction d with
  | zero => exact (pow_one (advPM f)).symm
  | succ d ih =>
      show advPM (composeFun f (iterFun f d)) = _
      rw [advPM_composeFun_eq, ih]
      ring

end Compose

end QuantumQueryComplexity
