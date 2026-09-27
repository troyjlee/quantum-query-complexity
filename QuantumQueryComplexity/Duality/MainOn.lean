import QuantumQueryComplexity.Duality.CompactOn
import QuantumQueryComplexity.Duality.WitnessOn
import Mathlib.Analysis.LocallyConvex.Separation

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1000000

/-!
# Strong duality for the adversary bound, on a promise domain

The promise mirror of `Duality/Main.lean`: for a **read-determined Boolean**
promise problem, every value above `advPMOn read f` is achieved by a feasible
`DualPairOn`:

    exists_dualPairOn_of_advPMOn_lt :
      advPMOn read f < c → ∃ m (P : DualPairOn read (Fin m) f), P.IsCostLe c.

The argument is the same single Hahn–Banach separation, run in the coordinate
space `DualOmegaOn X → ℝ` with the truncation `T = 2c·|X|`.  Determinacy
(`hdet`) is a genuine hypothesis here: an undetermined pair
(`read x = read y`, `f x ≠ f y`) makes the dual program infeasible while the
primal supremum degenerates.  In the proof it enters through `le_advPMOn`,
and in the no-query case (`ι` empty), where it forces `f` constant so the
zero dual is feasible; the `X = ∅` case is vacuous and does not use it.
The `±1` masking trick
needs the *output* to be two-valued, which is the `f : X → Bool` hypothesis —
exactly the scope the Boolean characterization needs.

Combined with the promise-native lower bound (Milestone A) and extraction
(`UpperBound.lean`), this yields the **promise-Boolean characterization**; see
`Quantum/Characterization.lean`.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Rank-one test matrices concentrated on one query position -/

/-- The vector of Gram indices carrying `s` on the `u`-side and `t` on the
`v`-side of the query position `i₀`, and zero elsewhere. -/
def concVecOn (i₀ : ι) (s t : X → ℝ) : GramIdxOn X ι → ℝ :=
  fun z => if z.2.1 = i₀ then (if z.2.2 then t z.1 else s z.1) else 0

lemma gramROn_concVecOn (read : X → ι → σ) (i₀ : ι) (s t : X → ℝ) (x y : X) :
    gramROn read (vecMulVec (concVecOn i₀ s t) (concVecOn i₀ s t)) x y
      = if read x i₀ = read y i₀ then 0 else s x * t y := by
  rw [gramROn_vecMulVec, Finset.sum_eq_single i₀]
  · by_cases h : read x i₀ = read y i₀ <;> simp [h, concVecOn]
  · intro i _ hi
    by_cases h : read x i = read y i <;> simp [h, concVecOn, hi]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

lemma gramCostOn_concVecOn_false (i₀ : ι) (s t : X → ℝ) (x : X) :
    gramCostOn (vecMulVec (concVecOn i₀ s t) (concVecOn i₀ s t)) false x
      = s x * s x := by
  rw [gramCostOn_vecMulVec, Finset.sum_eq_single i₀]
  · simp [concVecOn]
  · intro i _ hi
    simp [concVecOn, hi]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

lemma gramCostOn_concVecOn_true (i₀ : ι) (s t : X → ℝ) (x : X) :
    gramCostOn (vecMulVec (concVecOn i₀ s t) (concVecOn i₀ s t)) true x
      = t x * t x := by
  rw [gramCostOn_vecMulVec, Finset.sum_eq_single i₀]
  · simp [concVecOn]
  · intro i _ hi
    simp [concVecOn, hi]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

lemma sum_sq_concVecOn (i₀ : ι) (s t : X → ℝ) :
    (∑ z, concVecOn i₀ s t z * concVecOn i₀ s t z)
      = (∑ x, s x * s x) + ∑ x, t x * t x := by
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i₀]
  · simp [concVecOn]
    ring
  · intro i _ hi
    simp [concVecOn, hi]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

lemma concVecOn_ne_zero_left {i₀ : ι} {s t : X → ℝ} (hs : s ≠ 0) :
    concVecOn i₀ s t ≠ 0 := by
  intro h
  refine hs (funext fun x => ?_)
  have := congrFun h (x, i₀, false)
  simpa [concVecOn] using this

lemma concVecOn_ne_zero_right {i₀ : ι} {s t : X → ℝ} (ht : t ≠ 0) :
    concVecOn i₀ s t ≠ 0 := by
  intro h
  refine ht (funext fun x => ?_)
  have := congrFun h (x, i₀, true)
  simpa [concVecOn] using this

/-! ## Symmetrising a two-weight certificate -/

/-- The certificate with the two sides carrying different weights: averaging
reduces to the symmetric case, because `advDOn read i` and `dualTargetOn f`
are symmetric. -/
theorem lt_advPMOn_of_certificate_two {read : X → ι → σ} {f : X → Bool}
    (hdet : ∀ x y, read x = read y → f x = f y)
    {Ξ : Matrix X X ℝ} {p q : X → ℝ} {c : ℝ}
    (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (hquad : ∀ (i : ι) (s t : X → ℝ),
      |s ⬝ᵥ (Ξ ⊙ advDOn read i) *ᵥ t|
        ≤ (∑ x, p x * (s x * s x)) + ∑ y, q y * (t y * t y))
    (hobj : c * ((∑ x, p x) + ∑ x, q x)
      < ∑ x, ∑ y, Ξ x y * dualTargetOn f x y) :
    c < advPMOn read f := by
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
  refine lt_advPMOn_of_certificate hdet (Γ := Ξ') (p := p') ?_ ?_ ?_ ?_
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

/-! ## The separation argument -/

/-- **Promise strong duality, existence form.**  For a read-determined
Boolean promise problem, every value above the promise adversary bound is
achieved by a feasible promise dual solution. -/
theorem exists_dualPairOn_of_advPMOn_lt {read : X → ι → σ} {f : X → Bool}
    (hdet : ∀ x y, read x = read y → f x = f y) {c : ℝ}
    (hc : advPMOn read f < c) :
    ∃ (m : ℕ) (P : DualPairOn read (Fin m) f), P.IsCostLe c := by
  classical
  have hc0 : 0 < c := lt_of_le_of_lt (advPMOn_nonneg hdet) hc
  by_contra hno
  push_neg at hno
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
  have hdisj : Disjoint (gramImageOn read T) (dualBoxOn f c) := by
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
      (convex_dualBoxOn f c) (isClosed_dualBoxOn f c) hdisj
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
      simp [Pi.single_apply, hy]
    · intro h
      exact absurd (Finset.mem_univ x) h
  have hsingleγ : ∀ (b : Bool) (x : X),
      (∑ y, γ b y * ((Pi.single x (1 : ℝ) : X → ℝ) y
        * (Pi.single x (1 : ℝ) : X → ℝ) y)) = γ b x := by
    intro b x
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [Pi.single_apply, hy]
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
  have hcorner := hbox _ (dualCornerOn_mem (f := f) hc0.le)
  have hcornerval : φ (dualCornerOn f c)
      = (∑ x, ∑ y, dualTargetOn f x y * Ξ x y) + ∑ x, ∑ b, c * γ b x := by
    rw [apply_eq_sum_single]
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, dualCornerOn,
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
    (lt_advPMOn_of_certificate_two hdet (hPpos false) (hPpos true) hquadabs hobj)
    (not_lt.mpr hc.le)

/-! ## A nonconstant promise problem has `advPMOn ≥ 1/2`

The crude entrywise bound `‖M‖ ≤ ∑|M|` on the elementary pair matrix loses a
factor of two against the total case's exact `norm_pairMatrix`, which is all
the characterization's constant bookkeeping needs. -/

section Nonconstant

variable {O : Type*} [DecidableEq O]

/-- The elementary promise adversary matrix supported on one symmetric pair. -/
def pairMatrixOn (x y : X) : Matrix X X ℝ :=
  Matrix.single x y 1 + Matrix.single y x 1

lemma pairMatrixOn_isHermitian (x y : X) : (pairMatrixOn x y).IsHermitian := by
  show (pairMatrixOn x y)ᴴ = pairMatrixOn x y
  ext a b
  simp only [Matrix.conjTranspose_apply, pairMatrixOn, Matrix.add_apply,
    Matrix.single_apply, star_trivial]
  rw [add_comm]
  congr 1
  · exact if_congr (by tauto) rfl rfl
  · exact if_congr (by tauto) rfl rfl

lemma pairMatrixOn_apply_self {x y : X} (hxy : x ≠ y) :
    pairMatrixOn x y x y = 1 := by
  simp [pairMatrixOn, Matrix.single_apply, Ne.symm hxy]

lemma sum_abs_pairMatrixOn {x y : X} (hxy : x ≠ y) :
    (∑ a, ∑ b, |pairMatrixOn x y a b|) = 2 := by
  have hentry : ∀ a b, |pairMatrixOn x y a b|
      = (if x = a ∧ y = b then (1 : ℝ) else 0)
        + (if y = a ∧ x = b then (1 : ℝ) else 0) := by
    intro a b
    rw [pairMatrixOn, Matrix.add_apply, Matrix.single_apply,
      Matrix.single_apply]
    by_cases h1 : x = a ∧ y = b
    · obtain ⟨rfl, rfl⟩ := h1
      simp [hxy, Ne.symm hxy]
    · by_cases h2 : y = a ∧ x = b
      · obtain ⟨rfl, rfl⟩ := h2
        simp [hxy, Ne.symm hxy]
      · simp [h1, h2]
  have hone : ∀ (x' y' : X), (∑ a, ∑ b,
      (if x' = a ∧ y' = b then (1 : ℝ) else 0)) = 1 := by
    intro x' y'
    rw [Finset.sum_eq_single x']
    · rw [Finset.sum_eq_single y']
      · simp
      · intro b _ hb
        exact if_neg fun hcon => hb hcon.2.symm
      · intro h
        exact absurd (Finset.mem_univ y') h
    · intro a _ ha
      exact Finset.sum_eq_zero fun b _ => if_neg fun hcon => ha hcon.1.symm
    · intro h
      exact absurd (Finset.mem_univ x') h
  calc (∑ a, ∑ b, |pairMatrixOn x y a b|)
      = (∑ a, ∑ b, ((if x = a ∧ y = b then (1 : ℝ) else 0)
          + (if y = a ∧ x = b then (1 : ℝ) else 0))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          hentry a b
    _ = (∑ a, ∑ b, (if x = a ∧ y = b then (1 : ℝ) else 0))
          + ∑ a, ∑ b, (if y = a ∧ x = b then (1 : ℝ) else 0) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_add_distrib
    _ = 2 := by rw [hone x y, hone y x]; norm_num

/-- **A nonconstant promise problem has `advPMOn ≥ 1/2`**: half the
elementary pair matrix is feasible. -/
theorem half_le_advPMOn {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y) {x y : X}
    (hf : f x ≠ f y) : (1 / 2 : ℝ) ≤ advPMOn read f := by
  have hxy : x ≠ y := fun h => hf (by rw [h])
  have hpair : IsAdvMatrixOn f (pairMatrixOn x y) := by
    refine ⟨pairMatrixOn_isHermitian x y, ?_⟩
    intro a b hab
    by_cases h1 : x = a ∧ y = b
    · obtain ⟨rfl, rfl⟩ := h1
      exact absurd hab hf
    · by_cases h2 : y = a ∧ x = b
      · obtain ⟨rfl, rfl⟩ := h2
        exact absurd hab.symm hf
      · simp [pairMatrixOn, Matrix.single_apply, h1, h2]
  have hadv : IsAdvMatrixOn f ((2⁻¹ : ℝ) • pairMatrixOn x y) :=
    hpair.smul (2⁻¹ : ℝ)
  have hfeas : ∀ i, ‖((2⁻¹ : ℝ) • pairMatrixOn x y) ⊙ advDOn read i‖ ≤ 1 := by
    intro i
    have hsmul : ((2⁻¹ : ℝ) • pairMatrixOn x y) ⊙ advDOn read i
        = (2⁻¹ : ℝ) • (pairMatrixOn x y ⊙ advDOn read i) := by
      ext a b
      simp only [Matrix.smul_apply, Matrix.hadamard_apply, smul_eq_mul]
      ring
    have hmasked : ‖pairMatrixOn x y ⊙ advDOn read i‖ ≤ 2 := by
      refine (l2_opNorm_le_sum_abs _).trans ?_
      rw [← sum_abs_pairMatrixOn hxy]
      refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
      rw [hadamard_advDOn_apply]
      by_cases h : read a i = read b i <;> simp [h]
    rw [hsmul, norm_smul]
    have h2 : ‖(2⁻¹ : ℝ)‖ = (2⁻¹ : ℝ) := by norm_num
    rw [h2]
    nlinarith [hmasked, norm_nonneg (pairMatrixOn x y ⊙ advDOn read i)]
  have hle := le_advPMOn hdet hadv hfeas
  have hentry := abs_entry_le_l2_opNorm ((2⁻¹ : ℝ) • pairMatrixOn x y) x y
  rw [Matrix.smul_apply, pairMatrixOn_apply_self hxy, smul_eq_mul,
    mul_one] at hentry
  have habs : |(2⁻¹ : ℝ)| = (2⁻¹ : ℝ) := by norm_num
  rw [habs] at hentry
  linarith

end Nonconstant

end QuantumQueryComplexity
