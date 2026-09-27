import QuantumQueryComplexity.Quantum.LowerBound.Output
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The sharp output condition, for Boolean outputs

`Output.lean` bounds the final progress by `‖Γ‖(2√ε + ε)` for any finite
output type; this file proves the **sharp** constant `2√(ε(1−ε))` when the
output is Boolean — which is what makes `ε = 1/3` work without amplification.

Two extra facts are available for `O = Bool`, and they are exactly what the
matrix-level argument needs:

* **The `B–B` term vanishes too.**  With two outcomes the error part is
  `B x = qRestrict p (!f x) (ψ x)`; on the support of `Γ` the outputs differ,
  so `!f x ≠ !f y` and the error parts are orthogonal — the same
  `qInner_qRestrict_of_ne` that killed the `A–A` term.  Only the two *cross*
  terms survive.
* **The masses are linked, not just bounded.**  `‖A‖² + ‖B‖² = 1` per input,
  so the weighted masses satisfy `∑‖δA‖² = 1 − β` with `β = ∑‖δB‖² ≤ ε`
  *exactly*, and the two cross terms are `√(1−β)√β' + √β√(1−β')`.

The scalar maximization `√(1−β)√β' + √β√(1−β') ≤ 2√(ε(1−ε))` for
`β, β' ∈ [0, ε]`, `ε ≤ 1/2` is where the sharp constant comes from: after the
AM–GM step `cc' ≤ 1 − (s² + s'²)/2` the square of the left side is at most
`(s+s')²(1−ss')`, whose maximum over `[0,√ε]²` is at the corner — proved by
two monotone steps, each an explicit product-of-nonnegatives factorization
(`poly_step`), no calculus.

No spectral decomposition, no Helstrom measurement theory: the same bridge as
`Output.lean`, with the Boolean structure supplying the two extra facts.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-! ## The scalar maximization -/

private lemma poly_step {e s s' : ℝ} (hs0 : 0 ≤ s) (hs'0 : 0 ≤ s')
    (hse : s ≤ e) (hs'e : s' ≤ e) (he : e ^ 2 ≤ 1 / 2) :
    (s + s') ^ 2 * (1 - s * s') ≤ (e + s') ^ 2 * (1 - e * s') := by
  have he0 : 0 ≤ e := le_trans hs0 hse
  have hs'2 : s' ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ hs'0 hs'e 2
  have hs2 : s ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ hs0 hse 2
  have hes : e * s ≤ e ^ 2 := by
    nlinarith [mul_nonneg he0 (sub_nonneg.mpr hse)]
  have h1 : (0 : ℝ) ≤ 1 - 2 * s' ^ 2 := by linarith
  have h2 : (0 : ℝ) ≤ 2 - e ^ 2 - e * s - s ^ 2 - s' ^ 2 := by linarith
  have hbracket : (0 : ℝ)
      ≤ (e + s) * (1 - 2 * s' ^ 2) + s' * (2 - e ^ 2 - e * s - s ^ 2 - s' ^ 2) :=
    add_nonneg (mul_nonneg (by linarith) h1) (mul_nonneg hs'0 h2)
  have hfact : (e + s') ^ 2 * (1 - e * s') - (s + s') ^ 2 * (1 - s * s')
      = (e - s) * ((e + s) * (1 - 2 * s' ^ 2)
          + s' * (2 - e ^ 2 - e * s - s ^ 2 - s' ^ 2)) := by ring
  have hnn := mul_nonneg (sub_nonneg.mpr hse) hbracket
  linarith [hfact, hnn]

private lemma poly_bound {e s s' : ℝ} (hs0 : 0 ≤ s) (hs'0 : 0 ≤ s')
    (hse : s ≤ e) (hs'e : s' ≤ e) (he : e ^ 2 ≤ 1 / 2) :
    (s + s') ^ 2 * (1 - s * s') ≤ 4 * e ^ 2 * (1 - e ^ 2) := by
  have he0 : 0 ≤ e := le_trans hs0 hse
  calc (s + s') ^ 2 * (1 - s * s')
      ≤ (e + s') ^ 2 * (1 - e * s') := poly_step hs0 hs'0 hse hs'e he
    _ = (s' + e) ^ 2 * (1 - s' * e) := by ring
    _ ≤ (e + e) ^ 2 * (1 - e * e) := poly_step hs'0 he0 hs'e le_rfl he
    _ = 4 * e ^ 2 * (1 - e ^ 2) := by ring

/-- **The linked cross-term maximization**: for masses `β, β' ∈ [0, ε]` with
`ε ≤ 1/2`, `√(1−β)√β' + √β√(1−β') ≤ 2√(ε(1−ε))`, with the maximum at the
corner `β = β' = ε`. -/
private lemma sqrt_cross_sum_le {β β' ε : ℝ} (hβ0 : 0 ≤ β) (hβ'0 : 0 ≤ β')
    (hβε : β ≤ ε) (hβ'ε : β' ≤ ε) (hε2 : ε ≤ 1 / 2) :
    Real.sqrt (1 - β) * Real.sqrt β' + Real.sqrt β * Real.sqrt (1 - β')
      ≤ 2 * Real.sqrt (ε * (1 - ε)) := by
  have hε0 : 0 ≤ ε := le_trans hβ0 hβε
  have hβ1 : β ≤ 1 := by linarith
  have hβ'1 : β' ≤ 1 := by linarith
  set s := Real.sqrt β with hs
  set s' := Real.sqrt β' with hs'
  set c := Real.sqrt (1 - β) with hc
  set c' := Real.sqrt (1 - β') with hc'
  set e := Real.sqrt ε with he
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs'0 : 0 ≤ s' := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hc'0 : 0 ≤ c' := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = β := Real.sq_sqrt hβ0
  have hs'2 : s' ^ 2 = β' := Real.sq_sqrt hβ'0
  have hc2 : c ^ 2 = 1 - β := Real.sq_sqrt (by linarith)
  have hc'2 : c' ^ 2 = 1 - β' := Real.sq_sqrt (by linarith)
  have he2 : e ^ 2 = ε := Real.sq_sqrt hε0
  have hse : s ≤ e := by rw [hs, he]; exact Real.sqrt_le_sqrt hβε
  have hs'e : s' ≤ e := by rw [hs', he]; exact Real.sqrt_le_sqrt hβ'ε
  have heh : e ^ 2 ≤ 1 / 2 := by rw [he2]; exact hε2
  -- AM–GM on the cosine pair
  have hcc : c * c' ≤ 1 - (s ^ 2 + s' ^ 2) / 2 := by
    have hsq := sq_nonneg (c - c')
    rw [show (c - c') ^ 2 = c ^ 2 - 2 * (c * c') + c' ^ 2 from by ring,
      hc2, hc'2] at hsq
    rw [hs2, hs'2]
    linarith
  -- the squared left side, against the polynomial
  have hLsq : (c * s' + s * c') ^ 2 ≤ (s + s') ^ 2 * (1 - s * s') := by
    have h1 : (c * s' + s * c') ^ 2
        = (1 - β) * s' ^ 2 + s ^ 2 * (1 - β') + 2 * (s * s') * (c * c') := by
      rw [show (c * s' + s * c') ^ 2
          = c ^ 2 * s' ^ 2 + s ^ 2 * c' ^ 2 + 2 * (s * s') * (c * c') from by
        ring, hc2, hc'2]
    have h2 : 2 * (s * s') * (c * c')
        ≤ 2 * (s * s') * (1 - (s ^ 2 + s' ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left hcc (by positivity)
    have h3 : (1 - β) * s' ^ 2 + s ^ 2 * (1 - β')
          + 2 * (s * s') * (1 - (s ^ 2 + s' ^ 2) / 2)
        = (s + s') ^ 2 * (1 - s * s') := by
      rw [← hs2, ← hs'2]; ring
    linarith [h1, h2, h3]
  have hpoly := poly_bound hs0 hs'0 hse hs'e heh
  -- conclude by monotone square root
  have hL0 : 0 ≤ c * s' + s * c' :=
    add_nonneg (mul_nonneg hc0 hs'0) (mul_nonneg hs0 hc'0)
  have hchain : (c * s' + s * c') ^ 2 ≤ (2 * Real.sqrt (ε * (1 - ε))) ^ 2 := by
    have hRsq : (2 * Real.sqrt (ε * (1 - ε))) ^ 2 = 4 * (ε * (1 - ε)) := by
      rw [mul_pow, Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ ε * (1 - ε))]
      norm_num
    rw [hRsq]
    calc (c * s' + s * c') ^ 2 ≤ (s + s') ^ 2 * (1 - s * s') := hLsq
      _ ≤ 4 * e ^ 2 * (1 - e ^ 2) := hpoly
      _ = 4 * (ε * (1 - ε)) := by rw [he2]; ring
  have hfin := Real.sqrt_le_sqrt hchain
  rwa [Real.sqrt_sq hL0, Real.sqrt_sq (by positivity)] at hfin

/-! ## The sharp output condition -/

variable {X : Type} [Fintype X] [DecidableEq X]
variable {H : Type} [Fintype H] [DecidableEq H]

/-- **The sharp output condition for Boolean outputs.**  On final states that
are correct with probability at least `1 - ε`, `ε ≤ 1/2`, the progress of any
adversary matrix is at most `‖Γ‖ · 2√(ε(1−ε))`. -/
theorem abs_progress_output_le_bool {Γ : Matrix X X ℝ} {f : X → Bool}
    (hΓ : ∀ x y, f x = f y → Γ x y = 0)
    {ψ : X → (H → ℂ)} (hψ : ∀ x, IsQState (ψ x))
    {p : H → Bool} {ε : ℝ} (hε0 : 0 ≤ ε) (hε2 : ε ≤ 1 / 2)
    (hp : ∀ x, 1 - ε ≤ qProb p (ψ x) (f x))
    {δ δ' : X → ℝ} (hδ : ∑ x, δ x ^ 2 = 1) (hδ' : ∑ y, δ' y ^ 2 = 1) :
    |progress Γ δ δ' ψ| ≤ ‖Γ‖ * (2 * Real.sqrt (ε * (1 - ε))) := by
  classical
  set A : X → (H → ℂ) := fun x => qRestrict p (f x) (ψ x) with hA
  set B : X → (H → ℂ) := fun x => ψ x - A x with hB
  have hsplit : ∀ x, ψ x = A x + B x := by
    intro x
    rw [hB]
    simp
  -- the Boolean structure: the error part announces the complement
  have hBres : ∀ x, B x = qRestrict p (!(f x)) (ψ x) := by
    intro x
    funext h
    simp only [hB, hA, Pi.sub_apply, qRestrict]
    cases hph : p h <;> cases hfx : f x <;> simp
  -- the norms
  have hnormA : ∀ x, qNormSq (A x) = qProb p (ψ x) (f x) := by
    intro x
    rw [hA, qProb_eq_qNormSq_qRestrict]
  have hnormB : ∀ x, qNormSq (B x) = 1 - qProb p (ψ x) (f x) := by
    intro x
    rw [hB, hA, qNormSq_sub_qRestrict, hψ x]
  -- the masses: bounded by `ε` and linked to the `A`-side exactly
  have hsumB : ∑ x, qNormSq (qScale δ B x) ≤ ε := by
    calc ∑ x, qNormSq (qScale δ B x)
        = ∑ x, δ x ^ 2 * (1 - qProb p (ψ x) (f x)) := by
          exact Finset.sum_congr rfl fun x _ => by rw [qNormSq_qScale, hnormB x]
      _ ≤ ∑ x, δ x ^ 2 * ε :=
          Finset.sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left (by linarith [hp x]) (sq_nonneg _)
      _ = ε := by rw [← Finset.sum_mul, hδ, one_mul]
  have hsumB' : ∑ y, qNormSq (qScale δ' B y) ≤ ε := by
    calc ∑ y, qNormSq (qScale δ' B y)
        = ∑ y, δ' y ^ 2 * (1 - qProb p (ψ y) (f y)) := by
          exact Finset.sum_congr rfl fun y _ => by rw [qNormSq_qScale, hnormB y]
      _ ≤ ∑ y, δ' y ^ 2 * ε :=
          Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (by linarith [hp y]) (sq_nonneg _)
      _ = ε := by rw [← Finset.sum_mul, hδ', one_mul]
  have hB0 : 0 ≤ ∑ x, qNormSq (qScale δ B x) :=
    Finset.sum_nonneg fun x _ => qNormSq_nonneg _
  have hB'0 : 0 ≤ ∑ y, qNormSq (qScale δ' B y) :=
    Finset.sum_nonneg fun y _ => qNormSq_nonneg _
  have hAsum : ∑ x, qNormSq (qScale δ A x)
      = 1 - ∑ x, qNormSq (qScale δ B x) := by
    have h : ∀ x, qNormSq (qScale δ A x)
        = δ x ^ 2 - qNormSq (qScale δ B x) := by
      intro x
      rw [qNormSq_qScale, qNormSq_qScale, hnormA x, hnormB x]
      ring
    rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_sub_distrib, hδ]
  have hA'sum : ∑ y, qNormSq (qScale δ' A y)
      = 1 - ∑ y, qNormSq (qScale δ' B y) := by
    have h : ∀ y, qNormSq (qScale δ' A y)
        = δ' y ^ 2 - qNormSq (qScale δ' B y) := by
      intro y
      rw [qNormSq_qScale, qNormSq_qScale, hnormA y, hnormB y]
      ring
    rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_sub_distrib, hδ']
  -- both diagonal terms vanish on the support of `Γ`
  have hAA : gramForm Γ (qScale δ A) (qScale δ' A) = 0 := by
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
    by_cases hf : f x = f y
    · rw [hΓ x y hf, zero_mul]
    · have h0 : qInner (qScale δ A x) (qScale δ' A y) = 0 := by
        rw [qScale_apply, qScale_apply, qInner_smul_left, qInner_smul_right, hA]
        rw [qInner_qRestrict_of_ne p hf]
        ring
      rw [h0]
      simp
  have hBB : gramForm Γ (qScale δ B) (qScale δ' B) = 0 := by
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
    by_cases hf : f x = f y
    · rw [hΓ x y hf, zero_mul]
    · have hne : (!(f x)) ≠ (!(f y)) := by
        intro hcon
        apply hf
        have h2 := congrArg (fun b => !b) hcon
        simpa using h2
      have h0 : qInner (qScale δ B x) (qScale δ' B y) = 0 := by
        rw [qScale_apply, qScale_apply, qInner_smul_left, qInner_smul_right,
          hBres x, hBres y, qInner_qRestrict_of_ne p hne]
        ring
      rw [h0]
      simp
  -- only the two cross terms survive
  have hexp : progress Γ δ δ' ψ
      = gramForm Γ (qScale δ A) (qScale δ' B)
        + gramForm Γ (qScale δ B) (qScale δ' A) := by
    have h1 : qScale δ ψ = fun x => qScale δ A x + qScale δ B x := by
      funext x
      rw [← qScale_add]
      exact congrArg (fun w => qScale δ w x) (funext hsplit)
    have h2 : qScale δ' ψ = fun y => qScale δ' A y + qScale δ' B y := by
      funext y
      rw [← qScale_add]
      exact congrArg (fun w => qScale δ' w y) (funext hsplit)
    rw [progress, h1, h2, gramForm_add_left, gramForm_add_right,
      gramForm_add_right, hAA, hBB]
    ring
  -- the two bridge bounds, with the linked masses
  have hb1 := abs_gramForm_le Γ (qScale δ A) (qScale δ' B)
  have hb2 := abs_gramForm_le Γ (qScale δ B) (qScale δ' A)
  rw [hAsum] at hb1
  rw [hA'sum] at hb2
  -- combine with the scalar maximization
  have hcross := sqrt_cross_sum_le hB0 hB'0 hsumB hsumB' hε2
  have hmul := mul_le_mul_of_nonneg_left hcross (norm_nonneg Γ)
  have habs := abs_add_le (gramForm Γ (qScale δ A) (qScale δ' B))
    (gramForm Γ (qScale δ B) (qScale δ' A))
  rw [hexp]
  linarith [hb1, hb2, hmul, habs]

end QuantumQueryComplexity
