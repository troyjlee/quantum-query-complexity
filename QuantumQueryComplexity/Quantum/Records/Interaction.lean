import QuantumQueryComplexity.Quantum.Records.CondBern

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Two-coordinate interaction: Lemma 4.3

For independent bits the conditional differences commute.  For conditioned Bernoulli bits they
need not, and Lemma 4.3 of Cornelissen–Gilani–Zhou bounds the commutator `[Dᵢ, Dⱼ]`
(`CondBern.diffComm`) by the interaction indicator `Aᵢⱼ`.

Fix the coordinates outside `{i, j}` at an assignment of positive probability.  Downward closure
leaves one of the allowed sets `{00}`, `{00, 10}`, `{00, 01}`, `{00, 10, 01}`, `{00, 10, 01, 11}`.
All but `{00, 10, 01}` are products, where the two projections commute.  On `{00, 10, 01}` the
restrictions of `Dᵢ`, `Dⱼ` are rank-one projections onto unit vectors with overlap `p`, and
`Aᵢⱼ = 1` there.  The proofs regroup sums over strings by these two-coordinate fibres
(`sum_eq_sum_twoFiber`).

## Main results

* `CondBern.lemma_4_3` — Lemma 4.3, parts (4.17)–(4.20), for distinct `i`, `j`:
  `[Dᵢ,Dⱼ]†[Dᵢ,Dⱼ] ≤ p² Aᵢⱼ`; `[Dᵢ,Dⱼ]†[Dᵢ,Dⱼ] ≤ p²(1+p)((AᵢⱼDᵢ)†AᵢⱼDᵢ + (AᵢⱼDⱼ)†AᵢⱼDⱼ)`;
  `DᵢDⱼ + DⱼDᵢ ≥ −p Aᵢⱼ(Dᵢ + Dⱼ)`; and pointwise `‖([Dᵢ,Dⱼ]f)ˣ‖ ≤ 2p Aᵢⱼ(x) ‖f‖∞` on every
  finite workspace.
-/

namespace QuantumQueryComplexity

open scoped Matrix MatrixOrder ComplexOrder
open Matrix

variable {ι A : Type} [Fintype ι] [DecidableEq ι] [Fintype A]

namespace CondBern

variable (μ : CondBern ι)

/-- The commutator `[Dᵢ, Dⱼ] = DᵢDⱼ − DⱼDᵢ`. -/
noncomputable def diffComm (i j : ι) : Matrix μ.dist.Supp μ.dist.Supp ℂ :=
  μ.dist.condDiff i * μ.dist.condDiff j - μ.dist.condDiff j * μ.dist.condDiff i

/-! ### Two-coordinate fibres -/

/-- The point of the `{i, j}`-fibre of `w` with `xᵢ = a` and `xⱼ = b`. -/
private def fpt (i j : ι) (w : ι → Bool) (a b : Bool) : ι → Bool :=
  Function.update (Function.update w i a) j b

section Fibre

variable {i j : ι}

private lemma fpt_apply_left (hij : i ≠ j) (w : ι → Bool) (a b : Bool) : fpt i j w a b i = a := by
  simp [fpt, hij]

private lemma fpt_apply_right (w : ι → Bool) (a b : Bool) : fpt i j w a b j = b := by
  simp [fpt]

private lemma fpt_apply_of_ne {k : ι} (hki : k ≠ i) (hkj : k ≠ j) (w : ι → Bool) (a b : Bool) :
    fpt i j w a b k = w k := by
  simp [fpt, hki, hkj]

private lemma update_fpt_left (hij : i ≠ j) (w : ι → Bool) (a b c : Bool) :
    Function.update (fpt i j w a b) i c = fpt i j w c b := by
  funext k
  simp only [fpt, Function.update_apply]
  split_ifs <;> simp_all

private lemma update_fpt_right (w : ι → Bool) (a b c : Bool) :
    Function.update (fpt i j w a b) j c = fpt i j w a c := by
  simp [fpt]

private lemma fpt_fpt (w : ι → Bool) (a b c d : Bool) :
    fpt i j (fpt i j w a b) c d = fpt i j w c d := by
  funext k
  simp only [fpt, Function.update_apply]
  split_ifs <;> rfl

private lemma fpt_self (w : ι → Bool) : fpt i j w (w i) (w j) = w := by
  funext k
  simp only [fpt, Function.update_apply]
  split_ifs with h1 h2 <;> subst_vars <;> rfl

/-! ### Workspace vectors on a fibre -/

private lemma wvecAt_of_not_avoids (f : JVec μ.dist.Supp A) {y : ι → Bool}
    (hy : ¬ Avoids μ.forbidden y) : μ.dist.wvecAt f y = 0 := by
  unfold FinDist.wvecAt
  rw [dite_eq_right (fun h => absurd ((μ.mass_pos_iff y).mp h) hy)]

private lemma wvecAt_add (f g : JVec μ.dist.Supp A) (y : ι → Bool) :
    μ.dist.wvecAt (f + g) y = μ.dist.wvecAt f y + μ.dist.wvecAt g y := by
  unfold FinDist.wvecAt
  split_ifs
  · exact smul_add _ _ _
  · simp

private lemma wvecAt_sub (f g : JVec μ.dist.Supp A) (y : ι → Bool) :
    μ.dist.wvecAt (f - g) y = μ.dist.wvecAt f y - μ.dist.wvecAt g y := by
  unfold FinDist.wvecAt
  split_ifs
  · exact smul_sub _ _ _
  · simp

private lemma wvecAt_smul (c : ℂ) (f : JVec μ.dist.Supp A) (y : ι → Bool) :
    μ.dist.wvecAt (c • f) y = c • μ.dist.wvecAt f y := by
  unfold FinDist.wvecAt
  split_ifs with h
  · exact smul_comm ((Real.sqrt (μ.dist.mass y))⁻¹ : ℂ) c (f ⟨y, h⟩)
  · simp

private lemma wvecAt_condDiff_mul (k : ι) (f : JVec μ.dist.Supp A) (y : ι → Bool) :
    μ.dist.wvecAt (μ.dist.condDiff k * f) y =
      if Avoids μ.forbidden y ∧ Avoids μ.forbidden (Function.update y k true) then
        ((if y k then 1 - μ.p else μ.p : ℝ) : ℂ) •
          (μ.dist.wvecAt f y - μ.dist.wvecAt f (Function.update y k (!y k)))
      else 0 := by
  by_cases hy : Avoids μ.forbidden y
  · have hm : 0 < μ.dist.mass y := (μ.mass_pos_iff y).mpr hy
    have h1 := μ.dist.wvecAt_coe (μ.dist.condDiff k * f) ⟨y, hm⟩
    have h2 := μ.dist.wvecAt_coe f ⟨y, hm⟩
    simp only at h1 h2
    rw [h1, μ.wvec_condDiff_mul k f ⟨y, hm⟩, h2]
    simp only [Free, hy, true_and]
  · rw [wvecAt_of_not_avoids μ _ hy, ite_eq_right (fun h => hy h.1)]

private lemma wvecAt_condDiff_left (hij : i ≠ j) (f : JVec μ.dist.Supp A) (w : ι → Bool)
    (a b : Bool) :
    μ.dist.wvecAt (μ.dist.condDiff i * f) (fpt i j w a b) =
      if Avoids μ.forbidden (fpt i j w a b) ∧ Avoids μ.forbidden (fpt i j w true b) then
        ((if a then 1 - μ.p else μ.p : ℝ) : ℂ) •
          (μ.dist.wvecAt f (fpt i j w a b) - μ.dist.wvecAt f (fpt i j w (!a) b))
      else 0 := by
  rw [wvecAt_condDiff_mul, fpt_apply_left hij, update_fpt_left hij, update_fpt_left hij]

private lemma wvecAt_condDiff_right (f : JVec μ.dist.Supp A) (w : ι → Bool) (a b : Bool) :
    μ.dist.wvecAt (μ.dist.condDiff j * f) (fpt i j w a b) =
      if Avoids μ.forbidden (fpt i j w a b) ∧ Avoids μ.forbidden (fpt i j w a true) then
        ((if b then 1 - μ.p else μ.p : ℝ) : ℂ) •
          (μ.dist.wvecAt f (fpt i j w a b) - μ.dist.wvecAt f (fpt i j w a (!b)))
      else 0 := by
  rw [wvecAt_condDiff_mul, fpt_apply_right, update_fpt_right, update_fpt_right]

private lemma wvecAt_diagonal_mul (d : μ.dist.Supp → ℂ) (f : JVec μ.dist.Supp A) (y : ι → Bool)
    (c : ℂ) (hd : ∀ h : 0 < μ.dist.mass y, d ⟨y, h⟩ = c) :
    μ.dist.wvecAt (Matrix.diagonal d * f) y = c • μ.dist.wvecAt f y := by
  unfold FinDist.wvecAt
  split_ifs with h
  · rw [← hd h]
    funext a
    simp only [FinDist.wvec, Pi.smul_apply, smul_eq_mul, Matrix.diagonal_mul]
    ring
  · simp

private lemma wvecAt_interactOp_mul (f : JVec μ.dist.Supp A) (w : ι → Bool) (a b : Bool) :
    μ.dist.wvecAt (μ.interactOp i j * f) (fpt i j w a b) =
      (if μ.Interact i j w then 1 else 0 : ℂ) • μ.dist.wvecAt f (fpt i j w a b) := by
  refine μ.wvecAt_diagonal_mul _ f _ _ fun _ => ?_
  have : μ.Interact i j (fpt i j w a b) ↔ μ.Interact i j w :=
    μ.interact_congr fun k hki hkj => fpt_apply_of_ne hki hkj w a b
  simp only [this]

/-- The fibre of `w` has allowed pattern `{00, 10, 01}`: the only case where `Dᵢ` and `Dⱼ` fail
to commute. -/
private def NonProd (i j : ι) (w : ι → Bool) : Prop :=
  Avoids μ.forbidden (fpt i j w true false) ∧ Avoids μ.forbidden (fpt i j w false true) ∧
    ¬ Avoids μ.forbidden (fpt i j w true true)

private instance (i j : ι) : DecidablePred (μ.NonProd i j) := fun _ => by
  unfold NonProd; infer_instance

/-- The diagonal indicator of the non-product fibres. -/
private noncomputable def nonProdOp (i j : ι) : Matrix μ.dist.Supp μ.dist.Supp ℂ :=
  Matrix.diagonal fun x => if μ.NonProd i j x.1 then 1 else 0

private lemma nonProdOp_isHermitian (i j : ι) : (μ.nonProdOp i j).IsHermitian := by
  refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
  funext x
  simp only [Pi.star_apply]
  split_ifs <;> simp

private lemma nonProd_fpt (w : ι → Bool) (a b : Bool) :
    μ.NonProd i j (fpt i j w a b) ↔ μ.NonProd i j w := by
  simp only [NonProd, fpt_fpt]

private lemma wvecAt_nonProdOp_mul (f : JVec μ.dist.Supp A) (w : ι → Bool) (a b : Bool) :
    μ.dist.wvecAt (μ.nonProdOp i j * f) (fpt i j w a b) =
      (if μ.NonProd i j w then 1 else 0 : ℂ) • μ.dist.wvecAt f (fpt i j w a b) := by
  refine μ.wvecAt_diagonal_mul _ f _ _ fun _ => ?_
  simp only [μ.nonProd_fpt]

/-- In the non-product case some forbidden set contains `i` and `j` and is one elsewhere. -/
private lemma interact_of_nonProd (hij : i ≠ j) {w : ι → Bool} (h : μ.NonProd i j w) :
    μ.Interact i j w := by
  obtain ⟨h10, h01, h11⟩ := h
  simp only [Avoids, not_forall, not_exists, not_and, Bool.not_eq_false] at h11
  obtain ⟨C, hC, hCone⟩ := h11
  refine ⟨C, hC, ?_, ?_, fun k hk hki hkj => ?_⟩
  · obtain ⟨k, hk, hk0⟩ := h01 C hC
    by_cases hki : k = i
    · exact hki ▸ hk
    · by_cases hkj : k = j
      · rw [hkj, fpt_apply_right] at hk0
        exact absurd hk0 (by simp)
      · rw [fpt_apply_of_ne hki hkj] at hk0
        have := hCone k hk
        rw [fpt_apply_of_ne hki hkj] at this
        exact absurd hk0 (by simp [this])
  · obtain ⟨k, hk, hk0⟩ := h10 C hC
    by_cases hkj : k = j
    · exact hkj ▸ hk
    · by_cases hki : k = i
      · rw [hki, fpt_apply_left hij] at hk0
        exact absurd hk0 (by simp)
      · rw [fpt_apply_of_ne hki hkj] at hk0
        have := hCone k hk
        rw [fpt_apply_of_ne hki hkj] at this
        exact absurd hk0 (by simp [this])
  · have := hCone k hk
    rwa [fpt_apply_of_ne hki hkj] at this

private lemma avoids_fpt_mono (hij : i ≠ j) {w : ι → Bool} {a b a' b' : Bool}
    (h : Avoids μ.forbidden (fpt i j w a b)) (ha : a' = true → a = true)
    (hb : b' = true → b = true) : Avoids μ.forbidden (fpt i j w a' b') := by
  refine Avoids.mono h fun k hk => ?_
  by_cases hkj : k = j
  · subst hkj
    rw [fpt_apply_right] at hk ⊢
    exact hb hk
  by_cases hki : k = i
  · subst hki
    rw [fpt_apply_left hij] at hk ⊢
    exact ha hk
  rw [fpt_apply_of_ne hki hkj] at hk ⊢
  exact hk

/-- The five allowed patterns of a fibre (and the empty one). -/
private lemma fibre_pattern (hij : i ≠ j) (w : ι → Bool) :
    (Avoids μ.forbidden (fpt i j w false false) ∧ Avoids μ.forbidden (fpt i j w true false) ∧
      Avoids μ.forbidden (fpt i j w false true) ∧ Avoids μ.forbidden (fpt i j w true true)) ∨
    (Avoids μ.forbidden (fpt i j w false false) ∧ Avoids μ.forbidden (fpt i j w true false) ∧
      Avoids μ.forbidden (fpt i j w false true) ∧ ¬ Avoids μ.forbidden (fpt i j w true true)) ∨
    (Avoids μ.forbidden (fpt i j w false false) ∧ Avoids μ.forbidden (fpt i j w true false) ∧
      ¬ Avoids μ.forbidden (fpt i j w false true) ∧ ¬ Avoids μ.forbidden (fpt i j w true true)) ∨
    (Avoids μ.forbidden (fpt i j w false false) ∧ ¬ Avoids μ.forbidden (fpt i j w true false) ∧
      Avoids μ.forbidden (fpt i j w false true) ∧ ¬ Avoids μ.forbidden (fpt i j w true true)) ∨
    (Avoids μ.forbidden (fpt i j w false false) ∧ ¬ Avoids μ.forbidden (fpt i j w true false) ∧
      ¬ Avoids μ.forbidden (fpt i j w false true) ∧ ¬ Avoids μ.forbidden (fpt i j w true true)) ∨
    (¬ Avoids μ.forbidden (fpt i j w false false) ∧ ¬ Avoids μ.forbidden (fpt i j w true false) ∧
      ¬ Avoids μ.forbidden (fpt i j w false true) ∧
      ¬ Avoids μ.forbidden (fpt i j w true true)) := by
  have m : ∀ {a b a' b' : Bool}, Avoids μ.forbidden (fpt i j w a b) →
      (a' = true → a = true) → (b' = true → b = true) → Avoids μ.forbidden (fpt i j w a' b') :=
    fun h ha hb => μ.avoids_fpt_mono hij h ha hb
  by_cases h11 : Avoids μ.forbidden (fpt i j w true true)
  · exact Or.inl ⟨m h11 (by simp) (by simp), m h11 (by simp) (by simp),
      m h11 (by simp) (by simp), h11⟩
  by_cases h10 : Avoids μ.forbidden (fpt i j w true false) <;>
    by_cases h01 : Avoids μ.forbidden (fpt i j w false true)
  · exact Or.inr (Or.inl ⟨m h10 (by simp) (by simp), h10, h01, h11⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨m h10 (by simp) (by simp), h10, h01, h11⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m h01 (by simp) (by simp), h10, h01, h11⟩)))
  · by_cases h00 : Avoids μ.forbidden (fpt i j w false false)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h00, h10, h01, h11⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h00, h10, h01, h11⟩))))

/-- Matrices on the input register agree if they agree on every fibre point. -/
private lemma ext_fpt {M M' : Matrix μ.dist.Supp μ.dist.Supp ℂ}
    (h : ∀ (f : JVec μ.dist.Supp μ.dist.Supp) (w : ι → Bool) (a b : Bool),
      μ.dist.wvecAt (M * f) (fpt i j w a b) = μ.dist.wvecAt (M' * f) (fpt i j w a b)) :
    M = M' := by
  have key : ∀ x : μ.dist.Supp, μ.dist.wvec M x = μ.dist.wvec M' x := by
    intro x
    have := h 1 x.1 (x.1 i) (x.1 j)
    rw [fpt_self, Matrix.mul_one, Matrix.mul_one] at this
    rwa [μ.dist.wvecAt_coe, μ.dist.wvecAt_coe] at this
  rw [← μ.dist.ofWvec_wvec M, ← μ.dist.ofWvec_wvec M']
  exact congrArg _ (funext key)

end Fibre

section Keys

variable {i j : ι}

set_option hygiene false in
/-- Verify an identity at a fibre point `fpt i j w a b` by splitting into the allowed patterns of
the fibre, the value of `Aᵢⱼ`, and the position `(a, b)`, and evaluating every operator with the
two-point formulas. -/
local macro "fibre_bash" : tactic => `(tactic| (
  rcases μ.fibre_pattern hij w with ⟨h00, h10, h01, h11⟩ | ⟨h00, h10, h01, h11⟩ |
    ⟨h00, h10, h01, h11⟩ | ⟨h00, h10, h01, h11⟩ | ⟨h00, h10, h01, h11⟩ | ⟨h00, h10, h01, h11⟩ <;>
  by_cases hα : μ.Interact i j w <;>
  cases a <;> cases b <;>
  first
  | exact absurd hy h00 | exact absurd hy h10 | exact absurd hy h01 | exact absurd hy h11
  | exact absurd (μ.interact_of_nonProd hij ⟨h10, h01, h11⟩) hα
  | exact (hN ⟨h10, h01, h11⟩).elim
  | (simp only [μ.wvecAt_condDiff_left hij, μ.wvecAt_condDiff_right (i := i) (j := j),
      μ.wvecAt_interactOp_mul, μ.wvecAt_nonProdOp_mul, NonProd, h00, h10, h01, h11, hα,
      Bool.not_true, Bool.not_false, and_self, and_true, true_and, and_false, false_and,
      not_true_eq_false, not_false_eq_true, ↓reduceIte, Bool.false_eq_true,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_mul,
      Complex.ofReal_add]
     module)))

/-- Sum-of-squares form of (4.17): with `N` the non-product indicator and `S = Dᵢ + Dⱼ`,
`p²Aᵢⱼ − [Dᵢ,Dⱼ]†[Dᵢ,Dⱼ] = p²(Aᵢⱼ − N)² + p²((1 − S)N)†((1 − S)N)`. -/
private lemma key_17 (hij : i ≠ j) :
    ((μ.p ^ 2 : ℝ) : ℂ) • μ.interactOp i j
      - (μ.dist.condDiff j * μ.dist.condDiff i - μ.dist.condDiff i * μ.dist.condDiff j)
        * (μ.dist.condDiff i * μ.dist.condDiff j - μ.dist.condDiff j * μ.dist.condDiff i)
    = ((μ.p ^ 2 : ℝ) : ℂ) • ((μ.interactOp i j - μ.nonProdOp i j)
        * (μ.interactOp i j - μ.nonProdOp i j))
      + ((μ.p ^ 2 : ℝ) : ℂ) • ((μ.nonProdOp i j * (1 - μ.dist.condDiff i - μ.dist.condDiff j))
          * ((1 - μ.dist.condDiff i - μ.dist.condDiff j) * μ.nonProdOp i j)) := by
  refine μ.ext_fpt (i := i) (j := j) fun f w a b => ?_
  by_cases hy : Avoids μ.forbidden (fpt i j w a b)
  swap
  · rw [wvecAt_of_not_avoids μ _ hy, wvecAt_of_not_avoids μ _ hy]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.one_mul,
    Matrix.mul_sub, Matrix.mul_one, wvecAt_sub, wvecAt_add, wvecAt_smul]
  fibre_bash

/-- Sum-of-squares form of (4.18), with `X = (pDᵢ + DᵢDⱼ)N`. -/
private lemma key_18 (hij : i ≠ j) :
    ((μ.p ^ 2 * (1 + μ.p) : ℝ) : ℂ) •
        ((μ.dist.condDiff i * μ.interactOp i j) * (μ.interactOp i j * μ.dist.condDiff i)
          + (μ.dist.condDiff j * μ.interactOp i j) * (μ.interactOp i j * μ.dist.condDiff j))
      - (μ.dist.condDiff j * μ.dist.condDiff i - μ.dist.condDiff i * μ.dist.condDiff j)
        * (μ.dist.condDiff i * μ.dist.condDiff j - μ.dist.condDiff j * μ.dist.condDiff i)
    = ((μ.p ^ 2 * (1 + μ.p) : ℝ) : ℂ) •
        ((μ.dist.condDiff i * (μ.interactOp i j - μ.nonProdOp i j))
            * ((μ.interactOp i j - μ.nonProdOp i j) * μ.dist.condDiff i)
          + (μ.dist.condDiff j * (μ.interactOp i j - μ.nonProdOp i j))
            * ((μ.interactOp i j - μ.nonProdOp i j) * μ.dist.condDiff j))
      + ((μ.p : ℝ) : ℂ) •
        ((μ.nonProdOp i j * (((μ.p : ℝ) : ℂ) • μ.dist.condDiff i
            + μ.dist.condDiff j * μ.dist.condDiff i))
          * ((((μ.p : ℝ) : ℂ) • μ.dist.condDiff i + μ.dist.condDiff i * μ.dist.condDiff j)
            * μ.nonProdOp i j)) := by
  refine μ.ext_fpt (i := i) (j := j) fun f w a b => ?_
  by_cases hy : Avoids μ.forbidden (fpt i j w a b)
  swap
  · rw [wvecAt_of_not_avoids μ _ hy, wvecAt_of_not_avoids μ _ hy]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_sub,
    Matrix.mul_add, Matrix.mul_smul, wvecAt_sub, wvecAt_add, wvecAt_smul]
  fibre_bash

/-- Sum-of-squares form of `p` times (4.19); off the non-product fibres `DᵢDⱼ + DⱼDᵢ` is
`2(DⱼDᵢ(1 − N))†(DⱼDᵢ(1 − N))`. -/
private lemma key_19 (hij : i ≠ j) :
    ((μ.p : ℝ) : ℂ) • (μ.dist.condDiff i * μ.dist.condDiff j + μ.dist.condDiff j * μ.dist.condDiff i
      + ((μ.p : ℝ) : ℂ) • (μ.interactOp i j * (μ.dist.condDiff i + μ.dist.condDiff j)))
    = (μ.nonProdOp i j * (((μ.p : ℝ) : ℂ) • μ.dist.condDiff i
            + μ.dist.condDiff j * μ.dist.condDiff i))
          * ((((μ.p : ℝ) : ℂ) • μ.dist.condDiff i + μ.dist.condDiff i * μ.dist.condDiff j)
            * μ.nonProdOp i j)
      + ((μ.p : ℝ) : ℂ) • ((2 : ℂ) • (((1 - μ.nonProdOp i j)
            * (μ.dist.condDiff i * μ.dist.condDiff j))
          * (μ.dist.condDiff j * μ.dist.condDiff i * (1 - μ.nonProdOp i j)))
        + ((μ.p : ℝ) : ℂ) •
          ((μ.dist.condDiff i * (μ.interactOp i j - μ.nonProdOp i j))
              * ((μ.interactOp i j - μ.nonProdOp i j) * μ.dist.condDiff i)
            + (μ.dist.condDiff j * (μ.interactOp i j - μ.nonProdOp i j))
              * ((μ.interactOp i j - μ.nonProdOp i j) * μ.dist.condDiff j))) := by
  refine μ.ext_fpt (i := i) (j := j) fun f w a b => ?_
  by_cases hy : Avoids μ.forbidden (fpt i j w a b)
  swap
  · rw [wvecAt_of_not_avoids μ _ hy, wvecAt_of_not_avoids μ _ hy]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.one_mul,
    Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, wvecAt_sub, wvecAt_add,
    wvecAt_smul]
  fibre_bash

/-- Off the non-product fibres `Dᵢ` and `Dⱼ` commute. -/
private lemma wvecAt_comm_eq_zero (hij : i ≠ j) (f : JVec μ.dist.Supp A) (w : ι → Bool)
    (a b : Bool) (hN : ¬ μ.NonProd i j w) :
    μ.dist.wvecAt ((μ.dist.condDiff i * μ.dist.condDiff j
      - μ.dist.condDiff j * μ.dist.condDiff i) * f) (fpt i j w a b) = 0 := by
  by_cases hy : Avoids μ.forbidden (fpt i j w a b)
  swap
  · exact wvecAt_of_not_avoids μ _ hy
  simp only [Matrix.sub_mul, Matrix.mul_assoc, wvecAt_sub]
  fibre_bash

/-- The commutator on a non-product fibre (CGZ, proof of (4.20)). -/
private lemma wvecAt_comm_nonProd (hij : i ≠ j) (f : JVec μ.dist.Supp A) (w : ι → Bool)
    (hN : μ.NonProd i j w) :
    μ.dist.wvecAt ((μ.dist.condDiff i * μ.dist.condDiff j
        - μ.dist.condDiff j * μ.dist.condDiff i) * f) (fpt i j w false false)
      = ((μ.p ^ 2 : ℝ) : ℂ) •
        (μ.dist.wvecAt f (fpt i j w true false) - μ.dist.wvecAt f (fpt i j w false true)) ∧
    μ.dist.wvecAt ((μ.dist.condDiff i * μ.dist.condDiff j
        - μ.dist.condDiff j * μ.dist.condDiff i) * f) (fpt i j w true false)
      = ((μ.p * (1 - μ.p) : ℝ) : ℂ) •
        (μ.dist.wvecAt f (fpt i j w false true) - μ.dist.wvecAt f (fpt i j w false false)) ∧
    μ.dist.wvecAt ((μ.dist.condDiff i * μ.dist.condDiff j
        - μ.dist.condDiff j * μ.dist.condDiff i) * f) (fpt i j w false true)
      = ((μ.p * (1 - μ.p) : ℝ) : ℂ) •
        (μ.dist.wvecAt f (fpt i j w false false) - μ.dist.wvecAt f (fpt i j w true false)) := by
  obtain ⟨h10, h01, h11⟩ := hN
  have h00 : Avoids μ.forbidden (fpt i j w false false) :=
    μ.avoids_fpt_mono hij h10 (by simp) (by simp)
  simp only [Matrix.sub_mul, Matrix.mul_assoc, wvecAt_sub]
  refine ⟨?_, ?_, ?_⟩ <;>
  simp only [μ.wvecAt_condDiff_left hij, μ.wvecAt_condDiff_right (i := i) (j := j),
      h00, h10, h01, h11, Bool.not_true, Bool.not_false, and_self, and_false, ↓reduceIte,
      Bool.false_eq_true,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_mul] <;>
  module

end Keys

/-- `‖c (u − v)‖² ≤ 4c²K` when `‖u‖², ‖v‖² ≤ K`. -/
private lemma qNormSq_smul_sub_le {B : Type} [Fintype B] (c K : ℝ) (u v : B → ℂ)
    (hu : qNormSq u ≤ K) (hv : qNormSq v ≤ K) : qNormSq ((c : ℂ) • (u - v)) ≤ 4 * c ^ 2 * K := by
  classical
  rw [qNormSq_smul, Complex.normSq_ofReal]
  have h1 : qNormSq (u - v) ≤ 2 * qNormSq u + 2 * qNormSq v := by
    simp only [qNormSq_def, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    nlinarith [sq_nonneg ((u k).re + (v k).re), sq_nonneg ((u k).im + (v k).im)]
  have h2 : 0 ≤ c * c := mul_self_nonneg c
  calc c * c * qNormSq (u - v) ≤ c * c * (2 * K + 2 * K) :=
        mul_le_mul_of_nonneg_left (by linarith) h2
    _ = 4 * c ^ 2 * K := by ring

private lemma qNormSq_wvecAt_le (f : JVec μ.dist.Supp A) (y : ι → Bool) :
    qNormSq (μ.dist.wvecAt f y) ≤ μ.dist.infNormSq f := by
  classical
  unfold FinDist.wvecAt
  split_ifs with h
  · exact μ.dist.qNormSq_wvec_le_infNormSq f _
  · rw [qNormSq_zero]
    exact μ.dist.infNormSq_nonneg f



/-- **(4.17)** `‖[Dᵢ, Dⱼ] f‖ ≤ p ‖Aᵢⱼ f‖`. -/
theorem diffComm_sq_le_interactOp {i j : ι} (hij : i ≠ j) :
    (μ.diffComm i j)ᴴ * μ.diffComm i j ≤ ((μ.p ^ 2 : ℝ) : ℂ) • μ.interactOp i j := by
  have hD := (μ.dist.condDiff_isHermitian i).eq
  have hD' := (μ.dist.condDiff_isHermitian j).eq
  have hN := (μ.nonProdOp_isHermitian i j).eq
  have hAN := ((μ.interactOp_isHermitian i j).sub (μ.nonProdOp_isHermitian i j)).eq
  rw [Matrix.le_iff, diffComm, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hD, hD',
    μ.key_17 hij]
  have hp : (0 : ℂ) ≤ ((μ.p ^ 2 : ℝ) : ℂ) := Complex.zero_le_real.mpr (by positivity)
  refine (PosSemidef.smul ?_ hp).add (PosSemidef.smul ?_ hp)
  · simpa only [hAN] using
      posSemidef_conjTranspose_mul_self (μ.interactOp i j - μ.nonProdOp i j)
  · have h := posSemidef_conjTranspose_mul_self
        ((1 - μ.dist.condDiff i - μ.dist.condDiff j) * μ.nonProdOp i j)
    rw [conjTranspose_mul] at h
    rw [conjTranspose_sub] at h
    rw [conjTranspose_sub] at h
    rw [conjTranspose_one] at h
    rw [hD, hD', hN] at h
    exact h

/-- **(4.18)** `‖[Dᵢ, Dⱼ] f‖² ≤ p²(1 + p)(‖AᵢⱼDᵢ f‖² + ‖AᵢⱼDⱼ f‖²)`. -/
theorem diffComm_sq_le_interact_condDiff {i j : ι} (hij : i ≠ j) :
    (μ.diffComm i j)ᴴ * μ.diffComm i j ≤ ((μ.p ^ 2 * (1 + μ.p) : ℝ) : ℂ) •
      ((μ.interactOp i j * μ.dist.condDiff i)ᴴ * (μ.interactOp i j * μ.dist.condDiff i)
        + (μ.interactOp i j * μ.dist.condDiff j)ᴴ * (μ.interactOp i j * μ.dist.condDiff j)) := by
  have hD := (μ.dist.condDiff_isHermitian i).eq
  have hD' := (μ.dist.condDiff_isHermitian j).eq
  have hA := (μ.interactOp_isHermitian i j).eq
  have hN := (μ.nonProdOp_isHermitian i j).eq
  have hAN := ((μ.interactOp_isHermitian i j).sub (μ.nonProdOp_isHermitian i j)).eq
  rw [Matrix.le_iff, diffComm]
  simp only [conjTranspose_sub, conjTranspose_mul, hD, hD', hA]
  rw [μ.key_18 hij]
  have hp : (0 : ℂ) ≤ ((μ.p : ℝ) : ℂ) := Complex.zero_le_real.mpr μ.p_pos.le
  have hc : (0 : ℂ) ≤ ((μ.p ^ 2 * (1 + μ.p) : ℝ) : ℂ) :=
    Complex.zero_le_real.mpr (by have := μ.p_pos; positivity)
  have hs : star ((μ.p : ℝ) : ℂ) = ((μ.p : ℝ) : ℂ) := Complex.conj_ofReal _
  refine (PosSemidef.smul (PosSemidef.add ?_ ?_) hc).add (PosSemidef.smul ?_ hp)
  · have h := posSemidef_conjTranspose_mul_self
      ((μ.interactOp i j - μ.nonProdOp i j) * μ.dist.condDiff i)
    rw [conjTranspose_mul, hD, hAN] at h
    exact h
  · have h := posSemidef_conjTranspose_mul_self
      ((μ.interactOp i j - μ.nonProdOp i j) * μ.dist.condDiff j)
    rw [conjTranspose_mul, hD', hAN] at h
    exact h
  · have h := posSemidef_conjTranspose_mul_self ((((μ.p : ℝ) : ℂ) • μ.dist.condDiff i
        + μ.dist.condDiff i * μ.dist.condDiff j) * μ.nonProdOp i j)
    rw [conjTranspose_mul, conjTranspose_add, conjTranspose_smul, conjTranspose_mul, hD, hD', hN,
      hs] at h
    exact h

/-- **(4.19)** `DᵢDⱼ + DⱼDᵢ ≥ −p Aᵢⱼ (Dᵢ + Dⱼ)`. -/
theorem anticomm_ge {i j : ι} (hij : i ≠ j) :
    -(((μ.p : ℝ) : ℂ) • (μ.interactOp i j * (μ.dist.condDiff i + μ.dist.condDiff j)))
      ≤ μ.dist.condDiff i * μ.dist.condDiff j + μ.dist.condDiff j * μ.dist.condDiff i := by
  have hD := (μ.dist.condDiff_isHermitian i).eq
  have hD' := (μ.dist.condDiff_isHermitian j).eq
  have hN := (μ.nonProdOp_isHermitian i j).eq
  have hAN := ((μ.interactOp_isHermitian i j).sub (μ.nonProdOp_isHermitian i j)).eq
  have hp : (0 : ℂ) ≤ ((μ.p : ℝ) : ℂ) := Complex.zero_le_real.mpr μ.p_pos.le
  rw [Matrix.le_iff, sub_neg_eq_add]
  have key : (((μ.p : ℝ) : ℂ) • (μ.dist.condDiff i * μ.dist.condDiff j
      + μ.dist.condDiff j * μ.dist.condDiff i
      + ((μ.p : ℝ) : ℂ) • (μ.interactOp i j
        * (μ.dist.condDiff i + μ.dist.condDiff j)))).PosSemidef := by
    rw [μ.key_19 hij]
    have hs : star ((μ.p : ℝ) : ℂ) = ((μ.p : ℝ) : ℂ) := Complex.conj_ofReal _
    refine PosSemidef.add ?_ (PosSemidef.smul (PosSemidef.add (PosSemidef.smul ?_ zero_le_two)
      (PosSemidef.smul (PosSemidef.add ?_ ?_) hp)) hp)
    · have h := posSemidef_conjTranspose_mul_self ((((μ.p : ℝ) : ℂ) • μ.dist.condDiff i
          + μ.dist.condDiff i * μ.dist.condDiff j) * μ.nonProdOp i j)
      rw [conjTranspose_mul, conjTranspose_add, conjTranspose_smul, conjTranspose_mul, hD, hD',
        hN, hs] at h
      exact h
    · have h := posSemidef_conjTranspose_mul_self
        (μ.dist.condDiff j * μ.dist.condDiff i * (1 - μ.nonProdOp i j))
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hD, hD',
        hN] at h
      exact h
    · have h := posSemidef_conjTranspose_mul_self
        ((μ.interactOp i j - μ.nonProdOp i j) * μ.dist.condDiff i)
      rw [conjTranspose_mul, hD, hAN] at h
      exact h
    · have h := posSemidef_conjTranspose_mul_self
        ((μ.interactOp i j - μ.nonProdOp i j) * μ.dist.condDiff j)
      rw [conjTranspose_mul, hD', hAN] at h
      exact h
  have hinv : (0 : ℂ) ≤ ((μ.p⁻¹ : ℝ) : ℂ) := Complex.zero_le_real.mpr (inv_nonneg.mpr μ.p_pos.le)
  have e : μ.dist.condDiff i * μ.dist.condDiff j + μ.dist.condDiff j * μ.dist.condDiff i
      + ((μ.p : ℝ) : ℂ) • (μ.interactOp i j * (μ.dist.condDiff i + μ.dist.condDiff j))
      = ((μ.p⁻¹ : ℝ) : ℂ) • (((μ.p : ℝ) : ℂ) • (μ.dist.condDiff i * μ.dist.condDiff j
        + μ.dist.condDiff j * μ.dist.condDiff i
        + ((μ.p : ℝ) : ℂ) • (μ.interactOp i j * (μ.dist.condDiff i + μ.dist.condDiff j)))) := by
    rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ μ.p_pos.ne', Complex.ofReal_one, one_smul]
  rw [e]
  exact key.smul hinv

/-- **(4.20)** `‖([Dᵢ, Dⱼ] f)ˣ‖ ≤ 2p Aᵢⱼ(x) ‖f‖∞` at every support point, on every finite
workspace. -/
theorem qNormSq_wvec_diffComm_le {i j : ι} (hij : i ≠ j) (f : JVec μ.dist.Supp A)
    (x : μ.dist.Supp) :
    qNormSq (μ.dist.wvec (μ.diffComm i j * f) x)
      ≤ 4 * μ.p ^ 2 * (if μ.Interact i j x.1 then 1 else 0) * μ.dist.infNormSq f := by
  classical
  have hK := μ.qNormSq_wvecAt_le f
  have hK0 := μ.dist.infNormSq_nonneg f
  have hp := μ.p_pos
  have hp2 := μ.p_le_half
  have hx : μ.dist.wvec (μ.diffComm i j * f) x = μ.dist.wvecAt ((μ.dist.condDiff i
      * μ.dist.condDiff j - μ.dist.condDiff j * μ.dist.condDiff i) * f)
        (fpt i j x.1 (x.1 i) (x.1 j)) := by
    rw [fpt_self, μ.dist.wvecAt_coe]
    rfl
  rw [hx]
  by_cases hN : μ.NonProd i j x.1
  · rw [ite_eq_left (μ.interact_of_nonProd hij hN), mul_one]
    obtain ⟨e00, e10, e01⟩ := μ.wvecAt_comm_nonProd hij f x.1 hN
    have hx1 : Avoids μ.forbidden x.1 := (μ.mass_pos_iff _).mp x.2
    have h11 := hN.2.2
    cases ha : x.1 i <;> cases hb : x.1 j
    · rw [e00]
      refine (qNormSq_smul_sub_le _ _ _ _ (hK _) (hK _)).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ hK0
      nlinarith [mul_nonneg (sq_nonneg μ.p) (by nlinarith : (0 : ℝ) ≤ 1 - μ.p ^ 2)]
    · rw [e01]
      refine (qNormSq_smul_sub_le _ _ _ _ (hK _) (hK _)).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ hK0
      nlinarith [mul_nonneg (pow_nonneg hp.le 3) (by linarith : (0 : ℝ) ≤ 2 - μ.p)]
    · rw [e10]
      refine (qNormSq_smul_sub_le _ _ _ _ (hK _) (hK _)).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ hK0
      nlinarith [mul_nonneg (pow_nonneg hp.le 3) (by linarith : (0 : ℝ) ≤ 2 - μ.p)]
    · have e : fpt i j x.1 (x.1 i) (x.1 j) = x.1 := fpt_self _
      rw [ha, hb] at e
      rw [e] at h11
      exact absurd hx1 h11
  · rw [μ.wvecAt_comm_eq_zero hij f _ _ _ hN, qNormSq_zero]
    refine mul_nonneg (mul_nonneg (by positivity) ?_) hK0
    split_ifs <;> norm_num

/-- **Lemma 4.3 (two-coordinate interaction).** For conditioned Bernoulli bits and distinct
coordinates `i`, `j`:

* (4.17) `[Dᵢ,Dⱼ]†[Dᵢ,Dⱼ] ≤ p² Aᵢⱼ`;
* (4.18) `[Dᵢ,Dⱼ]†[Dᵢ,Dⱼ] ≤ p²(1 + p) ((AᵢⱼDᵢ)†(AᵢⱼDᵢ) + (AᵢⱼDⱼ)†(AᵢⱼDⱼ))`;
* (4.19) `DᵢDⱼ + DⱼDᵢ ≥ −p Aᵢⱼ(Dᵢ + Dⱼ)`;
* (4.20) `‖([Dᵢ,Dⱼ]f)ˣ‖² ≤ 4p² Aᵢⱼ(x) ‖f‖∞²` at every support point `x`, for joint vectors on
  every finite workspace.

The operator inequalities give the norm forms of the paper on every workspace by
`jInner_le_of_le` and `jNormSq_mul_le`. -/
theorem lemma_4_3 {i j : ι} (hij : i ≠ j) :
    (μ.diffComm i j)ᴴ * μ.diffComm i j ≤ ((μ.p ^ 2 : ℝ) : ℂ) • μ.interactOp i j ∧
    (μ.diffComm i j)ᴴ * μ.diffComm i j ≤ ((μ.p ^ 2 * (1 + μ.p) : ℝ) : ℂ) •
      ((μ.interactOp i j * μ.dist.condDiff i)ᴴ * (μ.interactOp i j * μ.dist.condDiff i)
        + (μ.interactOp i j * μ.dist.condDiff j)ᴴ * (μ.interactOp i j * μ.dist.condDiff j)) ∧
    -(((μ.p : ℝ) : ℂ) • (μ.interactOp i j * (μ.dist.condDiff i + μ.dist.condDiff j)))
      ≤ μ.dist.condDiff i * μ.dist.condDiff j + μ.dist.condDiff j * μ.dist.condDiff i ∧
    (∀ (A : Type) [Fintype A] (f : JVec μ.dist.Supp A) (x : μ.dist.Supp),
      qNormSq (μ.dist.wvec (μ.diffComm i j * f) x)
        ≤ 4 * μ.p ^ 2 * (if μ.Interact i j x.1 then 1 else 0) * μ.dist.infNormSq f) := by
  exact ⟨μ.diffComm_sq_le_interactOp hij, μ.diffComm_sq_le_interact_condDiff hij,
    μ.anticomm_ge hij, fun _ _ f x => μ.qNormSq_wvec_diffComm_le hij f x⟩

end CondBern

end QuantumQueryComplexity
