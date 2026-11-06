import QuantumQueryComplexity.Quantum.Records.CondExp

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Records of a product distribution

Let `ρ` be a **product distribution with full-support marginals** on strings `ι → σ`
(`FinDist.IsFullProduct`): `ρ(x) = ∏ᵢ μᵢ(xᵢ)` with every `μᵢ(a) > 0`. Then the conditional
averages `Eᵢ` of `Records/CondExp.lean` act on different tensor factors of the input register: in
the square-root weighted coordinates, `Eᵢ` is the projection onto `|√μᵢ⟩` in the factor of
coordinate `i` (`condExp_apply_of_isFullProduct`). So the `Eᵢ` and `Dᵢ = I − Eᵢ` all commute
(`condExp_commute`).

The **record projection** of a set `S` of coordinates is

    P_S = ∏_{i ∈ S} Dᵢ ∏_{i ∉ S} Eᵢ.

It is defined here by its tensor-product formula (`recProj`), whose factor at coordinate `i` is
`I − |√μᵢ⟩⟨√μᵢ|` for `i ∈ S` and `|√μᵢ⟩⟨√μᵢ|` otherwise, and proved equal to the product of the
`Dᵢ` and `Eᵢ` taken in any order (`recProj_eq_prod`). The `P_S` are orthogonal projections,
pairwise orthogonal, and sum to the identity; `P_S` is the joint eigenspace of the `Eᵢ` on which
exactly the coordinates in `S` are "recorded" (`condExp_mul_recProj`, `condDiff_mul_recProj`).
The uniform state `|ρ⟩` has no records (`recProj_mulVec_ket`).

No group structure on `σ` is used. For the uniform distribution on `Z_q` the `P_S` are spanned by
the Fourier characters with support `S`; for Bernoulli bits by tensor products of `|ω_p⟩` and
`|η_p⟩` (`BiasedBudget.lean`).

## Main definitions

* `FinDist.IsFullProduct`, `FinDist.marg`, `FinDist.recProj`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

namespace FinDist

variable (ρ : FinDist (ι → σ))

/-- **A product distribution with full-support marginals**: `ρ(x) = ∏ᵢ μᵢ(xᵢ)` for some positive
weights `μᵢ(a) > 0`. -/
def IsFullProduct : Prop :=
  ∃ μ : ι → σ → ℝ, (∀ i a, 0 < μ i a) ∧ ∀ x, ρ.mass x = ∏ i, μ i (x i)

/-- **The marginal** of coordinate `i`: the probability that `xᵢ = a`. -/
noncomputable def marg (i : ι) (a : σ) : ℝ := ∑ x, if x i = a then ρ.mass x else 0

variable {ρ}

/-- The marginals sum to one. -/
theorem sum_marg (i : ι) : ∑ a, ρ.marg i a = 1 := by
  unfold marg
  rw [Finset.sum_comm]
  simpa using ρ.sum_mass

/-- The marginals are nonnegative. -/
private lemma marg_nonneg (i : ι) (a : σ) : 0 ≤ ρ.marg i a :=
  Finset.sum_nonneg fun x _ => by
    split_ifs
    · exact ρ.mass_nonneg x
    · exact le_rfl

/-- Under a product representation `ρ = ∏ μᵢ`, the normalizers `∑_b μᵢ(b)` multiply to one. -/
private lemma prod_sum_weights {μ : ι → σ → ℝ} (hρ : ∀ x, ρ.mass x = ∏ i, μ i (x i)) :
    ∏ i, ∑ b, μ i b = 1 := by
  rw [Fintype.prod_sum, ← ρ.sum_mass]
  exact Finset.sum_congr rfl fun x _ => (hρ x).symm

/-- Under a product representation `ρ = ∏ μᵢ`, `margᵢ(a) · ∑_b μᵢ(b) = μᵢ(a)`. -/
private lemma marg_mul_sum_weights {μ : ι → σ → ℝ} (hρ : ∀ x, ρ.mass x = ∏ i, μ i (x i))
    (i : ι) (a : σ) : ρ.marg i a * ∑ b, μ i b = μ i a := by
  set g : ι → σ → ℝ := fun k b => if k = i then (if b = a then μ k b else 0) else μ k b with hg
  have h1 : ρ.marg i a = ∏ k, ∑ b, g k b := by
    rw [Fintype.prod_sum, marg]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x i = a
    · rw [ite_eq_left hx, hρ x]
      refine Finset.prod_congr rfl fun k _ => ?_
      by_cases hk : k = i
      · subst hk
        simp [hg, hx]
      · simp [hg, hk]
    · rw [ite_eq_right hx]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hg, hx])).symm
  have h2 : ∀ k, ∑ b, g k b = if k = i then μ i a else ∑ b, μ k b := by
    intro k
    by_cases hk : k = i
    · subst hk
      simp [hg]
    · simp [hg, hk]
  have h3 : ∏ k ∈ ({i}ᶜ : Finset ι), (if k = i then μ i a else ∑ b, μ k b) =
      ∏ k ∈ ({i}ᶜ : Finset ι), ∑ b, μ k b :=
    Finset.prod_congr rfl fun k hk => ite_eq_right (by simpa using hk)
  have h4 := prod_sum_weights hρ
  rw [Fintype.prod_eq_mul_prod_compl i] at h4
  rw [h1, Finset.prod_congr rfl fun k _ => h2 k, Fintype.prod_eq_mul_prod_compl i, h3,
    ite_eq_left rfl]
  linear_combination μ i a * h4

/-- Under `ρ = ∏ μᵢ` with positive weights, `margᵢ(a) = μᵢ(a) / ∑_b μᵢ(b)`. -/
private lemma marg_eq_div {μ : ι → σ → ℝ} (hμ : ∀ i a, 0 < μ i a)
    (hρ : ∀ x, ρ.mass x = ∏ i, μ i (x i)) (i : ι) (a : σ) :
    ρ.marg i a = μ i a / ∑ b, μ i b := by
  have hZ : 0 < ∑ b, μ i b := Finset.sum_pos (fun b _ => hμ i b) ⟨a, Finset.mem_univ a⟩
  rw [eq_div_iff hZ.ne']
  exact marg_mul_sum_weights hρ i a

/-- A product distribution is the product of its marginals. -/
theorem mass_eq_prod_marg (h : ρ.IsFullProduct) (x : ι → σ) :
    ρ.mass x = ∏ i, ρ.marg i (x i) := by
  obtain ⟨μ, hμ, hρ⟩ := h
  rw [Finset.prod_congr rfl fun i _ => marg_eq_div hμ hρ i (x i), Finset.prod_div_distrib,
    prod_sum_weights hρ, div_one, hρ]

/-- The marginals of a full product distribution are positive. -/
theorem marg_pos (h : ρ.IsFullProduct) (i : ι) (a : σ) : 0 < ρ.marg i a := by
  obtain ⟨μ, hμ, hρ⟩ := h
  rw [marg_eq_div hμ hρ i a]
  exact div_pos (hμ i a) (Finset.sum_pos (fun b _ => hμ i b) ⟨a, Finset.mem_univ a⟩)

/-- A full product distribution has full support. -/
theorem mass_pos_of_isFullProduct (h : ρ.IsFullProduct) (x : ι → σ) : 0 < ρ.mass x := by
  obtain ⟨μ, hμ, hρ⟩ := h
  rw [hρ]
  exact Finset.prod_pos fun i _ => hμ i (x i)

/-- The fibre mass of a full product distribution is the product of the other marginals. -/
private lemma fiberMass_eq_of_isFullProduct (h : ρ.IsFullProduct) (i : ι) (x : ι → σ) :
    ρ.fiberMass i x = ∏ k ∈ ({i}ᶜ : Finset ι), ρ.marg k (x k) := by
  set g : ι → σ → ℝ := fun k b =>
    if k = i then ρ.marg k b else (if b = x k then ρ.marg k b else 0) with hg
  have h1 : ρ.fiberMass i x = ∏ k, ∑ b, g k b := by
    rw [Fintype.prod_sum, fiberMass]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hxy : AgreeOff i x y
    · rw [ite_eq_left hxy, mass_eq_prod_marg h]
      refine Finset.prod_congr rfl fun k _ => ?_
      by_cases hk : k = i
      · simp [hg, hk]
      · simp [hg, hk, (hxy k hk).symm]
    · rw [ite_eq_right hxy]
      obtain ⟨j, hj, hne⟩ : ∃ j, j ≠ i ∧ x j ≠ y j := by
        unfold AgreeOff at hxy
        push Not at hxy
        exact hxy
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hg, hj, Ne.symm hne])).symm
  rw [h1, Fintype.prod_eq_mul_prod_compl i]
  have hi : ∑ b, g i b = 1 := by simp [hg, sum_marg]
  rw [hi, one_mul]
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk' : k ≠ i := by simpa using hk
  simp [hg, hk']

/-- **`Eᵢ` acts on the factor of coordinate `i`** as the projection onto `|√μᵢ⟩`. -/
theorem condExp_apply_of_isFullProduct (h : ρ.IsFullProduct) (i : ι) (x y : ρ.Supp) :
    ρ.condExp i x y = if AgreeOff i x.1 y.1 then
      ((Real.sqrt (ρ.marg i (x.1 i) * ρ.marg i (y.1 i)) : ℝ) : ℂ) else 0 := by
  unfold condExp
  by_cases hxy : AgreeOff i x.1 y.1
  · rw [ite_eq_left hxy, ite_eq_left hxy]
    congr 1
    set R := ∏ k ∈ ({i}ᶜ : Finset ι), ρ.marg k (x.1 k) with hR
    have hRpos : 0 < R := Finset.prod_pos fun k _ => marg_pos h k _
    have hx : ρ.mass x = ρ.marg i (x.1 i) * R := by
      rw [mass_eq_prod_marg h, Fintype.prod_eq_mul_prod_compl i]
    have hy : ρ.mass y = ρ.marg i (y.1 i) * R := by
      rw [mass_eq_prod_marg h, Fintype.prod_eq_mul_prod_compl i, hR]
      congr 1
      refine Finset.prod_congr rfl fun k hk => ?_
      rw [hxy k (by simpa using hk)]
    rw [fiberMass_eq_of_isFullProduct h, ← hR, hx, hy,
      show ρ.marg i (x.1 i) * R * (ρ.marg i (y.1 i) * R) =
        (ρ.marg i (x.1 i) * ρ.marg i (y.1 i)) * (R * R) by ring,
      Real.sqrt_mul (mul_nonneg (marg_nonneg _ _) (marg_nonneg _ _)),
      Real.sqrt_mul_self hRpos.le]
    field_simp
  · rw [ite_eq_right hxy, ite_eq_right hxy]

/-! ### Tensor-product matrices on strings -/

variable (ρ) in
/-- The one-coordinate projection `|√margᵢ⟩⟨√margᵢ|` on `σ`. -/
private noncomputable def margProj (i : ι) : Matrix σ σ ℂ :=
  Matrix.of fun a b => ((Real.sqrt (ρ.marg i a * ρ.marg i b) : ℝ) : ℂ)

variable (ρ) in
/-- The unit vector `|√margᵢ⟩` on `σ`. -/
private noncomputable def sqrtMarg (i : ι) : σ → ℂ := fun a => ((Real.sqrt (ρ.marg i a) : ℝ) : ℂ)

/-- The entries of `|√margᵢ⟩⟨√margᵢ|` with the square root split. -/
private lemma margProj_apply (i : ι) (a b : σ) :
    margProj ρ i a b = sqrtMarg ρ i a * sqrtMarg ρ i b := by
  rw [margProj, Matrix.of_apply, Real.sqrt_mul (marg_nonneg _ _), Complex.ofReal_mul, sqrtMarg,
    sqrtMarg]

/-- `|√margᵢ⟩` is a unit vector. -/
private lemma sum_sqrtMarg_mul_self (i : ι) : ∑ c, sqrtMarg ρ i c * sqrtMarg ρ i c = 1 := by
  simp_rw [sqrtMarg, ← Complex.ofReal_mul, Real.mul_self_sqrt (marg_nonneg _ _)]
  rw [← Complex.ofReal_sum, sum_marg, Complex.ofReal_one]

/-- `|√margᵢ⟩⟨√margᵢ|` fixes `|√margᵢ⟩`. -/
private lemma margProj_mulVec (i : ι) : margProj ρ i *ᵥ sqrtMarg ρ i = sqrtMarg ρ i := by
  funext a
  simp only [Matrix.mulVec, dotProduct, margProj_apply]
  calc ∑ c, sqrtMarg ρ i a * sqrtMarg ρ i c * sqrtMarg ρ i c
      = sqrtMarg ρ i a * ∑ c, sqrtMarg ρ i c * sqrtMarg ρ i c := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
    _ = sqrtMarg ρ i a := by rw [sum_sqrtMarg_mul_self, mul_one]

/-- `|√margᵢ⟩⟨√margᵢ|` is idempotent. -/
private lemma margProj_mul_self (i : ι) : margProj ρ i * margProj ρ i = margProj ρ i := by
  ext a b
  simp only [Matrix.mul_apply, margProj_apply]
  calc ∑ c, sqrtMarg ρ i a * sqrtMarg ρ i c * (sqrtMarg ρ i c * sqrtMarg ρ i b)
      = sqrtMarg ρ i a * sqrtMarg ρ i b * ∑ c, sqrtMarg ρ i c * sqrtMarg ρ i c := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
    _ = sqrtMarg ρ i a * sqrtMarg ρ i b := by rw [sum_sqrtMarg_mul_self, mul_one]

/-- `Πᵢ (I − Πᵢ) = 0`. -/
private lemma margProj_mul_one_sub (i : ι) : margProj ρ i * (1 - margProj ρ i) = 0 := by
  rw [mul_sub, mul_one, margProj_mul_self, sub_self]

/-- `(I − Πᵢ) Πᵢ = 0`. -/
private lemma one_sub_mul_margProj (i : ι) : (1 - margProj ρ i) * margProj ρ i = 0 := by
  rw [sub_mul, one_mul, margProj_mul_self, sub_self]

/-- `(I − Πᵢ)² = I − Πᵢ`. -/
private lemma one_sub_margProj_mul_self (i : ι) :
    (1 - margProj ρ i) * (1 - margProj ρ i) = 1 - margProj ρ i := by
  rw [sub_mul, one_mul, margProj_mul_one_sub, sub_zero]

variable (ρ) in
/-- The tensor-product matrix on `ρ.Supp` with factor `F k` at coordinate `k`. -/
private noncomputable def tens (F : ι → Matrix σ σ ℂ) : Matrix ρ.Supp ρ.Supp ℂ :=
  fun x y => ∏ k, F k (x.1 k) (y.1 k)

/-- Under full support, a sum over `ρ.Supp` is a sum over all strings. -/
private lemma sum_supp_eq_univ (hfull : ∀ x, 0 < ρ.mass x) {M : Type*} [AddCommMonoid M]
    (g : (ι → σ) → M) : ∑ z : ρ.Supp, g z.1 = ∑ z, g z :=
  (Finset.sum_subtype Finset.univ (fun z => by simp [hfull z]) g).symm

/-- Under full support, tensor-product matrices multiply factorwise. -/
private lemma tens_mul (hfull : ∀ x, 0 < ρ.mass x) (F G : ι → Matrix σ σ ℂ) :
    tens ρ F * tens ρ G = tens ρ (fun k => F k * G k) := by
  ext x y
  change ∑ z : ρ.Supp, (∏ k, F k (x.1 k) (z.1 k)) * (∏ k, G k (z.1 k) (y.1 k)) =
    ∏ k, (F k * G k) (x.1 k) (y.1 k)
  rw [sum_supp_eq_univ hfull (fun z => (∏ k, F k (x.1 k) (z k)) * ∏ k, G k (z k) (y.1 k))]
  simp_rw [← Finset.prod_mul_distrib, Matrix.mul_apply]
  rw [Fintype.prod_sum]

/-- The identity is the tensor product of identities. -/
private lemma tens_one : tens ρ (fun _ => (1 : Matrix σ σ ℂ)) = 1 := by
  ext x y
  simp only [tens, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    simp
  · rw [ite_eq_right hxy]
    obtain ⟨k, hk⟩ : ∃ k, x.1 k ≠ y.1 k := by
      by_contra hc
      push Not at hc
      exact hxy (Subtype.ext (funext hc))
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])

/-- A tensor-product matrix with a zero factor vanishes. -/
private lemma tens_eq_zero {F : ι → Matrix σ σ ℂ} (k : ι) (hk : F k = 0) : tens ρ F = 0 := by
  ext x y
  simp only [tens, Matrix.zero_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])

/-- Tensor-product matrices are linear in the factor at a single coordinate. -/
private lemma tens_ite_sub (i : ι) (A B C : Matrix σ σ ℂ) :
    tens ρ (fun k => if k = i then A - B else C) =
      tens ρ (fun k => if k = i then A else C) - tens ρ (fun k => if k = i then B else C) := by
  ext x y
  simp only [tens, Matrix.sub_apply]
  have hc : ∀ M : Matrix σ σ ℂ, ∏ k ∈ ({i}ᶜ : Finset ι), (if k = i then M else C) (x.1 k) (y.1 k)
      = ∏ k ∈ ({i}ᶜ : Finset ι), C (x.1 k) (y.1 k) := fun M =>
    Finset.prod_congr rfl fun k hk => by rw [ite_eq_right (by simpa using hk)]
  rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i,
    Fintype.prod_eq_mul_prod_compl i, hc, hc, hc, ite_eq_left rfl, ite_eq_left rfl,
    ite_eq_left rfl, Matrix.sub_apply, sub_mul]

/-- Under full support, tensor-product matrices with commuting factors commute. -/
private lemma tens_commute (hfull : ∀ x, 0 < ρ.mass x) {F G : ι → Matrix σ σ ℂ}
    (hFG : ∀ k, Commute (F k) (G k)) : Commute (tens ρ F) (tens ρ G) := by
  unfold Commute SemiconjBy
  rw [tens_mul hfull, tens_mul hfull]
  congr 1
  funext k
  exact (hFG k).eq

/-- For a full product distribution, `Eᵢ` is the tensor product of `Πᵢ` at `i` and `I` elsewhere. -/
private lemma condExp_eq_tens (h : ρ.IsFullProduct) (i : ι) :
    ρ.condExp i = tens ρ (fun k => if k = i then margProj ρ i else 1) := by
  ext x y
  rw [condExp_apply_of_isFullProduct h]
  simp only [tens]
  rw [Fintype.prod_eq_mul_prod_compl i, ite_eq_left rfl]
  by_cases hxy : AgreeOff i x.1 y.1
  · rw [ite_eq_left hxy, Finset.prod_eq_one fun k hk => ?_, mul_one]
    · rfl
    · have hk' : k ≠ i := by simpa using hk
      rw [ite_eq_right hk', Matrix.one_apply, ite_eq_left (hxy k hk')]
  · rw [ite_eq_right hxy]
    obtain ⟨j, hj, hne⟩ : ∃ j, j ≠ i ∧ x.1 j ≠ y.1 j := by
      unfold AgreeOff at hxy
      push Not at hxy
      exact hxy
    rw [Finset.prod_eq_zero (i := j) (by simpa using hj) (by simp [hj, hne]), mul_zero]

/-- For a full product, `Dᵢ` is the tensor product of `I − Πᵢ` at `i` and `I` elsewhere. -/
private lemma condDiff_eq_tens (h : ρ.IsFullProduct) (i : ι) :
    ρ.condDiff i = tens ρ (fun k => if k = i then 1 - margProj ρ i else 1) := by
  have e : tens ρ (fun k => if k = i then (1 : Matrix σ σ ℂ) else 1) = 1 := by
    simp only [ite_self]
    exact tens_one
  rw [tens_ite_sub, e, condDiff, condExp_eq_tens h]

/-- **The conditional averages of a product distribution commute.** -/
theorem condExp_commute (h : ρ.IsFullProduct) (i j : ι) :
    Commute (ρ.condExp i) (ρ.condExp j) := by
  rw [condExp_eq_tens h, condExp_eq_tens h]
  refine tens_commute (mass_pos_of_isFullProduct h) fun k => ?_
  split_ifs with hi hj hj
  · subst hi hj
    exact Commute.refl _
  · exact Commute.one_right _
  · exact Commute.one_left _
  · exact Commute.one_left _

theorem condDiff_commute (h : ρ.IsFullProduct) (i j : ι) :
    Commute (ρ.condDiff i) (ρ.condDiff j) := by
  rw [condDiff_eq_tens h, condDiff_eq_tens h]
  refine tens_commute (mass_pos_of_isFullProduct h) fun k => ?_
  split_ifs with hi hj hj
  · subst hi hj
    exact Commute.refl _
  · exact Commute.one_right _
  · exact Commute.one_left _
  · exact Commute.one_left _

theorem condExp_condDiff_commute (h : ρ.IsFullProduct) (i j : ι) :
    Commute (ρ.condExp i) (ρ.condDiff j) := by
  rw [condExp_eq_tens h, condDiff_eq_tens h]
  refine tens_commute (mass_pos_of_isFullProduct h) fun k => ?_
  split_ifs with hi hj hj
  · subst hi hj
    exact (Commute.one_right _).sub_right (Commute.refl _)
  · exact Commute.one_right _
  · exact Commute.one_left _
  · exact Commute.one_left _

/-! ## Record projections -/

variable (ρ)

/-- The factor of `P_S` at coordinate `i`: `I − |√μᵢ⟩⟨√μᵢ|` if `i ∈ S`, `|√μᵢ⟩⟨√μᵢ|` otherwise. -/
noncomputable def recFactor (S : Finset ι) (i : ι) (a b : σ) : ℂ :=
  if i ∈ S then (if a = b then 1 else 0) - ((Real.sqrt (ρ.marg i a * ρ.marg i b) : ℝ) : ℂ)
  else ((Real.sqrt (ρ.marg i a * ρ.marg i b) : ℝ) : ℂ)

/-- **The record projection** `P_S`, by its tensor-product formula. -/
noncomputable def recProj (S : Finset ι) : Matrix ρ.Supp ρ.Supp ℂ := fun x y =>
  ∏ i, ρ.recFactor S i (x.1 i) (y.1 i)

variable {ρ}

variable (ρ) in
/-- The factor of `P_S` at coordinate `k`, as a matrix on `σ`. -/
private noncomputable def recMat (S : Finset ι) (k : ι) : Matrix σ σ ℂ :=
  if k ∈ S then 1 - margProj ρ k else margProj ρ k

/-- `P_S` is the tensor product of the factors `recMat ρ S k`. -/
private lemma recProj_eq_tens (S : Finset ι) : ρ.recProj S = tens ρ (recMat ρ S) := by
  ext x y
  simp only [recProj, tens]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : k ∈ S <;> simp [recFactor, recMat, hk, margProj, Matrix.one_apply]

/-- Each factor of `P_S` is idempotent. -/
private lemma recMat_mul_self (S : Finset ι) (k : ι) :
    recMat ρ S k * recMat ρ S k = recMat ρ S k := by
  unfold recMat
  split_ifs
  · exact one_sub_margProj_mul_self k
  · exact margProj_mul_self k

/-- **`P_S = ∏_{i ∈ S} Dᵢ ∏_{i ∉ S} Eᵢ`**, the product taken along any enumeration of the
coordinates. -/
theorem recProj_eq_prod (h : ρ.IsFullProduct) (S : Finset ι) (l : List ι) (hl : l.Nodup)
    (hall : ∀ i, i ∈ l) :
    ρ.recProj S = (l.map fun i => if i ∈ S then ρ.condDiff i else ρ.condExp i).prod := by
  have hfull := mass_pos_of_isFullProduct h
  have key : ∀ l : List ι, l.Nodup →
      (l.map fun i => if i ∈ S then ρ.condDiff i else ρ.condExp i).prod =
        tens ρ (fun k => if k ∈ l then recMat ρ S k else 1) := by
    intro l hl
    induction l with
    | nil => simp [tens_one]
    | cons a l ih =>
      rw [List.map_cons, List.prod_cons, ih hl.of_cons]
      have ha : (if a ∈ S then ρ.condDiff a else ρ.condExp a) =
          tens ρ (fun k => if k = a then recMat ρ S a else 1) := by
        by_cases haS : a ∈ S
        · rw [ite_eq_left haS, condDiff_eq_tens h]
          simp [recMat, haS]
        · rw [ite_eq_right haS, condExp_eq_tens h]
          simp [recMat, haS]
      rw [ha, tens_mul hfull]
      congr 1
      funext k
      have hal : a ∉ l := (List.nodup_cons.mp hl).1
      by_cases hka : k = a
      · subst hka
        simp [hal]
      · simp [hka]
  rw [key l hl, recProj_eq_tens]
  congr 1
  funext k
  simp [hall k]

theorem recProj_isHermitian (S : Finset ι) : (ρ.recProj S).IsHermitian := by
  refine Matrix.IsHermitian.ext fun x y => ?_
  simp only [recProj]
  rw [star_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hxy : x.1 k = y.1 k
  · by_cases hk : k ∈ S <;> simp [recFactor, hk, hxy]
  · by_cases hk : k ∈ S <;> simp [recFactor, hk, hxy, Ne.symm hxy, mul_comm]

theorem recProj_mul_self (h : ρ.IsFullProduct) (S : Finset ι) :
    ρ.recProj S * ρ.recProj S = ρ.recProj S := by
  rw [recProj_eq_tens, tens_mul (mass_pos_of_isFullProduct h)]
  congr 1
  funext k
  exact recMat_mul_self S k

/-- Different record projections are orthogonal. -/
theorem recProj_mul_recProj (h : ρ.IsFullProduct) {S T : Finset ι} (hST : S ≠ T) :
    ρ.recProj S * ρ.recProj T = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, ¬ (k ∈ S ↔ k ∈ T) := by
    by_contra hc
    push Not at hc
    exact hST (Finset.ext hc)
  rw [recProj_eq_tens, recProj_eq_tens, tens_mul (mass_pos_of_isFullProduct h)]
  refine tens_eq_zero k ?_
  by_cases hS : k ∈ S
  · have hT : k ∉ T := fun hT => hk ⟨fun _ => hT, fun _ => hS⟩
    simp [recMat, hS, hT, one_sub_mul_margProj]
  · have hT : k ∈ T := by
      by_contra hT
      exact hk ⟨fun h => absurd h hS, fun h => absurd h hT⟩
    simp [recMat, hS, hT, margProj_mul_one_sub]

/-- `∑_S ∏ₖ (if k ∈ S then aₖ else bₖ) = ∏ₖ (aₖ + bₖ)`. -/
private lemma sum_prod_ite_mem (a b : ι → ℂ) :
    ∑ S : Finset ι, ∏ k, (if k ∈ S then a k else b k) = ∏ k, (a k + b k) := by
  rw [Fintype.prod_add]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_ite]
  congr 2
  · ext k
    simp
  · ext k
    simp

/-- **The record projections sum to the identity.** -/
theorem sum_recProj (h : ρ.IsFullProduct) : ∑ S : Finset ι, ρ.recProj S = 1 := by
  -- The identity holds entrywise for every distribution; `h` is not needed.
  have _ := h
  ext x y
  rw [Matrix.sum_apply, ← tens_one (ρ := ρ)]
  simp only [recProj, recFactor, tens]
  rw [sum_prod_ite_mem]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [sub_add_cancel, Matrix.one_apply]

/-- `Eᵢ` kills the records containing `i` and fixes the others. -/
theorem condExp_mul_recProj (h : ρ.IsFullProduct) (i : ι) (S : Finset ι) :
    ρ.condExp i * ρ.recProj S = if i ∈ S then 0 else ρ.recProj S := by
  rw [condExp_eq_tens h, recProj_eq_tens, tens_mul (mass_pos_of_isFullProduct h)]
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi]
    exact tens_eq_zero i (by simp [recMat, hi, margProj_mul_one_sub])
  · rw [ite_eq_right hi]
    congr 1
    funext k
    by_cases hk : k = i
    · subst hk
      simp [recMat, hi, margProj_mul_self]
    · simp [hk]

/-- `Dᵢ` fixes the records containing `i` and kills the others. -/
theorem condDiff_mul_recProj (h : ρ.IsFullProduct) (i : ι) (S : Finset ι) :
    ρ.condDiff i * ρ.recProj S = if i ∈ S then ρ.recProj S else 0 := by
  rw [condDiff_eq_tens h, recProj_eq_tens, tens_mul (mass_pos_of_isFullProduct h)]
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi]
    congr 1
    funext k
    by_cases hk : k = i
    · subst hk
      simp [recMat, hi, one_sub_margProj_mul_self]
    · simp [hk]
  · rw [ite_eq_right hi]
    exact tens_eq_zero i (by simp [recMat, hi, one_sub_mul_margProj])

/-- For a full product distribution, `|ρ⟩` is the tensor product of the `|√margₖ⟩`. -/
private lemma ket_eq_prod (h : ρ.IsFullProduct) :
    ρ.ket = fun x : ρ.Supp => ∏ k, sqrtMarg ρ k (x.1 k) := by
  funext x
  rw [ket, mass_eq_prod_marg h, Real.sqrt_prod _ fun k _ => marg_nonneg _ _, Complex.ofReal_prod]
  rfl

/-- Under full support, a tensor-product matrix maps a tensor-product vector factorwise. -/
private lemma tens_mulVec_prod (hfull : ∀ x, 0 < ρ.mass x) (F : ι → Matrix σ σ ℂ)
    (v : ι → σ → ℂ) :
    tens ρ F *ᵥ (fun x : ρ.Supp => ∏ k, v k (x.1 k)) =
      fun x => ∏ k, (F k *ᵥ v k) (x.1 k) := by
  funext x
  change ∑ z : ρ.Supp, (∏ k, F k (x.1 k) (z.1 k)) * (∏ k, v k (z.1 k)) =
    ∏ k, (F k *ᵥ v k) (x.1 k)
  rw [sum_supp_eq_univ hfull (fun z => (∏ k, F k (x.1 k) (z k)) * ∏ k, v k (z k))]
  simp_rw [← Finset.prod_mul_distrib, Matrix.mulVec, dotProduct]
  rw [Fintype.prod_sum]

/-- **The uniform state has no records**: `P_∅|ρ⟩ = |ρ⟩` and `P_S|ρ⟩ = 0` for `S ≠ ∅`. -/
theorem recProj_mulVec_ket (h : ρ.IsFullProduct) (S : Finset ι) :
    ρ.recProj S *ᵥ ρ.ket = if S = ∅ then ρ.ket else 0 := by
  rw [recProj_eq_tens, ket_eq_prod h, tens_mulVec_prod (mass_pos_of_isFullProduct h)]
  by_cases hS : S = ∅
  · rw [ite_eq_left hS]
    subst hS
    funext x
    simp [recMat, margProj_mulVec]
  · rw [ite_eq_right hS]
    obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    funext x
    refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
    simp [recMat, hk, Matrix.sub_mulVec, margProj_mulVec]

end FinDist

end QuantumQueryComplexity
