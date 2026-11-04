import QuantumQueryComplexity.Quantum.Records.Resolvent

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Summing projections: Lemma 4.4

Let `Π₁, …, Π_ℓ` be orthogonal projections on a finite-dimensional space and `L = ∑ₖ Πₖ`.  If
the projections commuted, a common eigendecomposition would give
`∑ₖ ⟨Πₖ f, F Πₖ f⟩ ≤ R‖f‖²` for `F = (I + L/R)⁻¹`, independently of `ℓ`: a component counted by
`k` projections appears in `k` summands but is damped by `R/(R + k)`.  Lemma 4.4 of
Cornelissen–Gilani–Zhou keeps this bound, up to the constant `2 + κ²/γ²`, when the projections do
not commute, assuming every positive eigenvalue of `L` is at least `γ` (`L² ≥ γL`) and the
commutators are controlled by `L`.

The statement is for matrices over an arbitrary finite index type; joint-vector forms on every
workspace follow from `jInner_le_of_le`.

## Main results

* `commute_resolvent_of_commute` — a matrix commuting with `H` commutes with `(I + H/R)⁻¹`.
* `lemma_4_4` — Lemma 4.4.
-/

namespace QuantumQueryComplexity

open scoped Matrix MatrixOrder ComplexOrder
open Matrix

variable {n ℓ : Type} [Fintype n] [DecidableEq n] [Fintype ℓ]

/-- A matrix commuting with `H` commutes with the resolvent `(I + H/R)⁻¹`. -/
theorem commute_resolvent_of_commute {R : ℝ} {H P : Matrix n n ℂ} (h : Commute H P) :
    Commute (resolvent R H) P := by
  set G : Matrix n n ℂ := 1 + ((R⁻¹ : ℝ) : ℂ) • H
  have hG : Commute G P := (Commute.one_left P).add_left (h.smul_left _)
  change Commute G⁻¹ P
  by_cases hd : IsUnit G.det
  · unfold Commute SemiconjBy
    calc G⁻¹ * P = G⁻¹ * (P * G) * G⁻¹ := by
          rw [mul_assoc, mul_assoc, mul_nonsing_inv _ hd, mul_one]
      _ = G⁻¹ * (G * P) * G⁻¹ := by rw [hG.eq]
      _ = P * G⁻¹ := by rw [← mul_assoc, nonsing_inv_mul _ hd, one_mul]
  · rw [nonsing_inv_apply_not_isUnit _ hd]
    exact Commute.zero_left P

/-! ### The real quadratic form `x ↦ Re ⟨x, M x⟩` -/

/-- The real quadratic form `Re ⟨x, M x⟩`. -/
private noncomputable def qf (x : n → ℂ) (M : Matrix n n ℂ) : ℝ := (star x ⬝ᵥ (M *ᵥ x)).re

private lemma qf_add (x : n → ℂ) (A B : Matrix n n ℂ) : qf x (A + B) = qf x A + qf x B := by
  simp [qf, add_mulVec, dotProduct_add]

private lemma qf_sub (x : n → ℂ) (A B : Matrix n n ℂ) : qf x (A - B) = qf x A - qf x B := by
  simp [qf, sub_mulVec, dotProduct_sub]

private lemma qf_smul (x : n → ℂ) (r : ℝ) (A : Matrix n n ℂ) :
    qf x ((r : ℂ) • A) = r * qf x A := by
  simp [qf, smul_mulVec, dotProduct_smul]

private lemma qf_sum (x : n → ℂ) (A : ℓ → Matrix n n ℂ) : qf x (∑ k, A k) = ∑ k, qf x (A k) := by
  simp [qf, sum_mulVec, dotProduct_sum]

private lemma qf_nonneg {M : Matrix n n ℂ} (hM : M.PosSemidef) (x : n → ℂ) : 0 ≤ qf x M :=
  (Complex.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg x)).1

private lemma qf_mono {A B : Matrix n n ℂ} (h : A ≤ B) (x : n → ℂ) : qf x A ≤ qf x B := by
  have := qf_nonneg (le_iff.mp h) x
  rw [qf_sub] at this
  linarith

/-- `Re ⟨x, Aᴴ B x⟩ = Re ⟨A x, B x⟩`. -/
private lemma qf_conjTranspose_mul (x : n → ℂ) (A B : Matrix n n ℂ) :
    qf x (Aᴴ * B) = (star (A *ᵥ x) ⬝ᵥ (B *ᵥ x)).re := by
  simp only [qf, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]

/-- `Re ⟨x, Bᴴ M B x⟩ = Re ⟨B x, M (B x)⟩`. -/
private lemma qf_conj (x : n → ℂ) (B M : Matrix n n ℂ) :
    qf x (Bᴴ * M * B) = qf (B *ᵥ x) M := by
  simp only [qf, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]

/-- Cauchy–Schwarz in the form `2a Re ⟨v, w⟩ ≤ a² ‖v‖² + ‖w‖²`. -/
private lemma two_mul_re_le (a : ℝ) (v w : n → ℂ) :
    2 * a * (star v ⬝ᵥ w).re ≤ a ^ 2 * (star v ⬝ᵥ v).re + (star w ⬝ᵥ w).re := by
  have h := (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg ((a : ℂ) • v - w))).1
  have hc : (star w ⬝ᵥ v).re = (star v ⬝ᵥ w).re := by
    rw [star_dotProduct w v, Complex.star_def, Complex.conj_re]
  simp only [star_sub, star_smul, Complex.star_def, Complex.conj_ofReal, dotProduct_sub,
    sub_dotProduct, dotProduct_smul, smul_dotProduct, Complex.sub_re] at h
  simp only [smul_eq_mul, Complex.sub_re, Complex.re_ofReal_mul] at h
  rw [hc] at h
  linarith

/-! ### Kernel and range of a Hermitian matrix -/

/-- For Hermitian `L` with `L a = 0`, `⟨a, L c⟩ = 0`. -/
private lemma star_dotProduct_mulVec_eq_zero {L : Matrix n n ℂ} (hL : L.IsHermitian)
    {a : n → ℂ} (ha : L *ᵥ a = 0) (c : n → ℂ) : star a ⬝ᵥ (L *ᵥ c) = 0 := by
  have h := hL.star_dotProduct_mulVec_comm a c
  rw [ha, dotProduct_zero] at h
  exact star_eq_zero.mp h

/-- A vector orthogonal to the kernel of a Hermitian matrix lies in its range. -/
private lemma exists_mulVec_eq {L : Matrix n n ℂ} (hL : L.IsHermitian) {u : n → ℂ}
    (hu : ∀ v, L *ᵥ v = 0 → star v ⬝ᵥ u = 0) : ∃ z, L *ᵥ z = u := by
  set K := LinearMap.ker L.mulVecLin
  set Rg := LinearMap.range L.mulVecLin
  have hinf : K ⊓ Rg = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨hxK, c, rfl⟩
    have hx : L *ᵥ (L *ᵥ c) = 0 := hxK
    exact dotProduct_star_self_eq_zero.mp (star_dotProduct_mulVec_eq_zero hL hx c)
  have htop : K ⊔ Rg = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq K Rg
    have h2 : Module.finrank ℂ Rg + Module.finrank ℂ K = Module.finrank ℂ (n → ℂ) :=
      LinearMap.finrank_range_add_finrank_ker L.mulVecLin
    rw [hinf, finrank_bot] at h1
    omega
  have hmem : u ∈ K ⊔ Rg := htop ▸ Submodule.mem_top
  obtain ⟨y, hy, z, ⟨c, rfl⟩, hyz⟩ := Submodule.mem_sup.mp hmem
  have hy' : L *ᵥ y = 0 := hy
  have hc : L.mulVecLin c = L *ᵥ c := rfl
  rw [hc] at hyz
  have hy0 : y = 0 := by
    apply dotProduct_star_self_eq_zero.mp
    have e : y = u - L *ᵥ c := by rw [← hyz]; abel
    calc star y ⬝ᵥ y = star y ⬝ᵥ u - star y ⬝ᵥ (L *ᵥ c) := by
          rw [← dotProduct_sub, ← e]
      _ = 0 := by rw [hu y hy', star_dotProduct_mulVec_eq_zero hL hy' c, sub_zero]
  exact ⟨c, by rw [← hyz, hy0, zero_add]⟩

/-! ### The scalar part of the argument -/

/-- The final scalar estimate of Lemma 4.4: with `Tₖ = ⟨Pₖ f, F Pₖ f⟩`, `Wₖ = ‖F Pₖ f‖²`,
`Sₖ = Re ⟨F Pₖ f, [Pₖ, L] F f⟩`, `Vₖ = ‖[Pₖ, L] F f‖²`, `Gₖ = Re ⟨f, Pₖ F f⟩`, `N = ‖f‖²` and
`Φ = ⟨F f, L F f⟩`. -/
private lemma sum_le_of_bounds (T W S V G : ℓ → ℝ) {R γ κ a N Φ : ℝ} (hR : 0 < R) (hγ : 0 < γ)
    (ha : a = R + γ) (hN : 0 ≤ N)
    (hb : ∀ k, R * T k = R * G k + S k) (hc : ∀ k, a * W k ≤ R * T k)
    (hd : ∀ k, 2 * a * S k ≤ a ^ 2 * W k + V k) (he : ∑ k, V k ≤ κ ^ 2 * Φ)
    (hf : a * Φ ≤ R ^ 2 * N) (hg : ∑ k, G k ≤ R * N) :
    ∑ k, T k ≤ (2 + κ ^ 2 / γ ^ 2) * R * N := by
  have ha0 : 0 < a := by rw [ha]; exact add_pos hR hγ
  have hb' : R * ∑ k, T k = R * ∑ k, G k + ∑ k, S k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => hb k
  have hc' : a * ∑ k, W k ≤ R * ∑ k, T k := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hc k
  have hd' : 2 * a * ∑ k, S k ≤ a ^ 2 * ∑ k, W k + ∑ k, V k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => hd k
  generalize ∑ k, T k = sT at hb' hc' ⊢
  generalize ∑ k, W k = sW at hc' hd'
  generalize ∑ k, S k = sS at hb' hd'
  generalize ∑ k, V k = sV at hd' he
  generalize ∑ k, G k = sG at hb' hg
  have h1a : a * (a * sW) ≤ a * (R * sT) := mul_le_mul_of_nonneg_left hc' ha0.le
  have h1 : 2 * a * sS ≤ a * R * sT + κ ^ 2 * Φ := by linarith
  have h2 : κ ^ 2 * (a * Φ) ≤ κ ^ 2 * (R ^ 2 * N) := mul_le_mul_of_nonneg_left hf (sq_nonneg κ)
  have h3 : a * (2 * a * sS) ≤ a * (a * R * sT + κ ^ 2 * Φ) := mul_le_mul_of_nonneg_left h1 ha0.le
  have h4 : a ^ 2 * (R * sG) ≤ a ^ 2 * (R * (R * N)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg hR.le) (sq_nonneg a)
  have h5 : a ^ 2 * (R * sT) = a ^ 2 * (R * sG + sS) := by rw [hb']
  have h6 : R * (a ^ 2 * sT) ≤ R * (2 * a ^ 2 * R * N + κ ^ 2 * R * N) := by nlinarith
  have h7 : a ^ 2 * sT ≤ 2 * a ^ 2 * R * N + κ ^ 2 * R * N := le_of_mul_le_mul_left h6 hR
  have hRN : 0 ≤ κ ^ 2 * R * N := mul_nonneg (mul_nonneg (sq_nonneg κ) hR.le) hN
  have h8 : sT ≤ 2 * R * N + κ ^ 2 * R * N / a ^ 2 := by
    rw [← sub_nonneg]
    have : 2 * R * N + κ ^ 2 * R * N / a ^ 2 - sT
        = (2 * a ^ 2 * R * N + κ ^ 2 * R * N - a ^ 2 * sT) / a ^ 2 := by
      field_simp
    rw [this]
    exact div_nonneg (by linarith) (sq_nonneg a)
  have h9 : κ ^ 2 * R * N / a ^ 2 ≤ κ ^ 2 * R * N / γ ^ 2 :=
    div_le_div_of_nonneg_left hRN (pow_pos hγ 2)
      (pow_le_pow_left₀ hγ.le (by rw [ha]; linarith) 2)
  calc sT ≤ 2 * R * N + κ ^ 2 * R * N / γ ^ 2 := by linarith
    _ = (2 + κ ^ 2 / γ ^ 2) * R * N := by ring

/-- **Lemma 4.4 (summing projections).** Let `Pₖ` (`k : ℓ`) be orthogonal projections,
`L = ∑ₖ Pₖ`, `γ > 0`, `R > 0`, and suppose

* `L² ≥ γ L`, and
* `∑ₖ [Pₖ, L]†[Pₖ, L] ≤ κ² L`, that is, `∑ₖ ‖[Pₖ, L] g‖² ≤ κ² ⟨g, L g⟩` for every `g`.

Then, with `F = (I + L/R)⁻¹`, `∑ₖ Pₖ F Pₖ ≤ (2 + κ²/γ²) R I`, that is,
`∑ₖ ⟨Pₖ f, F Pₖ f⟩ ≤ (2 + κ²/γ²) R ‖f‖²` for every `f`. -/
theorem lemma_4_4 (P : ℓ → Matrix n n ℂ) (hPh : ∀ k, (P k).IsHermitian)
    (hPi : ∀ k, P k * P k = P k) {γ κ R : ℝ} (hγ : 0 < γ) (hR : 0 < R)
    (hL : ((γ : ℝ) : ℂ) • (∑ k, P k) ≤ (∑ k, P k) * (∑ k, P k))
    (hcomm : ∑ k, (P k * (∑ k', P k') - (∑ k', P k') * P k)ᴴ
        * (P k * (∑ k', P k') - (∑ k', P k') * P k) ≤ ((κ ^ 2 : ℝ) : ℂ) • (∑ k, P k)) :
    ∑ k, P k * resolvent R (∑ k', P k') * P k
      ≤ (((2 + κ ^ 2 / γ ^ 2) * R : ℝ) : ℂ) • (1 : Matrix n n ℂ) := by
  set L : Matrix n n ℂ := ∑ k, P k with hLdef
  set F := resolvent R L with hFdef
  set C : ℓ → Matrix n n ℂ := fun k => P k * L - L * P k with hCdef
  set a : ℝ := R + γ with hadef
  have ha : 0 < a := add_pos hR hγ
  -- basic facts
  have hPpsd : ∀ k, (P k).PosSemidef := fun k => by
    have h := posSemidef_conjTranspose_mul_self (P k)
    rwa [(hPh k).eq, hPi k] at h
  have hLpsd : L.PosSemidef := posSemidef_sum Finset.univ fun k _ => hPpsd k
  have hLh : Lᴴ = L := hLpsd.isHermitian.eq
  have hFh : Fᴴ = F := resolvent_isHermitian hR hLpsd
  have hFpsd : F.PosSemidef := (resolvent_posDef hR hLpsd).posSemidef
  have hLF : L * F = F * L := (commute_resolvent hR hLpsd).eq
  have hLF' : L * F = (R : ℂ) • (1 - F) := mul_resolvent hR hLpsd
  -- (4.23) with (4.9): `Pₖ F Pₖ = Pₖ F + R⁻¹ (F Pₖ)† [Pₖ, L] F`
  have hF1 : ∀ k, P k * F * P k
      = P k * F + ((R⁻¹ : ℝ) : ℂ) • ((F * P k)ᴴ * (C k * F)) := by
    intro k
    have hc := commutator_resolvent hR hLpsd (P k)
    rw [← hFdef] at hc
    have e1 : P k * F * P k = P k * F - P k * (P k * F - F * P k) := by
      rw [mul_sub, ← mul_assoc, hPi k, ← mul_assoc]; abel
    have e2 : P k * F * (C k * F) = -(P k * (F * (L * P k - P k * L) * F)) := by
      simp only [hCdef]; noncomm_ring
    rw [e1, hc, conjTranspose_mul, hFh, (hPh k).eq, e2, mul_smul_comm, smul_neg, sub_eq_add_neg]
  -- `F (L − γ) F = R F − (R + γ) F²`
  have hFLF : F * L * F = (R : ℂ) • (F - F * F) := by
    rw [mul_assoc, hLF', mul_smul_comm, mul_sub, mul_one]
  have hF2 : F * (L - (γ : ℂ) • 1) * F = (R : ℂ) • F - (a : ℂ) • (F * F) := by
    rw [mul_sub, sub_mul, hFLF, mul_smul_comm, mul_one, smul_mul_assoc, hadef]
    push_cast
    module
  -- `R² − (R + γ) F L F = F (R² + R L + (L² − γ L)) F`
  have hF3 : ((R ^ 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ) - (a : ℂ) • (F * L * F)
      = Fᴴ * (((R ^ 2 : ℝ) : ℂ) • 1 + (R : ℂ) • L + (L * L - (γ : ℂ) • L)) * F := by
    have hFLLF : F * (L * L) * F = ((R : ℂ) • (1 - F)) * ((R : ℂ) • (1 - F)) := by
      rw [mul_assoc, mul_assoc, ← mul_assoc F L, ← hLF, hLF']
    have expand : Fᴴ * (((R ^ 2 : ℝ) : ℂ) • 1 + (R : ℂ) • L + (L * L - (γ : ℂ) • L)) * F
        = ((R ^ 2 : ℝ) : ℂ) • (F * F) + (R : ℂ) • (F * L * F)
          + (F * (L * L) * F - (γ : ℂ) • (F * L * F)) := by
      rw [hFh]
      simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, mul_one]
    rw [expand, hFLLF, hFLF]
    simp only [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, one_mul, mul_one, hadef]
    push_cast
    module
  -- on the range of `L`, `L ≥ γ`
  have hpos : ∀ w, 0 ≤ qf (L *ᵥ w) (L - (γ : ℂ) • 1) := by
    intro w
    rw [← qf_conj, hLh]
    have e : L * (L - (γ : ℂ) • 1) * L
        = (L - (γ : ℂ) • 1)ᴴ * L * (L - (γ : ℂ) • 1) + (γ : ℂ) • (L * L - (γ : ℂ) • L) := by
      rw [conjTranspose_sub, hLh, conjTranspose_smul, conjTranspose_one, Complex.star_def,
        Complex.conj_ofReal]
      simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, smul_sub]
      module
    rw [e]
    exact qf_nonneg ((hLpsd.conjTranspose_mul_mul_same _).add
      ((le_iff.mp hL).smul (Complex.zero_le_real.mpr hγ.le))) w
  -- each `Pₖ` vanishes on the kernel of `L`
  have hker : ∀ k v, L *ᵥ v = 0 → P k *ᵥ v = 0 := by
    intro k v hv
    apply (hPpsd k).dotProduct_mulVec_zero_iff.mp
    have hsum : ∑ j, star v ⬝ᵥ (P j *ᵥ v) = 0 := by
      rw [← dotProduct_sum, ← sum_mulVec]
      change star v ⬝ᵥ (L *ᵥ v) = 0
      rw [hv, dotProduct_zero]
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => (hPpsd j).dotProduct_mulVec_nonneg v)).mp hsum k (Finset.mem_univ k)
  -- the bound for each vector
  have hmain : ∀ x : n → ℂ,
      qf x (∑ k, P k * F * P k) ≤ (2 + κ ^ 2 / γ ^ 2) * R * qf x 1 := by
    intro x
    have hTk : ∀ k, qf x (P k * F * P k) = qf (P k *ᵥ x) F := fun k => by
      rw [← qf_conj, (hPh k).eq]
    rw [qf_sum, Finset.sum_congr rfl fun k _ => hTk k]
    refine sum_le_of_bounds (fun k => qf (P k *ᵥ x) F)
      (fun k => (star (F *ᵥ (P k *ᵥ x)) ⬝ᵥ (F *ᵥ (P k *ᵥ x))).re)
      (fun k => (star (F *ᵥ (P k *ᵥ x)) ⬝ᵥ (C k *ᵥ (F *ᵥ x))).re)
      (fun k => (star (C k *ᵥ (F *ᵥ x)) ⬝ᵥ (C k *ᵥ (F *ᵥ x))).re)
      (fun k => qf x (P k * F)) (Φ := qf (F *ᵥ x) L) hR hγ hadef (qf_nonneg PosSemidef.one x)
      ?_ ?_ (fun k => two_mul_re_le a _ _) ?_ ?_ ?_
    · -- (4.23)
      intro k
      have h := congrArg (qf x) (hF1 k)
      rw [qf_add, qf_smul, qf_conjTranspose_mul, hTk k] at h
      simp only [← mulVec_mulVec] at h
      rw [h, mul_add, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
    · -- `‖F Pₖ f‖² ≤ R/(R + γ) ⟨Pₖ f, F Pₖ f⟩`, since `Pₖ f` lies in the range of `L`
      intro k
      obtain ⟨z, hz⟩ := exists_mulVec_eq hLpsd.isHermitian (u := P k *ᵥ x) fun v hv => by
        rw [← (hPh k).star_dotProduct_mulVec_comm x v, hker k v hv, dotProduct_zero, star_zero]
      have hFu : F *ᵥ (P k *ᵥ x) = L *ᵥ (F *ᵥ z) := by
        rw [← hz, mulVec_mulVec, mulVec_mulVec, hLF]
      have h := hpos (F *ᵥ z)
      rw [← hFu, ← qf_conj, hFh, hF2, qf_sub, qf_smul, qf_smul] at h
      have hWk : qf (P k *ᵥ x) (F * F)
          = (star (F *ᵥ (P k *ᵥ x)) ⬝ᵥ (F *ᵥ (P k *ᵥ x))).re := by
        rw [← qf_conjTranspose_mul, hFh]
      rw [hWk] at h
      linarith
    · -- the commutator hypothesis at `F f`
      have h := qf_mono hcomm (F *ᵥ x)
      rw [qf_sum, qf_smul] at h
      simp only [← qf_conjTranspose_mul]
      exact h
    · -- `⟨F f, L F f⟩ ≤ R²/(R + γ) ‖f‖²`
      have hM : (((R ^ 2 : ℝ) : ℂ) • 1 + (R : ℂ) • L + (L * L - (γ : ℂ) • L)).PosSemidef :=
        ((PosSemidef.one.smul (Complex.zero_le_real.mpr (sq_nonneg R))).add
          (hLpsd.smul (Complex.zero_le_real.mpr hR.le))).add (le_iff.mp hL)
      have h := qf_nonneg (hM.conjTranspose_mul_mul_same F) x
      rw [← hF3, qf_sub, qf_smul, qf_smul] at h
      have hΦ : qf x (F * L * F) = qf (F *ᵥ x) L := by rw [← qf_conj, hFh]
      rw [hΦ] at h
      linarith
    · -- `⟨f, L F f⟩ = R ⟨f, (1 - F) f⟩ ≤ R ‖f‖²`
      rw [← qf_sum, ← Finset.sum_mul]
      change qf x (L * F) ≤ _
      rw [hLF', qf_smul, qf_sub]
      have := mul_nonneg hR.le (qf_nonneg hFpsd x)
      linarith
  have hPh' : ∀ k, (P k)ᴴ = P k := fun k => (hPh k).eq
  have hTh : (∑ k, P k * F * P k)ᴴ = ∑ k, P k * F * P k := by
    simp only [conjTranspose_sum, conjTranspose_mul, hFh, hPh', mul_assoc]
  have hKh : ((((2 + κ ^ 2 / γ ^ 2) * R : ℝ) : ℂ) • (1 : Matrix n n ℂ))ᴴ
      = (((2 + κ ^ 2 / γ ^ 2) * R : ℝ) : ℂ) • (1 : Matrix n n ℂ) := by
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  rw [le_iff]
  have hMh : ((((2 + κ ^ 2 / γ ^ 2) * R : ℝ) : ℂ) • (1 : Matrix n n ℂ)
      - ∑ k, P k * F * P k).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_sub, hKh, hTh]
  refine PosSemidef.of_dotProduct_mulVec_nonneg hMh fun x => ?_
  rw [Complex.nonneg_iff]
  refine ⟨?_, (hMh.im_star_dotProduct_mulVec_self x).symm⟩
  change 0 ≤ qf x _
  rw [qf_sub, qf_smul]
  linarith [hmain x]

end QuantumQueryComplexity
