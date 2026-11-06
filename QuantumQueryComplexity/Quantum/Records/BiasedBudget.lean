import QuantumQueryComplexity.Quantum.Records.RecordCount
import QuantumQueryComplexity.Quantum.Records.Domination

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Records of biased bits and the record budget

For `ν = Bernoulli(p)^{⊗ι}` with `0 < p < 1`, the record operators of one bit act in the basis

    |ω_p⟩ = √(1 − p)|0⟩ + √p|1⟩,   |η_p⟩ = √p|0⟩ − √(1 − p)|1⟩:

`Eᵢ` projects onto `|ω_p⟩` and `Dᵢ` onto `|η_p⟩`, so `P_S` is spanned by the tensor product with
`|η_p⟩` at the coordinates of `S` and `|ω_p⟩` elsewhere (`recProj_bern_mulVec`) [CMSZ21, HM23].

A phase query to bit `i` multiplies by `(−1)^{xᵢ}`, which in this basis has the off-diagonal entry
`2√(p(1 − p))`. Hence one query raises the expected number of records
`⟨∑ᵢ Dᵢ⟩ = ∑ᵢ ‖Dᵢ f‖²` (`recCount`) by at most `2√(p(1 − p))‖f‖²`, in the phase model and in the XOR
model (`recCount_jOracle_phase_le`, `recCount_jOracle_xor_le`). After `t` queries the expected
number of records is at most `2t√(p(1 − p))` (`recCount_jointXorState_le`), which for small `p`
is far below the bound `t` that holds for every distribution.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι A : Type} [Fintype ι] [DecidableEq ι] [Fintype A]

namespace FinDist

/-- **The expected number of records** `⟨∑ᵢ Dᵢ⟩ = ∑ᵢ ‖Dᵢ f‖²`. -/
noncomputable def recCount {σ : Type} [Fintype σ] [DecidableEq σ] (ρ : FinDist (ι → σ))
    (f : JVec ρ.Supp A) : ℝ :=
  ∑ i, jNormSq (ρ.condDiff i * f)

variable {p : ℝ}

/-- Bernoulli bits with `0 < p < 1` form a full product distribution. -/
theorem isFullProduct_bern (hp0 : 0 < p) (hp1 : p < 1) :
    (bern p hp0.le hp1.le : FinDist (ι → Bool)).IsFullProduct := by
  exact ⟨fun _ b => if b then p else 1 - p, fun _ b => by dsimp only; split_ifs <;> linarith,
    fun _ => rfl⟩

/-- Product Bernoulli masses are positive for `0 < p < 1`. -/
private lemma bernMass_pos (hp0 : 0 < p) (hp1 : p < 1) (x : ι → Bool) : 0 < bernMass p x :=
  Finset.prod_pos fun _ _ => by split_ifs <;> linarith

/-- The marginals of `Bernoulli(p)^{⊗ι}`. -/
private lemma marg_bern (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : ι) (a : Bool) :
    (bern p hp0 hp1 : FinDist (ι → Bool)).marg i a = if a then p else 1 - p := by
  set w : Bool → ℝ := fun b => if b then p else 1 - p with hw
  have key : ∀ x : ι → Bool, (if x i = a then bernMass p x else 0)
      = ∏ j, (if j = i then (if x j = a then w (x j) else 0) else w (x j)) := by
    intro x
    by_cases h : x i = a
    · rw [ite_eq_left h]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hj : j = i
      · subst hj
        simp [h, hw]
      · simp [hj, hw]
    · rw [ite_eq_right h]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h])).symm
  unfold marg
  simp only [bern_mass]
  rw [Finset.sum_congr rfl fun x _ => key x,
    ← Fintype.prod_sum (fun j b => if j = i then (if b = a then w b else 0) else w b)]
  have hs : ∀ j, (∑ b, if j = i then (if b = a then w b else 0) else w b)
      = if j = i then w a else 1 := by
    intro j
    by_cases hj : j = i
    · simp [hj]
    · simp [hj, hw]
  rw [Finset.prod_congr rfl fun j _ => hs j]
  simp [hw]

/-- `|ω_p⟩`: the unrecorded state of one bit. -/
noncomputable def bernOmega (p : ℝ) : Bool → ℂ := fun b =>
  if b then ((Real.sqrt p : ℝ) : ℂ) else ((Real.sqrt (1 - p) : ℝ) : ℂ)

/-- `|η_p⟩`: the recorded state of one bit. -/
noncomputable def bernEta (p : ℝ) : Bool → ℂ := fun b =>
  if b then -((Real.sqrt (1 - p) : ℝ) : ℂ) else ((Real.sqrt p : ℝ) : ℂ)

/-- The basis vector with records exactly at `T`: `|η_p⟩` on `T`, `|ω_p⟩` elsewhere. -/
noncomputable def bernVec (p : ℝ) (T : Finset ι) : (ι → Bool) → ℂ := fun x =>
  ∏ i, if i ∈ T then bernEta p (x i) else bernOmega p (x i)

/-- `√(μᵢ(a) μᵢ(b)) = ω_p(a) ω_p(b)` for Bernoulli bits. -/
private lemma sqrt_marg_bern (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : ι) (a b : Bool) :
    ((Real.sqrt ((bern p hp0 hp1 : FinDist (ι → Bool)).marg i a
      * (bern p hp0 hp1 : FinDist (ι → Bool)).marg i b) : ℝ) : ℂ)
      = bernOmega p a * bernOmega p b := by
  rw [marg_bern, marg_bern, Real.sqrt_mul (by split_ifs <;> linarith), Complex.ofReal_mul]
  cases a <;> cases b <;> simp [bernOmega]

/-- `(√p)² = p` in `ℂ`. -/
private lemma ofReal_sqrt_mul_self {r : ℝ} (hr : 0 ≤ r) :
    ((Real.sqrt r : ℝ) : ℂ) * ((Real.sqrt r : ℝ) : ℂ) = r := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr]

/-- The factors of `P_S` for Bernoulli bits: `|η_p⟩⟨η_p|` on `S`, `|ω_p⟩⟨ω_p|` elsewhere. -/
private lemma recFactor_bern (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset ι) (i : ι) (a b : Bool) :
    (bern p hp0 hp1 : FinDist (ι → Bool)).recFactor S i a b
      = if i ∈ S then bernEta p a * bernEta p b else bernOmega p a * bernOmega p b := by
  have hp := ofReal_sqrt_mul_self hp0
  have hq := ofReal_sqrt_mul_self (sub_nonneg.mpr hp1)
  push_cast at hq
  unfold recFactor
  rw [sqrt_marg_bern]
  by_cases hS : i ∈ S
  · simp only [hS, ↓reduceIte]
    cases a <;> cases b <;>
      simp only [bernOmega, bernEta, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
        zero_sub] <;>
      first | ring1 | linear_combination -hq - hp
  · simp only [hS, ↓reduceIte]

/-- One coordinate of `P_S` applied to `|η_p⟩` or `|ω_p⟩`. -/
private lemma sum_bern_coord (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P Q : Prop) [Decidable P]
    [Decidable Q] (a : Bool) :
    ∑ b, (if P then bernEta p a * bernEta p b else bernOmega p a * bernOmega p b)
        * (if Q then bernEta p b else bernOmega p b)
      = if (P ↔ Q) then (if Q then bernEta p a else bernOmega p a) else 0 := by
  have hp := ofReal_sqrt_mul_self hp0
  have hq := ofReal_sqrt_mul_self (sub_nonneg.mpr hp1)
  push_cast at hq
  cases a <;> by_cases hP : P <;> by_cases hQ : Q <;>
    simp only [hP, hQ, Fintype.sum_bool, bernOmega, bernEta, ↓reduceIte, iff_self, iff_false,
      false_iff, not_true_eq_false, Bool.false_eq_true] <;>
    first
    | ring1
    | linear_combination ((Real.sqrt p : ℝ) : ℂ) * (hq + hp)
    | linear_combination ((Real.sqrt (1 - p) : ℝ) : ℂ) * (hq + hp)
    | linear_combination -((Real.sqrt (1 - p) : ℝ) : ℂ) * (hq + hp)

/-- **The record subspaces of biased bits**: `P_S` fixes the basis vector with records at `S` and
kills those with records elsewhere. -/
theorem recProj_bern_mulVec (hp0 : 0 < p) (hp1 : p < 1) (S T : Finset ι) :
    (bern p hp0.le hp1.le : FinDist (ι → Bool)).recProj S
        *ᵥ (fun x : (bern p hp0.le hp1.le : FinDist (ι → Bool)).Supp => bernVec p T x.1)
      = if S = T then
          (fun x : (bern p hp0.le hp1.le : FinDist (ι → Bool)).Supp => bernVec p T x.1)
        else 0 := by
  have hpos : ∀ x : ι → Bool, 0 < (bern p hp0.le hp1.le : FinDist (ι → Bool)).mass x :=
    fun x => bernMass_pos hp0 hp1 x
  funext x
  have hsum : ((bern p hp0.le hp1.le : FinDist (ι → Bool)).recProj S
        *ᵥ (fun x : (bern p hp0.le hp1.le : FinDist (ι → Bool)).Supp => bernVec p T x.1)) x
      = ∑ y : ι → Bool, ∏ i, ((if i ∈ S then bernEta p (x.1 i) * bernEta p (y i)
          else bernOmega p (x.1 i) * bernOmega p (y i))
            * (if i ∈ T then bernEta p (y i) else bernOmega p (y i))) := by
    simp only [mulVec, dotProduct, recProj]
    rw [← (Equiv.subtypeUnivEquiv hpos).sum_comp]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [bernVec, ← Finset.prod_mul_distrib]
    simp only [recFactor_bern]
    rfl
  rw [hsum, ← Fintype.prod_sum (fun i b => (if i ∈ S then bernEta p (x.1 i) * bernEta p b
      else bernOmega p (x.1 i) * bernOmega p b) * (if i ∈ T then bernEta p b else bernOmega p b))]
  simp only [sum_bern_coord hp0.le hp1.le]
  split_ifs with hST
  · subst hST
    simp only [iff_self, ↓reduceIte]
    rfl
  · obtain ⟨i, hi⟩ : ∃ i, ¬(i ∈ S ↔ i ∈ T) := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hST (Finset.ext hc)
    rw [Pi.zero_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-! ### One query -/

/-- The phase `(−1)^b` of a phase query. -/
private def bitSign (b : Bool) : ℂ := if b then -1 else 1

/-- `((−1)^b)² = 1`. -/
private lemma bitSign_mul_self (b : Bool) : bitSign b * bitSign b = 1 := by
  cases b <;> norm_num [bitSign]

/-- The phase `(−1)^b` is real. -/
private lemma star_bitSign (b : Bool) : star (bitSign b) = bitSign b := by
  cases b <;> norm_num [bitSign]

/-- The phase `(−1)^b` has modulus one. -/
private lemma normSq_bitSign (b : Bool) : Complex.normSq (bitSign b) = 1 := by
  cases b <;> norm_num [bitSign]

/-- Column `q` of a joint vector, as a joint vector with a one-point workspace. -/
private def colJ {X B : Type} (f : JVec X B) (q : B) : JVec X Unit := fun x _ => f x q

/-- Input-register operators act on each column. -/
private lemma colJ_mul {X Y B : Type} [Fintype X] (M : Matrix Y X ℂ) (f : JVec X B) (q : B) :
    colJ (M * f) q = M * colJ f q := by
  ext x u
  simp only [colJ, Matrix.mul_apply]

/-- `‖f‖²` is the sum of the squared norms of the columns. -/
private lemma jNormSq_eq_sum_colJ {X B : Type} [Fintype X] [Fintype B] (f : JVec X B) :
    jNormSq f = ∑ q, jNormSq (colJ f q) := by
  simp only [jNormSq, qNormSq_def, colJ, Finset.univ_unique, Finset.sum_singleton]
  exact Finset.sum_comm

/-- A phase query to one bit preserves norms. -/
private lemma jNormSq_coordDiag_mul {ρ : FinDist (ι → Bool)} {B : Type} [Fintype B] (i : ι)
    (h : JVec ρ.Supp B) : jNormSq (ρ.coordDiag i bitSign * h) = jNormSq h := by
  unfold jNormSq
  refine Finset.sum_congr rfl fun x _ => ?_
  have hx : (ρ.coordDiag i bitSign * h) x = bitSign (x.1 i) • h x := by
    funext q
    simp only [coordDiag, Matrix.diagonal_mul, Pi.smul_apply, smul_eq_mul]
  simp only [qNormSq_def, hx, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, normSq_bitSign,
    one_mul]

/-- A phase query to bit `i` does not change `‖Dⱼ f‖` for `j ≠ i`. -/
private lemma jNormSq_condDiff_coordDiag_of_ne {ρ : FinDist (ι → Bool)} {B : Type} [Fintype B]
    {i j : ι} (hji : j ≠ i) (g : JVec ρ.Supp B) :
    jNormSq (ρ.condDiff j * (ρ.coordDiag i bitSign * g)) = jNormSq (ρ.condDiff j * g) := by
  rw [← Matrix.mul_assoc, (ρ.commute_condDiff_coordDiag hji bitSign).eq, Matrix.mul_assoc,
    jNormSq_coordDiag_mul]

/-- Flipping bit `i` of a string. -/
private def flipAt (i : ι) (x : ι → Bool) : ι → Bool := Function.update x i (!x i)

/-- Flipping a bit twice is the identity. -/
private lemma flipAt_flipAt (i : ι) (x : ι → Bool) : flipAt i (flipAt i x) = x := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [flipAt]
  · simp [flipAt, hj]

/-- Flipping bit `i`, on the support of `Bernoulli(p)^{⊗ι}`. -/
private def flipSupp (hp0 : 0 < p) (hp1 : p < 1) (i : ι) :
    Equiv.Perm (bern p hp0.le hp1.le : FinDist (ι → Bool)).Supp :=
  Function.Involutive.toPerm (fun x => ⟨flipAt i x.1, bernMass_pos hp0 hp1 _⟩)
    fun x => Subtype.ext (flipAt_flipAt i x.1)

/-- The underlying string of a flipped support point. -/
private lemma flipSupp_val (hp0 : 0 < p) (hp1 : p < 1) (i : ι)
    (x : (bern p hp0.le hp1.le : FinDist (ι → Bool)).Supp) :
    (flipSupp hp0 hp1 i x).1 = flipAt i x.1 := rfl

/-- `y` is the flip of `x` at `i` iff it agrees with `x` off `i` and differs at `i`. -/
private lemma eq_flipSupp_iff (hp0 : 0 < p) (hp1 : p < 1) (i : ι)
    (x y : (bern p hp0.le hp1.le : FinDist (ι → Bool)).Supp) :
    y = flipSupp hp0 hp1 i x ↔ AgreeOff i x.1 y.1 ∧ y.1 i = !x.1 i := by
  constructor
  · rintro rfl
    refine ⟨fun j hj => ?_, ?_⟩
    · simp [flipSupp_val, flipAt, hj]
    · simp [flipSupp_val, flipAt]
  · rintro ⟨h1, h2⟩
    refine Subtype.ext (funext fun j => ?_)
    by_cases hj : j = i
    · subst hj
      simp [flipSupp_val, flipAt, h2]
    · simp [flipSupp_val, flipAt, hj, h1 j hj]

/-- **`Eᵢ − ZᵢEᵢZᵢ` is `2√(p(1 − p))` times the flip of bit `i`.** -/
private lemma condExp_sub_conj_apply (hp0 : 0 < p) (hp1 : p < 1) (i : ι)
    (x y : (bern p hp0.le hp1.le : FinDist (ι → Bool)).Supp) :
    ((bern p hp0.le hp1.le : FinDist (ι → Bool)).condExp i
      - (bern p hp0.le hp1.le : FinDist (ι → Bool)).coordDiag i bitSign
        * (bern p hp0.le hp1.le : FinDist (ι → Bool)).condExp i
        * (bern p hp0.le hp1.le : FinDist (ι → Bool)).coordDiag i bitSign) x y
      = if y = flipSupp hp0 hp1 i x then ((2 * Real.sqrt (p * (1 - p)) : ℝ) : ℂ) else 0 := by
  have hs : ((2 * Real.sqrt (p * (1 - p)) : ℝ) : ℂ)
      = 2 * (((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt (1 - p) : ℝ) : ℂ)) := by
    rw [Real.sqrt_mul hp0.le]
    push_cast
    ring
  simp only [Matrix.sub_apply, coordDiag, Matrix.mul_diagonal, Matrix.diagonal_mul,
    condExp_apply_of_isFullProduct (isFullProduct_bern hp0 hp1), sqrt_marg_bern,
    eq_flipSupp_iff, hs]
  by_cases hxy : AgreeOff i x.1 y.1
  · simp only [hxy, true_and, ↓reduceIte]
    generalize x.1 i = a
    generalize y.1 i = b
    cases a <;> cases b <;> norm_num [bitSign, bernOmega] <;> ring
  · simp only [hxy, false_and, ↓reduceIte, mul_zero, zero_mul, sub_zero]

/-- `Re ⟨a, b⟩ ≤ (‖a‖² + ‖b‖²)/2`. -/
private lemma re_qInner_le {H : Type} [Fintype H] (a b : H → ℂ) :
    (qInner a b).re ≤ (qNormSq a + qNormSq b) / 2 := by
  classical
  rw [qInner_def, Complex.re_sum, qNormSq_def, qNormSq_def, ← Finset.sum_add_distrib,
    Finset.sum_div]
  refine Finset.sum_le_sum fun h _ => ?_
  rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply,
    Complex.normSq_apply]
  nlinarith [sq_nonneg ((a h).re - (b h).re), sq_nonneg ((a h).im - (b h).im)]

/-- **The budget of one phase query on its own bit**, abstractly: if `Eᵢ − ZᵢEᵢZᵢ` is `c ≥ 0`
times a permutation, then `‖DᵢZᵢg‖² ≤ ‖Dᵢg‖² + c‖g‖²`. -/
private lemma jNormSq_condDiff_coordDiag_le_of {ρ : FinDist (ι → Bool)} {B : Type} [Fintype B]
    (i : ι) {c : ℝ} (hc0 : 0 ≤ c) (τ : Equiv.Perm ρ.Supp)
    (hM : ∀ x y, (ρ.condExp i - ρ.coordDiag i bitSign * ρ.condExp i * ρ.coordDiag i bitSign) x y
      = if y = τ x then (c : ℂ) else 0) (g : JVec ρ.Supp B) :
    jNormSq (ρ.condDiff i * (ρ.coordDiag i bitSign * g))
      ≤ jNormSq (ρ.condDiff i * g) + c * jNormSq g := by
  classical
  set Z := ρ.coordDiag i bitSign with hZ
  set E := ρ.condExp i with hE
  have hZh : Zᴴ = Z := by
    rw [hZ, coordDiag, Matrix.diagonal_conjTranspose]
    congr 1
    funext x
    exact star_bitSign _
  have hZZ : Z * Z = 1 := by
    rw [hZ, coordDiag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext x
    exact bitSign_mul_self _
  have hre : ∀ h : JVec ρ.Supp B, jNormSq (ρ.condDiff i * h) = (jInner h (ρ.condDiff i * h)).re :=
    fun h => by rw [jInner_condDiff_mul, Complex.ofReal_re]
  have hmove : ∀ h : JVec ρ.Supp B, jInner (Z * g) h = jInner g (Z * h) := fun h => by
    rw [jInner_mul_right, hZh]
  have hD : ρ.condDiff i = 1 - E := rfl
  have hA : jNormSq (ρ.condDiff i * (Z * g)) = (jInner g ((1 - Z * E * Z) * g)).re := by
    rw [hre, hmove, hD, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one,
      Matrix.sub_mul, hZZ]
  have hB : jNormSq (ρ.condDiff i * g) = (jInner g ((1 - E) * g)).re := by
    rw [hre, hD]
  have hdiff : jInner g ((1 - Z * E * Z) * g)
      = jInner g ((1 - E) * g) + jInner g ((E - Z * E * Z) * g) := by
    rw [jInner_eq_trace, jInner_eq_trace, jInner_eq_trace, ← Matrix.trace_add, ← Matrix.mul_add,
      ← Matrix.add_mul]
    congr 3
    abel
  have hMg : (E - Z * E * Z) * g = fun x => (c : ℂ) • g (τ x) := by
    ext x q
    simp only [Matrix.mul_apply, hM, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, Pi.smul_apply, smul_eq_mul]
  have hbound : (jInner g (fun x => (c : ℂ) • g (τ x))).re ≤ c * jNormSq g := by
    simp only [jInner, qInner_smul_right, Complex.re_sum, Complex.re_ofReal_mul]
    calc ∑ x, c * (qInner (g x) (g (τ x))).re
        ≤ ∑ x, c * ((qNormSq (g x) + qNormSq (g (τ x))) / 2) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (re_qInner_le _ _) hc0
      _ = c * jNormSq g := by
          have hperm := Equiv.sum_comp τ (fun x => qNormSq (g x))
          rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib, hperm]
          unfold jNormSq
          ring
  rw [hA, hdiff, Complex.add_re, ← hB, hMg]
  linarith

/-- **The budget of one phase query on its own bit**:
`‖DᵢZᵢg‖² ≤ ‖Dᵢg‖² + 2√(p(1 − p))‖g‖²`. -/
private lemma jNormSq_condDiff_coordDiag_le (hp0 : 0 < p) (hp1 : p < 1) {B : Type} [Fintype B]
    (i : ι) (g : JVec (bern p hp0.le hp1.le : FinDist (ι → Bool)).Supp B) :
    jNormSq ((bern p hp0.le hp1.le : FinDist (ι → Bool)).condDiff i
        * ((bern p hp0.le hp1.le : FinDist (ι → Bool)).coordDiag i bitSign * g))
      ≤ jNormSq ((bern p hp0.le hp1.le : FinDist (ι → Bool)).condDiff i * g)
        + 2 * Real.sqrt (p * (1 - p)) * jNormSq g :=
  jNormSq_condDiff_coordDiag_le_of i (by positivity) (flipSupp hp0 hp1 i)
    (condExp_sub_conj_apply hp0 hp1 i) g

/-- On the column of a query sector, the phase oracle is the phase query to that bit. -/
private lemma colJ_jOracle_phase_sector {ρ : FinDist (ι → Bool)} {W : Type} [Fintype W]
    [DecidableEq W] (f : JVec ρ.Supp (QBasis ι Bool W)) (i : ι) (w : W) :
    colJ (jOracle phaseOracleMat (fun x : ρ.Supp => (x : ι → Bool)) f) (some i, some true, w)
      = ρ.coordDiag i bitSign * colJ f (some i, some true, w) := by
  ext x u
  simp only [colJ, jOracle, phaseOracleMat, Matrix.mulVec_diagonal, coordDiag,
    Matrix.diagonal_mul]
  rfl

/-- **The record budget of one column**: one phase query raises `∑ⱼ ‖Dⱼ fₚ‖²` by at most
`2√(p(1 − p))‖fₚ‖²` on each column `q`. -/
private lemma sum_jNormSq_colJ_phase_le (hp0 : 0 < p) (hp1 : p < 1) {W : Type} [Fintype W]
    [DecidableEq W] (f : JVec (bern p hp0.le hp1.le : FinDist (ι → Bool)).Supp (QBasis ι Bool W))
    (q : QBasis ι Bool W) :
    ∑ j, jNormSq ((bern p hp0.le hp1.le : FinDist (ι → Bool)).condDiff j
        * colJ (jOracle phaseOracleMat (fun x : (bern p hp0.le hp1.le : FinDist (ι → Bool)).Supp =>
          (x : ι → Bool)) f) q)
      ≤ ∑ j, jNormSq ((bern p hp0.le hp1.le : FinDist (ι → Bool)).condDiff j * colJ f q)
        + 2 * Real.sqrt (p * (1 - p)) * jNormSq (colJ f q) := by
  have hc0 : 0 ≤ 2 * Real.sqrt (p * (1 - p)) := by positivity
  by_cases hq : ∃ e w, q = (some e, some true, w)
  · obtain ⟨i, w, rfl⟩ := hq
    rw [colJ_jOracle_phase_sector]
    have hj : ∀ j, jNormSq ((bern p hp0.le hp1.le : FinDist (ι → Bool)).condDiff j
        * ((bern p hp0.le hp1.le : FinDist (ι → Bool)).coordDiag i bitSign
          * colJ f (some i, some true, w)))
        ≤ jNormSq ((bern p hp0.le hp1.le : FinDist (ι → Bool)).condDiff j
            * colJ f (some i, some true, w))
          + if j = i then 2 * Real.sqrt (p * (1 - p)) * jNormSq (colJ f (some i, some true, w))
            else 0 := by
      intro j
      by_cases hji : j = i
      · subst hji
        rw [ite_eq_left rfl]
        exact jNormSq_condDiff_coordDiag_le hp0 hp1 j _
      · rw [jNormSq_condDiff_coordDiag_of_ne hji, ite_eq_right hji, add_zero]
    refine (Finset.sum_le_sum fun j _ => hj j).trans_eq ?_
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ i)]
  · simp only [not_exists] at hq
    have hcol : colJ (jOracle phaseOracleMat (fun x : (bern p hp0.le hp1.le :
        FinDist (ι → Bool)).Supp => (x : ι → Bool)) f) q = colJ f q := by
      ext x u
      exact jOracle_phase_apply_of_not_sector _ f x q fun e w h => hq e w h
    rw [hcol]
    exact le_add_of_nonneg_right (mul_nonneg hc0 (jNormSq_nonneg _))

/-- **The record budget of a phase query**: one phase query raises `⟨∑ᵢ Dᵢ⟩` by at most
`2√(p(1 − p))‖f‖²`. -/
theorem recCount_jOracle_phase_le (hp0 : 0 < p) (hp1 : p < 1) {W : Type} [Fintype W]
    [DecidableEq W] (f : JVec (bern p hp0.le hp1.le : FinDist (ι → Bool)).Supp (QBasis ι Bool W)) :
    (bern p hp0.le hp1.le : FinDist (ι → Bool)).recCount
        (jOracle phaseOracleMat (fun x : (bern p hp0.le hp1.le : FinDist (ι → Bool)).Supp =>
          (x : ι → Bool)) f)
      ≤ (bern p hp0.le hp1.le : FinDist (ι → Bool)).recCount f
        + 2 * Real.sqrt (p * (1 - p)) * jNormSq f := by
  have hsplit : ∀ g : JVec (bern p hp0.le hp1.le : FinDist (ι → Bool)).Supp (QBasis ι Bool W),
      (bern p hp0.le hp1.le : FinDist (ι → Bool)).recCount g
        = ∑ q, ∑ j, jNormSq ((bern p hp0.le hp1.le : FinDist (ι → Bool)).condDiff j
          * colJ g q) := by
    intro g
    unfold recCount
    simp only [jNormSq_eq_sum_colJ (_ * g), colJ_mul]
    exact Finset.sum_comm
  rw [hsplit, hsplit, jNormSq_eq_sum_colJ f, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun q _ => sum_jNormSq_colJ_phase_le hp0 hp1 f q

/-- Workspace unitaries do not change the expected number of records. -/
private lemma recCount_wsOp {σ B : Type} [Fintype σ] [DecidableEq σ] [Fintype B] [DecidableEq B]
    (ρ : FinDist (ι → σ)) {U : Matrix B B ℂ} (hU : U ∈ Matrix.unitaryGroup B ℂ)
    (f : JVec ρ.Supp B) : ρ.recCount (wsOp U f) = ρ.recCount f := by
  unfold recCount
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_wsOp, jNormSq_wsOp_of_mem_unitaryGroup hU]

/-- **The record budget of an XOR query**, the same bound. -/
theorem recCount_jOracle_xor_le (hp0 : 0 < p) (hp1 : p < 1) {W : Type} [Fintype W]
    [DecidableEq W] (f : JVec (bern p hp0.le hp1.le : FinDist (ι → Bool)).Supp (QBasis ι Bool W)) :
    (bern p hp0.le hp1.le : FinDist (ι → Bool)).recCount
        (jOracle xorOracleMat (fun x : (bern p hp0.le hp1.le : FinDist (ι → Bool)).Supp =>
          (x : ι → Bool)) f)
      ≤ (bern p hp0.le hp1.le : FinDist (ι → Bool)).recCount f
        + 2 * Real.sqrt (p * (1 - p)) * jNormSq f := by
  rw [jOracle_xor_eq_hadAns_phase, recCount_wsOp _ hadAns_mem_unitaryGroup]
  refine (recCount_jOracle_phase_le hp0 hp1 _).trans_eq ?_
  rw [recCount_wsOp _ hadAns_mem_unitaryGroup,
    jNormSq_wsOp_of_mem_unitaryGroup hadAns_mem_unitaryGroup]

/-- **After `t` XOR queries on Bernoulli(p) bits**, the expected number of records is at most
`2t√(p(1 − p))`. -/
theorem recCount_jointXorState_le (hp0 : 0 < p) (hp1 : p < 1) {O W : Type} [Fintype W]
    [DecidableEq W] (A : QAlg ι Bool O W) (t : ℕ) :
    (bern p hp0.le hp1.le : FinDist (ι → Bool)).recCount
        ((bern p hp0.le hp1.le : FinDist (ι → Bool)).jointXorState id A t)
      ≤ 2 * Real.sqrt (p * (1 - p)) * t := by
  induction t with
  | zero =>
    have h0 : ∀ j, (bern p hp0.le hp1.le : FinDist (ι → Bool)).condDiff j
        * (bern p hp0.le hp1.le : FinDist (ι → Bool)).jointXorState id A 0 = 0 := by
      intro j
      ext x q
      have hk := congrFun ((bern p hp0.le hp1.le : FinDist (ι → Bool)).condDiff_mulVec_ket j) x
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hk
      have hy : ∀ y, (bern p hp0.le hp1.le : FinDist (ι → Bool)).jointXorState id A 0 y q
          = (bern p hp0.le hp1.le : FinDist (ι → Bool)).ket y * (A.step 0 *ᵥ A.init) q :=
        fun y => by rw [jointXorState_zero]; rfl
      rw [Matrix.mul_apply, Matrix.zero_apply]
      simp only [hy, ← mul_assoc, ← Finset.sum_mul, hk, zero_mul]
    have hz : jNormSq (0 : JVec (bern p hp0.le hp1.le : FinDist (ι → Bool)).Supp
        (QBasis ι Bool W)) = 0 :=
      Finset.sum_eq_zero fun x _ => qNormSq_zero
    simp only [recCount, h0, hz, Finset.sum_const_zero, Nat.cast_zero, mul_zero, le_refl]
  | succ t ih =>
    rw [jointXorState_succ, recCount_wsOp _ (A.step_unitary _)]
    have h := recCount_jOracle_xor_le hp0 hp1
      ((bern p hp0.le hp1.le : FinDist (ι → Bool)).jointXorState id A t)
    rw [jNormSq_jointXorState] at h
    push_cast
    refine h.trans ?_
    linarith

end FinDist

end QuantumQueryComplexity
