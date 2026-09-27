import QuantumQueryComplexity.Promise.Basic
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Transporting promise lower bounds

Three ways to move an `advPMOn` lower bound to a different problem.

* **Zero extension.** An injective encoding `encode : X → (ι → σ)` of a
  promise domain into a full cube carries a promise adversary matrix to a total
  one by padding with zeros, *without changing its norm*
  (`advPMOn_le_advPM_of_injective`).  The construction is
  `zextMat encode Γ = Eᵀ Γ E` for the one-hot incidence matrix `E` of `encode`,
  which makes the norm equality two applications of the bilinear
  characterisation of the operator norm in `Spectral.lean`: restriction
  `u ↦ u ∘ encode` never increases the ℓ² mass, and zero-extension of a vector
  preserves it exactly.
* **Query-local encodings.** If every target coordinate either copies one
  source coordinate or is constant across the promise, then every source
  difference matrix is reproduced or killed, so feasibility transports
  (`advPMOn_mono_of_local`).  `sourceAt` need not be injective — duplicating a
  source coordinate is harmless.
* **Output postprocessing.** An adversary matrix for `accept ∘ g` is one
  for `g` (`advPM_postcompose_le`, `advPMOn_postcompose_le`).

## Observation maps must determine the output

`advPMOn_mono_localEncoding` requires a side condition:
`le_advPMOn` needs the target observations to determine the output,
and a `LocalEncoding` whose `sourceAt` misses a source coordinate can lose that:
if `encode x = encode y` while `f x ≠ f y`, the feasible set for `encode` is
unbounded and `sSup` degenerates to `0`, while `advPMOn read f` can be positive.
So the theorem below carries `hdetEnc`, and
`advPMOn_mono_localEncoding_of_surjective` derives it from `sourceAt` hitting
every source coordinate.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-! ## Zero extension along an encoding -/

section Zext

variable {X K : Type*} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]

/-- The one-hot incidence matrix of an encoding: row `x` is the indicator of
`encode x`. -/
def encMat (encode : X → K) : Matrix X K ℝ :=
  Matrix.of fun x a => if a = encode x then 1 else 0

/-- **Zero extension**: the promise matrix `Γ` viewed as a matrix on the whole
target type, vanishing off the image of `encode`. -/
def zextMat (encode : X → K) (Γ : Matrix X X ℝ) : Matrix K K ℝ :=
  (encMat encode)ᵀ * Γ * encMat encode

/-- Zero extension of a vector. -/
def zextVec (encode : X → K) (p : X → ℝ) : K → ℝ :=
  p ᵥ* encMat encode

lemma encMat_apply (encode : X → K) (x : X) (a : K) :
    encMat encode x a = if a = encode x then 1 else 0 := rfl

lemma zextMat_apply (encode : X → K) (Γ : Matrix X X ℝ) (a b : K) :
    zextMat encode Γ a b
      = ∑ y, ∑ x, encMat encode x a * Γ x y * encMat encode y b := by
  change ((encMat encode)ᵀ * Γ * encMat encode) a b = _
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => rfl

/-- Applying the incidence matrix to a target vector restricts it along the
encoding. -/
lemma encMat_mulVec (encode : X → K) (w : K → ℝ) :
    encMat encode *ᵥ w = fun x => w (encode x) := by
  funext x
  change ∑ a, encMat encode x a * w a = w (encode x)
  rw [Finset.sum_eq_single (encode x)]
  · rw [show encMat encode x (encode x) = 1 from if_pos rfl, one_mul]
  · intro a _ ha
    rw [show encMat encode x a = 0 from if_neg ha, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma encMat_mulVec_zextVec {encode : X → K} (hinj : Function.Injective encode)
    (p : X → ℝ) : encMat encode *ᵥ zextVec encode p = p := by
  rw [encMat_mulVec]
  funext x
  change ∑ x', p x' * encMat encode x' (encode x) = p x
  rw [Finset.sum_eq_single x]
  · rw [show encMat encode x (encode x) = 1 from if_pos rfl, mul_one]
  · intro x' _ hx'
    rw [show encMat encode x' (encode x) = 0 from
      if_neg fun h => hx' (hinj h).symm, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Zero-extending a vector preserves its ℓ² mass. -/
lemma zextVec_dotProduct_self {encode : X → K}
    (hinj : Function.Injective encode) (p : X → ℝ) :
    zextVec encode p ⬝ᵥ zextVec encode p = p ⬝ᵥ p := by
  change (p ᵥ* encMat encode) ⬝ᵥ zextVec encode p = p ⬝ᵥ p
  rw [← Matrix.dotProduct_mulVec, encMat_mulVec_zextVec hinj]

/-- Restricting a target vector along an injective encoding does not increase
its ℓ² mass. -/
lemma encMat_mulVec_dotProduct_self_le {encode : X → K}
    (hinj : Function.Injective encode) (u : K → ℝ) :
    (encMat encode *ᵥ u) ⬝ᵥ (encMat encode *ᵥ u) ≤ u ⬝ᵥ u := by
  have hkey : ∑ a ∈ Finset.univ.image encode, u a * u a
      = ∑ x : X, u (encode x) * u (encode x) :=
    Finset.sum_image hinj.injOn
  rw [encMat_mulVec]
  change ∑ x : X, u (encode x) * u (encode x) ≤ ∑ a : K, u a * u a
  rw [← hkey]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun a _ _ => mul_self_nonneg (u a)

/-- The bilinear form of a zero extension is the bilinear form of the original
matrix on the restricted vectors. -/
lemma dotProduct_zextMat_mulVec (encode : X → K) (Γ : Matrix X X ℝ)
    (u w : K → ℝ) :
    u ⬝ᵥ zextMat encode Γ *ᵥ w
      = (encMat encode *ᵥ u) ⬝ᵥ Γ *ᵥ (encMat encode *ᵥ w) := by
  rw [zextMat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

lemma zextMat_isHermitian {encode : X → K} {Γ : Matrix X X ℝ}
    (hΓ : Γ.IsHermitian) : (zextMat encode Γ).IsHermitian := by
  have hsym : ∀ i j, Γ i j = Γ j i := by
    intro i j
    conv_lhs => rw [← hΓ.eq]
    simp [Matrix.conjTranspose_apply]
  change (zextMat encode Γ)ᴴ = zextMat encode Γ
  ext a b
  rw [Matrix.conjTranspose_apply, star_trivial, zextMat_apply, zextMat_apply]
  have hswap : ∑ y : X, ∑ x : X,
        encMat encode x b * Γ x y * encMat encode y a
      = ∑ x : X, ∑ y : X,
        encMat encode x b * Γ x y * encMat encode y a := Finset.sum_comm
  rw [hswap]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsym i j]
  ring

/-- Zero extension is supported on pairs of encoded inputs. -/
lemma zextMat_apply_eq_zero (encode : X → K) {Γ : Matrix X X ℝ} {a b : K}
    (h : ∀ x y, a = encode x → b = encode y → Γ x y = 0) :
    zextMat encode Γ a b = 0 := by
  rw [zextMat_apply]
  refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun x _ => ?_
  by_cases ha : a = encode x
  · by_cases hb : b = encode y
    · rw [h x y ha hb]
      ring
    · rw [show encMat encode y b = 0 from if_neg hb]
      ring
  · rw [show encMat encode x a = 0 from if_neg ha]
    ring

lemma zextMat_apply_of_not_mem_range (encode : X → K) (Γ : Matrix X X ℝ)
    {a b : K} (h : (∀ x, encode x ≠ a) ∨ (∀ y, encode y ≠ b)) :
    zextMat encode Γ a b = 0 := by
  refine zextMat_apply_eq_zero encode fun x y hx hy => ?_
  rcases h with h | h
  · exact absurd hx.symm (h x)
  · exact absurd hy.symm (h y)

/-- On the image, zero extension reproduces the original entries. -/
lemma zextMat_apply_encode {encode : X → K} (hinj : Function.Injective encode)
    (Γ : Matrix X X ℝ) (x₀ y₀ : X) :
    zextMat encode Γ (encode x₀) (encode y₀) = Γ x₀ y₀ := by
  rw [zextMat_apply, Finset.sum_eq_single y₀]
  · rw [Finset.sum_eq_single x₀]
    · rw [show encMat encode x₀ (encode x₀) = 1 from if_pos rfl,
        show encMat encode y₀ (encode y₀) = 1 from if_pos rfl]
      ring
    · intro x _ hx
      rw [show encMat encode x (encode x₀) = 0 from
        if_neg fun h => hx (hinj h).symm]
      ring
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro y _ hy
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [show encMat encode y (encode y₀) = 0 from
      if_neg fun h => hy (hinj h).symm]
    ring
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A mask on the target pulls back through the encoding. -/
lemma zextMat_hadamard (encode : X → K) (Γ : Matrix X X ℝ)
    (mask : Matrix K K ℝ) :
    zextMat encode Γ ⊙ mask
      = zextMat encode (Γ ⊙ mask.submatrix encode encode) := by
  ext a b
  rw [Matrix.hadamard_apply, zextMat_apply, zextMat_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases ha : a = encode x
  · by_cases hb : b = encode y
    · subst ha
      subst hb
      rw [Matrix.hadamard_apply, Matrix.submatrix_apply]
      ring
    · rw [show encMat encode y b = 0 from if_neg hb]
      ring
  · rw [show encMat encode x a = 0 from if_neg ha]
    ring

/-- **Zero extension preserves the operator norm.** -/
theorem norm_zextMat {encode : X → K} (hinj : Function.Injective encode)
    (Γ : Matrix X X ℝ) : ‖zextMat encode Γ‖ = ‖Γ‖ := by
  refine le_antisymm ?_ ?_
  · refine l2_opNorm_le_of_forall_dotProduct _ (norm_nonneg Γ) fun u w => ?_
    rw [dotProduct_zextMat_mulVec]
    refine (abs_dotProduct_mulVec_le Γ _ _).trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (encMat_mulVec_dotProduct_self_le hinj u))
        (norm_nonneg Γ))
      (Real.sqrt_le_sqrt (encMat_mulVec_dotProduct_self_le hinj w))
      (Real.sqrt_nonneg _) (by positivity)
  · refine l2_opNorm_le_of_forall_dotProduct _ (norm_nonneg _) fun p q => ?_
    have h := abs_dotProduct_mulVec_le (zextMat encode Γ)
      (zextVec encode p) (zextVec encode q)
    rwa [dotProduct_zextMat_mulVec, encMat_mulVec_zextVec hinj,
      encMat_mulVec_zextVec hinj, zextVec_dotProduct_self hinj,
      zextVec_dotProduct_self hinj] at h

end Zext

/-! ## §7.1  Embedding a promise into a total input cube -/

section Embed

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {O : Type*}

lemma submatrix_advD_eq_advDOn (encode : X → ι → σ) (i : ι) :
    (advD (σ := σ) i).submatrix encode encode = advDOn encode i := rfl

/-- **An injectively encoded promise is no harder than the total problem.** -/
theorem advPMOn_le_advPM_of_injective {encode : X → ι → σ} {f : X → O}
    {g : (ι → σ) → O} (hinj : Function.Injective encode)
    (hout : ∀ x, f x = g (encode x)) :
    advPMOn encode f ≤ advPM g := by
  refine advPMOn_le fun Γ hΓ hmask => ?_
  have hadv : IsAdvMatrix g (zextMat encode Γ) := by
    refine ⟨zextMat_isHermitian hΓ.1, fun a b hab => ?_⟩
    refine zextMat_apply_eq_zero encode fun x y ha hb => ?_
    refine hΓ.2 x y ?_
    rw [hout x, hout y, ← ha, ← hb]
    exact hab
  have hmask' : ∀ i, ‖zextMat encode Γ ⊙ advD i‖ ≤ 1 := by
    intro i
    rw [zextMat_hadamard, submatrix_advD_eq_advDOn, norm_zextMat hinj]
    exact hmask i
  rw [← norm_zextMat hinj Γ]
  exact le_advPM hadv hmask'

end Embed

/-! ## §7.2  Query-local encodings -/

section Local

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {σ : Type*} [DecidableEq σ]
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {O : Type*} {read : X → ι → σ} {encode : X → κ → σ} {f : X → O}

/-- A target coordinate is *local* if it copies a single source coordinate at
every promise input, or is constant across the promise. -/
def IsLocalCoord (read : X → ι → σ) (encode : X → κ → σ) (j : κ) : Prop :=
  (∃ i, ∀ x, encode x j = read x i) ∨ ∀ x y, encode x j = encode y j

/-- A target coordinate reads one source coordinate or a
constant. -/
structure LocalEncoding (read : X → ι → σ) (encode : X → κ → σ) where
  /-- The source coordinate read by a target coordinate, if any. -/
  sourceAt : κ → Option ι
  /-- The value of a constant target coordinate. -/
  constAt : κ → σ
  /-- The defining equation of the encoding. -/
  apply_eq : ∀ x j, encode x j = (sourceAt j).elim (constAt j) (read x)

lemma LocalEncoding.isLocalCoord (E : LocalEncoding read encode) (j : κ) :
    IsLocalCoord read encode j := by
  cases hj : E.sourceAt j with
  | some i => exact Or.inl ⟨i, fun x => by rw [E.apply_eq x j, hj]; rfl⟩
  | none =>
      exact Or.inr fun x y => by
        rw [E.apply_eq x j, E.apply_eq y j, hj]
        rfl

/-- Every source coordinate reached by `sourceAt` is separated by the target
observations. -/
lemma LocalEncoding.read_eq_of_encode_eq (E : LocalEncoding read encode)
    (hsurj : ∀ i, ∃ j, E.sourceAt j = some i) {x y : X}
    (h : encode x = encode y) : read x = read y := by
  funext i
  obtain ⟨j, hj⟩ := hsurj i
  have hx : encode x j = read x i := by rw [E.apply_eq x j, hj]; rfl
  have hy : encode y j = read y i := by rw [E.apply_eq y j, hj]; rfl
  rw [← hx, ← hy, h]

/-- **Local encodings only make a problem harder.** -/
theorem advPMOn_mono_of_local
    (hdetEnc : ∀ x y, encode x = encode y → f x = f y)
    (hloc : ∀ j, IsLocalCoord read encode j) :
    advPMOn read f ≤ advPMOn encode f := by
  refine advPMOn_le fun Γ hΓ hmask => ?_
  refine le_advPMOn hdetEnc hΓ fun j => ?_
  rcases hloc j with ⟨i, hi⟩ | hc
  · have hEq : advDOn encode j = advDOn read i := by
      ext x y
      rw [advDOn_apply, advDOn_apply, hi x, hi y]
    rw [hEq]
    exact hmask i
  · have h0 : Γ ⊙ advDOn encode j = 0 := by
      ext x y
      rw [hadamard_advDOn_apply, if_pos (hc x y), Matrix.zero_apply]
    rw [h0, norm_zero]
    norm_num

theorem advPMOn_mono_localEncoding
    (hdetEnc : ∀ x y, encode x = encode y → f x = f y)
    (E : LocalEncoding read encode) :
    advPMOn read f ≤ advPMOn encode f :=
  advPMOn_mono_of_local hdetEnc E.isLocalCoord

theorem advPMOn_mono_localEncoding_of_surjective
    (hdet : ∀ x y, read x = read y → f x = f y)
    (E : LocalEncoding read encode)
    (hsurj : ∀ i, ∃ j, E.sourceAt j = some i) :
    advPMOn read f ≤ advPMOn encode f :=
  advPMOn_mono_of_local
    (fun x y h => hdet x y (E.read_eq_of_encode_eq hsurj h)) E.isLocalCoord

end Local

/-! ## §7.3  Boolean postprocessing of a richer output -/

section Post

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [DecidableEq σ]
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {O O' : Type*}

theorem advPMOn_postcompose_le {read : X → ι → σ} {g : X → O}
    (hdet : ∀ x y, read x = read y → g x = g y) (accept : O → O') :
    advPMOn read (fun x => accept (g x)) ≤ advPMOn read g := by
  refine advPMOn_le fun Γ hΓ hmask => ?_
  exact le_advPMOn hdet
    ⟨hΓ.1, fun x y hxy => hΓ.2 x y (congrArg accept hxy)⟩ hmask

variable [Fintype σ]

/-- **Postprocessing the output cannot increase the adversary bound.** -/
theorem advPM_postcompose_le {g : (ι → σ) → O} (accept : O → O') :
    advPM (fun x => accept (g x)) ≤ advPM g := by
  refine advPM_le fun Γ hΓ hmask => ?_
  exact le_advPM ⟨hΓ.1, fun x y hxy => hΓ.2 x y (congrArg accept hxy)⟩ hmask

end Post

end QuantumQueryComplexity
