import QuantumQueryComplexity.EDLower.Mask
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Grams of the assembled blocks

The Gram of each modified block collapses by orthogonality of the pattern
terms (`gram_blockTerm_*`) to a nonnegative combination of scheme
projectors (plus, for the pair-avoiding case, the two swap couplings):

* `gram_edBlockA` — `∑_T α_{|T|}² • schemeProd (T ∪ {b})`;
* `gram_edBlockB` — `∑_T α_{|T|}² • schemeProd (T ∪ {a})`;
* `gram_edBlockC` — `∑_T β_{|T|}² •` (four parts), `β_k := α_k − α_{k+1}`.

Also the norm/quadform infrastructure over scheme projectors: the full
powerset resolves the identity (`sum_powerset_schemeProd`), its quadform is
dominated (`sum_schemeProd_quadform_le`), and any subfamily combination is
bounded by its largest coefficient (`norm_schemeProd_combo_le`).
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-! ## Scheme-projector infrastructure -/

lemma sum_powerset_schemeProd [Nonempty σ] :
    (∑ S ∈ (Finset.univ : Finset ι).powerset, schemeProd (σ := σ) S) = 1 := by
  rw [Finset.sum_powerset, Finset.card_univ,
    show (∑ j ∈ Finset.range (Fintype.card ι + 1),
        ∑ T ∈ Finset.powersetCard j (Finset.univ : Finset ι),
          schemeProd (σ := σ) T)
      = ∑ j ∈ Finset.range (Fintype.card ι + 1),
          weightProj (σ := σ) (ι := ι) j from rfl,
    sum_weightProj]

lemma schemeProd_idem [Nonempty σ] (S : Finset ι) :
    schemeProd (σ := σ) S * schemeProd S = schemeProd S := by
  rw [schemeProd_mul, if_pos rfl]

/-- The quadform of the full scheme family is dominated by the identity. -/
lemma sum_schemeProd_quadform_le [Nonempty σ] (v : (ι → σ) → ℝ) :
    (∑ S ∈ (Finset.univ : Finset ι).powerset,
      (schemeProd (σ := σ) S *ᵥ v) ⬝ᵥ (schemeProd S *ᵥ v)) ≤ v ⬝ᵥ v := by
  rw [sum_proj_quadform _ (fun S _ => schemeProd_transpose S)
    (fun S _ => schemeProd_idem S) v, sum_powerset_schemeProd,
    Matrix.one_mulVec]

/-- Any subfamily's quadform is dominated as well. -/
lemma sum_schemeProd_quadform_le' [Nonempty σ] (𝒮 : Finset (Finset ι))
    (v : (ι → σ) → ℝ) :
    (∑ S ∈ 𝒮, (schemeProd (σ := σ) S *ᵥ v) ⬝ᵥ (schemeProd S *ᵥ v))
      ≤ v ⬝ᵥ v := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (fun S _ => Finset.mem_powerset.mpr (Finset.subset_univ S))
    fun S _ _ => dotProduct_self_nonneg _) (sum_schemeProd_quadform_le v)

/-- A nonnegative combination of scheme projectors over any subfamily has
norm at most its largest coefficient. -/
theorem norm_schemeProd_combo_le [Nonempty σ] (𝒮 : Finset (Finset ι))
    (c : Finset ι → ℝ) (hc : ∀ S ∈ 𝒮, 0 ≤ c S) {b : ℝ}
    (hb : ∀ S ∈ 𝒮, c S ≤ b) (hb0 : 0 ≤ b) :
    ‖∑ S ∈ 𝒮, c S • schemeProd (σ := σ) S‖ ≤ b :=
  norm_combo_le 𝒮 (fun S _ => schemeProd_transpose S)
    (fun S _ S' _ => schemeProd_mul S S')
    (fun v => sum_schemeProd_quadform_le' 𝒮 v) hc hb hb0

/-! ## Grams of the assembled blocks -/

/-- Collapsing a sum of block-term Grams by the diagonal δ. -/
private lemma gram_sum_collapse {a b : ι}
    (φ : σ → σ × σ → ℝ) (α : ℕ → ℝ) (𝒯 : Finset (Finset ι))
    (M : Finset ι → Matrix (ι → σ) (ι → σ) ℝ)
    (hδ : ∀ T ∈ 𝒯, ∀ U ∈ 𝒯,
      (blockTerm a b φ T)ᵀ * blockTerm a b φ U = if T = U then M T else 0) :
    (∑ T ∈ 𝒯, α T.card • blockTerm (σ := σ) a b φ T)ᵀ
      * (∑ U ∈ 𝒯, α U.card • blockTerm a b φ U)
    = ∑ T ∈ 𝒯, (α T.card * α T.card) • M T := by
  rw [Matrix.transpose_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_sum]
  rw [Finset.sum_congr rfl fun U hU =>
    show (blockTerm a b φ T)ᵀ * (α U.card • blockTerm a b φ U)
      = if T = U then α U.card • M T else 0 from by
      rw [Matrix.mul_smul, hδ T hT U hU]
      by_cases hTU : T = U
      · rw [if_pos hTU, if_pos hTU]
      · rw [if_neg hTU, if_neg hTU, smul_zero],
    Finset.sum_ite_eq 𝒯 T fun U => α U.card • M T, if_pos hT,
    smul_smul]

/-- The Gram of an `edBlockA`. -/
lemma gram_edBlockA [Nonempty σ] {i b : ι} (hib : i ≠ b) (α : ℕ → ℝ) :
    (edBlockA (σ := σ) i b α)ᵀ * edBlockA i b α
      = ∑ T ∈ ({i, b} : Finset ι)ᶜ.powerset,
          (α T.card * α T.card) • schemeProd (insert b T) := by
  rw [edBlockA]
  exact gram_sum_collapse edF' α _ _ fun T hT U hU =>
    gram_blockTerm_edF' hib (Finset.mem_powerset.mp hT)
      (Finset.mem_powerset.mp hU)

/-- The Gram of an `edBlockB`. -/
lemma gram_edBlockB [Nonempty σ] {a i : ι} (hai : a ≠ i) (α : ℕ → ℝ) :
    (edBlockB (σ := σ) a i α)ᵀ * edBlockB a i α
      = ∑ T ∈ ({a, i} : Finset ι)ᶜ.powerset,
          (α T.card * α T.card) • schemeProd (insert a T) := by
  rw [edBlockB]
  exact gram_sum_collapse edF'' α _ _ fun T hT U hU =>
    gram_blockTerm_edF'' hai (Finset.mem_powerset.mp hT)
      (Finset.mem_powerset.mp hU)

/-- Splitting the collision factor of a block term. -/
lemma blockTerm_edF_split (a b : ι) (T : Finset ι) :
    blockTerm (σ := σ) a b edF T
      = blockTerm a b edF0 T + blockTerm a b edF1 T := by
  ext x y
  rw [Matrix.add_apply, blockTerm, blockTerm, blockTerm, Matrix.of_apply,
    Matrix.of_apply, Matrix.of_apply, ← edF0_add_edF1]
  ring

/-- The four-part Gram target of the `edF`-blocks. -/
noncomputable def gramFour (a b : ι) (T : Finset ι) :
    Matrix (ι → σ) (ι → σ) ℝ :=
  schemeProd T + (schemeProd (insert a T) + schemeProd (insert b T)
    + ((schemeProd (insert a T)).submatrix id ⇑(swapInput (σ := σ) a b)
      + (schemeProd (insert b T)).submatrix id ⇑(swapInput (σ := σ) a b)))

/-- The Gram of two full `edF` block terms. -/
lemma gram_blockTerm_edF [Nonempty σ] {a b : ι} (hab : a ≠ b)
    {T U : Finset ι} (hT : T ⊆ ({a, b} : Finset ι)ᶜ)
    (hU : U ⊆ ({a, b} : Finset ι)ᶜ) :
    (blockTerm a b (edF (σ := σ)) T)ᵀ * blockTerm a b edF U
      = if T = U then gramFour a b T else 0 := by
  rw [blockTerm_edF_split, blockTerm_edF_split, Matrix.transpose_add,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    gram_blockTerm_edF0 hab hT hU, gram_blockTerm_edF0_edF1 hab,
    gram_blockTerm_edF1_edF0 hab, gram_blockTerm_edF1 hab hT hU]
  by_cases hTU : T = U
  · rw [if_pos hTU, if_pos hTU, if_pos hTU, gramFour]
    abel
  · rw [if_neg hTU, if_neg hTU, if_neg hTU]
    abel

/-- The Gram of an `edBlockC`. -/
lemma gram_edBlockC [Nonempty σ] {a b i : ι} (hab : a ≠ b) (α : ℕ → ℝ) :
    (edBlockC (σ := σ) a b i α)ᵀ * edBlockC a b i α
      = ∑ T ∈ (({a, b} : Finset ι)ᶜ.erase i).powerset,
          ((α T.card - α (T.card + 1)) * (α T.card - α (T.card + 1)))
            • gramFour a b T := by
  rw [edBlockC]
  exact gram_sum_collapse edF (fun k => α k - α (k + 1)) _ _ fun T hT U hU =>
    gram_blockTerm_edF hab
      ((Finset.mem_powerset.mp hT).trans (Finset.erase_subset _ _))
      ((Finset.mem_powerset.mp hU).trans (Finset.erase_subset _ _))

/-! ## Quadform bounds for the modified block family -/

private lemma mulVec_dotProduct_self {X : Type*} [Fintype X]
    (M : Matrix X X ℝ) (v : X → ℝ) :
    (M *ᵥ v) ⬝ᵥ (M *ᵥ v) = v ⬝ᵥ ((Mᵀ * M) *ᵥ v) := by
  calc (M *ᵥ v) ⬝ᵥ (M *ᵥ v)
      = v ᵥ* Mᵀ ⬝ᵥ (M *ᵥ v) := by rw [Matrix.vecMul_transpose]
    _ = v ⬝ᵥ (Mᵀ *ᵥ (M *ᵥ v)) := (Matrix.dotProduct_mulVec _ _ _).symm
    _ = v ⬝ᵥ ((Mᵀ * M) *ᵥ v) := by rw [Matrix.mulVec_mulVec]

private lemma quadform_sum_smul {X : Type*} [Fintype X] {J : Type*}
    (𝒯 : Finset J) (c : J → ℝ) (M : J → Matrix X X ℝ) (v : X → ℝ) :
    v ⬝ᵥ ((∑ T ∈ 𝒯, c T • M T) *ᵥ v)
      = ∑ T ∈ 𝒯, c T * (v ⬝ᵥ (M T *ᵥ v)) := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

private lemma quadform_schemeProd_nonneg [Nonempty σ] (S : Finset ι)
    (v : (ι → σ) → ℝ) : 0 ≤ v ⬝ᵥ (schemeProd (σ := σ) S *ᵥ v) := by
  rw [← proj_quadform (schemeProd_transpose S) (schemeProd_idem S) v]
  exact dotProduct_self_nonneg _

private lemma sum_quadform_schemeProd_le [Nonempty σ]
    (𝒮 : Finset (Finset ι)) (v : (ι → σ) → ℝ) :
    (∑ S ∈ 𝒮, v ⬝ᵥ (schemeProd (σ := σ) S *ᵥ v)) ≤ v ⬝ᵥ v := by
  rw [Finset.sum_congr rfl fun S (_ : S ∈ 𝒮) =>
    (proj_quadform (schemeProd_transpose S) (schemeProd_idem S) v).symm]
  exact sum_schemeProd_quadform_le' 𝒮 v

private lemma insert_injOn (a : ι) (𝒯 : Finset (Finset ι))
    (h𝒯 : ∀ T ∈ 𝒯, a ∉ T) :
    Set.InjOn (insert a) (𝒯 : Set (Finset ι)) := by
  intro T hT U hU h
  have h1 : (insert a T).erase a = (insert a U).erase a := by rw [h]
  rwa [Finset.erase_insert (h𝒯 T (Finset.mem_coe.mp hT)),
    Finset.erase_insert (h𝒯 U (Finset.mem_coe.mp hU))] at h1

private lemma sum_quadform_insert_le [Nonempty σ] (a : ι)
    (𝒯 : Finset (Finset ι)) (h𝒯 : ∀ T ∈ 𝒯, a ∉ T) (v : (ι → σ) → ℝ) :
    (∑ T ∈ 𝒯, v ⬝ᵥ (schemeProd (σ := σ) (insert a T) *ᵥ v)) ≤ v ⬝ᵥ v := by
  rw [← Finset.sum_image (f := fun S => v ⬝ᵥ (schemeProd (σ := σ) S *ᵥ v))
    (insert_injOn a 𝒯 h𝒯)]
  exact sum_quadform_schemeProd_le _ v

/-- The pair-containing reindex: summing a set function over
`(b, T ⊆ {i,b}ᶜ)` through `T ∪ {b}` counts each set once per element. -/
lemma sum_erase_powerset_insert {M : Type*} [AddCommMonoid M] (i : ι)
    (f : Finset ι → M) :
    (∑ b ∈ Finset.univ.erase i, ∑ T ∈ ({i, b} : Finset ι)ᶜ.powerset,
        f (insert b T))
      = ∑ S ∈ (Finset.univ.erase i).powerset, S.card • f S := by
  rw [Finset.sum_congr rfl fun S (_ : S ∈ (Finset.univ.erase i).powerset) =>
    show S.card • f S = ∑ b ∈ S, f S from by
      rw [Finset.sum_const]]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun q => ⟨insert q.1 q.2, q.1⟩)
    (fun q => ⟨q.2, q.1.erase q.2⟩) ?_ ?_ ?_ ?_ (fun q _ => rfl)
  · rintro ⟨b, T⟩ hq
    rw [Finset.mem_sigma] at hq ⊢
    obtain ⟨hb, hT⟩ := hq
    have hT' := Finset.mem_powerset.mp hT
    refine ⟨Finset.mem_powerset.mpr fun c hc => ?_, Finset.mem_insert_self _ _⟩
    rcases Finset.mem_insert.mp hc with h | h
    · rw [h]; exact hb
    · have := hT' h
      refine Finset.mem_erase.mpr ⟨fun hci => ?_, Finset.mem_univ _⟩
      exact (Finset.mem_compl.mp this) (by
        rw [hci]; exact Finset.mem_insert_self i {b})
  · rintro ⟨S, c⟩ hq
    rw [Finset.mem_sigma] at hq ⊢
    obtain ⟨hS, hc⟩ := hq
    have hS' := Finset.mem_powerset.mp hS
    refine ⟨hS' hc, Finset.mem_powerset.mpr fun d hd => ?_⟩
    obtain ⟨hdc, hdS⟩ := Finset.mem_erase.mp hd
    have hdi : d ≠ i := (Finset.mem_erase.mp (hS' hdS)).1
    refine Finset.mem_compl.mpr fun hdpair => ?_
    rcases Finset.mem_insert.mp hdpair with h | h
    · exact hdi h
    · exact hdc (Finset.mem_singleton.mp h)
  · rintro ⟨b, T⟩ hq
    rw [Finset.mem_sigma] at hq
    have hbT : b ∉ T := fun h =>
      (Finset.mem_compl.mp (Finset.mem_powerset.mp hq.2 h))
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
    simp only [Finset.erase_insert hbT]
  · rintro ⟨S, c⟩ hq
    rw [Finset.mem_sigma] at hq
    simp only [Finset.insert_erase hq.2]

/-- Bound for the pairs whose first element is the queried cell. -/
private lemma boundA [Nonempty σ] (i : ι) (α : ℕ → ℝ) {A : ℝ}
    (hA : ∀ k : ℕ, ((k : ℝ) + 1) * (α k * α k) ≤ A) (hA0 : 0 ≤ A)
    (v : (ι → σ) → ℝ) :
    (∑ b ∈ Finset.univ.erase i,
      v ⬝ᵥ (((edBlockA (σ := σ) i b α)ᵀ * edBlockA i b α) *ᵥ v))
      ≤ A * (v ⬝ᵥ v) := by
  have hstep : ∀ b ∈ Finset.univ.erase i,
      v ⬝ᵥ (((edBlockA (σ := σ) i b α)ᵀ * edBlockA i b α) *ᵥ v)
      = ∑ T ∈ ({i, b} : Finset ι)ᶜ.powerset,
          (fun S => α (S.card - 1) * α (S.card - 1)
            * (v ⬝ᵥ (schemeProd (σ := σ) S *ᵥ v))) (insert b T) := by
    intro b hb
    have hib : i ≠ b := fun h => (Finset.mem_erase.mp hb).1 h.symm
    rw [gram_edBlockA hib α, quadform_sum_smul]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hbT : b ∉ T := fun h =>
      (Finset.mem_compl.mp (Finset.mem_powerset.mp hT h))
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
    simp only
    rw [Finset.card_insert_of_notMem hbT, Nat.add_sub_cancel]
  rw [Finset.sum_congr rfl hstep,
    sum_erase_powerset_insert i (fun S => α (S.card - 1) * α (S.card - 1)
      * (v ⬝ᵥ (schemeProd (σ := σ) S *ᵥ v)))]
  have hbound : ∀ S ∈ (Finset.univ.erase i).powerset,
      S.card • (α (S.card - 1) * α (S.card - 1)
        * (v ⬝ᵥ (schemeProd (σ := σ) S *ᵥ v)))
      ≤ A * (v ⬝ᵥ (schemeProd (σ := σ) S *ᵥ v)) := by
    intro S _
    rw [nsmul_eq_mul, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (quadform_schemeProd_nonneg S v)
    rcases Nat.eq_zero_or_pos S.card with h0 | hpos
    · rw [h0]
      simpa using hA0
    · have h1 : S.card = (S.card - 1) + 1 := by omega
      calc (S.card : ℝ) * (α (S.card - 1) * α (S.card - 1))
          = (((S.card - 1 : ℕ) : ℝ) + 1)
              * (α (S.card - 1) * α (S.card - 1)) := by
            rw [show ((S.card : ℕ) : ℝ) = ((S.card - 1 : ℕ) : ℝ) + 1 from by
              exact_mod_cast congrArg (Nat.cast (R := ℝ)) h1]
        _ ≤ A := hA (S.card - 1)
  calc (∑ S ∈ (Finset.univ.erase i).powerset,
      S.card • (α (S.card - 1) * α (S.card - 1)
        * (v ⬝ᵥ (schemeProd (σ := σ) S *ᵥ v))))
      ≤ ∑ S ∈ (Finset.univ.erase i).powerset,
          A * (v ⬝ᵥ (schemeProd (σ := σ) S *ᵥ v)) :=
        Finset.sum_le_sum hbound
    _ = A * ∑ S ∈ (Finset.univ.erase i).powerset,
          (v ⬝ᵥ (schemeProd (σ := σ) S *ᵥ v)) := by rw [Finset.mul_sum]
    _ ≤ A * (v ⬝ᵥ v) :=
        mul_le_mul_of_nonneg_left (sum_quadform_schemeProd_le _ v) hA0

/-- Bound for the pairs whose second element is the queried cell. -/
private lemma boundB [Nonempty σ] (i : ι) (α : ℕ → ℝ) {A : ℝ}
    (hA : ∀ k : ℕ, ((k : ℝ) + 1) * (α k * α k) ≤ A) (hA0 : 0 ≤ A)
    (v : (ι → σ) → ℝ) :
    (∑ a ∈ Finset.univ.erase i,
      v ⬝ᵥ (((edBlockB (σ := σ) a i α)ᵀ * edBlockB a i α) *ᵥ v))
      ≤ A * (v ⬝ᵥ v) := by
  have hstep : ∀ a ∈ Finset.univ.erase i,
      v ⬝ᵥ (((edBlockB (σ := σ) a i α)ᵀ * edBlockB a i α) *ᵥ v)
      = ∑ T ∈ ({i, a} : Finset ι)ᶜ.powerset,
          (fun S => α (S.card - 1) * α (S.card - 1)
            * (v ⬝ᵥ (schemeProd (σ := σ) S *ᵥ v))) (insert a T) := by
    intro a ha
    have hai : a ≠ i := (Finset.mem_erase.mp ha).1
    rw [gram_edBlockB hai α, quadform_sum_smul]
    rw [show ({a, i} : Finset ι)ᶜ = ({i, a} : Finset ι)ᶜ from by
      rw [Finset.pair_comm]]
    refine Finset.sum_congr rfl fun T hT => ?_
    have haT : a ∉ T := fun h =>
      (Finset.mem_compl.mp (Finset.mem_powerset.mp hT h))
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self a))
    simp only
    rw [Finset.card_insert_of_notMem haT, Nat.add_sub_cancel]
  rw [Finset.sum_congr rfl hstep,
    sum_erase_powerset_insert i (fun S => α (S.card - 1) * α (S.card - 1)
      * (v ⬝ᵥ (schemeProd (σ := σ) S *ᵥ v)))]
  have hbound : ∀ S ∈ (Finset.univ.erase i).powerset,
      S.card • (α (S.card - 1) * α (S.card - 1)
        * (v ⬝ᵥ (schemeProd (σ := σ) S *ᵥ v)))
      ≤ A * (v ⬝ᵥ (schemeProd (σ := σ) S *ᵥ v)) := by
    intro S _
    rw [nsmul_eq_mul, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (quadform_schemeProd_nonneg S v)
    rcases Nat.eq_zero_or_pos S.card with h0 | hpos
    · rw [h0]
      simpa using hA0
    · have h1 : S.card = (S.card - 1) + 1 := by omega
      calc (S.card : ℝ) * (α (S.card - 1) * α (S.card - 1))
          = (((S.card - 1 : ℕ) : ℝ) + 1)
              * (α (S.card - 1) * α (S.card - 1)) := by
            rw [show ((S.card : ℕ) : ℝ) = ((S.card - 1 : ℕ) : ℝ) + 1 from by
              exact_mod_cast congrArg (Nat.cast (R := ℝ)) h1]
        _ ≤ A := hA (S.card - 1)
  calc (∑ S ∈ (Finset.univ.erase i).powerset,
      S.card • (α (S.card - 1) * α (S.card - 1)
        * (v ⬝ᵥ (schemeProd (σ := σ) S *ᵥ v))))
      ≤ ∑ S ∈ (Finset.univ.erase i).powerset,
          A * (v ⬝ᵥ (schemeProd (σ := σ) S *ᵥ v)) :=
        Finset.sum_le_sum hbound
    _ = A * ∑ S ∈ (Finset.univ.erase i).powerset,
          (v ⬝ᵥ (schemeProd (σ := σ) S *ᵥ v)) := by rw [Finset.mul_sum]
    _ ≤ A * (v ⬝ᵥ v) :=
        mul_le_mul_of_nonneg_left (sum_quadform_schemeProd_le _ v) hA0

/-! ## The pair-avoiding bound -/

private lemma quadform_le_norm {X : Type*} [Fintype X] [DecidableEq X]
    (M : Matrix X X ℝ) (v : X → ℝ) :
    v ⬝ᵥ (M *ᵥ v) ≤ ‖M‖ * (v ⬝ᵥ v) := by
  refine le_trans (le_abs_self _) ?_
  refine le_trans (abs_dotProduct_mulVec_le M v v) ?_
  rw [mul_assoc, Real.mul_self_sqrt (dotProduct_self_nonneg v)]

private lemma submatrix_sum_smul {X : Type*} [Fintype X] {J : Type*}
    (𝒯 : Finset J) (c : J → ℝ) (M : J → Matrix X X ℝ) (e : X → X) :
    (∑ T ∈ 𝒯, c T • M T).submatrix id e
      = ∑ T ∈ 𝒯, c T • (M T).submatrix id e := by
  ext x y
  rw [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Matrix.smul_apply, Matrix.smul_apply, Matrix.submatrix_apply]

/-- The norm of a `β²`-combination of inserted scheme projectors. -/
private lemma norm_insert_combo_le [Nonempty σ] (a : ι) (α : ℕ → ℝ) {B : ℝ}
    (hB : ∀ k : ℕ, (α k - α (k + 1)) * (α k - α (k + 1)) ≤ B) (hB0 : 0 ≤ B)
    (𝒯 : Finset (Finset ι)) (h𝒯 : ∀ T ∈ 𝒯, a ∉ T) :
    ‖∑ T ∈ 𝒯, ((α T.card - α (T.card + 1)) * (α T.card - α (T.card + 1)))
      • schemeProd (σ := σ) (insert a T)‖ ≤ B := by
  have hre : (∑ T ∈ 𝒯,
      ((α T.card - α (T.card + 1)) * (α T.card - α (T.card + 1)))
        • schemeProd (σ := σ) (insert a T))
      = ∑ S ∈ 𝒯.image (insert a),
          ((α (S.card - 1) - α S.card) * (α (S.card - 1) - α S.card))
            • schemeProd (σ := σ) S := by
    rw [Finset.sum_image (f := fun S =>
        ((α (S.card - 1) - α S.card) * (α (S.card - 1) - α S.card))
          • schemeProd (σ := σ) S)
      (insert_injOn a 𝒯 h𝒯)]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.card_insert_of_notMem (h𝒯 T hT), Nat.add_sub_cancel]
  rw [hre]
  refine norm_schemeProd_combo_le _ _ (fun S _ => mul_self_nonneg _)
    (fun S hS => ?_) hB0
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
  rw [Finset.card_insert_of_notMem (h𝒯 T hT), Nat.add_sub_cancel]
  exact hB T.card

/-- **The per-pair bound for pairs avoiding the queried cell.** -/
private lemma boundC [Nonempty σ] (i : ι) (α : ℕ → ℝ) {B : ℝ}
    (hB : ∀ k : ℕ, (α k - α (k + 1)) * (α k - α (k + 1)) ≤ B) (hB0 : 0 ≤ B)
    (v : (ι → σ) → ℝ) {a b : ι} (hab : a ≠ b) :
    v ⬝ᵥ (((edBlockC (σ := σ) a b i α)ᵀ * edBlockC a b i α) *ᵥ v)
      ≤ 5 * B * (v ⬝ᵥ v) := by
  rw [gram_edBlockC hab α, quadform_sum_smul]
  set 𝒯 := (({a, b} : Finset ι)ᶜ.erase i).powerset with h𝒯def
  have h𝒯a : ∀ T ∈ 𝒯, a ∉ T := fun T hT h =>
    (Finset.mem_compl.mp
      ((Finset.mem_powerset.mp hT).trans (Finset.erase_subset _ _) h))
      (Finset.mem_insert_self a {b})
  have h𝒯b : ∀ T ∈ 𝒯, b ∉ T := fun T hT h =>
    (Finset.mem_compl.mp
      ((Finset.mem_powerset.mp hT).trans (Finset.erase_subset _ _) h))
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  have hβ : ∀ T : Finset ι,
      0 ≤ (α T.card - α (T.card + 1)) * (α T.card - α (T.card + 1)) :=
    fun T => mul_self_nonneg _
  have hqf4 : ∀ T : Finset ι, v ⬝ᵥ (gramFour (σ := σ) a b T *ᵥ v)
      = v ⬝ᵥ (schemeProd T *ᵥ v)
        + (v ⬝ᵥ (schemeProd (insert a T) *ᵥ v)
          + v ⬝ᵥ (schemeProd (insert b T) *ᵥ v)
          + (v ⬝ᵥ ((schemeProd (insert a T)).submatrix id
              ⇑(swapInput (σ := σ) a b) *ᵥ v)
            + v ⬝ᵥ ((schemeProd (insert b T)).submatrix id
              ⇑(swapInput (σ := σ) a b) *ᵥ v))) := by
    intro T
    rw [gramFour, Matrix.add_mulVec, dotProduct_add, Matrix.add_mulVec,
      dotProduct_add, Matrix.add_mulVec, dotProduct_add, Matrix.add_mulVec,
      dotProduct_add]
  rw [Finset.sum_congr rfl fun T (_ : T ∈ 𝒯) =>
    show ((α T.card - α (T.card + 1)) * (α T.card - α (T.card + 1)))
        * (v ⬝ᵥ (gramFour (σ := σ) a b T *ᵥ v))
      = ((α T.card - α (T.card + 1)) * (α T.card - α (T.card + 1)))
          * (v ⬝ᵥ (schemeProd T *ᵥ v))
        + ((α T.card - α (T.card + 1)) * (α T.card - α (T.card + 1)))
          * (v ⬝ᵥ (schemeProd (insert a T) *ᵥ v))
        + ((α T.card - α (T.card + 1)) * (α T.card - α (T.card + 1)))
          * (v ⬝ᵥ (schemeProd (insert b T) *ᵥ v))
        + (((α T.card - α (T.card + 1)) * (α T.card - α (T.card + 1)))
          * (v ⬝ᵥ ((schemeProd (insert a T)).submatrix id
              ⇑(swapInput (σ := σ) a b) *ᵥ v))
        + ((α T.card - α (T.card + 1)) * (α T.card - α (T.card + 1)))
          * (v ⬝ᵥ ((schemeProd (insert b T)).submatrix id
              ⇑(swapInput (σ := σ) a b) *ᵥ v))) from by
      rw [hqf4 T]
      ring,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hS1 : (∑ T ∈ 𝒯,
      ((α T.card - α (T.card + 1)) * (α T.card - α (T.card + 1)))
        * (v ⬝ᵥ (schemeProd (σ := σ) T *ᵥ v))) ≤ B * (v ⬝ᵥ v) := by
    calc (∑ T ∈ 𝒯,
        ((α T.card - α (T.card + 1)) * (α T.card - α (T.card + 1)))
          * (v ⬝ᵥ (schemeProd (σ := σ) T *ᵥ v)))
        ≤ ∑ T ∈ 𝒯, B * (v ⬝ᵥ (schemeProd (σ := σ) T *ᵥ v)) :=
          Finset.sum_le_sum fun T _ => mul_le_mul_of_nonneg_right
            (hB T.card) (quadform_schemeProd_nonneg T v)
      _ = B * ∑ T ∈ 𝒯, (v ⬝ᵥ (schemeProd (σ := σ) T *ᵥ v)) := by
          rw [Finset.mul_sum]
      _ ≤ B * (v ⬝ᵥ v) :=
          mul_le_mul_of_nonneg_left (sum_quadform_schemeProd_le _ v) hB0
  have hS2 : (∑ T ∈ 𝒯,
      ((α T.card - α (T.card + 1)) * (α T.card - α (T.card + 1)))
        * (v ⬝ᵥ (schemeProd (σ := σ) (insert a T) *ᵥ v))) ≤ B * (v ⬝ᵥ v) := by
    calc (∑ T ∈ 𝒯,
        ((α T.card - α (T.card + 1)) * (α T.card - α (T.card + 1)))
          * (v ⬝ᵥ (schemeProd (σ := σ) (insert a T) *ᵥ v)))
        ≤ ∑ T ∈ 𝒯, B * (v ⬝ᵥ (schemeProd (σ := σ) (insert a T) *ᵥ v)) :=
          Finset.sum_le_sum fun T _ => mul_le_mul_of_nonneg_right
            (hB T.card) (quadform_schemeProd_nonneg _ v)
      _ = B * ∑ T ∈ 𝒯, (v ⬝ᵥ (schemeProd (σ := σ) (insert a T) *ᵥ v)) := by
          rw [Finset.mul_sum]
      _ ≤ B * (v ⬝ᵥ v) :=
          mul_le_mul_of_nonneg_left (sum_quadform_insert_le a 𝒯 h𝒯a v) hB0
  have hS3 : (∑ T ∈ 𝒯,
      ((α T.card - α (T.card + 1)) * (α T.card - α (T.card + 1)))
        * (v ⬝ᵥ (schemeProd (σ := σ) (insert b T) *ᵥ v))) ≤ B * (v ⬝ᵥ v) := by
    calc (∑ T ∈ 𝒯,
        ((α T.card - α (T.card + 1)) * (α T.card - α (T.card + 1)))
          * (v ⬝ᵥ (schemeProd (σ := σ) (insert b T) *ᵥ v)))
        ≤ ∑ T ∈ 𝒯, B * (v ⬝ᵥ (schemeProd (σ := σ) (insert b T) *ᵥ v)) :=
          Finset.sum_le_sum fun T _ => mul_le_mul_of_nonneg_right
            (hB T.card) (quadform_schemeProd_nonneg _ v)
      _ = B * ∑ T ∈ 𝒯, (v ⬝ᵥ (schemeProd (σ := σ) (insert b T) *ᵥ v)) := by
          rw [Finset.mul_sum]
      _ ≤ B * (v ⬝ᵥ v) :=
          mul_le_mul_of_nonneg_left (sum_quadform_insert_le b 𝒯 h𝒯b v) hB0
  have hswap : ∀ (c : ι), (∀ T ∈ 𝒯, c ∉ T) →
      (∑ T ∈ 𝒯,
        ((α T.card - α (T.card + 1)) * (α T.card - α (T.card + 1)))
          * (v ⬝ᵥ ((schemeProd (σ := σ) (insert c T)).submatrix id
            ⇑(swapInput (σ := σ) a b) *ᵥ v))) ≤ B * (v ⬝ᵥ v) := by
    intro c h𝒯c
    rw [← quadform_sum_smul 𝒯 _
      (fun T => (schemeProd (σ := σ) (insert c T)).submatrix id
        ⇑(swapInput (σ := σ) a b)) v,
      ← submatrix_sum_smul]
    refine le_trans (quadform_le_norm _ v) ?_
    refine mul_le_mul_of_nonneg_right ?_ (dotProduct_self_nonneg v)
    refine le_trans (l2_opNorm_submatrix_id_le _ (swapInput (σ := σ) a b)) ?_
    exact norm_insert_combo_le c α hB hB0 𝒯 h𝒯c
  have hS4 := hswap a h𝒯a
  have hS5 := hswap b h𝒯b
  linarith

/-! ## The master quadform bound -/

/-- The modified block of an ordered pair, as a function of the raw pair. -/
noncomputable def edBlockModPair (i : ι) (α : ℕ → ℝ) (q : ι × ι) :
    Matrix (ι → σ) (ι → σ) ℝ :=
  if i = q.1 then edBlockA q.1 q.2 α
  else if i = q.2 then edBlockB q.1 q.2 α
  else edBlockC q.1 q.2 i α

/-- The `Δ_i`-modified block family. -/
noncomputable def edBlockMod (i : ι) (α : ℕ → ℝ)
    (p : {q : ι × ι // q.1 ≠ q.2}) : Matrix (ι → σ) (ι → σ) ℝ :=
  edBlockModPair i α p.1

/-- **The summed Gram bound for the modified family**: the paper's (8) and
(9) combined, with explicit constants. -/
theorem quadform_edBlockMod_le [Nonempty σ] (i : ι) (α : ℕ → ℝ)
    {A B : ℝ} (hA : ∀ k : ℕ, ((k : ℝ) + 1) * (α k * α k) ≤ A)
    (hB : ∀ k : ℕ, (α k - α (k + 1)) * (α k - α (k + 1)) ≤ B)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (v : (ι → σ) → ℝ) :
    (∑ p : {q : ι × ι // q.1 ≠ q.2},
      (edBlockMod (σ := σ) i α p *ᵥ v) ⬝ᵥ (edBlockMod i α p *ᵥ v))
      ≤ (2 * A + 5 * (Fintype.card ι : ℝ) ^ 2 * B) * (v ⬝ᵥ v) := by
  have h1 : (∑ p : {q : ι × ι // q.1 ≠ q.2},
      (edBlockMod (σ := σ) i α p *ᵥ v) ⬝ᵥ (edBlockMod i α p *ᵥ v))
      = ∑ q ∈ Finset.univ.filter (fun q : ι × ι => q.1 ≠ q.2),
          v ⬝ᵥ (((edBlockModPair (σ := σ) i α q)ᵀ
            * edBlockModPair i α q) *ᵥ v) := by
    rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) =>
      mulVec_dotProduct_self (edBlockMod (σ := σ) i α p) v]
    exact (Finset.sum_subtype
      (Finset.univ.filter fun q : ι × ι => q.1 ≠ q.2)
      (fun q => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ q)))
      (fun q => v ⬝ᵥ (((edBlockModPair (σ := σ) i α q)ᵀ
        * edBlockModPair i α q) *ᵥ v))).symm
  rw [h1, ← Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter fun q : ι × ι => q.1 ≠ q.2) (fun q => q.1 = i),
    ← Finset.sum_filter_add_sum_filter_not
    ((Finset.univ.filter fun q : ι × ι => q.1 ≠ q.2).filter
      fun q => ¬ q.1 = i) (fun q => q.2 = i)]
  have hSa : (∑ q ∈ (Finset.univ.filter fun q : ι × ι => q.1 ≠ q.2).filter
      (fun q => q.1 = i),
      v ⬝ᵥ (((edBlockModPair (σ := σ) i α q)ᵀ * edBlockModPair i α q) *ᵥ v))
      = ∑ b ∈ Finset.univ.erase i,
          v ⬝ᵥ (((edBlockA (σ := σ) i b α)ᵀ * edBlockA i b α) *ᵥ v) := by
    refine Finset.sum_nbij' (fun q => q.2) (fun b => (i, b)) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
      obtain ⟨-, hne⟩ := Finset.mem_filter.mp hq1
      exact Finset.mem_erase.mpr
        ⟨fun h => hne (by rw [hq2, h]), Finset.mem_univ _⟩
    · intro b hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        fun h => (Finset.mem_erase.mp hb).1 h.symm⟩, rfl⟩
    · intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
      rw [← hq2]
    · intro b hb
      rfl
    · intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
      rw [edBlockModPair, if_pos hq2.symm, hq2]
  have hSb : (∑ q ∈ ((Finset.univ.filter fun q : ι × ι => q.1 ≠ q.2).filter
      (fun q => ¬ q.1 = i)).filter (fun q => q.2 = i),
      v ⬝ᵥ (((edBlockModPair (σ := σ) i α q)ᵀ * edBlockModPair i α q) *ᵥ v))
      = ∑ a ∈ Finset.univ.erase i,
          v ⬝ᵥ (((edBlockB (σ := σ) a i α)ᵀ * edBlockB a i α) *ᵥ v) := by
    refine Finset.sum_nbij' (fun q => q.1) (fun a => (a, i)) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
      obtain ⟨-, hne1⟩ := Finset.mem_filter.mp hq1
      exact Finset.mem_erase.mpr ⟨hne1, Finset.mem_univ _⟩
    · intro a ha
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          fun h => (Finset.mem_erase.mp ha).1 h⟩,
        (Finset.mem_erase.mp ha).1⟩, rfl⟩
    · intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
      rw [← hq2]
    · intro a ha
      rfl
    · intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
      obtain ⟨-, hne1⟩ := Finset.mem_filter.mp hq1
      rw [edBlockModPair, if_neg (fun h => hne1 h.symm), if_pos hq2.symm, hq2]
  have hSc : (∑ q ∈ ((Finset.univ.filter fun q : ι × ι => q.1 ≠ q.2).filter
      (fun q => ¬ q.1 = i)).filter (fun q => ¬ q.2 = i),
      v ⬝ᵥ (((edBlockModPair (σ := σ) i α q)ᵀ * edBlockModPair i α q) *ᵥ v))
      ≤ (Fintype.card ι : ℝ) ^ 2 * (5 * B * (v ⬝ᵥ v)) := by
    have h5B : (0 : ℝ) ≤ 5 * B * (v ⬝ᵥ v) :=
      mul_nonneg (mul_nonneg (by norm_num) hB0) (dotProduct_self_nonneg v)
    have hper : ∀ q ∈ ((Finset.univ.filter fun q : ι × ι => q.1 ≠ q.2).filter
        (fun q => ¬ q.1 = i)).filter (fun q => ¬ q.2 = i),
        v ⬝ᵥ (((edBlockModPair (σ := σ) i α q)ᵀ
          * edBlockModPair i α q) *ᵥ v) ≤ 5 * B * (v ⬝ᵥ v) := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
      obtain ⟨hq3, hq4⟩ := Finset.mem_filter.mp hq1
      obtain ⟨-, hne⟩ := Finset.mem_filter.mp hq3
      rw [edBlockModPair, if_neg (fun h => hq4 h.symm),
        if_neg (fun h => hq2 h.symm)]
      exact boundC i α hB hB0 v hne
    calc (∑ q ∈ ((Finset.univ.filter fun q : ι × ι => q.1 ≠ q.2).filter
        (fun q => ¬ q.1 = i)).filter (fun q => ¬ q.2 = i),
        v ⬝ᵥ (((edBlockModPair (σ := σ) i α q)ᵀ
          * edBlockModPair i α q) *ᵥ v))
        ≤ (((Finset.univ.filter fun q : ι × ι => q.1 ≠ q.2).filter
            (fun q => ¬ q.1 = i)).filter (fun q => ¬ q.2 = i)).card
            • (5 * B * (v ⬝ᵥ v)) :=
          Finset.sum_le_card_nsmul _ _ _ hper
      _ ≤ (Fintype.card ι : ℝ) ^ 2 * (5 * B * (v ⬝ᵥ v)) := by
          rw [nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ h5B
          have hcard : (((Finset.univ.filter fun q : ι × ι => q.1 ≠ q.2).filter
              (fun q => ¬ q.1 = i)).filter (fun q => ¬ q.2 = i)).card
              ≤ Fintype.card ι * Fintype.card ι := by
            calc (((Finset.univ.filter fun q : ι × ι => q.1 ≠ q.2).filter
                (fun q => ¬ q.1 = i)).filter (fun q => ¬ q.2 = i)).card
                ≤ ((Finset.univ.filter fun q : ι × ι => q.1 ≠ q.2).filter
                    (fun q => ¬ q.1 = i)).card := Finset.card_filter_le _ _
              _ ≤ (Finset.univ.filter fun q : ι × ι => q.1 ≠ q.2).card :=
                  Finset.card_filter_le _ _
              _ ≤ (Finset.univ : Finset (ι × ι)).card :=
                  Finset.card_filter_le _ _
              _ = Fintype.card ι * Fintype.card ι := by
                  rw [Finset.card_univ, Fintype.card_prod]
          rw [pow_two]
          exact_mod_cast hcard
  rw [hSa, hSb]
  have hbA := boundA i α hA hA0 v
  have hbB := boundB i α hA hA0 v
  nlinarith [hSc, hbA, hbB]

end QuantumQueryComplexity
