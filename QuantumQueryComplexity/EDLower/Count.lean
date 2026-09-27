import QuantumQueryComplexity.EDLower.Gee
import QuantumQueryComplexity.EDLower.PairOps
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Counting injective extensions

The workhorse of the positive side of the lower bound: the number of
injective functions `ι → σ` extending a prescribed injective assignment on
a cell set `C` is the falling factorial

    ∏_{j < n - |C|} (q - |C| - j)

— in particular it depends only on `|C|`, which is the uniformity that turns
the legal entry sums into `gee`-sums.  Instantiated at `C = ∅` it counts the
injective columns; instantiated at `ι := Fin k` it counts injective tuples.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The number of injective extensions of an injective partial assignment is
the falling factorial, independently of the prescribed values. -/
lemma card_injective_extensions (C : Finset ι) (z : ι → σ)
    (hz : Set.InjOn z (C : Set ι)) :
    ((Finset.univ.filter fun y : ι → σ =>
      Function.Injective y ∧ ∀ c ∈ C, y c = z c)).card
    = ∏ j ∈ Finset.range (Fintype.card ι - C.card),
        (Fintype.card σ - C.card - j) := by
  induction hn : Fintype.card ι - C.card using Nat.strong_induction_on
    generalizing C z with
  | _ n IH =>
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · -- no free cells: `C = univ`, the only candidate is `z` itself
    subst h0
    have hCcard : C.card = Fintype.card ι := by
      have h1 := Finset.card_le_card (Finset.subset_univ C)
      rw [Finset.card_univ] at h1
      omega
    have hCuniv : C = Finset.univ := Finset.eq_univ_of_card C hCcard
    have hzinj : Function.Injective z := by
      rw [hCuniv, Finset.coe_univ] at hz
      exact Set.injOn_univ.mp hz
    rw [show (Finset.univ.filter fun y : ι → σ =>
        Function.Injective y ∧ ∀ c ∈ C, y c = z c) = {z} from by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨-, hy⟩
        exact funext fun c => hy c (hCuniv ▸ Finset.mem_univ c)
      · rintro rfl
        exact ⟨hzinj, fun c _ => rfl⟩,
      Finset.card_singleton, Finset.range_zero, Finset.prod_empty]
  · -- pick a free cell and partition by its value
    have hCne : C ≠ Finset.univ := fun h => by
      rw [h, Finset.card_univ] at hn
      omega
    obtain ⟨d, hd⟩ : ∃ d, d ∉ C := by
      by_contra hall
      push_neg at hall
      exact hCne (Finset.eq_univ_iff_forall.mpr hall)
    have hmaps : ∀ y ∈ Finset.univ.filter (fun y : ι → σ =>
        Function.Injective y ∧ ∀ c ∈ C, y c = z c),
        y d ∈ Finset.univ \ C.image z := by
      intro y hy
      obtain ⟨hyinj, hyz⟩ := (Finset.mem_filter.mp hy).2
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hmem => ?_⟩
      obtain ⟨c, hc, hcz⟩ := Finset.mem_image.mp hmem
      exact hd (by
        rw [show d = c from hyinj (by rw [hyz c hc, hcz])]
        exact hc)
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    have hfiber : ∀ v ∈ Finset.univ \ C.image z,
        ((Finset.univ.filter fun y : ι → σ =>
          Function.Injective y ∧ ∀ c ∈ C, y c = z c).filter
          fun y => y d = v).card
        = ∏ j ∈ Finset.range (n - 1),
            (Fintype.card σ - (C.card + 1) - j) := by
      intro v hv
      have hvz : v ∉ C.image z := (Finset.mem_sdiff.mp hv).2
      have hset : ((Finset.univ.filter fun y : ι → σ =>
          Function.Injective y ∧ ∀ c ∈ C, y c = z c).filter
          fun y => y d = v)
          = Finset.univ.filter fun y : ι → σ =>
              Function.Injective y ∧
                ∀ c ∈ insert d C, y c = Function.update z d v c := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨hyinj, hyz⟩, hyd⟩
          refine ⟨hyinj, fun c hc => ?_⟩
          rcases Finset.mem_insert.mp hc with h | h
          · rw [h, Function.update_self, hyd]
          · rw [Function.update_of_ne (show c ≠ d from fun hcd =>
              hd (by rw [← hcd]; exact h)) v z, hyz c h]
        · rintro ⟨hyinj, hy⟩
          refine ⟨⟨hyinj, fun c hc => ?_⟩, ?_⟩
          · have := hy c (Finset.mem_insert_of_mem hc)
            rwa [Function.update_of_ne (show c ≠ d from fun hcd =>
              hd (by rw [← hcd]; exact hc)) v z] at this
          · have := hy d (Finset.mem_insert_self d C)
            rwa [Function.update_self] at this
      have hz' : Set.InjOn (Function.update z d v)
          ((insert d C : Finset ι) : Set ι) := by
        intro u hu w hw huw
        rw [Finset.mem_coe, Finset.mem_insert] at hu hw
        rcases hu with hu | hu <;> rcases hw with hw | hw
        · rw [hu, hw]
        · rw [hu, Function.update_self,
            Function.update_of_ne (show w ≠ d from fun h =>
              hd (by rw [← h]; exact hw)) v z] at huw
          exact absurd (Finset.mem_image_of_mem z hw) (huw ▸ hvz)
        · rw [hw, Function.update_self,
            Function.update_of_ne (show u ≠ d from fun h =>
              hd (by rw [← h]; exact hu)) v z] at huw
          exact absurd (Finset.mem_image_of_mem z hu) (huw.symm ▸ hvz)
        · rw [Function.update_of_ne (show u ≠ d from fun h =>
              hd (by rw [← h]; exact hu)) v z,
            Function.update_of_ne (show w ≠ d from fun h =>
              hd (by rw [← h]; exact hw)) v z] at huw
          exact hz hu hw huw
      have hcard' : Fintype.card ι - (insert d C).card = n - 1 := by
        rw [Finset.card_insert_of_notMem hd]
        omega
      rw [hset, IH (n - 1) (by omega) (insert d C)
        (Function.update z d v) hz' hcard',
        Finset.card_insert_of_notMem hd]
    rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul]
    have hcardv : (Finset.univ \ C.image z).card
        = Fintype.card σ - C.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
        Finset.card_univ, Finset.card_image_of_injOn hz]
    rw [hcardv]
    -- peel the first factor of the falling product
    have hn1 : n = (n - 1) + 1 := by omega
    rw [hn1, Finset.prod_range_succ']
    have hcongr : ∀ j ∈ Finset.range (n - 1),
        Fintype.card σ - C.card - (j + 1)
          = Fintype.card σ - (C.card + 1) - j := fun j _ => by omega
    rw [Finset.prod_congr rfl hcongr, Nat.sub_zero, mul_comm,
      Nat.add_sub_cancel]

/-! ## Specializations of the extension count -/

/-- The number of injective columns is the full falling factorial. -/
lemma card_injectives [Nonempty σ] :
    (Finset.univ.filter fun y : ι → σ => Function.Injective y).card
      = ∏ j ∈ Finset.range (Fintype.card ι), (Fintype.card σ - j) := by
  have h := card_injective_extensions (∅ : Finset ι)
      (fun _ => Classical.arbitrary σ)
      (by rw [Finset.coe_empty]; exact Set.injOn_empty _)
  rw [Finset.card_empty, Nat.sub_zero, Nat.sub_zero] at h
  rw [← h]
  congr 1
  exact Finset.filter_congr fun y _ =>
    (and_iff_left fun c hc => absurd hc (Finset.notMem_empty c)).symm

/-- The rows with a collision at `(a, b)` and no other collision are counted
by dropping the cell `a`: they are the injective assignments of the other
`n - 1` cells. -/
lemma card_collision_rows [Nonempty σ] (a b : ι) (hab : a ≠ b) :
    (Finset.univ.filter fun x : ι → σ =>
        x a = x b ∧ Function.Injective
          fun c : ↥(({a} : Finset ι)ᶜ) => x c.1).card
      = ∏ j ∈ Finset.range (Fintype.card ι - 1), (Fintype.card σ - j) := by
  have hbmem : b ∈ ({a} : Finset ι)ᶜ :=
    Finset.mem_compl.mpr fun h => hab (Finset.mem_singleton.mp h).symm
  have hcard : Fintype.card ↥(({a} : Finset ι)ᶜ) = Fintype.card ι - 1 := by
    rw [Fintype.card_coe, Finset.card_compl, Finset.card_singleton]
  have hbij : (Finset.univ.filter fun x : ι → σ =>
        x a = x b ∧ Function.Injective
          fun c : ↥(({a} : Finset ι)ᶜ) => x c.1).card
      = (Finset.univ.filter fun w : ↥(({a} : Finset ι)ᶜ) → σ =>
          Function.Injective w).card := by
    refine Finset.card_nbij'
      (fun x => fun c : ↥(({a} : Finset ι)ᶜ) => x c.1)
      (fun w => fun c => if h : c ∈ ({a} : Finset ι)ᶜ then w ⟨c, h⟩
        else w ⟨b, hbmem⟩) ?_ ?_ ?_ ?_
    · intro x hx
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2.2⟩
    · intro w hw
      have hwinj := (Finset.mem_filter.mp hw).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · change (if h : a ∈ ({a} : Finset ι)ᶜ then w ⟨a, h⟩
            else w ⟨b, hbmem⟩)
          = if h : b ∈ ({a} : Finset ι)ᶜ then w ⟨b, h⟩ else w ⟨b, hbmem⟩
        rw [dif_neg (fun h => (Finset.mem_compl.mp h)
            (Finset.mem_singleton_self a)), dif_pos hbmem]
      · intro c₁ c₂ hcc
        have h1 : (if h : c₁.1 ∈ ({a} : Finset ι)ᶜ then w ⟨c₁.1, h⟩
            else w ⟨b, hbmem⟩)
            = if h : c₂.1 ∈ ({a} : Finset ι)ᶜ then w ⟨c₂.1, h⟩
              else w ⟨b, hbmem⟩ := hcc
        rw [dif_pos c₁.2, dif_pos c₂.2] at h1
        exact hwinj h1
    · intro x hx
      obtain ⟨-, hxab, -⟩ := Finset.mem_filter.mp hx
      funext c
      by_cases h : c ∈ ({a} : Finset ι)ᶜ
      · exact dif_pos h
      · change (if h : c ∈ ({a} : Finset ι)ᶜ then x c else x b) = x c
        rw [dif_neg h]
        have hca : c = a := Finset.mem_singleton.mp
          (not_not.mp fun hc => h (Finset.mem_compl.mpr hc))
        rw [hca, hxab]
    · intro w hw
      funext c
      exact dif_pos c.2
  rw [hbij, card_injectives, hcard]

/-! ## The gee-transfer -/

/-- Reindexing a product over a finset through its enumeration equiv. -/
lemma prod_eq_prod_equivFin (C : Finset ι) (G : ι → ℝ) :
    (∏ c ∈ C, G c) = ∏ i, G (C.equivFin.symm i).1 := by
  rw [← Finset.prod_attach C G, ← Finset.univ_eq_attach]
  exact (Equiv.prod_comp C.equivFin.symm fun c => G c.1).symm

/-- **The gee-transfer**: summing the centred product over the injective
columns fibers over the values on the coupled cells; each fiber count is the
same falling factorial (`card_injective_extensions`), so the sum is that
count times Belovs' `gee` — nonnegative by `gee_nonneg`.  This is the
positivity of every non-main term of the adversary matrix's entry sum. -/
lemma sum_injective_centered_nonneg (C : Finset ι) (x : ι → σ)
    (hx : Set.InjOn x (C : Set ι)) :
    0 ≤ ∑ y ∈ Finset.univ.filter fun y : ι → σ => Function.Injective y,
        ∏ c ∈ C, ((Fintype.card σ : ℝ)
          * (if y c = x c then 1 else 0) - 1) := by
  have hce_mem : ∀ i : Fin C.card, (C.equivFin.symm i).1 ∈ C :=
    fun i => (C.equivFin.symm i).2
  have hce_inj : Function.Injective
      fun i : Fin C.card => (C.equivFin.symm i).1 :=
    fun i j hij => C.equivFin.symm.injective (Subtype.ext hij)
  have hmaps : ∀ y ∈ Finset.univ.filter fun y : ι → σ =>
      Function.Injective y,
      (fun i => y (C.equivFin.symm i).1)
        ∈ injTuples C.card (Finset.univ : Finset σ) :=
    fun y hy => mem_injTuples.mpr ⟨fun i => Finset.mem_univ _,
      fun i j hij => hce_inj ((Finset.mem_filter.mp hy).2 hij)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber : ∀ t ∈ injTuples C.card (Finset.univ : Finset σ),
      (∑ y ∈ (Finset.univ.filter fun y : ι → σ =>
            Function.Injective y).filter
          fun y => (fun i => y (C.equivFin.symm i).1) = t,
        ∏ c ∈ C, ((Fintype.card σ : ℝ)
          * (if y c = x c then 1 else 0) - 1))
      = ((∏ j ∈ Finset.range (Fintype.card ι - C.card),
            (Fintype.card σ - C.card - j) : ℕ) : ℝ)
          * ∏ i, ((Fintype.card σ : ℝ)
              * (if t i = x (C.equivFin.symm i).1 then 1 else 0) - 1) := by
    intro t ht
    obtain ⟨-, htinj⟩ := mem_injTuples.mp ht
    have hzinj : Set.InjOn
        (fun c => if h : c ∈ C then t (C.equivFin ⟨c, h⟩) else x c)
        (C : Set ι) := by
      intro c₁ hc₁ c₂ hc₂ hcc
      rw [Finset.mem_coe] at hc₁ hc₂
      have hcc' : (if h : c₁ ∈ C then t (C.equivFin ⟨c₁, h⟩) else x c₁)
          = if h : c₂ ∈ C then t (C.equivFin ⟨c₂, h⟩) else x c₂ := hcc
      rw [dif_pos hc₁, dif_pos hc₂] at hcc'
      exact Subtype.ext_iff.mp (C.equivFin.injective (htinj hcc'))
    have hfilter_eq : (Finset.univ.filter fun y : ι → σ =>
          Function.Injective y).filter
          (fun y => (fun i => y (C.equivFin.symm i).1) = t)
        = Finset.univ.filter fun y : ι → σ =>
            Function.Injective y ∧ ∀ c ∈ C, y c
              = if h : c ∈ C then t (C.equivFin ⟨c, h⟩) else x c := by
      rw [Finset.filter_filter]
      refine Finset.filter_congr fun y _ => ?_
      constructor
      · rintro ⟨hyinj, hyt⟩
        refine ⟨hyinj, fun c hc => ?_⟩
        rw [dif_pos hc]
        have h1 : (C.equivFin.symm (C.equivFin ⟨c, hc⟩)).1 = c := by
          rw [Equiv.symm_apply_apply]
        calc y c = y (C.equivFin.symm (C.equivFin ⟨c, hc⟩)).1 := by rw [h1]
          _ = t (C.equivFin ⟨c, hc⟩) := congrFun hyt _
      · rintro ⟨hyinj, hyz⟩
        refine ⟨hyinj, funext fun i => ?_⟩
        have h1 := hyz (C.equivFin.symm i).1 (hce_mem i)
        rw [dif_pos (hce_mem i)] at h1
        have h2 : C.equivFin ⟨(C.equivFin.symm i).1, hce_mem i⟩ = i := by
          rw [show (⟨(C.equivFin.symm i).1, hce_mem i⟩ : ↥C)
              = C.equivFin.symm i from Subtype.ext rfl,
            Equiv.apply_symm_apply]
        change y (C.equivFin.symm i).1 = t i
        rw [h1, h2]
    have hcard : ((Finset.univ.filter fun y : ι → σ =>
          Function.Injective y).filter
          (fun y => (fun i => y (C.equivFin.symm i).1) = t)).card
        = ∏ j ∈ Finset.range (Fintype.card ι - C.card),
            (Fintype.card σ - C.card - j) := by
      rw [hfilter_eq]
      exact card_injective_extensions C _ hzinj
    have hconst : ∀ y ∈ (Finset.univ.filter fun y : ι → σ =>
          Function.Injective y).filter
          fun y => (fun i => y (C.equivFin.symm i).1) = t,
        (∏ c ∈ C, ((Fintype.card σ : ℝ)
            * (if y c = x c then 1 else 0) - 1))
          = ∏ i, ((Fintype.card σ : ℝ)
              * (if t i = x (C.equivFin.symm i).1 then 1 else 0) - 1) := by
      intro y hy
      have hyt := (Finset.mem_filter.mp hy).2
      rw [prod_eq_prod_equivFin C]
      exact Finset.prod_congr rfl fun i _ => by
        rw [show y (C.equivFin.symm i).1 = t i from congrFun hyt i]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcard, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hfiber, ← Finset.mul_sum]
  exact mul_nonneg (Nat.cast_nonneg _)
    (gee_nonneg (Fintype.card σ) C.card Finset.univ
      (fun i => x (C.equivFin.symm i).1)
      (fun i j hij => hce_inj (hx (Finset.mem_coe.mpr (hce_mem i))
        (Finset.mem_coe.mpr (hce_mem j)) hij))
      (fun i => Finset.mem_univ _)
      (le_of_eq Finset.card_univ))

/-! ## Block-term entries as centred products

Over a collision row (`x a = x b`) every block-term entry is a fixed
constant `q^{-1/2}·q^{-(n-1)}` times the centred product
`∏_{c ∈ C} (q·[y c = x c] - 1)` over its coupled cell set `C`: the `E₁`
cells contribute their cell, `F'` couples `y b` (whose label `x a` *is*
`x b` on a collision row), `F''` couples `y a`, and `F₀` couples nothing. -/

/-- Splitting the scheme pattern over `{a,b}ᶜ` and extracting `q⁻¹` from
every cell. -/
lemma prod_scheme_cells [Nonempty σ] {a b : ι} (hab : a ≠ b) {T : Finset ι}
    (hT : T ⊆ ({a, b} : Finset ι)ᶜ) (x y : ι → σ) :
    (∏ c ∈ ({a, b} : Finset ι)ᶜ,
        (if c ∈ T then cellE1 (x c) (y c) else cellE0 (x c) (y c)))
      = ((Fintype.card σ : ℝ)⁻¹) ^ (Fintype.card ι - 2)
          * ∏ c ∈ T, ((Fintype.card σ : ℝ)
              * (if y c = x c then 1 else 0) - 1) := by
  have hq : ((Fintype.card σ : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcell : ∀ c ∈ ({a, b} : Finset ι)ᶜ,
      (if c ∈ T then cellE1 (x c) (y c) else cellE0 (x c) (y c))
        = (Fintype.card σ : ℝ)⁻¹
          * (if c ∈ T then ((Fintype.card σ : ℝ)
              * (if y c = x c then 1 else 0) - 1) else 1) := by
    intro c _
    by_cases hcT : c ∈ T
    · rw [if_pos hcT, if_pos hcT]
      simp only [cellE1, Matrix.of_apply]
      rw [show (if x c = y c then (1 : ℝ) else 0)
          = if y c = x c then (1 : ℝ) else 0 from if_congr eq_comm rfl rfl,
        mul_sub, ← mul_assoc, inv_mul_cancel₀ hq, one_mul, mul_one]
    · rw [if_neg hcT, if_neg hcT, mul_one]
      simp only [cellE0, Matrix.of_apply]
  rw [Finset.prod_congr rfl hcell, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.prod_ite_mem,
    Finset.inter_eq_right.mpr hT, Finset.card_compl,
    Finset.card_pair hab]

/-- The `F₀` block-term entry over a collision row. -/
lemma blockTerm_edF0_apply [Nonempty σ] {a b : ι} (hab : a ≠ b)
    {T : Finset ι} (hT : T ⊆ ({a, b} : Finset ι)ᶜ) {x : ι → σ}
    (hx : x a = x b) (y : ι → σ) :
    blockTerm a b edF0 T x y
      = (Real.sqrt (Fintype.card σ))⁻¹
          * ((Fintype.card σ : ℝ)⁻¹) ^ (Fintype.card ι - 1)
          * ∏ c ∈ T, ((Fintype.card σ : ℝ)
              * (if y c = x c then 1 else 0) - 1) := by
  have h2 : 2 ≤ Fintype.card ι := by
    rw [← Finset.card_pair hab, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  simp only [blockTerm, Matrix.of_apply, edF0]
  rw [if_pos hx, one_mul, prod_scheme_cells hab hT x y,
    show Fintype.card ι - 1 = (Fintype.card ι - 2) + 1 from by omega,
    pow_succ]
  ring

/-- The `F'` block-term entry over a collision row: the mask cell `b`
joins the coupled set, with its label `x a = x b`. -/
lemma blockTerm_edF'_apply [Nonempty σ] {a b : ι} (hab : a ≠ b)
    {T : Finset ι} (hT : T ⊆ ({a, b} : Finset ι)ᶜ) {x : ι → σ}
    (hx : x a = x b) (y : ι → σ) :
    blockTerm a b edF' T x y
      = (Real.sqrt (Fintype.card σ))⁻¹
          * ((Fintype.card σ : ℝ)⁻¹) ^ (Fintype.card ι - 1)
          * ∏ c ∈ insert b T, ((Fintype.card σ : ℝ)
              * (if y c = x c then 1 else 0) - 1) := by
  have hq : ((Fintype.card σ : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h2 : 2 ≤ Fintype.card ι := by
    rw [← Finset.card_pair hab, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  have hbT : b ∉ T := fun hbT' => (Finset.mem_compl.mp (hT hbT'))
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  simp only [blockTerm, Matrix.of_apply, edF']
  rw [if_pos hx, one_mul, prod_scheme_cells hab hT x y,
    Finset.prod_insert hbT, hx,
    show (if y b = x b then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹
      = (Fintype.card σ : ℝ)⁻¹ * ((Fintype.card σ : ℝ)
          * (if y b = x b then 1 else 0) - 1) from by
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hq, one_mul, mul_one],
    show Fintype.card ι - 1 = (Fintype.card ι - 2) + 1 from by omega,
    pow_succ]
  ring

/-- The `F''` block-term entry over a collision row: the mask cell `a`
joins the coupled set. -/
lemma blockTerm_edF''_apply [Nonempty σ] {a b : ι} (hab : a ≠ b)
    {T : Finset ι} (hT : T ⊆ ({a, b} : Finset ι)ᶜ) {x : ι → σ}
    (hx : x a = x b) (y : ι → σ) :
    blockTerm a b edF'' T x y
      = (Real.sqrt (Fintype.card σ))⁻¹
          * ((Fintype.card σ : ℝ)⁻¹) ^ (Fintype.card ι - 1)
          * ∏ c ∈ insert a T, ((Fintype.card σ : ℝ)
              * (if y c = x c then 1 else 0) - 1) := by
  have hq : ((Fintype.card σ : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h2 : 2 ≤ Fintype.card ι := by
    rw [← Finset.card_pair hab, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  have haT : a ∉ T := fun haT' => (Finset.mem_compl.mp (hT haT'))
    (Finset.mem_insert_self a {b})
  simp only [blockTerm, Matrix.of_apply, edF'']
  rw [if_pos hx, one_mul, prod_scheme_cells hab hT x y,
    Finset.prod_insert haT,
    show (if y a = x a then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹
      = (Fintype.card σ : ℝ)⁻¹ * ((Fintype.card σ : ℝ)
          * (if y a = x a then 1 else 0) - 1) from by
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hq, one_mul, mul_one],
    show Fintype.card ι - 1 = (Fintype.card ι - 2) + 1 from by omega,
    pow_succ]
  ring

/-! ## Column sums of the block terms -/

/-- The pointwise decomposition `F = F₀ + F' + F''` of the collision
factor, at the block-term level. -/
lemma blockTerm_edF_split3 (a b : ι) (T : Finset ι) (x y : ι → σ) :
    blockTerm a b edF T x y
      = blockTerm a b edF0 T x y + blockTerm a b edF' T x y
        + blockTerm a b edF'' T x y := by
  have h : edF0 (x a) ((y a, y b) : σ × σ)
      + (edF' (x a) (y a, y b) + edF'' (x a) (y a, y b))
      = edF (x a) (y a, y b) := by
    rw [edF0, edF', edF'', edF]
    ring
  simp only [blockTerm, Matrix.of_apply]
  rw [← h]
  ring

/-- Non-main terms, `F₀` part: nonnegative column sum. -/
lemma sum_col_blockTerm_edF0_nonneg [Nonempty σ] {a b : ι} (hab : a ≠ b)
    {T : Finset ι} (hT : T ⊆ ({a, b} : Finset ι)ᶜ) {x : ι → σ}
    (hx : x a = x b) (hinj : Set.InjOn x (T : Set ι)) :
    0 ≤ ∑ y ∈ Finset.univ.filter fun y : ι → σ => Function.Injective y,
        blockTerm a b edF0 T x y := by
  rw [Finset.sum_congr rfl fun y _ => blockTerm_edF0_apply hab hT hx y,
    ← Finset.mul_sum]
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
      (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _))
    (sum_injective_centered_nonneg T x hinj)

/-- Non-main terms, `F'` part: nonnegative column sum. -/
lemma sum_col_blockTerm_edF'_nonneg [Nonempty σ] {a b : ι} (hab : a ≠ b)
    {T : Finset ι} (hT : T ⊆ ({a, b} : Finset ι)ᶜ) {x : ι → σ}
    (hx : x a = x b)
    (hinj : Set.InjOn x ((insert b T : Finset ι) : Set ι)) :
    0 ≤ ∑ y ∈ Finset.univ.filter fun y : ι → σ => Function.Injective y,
        blockTerm a b edF' T x y := by
  rw [Finset.sum_congr rfl fun y _ => blockTerm_edF'_apply hab hT hx y,
    ← Finset.mul_sum]
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
      (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _))
    (sum_injective_centered_nonneg (insert b T) x hinj)

/-- Non-main terms, `F''` part: nonnegative column sum. -/
lemma sum_col_blockTerm_edF''_nonneg [Nonempty σ] {a b : ι} (hab : a ≠ b)
    {T : Finset ι} (hT : T ⊆ ({a, b} : Finset ι)ᶜ) {x : ι → σ}
    (hx : x a = x b)
    (hinj : Set.InjOn x ((insert a T : Finset ι) : Set ι)) :
    0 ≤ ∑ y ∈ Finset.univ.filter fun y : ι → σ => Function.Injective y,
        blockTerm a b edF'' T x y := by
  rw [Finset.sum_congr rfl fun y _ => blockTerm_edF''_apply hab hT hx y,
    ← Finset.mul_sum]
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
      (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _))
    (sum_injective_centered_nonneg (insert a T) x hinj)

/-- **Every term of the entry sum is nonnegative**: the full-factor block
term has nonnegative column sum over the injective inputs. -/
lemma sum_col_blockTerm_edF_nonneg [Nonempty σ] {a b : ι} (hab : a ≠ b)
    {T : Finset ι} (hT : T ⊆ ({a, b} : Finset ι)ᶜ) {x : ι → σ}
    (hx : x a = x b)
    (hinjb : Set.InjOn x ((insert b T : Finset ι) : Set ι))
    (hinja : Set.InjOn x ((insert a T : Finset ι) : Set ι)) :
    0 ≤ ∑ y ∈ Finset.univ.filter fun y : ι → σ => Function.Injective y,
        blockTerm a b edF T x y := by
  rw [Finset.sum_congr rfl fun y _ => blockTerm_edF_split3 a b T x y,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h0 := sum_col_blockTerm_edF0_nonneg hab hT hx
    (hinjb.mono (Finset.coe_subset.mpr (Finset.subset_insert b T)))
  have h' := sum_col_blockTerm_edF'_nonneg hab hT hx hinjb
  have h'' := sum_col_blockTerm_edF''_nonneg hab hT hx hinja
  linarith

/-- The main-term value: the `F₀` part of the empty block term is a
constant row, summing to an explicit positive multiple of the injective
count. -/
lemma sum_col_blockTerm_edF0_empty [Nonempty σ] {a b : ι} (hab : a ≠ b)
    {x : ι → σ} (hx : x a = x b) :
    (∑ y ∈ Finset.univ.filter fun y : ι → σ => Function.Injective y,
        blockTerm a b edF0 (∅ : Finset ι) x y)
      = (Real.sqrt (Fintype.card σ))⁻¹
          * ((Fintype.card σ : ℝ)⁻¹) ^ (Fintype.card ι - 1)
          * ((Finset.univ.filter fun y : ι → σ =>
              Function.Injective y).card : ℝ) := by
  have hentry : ∀ y ∈ Finset.univ.filter fun y : ι → σ =>
      Function.Injective y,
      blockTerm a b edF0 (∅ : Finset ι) x y
        = (Real.sqrt (Fintype.card σ))⁻¹
            * ((Fintype.card σ : ℝ)⁻¹) ^ (Fintype.card ι - 1) := by
    intro y _
    rw [blockTerm_edF0_apply hab (Finset.empty_subset _) hx y,
      Finset.prod_empty, mul_one]
  rw [Finset.sum_congr rfl hentry, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **The main term dominates**: the empty block term of the full factor
sums to at least the main-term constant (its `F'`/`F''` parts are
nonnegative since a singleton coupled set is always injectively
labelled). -/
lemma sum_col_blockTerm_edF_empty_ge [Nonempty σ] {a b : ι} (hab : a ≠ b)
    {x : ι → σ} (hx : x a = x b) :
    (Real.sqrt (Fintype.card σ))⁻¹
        * ((Fintype.card σ : ℝ)⁻¹) ^ (Fintype.card ι - 1)
        * ((Finset.univ.filter fun y : ι → σ =>
            Function.Injective y).card : ℝ)
      ≤ ∑ y ∈ Finset.univ.filter fun y : ι → σ => Function.Injective y,
          blockTerm a b edF (∅ : Finset ι) x y := by
  have hsing : ∀ d : ι,
      Set.InjOn x ((insert d (∅ : Finset ι) : Finset ι) : Set ι) := by
    intro d c₁ hc₁ c₂ hc₂ _
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hc₁) with h₁ | h₁
    · rcases Finset.mem_insert.mp (Finset.mem_coe.mp hc₂) with h₂ | h₂
      · rw [h₁, h₂]
      · exact absurd h₂ (Finset.notMem_empty _)
    · exact absurd h₁ (Finset.notMem_empty _)
  have h' := sum_col_blockTerm_edF'_nonneg hab (Finset.empty_subset _) hx
    (hsing b)
  have h'' := sum_col_blockTerm_edF''_nonneg hab (Finset.empty_subset _) hx
    (hsing a)
  rw [Finset.sum_congr rfl fun y _ => blockTerm_edF_split3 a b ∅ x y,
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_col_blockTerm_edF0_empty hab hx]
  linarith

/-! ## Falling-factorial estimates -/

/-- Cast bridge: the natural falling factorial equals the real one while
the number of factors stays below `q`. -/
lemma cast_falling_factorial (q m : ℕ) (hm : m ≤ q) :
    ((∏ j ∈ Finset.range m, (q - j) : ℕ) : ℝ)
      = ∏ j ∈ Finset.range m, ((q : ℝ) - j) := by
  rw [Nat.cast_prod]
  exact Finset.prod_congr rfl fun j hj =>
    Nat.cast_sub (le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hj) hm))

/-- The falling factorial loses at most an `m²/(2q)` fraction of `q^m`. -/
lemma prod_range_sub_ge (q : ℕ) :
    ∀ m : ℕ, m ≤ q →
      (1 - (m : ℝ) * m / (2 * (q : ℝ))) * (q : ℝ) ^ m
        ≤ ∏ j ∈ Finset.range m, ((q : ℝ) - j) := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [Finset.range_zero, Finset.prod_empty]
    norm_num
  | succ m IH =>
    intro hm1
    push_cast
    have hq0 : (0 : ℝ) < q := by
      have h : 0 < q := by omega
      exact_mod_cast h
    have hmq : (m : ℝ) + 1 ≤ q := by exact_mod_cast hm1
    have hpow : (0 : ℝ) < (q : ℝ) ^ m := pow_pos hq0 m
    have hIH := IH (by omega)
    have key : (1 - ((m : ℝ) + 1) * ((m : ℝ) + 1) / (2 * (q : ℝ)))
          * (q : ℝ)
        ≤ (1 - (m : ℝ) * m / (2 * (q : ℝ))) * ((q : ℝ) - m) := by
      have hq0' : (q : ℝ) ≠ 0 := ne_of_gt hq0
      have expand : (1 - (m : ℝ) * m / (2 * (q : ℝ))) * ((q : ℝ) - m)
          - (1 - ((m : ℝ) + 1) * ((m : ℝ) + 1) / (2 * (q : ℝ)))
            * (q : ℝ)
          = ((q : ℝ) + (m : ℝ) ^ 3) / (2 * (q : ℝ)) := by
        field_simp
        ring
      have hnn : (0 : ℝ) ≤ ((q : ℝ) + (m : ℝ) ^ 3) / (2 * (q : ℝ)) :=
        div_nonneg (by positivity) (by linarith)
      linarith
    rw [Finset.prod_range_succ]
    calc (1 - ((m : ℝ) + 1) * ((m : ℝ) + 1) / (2 * (q : ℝ)))
          * (q : ℝ) ^ (m + 1)
        = ((1 - ((m : ℝ) + 1) * ((m : ℝ) + 1) / (2 * (q : ℝ)))
            * (q : ℝ)) * (q : ℝ) ^ m := by
          rw [pow_succ]
          ring
      _ ≤ ((1 - (m : ℝ) * m / (2 * (q : ℝ))) * ((q : ℝ) - m))
            * (q : ℝ) ^ m :=
          mul_le_mul_of_nonneg_right key (le_of_lt hpow)
      _ = ((1 - (m : ℝ) * m / (2 * (q : ℝ))) * (q : ℝ) ^ m)
            * ((q : ℝ) - m) := by ring
      _ ≤ (∏ j ∈ Finset.range m, ((q : ℝ) - j)) * ((q : ℝ) - m) :=
          mul_le_mul_of_nonneg_right hIH (by linarith)

/-- Under `m² ≤ q` the falling factorial keeps at least half of `q^m`. -/
lemma prod_range_sub_ge_half (q m : ℕ) (hq : 0 < q) (hm : m * m ≤ q) :
    (q : ℝ) ^ m / 2 ≤ ∏ j ∈ Finset.range m, ((q : ℝ) - j) := by
  have hmq : m ≤ q := by
    rcases Nat.eq_zero_or_pos m with h0 | h1
    · omega
    · exact le_trans (Nat.le_mul_of_pos_left m h1) hm
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hm' : (m : ℝ) * m ≤ q := by exact_mod_cast hm
  have hhalf : (1 : ℝ) / 2 ≤ 1 - (m : ℝ) * m / (2 * (q : ℝ)) := by
    have h : (m : ℝ) * m / (2 * (q : ℝ)) ≤ 1 / 2 := by
      rw [div_eq_mul_inv]
      calc (m : ℝ) * m * (2 * (q : ℝ))⁻¹
          ≤ (q : ℝ) * (2 * (q : ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_right hm'
              (le_of_lt (inv_pos.mpr (by linarith)))
        _ = 1 / 2 := by
            field_simp
    linarith
  refine le_trans ?_ (prod_range_sub_ge q m hmq)
  calc (q : ℝ) ^ m / 2 = (1 / 2) * (q : ℝ) ^ m := by ring
    _ ≤ (1 - (m : ℝ) * m / (2 * (q : ℝ))) * (q : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right hhalf (pow_nonneg (le_of_lt hq0) m)

end QuantumQueryComplexity
