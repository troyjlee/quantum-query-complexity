import QuantumQueryComplexity.EDLower.Count
import QuantumQueryComplexity.EDLower.WBounds
import QuantumQueryComplexity.ED.Defs
import QuantumQueryComplexity.ED.Main
import QuantumQueryComplexity.Basic
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Belovs' Ω(n^{2/3}) lower bound for element distinctness — assembly

The adversary matrix has rows supported on the *legal* inputs (exactly one
collision) and columns masked to the injective inputs.  A legal row carries
the `edBlock` of its collision pair; since the pair is unique up to order,
any `Classical.choose`-extracted certificate is the collision pair, and no
canonical ordering is needed.

* mask side: each row of `edGammaMat α ⊙ advD i` is a row of
  `edBlockMod i α p ⊙ advD i` times the column mask, so
  `norm_le_sqrt_of_rows` + pinching + the summed Gram bound give
  `‖edGammaMat α ⊙ advD i‖ ≤ √(4(2A + 5n²B))`;
* value side: the all-ones test vectors and the `gee`-positivity of every
  non-main term leave the main term `α₀·q^{-1/2}(q⁻¹)^{n-1}·C`, and the
  counting estimates make the `q`-powers cancel exactly.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-! ## Legal rows -/

/-- Legality for the ordered pair `(a, b)`: a collision at the pair and
injectivity away from `a`. -/
def edLegalPair (a b : ι) (x : ι → σ) : Prop :=
  x a = x b ∧ Function.Injective fun c : ↥(({a} : Finset ι)ᶜ) => x c.1

instance (a b : ι) : DecidablePred (edLegalPair (σ := σ) a b) := fun x =>
  decidable_of_iff (x a = x b ∧ Function.Injective
    fun c : ↥(({a} : Finset ι)ᶜ) => x c.1) Iff.rfl

/-- A legal row: some ordered pair certifies exactly-one-collision. -/
def edLegal (x : ι → σ) : Prop :=
  ∃ p : ι × ι, p.1 ≠ p.2 ∧ edLegalPair p.1 p.2 x

instance : DecidablePred (edLegal (ι := ι) (σ := σ)) := fun x =>
  decidable_of_iff (∃ p : ι × ι, p.1 ≠ p.2 ∧ edLegalPair p.1 p.2 x) Iff.rfl

/-- The injectivity component of a certificate, as `Set.InjOn`. -/
lemma edLegalPair.injOn_compl {a b : ι} {x : ι → σ}
    (h : edLegalPair a b x) :
    Set.InjOn x ((({a} : Finset ι)ᶜ : Finset ι) : Set ι) :=
  fun c₁ h₁ c₂ h₂ hcc => congrArg Subtype.val
    (h.2 (a₁ := ⟨c₁, Finset.mem_coe.mp h₁⟩)
      (a₂ := ⟨c₂, Finset.mem_coe.mp h₂⟩) hcc)

/-- The certificate with the roles of the pair swapped. -/
lemma edLegalPair.symm {a b : ι} {x : ι → σ} (hab : a ≠ b)
    (h : edLegalPair a b x) : edLegalPair b a x := by
  obtain ⟨hxab, hinj⟩ := h
  have hinj' : Set.InjOn x ((({a} : Finset ι)ᶜ : Finset ι) : Set ι) :=
    edLegalPair.injOn_compl ⟨hxab, hinj⟩
  have hbmem : b ∈ ((({a} : Finset ι)ᶜ : Finset ι) : Set ι) :=
    Finset.mem_coe.mpr (Finset.mem_compl.mpr
      fun hb => hab (Finset.mem_singleton.mp hb).symm)
  refine ⟨hxab.symm, ?_⟩
  intro c₁ c₂ hcc
  have hcc' : x c₁.1 = x c₂.1 := hcc
  have h₁b : c₁.1 ≠ b := fun hb =>
    (Finset.mem_compl.mp c₁.2) (Finset.mem_singleton.mpr hb)
  have h₂b : c₂.1 ≠ b := fun hb =>
    (Finset.mem_compl.mp c₂.2) (Finset.mem_singleton.mpr hb)
  refine Subtype.ext ?_
  by_cases h₁a : c₁.1 = a
  · by_cases h₂a : c₂.1 = a
    · rw [h₁a, h₂a]
    · exfalso
      have hmem₂ : c₂.1 ∈ ((({a} : Finset ι)ᶜ : Finset ι) : Set ι) :=
        Finset.mem_coe.mpr (Finset.mem_compl.mpr
          fun hc => h₂a (Finset.mem_singleton.mp hc))
      have hxc : x c₂.1 = x b := by rw [← hcc', h₁a, hxab]
      exact h₂b (hinj' hmem₂ hbmem hxc)
  · by_cases h₂a : c₂.1 = a
    · exfalso
      have hmem₁ : c₁.1 ∈ ((({a} : Finset ι)ᶜ : Finset ι) : Set ι) :=
        Finset.mem_coe.mpr (Finset.mem_compl.mpr
          fun hc => h₁a (Finset.mem_singleton.mp hc))
      have hxc : x c₁.1 = x b := by rw [hcc', h₂a, hxab]
      exact h₁b (hinj' hmem₁ hbmem hxc)
    · have hmem₁ : c₁.1 ∈ ((({a} : Finset ι)ᶜ : Finset ι) : Set ι) :=
        Finset.mem_coe.mpr (Finset.mem_compl.mpr
          fun hc => h₁a (Finset.mem_singleton.mp hc))
      have hmem₂ : c₂.1 ∈ ((({a} : Finset ι)ᶜ : Finset ι) : Set ι) :=
        Finset.mem_coe.mpr (Finset.mem_compl.mpr
          fun hc => h₂a (Finset.mem_singleton.mp hc))
      exact hinj' hmem₁ hmem₂ hcc'

lemma edLegal.edFun_eq_true {x : ι → σ} (h : edLegal x) :
    edFun x = true := by
  obtain ⟨p, hne, hpair⟩ := h
  exact edFun_eq_true_iff.mpr ⟨p, hne, hpair.1⟩

lemma edFun_eq_false_of_injective {y : ι → σ}
    (h : Function.Injective y) : edFun y = false := by
  cases hb : edFun y
  · rfl
  · exfalso
    obtain ⟨q, hne, heq⟩ := edFun_eq_true_iff.mp hb
    exact hne (h heq)

/-! ## The adversary matrix -/

/-- The one-sided adversary matrix: a legal row carries the block of its
collision pair; columns are masked to the injective inputs. -/
noncomputable def edGammaMat (α : ℕ → ℝ) : Matrix (ι → σ) (ι → σ) ℝ :=
  Matrix.of fun x y =>
    if h : edLegal x then
      edBlock (Classical.choose h).1 (Classical.choose h).2 α x y
        * (if Function.Injective y then 1 else 0)
    else 0

lemma edGammaMat_apply_of_not_legal {α : ℕ → ℝ} {x : ι → σ}
    (h : ¬ edLegal x) (y : ι → σ) : edGammaMat (ι := ι) (σ := σ) α x y = 0 := by
  rw [edGammaMat, Matrix.of_apply, dif_neg h]

lemma edGammaMat_apply_of_legal {α : ℕ → ℝ} {x : ι → σ} (h : edLegal x)
    (y : ι → σ) :
    edGammaMat α x y
      = edBlock (Classical.choose h).1 (Classical.choose h).2 α x y
          * (if Function.Injective y then 1 else 0) := by
  rw [edGammaMat, Matrix.of_apply, dif_pos h]

/-- Entries vanish on `f`-equal pairs: a nonzero entry needs a legal
(colliding) row and an injective column. -/
lemma edGammaMat_apply_eq_zero {α : ℕ → ℝ} {x y : ι → σ}
    (h : edFun x = edFun y) : edGammaMat (ι := ι) (σ := σ) α x y = 0 := by
  by_cases hx : edLegal x
  · rw [edGammaMat_apply_of_legal hx]
    by_cases hy : Function.Injective y
    · exfalso
      rw [edLegal.edFun_eq_true hx, edFun_eq_false_of_injective hy] at h
      exact Bool.noConfusion h
    · rw [if_neg hy, mul_zero]
  · exact edGammaMat_apply_of_not_legal hx y

/-! ## The mask bound -/

/-- The three replacement identities, packaged as the `edBlockModPair`
case split. -/
lemma edBlock_hadamard_modPair (i : ι) (α : ℕ → ℝ) {q : ι × ι}
    (hab : q.1 ≠ q.2) :
    edBlock (σ := σ) q.1 q.2 α ⊙ advD i = edBlockModPair i α q ⊙ advD i := by
  by_cases hia : i = q.1
  · subst hia
    rw [edBlock_hadamard_left q.1 q.2 α]
    congr 1
    simp [edBlockModPair]
  · by_cases hib : i = q.2
    · subst hib
      rw [edBlock_hadamard_right hab α]
      congr 1
      simp [edBlockModPair, hia]
    · rw [edBlock_hadamard_out hab hia hib α]
      congr 1
      simp [edBlockModPair, hia, hib]

/-- Rows of the masked matrix: zero on illegal rows, a masked modified
block row (times the column mask) on legal ones. -/
lemma edGammaMat_hadamard_rows (α : ℕ → ℝ) (i : ι) (x : ι → σ) :
    (∀ y, (edGammaMat (ι := ι) (σ := σ) α ⊙ advD i) x y = 0)
      ∨ ∃ p : {q : ι × ι // q.1 ≠ q.2}, ∀ y,
          (edGammaMat α ⊙ advD i) x y
            = ((edBlockMod i α p ⊙ advD i) x y)
                * (if Function.Injective y then 1 else 0) := by
  by_cases h : edLegal x
  · right
    refine ⟨⟨Classical.choose h, (Classical.choose_spec h).1⟩, fun y => ?_⟩
    have hentry : (edBlockMod (σ := σ) i α
          ⟨Classical.choose h, (Classical.choose_spec h).1⟩ ⊙ advD i) x y
        = (edBlock (Classical.choose h).1 (Classical.choose h).2 α
            ⊙ advD i) x y := by
      change (edBlockModPair (σ := σ) i α (Classical.choose h)
        ⊙ advD i) x y = _
      rw [← edBlock_hadamard_modPair i α (Classical.choose_spec h).1]
    rw [Matrix.hadamard_apply, edGammaMat_apply_of_legal h y, hentry,
      Matrix.hadamard_apply]
    ring
  · left
    intro y
    rw [Matrix.hadamard_apply, edGammaMat_apply_of_not_legal h y, zero_mul]

/-- **The mask bound**: every Schur product of the one-sided matrix is
uniformly small. -/
theorem norm_edGammaMat_hadamard_le [Nonempty σ] (α : ℕ → ℝ) {A B : ℝ}
    (hA : ∀ k : ℕ, ((k : ℝ) + 1) * (α k * α k) ≤ A)
    (hB : ∀ k : ℕ, (α k - α (k + 1)) * (α k - α (k + 1)) ≤ B)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (i : ι) :
    ‖edGammaMat (ι := ι) (σ := σ) α ⊙ advD i‖
      ≤ Real.sqrt (4 * (2 * A + 5 * (Fintype.card ι : ℝ) ^ 2 * B)) := by
  have hW0 : (0 : ℝ) ≤ 2 * A + 5 * (Fintype.card ι : ℝ) ^ 2 * B := by
    positivity
  refine norm_le_sqrt_of_rows (edGammaMat α ⊙ advD i)
    (fun p => edBlockMod i α p ⊙ advD i)
    (fun y => if Function.Injective y then 1 else 0)
    (fun y => ?_) (edGammaMat_hadamard_rows α i) (by positivity)
    (fun v => sum_gram_hadamard_advD_le i (edBlockMod i α) hW0
      (fun w => quadform_edBlockMod_le i α hA hB hA0 hB0 w) v)
  by_cases h : Function.Injective y
  · rw [if_pos h]
    norm_num
  · rw [if_neg h]
    norm_num

/-! ## Symmetrization -/

lemma advD_transpose (i : ι) : (advD (σ := σ) i)ᵀ = advD i := by
  ext x y
  rw [Matrix.transpose_apply, advD_apply, advD_apply]
  exact if_congr eq_comm rfl rfl

lemma transpose_hadamard_advD (A : Matrix (ι → σ) (ι → σ) ℝ) (i : ι) :
    (A ⊙ advD i)ᵀ = Aᵀ ⊙ advD i := by
  ext x y
  rw [Matrix.transpose_apply, Matrix.hadamard_apply, Matrix.hadamard_apply,
    Matrix.transpose_apply, advD_apply, advD_apply]
  congr 1
  exact if_congr eq_comm rfl rfl

/-- Symmetrizing at most doubles the operator norm. -/
lemma l2_opNorm_add_transpose_le {X : Type*} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℝ) : ‖A + Aᵀ‖ ≤ 2 * ‖A‖ := by
  refine l2_opNorm_le_of_forall_dotProduct _ (by positivity) fun u v => ?_
  have h1 : u ⬝ᵥ (A + Aᵀ) *ᵥ v = u ⬝ᵥ A *ᵥ v + v ⬝ᵥ A *ᵥ u := by
    rw [Matrix.add_mulVec, dotProduct_add]
    congr 1
    exact Matrix.dotProduct_transpose_mulVec ..
  calc |u ⬝ᵥ (A + Aᵀ) *ᵥ v|
      ≤ |u ⬝ᵥ A *ᵥ v| + |v ⬝ᵥ A *ᵥ u| := by
        rw [h1]
        exact abs_add_le _ _
    _ ≤ ‖A‖ * Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v)
        + ‖A‖ * Real.sqrt (v ⬝ᵥ v) * Real.sqrt (u ⬝ᵥ u) :=
        add_le_add (abs_dotProduct_mulVec_le A u v)
          (abs_dotProduct_mulVec_le A v u)
    _ = 2 * ‖A‖ * Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v) := by ring

/-- The symmetrized adversary matrix is a valid adversary matrix for
element distinctness. -/
lemma isAdvMatrix_edGammaMat (α : ℕ → ℝ) :
    IsAdvMatrix (edFun (ι := ι) (σ := σ))
      (edGammaMat α + (edGammaMat α)ᵀ) := by
  constructor
  · rw [Matrix.isHermitian_iff_isSymm]
    show (edGammaMat (ι := ι) (σ := σ) α + (edGammaMat α)ᵀ)ᵀ = _
    rw [Matrix.transpose_add, Matrix.transpose_transpose]
    exact add_comm _ _
  · intro x y hxy
    rw [Matrix.add_apply, Matrix.transpose_apply,
      edGammaMat_apply_eq_zero hxy, edGammaMat_apply_eq_zero hxy.symm, add_zero]

/-- The mask bound for the symmetrized matrix. -/
theorem norm_edGammaMat_symm_hadamard_le [Nonempty σ] (α : ℕ → ℝ) {A B : ℝ}
    (hA : ∀ k : ℕ, ((k : ℝ) + 1) * (α k * α k) ≤ A)
    (hB : ∀ k : ℕ, (α k - α (k + 1)) * (α k - α (k + 1)) ≤ B)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (i : ι) :
    ‖(edGammaMat (ι := ι) (σ := σ) α + (edGammaMat α)ᵀ) ⊙ advD i‖
      ≤ 2 * Real.sqrt (4 * (2 * A + 5 * (Fintype.card ι : ℝ) ^ 2 * B)) := by
  rw [Matrix.add_hadamard, ← transpose_hadamard_advD]
  calc ‖(edGammaMat (ι := ι) (σ := σ) α ⊙ advD i) + (edGammaMat α ⊙ advD i)ᵀ‖
      ≤ 2 * ‖edGammaMat (ι := ι) (σ := σ) α ⊙ advD i‖ :=
        l2_opNorm_add_transpose_le _
    _ ≤ 2 * Real.sqrt (4 * (2 * A + 5 * (Fintype.card ι : ℝ) ^ 2 * B)) := by
        have h := norm_edGammaMat_hadamard_le (σ := σ) α hA hB hA0 hB0 i
        linarith

/-! ## Counting the legal rows -/

/-- The collision set of an input. -/
def colSet (x : ι → σ) : Finset ι :=
  Finset.univ.filter fun c => ∃ d, d ≠ c ∧ x d = x c

/-- A legality certificate pins the collision set to the pair. -/
lemma colSet_eq_pair {a b : ι} {x : ι → σ} (hab : a ≠ b)
    (h : edLegalPair a b x) : colSet x = {a, b} := by
  have hinj := edLegalPair.injOn_compl h
  ext c
  simp only [colSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨d, hdc, hxdc⟩
    by_contra hc
    obtain ⟨hca, hcb⟩ := not_or.mp hc
    have hcmem : c ∈ ((({a} : Finset ι)ᶜ : Finset ι) : Set ι) :=
      Finset.mem_coe.mpr (Finset.mem_compl.mpr
        fun hm => hca (Finset.mem_singleton.mp hm))
    by_cases hda : d = a
    · have hbmem : b ∈ ((({a} : Finset ι)ᶜ : Finset ι) : Set ι) :=
        Finset.mem_coe.mpr (Finset.mem_compl.mpr
          fun hm => hab (Finset.mem_singleton.mp hm).symm)
      have hxbc : x b = x c := by rw [← h.1, ← hda]; exact hxdc
      exact hcb (hinj hbmem hcmem hxbc).symm
    · have hdmem : d ∈ ((({a} : Finset ι)ᶜ : Finset ι) : Set ι) :=
        Finset.mem_coe.mpr (Finset.mem_compl.mpr
          fun hm => hda (Finset.mem_singleton.mp hm))
      exact hdc (hinj hdmem hcmem hxdc)
  · intro hc
    rcases hc with rfl | rfl
    · exact ⟨b, fun hb => hab hb.symm, h.1.symm⟩
    · exact ⟨a, hab, h.1⟩

/-- **The legal-row count**: `C(n,2)` collision sets, each carrying the
falling-factorial count. -/
lemma card_edLegal [Nonempty σ] :
    (Finset.univ.filter fun x : ι → σ => edLegal x).card
      = (Fintype.card ι).choose 2
          * ∏ j ∈ Finset.range (Fintype.card ι - 1),
              (Fintype.card σ - j) := by
  have hmaps : ∀ x ∈ Finset.univ.filter fun x : ι → σ => edLegal x,
      colSet x ∈ Finset.powersetCard 2 (Finset.univ : Finset ι) := by
    intro x hx
    obtain ⟨p, hne, hpair⟩ := (Finset.mem_filter.mp hx).2
    rw [colSet_eq_pair hne hpair]
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
      Finset.card_pair hne⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ s ∈ Finset.powersetCard 2 (Finset.univ : Finset ι),
      ((Finset.univ.filter fun x : ι → σ => edLegal x).filter
        fun x => colSet x = s).card
      = ∏ j ∈ Finset.range (Fintype.card ι - 1),
          (Fintype.card σ - j) := by
    intro s hs
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp
      (Finset.mem_powersetCard.mp hs).2
    have hfiber_eq : (Finset.univ.filter fun x : ι → σ =>
          edLegal x).filter (fun x => colSet x = {a, b})
        = Finset.univ.filter fun x : ι → σ =>
            x a = x b ∧ Function.Injective
              fun c : ↥(({a} : Finset ι)ᶜ) => x c.1 := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨p, hne, hpair⟩, hcs⟩
        have hcs' : ({p.1, p.2} : Finset ι) = {a, b} := by
          rw [← colSet_eq_pair hne hpair, hcs]
        have h1 : p.1 = a ∨ p.1 = b := by
          have hm : p.1 ∈ ({a, b} : Finset ι) := by
            rw [← hcs']
            exact Finset.mem_insert_self p.1 {p.2}
          rcases Finset.mem_insert.mp hm with hm' | hm'
          · exact Or.inl hm'
          · exact Or.inr (Finset.mem_singleton.mp hm')
        have h2 : p.2 = a ∨ p.2 = b := by
          have hm : p.2 ∈ ({a, b} : Finset ι) := by
            rw [← hcs']
            exact Finset.mem_insert_of_mem (Finset.mem_singleton_self p.2)
          rcases Finset.mem_insert.mp hm with hm' | hm'
          · exact Or.inl hm'
          · exact Or.inr (Finset.mem_singleton.mp hm')
        rcases h1 with h1 | h1
        · rcases h2 with h2 | h2
          · exact absurd (h1.trans h2.symm) hne
          · rw [← h1, ← h2]
            exact hpair
        · rcases h2 with h2 | h2
          · rw [← h2, ← h1]
            exact edLegalPair.symm hne hpair
          · exact absurd (h1.trans h2.symm) hne
      · intro hpair
        exact ⟨⟨(a, b), hab, hpair⟩, colSet_eq_pair hab hpair⟩
    rw [hfiber_eq, card_collision_rows a b hab]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_powersetCard, Finset.card_univ]

/-! ## The value bound -/

/-- Over a legal row, the block's column sum over the injective inputs
dominates the main term. -/
lemma sum_col_edBlock_ge [Nonempty σ] {a b : ι} (hab : a ≠ b) {x : ι → σ}
    (h : edLegalPair a b x) (α : ℕ → ℝ) (hα : ∀ k, 0 ≤ α k) :
    α 0 * ((Real.sqrt (Fintype.card σ))⁻¹
        * ((Fintype.card σ : ℝ)⁻¹) ^ (Fintype.card ι - 1))
      * ((Finset.univ.filter fun y : ι → σ =>
          Function.Injective y).card : ℝ)
      ≤ ∑ y ∈ Finset.univ.filter fun y : ι → σ => Function.Injective y,
          edBlock a b α x y := by
  have hxab : x a = x b := h.1
  have hinjA : Set.InjOn x ((({a} : Finset ι)ᶜ : Finset ι) : Set ι) :=
    edLegalPair.injOn_compl h
  have hinjB : Set.InjOn x ((({b} : Finset ι)ᶜ : Finset ι) : Set ι) :=
    edLegalPair.injOn_compl (edLegalPair.symm hab h)
  have hsubA : ∀ {T : Finset ι}, T ∈ ({a, b} : Finset ι)ᶜ.powerset →
      (insert b T : Finset ι) ⊆ ({a} : Finset ι)ᶜ := by
    intro T hT
    refine Finset.insert_subset (Finset.mem_compl.mpr
      fun hm => hab (Finset.mem_singleton.mp hm).symm) ?_
    refine (Finset.mem_powerset.mp hT).trans ?_
    exact Finset.compl_subset_compl.mpr
      (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self a {b}))
  have hsubB : ∀ {T : Finset ι}, T ∈ ({a, b} : Finset ι)ᶜ.powerset →
      (insert a T : Finset ι) ⊆ ({b} : Finset ι)ᶜ := by
    intro T hT
    refine Finset.insert_subset (Finset.mem_compl.mpr
      fun hm => hab (Finset.mem_singleton.mp hm)) ?_
    refine (Finset.mem_powerset.mp hT).trans ?_
    exact Finset.compl_subset_compl.mpr
      (Finset.singleton_subset_iff.mpr
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self b)))
  have hexpand : ∀ y : ι → σ, edBlock (σ := σ) a b α x y
      = ∑ T ∈ ({a, b} : Finset ι)ᶜ.powerset,
          α T.card * blockTerm a b edF T x y := by
    intro y
    rw [edBlock, Matrix.sum_apply]
    exact Finset.sum_congr rfl fun T _ => by
      rw [Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl fun y _ => hexpand y, Finset.sum_comm]
  have hterm : ∀ T ∈ ({a, b} : Finset ι)ᶜ.powerset,
      (0 : ℝ) ≤ ∑ y ∈ Finset.univ.filter fun y : ι → σ =>
          Function.Injective y, α T.card * blockTerm a b edF T x y := by
    intro T hT
    rw [← Finset.mul_sum]
    refine mul_nonneg (hα _) ?_
    exact sum_col_blockTerm_edF_nonneg hab (Finset.mem_powerset.mp hT)
      hxab (hinjA.mono (Finset.coe_subset.mpr (hsubA hT)))
      (hinjB.mono (Finset.coe_subset.mpr (hsubB hT)))
  calc α 0 * ((Real.sqrt (Fintype.card σ))⁻¹
        * ((Fintype.card σ : ℝ)⁻¹) ^ (Fintype.card ι - 1))
      * ((Finset.univ.filter fun y : ι → σ =>
          Function.Injective y).card : ℝ)
      ≤ α 0 * ∑ y ∈ Finset.univ.filter fun y : ι → σ =>
          Function.Injective y, blockTerm a b edF ∅ x y := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (sum_col_blockTerm_edF_empty_ge hab hxab) (hα 0)
    _ = ∑ y ∈ Finset.univ.filter fun y : ι → σ =>
          Function.Injective y, α (∅ : Finset ι).card
            * blockTerm a b edF ∅ x y := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by rw [Finset.card_empty]
    _ ≤ ∑ T ∈ ({a, b} : Finset ι)ᶜ.powerset,
          ∑ y ∈ Finset.univ.filter fun y : ι → σ =>
            Function.Injective y, α T.card * blockTerm a b edF T x y :=
        Finset.single_le_sum hterm
          (Finset.mem_powerset.mpr (Finset.empty_subset _))

/-- The transpose part of the bilinear form dies: its rows need a legal
(hence noninjective) column index, which the injective indicator kills. -/
lemma dot_indicator_edGammaMat_transpose (α : ℕ → ℝ) :
    ((fun x : ι → σ => if edLegal x then (1 : ℝ) else 0) ⬝ᵥ
      ((edGammaMat (ι := ι) (σ := σ) α)ᵀ *ᵥ
        fun y => if Function.Injective y then (1 : ℝ) else 0)) = 0 := by
  rw [dotProduct]
  refine Finset.sum_eq_zero fun x _ => ?_
  have hzero : ((edGammaMat (ι := ι) (σ := σ) α)ᵀ *ᵥ
      fun y => if Function.Injective y then (1 : ℝ) else 0) x = 0 := by
    rw [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [Matrix.transpose_apply]
    by_cases hy : Function.Injective y
    · have hyl : ¬ edLegal y := fun ⟨p, hne, hpair⟩ => hne (hy hpair.1)
      rw [edGammaMat_apply_of_not_legal hyl, zero_mul]
    · rw [if_neg hy, mul_zero]
  rw [hzero, mul_zero]

/-- **The value bound**: the symmetrized matrix has norm at least the
main-term constant times the geometric mean of the two counts. -/
theorem norm_edGammaMat_symm_ge [Nonempty σ] (α : ℕ → ℝ)
    (hα : ∀ k, 0 ≤ α k) :
    α 0 * ((Real.sqrt (Fintype.card σ))⁻¹
        * ((Fintype.card σ : ℝ)⁻¹) ^ (Fintype.card ι - 1))
      * Real.sqrt ((Finset.univ.filter fun x : ι → σ =>
          edLegal x).card)
      * Real.sqrt ((Finset.univ.filter fun y : ι → σ =>
          Function.Injective y).card)
      ≤ ‖edGammaMat (ι := ι) (σ := σ) α + (edGammaMat α)ᵀ‖ := by
  rcases Nat.eq_zero_or_pos (Finset.univ.filter fun x : ι → σ =>
      edLegal x).card with hR0 | hRpos
  · rw [hR0, Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_mul]
    exact norm_nonneg _
  rcases Nat.eq_zero_or_pos (Finset.univ.filter fun y : ι → σ =>
      Function.Injective y).card with hC0 | hCpos
  · rw [hC0, Nat.cast_zero, Real.sqrt_zero, mul_zero]
    exact norm_nonneg _
  have huu : ((fun x : ι → σ => if edLegal x then (1 : ℝ) else 0) ⬝ᵥ
      fun x => if edLegal x then (1 : ℝ) else 0)
      = ((Finset.univ.filter fun x : ι → σ => edLegal x).card : ℝ) := by
    rw [dotProduct]
    rw [Finset.sum_congr rfl fun x _ => show
        (if edLegal x then (1 : ℝ) else 0)
          * (if edLegal x then (1 : ℝ) else 0)
        = if edLegal x then (1 : ℝ) else 0 from by
      by_cases h : edLegal x
      · rw [if_pos h, mul_one]
      · rw [if_neg h, mul_zero]]
    exact Finset.sum_boole _ _
  have hvv : ((fun y : ι → σ => if Function.Injective y then (1 : ℝ)
      else 0) ⬝ᵥ fun y => if Function.Injective y then (1 : ℝ) else 0)
      = ((Finset.univ.filter fun y : ι → σ =>
          Function.Injective y).card : ℝ) := by
    rw [dotProduct]
    rw [Finset.sum_congr rfl fun y _ => show
        (if Function.Injective y then (1 : ℝ) else 0)
          * (if Function.Injective y then (1 : ℝ) else 0)
        = if Function.Injective y then (1 : ℝ) else 0 from by
      by_cases h : Function.Injective y
      · rw [if_pos h, mul_one]
      · rw [if_neg h, mul_zero]]
    exact Finset.sum_boole _ _
  have hmain : α 0 * ((Real.sqrt (Fintype.card σ))⁻¹
        * ((Fintype.card σ : ℝ)⁻¹) ^ (Fintype.card ι - 1))
      * (((Finset.univ.filter fun x : ι → σ => edLegal x).card : ℝ)
        * ((Finset.univ.filter fun y : ι → σ =>
            Function.Injective y).card : ℝ))
      ≤ ((fun x : ι → σ => if edLegal x then (1 : ℝ) else 0) ⬝ᵥ
          ((edGammaMat (ι := ι) (σ := σ) α + (edGammaMat α)ᵀ) *ᵥ
            fun y => if Function.Injective y then (1 : ℝ) else 0)) := by
    rw [Matrix.add_mulVec, dotProduct_add,
      dot_indicator_edGammaMat_transpose, add_zero, dotProduct]
    have hx : ∀ x ∈ Finset.univ.filter fun x : ι → σ => edLegal x,
        α 0 * ((Real.sqrt (Fintype.card σ))⁻¹
            * ((Fintype.card σ : ℝ)⁻¹) ^ (Fintype.card ι - 1))
          * ((Finset.univ.filter fun y : ι → σ =>
              Function.Injective y).card : ℝ)
          ≤ (edGammaMat (ι := ι) (σ := σ) α *ᵥ
              fun y => if Function.Injective y then (1 : ℝ) else 0) x := by
      intro x hx
      have h := (Finset.mem_filter.mp hx).2
      have hrow : ((edGammaMat (ι := ι) (σ := σ) α *ᵥ
          fun y => if Function.Injective y then (1 : ℝ) else 0) x)
          = ∑ y ∈ Finset.univ.filter fun y : ι → σ =>
              Function.Injective y,
              edBlock (Classical.choose h).1 (Classical.choose h).2
                α x y := by
        rw [Matrix.mulVec, dotProduct]
        rw [Finset.sum_congr rfl fun y _ => show
            edGammaMat (ι := ι) (σ := σ) α x y
              * (if Function.Injective y then (1 : ℝ) else 0)
            = if Function.Injective y then
                edBlock (Classical.choose h).1 (Classical.choose h).2
                  α x y
              else 0 from by
          rw [edGammaMat_apply_of_legal h y]
          by_cases hy : Function.Injective y
          · rw [if_pos hy, if_pos hy]
            ring
          · rw [if_neg hy, if_neg hy]
            ring]
        rw [← Finset.sum_filter]
      rw [hrow]
      exact sum_col_edBlock_ge (Classical.choose_spec h).1
        (Classical.choose_spec h).2 α hα
    have hsum : ∀ x : ι → σ,
        (if edLegal x then (1 : ℝ) else 0)
          * ((edGammaMat (ι := ι) (σ := σ) α *ᵥ
              fun y => if Function.Injective y then (1 : ℝ) else 0) x)
        = if edLegal x then ((edGammaMat (ι := ι) (σ := σ) α *ᵥ
            fun y => if Function.Injective y then (1 : ℝ) else 0) x)
          else 0 := by
      intro x
      by_cases hl : edLegal x
      · rw [if_pos hl, if_pos hl, one_mul]
      · rw [if_neg hl, if_neg hl, zero_mul]
    rw [Finset.sum_congr rfl fun x _ => hsum x, ← Finset.sum_filter]
    calc α 0 * ((Real.sqrt (Fintype.card σ))⁻¹
          * ((Fintype.card σ : ℝ)⁻¹) ^ (Fintype.card ι - 1))
        * (((Finset.univ.filter fun x : ι → σ => edLegal x).card : ℝ)
          * ((Finset.univ.filter fun y : ι → σ =>
              Function.Injective y).card : ℝ))
        = ∑ _x ∈ Finset.univ.filter fun x : ι → σ => edLegal x,
            α 0 * ((Real.sqrt (Fintype.card σ))⁻¹
              * ((Fintype.card σ : ℝ)⁻¹) ^ (Fintype.card ι - 1))
            * ((Finset.univ.filter fun y : ι → σ =>
                Function.Injective y).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ ∑ x ∈ Finset.univ.filter fun x : ι → σ => edLegal x,
            (edGammaMat (ι := ι) (σ := σ) α *ᵥ
              fun y => if Function.Injective y then (1 : ℝ) else 0) x :=
          Finset.sum_le_sum hx
  have habs := abs_dotProduct_mulVec_le
    (edGammaMat (ι := ι) (σ := σ) α + (edGammaMat α)ᵀ)
    (fun x => if edLegal x then (1 : ℝ) else 0)
    (fun y => if Function.Injective y then (1 : ℝ) else 0)
  rw [huu, hvv] at habs
  have hval : α 0 * ((Real.sqrt (Fintype.card σ))⁻¹
        * ((Fintype.card σ : ℝ)⁻¹) ^ (Fintype.card ι - 1))
      * (((Finset.univ.filter fun x : ι → σ => edLegal x).card : ℝ)
        * ((Finset.univ.filter fun y : ι → σ =>
            Function.Injective y).card : ℝ))
      ≤ ‖edGammaMat (ι := ι) (σ := σ) α + (edGammaMat α)ᵀ‖
          * Real.sqrt ((Finset.univ.filter fun x : ι → σ =>
              edLegal x).card)
          * Real.sqrt ((Finset.univ.filter fun y : ι → σ =>
              Function.Injective y).card) :=
    le_trans hmain (le_trans (le_abs_self _) habs)
  have hsR : (0 : ℝ) < Real.sqrt ((Finset.univ.filter fun x : ι → σ =>
      edLegal x).card) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hRpos)
  have hsC : (0 : ℝ) < Real.sqrt ((Finset.univ.filter fun y : ι → σ =>
      Function.Injective y).card) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hCpos)
  refine le_of_mul_le_mul_right ?_ (mul_pos hsR hsC)
  calc (α 0 * ((Real.sqrt (Fintype.card σ))⁻¹
        * ((Fintype.card σ : ℝ)⁻¹) ^ (Fintype.card ι - 1))
      * Real.sqrt ((Finset.univ.filter fun x : ι → σ =>
          edLegal x).card)
      * Real.sqrt ((Finset.univ.filter fun y : ι → σ =>
          Function.Injective y).card))
      * (Real.sqrt ((Finset.univ.filter fun x : ι → σ =>
          edLegal x).card)
        * Real.sqrt ((Finset.univ.filter fun y : ι → σ =>
            Function.Injective y).card))
      = α 0 * ((Real.sqrt (Fintype.card σ))⁻¹
          * ((Fintype.card σ : ℝ)⁻¹) ^ (Fintype.card ι - 1))
        * ((Real.sqrt ((Finset.univ.filter fun x : ι → σ =>
            edLegal x).card)
          * Real.sqrt ((Finset.univ.filter fun x : ι → σ =>
              edLegal x).card))
          * (Real.sqrt ((Finset.univ.filter fun y : ι → σ =>
              Function.Injective y).card)
            * Real.sqrt ((Finset.univ.filter fun y : ι → σ =>
                Function.Injective y).card))) := by ring
    _ = α 0 * ((Real.sqrt (Fintype.card σ))⁻¹
          * ((Fintype.card σ : ℝ)⁻¹) ^ (Fintype.card ι - 1))
        * (((Finset.univ.filter fun x : ι → σ => edLegal x).card : ℝ)
          * ((Finset.univ.filter fun y : ι → σ =>
              Function.Injective y).card : ℝ)) := by
        rw [Real.mul_self_sqrt (Nat.cast_nonneg _),
          Real.mul_self_sqrt (Nat.cast_nonneg _)]
    _ ≤ ‖edGammaMat (ι := ι) (σ := σ) α + (edGammaMat α)ᵀ‖
          * Real.sqrt ((Finset.univ.filter fun x : ι → σ =>
              edLegal x).card)
          * Real.sqrt ((Finset.univ.filter fun y : ι → σ =>
              Function.Injective y).card) := hval
    _ = ‖edGammaMat (ι := ι) (σ := σ) α + (edGammaMat α)ᵀ‖
          * (Real.sqrt ((Finset.univ.filter fun x : ι → σ =>
              edLegal x).card)
            * Real.sqrt ((Finset.univ.filter fun y : ι → σ =>
                Function.Injective y).card)) := by ring

/-! ## The coefficient sequence -/

/-- Belovs' coefficients: constant `K/(2n)` up to level `K`, then linear
down to `0` at level `2K` (the ℕ-subtraction truncates). -/
noncomputable def edAlpha (n K k : ℕ) : ℝ :=
  ((2 * K - max k K : ℕ) : ℝ) / (2 * (n : ℝ))

lemma edAlpha_nonneg (n K k : ℕ) : 0 ≤ edAlpha n K k :=
  div_nonneg (Nat.cast_nonneg _) (by positivity)

lemma edAlpha_zero_eq (n K : ℕ) :
    edAlpha n K 0 = (K : ℝ) / (2 * (n : ℝ)) := by
  rw [edAlpha]
  congr 1
  norm_cast
  omega

/-- The `(k+1)α_k²` bound with `A = 1`, under `K³ ≤ 2n²`. -/
lemma edAlpha_quad_le (n K : ℕ)
    (hK : K * K * K ≤ 2 * (n * n)) (k : ℕ) :
    ((k : ℝ) + 1) * (edAlpha n K k * edAlpha n K k) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    rw [edAlpha]
    norm_num
  by_cases hk : 2 * K ≤ k
  · rw [edAlpha, show (2 * K - max k K : ℕ) = 0 from by omega]
    norm_num
  · have h1 : (2 * K - max k K : ℕ) ≤ K := by omega
    have h2 : (k : ℝ) + 1 ≤ 2 * (K : ℝ) := by
      have h2' : k + 1 ≤ 2 * K := by omega
      exact_mod_cast h2'
    have haK : edAlpha n K k * (2 * (n : ℝ)) ≤ (K : ℝ) := by
      rw [edAlpha, div_mul_cancel₀ _ (by positivity : (2 * (n : ℝ)) ≠ 0)]
      exact_mod_cast h1
    have hK' : (K : ℝ) * K * K ≤ 2 * ((n : ℝ) * n) := by
      exact_mod_cast hK
    have hc0 : (0 : ℝ) ≤ edAlpha n K k * edAlpha n K k :=
      mul_self_nonneg _
    have hN2 : (0 : ℝ) < 2 * ((n : ℝ) * n) := by positivity
    have h4 : (edAlpha n K k * (2 * (n : ℝ)))
        * (edAlpha n K k * (2 * (n : ℝ))) ≤ (K : ℝ) * K :=
      mul_self_le_mul_self
        (mul_nonneg (edAlpha_nonneg n K k) (by positivity)) haK
    refine le_of_mul_le_mul_right ?_ hN2
    calc ((k : ℝ) + 1) * (edAlpha n K k * edAlpha n K k)
          * (2 * ((n : ℝ) * n))
        ≤ 2 * (K : ℝ) * (edAlpha n K k * edAlpha n K k)
          * (2 * ((n : ℝ) * n)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h2 hc0) (le_of_lt hN2)
      _ = (K : ℝ) * ((edAlpha n K k * (2 * (n : ℝ)))
          * (edAlpha n K k * (2 * (n : ℝ)))) := by ring
      _ ≤ (K : ℝ) * ((K : ℝ) * K) :=
          mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg K)
      _ = (K : ℝ) * K * K := by ring
      _ ≤ 2 * ((n : ℝ) * n) := hK'
      _ = 1 * (2 * ((n : ℝ) * n)) := (one_mul _).symm

/-- The step bound with `B = (2n)⁻¹·(2n)⁻¹`. -/
lemma edAlpha_step_le (n K k : ℕ) :
    (edAlpha n K k - edAlpha n K (k + 1))
        * (edAlpha n K k - edAlpha n K (k + 1))
      ≤ (2 * (n : ℝ))⁻¹ * (2 * (n : ℝ))⁻¹ := by
  have hA21 : (2 * K - max (k + 1) K) ≤ (2 * K - max k K) := by omega
  have hdiff : edAlpha n K k - edAlpha n K (k + 1)
      = (((2 * K - max k K) - (2 * K - max (k + 1) K) : ℕ) : ℝ)
          / (2 * (n : ℝ)) := by
    rw [Nat.cast_sub hA21, edAlpha, edAlpha, div_sub_div_same]
  have hd1 : (((2 * K - max k K) - (2 * K - max (k + 1) K) : ℕ) : ℝ)
      ≤ 1 := by
    have h : (2 * K - max k K) - (2 * K - max (k + 1) K) ≤ 1 := by omega
    exact_mod_cast h
  have hd0 : (0 : ℝ)
      ≤ (((2 * K - max k K) - (2 * K - max (k + 1) K) : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hinv0 : (0 : ℝ) ≤ (2 * (n : ℝ))⁻¹ := by positivity
  rw [hdiff, div_eq_mul_inv]
  calc (((2 * K - max k K) - (2 * K - max (k + 1) K) : ℕ) : ℝ)
        * (2 * (n : ℝ))⁻¹
        * ((((2 * K - max k K) - (2 * K - max (k + 1) K) : ℕ) : ℝ)
          * (2 * (n : ℝ))⁻¹)
      = ((((2 * K - max k K) - (2 * K - max (k + 1) K) : ℕ) : ℝ)
          * (((2 * K - max k K) - (2 * K - max (k + 1) K) : ℕ) : ℝ))
        * ((2 * (n : ℝ))⁻¹ * (2 * (n : ℝ))⁻¹) := by ring
    _ ≤ 1 * ((2 * (n : ℝ))⁻¹ * (2 * (n : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_right (by nlinarith [hd0, hd1])
          (mul_nonneg hinv0 hinv0)
    _ = (2 * (n : ℝ))⁻¹ * (2 * (n : ℝ))⁻¹ := one_mul _

/-! ## The lower bound -/

/-- The end-game arithmetic over abstract reals: the `q`-powers cancel
exactly against the counting estimates. -/
private lemma lower_value_arith (m : ℕ) {K n q ch F1 F0 : ℝ}
    (hn0 : 0 < n) (hq0 : 0 < q) (hK0 : 0 ≤ K)
    (hch : n * n ≤ 4 * ch)
    (hF1 : q ^ m / 2 ≤ F1)
    (hF0 : q ^ (m + 1) / 2 ≤ F0) :
    K / 8 ≤ K / (2 * n) * ((Real.sqrt q)⁻¹ * q⁻¹ ^ m)
      * (Real.sqrt ch * Real.sqrt F1) * Real.sqrt F0 := by
  have hq0' : (0 : ℝ) ≤ q := le_of_lt hq0
  have hsq : Real.sqrt q * q ^ m / 2
      ≤ Real.sqrt F1 * Real.sqrt F0 := by
    have h1 : Real.sqrt (q ^ m / 2) ≤ Real.sqrt F1 :=
      Real.sqrt_le_sqrt hF1
    have h2 : Real.sqrt (q ^ (m + 1) / 2) ≤ Real.sqrt F0 :=
      Real.sqrt_le_sqrt hF0
    have h3 : Real.sqrt (q ^ m / 2) * Real.sqrt (q ^ (m + 1) / 2)
        = Real.sqrt q * q ^ m / 2 := by
      rw [← Real.sqrt_mul (by positivity)]
      rw [show q ^ m / 2 * (q ^ (m + 1) / 2)
          = q * (q ^ m / 2) ^ 2 from by rw [pow_succ]; ring]
      rw [Real.sqrt_mul hq0', Real.sqrt_sq (by positivity)]
      ring
    calc Real.sqrt q * q ^ m / 2
        = Real.sqrt (q ^ m / 2) * Real.sqrt (q ^ (m + 1) / 2) := h3.symm
      _ ≤ Real.sqrt F1 * Real.sqrt F0 :=
          mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsch : n / 2 ≤ Real.sqrt ch := by
    rw [show n / 2 = Real.sqrt ((n / 2) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    rw [show ((n / 2) : ℝ) ^ 2 = n * n / 4 from by ring]
    linarith
  have hKc : (0 : ℝ) ≤ K / (2 * n) * ((Real.sqrt q)⁻¹ * q⁻¹ ^ m) :=
    mul_nonneg (div_nonneg hK0 (by positivity)) (by positivity)
  calc K / 8
      = K / (2 * n) * ((Real.sqrt q)⁻¹ * q⁻¹ ^ m)
        * ((n / 2) * (Real.sqrt q * q ^ m / 2)) := by
        have hn' : n ≠ 0 := ne_of_gt hn0
        have h1 : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hq0)
        have h2 : (q : ℝ) ^ m ≠ 0 := pow_ne_zero m (ne_of_gt hq0)
        rw [inv_pow]
        field_simp
        ring
    _ ≤ K / (2 * n) * ((Real.sqrt q)⁻¹ * q⁻¹ ^ m)
        * (Real.sqrt ch * (Real.sqrt F1 * Real.sqrt F0)) := by
        refine mul_le_mul_of_nonneg_left ?_ hKc
        exact mul_le_mul hsch hsq (by positivity) (Real.sqrt_nonneg _)
    _ = K / (2 * n) * ((Real.sqrt q)⁻¹ * q⁻¹ ^ m)
        * (Real.sqrt ch * Real.sqrt F1) * Real.sqrt F0 := by ring

/-- **Belovs' adversary lower bound for element distinctness**,
`K`-parametric form: for `n ≥ 2`, alphabet size `q ≥ 4n²`, and any level
parameter with `K³ ≤ 2n²`, `advPM(ED) ≥ K/64`. -/
theorem le_advPM_edFun {K : ℕ}
    (hn : 2 ≤ Fintype.card ι)
    (hq : 4 * (Fintype.card ι * Fintype.card ι) ≤ Fintype.card σ)
    (hK : K * K * K ≤ 2 * (Fintype.card ι * Fintype.card ι)) :
    (K : ℝ) / 64 ≤ advPM (edFun (ι := ι) (σ := σ)) := by
  have hn2 : (0 : ℕ) < Fintype.card ι := by omega
  have hq0 : (0 : ℕ) < Fintype.card σ := by
    have h4 : 4 ≤ Fintype.card ι * Fintype.card ι := Nat.mul_le_mul hn hn
    omega
  haveI : Nonempty σ := Fintype.card_pos_iff.mp hq0
  have hqn : Fintype.card ι ≤ Fintype.card σ := by
    have h4 : Fintype.card ι ≤ Fintype.card ι * Fintype.card ι :=
      Nat.le_mul_of_pos_left _ hn2
    omega
  have hq2 : Fintype.card ι * Fintype.card ι ≤ Fintype.card σ := by omega
  -- the α-sequence data
  have hα0 : ∀ k, 0 ≤ edAlpha (Fintype.card ι) K k :=
    fun k => edAlpha_nonneg _ K k
  have hA : ∀ k : ℕ, ((k : ℝ) + 1)
      * (edAlpha (Fintype.card ι) K k * edAlpha (Fintype.card ι) K k)
      ≤ 1 := edAlpha_quad_le (Fintype.card ι) K hK
  have hB : ∀ k : ℕ, (edAlpha (Fintype.card ι) K k
        - edAlpha (Fintype.card ι) K (k + 1))
      * (edAlpha (Fintype.card ι) K k
        - edAlpha (Fintype.card ι) K (k + 1))
      ≤ (2 * (Fintype.card ι : ℝ))⁻¹
          * (2 * (Fintype.card ι : ℝ))⁻¹ :=
    fun k => edAlpha_step_le (Fintype.card ι) K k
  have hB0 : (0 : ℝ) ≤ (2 * (Fintype.card ι : ℝ))⁻¹
      * (2 * (Fintype.card ι : ℝ))⁻¹ := by positivity
  have hnR : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hn2
  -- the mask bound at the numeric value
  have hWval : 2 * 1 + 5 * (Fintype.card ι : ℝ) ^ 2
      * ((2 * (Fintype.card ι : ℝ))⁻¹ * (2 * (Fintype.card ι : ℝ))⁻¹)
      = 13 / 4 := by
    field_simp
    ring
  have hmask : ∀ i, ‖(edGammaMat (ι := ι) (σ := σ)
      (edAlpha (Fintype.card ι) K)
      + (edGammaMat (edAlpha (Fintype.card ι) K))ᵀ) ⊙ advD i‖ ≤ 8 := by
    intro i
    have h := norm_edGammaMat_symm_hadamard_le (σ := σ)
      (edAlpha (Fintype.card ι) K) hA hB (by norm_num) hB0 i
    rw [hWval] at h
    have h13 : Real.sqrt (4 * (13 / 4)) ≤ 4 := by
      rw [show (4 : ℝ) * (13 / 4) = 13 from by norm_num]
      rw [show (4 : ℝ) = Real.sqrt 16 from by
        rw [show (16 : ℝ) = 4 ^ 2 from by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  -- the value bound at the numeric counts
  have hnorm : (K : ℝ) / 8 ≤ ‖edGammaMat (ι := ι) (σ := σ)
      (edAlpha (Fintype.card ι) K)
      + (edGammaMat (edAlpha (Fintype.card ι) K))ᵀ‖ := by
    refine le_trans ?_ (norm_edGammaMat_symm_ge (σ := σ)
      (edAlpha (Fintype.card ι) K) hα0)
    rw [edAlpha_zero_eq, card_edLegal, card_injectives,
      Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card ι = m + 1 :=
      ⟨Fintype.card ι - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel]
    have hm1 : 1 ≤ m := by omega
    have hq2' : (m + 1) * (m + 1) ≤ Fintype.card σ := by
      rw [← hm]
      exact hq2
    have hdvd : 2 ∣ (m + 1) * m := by
      rcases Nat.even_or_odd m with he | ho
      · obtain ⟨t, ht⟩ := he
        exact ⟨(m + 1) * t, by rw [ht]; ring⟩
      · obtain ⟨t, ht⟩ := ho
        exact ⟨(t + 1) * m, by rw [ht]; ring⟩
    have hch' : (m + 1) * (m + 1) ≤ 4 * ((m + 1).choose 2) := by
      rw [Nat.choose_two_right, show m + 1 - 1 = m from rfl]
      obtain ⟨t, ht⟩ := hdvd
      rw [ht, Nat.mul_div_cancel_left t (by norm_num : 0 < 2)]
      nlinarith [hm1, ht]
    have hF1' : ((Fintype.card σ : ℝ)) ^ m / 2
        ≤ ((∏ j ∈ Finset.range m, (Fintype.card σ - j) : ℕ) : ℝ) := by
      rw [cast_falling_factorial _ _ (by omega : m ≤ Fintype.card σ)]
      exact prod_range_sub_ge_half _ _ hq0
        (le_trans (Nat.mul_le_mul (Nat.le_succ m) (Nat.le_succ m)) hq2')
    have hF0' : ((Fintype.card σ : ℝ)) ^ (m + 1) / 2
        ≤ ((∏ j ∈ Finset.range (m + 1),
            (Fintype.card σ - j) : ℕ) : ℝ) := by
      rw [cast_falling_factorial _ _ (by omega : m + 1 ≤ Fintype.card σ)]
      exact prod_range_sub_ge_half _ _ hq0 hq2'
    exact lower_value_arith m
      (by exact_mod_cast Nat.succ_pos m)
      (by exact_mod_cast hq0)
      (Nat.cast_nonneg K)
      (by exact_mod_cast hch')
      hF1' hF0'
  -- assemble
  have hadv := norm_div_le_advPM
    (isAdvMatrix_edGammaMat (edAlpha (Fintype.card ι) K)) hmask
    (by norm_num : (0 : ℝ) < 8)
  calc (K : ℝ) / 64 = ((K : ℝ) / 8) * (8 : ℝ)⁻¹ := by ring
    _ ≤ ‖edGammaMat (ι := ι) (σ := σ) (edAlpha (Fintype.card ι) K)
        + (edGammaMat (edAlpha (Fintype.card ι) K))ᵀ‖ * (8 : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hnorm (by norm_num)
    _ = ‖edGammaMat (ι := ι) (σ := σ) (edAlpha (Fintype.card ι) K)
        + (edGammaMat (edAlpha (Fintype.card ι) K))ᵀ‖ / 8 := by
        rw [div_eq_mul_inv]
    _ ≤ advPM (edFun (ι := ι) (σ := σ)) := hadv

/-- **The Ω(n^{2/3}) form**: instantiating `K := ⌊n^{2/3}⌋`. -/
theorem advPM_edFun_ge (hn : 2 ≤ Fintype.card ι)
    (hq : 4 * (Fintype.card ι * Fintype.card ι) ≤ Fintype.card σ) :
    (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) / 128
      ≤ advPM (edFun (ι := ι) (σ := σ)) := by
  have hn1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    have h : (1 : ℕ) ≤ Fintype.card ι := by omega
    exact_mod_cast h
  have hx0 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) := by
    positivity
  have hx1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((2 : ℝ) / 3) := (Real.one_rpow _).symm
      _ ≤ (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) :=
          Real.rpow_le_rpow (by norm_num) hn1 (by norm_num)
  have hKle : ((⌊(Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)⌋₊ : ℕ) : ℝ)
      ≤ (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) := Nat.floor_le hx0
  have hcube : ((⌊(Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)⌋₊ : ℕ) : ℝ)
        ^ (3 : ℕ)
      ≤ (Fintype.card ι : ℝ) ^ (2 : ℕ) := by
    calc ((⌊(Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)⌋₊ : ℕ) : ℝ) ^ (3 : ℕ)
        ≤ ((Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hKle 3
      _ = (Fintype.card ι : ℝ) ^ (((2 : ℝ) / 3) * ((3 : ℕ) : ℝ)) := by
          rw [← Real.rpow_natCast
            ((Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)) 3,
            ← Real.rpow_mul (Nat.cast_nonneg _)]
      _ = (Fintype.card ι : ℝ) ^ ((2 : ℕ) : ℝ) := by
          congr 1
          norm_num
      _ = (Fintype.card ι : ℝ) ^ (2 : ℕ) := Real.rpow_natCast _ 2
  have hK3 : ⌊(Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)⌋₊
      * ⌊(Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)⌋₊
      * ⌊(Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)⌋₊
      ≤ 2 * (Fintype.card ι * Fintype.card ι) := by
    have hcast : ((⌊(Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)⌋₊
        * ⌊(Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)⌋₊
        * ⌊(Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)⌋₊ : ℕ) : ℝ)
        ≤ ((Fintype.card ι * Fintype.card ι : ℕ) : ℝ) := by
      push_cast
      calc ((⌊(Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)⌋₊ : ℕ) : ℝ)
            * ((⌊(Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)⌋₊ : ℕ) : ℝ)
            * ((⌊(Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)⌋₊ : ℕ) : ℝ)
          = ((⌊(Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)⌋₊ : ℕ) : ℝ)
              ^ (3 : ℕ) := by ring
        _ ≤ (Fintype.card ι : ℝ) ^ (2 : ℕ) := hcube
        _ = (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) := by ring
    have h := Nat.cast_le (α := ℝ) |>.mp hcast
    omega
  have hmain := le_advPM_edFun (ι := ι) (σ := σ) hn hq hK3
  have hxK : (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) / 2
      ≤ ((⌊(Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)⌋₊ : ℕ) : ℝ) := by
    rcases lt_or_ge ((Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)) 2 with h2 | h2
    · have hfl1 : (1 : ℕ) ≤ ⌊(Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)⌋₊ :=
        Nat.le_floor (by exact_mod_cast hx1)
      have h1' : (1 : ℝ)
          ≤ ((⌊(Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3)⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast hfl1
      linarith
    · have hfl := Nat.sub_one_lt_floor
        ((Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3))
      linarith
  linarith [hmain, hxK]

/-- **The n^{2/3} characterization of element distinctness**: for `n ≥ 2`
and alphabet size at least `4n²`,
`n^{2/3}/128 ≤ ADV±(ED) ≤ 8·n^{2/3}`.

The operational counterparts live in `Quantum/EDApplications.lean`:
`ed_qQuery_sandwich` (`n^{2/3}/4608 ≤ Q_{1/3}(ED) ≤ min{n, 73728·n^{2/3}}`,
native transposition oracle) and `ed_oneHotQQuery_sandwich`
(`n^{2/3}/9216 ≤ Q^{1-hot}_{1/3}(ED) ≤ min{n, 147456·n^{2/3}}`, the
canonical one-hot XOR model), both from this sandwich's two certificates. -/
theorem advPM_edFun_sandwich (ι σ : Type) [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ]
    (hn : 2 ≤ Fintype.card ι)
    (hq : 4 * (Fintype.card ι * Fintype.card ι) ≤ Fintype.card σ) :
    (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) / 128
        ≤ advPM (edFun (ι := ι) (σ := σ))
      ∧ advPM (edFun (ι := ι) (σ := σ))
        ≤ 8 * (Fintype.card ι : ℝ) ^ ((2 : ℝ) / 3) :=
  ⟨advPM_edFun_ge hn hq, advPM_edFun_le ι σ⟩

end QuantumQueryComplexity
