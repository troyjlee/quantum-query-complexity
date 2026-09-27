import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Belovs' Lemma 3: the signed sum over injective tuples is nonnegative

For an injective labelling `x : Fin k → α` with values in a ground set `S`,

    gee q k S x  :=  ∑_{y injective, values ∈ S}  ∏ i (q·[y i = x i] − 1).

The paper's `g(k, ℓ, q)` is this quantity for `ℓ = |S|`; the headline
`gee_nonneg` states `0 ≤ gee q k S x` whenever `x` is injective with values
in `S` and `|S| ≤ q`.  It is the only place the ED lower bound's
illegal-row-removal argument needs real combinatorics: the entry sum of
`E₁^{⊗k}` restricted to distinct-valued rows and columns is
`q^{-k} · ∑_{rows} gee q k univ (row)` — nonnegative by this lemma.

The proof is by strong induction, peeling the value at position `0`
(`gee_peel`, via the `insertNth/removeNth` bijection `sum_injTuples_succ`):
the case `y 0 = x 0` contributes `(q−1)·g(k−1, ℓ−1)`, the values outside the
labels contribute `−(ℓ−k)·g(k−1, ℓ−1)` (equal ground sets up to a
transposition — `gee_erase_swap`), and a value `x j` of another label kills
that label's position, whose sum is a constant count (`gee_out`), giving
`+(ℓ−k+1)(k−1)·g(k−2, ℓ−1)`.  All three multiples are nonnegative when
`k ≤ ℓ ≤ q`.
-/

namespace QuantumQueryComplexity

variable {α : Type*} [DecidableEq α]

/-! ## Injective tuples -/

/-- The injective tuples of length `k` with values in `S`. -/
noncomputable def injTuples (k : ℕ) (S : Finset α) : Finset (Fin k → α) :=
  (Fintype.piFinset fun _ : Fin k => S).filter Function.Injective

lemma mem_injTuples {k : ℕ} {S : Finset α} {y : Fin k → α} :
    y ∈ injTuples k S ↔ (∀ i, y i ∈ S) ∧ Function.Injective y := by
  rw [injTuples, Finset.mem_filter, Fintype.mem_piFinset]

/-- Belovs' signed sum over injective tuples. -/
noncomputable def gee (q k : ℕ) (S : Finset α) (x : Fin k → α) : ℝ :=
  ∑ y ∈ injTuples k S,
    ∏ i, ((q : ℝ) * (if y i = x i then 1 else 0) - 1)

lemma gee_zero (q : ℕ) (S : Finset α) (x : Fin 0 → α) : gee q 0 S x = 1 := by
  rw [gee, show injTuples 0 S = {(Fin.elim0 : Fin 0 → α)} from
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨mem_injTuples.mpr ⟨fun i => i.elim0,
        Function.injective_of_subsingleton _⟩,
       fun y _ => funext fun i => i.elim0⟩,
    Finset.sum_singleton]
  simp

/-! ## Peeling one position -/

/-- The `insertNth/removeNth` bijection: summing over injective
`(k+1)`-tuples is summing over the value at position `p` and an injective
`k`-tuple avoiding it. -/
lemma sum_injTuples_succ {k : ℕ} (S : Finset α) (p : Fin (k + 1))
    (F : (Fin (k + 1) → α) → ℝ) :
    (∑ y ∈ injTuples (k + 1) S, F y)
      = ∑ v ∈ S, ∑ z ∈ injTuples k (S.erase v), F (p.insertNth v z) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun y => ⟨y p, p.removeNth y⟩)
    (fun q => p.insertNth q.1 q.2) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    obtain ⟨hval, hinj⟩ := mem_injTuples.mp hy
    refine Finset.mem_sigma.mpr ⟨hval p, mem_injTuples.mpr ⟨fun i => ?_, ?_⟩⟩
    · refine Finset.mem_erase.mpr ⟨fun h => ?_, hval _⟩
      exact Fin.succAbove_ne p i (hinj h)
    · exact hinj.comp (Fin.succAbove_right_injective)
  · rintro ⟨v, z⟩ hq
    obtain ⟨hv, hz⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hzval, hzinj⟩ := mem_injTuples.mp hz
    refine mem_injTuples.mpr ⟨fun i => ?_, fun a b hab => ?_⟩
    · by_cases hi : i = p
      · rw [hi, Fin.insertNth_apply_same]
        exact hv
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
        rw [Fin.insertNth_apply_succAbove]
        exact Finset.mem_of_mem_erase (hzval j)
    · by_cases ha : a = p <;> by_cases hb : b = p
      · rw [ha, hb]
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hb
        rw [ha, Fin.insertNth_apply_same,
          Fin.insertNth_apply_succAbove] at hab
        exact absurd hab.symm (Finset.mem_erase.mp (hzval j)).1
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq ha
        rw [hb, Fin.insertNth_apply_same,
          Fin.insertNth_apply_succAbove] at hab
        exact absurd hab (Finset.mem_erase.mp (hzval j)).1
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq ha
        obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hb
        rw [Fin.insertNth_apply_succAbove,
          Fin.insertNth_apply_succAbove] at hab
        rw [hzinj hab]
  · intro y _
    exact Fin.insertNth_self_removeNth p y
  · rintro ⟨v, z⟩ _
    simp only [Fin.insertNth_apply_same, Fin.removeNth_insertNth]
  · intro y _
    rw [Fin.insertNth_self_removeNth]

/-- Peeling the factor at position `p`. -/
lemma gee_peel (q : ℕ) {k : ℕ} (S : Finset α) (x : Fin (k + 1) → α)
    (p : Fin (k + 1)) :
    gee q (k + 1) S x
      = ∑ v ∈ S, ((q : ℝ) * (if v = x p then 1 else 0) - 1)
          * gee q k (S.erase v) (p.removeNth x) := by
  rw [gee, sum_injTuples_succ S p]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [gee, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Fin.prod_univ_succAbove _ p]
  congr 1
  · rw [Fin.insertNth_apply_same]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.insertNth_apply_succAbove]
    rfl

/-- **Summing out a position whose label left the ground set**: every value
choice contributes the constant factor `−1`, and there are `|S| − k` choices
whatever the rest of the tuple does. -/
lemma gee_out (q : ℕ) {k : ℕ} (S : Finset α) (x : Fin (k + 1) → α)
    (p : Fin (k + 1)) (hp : x p ∉ S) :
    gee q (k + 1) S x
      = -(((S.card : ℝ) - k)) * gee q k S (p.removeNth x) := by
  have hfac : ∀ v ∈ S, ((q : ℝ) * (if v = x p then 1 else 0) - 1)
      * gee q k (S.erase v) (p.removeNth x)
      = -(gee q k (S.erase v) (p.removeNth x)) := by
    intro v hv
    rw [if_neg (fun h : v = x p => hp (h ▸ hv)), mul_zero, zero_sub,
      neg_one_mul]
  have hmem : ∀ (v : α) (z : Fin k → α),
      v ∈ S ∧ z ∈ injTuples k (S.erase v)
        ↔ v ∈ S.filter (fun v => ∀ i, z i ≠ v) ∧ z ∈ injTuples k S := by
    intro v z
    constructor
    · rintro ⟨hvS, hz⟩
      obtain ⟨hzval, hzinj⟩ := mem_injTuples.mp hz
      exact ⟨Finset.mem_filter.mpr ⟨hvS, fun i =>
          (Finset.mem_erase.mp (hzval i)).1⟩,
        mem_injTuples.mpr ⟨fun i =>
          Finset.mem_of_mem_erase (hzval i), hzinj⟩⟩
    · rintro ⟨hvf, hz⟩
      obtain ⟨hvS, hne⟩ := Finset.mem_filter.mp hvf
      obtain ⟨hzval, hzinj⟩ := mem_injTuples.mp hz
      exact ⟨hvS, mem_injTuples.mpr ⟨fun i =>
        Finset.mem_erase.mpr ⟨hne i, hzval i⟩, hzinj⟩⟩
  have hswap : (∑ v ∈ S, gee q k (S.erase v) (p.removeNth x))
      = ((S.card : ℝ) - k) * gee q k S (p.removeNth x) := by
    simp only [gee]
    rw [Finset.sum_comm' hmem, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    obtain ⟨hzval, hzinj⟩ := mem_injTuples.mp hz
    have himg : S.filter (fun v => ∀ i, z i ≠ v)
        = S \ Finset.image z Finset.univ := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_image,
        Finset.mem_univ, true_and]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun ⟨i, hi⟩ => h2 i hi⟩,
        fun ⟨h1, h2⟩ => ⟨h1, fun i hi => h2 ⟨i, hi⟩⟩⟩
    have hkS : k ≤ S.card := by
      calc k = (Finset.image z Finset.univ).card := by
            rw [Finset.card_image_of_injective _ hzinj, Finset.card_univ,
              Fintype.card_fin]
        _ ≤ S.card := Finset.card_le_card fun w hw => by
            obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
            exact hzval i
    have hcard : ((S.filter fun v => ∀ i, z i ≠ v).card : ℝ)
        = (S.card : ℝ) - k := by
      rw [himg, Finset.card_sdiff, Finset.inter_eq_left.mpr
          (fun w hw => by
            obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
            exact hzval i),
        Finset.card_image_of_injective _ hzinj, Finset.card_univ,
        Fintype.card_fin, Nat.cast_sub hkS]
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
  rw [gee_peel q S x p, Finset.sum_congr rfl hfac, Finset.sum_neg_distrib,
    hswap, neg_mul]

/-! ## Invariance under relabelling -/

lemma gee_equiv (q k : ℕ) (S : Finset α) (x : Fin k → α) (φ : α ≃ α) :
    gee q k (S.image φ) (φ ∘ x) = gee q k S x := by
  rw [gee, gee]
  refine Finset.sum_nbij' (fun y => φ.symm ∘ y) (fun y => φ ∘ y)
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    obtain ⟨hval, hinj⟩ := mem_injTuples.mp hy
    refine mem_injTuples.mpr ⟨fun i => ?_, (Equiv.injective φ.symm).comp hinj⟩
    obtain ⟨s, hs, hsy⟩ := Finset.mem_image.mp (hval i)
    rw [Function.comp_apply, ← hsy, Equiv.symm_apply_apply]
    exact hs
  · intro y hy
    obtain ⟨hval, hinj⟩ := mem_injTuples.mp hy
    exact mem_injTuples.mpr ⟨fun i => Finset.mem_image_of_mem φ (hval i),
      (Equiv.injective φ).comp hinj⟩
  · intro y _
    funext i
    exact Equiv.apply_symm_apply φ (y i)
  · intro y _
    funext i
    exact Equiv.symm_apply_apply φ (y i)
  · intro y _
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : φ.symm (y i) = x i
    · have h2 : y i = φ (x i) := by rw [← h, Equiv.apply_symm_apply]
      simp [h, h2]
    · have h2 : ¬ y i = φ (x i) := fun hc =>
        h (by rw [hc, Equiv.symm_apply_apply])
      simp [h, h2]

/-- Erasing any non-label value from the ground set gives the same sum: a
transposition carries one ground set to the other and fixes the labels. -/
lemma gee_erase_swap (q : ℕ) {k : ℕ} {S : Finset α} {x : Fin k → α}
    {a v : α} (ha : a ∈ S) (hv : v ∈ S)
    (hxa : ∀ i, x i ≠ a) (hxv : ∀ i, x i ≠ v) :
    gee q k (S.erase a) x = gee q k (S.erase v) x := by
  by_cases hav : a = v
  · rw [hav]
  · have hcomp : (Equiv.swap a v) ∘ x = x := by
      funext i
      exact Equiv.swap_apply_of_ne_of_ne (hxa i) (hxv i)
    have himg : (S.erase a).image (Equiv.swap a v) = S.erase v := by
      ext w
      simp only [Finset.mem_image, Finset.mem_erase]
      constructor
      · rintro ⟨u, ⟨hua, huS⟩, rfl⟩
        by_cases huv : u = v
        · rw [huv, Equiv.swap_apply_right]
          exact ⟨hav, ha⟩
        · rw [Equiv.swap_apply_of_ne_of_ne hua huv]
          exact ⟨huv, huS⟩
      · rintro ⟨hwv, hwS⟩
        by_cases hwa : w = a
        · exact ⟨v, ⟨fun h => hav h.symm, hv⟩,
            by rw [Equiv.swap_apply_right, hwa]⟩
        · exact ⟨w, ⟨hwa, hwS⟩, Equiv.swap_apply_of_ne_of_ne hwa hwv⟩
    calc gee q k (S.erase a) x
        = gee q k ((S.erase a).image (Equiv.swap a v))
            ((Equiv.swap a v) ∘ x) := (gee_equiv q k _ x _).symm
      _ = gee q k (S.erase v) x := by rw [himg, hcomp]

/-! ## The main nonnegativity theorem -/

/-- **Belovs' Lemma 3**: for an injective labelling inside a ground set of
size at most `q`, the signed sum is nonnegative. -/
theorem gee_nonneg (q : ℕ) (k : ℕ) : ∀ (S : Finset α) (x : Fin k → α),
    Function.Injective x → (∀ i, x i ∈ S) → S.card ≤ q →
    0 ≤ gee q k S x := by
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    rcases k with _ | k1
    · intro S x hxinj hxS hSq
      rw [gee_zero]
      norm_num
    rcases k1 with _ | m
    · intro S x hxinj hxS hSq
      rw [gee_peel q S x 0,
        Finset.sum_congr rfl fun v (_ : v ∈ S) => by
          rw [gee_zero, mul_one],
        Finset.sum_sub_distrib,
        Finset.sum_congr rfl fun v (_ : v ∈ S) =>
          show (q : ℝ) * (if v = x 0 then 1 else 0)
              = if v = x 0 then (q : ℝ) else 0 from by
            by_cases h : v = x 0 <;> simp [h],
        Finset.sum_ite_eq' S (x 0) fun _ => (q : ℝ), if_pos (hxS 0),
        Finset.sum_const, nsmul_eq_mul, mul_one]
      have hq : (S.card : ℝ) ≤ (q : ℝ) := by exact_mod_cast hSq
      linarith
    · intro S x hxinj hxS hSq
      rw [gee_peel q S x 0]
      set x' := (0 : Fin (m + 2)).removeNth x with hx'def
      have hx'inj : Function.Injective x' :=
        hxinj.comp Fin.succAbove_right_injective
      have hx'S : ∀ i, x' i ∈ S := fun i => hxS _
      have hx'ne0 : ∀ i, x' i ≠ x 0 := fun i h =>
        absurd (hxinj h) (Fin.succAbove_ne 0 i)
      set R := Finset.image x' Finset.univ with hRdef
      have hRcard : R.card = m + 1 := by
        rw [hRdef, Finset.card_image_of_injective _ hx'inj,
          Finset.card_univ, Fintype.card_fin]
      have hRS : R ⊆ S := fun w hw => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
        exact hx'S i
      have hx0R : x 0 ∉ R := fun h => by
        obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
        exact hx'ne0 i hi
      have hsub : insert (x 0) R ⊆ S := Finset.insert_subset (hxS 0) hRS
      have hkl : m + 2 ≤ S.card := by
        calc m + 2 = (insert (x 0) R).card := by
              rw [Finset.card_insert_of_notMem hx0R, hRcard]
          _ ≤ S.card := Finset.card_le_card hsub
      have hGnn : 0 ≤ gee q (m + 1) (S.erase (x 0)) x' :=
        IH (m + 1) (by omega) _ _ hx'inj
          (fun i => Finset.mem_erase.mpr ⟨hx'ne0 i, hx'S i⟩)
          (le_trans (Finset.card_erase_le) hSq)
      -- split the sum into the label value, the other labels, and the rest
      rw [← Finset.sum_sdiff hsub, Finset.sum_insert hx0R]
      have hrest : ∀ v ∈ S \ insert (x 0) R,
          ((q : ℝ) * (if v = x 0 then 1 else 0) - 1)
            * gee q (m + 1) (S.erase v) x'
          = -(gee q (m + 1) (S.erase (x 0)) x') := by
        intro v hv
        obtain ⟨hvS, hvni⟩ := Finset.mem_sdiff.mp hv
        have hvx0 : v ≠ x 0 := fun h =>
          hvni (h ▸ Finset.mem_insert_self _ _)
        have hvR : ∀ i, x' i ≠ v := fun i h =>
          hvni (Finset.mem_insert_of_mem
            (h ▸ Finset.mem_image_of_mem x' (Finset.mem_univ i)))
        rw [if_neg hvx0, mul_zero, zero_sub, neg_one_mul,
          gee_erase_swap q hvS (hxS 0) hvR hx'ne0]
      have h2 : (∑ v ∈ S \ insert (x 0) R,
          ((q : ℝ) * (if v = x 0 then 1 else 0) - 1)
            * gee q (m + 1) (S.erase v) x')
          = -(((S.card - (m + 2) : ℕ) : ℝ)
              * gee q (m + 1) (S.erase (x 0)) x') := by
        rw [Finset.sum_congr rfl hrest, Finset.sum_neg_distrib,
          Finset.sum_const, nsmul_eq_mul,
          show (S \ insert (x 0) R).card = S.card - (m + 2) from by
            rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
              Finset.card_insert_of_notMem hx0R, hRcard]]
      have hRterm : ∀ v ∈ R, 0 ≤ ((q : ℝ) * (if v = x 0 then 1 else 0) - 1)
          * gee q (m + 1) (S.erase v) x' := by
        intro v hvR
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hvR
        rw [if_neg (hx'ne0 j), mul_zero, zero_sub, neg_one_mul,
          gee_out q (S.erase (x' j)) x' j (Finset.notMem_erase _ _),
          Finset.card_erase_of_mem (hx'S j)]
        have hG'j : 0 ≤ gee q m (S.erase (x' j)) (j.removeNth x') :=
          IH m (by omega) _ _ (hx'inj.comp Fin.succAbove_right_injective)
            (fun i => Finset.mem_erase.mpr
              ⟨fun h => absurd (hx'inj h) (Fin.succAbove_ne j i), hx'S _⟩)
            (le_trans (Finset.card_erase_le) hSq)
        have hcast : (m : ℝ) + 1 ≤ ((S.card - 1 : ℕ) : ℝ) := by
          have h1 : m + 1 ≤ S.card - 1 := by omega
          exact_mod_cast h1
        nlinarith [hG'j]
      have h3 : 0 ≤ ∑ v ∈ R,
          ((q : ℝ) * (if v = x 0 then 1 else 0) - 1)
            * gee q (m + 1) (S.erase v) x' :=
        Finset.sum_nonneg hRterm
      have h1 : ((q : ℝ) * (if x 0 = x 0 then 1 else 0) - 1)
          * gee q (m + 1) (S.erase (x 0)) x'
          = ((q : ℝ) - 1) * gee q (m + 1) (S.erase (x 0)) x' := by
        rw [if_pos rfl, mul_one]
      have hc2le : ((S.card - (m + 2) : ℕ) : ℝ) ≤ (q : ℝ) - 1 := by
        have h1' : S.card - (m + 2) + 1 ≤ q := by omega
        have := (Nat.cast_le (α := ℝ)).mpr h1'
        push_cast at this
        linarith
      have hkey : 0 ≤ ((q : ℝ) - 1 - ((S.card - (m + 2) : ℕ) : ℝ))
          * gee q (m + 1) (S.erase (x 0)) x' :=
        mul_nonneg (by linarith) hGnn
      rw [h2, h1]
      linarith

end QuantumQueryComplexity
