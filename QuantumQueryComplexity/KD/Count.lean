import QuantumQueryComplexity.KD.Flow
import QuantumQueryComplexity.ED.Count
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Counting for the k-distinctness learning graph

The `k`-fold generalizations of the ED counting identities:

* `choose_ratio_pow` — `C(n,t)·∏_{i<k}(n-t-i) = ∏_{i<k}(n-i)·C(n-k,t)`
  (hypothesis-free; all degenerate cases vanish on both sides);
* `choose_shift` — `C(n,r+ℓ)·∏_{s<ℓ}(r+1+s) = C(n,r)·∏_{s<ℓ}(n-r-s)`;
* the stage-I edge-count bound `≤ 2^{k+1}` per level and the stage-`ℓ`
  bound `C(n,r+ℓ)(n-r-ℓ)(r+1)^ℓ ≤ 2^k n^{ℓ+1} C(n-k,r)`, both under
  `2(r+k) ≤ n`;
* the stage-`ℓ` support count: the vertices with prefix `ℓ` and
  cardinality `r+ℓ` biject with the `r`-subsets of `univ ∖ range a`.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The k-fold ratio identity -/

/-- `C(n,t)·∏_{i<k}(n-t-i) = ∏_{i<k}(n-i)·C(n-k,t)`, hypothesis-free. -/
lemma choose_ratio_pow (k : ℕ) : ∀ n t : ℕ,
    n.choose t * ∏ i ∈ Finset.range k, (n - t - i)
      = (∏ i ∈ Finset.range k, (n - i)) * (n - k).choose t := by
  induction k with
  | zero =>
    intro n t
    simp
  | succ k IH =>
    intro n t
    rw [Finset.prod_range_succ', Finset.prod_range_succ',
      Finset.prod_congr rfl fun i (_ : i ∈ Finset.range k) =>
        show n - t - (i + 1) = (n - 1) - t - i from by omega,
      Finset.prod_congr rfl
        (fun i (_ : i ∈ Finset.range k) =>
          show n - (i + 1) = (n - 1) - i from by omega),
      Nat.sub_zero, Nat.sub_zero]
    calc n.choose t * ((∏ i ∈ Finset.range k, ((n - 1) - t - i)) * (n - t))
        = ((n - t) * n.choose t)
            * ∏ i ∈ Finset.range k, ((n - 1) - t - i) := by ring
      _ = (n * (n - 1).choose t)
            * ∏ i ∈ Finset.range k, ((n - 1) - t - i) := by
          rw [sub_mul_choose]
      _ = n * ((n - 1).choose t
            * ∏ i ∈ Finset.range k, ((n - 1) - t - i)) := by ring
      _ = n * ((∏ i ∈ Finset.range k, ((n - 1) - i))
            * ((n - 1) - k).choose t) := by rw [IH (n - 1) t]
      _ = (∏ i ∈ Finset.range k, ((n - 1) - i)) * n
            * ((n - (k + 1)).choose t) := by
          rw [show (n - 1) - k = n - (k + 1) from by omega]
          ring

/-- Under `2t + k ≤ n` each ambient factor at most doubles. -/
lemma prod_range_sub_le (k n t : ℕ) (h : 2 * t + k ≤ n) :
    (∏ i ∈ Finset.range k, (n - i))
      ≤ 2 ^ k * ∏ i ∈ Finset.range k, (n - t - i) := by
  rw [show (2 : ℕ) ^ k = ∏ _i ∈ Finset.range k, 2 from by
      rw [Finset.prod_const, Finset.card_range],
    ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod' fun i hi => ?_
  have hik := Finset.mem_range.mp hi
  omega

/-- Stage-I per-level bound: the ambient edge count is at most `2^{k+1}`
times the `D`-internal one. -/
lemma kd_stageI_count_bound {n k r t : ℕ} (ht : t < r)
    (hrn : 2 * (r + k) ≤ n) :
    n.choose t * (n - t)
      ≤ 2 ^ (k + 1) * ((n - k).choose t * (n - k - t)) := by
  have hc : 0 < ∏ i ∈ Finset.range k, (n - t - i) := by
    refine Finset.prod_pos fun i hi => ?_
    have hik := Finset.mem_range.mp hi
    omega
  refine Nat.le_of_mul_le_mul_right ?_ hc
  calc n.choose t * (n - t) * ∏ i ∈ Finset.range k, (n - t - i)
      = (n - t) * (n.choose t * ∏ i ∈ Finset.range k, (n - t - i)) := by
        ring
    _ = (n - t) * ((∏ i ∈ Finset.range k, (n - i))
          * (n - k).choose t) := by rw [choose_ratio_pow k n t]
    _ ≤ (n - t) * ((2 ^ k * ∏ i ∈ Finset.range k, (n - t - i))
          * (n - k).choose t) :=
        Nat.mul_le_mul (le_refl _)
          (Nat.mul_le_mul (prod_range_sub_le k n t (by omega)) (le_refl _))
    _ ≤ (2 * (n - k - t)) * ((2 ^ k * ∏ i ∈ Finset.range k, (n - t - i))
          * (n - k).choose t) :=
        Nat.mul_le_mul (by omega) (le_refl _)
    _ = 2 ^ (k + 1) * ((n - k).choose t * (n - k - t))
          * ∏ i ∈ Finset.range k, (n - t - i) := by ring

/-- Dropping `k` ambient coordinates costs at most `2^k` on a binomial. -/
lemma kd_choose_le {n k r : ℕ} (hrn : 2 * (r + k) ≤ n) :
    n.choose r ≤ 2 ^ k * (n - k).choose r := by
  have hc : 0 < ∏ i ∈ Finset.range k, (n - r - i) := by
    refine Finset.prod_pos fun i hi => ?_
    have hik := Finset.mem_range.mp hi
    omega
  refine Nat.le_of_mul_le_mul_right ?_ hc
  calc n.choose r * ∏ i ∈ Finset.range k, (n - r - i)
      = (∏ i ∈ Finset.range k, (n - i)) * (n - k).choose r :=
        choose_ratio_pow k n r
    _ ≤ (2 ^ k * ∏ i ∈ Finset.range k, (n - r - i)) * (n - k).choose r :=
        Nat.mul_le_mul (prod_range_sub_le k n r (by omega)) (le_refl _)
    _ = 2 ^ k * (n - k).choose r * ∏ i ∈ Finset.range k, (n - r - i) := by
        ring

/-! ## The shift identity and the stage-ℓ bound -/

/-- `C(n,r+ℓ)·∏_{s<ℓ}(r+1+s) = C(n,r)·∏_{s<ℓ}(n-r-s)`, hypothesis-free. -/
lemma choose_shift (n r : ℕ) : ∀ ℓ : ℕ,
    n.choose (r + ℓ) * ∏ s ∈ Finset.range ℓ, (r + 1 + s)
      = n.choose r * ∏ s ∈ Finset.range ℓ, (n - r - s) := by
  intro ℓ
  induction ℓ with
  | zero => simp
  | succ ℓ IH =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ,
      show r + (ℓ + 1) = (r + ℓ) + 1 from by omega,
      show r + 1 + ℓ = (r + ℓ) + 1 from by omega]
    calc n.choose ((r + ℓ) + 1)
          * ((∏ s ∈ Finset.range ℓ, (r + 1 + s)) * ((r + ℓ) + 1))
        = (n.choose ((r + ℓ) + 1) * ((r + ℓ) + 1))
            * ∏ s ∈ Finset.range ℓ, (r + 1 + s) := by ring
      _ = (n.choose (r + ℓ) * (n - (r + ℓ)))
            * ∏ s ∈ Finset.range ℓ, (r + 1 + s) := by
          rw [Nat.choose_succ_right_eq]
      _ = (n.choose (r + ℓ) * ∏ s ∈ Finset.range ℓ, (r + 1 + s))
            * (n - (r + ℓ)) := by ring
      _ = (n.choose r * ∏ s ∈ Finset.range ℓ, (n - r - s))
            * (n - (r + ℓ)) := by rw [IH]
      _ = n.choose r
            * ((∏ s ∈ Finset.range ℓ, (n - r - s)) * (n - r - ℓ)) := by
          rw [show n - (r + ℓ) = n - r - ℓ from by omega]
          ring

/-- The stage-`ℓ` cost bound: under `2(r+k) ≤ n`,
`C(n,r+ℓ)(n-r-ℓ)(r+1)^ℓ ≤ 2^k·n^{ℓ+1}·C(n-k,r)`. -/
lemma kd_stageL_count_bound {n k r ℓ : ℕ} (hrn : 2 * (r + k) ≤ n) :
    n.choose (r + ℓ) * (n - r - ℓ) * (r + 1) ^ ℓ
      ≤ 2 ^ k * n ^ (ℓ + 1) * (n - k).choose r := by
  have h1 : (r + 1) ^ ℓ ≤ ∏ s ∈ Finset.range ℓ, (r + 1 + s) := by
    rw [show (r + 1) ^ ℓ = ∏ _s ∈ Finset.range ℓ, (r + 1) from by
      rw [Finset.prod_const, Finset.card_range]]
    exact Finset.prod_le_prod' fun s _ => by omega
  have h2 : (∏ s ∈ Finset.range ℓ, (n - r - s)) ≤ n ^ ℓ := by
    rw [show n ^ ℓ = ∏ _s ∈ Finset.range ℓ, n from by
      rw [Finset.prod_const, Finset.card_range]]
    exact Finset.prod_le_prod' fun s _ => by omega
  calc n.choose (r + ℓ) * (n - r - ℓ) * (r + 1) ^ ℓ
      ≤ n.choose (r + ℓ) * (n - r - ℓ)
          * ∏ s ∈ Finset.range ℓ, (r + 1 + s) :=
        Nat.mul_le_mul (le_refl _) h1
    _ = (n.choose (r + ℓ) * ∏ s ∈ Finset.range ℓ, (r + 1 + s))
          * (n - r - ℓ) := by ring
    _ = (n.choose r * ∏ s ∈ Finset.range ℓ, (n - r - s))
          * (n - r - ℓ) := by rw [choose_shift]
    _ ≤ (n.choose r * n ^ ℓ) * n :=
        Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) h2) (by omega)
    _ ≤ ((2 ^ k * (n - k).choose r) * n ^ ℓ) * n :=
        Nat.mul_le_mul
          (Nat.mul_le_mul (kd_choose_le hrn) (le_refl _)) (le_refl _)
    _ = 2 ^ k * n ^ (ℓ + 1) * (n - k).choose r := by ring

/-! ## The stage-ℓ support count -/

private lemma card_filter_lt {k ℓ : ℕ} (hℓ : ℓ ≤ k) :
    (Finset.univ.filter fun i : Fin k => (i : ℕ) < ℓ).card = ℓ := by
  have himg : Finset.univ.filter (fun i : Fin k => (i : ℕ) < ℓ)
      = Finset.image (Fin.castLE hℓ) Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · intro hi
      exact ⟨⟨(i : ℕ), hi⟩, Fin.ext rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.isLt
  rw [himg, Finset.card_image_of_injective _ (Fin.castLE_injective hℓ),
    Finset.card_univ, Fintype.card_fin]

private lemma kdPrefixIm_card_aux {k ℓ : ℕ} {a : Fin k → ι}
    (hinj : Function.Injective a) (hℓ : ℓ ≤ k) :
    (Finset.image a (Finset.univ.filter
      fun i : Fin k => (i : ℕ) < ℓ)).card = ℓ := by
  rw [Finset.card_image_of_injective _ hinj, card_filter_lt hℓ]

/-- Stage-`ℓ` edges: one per `r`-subset of `univ ∖ range a`. -/
lemma kd_sum_edge_stage {k : ℕ} {a : Fin k → ι}
    (hinj : Function.Injective a) (ℓ : Fin k) (r : ℕ) (c : ℝ) :
    (∑ e : Finset ι × ι,
      if kdPrefix a (ℓ : ℕ) e.1 ∧ e.1.card = r + (ℓ : ℕ) ∧ e.2 = a ℓ
      then c else 0)
    = (((Finset.univ \ Finset.image a Finset.univ
        : Finset ι).card).choose r : ℝ) * c := by
  rw [Fintype.sum_prod_type]
  have hinner : ∀ S : Finset ι,
      (∑ j : ι, if kdPrefix a (ℓ : ℕ) S ∧ S.card = r + (ℓ : ℕ) ∧ j = a ℓ
        then c else 0)
      = if kdPrefix a (ℓ : ℕ) S ∧ S.card = r + (ℓ : ℕ) then c else 0 := by
    intro S
    by_cases hS : kdPrefix a (ℓ : ℕ) S ∧ S.card = r + (ℓ : ℕ)
    · rw [if_pos hS,
        Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) =>
          show (if kdPrefix a (ℓ : ℕ) S ∧ S.card = r + (ℓ : ℕ) ∧ j = a ℓ
              then c else 0)
            = if j = a ℓ then c else 0 from by
          by_cases hj : j = a ℓ
          · rw [if_pos ⟨hS.1, hS.2, hj⟩, if_pos hj]
          · rw [if_neg fun hc => hj hc.2.2, if_neg hj],
        Finset.sum_ite_eq' Finset.univ (a ℓ) fun _ => c,
        if_pos (Finset.mem_univ _)]
    · rw [if_neg hS]
      exact Finset.sum_eq_zero fun j _ =>
        if_neg fun hc => hS ⟨hc.1, hc.2.1⟩
  rw [Finset.sum_congr rfl fun S (_ : S ∈ Finset.univ) => hinner S]
  have hcount : (Finset.univ.filter
        (fun S : Finset ι => kdPrefix a (ℓ : ℕ) S
          ∧ S.card = r + (ℓ : ℕ))).card
      = ((Finset.univ \ Finset.image a Finset.univ
          : Finset ι).card).choose r := by
    rw [← Finset.card_powersetCard r
      (Finset.univ \ Finset.image a Finset.univ : Finset ι)]
    have hPsub : ∀ {S : Finset ι}, kdPrefix a (ℓ : ℕ) S →
        Finset.image a (Finset.univ.filter
          fun i : Fin k => (i : ℕ) < (ℓ : ℕ)) ⊆ S := by
      intro S hpre z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact hpre.1 i (Finset.mem_filter.mp hi).2
    refine Finset.card_bij'
      (fun S _ => S \ Finset.image a (Finset.univ.filter
        fun i : Fin k => (i : ℕ) < (ℓ : ℕ)))
      (fun T _ => T ∪ Finset.image a (Finset.univ.filter
        fun i : Fin k => (i : ℕ) < (ℓ : ℕ))) ?_ ?_ ?_ ?_
    · intro S hS
      obtain ⟨hpre, hcard⟩ := (Finset.mem_filter.mp hS).2
      refine Finset.mem_powersetCard.mpr ⟨fun z hz => ?_, ?_⟩
      · obtain ⟨hzS, hzP⟩ := Finset.mem_sdiff.mp hz
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun himg => ?_⟩
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp himg
        rcases Nat.lt_or_ge (i : ℕ) (ℓ : ℕ) with hlt | hge
        · exact hzP (Finset.mem_image.mpr
            ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, rfl⟩)
        · exact (hpre.2 i hge) hzS
      · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (hPsub hpre),
          kdPrefixIm_card_aux hinj ℓ.isLt.le, hcard]
        omega
    · intro T hT
      obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
      have hTD : ∀ i : Fin k, a i ∉ T := fun i hmem =>
        (Finset.mem_sdiff.mp (hTsub hmem)).2
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      have hdisj : ∀ z ∈ T, z ∉ Finset.image a (Finset.univ.filter
          fun i : Fin k => (i : ℕ) < (ℓ : ℕ)) := by
        intro z hz hmem
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hmem
        exact hTD i hz
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨?_, ?_⟩, ?_⟩
      · intro i hi
        exact Finset.mem_union_right T (Finset.mem_image.mpr
          ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩)
      · intro i hi hmem
        rcases Finset.mem_union.mp hmem with h | h
        · exact hTD i h
        · obtain ⟨i', hi', heq⟩ := Finset.mem_image.mp h
          have hii : i' = i := hinj heq
          have hlt := (Finset.mem_filter.mp hi').2
          omega
      · rw [Finset.card_union_of_disjoint
            (Finset.disjoint_left.mpr hdisj), hTcard,
          kdPrefixIm_card_aux hinj ℓ.isLt.le]
    · intro S hS
      exact Finset.sdiff_union_of_subset
        (hPsub (Finset.mem_filter.mp hS).2.1)
    · intro T hT
      obtain ⟨hTsub, -⟩ := Finset.mem_powersetCard.mp hT
      have hTD : ∀ i : Fin k, a i ∉ T := fun i hmem =>
        (Finset.mem_sdiff.mp (hTsub hmem)).2
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hz | hz, hzP⟩
        · exact hz
        · exact absurd hz hzP
      · intro hz
        refine ⟨Or.inl hz, fun hzP => ?_⟩
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hzP
        exact hTD i hz
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcount]

end QuantumQueryComplexity
