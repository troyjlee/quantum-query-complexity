import QuantumQueryComplexity.ED.Flow
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Counting edges and binomial ratios

Two kinds of bookkeeping feed the cost computation:

* pure `ℕ` binomial facts, all consequences of
  `(n-t)·C(n,t) = n·C(n-1,t)` applied twice —
  `C(n,t)·(n-t)(n-t-1) = n(n-1)·C(n-2,t)` — which bound the three
  level ratios under `2r + 2 ≤ n`;
* edge counts: the graph has `C(n,t)·(n-t)` loading edges at level `t`, and
  the flow of a fixed input uses `C(m,t)·(m-t)` of them in stage I,
  `C(m,r)` in each of stages II and III (`m = n - 2`).
-/

namespace QuantumQueryComplexity

/-! ## Binomial identities and inequalities -/

lemma sub_mul_choose (n t : ℕ) :
    (n - t) * n.choose t = n * ((n - 1).choose t) := by
  cases n with
  | zero => simp
  | succ k =>
    simp only [Nat.add_sub_cancel]
    have h := Nat.choose_mul_succ_eq k t
    rw [mul_comm, ← h]
    ring

/-- The double-step ratio identity: `C(n,t)·(n-t)(n-t-1) = n(n-1)·C(n-2,t)`,
with no hypotheses (both sides vanish in every degenerate case). -/
lemma choose_ratio_identity (n t : ℕ) :
    n.choose t * ((n - t) * (n - t - 1)) = n * (n - 1) * ((n - 2).choose t) := by
  have h1 := sub_mul_choose n t
  have h2 : (n - 1 - t) * ((n - 1).choose t) = (n - 1) * ((n - 2).choose t) := by
    have h := sub_mul_choose (n - 1) t
    rwa [show n - 1 - 1 = n - 2 from by omega] at h
  have hsub : n - t - 1 = n - 1 - t := by omega
  calc n.choose t * ((n - t) * (n - t - 1))
      = (n - t - 1) * ((n - t) * n.choose t) := by ring
    _ = (n - t - 1) * (n * ((n - 1).choose t)) := by rw [h1]
    _ = n * ((n - 1 - t) * ((n - 1).choose t)) := by rw [hsub]; ring
    _ = n * ((n - 1) * ((n - 2).choose t)) := by rw [h2]
    _ = n * (n - 1) * ((n - 2).choose t) := by ring

/-- Stage-I level ratio: below level `r` the ambient edge count is at most
four times the flow's edge count. -/
lemma stageI_count_bound {n r t : ℕ} (ht : t < r) (hrn : 2 * r + 2 ≤ n) :
    n.choose t * (n - t) ≤ 4 * ((n - 2).choose t * (n - 2 - t)) := by
  have hpos : 0 < n - t - 1 := by omega
  have hu : n + 2 ≤ 2 * (n - t - 1) := by omega
  have hv : n ≤ 2 * (n - 2 - t) := by omega
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc n.choose t * (n - t) * (n - t - 1)
      = n.choose t * ((n - t) * (n - t - 1)) := by ring
    _ = n * (n - 1) * ((n - 2).choose t) := choose_ratio_identity n t
    _ ≤ (n + 2) * n * ((n - 2).choose t) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) le_rfl
    _ ≤ (2 * (n - t - 1)) * (2 * (n - 2 - t)) * ((n - 2).choose t) :=
        Nat.mul_le_mul (Nat.mul_le_mul hu hv) le_rfl
    _ = 4 * ((n - 2).choose t * (n - 2 - t)) * (n - t - 1) := by ring

/-- Stage-II ratio: `C(n,r)·(n-r) ≤ 2n·C(n-2,r)`. -/
lemma stageII_count_bound {n r : ℕ} (hrn : 2 * r + 2 ≤ n) :
    n.choose r * (n - r) ≤ 2 * n * ((n - 2).choose r) := by
  have hpos : 0 < n - r - 1 := by omega
  have hu : n - 1 ≤ 2 * (n - r - 1) := by omega
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc n.choose r * (n - r) * (n - r - 1)
      = n.choose r * ((n - r) * (n - r - 1)) := by ring
    _ = n * (n - 1) * ((n - 2).choose r) := choose_ratio_identity n r
    _ ≤ n * (2 * (n - r - 1)) * ((n - 2).choose r) :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl hu) le_rfl
    _ = 2 * n * ((n - 2).choose r) * (n - r - 1) := by ring

/-- Stage-III ratio: `C(n,r+1)·(n-r-1)·(r+1) ≤ n²·C(n-2,r)`, exact up to
`n-1 ≤ n`, with no hypotheses. -/
lemma stageIII_count_bound (n r : ℕ) :
    n.choose (r + 1) * (n - (r + 1)) * (r + 1)
      ≤ n * n * ((n - 2).choose r) := by
  have h1 : n.choose (r + 1) * (r + 1) = n.choose r * (n - r) :=
    Nat.choose_succ_right_eq n r
  calc n.choose (r + 1) * (n - (r + 1)) * (r + 1)
      = n.choose (r + 1) * (r + 1) * (n - (r + 1)) := by ring
    _ = n.choose r * (n - r) * (n - (r + 1)) := by rw [h1]
    _ = n.choose r * ((n - r) * (n - r - 1)) := by
        rw [show n - (r + 1) = n - r - 1 from by omega]; ring
    _ = n * (n - 1) * ((n - 2).choose r) := choose_ratio_identity n r
    _ ≤ n * n * ((n - 2).choose r) :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl (Nat.sub_le n 1)) le_rfl

/-! ## Edge counts -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A sum over all loading edges of a quantity depending only on the level:
level `t` holds `C(n,t)·(n-t)` edges. -/
lemma sum_edge_levelWeight (φ : ℕ → ℝ) :
    (∑ e : Finset ι × ι, if e.2 ∈ e.1 then (0 : ℝ) else φ e.1.card)
    = ∑ t ∈ Finset.range (Fintype.card ι + 1),
        ((Fintype.card ι).choose t : ℝ)
          * (((Fintype.card ι - t : ℕ)) : ℝ) * φ t := by
  rw [Fintype.sum_prod_type]
  have hinner : ∀ S : Finset ι,
      (∑ j : ι, if j ∈ S then (0 : ℝ) else φ S.card)
      = (((Fintype.card ι - S.card : ℕ)) : ℝ) * φ S.card := by
    intro S
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) =>
      show (if j ∈ S then (0 : ℝ) else φ S.card)
        = if j ∈ Sᶜ then φ S.card else 0 from by
        by_cases hj : j ∈ S
        · rw [if_pos hj, if_neg (by simp [hj])]
        · rw [if_neg hj, if_pos (Finset.mem_compl.mpr hj)],
      Finset.sum_ite_mem Finset.univ Sᶜ fun _ => φ S.card,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, Finset.card_compl]
  rw [Finset.sum_congr rfl fun S (_ : S ∈ Finset.univ) => hinner S,
    ← Finset.powerset_univ, Finset.sum_powerset, Finset.card_univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_powersetCard t Finset.univ
      (fun u => (((Fintype.card ι - u : ℕ)) : ℝ) * φ u),
    Finset.card_univ, nsmul_eq_mul, ← mul_assoc]

/-- The same sum restricted to a ground set `D`: level `t` holds
`C(|D|,t)·(|D|-t)` edges inside `D`. -/
lemma sum_edge_levelWeight_sub (D : Finset ι) (φ : ℕ → ℝ) :
    (∑ e : Finset ι × ι,
      if e.1 ⊆ D ∧ e.2 ∈ D ∧ e.2 ∉ e.1 then φ e.1.card else 0)
    = ∑ t ∈ Finset.range (D.card + 1),
        (D.card.choose t : ℝ) * (((D.card - t : ℕ)) : ℝ) * φ t := by
  rw [Fintype.sum_prod_type]
  have hinner : ∀ S : Finset ι,
      (∑ j : ι, if S ⊆ D ∧ j ∈ D ∧ j ∉ S then φ S.card else 0)
      = if S ⊆ D then (((D.card - S.card : ℕ)) : ℝ) * φ S.card else 0 := by
    intro S
    by_cases hS : S ⊆ D
    · rw [if_pos hS,
        Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) =>
          show (if S ⊆ D ∧ j ∈ D ∧ j ∉ S then φ S.card else 0)
            = if j ∈ D \ S then φ S.card else 0 from by
          by_cases hj : j ∈ D \ S
          · rw [if_pos ⟨hS, (Finset.mem_sdiff.mp hj).1,
              (Finset.mem_sdiff.mp hj).2⟩, if_pos hj]
          · rw [if_neg fun hc =>
              hj (Finset.mem_sdiff.mpr ⟨hc.2.1, hc.2.2⟩), if_neg hj],
        Finset.sum_ite_mem Finset.univ (D \ S) fun _ => φ S.card,
        Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
        Finset.card_sdiff, Finset.inter_eq_left.mpr hS]
    · rw [if_neg hS]
      exact Finset.sum_eq_zero fun j _ => if_neg fun hc => hS hc.1
  rw [Finset.sum_congr rfl fun S (_ : S ∈ Finset.univ) => hinner S,
    show (∑ S : Finset ι, if S ⊆ D
        then (((D.card - S.card : ℕ)) : ℝ) * φ S.card else 0)
      = ∑ S ∈ D.powerset, (((D.card - S.card : ℕ)) : ℝ) * φ S.card from
      (Finset.sum_congr rfl fun S _ =>
        if_congr Finset.mem_powerset.symm rfl rfl).trans
        (by rw [Finset.sum_ite_mem, Finset.univ_inter]),
    Finset.sum_powerset]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_powersetCard t D
      (fun u => (((D.card - u : ℕ)) : ℝ) * φ u), nsmul_eq_mul, ← mul_assoc]

/-- Stage-II edges: one per `r`-subset of `D`. -/
lemma sum_edge_stageII (D : Finset ι) (a : ι) (r : ℕ) (c : ℝ) :
    (∑ e : Finset ι × ι,
      if e.1 ⊆ D ∧ e.1.card = r ∧ e.2 = a then c else 0)
    = (D.card.choose r : ℝ) * c := by
  rw [Fintype.sum_prod_type]
  have hinner : ∀ S : Finset ι,
      (∑ j : ι, if S ⊆ D ∧ S.card = r ∧ j = a then c else 0)
      = if S ⊆ D ∧ S.card = r then c else 0 := by
    intro S
    by_cases hS : S ⊆ D ∧ S.card = r
    · rw [if_pos hS,
        Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) =>
          show (if S ⊆ D ∧ S.card = r ∧ j = a then c else 0)
            = if j = a then c else 0 from by
          by_cases hj : j = a
          · rw [if_pos ⟨hS.1, hS.2, hj⟩, if_pos hj]
          · rw [if_neg fun hc => hj hc.2.2, if_neg hj],
        Finset.sum_ite_eq' Finset.univ a fun _ => c,
        if_pos (Finset.mem_univ _)]
    · rw [if_neg hS]
      exact Finset.sum_eq_zero fun j _ => if_neg fun hc => hS ⟨hc.1, hc.2.1⟩
  rw [Finset.sum_congr rfl fun S (_ : S ∈ Finset.univ) => hinner S,
    show (∑ S : Finset ι, if S ⊆ D ∧ S.card = r then c else 0)
      = ∑ S ∈ Finset.powersetCard r D, c from
      (Finset.sum_congr rfl fun S _ =>
        if_congr Finset.mem_powersetCard.symm rfl rfl).trans
        (by rw [Finset.sum_ite_mem, Finset.univ_inter]),
    Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

/-- Stage-III edges: one per set `insert a T` with `T` an `r`-subset of
`univ \ {a, b}`. -/
lemma sum_edge_stageIII {a b : ι} (hab : a ≠ b) (r : ℕ) (c : ℝ) :
    (∑ e : Finset ι × ι,
      if a ∈ e.1 ∧ b ∉ e.1 ∧ e.1.card = r + 1 ∧ e.2 = b then c else 0)
    = (((Finset.univ \ {a, b} : Finset ι).card).choose r : ℝ) * c := by
  rw [Fintype.sum_prod_type]
  have hinner : ∀ S : Finset ι,
      (∑ j : ι, if a ∈ S ∧ b ∉ S ∧ S.card = r + 1 ∧ j = b then c else 0)
      = if a ∈ S ∧ b ∉ S ∧ S.card = r + 1 then c else 0 := by
    intro S
    by_cases hS : a ∈ S ∧ b ∉ S ∧ S.card = r + 1
    · rw [if_pos hS,
        Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) =>
          show (if a ∈ S ∧ b ∉ S ∧ S.card = r + 1 ∧ j = b then c else 0)
            = if j = b then c else 0 from by
          by_cases hj : j = b
          · rw [if_pos ⟨hS.1, hS.2.1, hS.2.2, hj⟩, if_pos hj]
          · rw [if_neg fun hc => hj hc.2.2.2, if_neg hj],
        Finset.sum_ite_eq' Finset.univ b fun _ => c,
        if_pos (Finset.mem_univ _)]
    · rw [if_neg hS]
      exact Finset.sum_eq_zero fun j _ =>
        if_neg fun hc => hS ⟨hc.1, hc.2.1, hc.2.2.1⟩
  rw [Finset.sum_congr rfl fun S (_ : S ∈ Finset.univ) => hinner S]
  have hcount : (Finset.univ.filter
        (fun S : Finset ι => a ∈ S ∧ b ∉ S ∧ S.card = r + 1)).card
      = ((Finset.univ \ {a, b} : Finset ι).card).choose r := by
    rw [← Finset.card_powersetCard r (Finset.univ \ {a, b} : Finset ι)]
    refine Finset.card_bij' (fun S _ => S.erase a) (fun T _ => insert a T)
      ?_ ?_ ?_ ?_
    · intro S hS
      obtain ⟨ha, hb, hcard⟩ := (Finset.mem_filter.mp hS).2
      refine Finset.mem_powersetCard.mpr ⟨fun z hz => ?_, ?_⟩
      · obtain ⟨hza, hzS⟩ := Finset.mem_erase.mp hz
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hzab => ?_⟩
        rcases Finset.mem_insert.mp hzab with h | h
        · exact hza h
        · rw [Finset.mem_singleton.mp h] at hzS
          exact hb hzS
      · rw [Finset.card_erase_of_mem ha, hcard]
        omega
    · intro T hT
      obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
      have haT : a ∉ T := fun h =>
        (Finset.mem_sdiff.mp (hTsub h)).2 (Finset.mem_insert_self a {b})
      have hbT : b ∉ T := fun h =>
        (Finset.mem_sdiff.mp (hTsub h)).2
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Finset.mem_insert_self a T, ?_, ?_⟩
      · intro hbin
        rcases Finset.mem_insert.mp hbin with h | h
        · exact hab h.symm
        · exact hbT h
      · rw [Finset.card_insert_of_notMem haT, hTcard]
    · intro S hS
      exact Finset.insert_erase (Finset.mem_filter.mp hS).2.1
    · intro T hT
      have haT : a ∉ T := fun h =>
        (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hT).1 h)).2
          (Finset.mem_insert_self a {b})
      exact Finset.erase_insert haT
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcount]

end QuantumQueryComplexity
