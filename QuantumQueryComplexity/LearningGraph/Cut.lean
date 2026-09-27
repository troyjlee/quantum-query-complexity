import QuantumQueryComplexity.LearningGraph.Defs
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The cut identity

Fix a positive input `x` and a negative input `y`, and let `A` be the family
of sets on which they agree.  `A` is closed under subsets, contains `∅`, and
contains no sink of `x` (`sinkCert`).  Telescoping conservation over `A`
shows that the flow crossing from `A` to its complement is exactly the unit
that leaves the source:

  `∑_{(S,j) : x,y agree on S, x j ≠ y j}  p x (S,j)  =  1`.

Edges internal to `A` cancel against the inflow reindexing
`(S, j) ↦ (S \ {j}, j)`; edges with `j ∈ S` never cross, because agreement on
`S` forces `x j = y j`.  This is the only place conservation is used, and no
nonnegativity of the flow is needed.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [DecidableEq σ]
variable {f : (ι → σ) → Bool}

/-- **The cut identity**: the flow of a positive input across the boundary of
agreement with a negative input is `1`. -/
theorem LGFlow.sum_cut (L : LGFlow f) {x y : ι → σ}
    (hx : f x = true) (hy : f y = false) :
    (∑ e : Finset ι × ι, if x e.2 = y e.2 then (0 : ℝ)
      else if setMask x e.1 = setMask y e.1 then L.p x e else 0) = 1 := by
  classical
  -- the agreement family and the disagreement coordinates
  have hmemA : ∀ {S : Finset ι},
      S ∈ Finset.univ.filter (fun S : Finset ι => ∀ i ∈ S, x i = y i)
        ↔ ∀ i ∈ S, x i = y i := by
    intro S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  -- Step 1: the cut sum is the disagreeing outflow of the agreement family.
  have hstep1 : (∑ e : Finset ι × ι, if x e.2 = y e.2 then (0 : ℝ)
      else if setMask x e.1 = setMask y e.1 then L.p x e else 0)
      = ∑ S ∈ Finset.univ.filter (fun S : Finset ι => ∀ i ∈ S, x i = y i),
          ∑ j ∈ Finset.univ.filter (fun j => ¬ x j = y j), L.p x (S, j) := by
    have hvanish : ∀ S ∈ (Finset.univ : Finset (Finset ι)),
        S ∉ Finset.univ.filter (fun S : Finset ι => ∀ i ∈ S, x i = y i) →
        (∑ j : ι, if x j = y j then (0 : ℝ)
          else if setMask x S = setMask y S then L.p x (S, j) else 0) = 0 := by
      intro S _ hS
      refine Finset.sum_eq_zero fun j _ => ?_
      have hmask : ¬ setMask x S = setMask y S := fun hc =>
        hS (hmemA.mpr (setMask_eq_iff.mp hc))
      by_cases hj : x j = y j
      · rw [if_pos hj]
      · rw [if_neg hj, if_neg hmask]
    rw [Fintype.sum_prod_type,
      ← Finset.sum_subset (Finset.subset_univ _) hvanish]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hmask : setMask x S = setMask y S := setMask_eq_iff.mpr (hmemA.mp hS)
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) =>
      show (if x j = y j then (0 : ℝ)
          else if setMask x S = setMask y S then L.p x (S, j) else 0)
        = if ¬ x j = y j then L.p x (S, j) else 0 from by
        by_cases hj : x j = y j
        · rw [if_pos hj, if_neg (not_not_intro hj)]
        · rw [if_neg hj, if_pos hmask, if_pos hj],
      ← Finset.sum_filter]
  -- Step 2: telescoping conservation over the agreement family.
  have hAempty : (∅ : Finset ι)
      ∈ Finset.univ.filter (fun S : Finset ι => ∀ i ∈ S, x i = y i) :=
    hmemA.mpr fun i hi => absurd hi (Finset.notMem_empty i)
  have hnosink : ∀ S ∈ Finset.univ.filter (fun S : Finset ι => ∀ i ∈ S, x i = y i),
      ¬ L.sink x S := by
    intro S hS hsink
    obtain ⟨i, hiS, hne⟩ := L.sinkCert x y hx hy S hsink
    exact hne (hmemA.mp hS i hiS)
  have htele : (∑ S ∈ Finset.univ.filter (fun S : Finset ι => ∀ i ∈ S, x i = y i),
      ((∑ j ∈ Sᶜ, L.p x (S, j)) - ∑ j ∈ S, L.p x (S.erase j, j))) = 1 := by
    rw [← Finset.sum_erase_add _ _ hAempty]
    have hzero : ∀ S ∈ (Finset.univ.filter
        (fun S : Finset ι => ∀ i ∈ S, x i = y i)).erase ∅,
        ((∑ j ∈ Sᶜ, L.p x (S, j)) - ∑ j ∈ S, L.p x (S.erase j, j)) = 0 := by
      intro S hS
      rw [L.conserve x hx S (Finset.mem_erase.mp hS).1
        (hnosink S (Finset.mem_erase.mp hS).2), sub_self]
    rw [Finset.sum_eq_zero hzero, zero_add, Finset.compl_empty,
      Finset.sum_empty, sub_zero]
    exact L.source x hx
  -- Step 3: the inflow reindexing `(S, j) ↦ (S \ {j}, j)`.
  have hbij : (∑ S ∈ Finset.univ.filter (fun S : Finset ι => ∀ i ∈ S, x i = y i),
      ∑ j ∈ S, L.p x (S.erase j, j))
      = ∑ S ∈ Finset.univ.filter (fun S : Finset ι => ∀ i ∈ S, x i = y i),
          ∑ j ∈ Sᶜ.filter (fun j => x j = y j), L.p x (S, j) := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_nbij' (fun q => ⟨q.1.erase q.2, q.2⟩)
      (fun q => ⟨insert q.2 q.1, q.2⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨S, j⟩ hq
      rw [Finset.mem_sigma] at hq ⊢
      obtain ⟨hS, hjS⟩ := hq
      have hSA := hmemA.mp hS
      refine ⟨hmemA.mpr fun i hi => hSA i (Finset.mem_of_mem_erase hi), ?_⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_compl.mpr (Finset.notMem_erase j S), hSA j hjS⟩
    · rintro ⟨T, j⟩ hq
      rw [Finset.mem_sigma] at hq ⊢
      obtain ⟨hT, hjT⟩ := hq
      have hTA := hmemA.mp hT
      obtain ⟨hjc, hjxy⟩ := Finset.mem_filter.mp hjT
      refine ⟨hmemA.mpr fun i hi => ?_, Finset.mem_insert_self _ _⟩
      rcases Finset.mem_insert.mp hi with h | h
      · rw [h]; exact hjxy
      · exact hTA i h
    · rintro ⟨S, j⟩ hq
      rw [Finset.mem_sigma] at hq
      rw [Finset.insert_erase hq.2]
    · rintro ⟨T, j⟩ hq
      rw [Finset.mem_sigma] at hq
      have hjc := Finset.mem_compl.mp (Finset.mem_filter.mp hq.2).1
      rw [Finset.erase_insert hjc]
    · rintro ⟨S, j⟩ _
      rfl
  -- Assemble: disagreeing outflow = total outflow − agreeing outflow
  --         = total outflow − inflow, which telescopes to the source.
  rw [hstep1]
  have hagree : ∀ S ∈ Finset.univ.filter (fun S : Finset ι => ∀ i ∈ S, x i = y i),
      (∑ j ∈ Finset.univ.filter (fun j => ¬ x j = y j), L.p x (S, j))
      = (∑ j ∈ Sᶜ, L.p x (S, j))
        - ∑ j ∈ Sᶜ.filter (fun j => x j = y j), L.p x (S, j) := by
    intro S hS
    have hDeq : Sᶜ.filter (fun j => ¬ x j = y j)
        = Finset.univ.filter (fun j => ¬ x j = y j) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_compl, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨fun hjS => h (hmemA.mp hS j hjS), h⟩⟩
    rw [← hDeq, eq_sub_iff_add_eq, add_comm]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  rw [Finset.sum_congr rfl hagree, Finset.sum_sub_distrib, ← hbij,
    ← Finset.sum_sub_distrib]
  exact htele

end QuantumQueryComplexity
