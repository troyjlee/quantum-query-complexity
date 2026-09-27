import QuantumQueryComplexity.Scan.Record
import QuantumQueryComplexity.Scan.Average
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# `ADV±(MAX) = O(√n)`, with no alphabet dependence

Give the coordinate scanned at time `t` the
weights

  `W(t, black) = √(t+1)`,   `W(t, red) = 1/√(t+1)`,

and average the resulting scan duals over all scan orders.  A red branch is a
strict record, which by the record lemma happens for at most a `1/(t+1)`
fraction of orders, so at each time the two contributions balance:

  `√(t+1) · (fraction of records) + 1/√(t+1) ≤ 2/√(t+1)`,

and `∑_{t<n} 1/√(t+1) ≤ 2√n`.  Both squared masses are therefore `O(√n)`.

The bound is independent of the alphabet.  This is what the threshold/staircase
route could not achieve: there the pairing constraints force a γ₂ factorization
of the greater-than matrix, costing `Θ(log m)`.  The scan never compares two
alphabet symbols through an inner product — the comparison happens inside the
branch structure, and the dual only ever tests branch labels for *equality*.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Type*} [Fintype A] [DecidableEq A] [LinearOrder A]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-! ## The elementary sum -/

lemma inv_sqrt_le_two_mul_sub (t : ℕ) :
    (Real.sqrt (t + 1))⁻¹ ≤ 2 * (Real.sqrt (t + 1) - Real.sqrt t) := by
  have ha : Real.sqrt t * Real.sqrt t = (t : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hb : Real.sqrt ((t : ℝ) + 1) * Real.sqrt ((t : ℝ) + 1) = (t : ℝ) + 1 :=
    Real.mul_self_sqrt (by positivity)
  have hbpos : 0 < Real.sqrt ((t : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  rw [inv_le_iff_one_le_mul₀ hbpos]
  nlinarith [sq_nonneg (Real.sqrt ((t : ℝ) + 1) - Real.sqrt t),
    Real.sqrt_nonneg ((t : ℝ) + 1), Real.sqrt_nonneg (t : ℝ)]

/-- `∑_{t < n} 1/√(t+1) ≤ 2√n`, by telescoping. -/
lemma sum_inv_sqrt_le (n : ℕ) :
    (∑ t ∈ Finset.range n, (Real.sqrt (t + 1))⁻¹) ≤ 2 * Real.sqrt n := by
  calc (∑ t ∈ Finset.range n, (Real.sqrt (t + 1))⁻¹)
      ≤ ∑ t ∈ Finset.range n, 2 * (Real.sqrt (t + 1) - Real.sqrt t) :=
        Finset.sum_le_sum fun t _ => inv_sqrt_le_two_mul_sub t
    _ = 2 * Real.sqrt n := by
        have hcast : ∀ i : ℕ, Real.sqrt ((i : ℝ) + 1) = Real.sqrt ((i + 1 : ℕ) : ℝ) := by
          intro i; norm_cast
        simp only [hcast]
        rw [← Finset.mul_sum,
          Finset.sum_range_sub fun t : ℕ => Real.sqrt ((t : ℕ) : ℝ)]
        simp

lemma sum_inv_sqrt_fin_le (n : ℕ) :
    (∑ t : Fin n, (Real.sqrt ((t : ℕ) + 1))⁻¹) ≤ 2 * Real.sqrt n := by
  rw [Fin.sum_univ_eq_sum_range fun t : ℕ => (Real.sqrt ((t : ℝ) + 1))⁻¹]
  exact_mod_cast sum_inv_sqrt_le n

/-! ## The weights -/

/-- Depth-dependent weights: black is `√(t+1)`, red is `1/√(t+1)`. -/
noncomputable def scanWeight (e : Order ι) (i : ι) (c : Bool) : ℝ :=
  if c then (Real.sqrt ((e i : ℕ) + 1))⁻¹ else Real.sqrt ((e i : ℕ) + 1)

lemma scanWeight_pos (e : Order ι) (i : ι) (c : Bool) : 0 < scanWeight e i c := by
  have h : (0 : ℝ) < Real.sqrt ((e i : ℕ) + 1) :=
    Real.sqrt_pos.mpr (by positivity)
  cases c <;> simp only [scanWeight, if_true, if_false] <;> positivity

/-- The `u`-side weight at a coordinate: `√(t+1)` on a record, `1/√(t+1)`
otherwise. -/
lemma scanWeight_inv (e : Order ι) (x : ι → A) (i : ι) :
    (scanWeight e i (isRecord (⇑e) x i))⁻¹
      = if isRecord (⇑e) x i then Real.sqrt ((e i : ℕ) + 1)
        else (Real.sqrt ((e i : ℕ) + 1))⁻¹ := by
  have h : (0 : ℝ) < Real.sqrt ((e i : ℕ) + 1) := Real.sqrt_pos.mpr (by positivity)
  cases hc : isRecord (⇑e) x i <;>
    simp only [scanWeight, hc, if_true, if_false] <;>
    simp [inv_inv]

/-- The `v`-side weight at a coordinate. -/
lemma scanWeight_v (e : Order ι) (x : ι → A) (i : ι) :
    scanWeight e i true + (if isRecord (⇑e) x i then scanWeight e i false else 0)
      = (Real.sqrt ((e i : ℕ) + 1))⁻¹
        + if isRecord (⇑e) x i then Real.sqrt ((e i : ℕ) + 1) else 0 := by
  cases hc : isRecord (⇑e) x i <;> simp [scanWeight, hc]

/-! ## Summing over the scan order -/

/-- Reindexing a sum over coordinates as a sum over times. -/
lemma sum_over_times (e : Order ι) (F : Fin (Fintype.card ι) → ℝ) :
    (∑ i : ι, F (e i)) = ∑ t : Fin (Fintype.card ι), F t :=
  Fintype.sum_equiv e _ _ fun _ => rfl

/-- **The key per-time estimate.**  Summed over all scan orders, the `u`-side
cost at time `t` is at most `2 / √(t+1)` times the number of orders. -/
lemma sum_orders_u_le (x : ι → A) (t : Fin (Fintype.card ι)) :
    (∑ e : Order ι, if isRecord (⇑e) x (e.symm t) then Real.sqrt ((t : ℕ) + 1)
        else (Real.sqrt ((t : ℕ) + 1))⁻¹)
      ≤ (Fintype.card (Order ι) : ℝ) * (2 * (Real.sqrt ((t : ℕ) + 1))⁻¹) := by
  classical
  have hsq : Real.sqrt ((t : ℕ) + 1) * Real.sqrt ((t : ℕ) + 1) = ((t : ℕ) : ℝ) + 1 :=
    Real.mul_self_sqrt (by positivity)
  have hpos : (0 : ℝ) < Real.sqrt ((t : ℕ) + 1) := Real.sqrt_pos.mpr (by positivity)
  set R := (Finset.univ.filter fun e : Order ι =>
    isRecord (⇑e) x (e.symm t) = true).card with hRdef
  set R' := (Finset.univ.filter fun e : Order ι =>
    ¬ (isRecord (⇑e) x (e.symm t) = true)).card with hR'def
  have hsplit : (∑ e : Order ι, if isRecord (⇑e) x (e.symm t) then
        Real.sqrt ((t : ℕ) + 1) else (Real.sqrt ((t : ℕ) + 1))⁻¹)
      = (R : ℝ) * Real.sqrt ((t : ℕ) + 1)
        + (R' : ℝ) * (Real.sqrt ((t : ℕ) + 1))⁻¹ := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
      nsmul_eq_mul, hRdef, hR'def]
  -- the record count is small, so the first piece is no bigger than the second
  have hcount : (((t : ℕ) : ℝ) + 1) * (R : ℝ) ≤ (Fintype.card (Order ι) : ℝ) := by
    exact_mod_cast card_record_mul_le x t
  have hkey : (R : ℝ) * Real.sqrt ((t : ℕ) + 1)
      ≤ (Fintype.card (Order ι) : ℝ) * (Real.sqrt ((t : ℕ) + 1))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hpos, mul_assoc, hsq]
    calc (R : ℝ) * (((t : ℕ) : ℝ) + 1) = (((t : ℕ) : ℝ) + 1) * (R : ℝ) := by ring
      _ ≤ (Fintype.card (Order ι) : ℝ) := hcount
  have hR' : (R' : ℝ) ≤ (Fintype.card (Order ι) : ℝ) := by
    rw [hR'def]
    exact_mod_cast Finset.card_le_univ _
  rw [hsplit]
  have h2 : (R' : ℝ) * (Real.sqrt ((t : ℕ) + 1))⁻¹
      ≤ (Fintype.card (Order ι) : ℝ) * (Real.sqrt ((t : ℕ) + 1))⁻¹ :=
    mul_le_mul_of_nonneg_right hR' (by positivity)
  linarith [hkey, h2]

/-- The `v`-side analogue: at most `3 / √(t+1)` per order. -/
lemma sum_orders_v_le (x : ι → A) (t : Fin (Fintype.card ι)) :
    (∑ e : Order ι, ((Real.sqrt ((t : ℕ) + 1))⁻¹
        + if isRecord (⇑e) x (e.symm t) then Real.sqrt ((t : ℕ) + 1) else 0))
      ≤ (Fintype.card (Order ι) : ℝ) * (3 * (Real.sqrt ((t : ℕ) + 1))⁻¹) := by
  classical
  have hpos : (0 : ℝ) < Real.sqrt ((t : ℕ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hle : ∀ e : Order ι,
      ((Real.sqrt ((t : ℕ) + 1))⁻¹
        + if isRecord (⇑e) x (e.symm t) then Real.sqrt ((t : ℕ) + 1) else 0)
      ≤ ((if isRecord (⇑e) x (e.symm t) then Real.sqrt ((t : ℕ) + 1)
            else (Real.sqrt ((t : ℕ) + 1))⁻¹) + (Real.sqrt ((t : ℕ) + 1))⁻¹) := by
    intro e
    have hnn : (0 : ℝ) ≤ (Real.sqrt ((t : ℕ) + 1))⁻¹ := by positivity
    split_ifs <;> linarith
  calc (∑ e : Order ι, ((Real.sqrt ((t : ℕ) + 1))⁻¹
        + if isRecord (⇑e) x (e.symm t) then Real.sqrt ((t : ℕ) + 1) else 0))
      ≤ ∑ e : Order ι, ((if isRecord (⇑e) x (e.symm t) then Real.sqrt ((t : ℕ) + 1)
          else (Real.sqrt ((t : ℕ) + 1))⁻¹) + (Real.sqrt ((t : ℕ) + 1))⁻¹) :=
        Finset.sum_le_sum fun e _ => hle e
    _ = (∑ e : Order ι, if isRecord (⇑e) x (e.symm t) then Real.sqrt ((t : ℕ) + 1)
          else (Real.sqrt ((t : ℕ) + 1))⁻¹)
        + (Fintype.card (Order ι) : ℝ) * (Real.sqrt ((t : ℕ) + 1))⁻¹ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Fintype.card (Order ι) : ℝ) * (2 * (Real.sqrt ((t : ℕ) + 1))⁻¹)
        + (Fintype.card (Order ι) : ℝ) * (Real.sqrt ((t : ℕ) + 1))⁻¹ := by
        gcongr
        exact sum_orders_u_le x t
    _ = (Fintype.card (Order ι) : ℝ) * (3 * (Real.sqrt ((t : ℕ) + 1))⁻¹) := by ring

/-! ## The theorem -/

set_option maxHeartbeats 1000000 in
-- the dimension type and the order Fintype make unification costly
/-- **`ADV±(MAX) ≤ 24 √n`, with no dependence on the alphabet**, for the maximum
of a *value map* applied to the letters.

Averaging the depth-weighted scan duals over all scan orders.  A red branch is a
strict record, which happens for at most a `1/(t+1)` fraction of orders, so the
two colour contributions balance at every time and the total is governed by
`∑_t 1/√(t+1) ≤ 2√n`.

Nothing about the bound sees `m`: neither its injectivity nor the size of the
alphabet `σ` of letters plays any role. -/
theorem exists_maxMap_dual_isCostLe (m : σ → A) :
    ∃ P : DualPair (Order ι × ScanDim ι A (WithBot A))
      (fun x : ι → σ => maxFun fun j => m (x j)),
      P.IsCostLe (24 * Real.sqrt (Fintype.card ι)) := by
  classical
  haveI : Nonempty (Order ι) := ⟨Fintype.equivFin ι⟩
  set N : ℝ := (Fintype.card (Order ι) : ℝ) with hNdef
  have hNpos : (0 : ℝ) < N := by rw [hNdef, Nat.cast_pos]; exact Fintype.card_pos
  set P : Order ι → DualPair (ScanDim ι A (WithBot A))
      (fun x : ι → σ => maxFun fun j => m (x j)) :=
    fun e => (maxScanMap m (⇑e) e.injective).dual (scanWeight e) (scanWeight_pos e)
    with hPdef
  refine ⟨DualPair.averageUnif P, ?_⟩
  refine DualPair.averageUnif_isCostLe P (fun x => ?_) (fun y => ?_)
  · -- the `u` side
    have hmass : ∀ e : Order ι,
        (∑ i : ι, ∑ k : ScanDim ι A (WithBot A), (P e).u x i k * (P e).u x i k)
          = 4 * ∑ t : Fin (Fintype.card ι),
            (if isRecord (⇑e) (fun j => m (x j)) (e.symm t) then
                Real.sqrt ((t : ℕ) + 1)
              else (Real.sqrt ((t : ℕ) + 1))⁻¹) := by
      intro e
      rw [hPdef, Scan.sum_dual_u_sq]
      congr 1
      rw [← sum_over_times e fun t =>
        if isRecord (⇑e) (fun j => m (x j)) (e.symm t) then
        Real.sqrt ((t : ℕ) + 1) else (Real.sqrt ((t : ℕ) + 1))⁻¹]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Equiv.symm_apply_apply]
      exact scanWeight_inv e (fun j => m (x j)) i
    have hstep : (∑ e : Order ι, ∑ i : ι, ∑ k : ScanDim ι A (WithBot A),
        (P e).u x i k * (P e).u x i k) ≤ N * (24 * Real.sqrt (Fintype.card ι)) := by
      calc (∑ e : Order ι, ∑ i : ι, ∑ k : ScanDim ι A (WithBot A),
            (P e).u x i k * (P e).u x i k)
          = ∑ e : Order ι, 4 * ∑ t : Fin (Fintype.card ι),
              (if isRecord (⇑e) (fun j => m (x j)) (e.symm t) then
                  Real.sqrt ((t : ℕ) + 1)
                else (Real.sqrt ((t : ℕ) + 1))⁻¹) :=
            Finset.sum_congr rfl fun e _ => hmass e
        _ = 4 * ∑ t : Fin (Fintype.card ι), ∑ e : Order ι,
              (if isRecord (⇑e) (fun j => m (x j)) (e.symm t) then
                  Real.sqrt ((t : ℕ) + 1)
                else (Real.sqrt ((t : ℕ) + 1))⁻¹) := by
            rw [← Finset.mul_sum, Finset.sum_comm]
        _ ≤ 4 * ∑ t : Fin (Fintype.card ι), N * (2 * (Real.sqrt ((t : ℕ) + 1))⁻¹) := by
            gcongr with t
            exact sum_orders_u_le (fun j => m (x j)) t
        _ = 4 * (N * 2 * ∑ t : Fin (Fintype.card ι), (Real.sqrt ((t : ℕ) + 1))⁻¹) := by
            congr 1
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun t _ => by ring
        _ ≤ 4 * (N * 2 * (2 * Real.sqrt (Fintype.card ι))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (sum_inv_sqrt_fin_le (Fintype.card ι)) (by positivity)) (by norm_num)
        _ ≤ N * (24 * Real.sqrt (Fintype.card ι)) := by
            have : (0:ℝ) ≤ N * Real.sqrt (Fintype.card ι) := by positivity
            nlinarith [this]
    calc N⁻¹ * (∑ e : Order ι, ∑ i : ι, ∑ k : ScanDim ι A (WithBot A),
          (P e).u x i k * (P e).u x i k)
        ≤ N⁻¹ * (N * (24 * Real.sqrt (Fintype.card ι))) := by
          exact mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 24 * Real.sqrt (Fintype.card ι) := by field_simp
  · -- the `v` side
    have hmass : ∀ e : Order ι,
        (∑ i : ι, ∑ k : ScanDim ι A (WithBot A), (P e).v y i k * (P e).v y i k)
          = 4 * ∑ t : Fin (Fintype.card ι),
            ((Real.sqrt ((t : ℕ) + 1))⁻¹
              + if isRecord (⇑e) (fun j => m (y j)) (e.symm t) then
                  Real.sqrt ((t : ℕ) + 1) else 0) := by
      intro e
      rw [hPdef, Scan.sum_dual_v_sq]
      congr 1
      rw [← sum_over_times e fun t => (Real.sqrt ((t : ℕ) + 1))⁻¹
        + if isRecord (⇑e) (fun j => m (y j)) (e.symm t) then
            Real.sqrt ((t : ℕ) + 1) else 0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Equiv.symm_apply_apply]
      exact scanWeight_v e (fun j => m (y j)) i
    have hstep : (∑ e : Order ι, ∑ i : ι, ∑ k : ScanDim ι A (WithBot A),
        (P e).v y i k * (P e).v y i k) ≤ N * (24 * Real.sqrt (Fintype.card ι)) := by
      calc (∑ e : Order ι, ∑ i : ι, ∑ k : ScanDim ι A (WithBot A),
            (P e).v y i k * (P e).v y i k)
          = ∑ e : Order ι, 4 * ∑ t : Fin (Fintype.card ι),
              ((Real.sqrt ((t : ℕ) + 1))⁻¹
                + if isRecord (⇑e) (fun j => m (y j)) (e.symm t) then
                    Real.sqrt ((t : ℕ) + 1) else 0) :=
            Finset.sum_congr rfl fun e _ => hmass e
        _ = 4 * ∑ t : Fin (Fintype.card ι), ∑ e : Order ι,
              ((Real.sqrt ((t : ℕ) + 1))⁻¹
                + if isRecord (⇑e) (fun j => m (y j)) (e.symm t) then
                    Real.sqrt ((t : ℕ) + 1) else 0) := by
            rw [← Finset.mul_sum, Finset.sum_comm]
        _ ≤ 4 * ∑ t : Fin (Fintype.card ι), N * (3 * (Real.sqrt ((t : ℕ) + 1))⁻¹) := by
            gcongr with t
            exact sum_orders_v_le (fun j => m (y j)) t
        _ = 4 * (N * 3 * ∑ t : Fin (Fintype.card ι), (Real.sqrt ((t : ℕ) + 1))⁻¹) := by
            congr 1
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun t _ => by ring
        _ ≤ 4 * (N * 3 * (2 * Real.sqrt (Fintype.card ι))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (sum_inv_sqrt_fin_le (Fintype.card ι)) (by positivity)) (by norm_num)
        _ = N * (24 * Real.sqrt (Fintype.card ι)) := by ring
    calc N⁻¹ * (∑ e : Order ι, ∑ i : ι, ∑ k : ScanDim ι A (WithBot A),
          (P e).v y i k * (P e).v y i k)
        ≤ N⁻¹ * (N * (24 * Real.sqrt (Fintype.card ι))) := by
          exact mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 24 * Real.sqrt (Fintype.card ι) := by field_simp

/-- The maximum of the input itself: the value map is the identity. -/
theorem exists_maxFun_dual_isCostLe :
    ∃ P : DualPair (Order ι × ScanDim ι A (WithBot A)) (maxFun : (ι → A) → A),
      P.IsCostLe (24 * Real.sqrt (Fintype.card ι)) :=
  exists_maxMap_dual_isCostLe (ι := ι) (A := A) (σ := A) id

/-- **`ADV±(MAX) ≤ 24 √n`**, with no dependence on the alphabet. -/
theorem advPM_maxFun_le_sqrt :
    advPM (maxFun : (ι → A) → A) ≤ 24 * Real.sqrt (Fintype.card ι) := by
  obtain ⟨P, hP⟩ := exists_maxFun_dual_isCostLe (ι := ι) (A := A)
  exact advPM_le_of_dualPair P (by positivity) hP

end QuantumQueryComplexity
