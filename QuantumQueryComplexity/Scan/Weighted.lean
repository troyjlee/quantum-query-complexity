import QuantumQueryComplexity.Scan.Final
import QuantumQueryComplexity.Scan.Uniform
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# A weighted maximum dual: `ADV±_c(MAX) ≤ 16 √(∑ᵢ cᵢ²)`

`QuantumQueryComplexity/Scan/Final.lean` gives maximum finding an alphabet-free dual of cost
`24 √n`.  Composition, however, consumes the **weighted** cost: if the `i`-th
subproblem under an outer maximum costs `cᵢ`, then
`DualPair.composeShared_isCostLe` charges `∑ᵢ cᵢ ‖u_{x,i}‖²`, and the composition
is only worth running when that is `√(∑ᵢ cᵢ²)` rather than `∑ᵢ cᵢ`.

Scale the scan weights by the coordinate cost.  If coordinate `i` is scanned at
time `t`, put

  `q_t = C √(t+1) / √n`,   `W(i, black) = q_t / cᵢ`,   `W(i, red) = cᵢ / q_t`,

where `C = √(∑ᵢ cᵢ²)`.  At `c ≡ 1` this is exactly `Scan/Final.lean`'s
`√(t+1)`, `1/√(t+1)`.  The scan dual is feasible for *any* positive
input-independent weights, so nothing about the constraint changes; only the
masses do, and both are bounded by

  `cᵢ²/q_t + [record at i] · q_t`.                                    (∗)

That expression is what makes the argument work, and it is worth saying why the
obvious attempt fails.  A weight depending on the coordinate alone cannot help:
for a *fixed* coordinate the record probability is not small — every coordinate
holds the maximum for some input, and then it is a record whenever it is scanned
first.  In (∗) the two terms are decoupled instead: the record term is
independent of `i`, so `card_record_mul_le` (records are rare per *time slot*)
bounds it, while the coordinate-dependent term carries no record event, so
`sum_orders_coord` (the coordinate at a fixed time is uniform) averages it.  Each
averages to `C / (√n √(t+1))`, and `∑_t 1/√(t+1) ≤ 2√n` finishes.

Setting `cᵢ = 1` also improves the unweighted bound from `24 √n` to `16 √n`: the
present proof bounds the `v` side coarsely by `3/√(t+1)` per time, whereas
estimating the two contributions of (∗) separately gives `2/√(t+1)` on both
sides.
-/

namespace QuantumQueryComplexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Type*} [Fintype A] [DecidableEq A] [LinearOrder A]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-! ## The cost scale -/

/-- `C = √(∑ᵢ cᵢ²)`, the value the weighted dual will cost up to a constant. -/
noncomputable def costNorm (c : ι → ℝ) : ℝ := Real.sqrt (∑ i, c i * c i)

/-- The scale at scan time `t`.  At `c ≡ 1` this is `√(t+1)`. -/
noncomputable def costScale (c : ι → ℝ) (t : ℕ) : ℝ :=
  costNorm c * Real.sqrt ((t : ℝ) + 1) / Real.sqrt (Fintype.card ι)

/-- The average that each of the two terms of (∗) reaches at time `t`. -/
noncomputable def costBase (c : ι → ℝ) (t : ℕ) : ℝ :=
  costNorm c / (Real.sqrt (Fintype.card ι) * Real.sqrt ((t : ℝ) + 1))

variable (c : ι → ℝ)

lemma sqrt_card_pos : (0 : ℝ) < Real.sqrt (Fintype.card ι) :=
  Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)

lemma sqrt_card_sq : Real.sqrt (Fintype.card ι) * Real.sqrt (Fintype.card ι)
    = (Fintype.card ι : ℝ) :=
  Real.mul_self_sqrt (Nat.cast_nonneg _)

lemma costNorm_pos (hc : ∀ i, 0 < c i) : 0 < costNorm c := by
  rw [costNorm, Real.sqrt_pos]
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  exact Finset.sum_pos' (fun i _ => mul_self_nonneg _)
    ⟨i₀, Finset.mem_univ _, mul_pos (hc i₀) (hc i₀)⟩

lemma costNorm_sq (hc : ∀ i, 0 < c i) : costNorm c * costNorm c = ∑ i, c i * c i :=
  Real.mul_self_sqrt (Finset.sum_nonneg fun i _ => mul_self_nonneg _)

lemma costScale_pos (hc : ∀ i, 0 < c i) (t : ℕ) : 0 < costScale c t :=
  div_pos (mul_pos (costNorm_pos c hc) (Real.sqrt_pos.mpr (by positivity)))
    sqrt_card_pos

lemma costBase_nonneg (hc : ∀ i, 0 < c i) (t : ℕ) : 0 ≤ costBase c t :=
  div_nonneg (le_of_lt (costNorm_pos c hc)) (by positivity)

/-! ## The weights -/

/-- The scan weights, scaled by the coordinate cost: black is `q/cᵢ`, red is
`cᵢ/q`, with `q` the scale at the time `i` is scanned. -/
noncomputable def wScanWeight (c : ι → ℝ) (e : Order ι) (i : ι) (col : Bool) : ℝ :=
  if col then c i / costScale c ((e i : ℕ)) else costScale c ((e i : ℕ)) / c i

lemma wScanWeight_true (e : Order ι) (i : ι) :
    wScanWeight c e i true = c i / costScale c ((e i : ℕ)) := by simp [wScanWeight]

lemma wScanWeight_false (e : Order ι) (i : ι) :
    wScanWeight c e i false = costScale c ((e i : ℕ)) / c i := by simp [wScanWeight]

lemma wScanWeight_pos (hc : ∀ i, 0 < c i) (e : Order ι) (i : ι) (col : Bool) :
    0 < wScanWeight c e i col := by
  have h1 := hc i
  have h2 := costScale_pos c hc ((e i : ℕ))
  cases col
  · rw [wScanWeight_false]
    exact div_pos h2 h1
  · rw [wScanWeight_true]
    exact div_pos h1 h2

/-- The bound (∗) on both weighted masses at one coordinate. -/
noncomputable def costTerm (c : ι → ℝ) (i : ι) (t : ℕ) (rec : Bool) : ℝ :=
  c i * c i / costScale c t + if rec then costScale c t else 0

lemma costTerm_false (i : ι) (t : ℕ) :
    costTerm c i t false = c i * c i / costScale c t := by simp [costTerm]

lemma costTerm_true (i : ι) (t : ℕ) :
    costTerm c i t true = c i * c i / costScale c t + costScale c t := by
  simp [costTerm]

/-- The `u`-side weighted mass at a coordinate is bounded by (∗). -/
lemma weighted_u_le (hc : ∀ i, 0 < c i) (e : Order ι) (col : Bool) (i : ι) :
    c i * (wScanWeight c e i col)⁻¹ ≤ costTerm c i ((e i : ℕ)) col := by
  have hci : (0 : ℝ) < c i := hc i
  have hq : (0 : ℝ) < costScale c ((e i : ℕ)) := costScale_pos c hc ((e i : ℕ))
  have hci' : c i ≠ 0 := ne_of_gt hci
  have hq' : costScale c ((e i : ℕ)) ≠ 0 := ne_of_gt hq
  have hpos : (0 : ℝ) ≤ c i * c i / costScale c ((e i : ℕ)) :=
    div_nonneg (mul_self_nonneg _) hq.le
  cases col
  · rw [wScanWeight_false, costTerm_false, inv_div]
    apply le_of_eq
    field_simp
  · rw [wScanWeight_true, costTerm_true, inv_div]
    have hstep : c i * (costScale c ((e i : ℕ)) / c i)
        = costScale c ((e i : ℕ)) := by field_simp
    rw [hstep]
    linarith

/-- The `v`-side weighted mass at a coordinate is exactly (∗). -/
lemma weighted_v_eq (hc : ∀ i, 0 < c i) (e : Order ι) (col : Bool) (i : ι) :
    c i * (wScanWeight c e i true + if col then wScanWeight c e i false else 0)
      = costTerm c i ((e i : ℕ)) col := by
  have hci' : c i ≠ 0 := ne_of_gt (hc i)
  have hq' : costScale c ((e i : ℕ)) ≠ 0 :=
    ne_of_gt (costScale_pos c hc ((e i : ℕ)))
  cases col
  · have h0 : (if (false : Bool) then wScanWeight c e i false else (0 : ℝ)) = 0 := by
      simp
    rw [h0, add_zero, wScanWeight_true, costTerm_false]
    field_simp
  · have h1 : (if (true : Bool) then wScanWeight c e i false else (0 : ℝ))
        = wScanWeight c e i false := by simp
    rw [h1, wScanWeight_true, wScanWeight_false, costTerm_true]
    field_simp

/-- `q_t = (t+1) · costBase t`: the record term, once the record lemma has paid
the factor `1/(t+1)`, lands on the same average as the coordinate term. -/
lemma costScale_eq (t : ℕ) : costScale c t = ((t : ℝ) + 1) * costBase c t := by
  have ht : (0 : ℝ) < Real.sqrt ((t : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have htt : Real.sqrt ((t : ℝ) + 1) * Real.sqrt ((t : ℝ) + 1) = (t : ℝ) + 1 :=
    Real.mul_self_sqrt (by positivity)
  have hn := sqrt_card_pos (ι := ι)
  have hn' : Real.sqrt (Fintype.card ι) ≠ 0 := ne_of_gt hn
  have ht' : Real.sqrt ((t : ℝ) + 1) ≠ 0 := ne_of_gt ht
  rw [costScale, costBase]
  field_simp
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (t : ℝ) + 1)]

/-! ## Averaging over scan orders -/

/-- **The coordinate term averages to `costBase`.**  This is where uniformity of
the coordinate at a fixed time is used; no record event is involved. -/
lemma sum_orders_coordTerm (hc : ∀ i, 0 < c i) (t : Fin (Fintype.card ι)) :
    (∑ e : Order ι, c (e.symm t) * c (e.symm t) / costScale c ((t : ℕ)))
      = (Fintype.card (Order ι) : ℝ) * costBase c ((t : ℕ)) := by
  have hn := sqrt_card_pos (ι := ι)
  have hnn := sqrt_card_sq (ι := ι)
  have hC := costNorm_pos c hc
  have hCC := costNorm_sq c hc
  have ht : (0 : ℝ) < Real.sqrt (((t : ℕ) : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hn' : Real.sqrt (Fintype.card ι) ≠ 0 := ne_of_gt hn
  have ht' : Real.sqrt (((t : ℕ) : ℝ) + 1) ≠ 0 := ne_of_gt ht
  have hC' : costNorm c ≠ 0 := ne_of_gt hC
  have hnc : (Fintype.card ι : ℝ) ≠ 0 := by
    have h : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
    exact ne_of_gt h
  have huni := sum_orders_coord t (fun i => c i * c i)
  have hsum : (∑ e : Order ι, c (e.symm t) * c (e.symm t))
      = (Fintype.card (Order ι) : ℝ) * (costNorm c * costNorm c)
        / (Real.sqrt (Fintype.card ι) * Real.sqrt (Fintype.card ι)) := by
    rw [hnn, hCC, eq_div_iff hnc]
    linarith [huni]
  rw [← Finset.sum_div, hsum, costScale, costBase]
  field_simp

/-- **The record term averages to at most `costBase`.**  This is where the record
lemma is used; the term does not depend on the coordinate. -/
lemma sum_orders_recTerm_le (hc : ∀ i, 0 < c i) (m : σ → A) (x : ι → σ)
    (t : Fin (Fintype.card ι)) :
    (∑ e : Order ι, if isRecord (⇑e) (fun j => m (x j)) (e.symm t) then
        costScale c ((t : ℕ)) else 0)
      ≤ (Fintype.card (Order ι) : ℝ) * costBase c ((t : ℕ)) := by
  classical
  have hn := sqrt_card_pos (ι := ι)
  have ht : (0 : ℝ) < Real.sqrt (((t : ℕ) : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hn' : Real.sqrt (Fintype.card ι) ≠ 0 := ne_of_gt hn
  have ht' : Real.sqrt (((t : ℕ) : ℝ) + 1) ≠ 0 := ne_of_gt ht
  have htt : Real.sqrt (((t : ℕ) : ℝ) + 1) * Real.sqrt (((t : ℕ) : ℝ) + 1)
      = ((t : ℕ) : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
  set R := (Finset.univ.filter fun e : Order ι =>
    isRecord (⇑e) (fun j => m (x j)) (e.symm t) = true).card with hRdef
  have hsplit : (∑ e : Order ι, if isRecord (⇑e) (fun j => m (x j)) (e.symm t) then
      costScale c ((t : ℕ)) else 0) = (R : ℝ) * costScale c ((t : ℕ)) := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, nsmul_eq_mul,
      add_zero, hRdef]
  have hcount : (((t : ℕ) : ℝ) + 1) * (R : ℝ) ≤ (Fintype.card (Order ι) : ℝ) := by
    exact_mod_cast card_record_mul_le (fun j => m (x j)) t
  have hL : (R : ℝ) * costScale c ((t : ℕ))
      = ((R : ℝ) * (((t : ℕ) : ℝ) + 1)) * costBase c ((t : ℕ)) := by
    rw [costScale_eq]
    ring
  rw [hsplit, hL]
  refine mul_le_mul_of_nonneg_right ?_ (costBase_nonneg c hc _)
  linarith [hcount]

/-- `∑_t C/(√n √(t+1)) ≤ 2 C`. -/
lemma sum_costBase_le (hc : ∀ i, 0 < c i) :
    (∑ t : Fin (Fintype.card ι), costBase c ((t : ℕ))) ≤ 2 * costNorm c := by
  have hn := sqrt_card_pos (ι := ι)
  have hn' : Real.sqrt (Fintype.card ι) ≠ 0 := ne_of_gt hn
  have hCnn : 0 ≤ costNorm c := le_of_lt (costNorm_pos c hc)
  have hstep : (∑ t : Fin (Fintype.card ι), costBase c ((t : ℕ)))
      = costNorm c / Real.sqrt (Fintype.card ι)
        * ∑ t : Fin (Fintype.card ι), (Real.sqrt (((t : ℕ) : ℝ) + 1))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [costBase]
    have ht' : Real.sqrt (((t : ℕ) : ℝ) + 1) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    field_simp
  rw [hstep]
  have hsum := sum_inv_sqrt_fin_le (Fintype.card ι)
  refine le_trans (mul_le_mul_of_nonneg_left hsum (by positivity)) (le_of_eq ?_)
  field_simp

/-! ## The weighted maximum theorem -/

set_option maxHeartbeats 1000000 in
/-- **`ADV±_c(MAX) ≤ 16 √(∑ᵢ cᵢ²)`, with no dependence on the alphabet.**

The `c`-weighted cost of a dual solution is what shared-input composition
charges, so this is the theorem that turns "the `i`-th subproblem costs `cᵢ`"
into "their maximum costs `16 √(∑ cᵢ²)`". -/
theorem exists_maxMap_dual_isWeightedCostLe (m : σ → A) (c : ι → ℝ)
    (hc : ∀ i, 0 < c i) :
    ∃ P : DualPair (Order ι × ScanDim ι A (WithBot A))
      (fun x : ι → σ => maxFun fun j => m (x j)),
      P.IsWeightedCostLe c (16 * costNorm c) := by
  classical
  haveI : Nonempty (Order ι) := ⟨Fintype.equivFin ι⟩
  set N : ℝ := (Fintype.card (Order ι) : ℝ) with hNdef
  have hNpos : (0 : ℝ) < N := by rw [hNdef, Nat.cast_pos]; exact Fintype.card_pos
  have hN' : N ≠ 0 := ne_of_gt hNpos
  set P : Order ι → DualPair (ScanDim ι A (WithBot A))
      (fun x : ι → σ => maxFun fun j => m (x j)) :=
    fun e => (maxScanMap m (⇑e) e.injective).dual (wScanWeight c e)
      (wScanWeight_pos c hc e) with hPdef
  -- the total, over all orders, of the bound (∗)
  have hmaster : ∀ x : ι → σ,
      (∑ e : Order ι, ∑ i : ι,
          costTerm c i ((e i : ℕ)) (isRecord (⇑e) (fun j => m (x j)) i))
        ≤ N * (4 * costNorm c) := by
    intro x
    have hswap : ∀ e : Order ι,
        (∑ i : ι, costTerm c i ((e i : ℕ)) (isRecord (⇑e) (fun j => m (x j)) i))
          = ∑ t : Fin (Fintype.card ι), costTerm c (e.symm t) ((t : ℕ))
              (isRecord (⇑e) (fun j => m (x j)) (e.symm t)) := by
      intro e
      refine Fintype.sum_equiv e _ _ fun i => ?_
      rw [Equiv.symm_apply_apply]
    rw [Finset.sum_congr rfl fun e (_ : e ∈ Finset.univ) => hswap e, Finset.sum_comm]
    have hper : ∀ t : Fin (Fintype.card ι),
        (∑ e : Order ι, costTerm c (e.symm t) ((t : ℕ))
            (isRecord (⇑e) (fun j => m (x j)) (e.symm t)))
          ≤ N * (2 * costBase c ((t : ℕ))) := by
      intro t
      simp only [costTerm]
      rw [Finset.sum_add_distrib, sum_orders_coordTerm c hc t]
      have := sum_orders_recTerm_le c hc m x t
      rw [hNdef]
      linarith
    calc (∑ t : Fin (Fintype.card ι), ∑ e : Order ι,
          costTerm c (e.symm t) ((t : ℕ))
            (isRecord (⇑e) (fun j => m (x j)) (e.symm t)))
        ≤ ∑ t : Fin (Fintype.card ι), N * (2 * costBase c ((t : ℕ))) :=
          Finset.sum_le_sum fun t _ => hper t
      _ = N * 2 * ∑ t : Fin (Fintype.card ι), costBase c ((t : ℕ)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by ring
      _ ≤ N * 2 * (2 * costNorm c) :=
          mul_le_mul_of_nonneg_left (sum_costBase_le c hc) (by positivity)
      _ = N * (4 * costNorm c) := by ring
  refine ⟨DualPair.averageUnif P, ?_⟩
  refine DualPair.averageUnif_isWeightedCostLe P (fun x => ?_) (fun y => ?_)
  · -- the `u` side
    have hmass : ∀ e : Order ι,
        (∑ i : ι, c i * ∑ k : ScanDim ι A (WithBot A), (P e).u x i k * (P e).u x i k)
          ≤ 4 * ∑ i : ι,
              costTerm c i ((e i : ℕ)) (isRecord (⇑e) (fun j => m (x j)) i) := by
      intro e
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [hPdef, Scan.sum_dual_u_sq_coord]
      rw [show c i * (4 * (wScanWeight c e i
            ((maxScanMap m (⇑e) e.injective).col x i))⁻¹)
          = 4 * (c i * (wScanWeight c e i
            ((maxScanMap m (⇑e) e.injective).col x i))⁻¹) from by ring]
      exact mul_le_mul_of_nonneg_left
        (weighted_u_le c hc e _ i) (by norm_num)
    calc N⁻¹ * ∑ e : Order ι,
          (∑ i : ι, c i * ∑ k : ScanDim ι A (WithBot A), (P e).u x i k * (P e).u x i k)
        ≤ N⁻¹ * ∑ e : Order ι, 4 * ∑ i : ι,
            costTerm c i ((e i : ℕ)) (isRecord (⇑e) (fun j => m (x j)) i) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e _ => hmass e) ?_
          positivity
      _ = N⁻¹ * (4 * ∑ e : Order ι, ∑ i : ι,
            costTerm c i ((e i : ℕ)) (isRecord (⇑e) (fun j => m (x j)) i)) := by
          rw [← Finset.mul_sum]
      _ ≤ N⁻¹ * (4 * (N * (4 * costNorm c))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (hmaster x) (by norm_num)
      _ = 16 * costNorm c := by
          rw [show N⁻¹ * (4 * (N * (4 * costNorm c)))
              = (N⁻¹ * N) * (16 * costNorm c) from by ring,
            inv_mul_cancel₀ hN', one_mul]
  · -- the `v` side
    have hmass : ∀ e : Order ι,
        (∑ i : ι, c i * ∑ k : ScanDim ι A (WithBot A), (P e).v y i k * (P e).v y i k)
          = 4 * ∑ i : ι,
              costTerm c i ((e i : ℕ)) (isRecord (⇑e) (fun j => m (y j)) i) := by
      intro e
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hPdef, Scan.sum_dual_v_sq_coord]
      rw [show c i * (4 * (wScanWeight c e i true
            + if (maxScanMap m (⇑e) e.injective).col y i then
                wScanWeight c e i false else 0))
          = 4 * (c i * (wScanWeight c e i true
            + if (maxScanMap m (⇑e) e.injective).col y i then
                wScanWeight c e i false else 0)) from by ring]
      rw [weighted_v_eq c hc e _ i]
      rfl
    calc N⁻¹ * ∑ e : Order ι,
          (∑ i : ι, c i * ∑ k : ScanDim ι A (WithBot A), (P e).v y i k * (P e).v y i k)
        = N⁻¹ * ∑ e : Order ι, 4 * ∑ i : ι,
            costTerm c i ((e i : ℕ)) (isRecord (⇑e) (fun j => m (y j)) i) := by
          rw [Finset.sum_congr rfl fun e (_ : e ∈ Finset.univ) => hmass e]
      _ = N⁻¹ * (4 * ∑ e : Order ι, ∑ i : ι,
            costTerm c i ((e i : ℕ)) (isRecord (⇑e) (fun j => m (y j)) i)) := by
          rw [← Finset.mul_sum]
      _ ≤ N⁻¹ * (4 * (N * (4 * costNorm c))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (hmaster y) (by norm_num)
      _ = 16 * costNorm c := by
          rw [show N⁻¹ * (4 * (N * (4 * costNorm c)))
              = (N⁻¹ * N) * (16 * costNorm c) from by ring,
            inv_mul_cancel₀ hN', one_mul]

/-- **Unit costs sharpen the unweighted bound from `24 √n` to `16 √n`.**

`QuantumQueryComplexity/Scan/Final.lean` bounds the `v` side coarsely by `3/√(t+1)` at each
time; splitting (∗) into its two contributions gives `2/√(t+1)` on both sides. -/
theorem exists_maxMap_dual_isCostLe_sixteen (m : σ → A) :
    ∃ P : DualPair (Order ι × ScanDim ι A (WithBot A))
      (fun x : ι → σ => maxFun fun j => m (x j)),
      P.IsCostLe (16 * Real.sqrt (Fintype.card ι)) := by
  obtain ⟨P, hP⟩ := exists_maxMap_dual_isWeightedCostLe (ι := ι) (A := A) (σ := σ)
    m (fun _ => 1) (fun _ => one_pos)
  have hnorm : costNorm (fun _ : ι => (1 : ℝ)) = Real.sqrt (Fintype.card ι) := by
    rw [costNorm]
    congr 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hnorm] at hP
  exact ⟨P, fun x => by simpa using hP.1 x, fun y => by simpa using hP.2 y⟩

/-- The maximum of the input itself, weighted. -/
theorem exists_maxFun_dual_isWeightedCostLe (c : ι → ℝ) (hc : ∀ i, 0 < c i) :
    ∃ P : DualPair (Order ι × ScanDim ι A (WithBot A)) (maxFun : (ι → A) → A),
      P.IsWeightedCostLe c (16 * costNorm c) :=
  exists_maxMap_dual_isWeightedCostLe (ι := ι) (A := A) (σ := A) id c hc

end QuantumQueryComplexity
