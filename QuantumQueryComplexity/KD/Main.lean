import QuantumQueryComplexity.KD.Cost
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The k-distinctness upper bound

Assembling the flow (`QuantumQueryComplexity/KD/Flow.lean`), the half-weights and the
two complexities (`QuantumQueryComplexity/KD/Cost.lean`) through the learning-graph
theorem gives, for `2(r+k) ≤ n`,

  `ADV±(kdFun k) ≤ 2^{k+1}·r + ∑_{ℓ<k} √(2^k·n^{ℓ+1}/(r+1)^ℓ)`,

and choosing `r = ⌊n^{k/(k+1)}⌋` (with the read-everything dual `2n`
covering `n ≤ 4^{k+1}`),

  `ADV±(kdFun k) ≤ (k+1)·2^{k+1}·n^{k/(k+1)}`,

matching Ambainis' quantum walk up to the constant, uniformly in the
alphabet.  `k = 2` recovers element distinctness (with a larger constant
than the dedicated `advPM_edFun_le`).
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- **The parametric certificate**: for `2(r+k) ≤ n`, the flow's dual is
bundled at `2^{k+1}·r + ∑_{ℓ<k} √(2^k·n^{ℓ+1}/(r+1)^ℓ)`. -/
theorem hasDual_kdFun_param (k r : ℕ) (hk : 1 ≤ k)
    (hrn : 2 * (r + k) ≤ Fintype.card ι) :
    HasDual (kdFun (ι := ι) (σ := σ) k)
      (2 ^ (k + 1) * r
        + ∑ ℓ ∈ Finset.range k,
            Real.sqrt (((2 ^ k * Fintype.card ι ^ (ℓ + 1) : ℕ) : ℝ)
              / (((r + 1) ^ ℓ : ℕ) : ℝ))) := by
  have hn0 : 0 < Fintype.card ι := by omega
  have hterm0 : (0 : ℝ) < Real.sqrt
      (((2 ^ k * Fintype.card ι ^ (0 + 1) : ℕ) : ℝ)
        / (((r + 1) ^ 0 : ℕ) : ℝ)) := by
    refine Real.sqrt_pos.mpr (div_pos ?_ ?_)
    · exact_mod_cast Nat.mul_pos (pow_pos (by norm_num : 0 < 2) k)
        (pow_pos hn0 (0 + 1))
    · exact_mod_cast pow_pos (show 0 < r + 1 by omega) 0
  have hBpos : (0 : ℝ) < 2 ^ (k + 1) * r
      + ∑ ℓ ∈ Finset.range k,
          Real.sqrt (((2 ^ k * Fintype.card ι ^ (ℓ + 1) : ℕ) : ℝ)
            / (((r + 1) ^ ℓ : ℕ) : ℝ)) := by
    have hsum_pos : (0 : ℝ) < ∑ ℓ ∈ Finset.range k,
        Real.sqrt (((2 ^ k * Fintype.card ι ^ (ℓ + 1) : ℕ) : ℝ)
          / (((r + 1) ^ ℓ : ℕ) : ℝ)) :=
      Finset.sum_pos' (fun ℓ _ => Real.sqrt_nonneg _)
        ⟨0, Finset.mem_range.mpr (by omega), hterm0⟩
    have h1 : (0 : ℝ) ≤ 2 ^ (k + 1) * r := by positivity
    linarith
  have hr : r ≤ Fintype.card ι - k := by omega
  have hhas := LGFlow.hasDual (kdLGFlow (σ := σ) k r hk hr
      (kdOmega (Fintype.card ι) k r)
      (fun e hj hc => kdOmega_ne_zero hk hrn hj hc)) hBpos hBpos
    (by
      show (∑ e : Finset ι × ι, kdOmega (Fintype.card ι) k r e ^ 2) ≤ _
      exact sum_kdOmega_sq_le hk hrn)
    (by
      intro x hx
      have hex := kdFun_eq_true_iff.mp hx
      show (∑ e : Finset ι × ι,
        ((if h : ∃ a : Fin k → ι, Function.Injective a ∧
            ∀ i j : Fin k, x (a i) = x (a j)
          then kdFlow k r h.choose e.1 e.2 else 0)
          / kdOmega (Fintype.card ι) k r e) ^ 2) ≤ _
      simp only [dif_pos hex]
      refine (sum_kdFlow_div_sq_le hex.choose_spec.1 hk hrn).trans ?_
      have h2p : (1 : ℝ) ≤ 2 ^ (k + 1) := by
        calc (1 : ℝ) = 1 ^ (k + 1) := (one_pow _).symm
          _ ≤ 2 ^ (k + 1) :=
            pow_le_pow_left₀ (by norm_num) (by norm_num) (k + 1)
      have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      nlinarith)
  rw [Real.sqrt_mul_self hBpos.le] at hhas
  exact hhas

/-- **The parametric bound**: for `2(r+k) ≤ n`,
`ADV±(kdFun k) ≤ 2^{k+1}·r + ∑_{ℓ<k} √(2^k·n^{ℓ+1}/(r+1)^ℓ)` — weak
duality on the bundled certificate. -/
theorem advPM_kdFun_le_param (k r : ℕ) (hk : 1 ≤ k)
    (hrn : 2 * (r + k) ≤ Fintype.card ι) :
    advPM (kdFun (ι := ι) (σ := σ) k)
      ≤ 2 ^ (k + 1) * r
        + ∑ ℓ ∈ Finset.range k,
            Real.sqrt (((2 ^ k * Fintype.card ι ^ (ℓ + 1) : ℕ) : ℝ)
              / (((r + 1) ^ ℓ : ℕ) : ℝ)) :=
  advPM_le_of_hasDual
    (add_nonneg (by positivity)
      (Finset.sum_nonneg fun ℓ _ => Real.sqrt_nonneg _))
    (hasDual_kdFun_param k r hk hrn)

/-! ## The headline arithmetic -/

private lemma kd_rpow_four (k : ℕ) :
    ((4 : ℝ) ^ (k + 1 : ℕ)) ^ ((1 : ℝ) / ((k : ℝ) + 1)) = 4 := by
  have hkR : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [← Real.rpow_natCast (4 : ℝ) (k + 1),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4),
    show ((k + 1 : ℕ) : ℝ) * ((1 : ℝ) / ((k : ℝ) + 1)) = 1 from by
      rw [mul_one_div]
      push_cast
      exact div_self hkR.ne']
  exact Real.rpow_one 4

private lemma kd_rpow_split (k : ℕ) {y : ℝ} (hy : 0 < y) :
    y ^ ((1 : ℝ) / ((k : ℝ) + 1)) * y ^ ((k : ℝ) / ((k : ℝ) + 1)) = y := by
  have hkR : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [← Real.rpow_add hy, ← add_div,
    show (1 : ℝ) + (k : ℝ) = (k : ℝ) + 1 from by ring, div_self hkR.ne',
    Real.rpow_one]

/-- The per-stage headline bound: with `r = ⌊n^{k/(k+1)}⌋` every stage
term is at most `2^k · n^{k/(k+1)}`. -/
private lemma kd_term_le {n k r ℓ : ℕ} (hℓ : ℓ < k)
    (hn1 : (1 : ℝ) ≤ (n : ℝ))
    (hrx : ((n : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1)) < (r : ℝ) + 1) :
    Real.sqrt (((2 ^ k * n ^ (ℓ + 1) : ℕ) : ℝ)
        / (((r + 1) ^ ℓ : ℕ) : ℝ))
      ≤ 2 ^ k * ((n : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hkR : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hx1 : (1 : ℝ) ≤ ((n : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1)) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1)) :=
        (Real.one_rpow _).symm
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) hn1 (by positivity)
  have hxpos : (0 : ℝ) < ((n : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1)) := by
    linarith
  have hfrac : ((2 ^ k * n ^ (ℓ + 1) : ℕ) : ℝ)
      / (((r + 1) ^ ℓ : ℕ) : ℝ)
      ≤ 2 ^ k * (((n : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))) ^ 2 := by
    have hcast : ((2 ^ k * n ^ (ℓ + 1) : ℕ) : ℝ)
        = 2 ^ k * ((n : ℝ)) ^ (ℓ + 1 : ℕ) := by
      push_cast
      ring
    have hcast2 : (((r + 1) ^ ℓ : ℕ) : ℝ) = ((r : ℝ) + 1) ^ ℓ := by
      push_cast
      ring
    rw [hcast, hcast2]
    have hxℓ : (((n : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))) ^ ℓ
        ≤ ((r : ℝ) + 1) ^ ℓ :=
      pow_le_pow_left₀ (by positivity) hrx.le ℓ
    have hxℓpos : (0 : ℝ)
        < (((n : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))) ^ ℓ := pow_pos hxpos ℓ
    have hkey : ((n : ℝ)) ^ (ℓ + 1 : ℕ)
        / (((n : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))) ^ ℓ
        ≤ (((n : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))) ^ 2 := by
      have hL : ((n : ℝ)) ^ (ℓ + 1 : ℕ)
          / (((n : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))) ^ ℓ
          = ((n : ℝ)) ^ (((ℓ : ℝ) + 1)
              - (k : ℝ) / ((k : ℝ) + 1) * ℓ) := by
        rw [← Real.rpow_natCast ((n : ℝ)) (ℓ + 1),
          ← Real.rpow_natCast
            (((n : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))) ℓ,
          ← Real.rpow_mul hnpos.le, ← Real.rpow_sub hnpos]
        congr 1
        push_cast
        ring
      have hR : (((n : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))) ^ 2
          = ((n : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1) * 2) := by
        rw [← Real.rpow_natCast
          (((n : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))) 2,
          ← Real.rpow_mul hnpos.le]
        norm_num
      rw [hL, hR]
      refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
      have hle : ((ℓ : ℝ) + 1) ≤ (k : ℝ) * ((ℓ : ℝ) + 2) / ((k : ℝ) + 1) := by
        rw [le_div_iff₀ hkR]
        have hℓk : (ℓ : ℝ) + 1 ≤ (k : ℝ) := by
          have h := hℓ
          exact_mod_cast h
        nlinarith
      have heq : (k : ℝ) / ((k : ℝ) + 1) * 2
          + (k : ℝ) / ((k : ℝ) + 1) * ℓ
          = (k : ℝ) * ((ℓ : ℝ) + 2) / ((k : ℝ) + 1) := by
        field_simp
        ring
      linarith
    calc 2 ^ k * ((n : ℝ)) ^ (ℓ + 1 : ℕ) / (((r : ℝ) + 1) ^ ℓ)
        ≤ 2 ^ k * ((n : ℝ)) ^ (ℓ + 1 : ℕ)
            / ((((n : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))) ^ ℓ) :=
          div_le_div_of_nonneg_left (by positivity) hxℓpos hxℓ
      _ = 2 ^ k * (((n : ℝ)) ^ (ℓ + 1 : ℕ)
            / ((((n : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))) ^ ℓ)) := by
          ring
      _ ≤ 2 ^ k * (((n : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))) ^ 2 :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
  have h2k1 : (1 : ℝ) ≤ 2 ^ k := by
    calc (1 : ℝ) = 1 ^ k := (one_pow k).symm
      _ ≤ 2 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  calc Real.sqrt (((2 ^ k * n ^ (ℓ + 1) : ℕ) : ℝ)
      / (((r + 1) ^ ℓ : ℕ) : ℝ))
      ≤ Real.sqrt (2 ^ k
          * (((n : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))) ^ 2) :=
        Real.sqrt_le_sqrt hfrac
    _ = Real.sqrt (2 ^ k) * ((n : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hxpos.le]
    _ ≤ 2 ^ k * ((n : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1)) := by
        refine mul_le_mul_of_nonneg_right ?_ hxpos.le
        calc Real.sqrt (2 ^ k) ≤ Real.sqrt ((2 ^ k) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith)
          _ = 2 ^ k := Real.sqrt_sq (by positivity)

/-- **The k-distinctness certificate at the headline cost**:
`HasDual (kdFun k) ((k+1)·2^{k+1}·n^{k/(k+1)})`, for every `k ≥ 1`, every
finite index type, and every alphabet — the flow at `r = ⌊n^{k/(k+1)}⌋`,
with the read-everything dual covering `n ≤ 4^{k+1}`. -/
theorem hasDual_kdFun (k : ℕ) (hk : 1 ≤ k) (ι σ : Type)
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] :
    HasDual (kdFun (ι := ι) (σ := σ) k)
      (((k : ℝ) + 1) * 2 ^ (k + 1)
        * (Fintype.card ι : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1))) := by
  have hkR : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hexp0 : (0 : ℝ) < (k : ℝ) / ((k : ℝ) + 1) := div_pos hkpos hkR
  by_cases hn : Fintype.card ι ≤ 4 ^ (k + 1)
  · -- small `n`: the read-everything dual costs `2n`
    refine (hasDual_two_mul_card (kdFun (ι := ι) (σ := σ) k)).mono ?_
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.zero_rpow (ne_of_gt hexp0), mul_zero]
      norm_num
    · have hnpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hpos
      have hn1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hpos
      have h4 : ((Fintype.card ι : ℝ)) ^ ((1 : ℝ) / ((k : ℝ) + 1)) ≤ 4 := by
        rw [← kd_rpow_four k]
        refine Real.rpow_le_rpow hnpos.le ?_ (by positivity)
        calc (Fintype.card ι : ℝ) ≤ ((4 ^ (k + 1) : ℕ) : ℝ) := by
              exact_mod_cast hn
          _ = (4 : ℝ) ^ (k + 1 : ℕ) := by push_cast; ring
      have hκ0 : (0 : ℝ)
          ≤ ((Fintype.card ι : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1)) :=
        Real.rpow_nonneg hnpos.le _
      have h8 : (8 : ℝ) ≤ ((k : ℝ) + 1) * 2 ^ (k + 1) := by
        have h2k : (4 : ℝ) ≤ 2 ^ (k + 1) := by
          calc (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
            _ ≤ 2 ^ (k + 1) :=
              pow_le_pow_right₀ (by norm_num) (by omega)
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        nlinarith
      calc 2 * (Fintype.card ι : ℝ)
          = 2 * (((Fintype.card ι : ℝ)) ^ ((1 : ℝ) / ((k : ℝ) + 1))
              * ((Fintype.card ι : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))) := by
            rw [kd_rpow_split k hnpos]
        _ ≤ 2 * (4 * ((Fintype.card ι : ℝ))
              ^ ((k : ℝ) / ((k : ℝ) + 1))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact mul_le_mul_of_nonneg_right h4 hκ0
        _ = 8 * ((Fintype.card ι : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1)) := by
            ring
        _ ≤ ((k : ℝ) + 1) * 2 ^ (k + 1)
              * ((Fintype.card ι : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right h8 hκ0
  · -- large `n`: the flow at `r = ⌊n^{k/(k+1)}⌋`
    push_neg at hn
    have hnpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
      have h : 0 < Fintype.card ι := by
        have := pow_pos (show 0 < 4 by norm_num) (k + 1)
        omega
      exact_mod_cast h
    have hn1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
      have h : 1 ≤ Fintype.card ι := by
        have := pow_pos (show 0 < 4 by norm_num) (k + 1)
        omega
      exact_mod_cast h
    have hκ0 : (0 : ℝ)
        ≤ ((Fintype.card ι : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1)) :=
      Real.rpow_nonneg hnpos.le _
    have hfloorle : ((⌊((Fintype.card ι : ℝ))
        ^ ((k : ℝ) / ((k : ℝ) + 1))⌋₊ : ℕ) : ℝ)
        ≤ ((Fintype.card ι : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1)) :=
      Nat.floor_le hκ0
    have hfloorlt : ((Fintype.card ι : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))
        < ((⌊((Fintype.card ι : ℝ))
            ^ ((k : ℝ) / ((k : ℝ) + 1))⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hroot4 : (4 : ℝ)
        ≤ ((Fintype.card ι : ℝ)) ^ ((1 : ℝ) / ((k : ℝ) + 1)) := by
      rw [← kd_rpow_four k]
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      calc (4 : ℝ) ^ (k + 1 : ℕ) = ((4 ^ (k + 1) : ℕ) : ℝ) := by
            push_cast
            ring
        _ ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hn.le
    have hquarter : 4 * ((Fintype.card ι : ℝ))
        ^ ((k : ℝ) / ((k : ℝ) + 1)) ≤ (Fintype.card ι : ℝ) := by
      calc 4 * ((Fintype.card ι : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))
          ≤ ((Fintype.card ι : ℝ)) ^ ((1 : ℝ) / ((k : ℝ) + 1))
            * ((Fintype.card ι : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right hroot4 hκ0
        _ = (Fintype.card ι : ℝ) := kd_rpow_split k hnpos
    have h4k : 4 * ((k : ℝ) + 1) ≤ (Fintype.card ι : ℝ) := by
      have hn4 : 4 * (k + 1) ≤ Fintype.card ι := by
        have h1 : k < 2 ^ k := Nat.lt_pow_self (by norm_num : (1 : ℕ) < 2)
        have h2 : (2 : ℕ) ^ k ≤ 4 ^ k := Nat.pow_le_pow_left (by norm_num) k
        have h3 : 4 * 4 ^ k = 4 ^ (k + 1) := by ring
        have h4 : 4 ^ (k + 1) ≤ Fintype.card ι := hn.le
        calc 4 * (k + 1) ≤ 4 * 2 ^ k := by omega
          _ ≤ 4 * 4 ^ k := by omega
          _ = 4 ^ (k + 1) := h3
          _ ≤ _ := h4
      have hc : ((4 * (k + 1) : ℕ) : ℝ) ≤ ((Fintype.card ι : ℕ) : ℝ) :=
        Nat.cast_le.mpr hn4
      push_cast at hc
      linarith
    have hkey : 2 * (⌊((Fintype.card ι : ℝ))
        ^ ((k : ℝ) / ((k : ℝ) + 1))⌋₊ + k) ≤ Fintype.card ι := by
      have hc : ((2 * (⌊((Fintype.card ι : ℝ))
          ^ ((k : ℝ) / ((k : ℝ) + 1))⌋₊ + k) : ℕ) : ℝ)
          ≤ (Fintype.card ι : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hc
    refine (hasDual_kdFun_param (σ := σ) k
      ⌊((Fintype.card ι : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))⌋₊ hk
      hkey).mono ?_
    have hsum : (∑ ℓ ∈ Finset.range k,
        Real.sqrt (((2 ^ k * Fintype.card ι ^ (ℓ + 1) : ℕ) : ℝ)
          / ((((⌊((Fintype.card ι : ℝ))
              ^ ((k : ℝ) / ((k : ℝ) + 1))⌋₊ : ℕ) + 1) ^ ℓ : ℕ) : ℝ))
        ≤ (k : ℝ) * (2 ^ k * ((Fintype.card ι : ℝ))
            ^ ((k : ℝ) / ((k : ℝ) + 1)))) := by
      calc (∑ ℓ ∈ Finset.range k,
          Real.sqrt (((2 ^ k * Fintype.card ι ^ (ℓ + 1) : ℕ) : ℝ)
            / ((((⌊((Fintype.card ι : ℝ))
                ^ ((k : ℝ) / ((k : ℝ) + 1))⌋₊ : ℕ) + 1) ^ ℓ : ℕ) : ℝ)))
          ≤ ∑ _ℓ ∈ Finset.range k, (2 ^ k * ((Fintype.card ι : ℝ))
              ^ ((k : ℝ) / ((k : ℝ) + 1))) := by
            refine Finset.sum_le_sum fun ℓ hℓ => ?_
            exact kd_term_le (Finset.mem_range.mp hℓ) hn1 hfloorlt
        _ = (k : ℝ) * (2 ^ k * ((Fintype.card ι : ℝ))
              ^ ((k : ℝ) / ((k : ℝ) + 1))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hstageI : (2 : ℝ) ^ (k + 1)
        * (⌊((Fintype.card ι : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))⌋₊ : ℝ)
        ≤ 2 ^ (k + 1)
          * ((Fintype.card ι : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hfloorle (by positivity)
    have hfinal : (2 : ℝ) ^ (k + 1)
        * ((Fintype.card ι : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))
        + (k : ℝ) * (2 ^ k * ((Fintype.card ι : ℝ))
            ^ ((k : ℝ) / ((k : ℝ) + 1)))
        ≤ ((k : ℝ) + 1) * 2 ^ (k + 1)
          * ((Fintype.card ι : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1)) := by
      have hbase : (0 : ℝ) ≤ 2 ^ k
          * ((Fintype.card ι : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1)) := by
        positivity
      have hstep : ((k : ℝ) + 1) * 2 ^ (k + 1)
            * ((Fintype.card ι : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))
          - (2 ^ (k + 1)
              * ((Fintype.card ι : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))
            + (k : ℝ) * (2 ^ k
              * ((Fintype.card ι : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))))
          = (k : ℝ) * (2 ^ k
              * ((Fintype.card ι : ℝ)) ^ ((k : ℝ) / ((k : ℝ) + 1))) := by
        ring
      linarith [mul_nonneg hkpos.le hbase]
    linarith

/-- **The k-distinctness upper bound**:
`ADV±(kdFun k) ≤ (k+1)·2^{k+1}·n^{k/(k+1)}`, for every `k ≥ 1`, every
finite index type, and every alphabet — weak duality on the bundled
certificate. -/
theorem advPM_kdFun_le (k : ℕ) (hk : 1 ≤ k) (ι σ : Type)
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] :
    advPM (kdFun (ι := ι) (σ := σ) k)
      ≤ ((k : ℝ) + 1) * 2 ^ (k + 1)
        * (Fintype.card ι : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1)) :=
  advPM_le_of_hasDual
    (mul_nonneg (by positivity)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (hasDual_kdFun k hk ι σ)

end QuantumQueryComplexity
