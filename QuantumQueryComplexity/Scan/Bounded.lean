import QuantumQueryComplexity.Scan.Dual
import QuantumQueryComplexity.HasDual
import QuantumQueryComplexity.Promise.HasDual
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The bounded-change scan: `HasDual f (8√(nC))`

If `f` is computed by a deterministic sequential summary in a fixed order,

    q₀ ∈ Q,   qᵢ(x) = δᵢ(qᵢ₋₁(x), xᵢ),   f(x) = g(q_n(x)),

and every trajectory changes state at most `C` times, then `f` has an
explicit dual of cost `8√(nC)`.

All the adversary algebra is inherited from `Scan.dual`: the scan's branch
at coordinate `i` is the **after-state** `qᵢ₊₁(x)` and its colour marks a
state change.  The node component of `Scan.dual` is the transcript of
earlier after-states, `black_unique` is determinism (two unchanged branches
from a common old state coincide), and `br_ne` is determinism read
backwards (a changed after-state from a common old state forces a changed
letter).  What is new here is only the **constant** weight choice

    W^black = √n/√C,   W^red = √C/√n,

under which the `u` mass is `4((n−r)·√C/√n + r·√n/√C) ≤ 8√(nC)` and the
`v` mass is `4(n·√C/√n + r·√n/√C) ≤ 8√(nC)` for every trajectory with
`r ≤ C` red steps — no permutation averaging, no depth dependence.

The statement covers the degenerate cases: at `C = 0` every trajectory is
constant so `f` is constant, at `n = 0` the domain is a single point, and
in both the bound `8√(nC)` is exactly `0`.

Two forms. `hasDualOn_scan` is the **promise-native** lemma: the
change bound is required only on the promised inputs `read x`, and the
total scan dual is restricted to the promise (`DualPair.restrictTo`), where
only the promise inputs' masses are charged.  `hasDual_scan` is the total
special case `read = id`.
-/

namespace QuantumQueryComplexity

variable {n : ℕ} {σ : Type} [Fintype σ] [DecidableEq σ]
variable {O : Type} [Fintype O] [DecidableEq O]
variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-! ## The sequential summary -/

/-- The state after `t` steps of the sequential summary. -/
def scanState (q₀ : Q) (δ : Fin n → Q → σ → Q) (x : Fin n → σ) : ℕ → Q
  | 0 => q₀
  | t + 1 =>
      if h : t < n then δ ⟨t, h⟩ (scanState q₀ δ x t) (x ⟨t, h⟩)
      else scanState q₀ δ x t

variable (q₀ : Q) (δ : Fin n → Q → σ → Q)

@[simp] lemma scanState_zero (x : Fin n → σ) : scanState q₀ δ x 0 = q₀ := rfl

/-- The step at a genuine coordinate. -/
lemma scanState_succ_fin (x : Fin n → σ) (i : Fin n) :
    scanState q₀ δ x ((i : ℕ) + 1)
      = δ i (scanState q₀ δ x (i : ℕ)) (x i) := by
  simp only [scanState, dif_pos i.isLt, Fin.eta]

/-- The colour of step `i`: `true` exactly when the state changes. -/
def scanCol (x : Fin n → σ) (i : Fin n) : Bool :=
  decide (scanState q₀ δ x ((i : ℕ) + 1) ≠ scanState q₀ δ x (i : ℕ))

/-- The number of state changes along the trajectory. -/
def changeCount (x : Fin n → σ) : ℕ :=
  (Finset.univ.filter fun i => scanCol q₀ δ x i = true).card

/-! ## Agreement lemmas -/

/-- The state before a coordinate is determined by the earlier after-states:
it is `q₀` at the start and the previous after-state otherwise. -/
lemma scanState_coe_eq_of_agree {x y : Fin n → σ} {i : Fin n}
    (h : ∀ j : Fin n, (j : ℕ) < (i : ℕ) →
      scanState q₀ δ x ((j : ℕ) + 1) = scanState q₀ δ y ((j : ℕ) + 1)) :
    scanState q₀ δ x (i : ℕ) = scanState q₀ δ y (i : ℕ) := by
  by_cases h0 : (i : ℕ) = 0
  · rw [h0, scanState_zero, scanState_zero]
  · obtain ⟨m, hm⟩ : ∃ m, (i : ℕ) = m + 1 := ⟨(i : ℕ) - 1, by omega⟩
    have hmn : m < n := by have := i.isLt; omega
    have hcoe : ((⟨m, hmn⟩ : Fin n) : ℕ) = m := rfl
    have := h ⟨m, hmn⟩ (by rw [hcoe]; omega)
    rw [hm]
    exact this

/-- Agreement of all after-states propagates to every time. -/
lemma scanState_eq_of_all_agree {x y : Fin n → σ}
    (h : ∀ j : Fin n,
      scanState q₀ δ x ((j : ℕ) + 1) = scanState q₀ δ y ((j : ℕ) + 1)) :
    ∀ t, scanState q₀ δ x t = scanState q₀ δ y t := by
  intro t
  induction t with
  | zero => rfl
  | succ m ih =>
      by_cases hm : m < n
      · exact h ⟨m, hm⟩
      · simp only [scanState, dif_neg hm]
        exact ih

/-- A changeless trajectory never leaves `q₀`. -/
lemma scanState_eq_of_changeCount_zero {x : Fin n → σ}
    (hx : changeCount q₀ δ x = 0) : ∀ t, scanState q₀ δ x t = q₀ := by
  have hall : ∀ i : Fin n,
      scanState q₀ δ x ((i : ℕ) + 1) = scanState q₀ δ x (i : ℕ) := by
    intro i
    by_contra hne
    have hmem : i ∈ Finset.univ.filter fun j => scanCol q₀ δ x j = true := by
      simp [scanCol, hne]
    rw [Finset.card_eq_zero.mp hx] at hmem
    exact absurd hmem (Finset.notMem_empty i)
  intro t
  induction t with
  | zero => rfl
  | succ m ih =>
      by_cases hm : m < n
      · rw [hall ⟨m, hm⟩]
        exact ih
      · simp only [scanState, dif_neg hm]
        exact ih

/-! ## The scan -/

/-- **The bounded-change scan**: the natural-order scan whose branch is the
after-state and whose colour marks a state change. -/
def boundedScan (g : Q → O) : Scan (Fin n) σ O Q where
  rank := fun i => Fin.cast (Fintype.card_fin n).symm i
  rank_inj := Fin.cast_injective _
  br x i := scanState q₀ δ x ((i : ℕ) + 1)
  col x i := scanCol q₀ δ x i
  out x := g (scanState q₀ δ x n)
  br_ne := by
    intro x y i hagree hbr hxy
    apply hbr
    have hbefore : scanState q₀ δ x (i : ℕ) = scanState q₀ δ y (i : ℕ) :=
      scanState_coe_eq_of_agree q₀ δ fun j hj => hagree j hj
    rw [scanState_succ_fin, scanState_succ_fin, hbefore, hxy]
  out_eq := fun x y h =>
    congrArg g (scanState_eq_of_all_agree q₀ δ h n)
  black_unique := by
    intro x y i hx hy hagree
    have hx' : scanState q₀ δ x ((i : ℕ) + 1) = scanState q₀ δ x (i : ℕ) :=
      not_not.mp (by simpa [scanCol] using hx)
    have hy' : scanState q₀ δ y ((i : ℕ) + 1) = scanState q₀ δ y (i : ℕ) :=
      not_not.mp (by simpa [scanCol] using hy)
    have hbefore : scanState q₀ δ x (i : ℕ) = scanState q₀ δ y (i : ℕ) :=
      scanState_coe_eq_of_agree q₀ δ fun j hj => hagree j hj
    rw [hx', hy', hbefore]

/-! ## The constant weights -/

/-- Black pays `√n/√C`, red pays `√C/√n`. -/
noncomputable def bcWeight (n C : ℕ) : Fin n → Bool → ℝ := fun _ c =>
  if c then Real.sqrt C / Real.sqrt n else Real.sqrt n / Real.sqrt C

lemma bcWeight_pos {C : ℕ} (hn : 0 < n) (hC : 0 < C) (i : Fin n) (c : Bool) :
    0 < bcWeight n C i c := by
  have h1 : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have h2 : (0 : ℝ) < Real.sqrt C := Real.sqrt_pos.mpr (by exact_mod_cast hC)
  cases c <;> simp only [bcWeight, if_true] <;> positivity

lemma bcWeight_inv {C : ℕ} (i : Fin n) (c : Bool) :
    (bcWeight n C i c)⁻¹
      = if c then Real.sqrt n / Real.sqrt C
        else Real.sqrt C / Real.sqrt n := by
  cases c <;> simp [bcWeight, inv_div]

/-! ## The cost arithmetic -/

private lemma sum_ite_le {p : Fin n → Prop} [DecidablePred p] {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) {r : ℕ}
    (hr : (Finset.univ.filter p).card ≤ r) :
    (∑ i, if p i then a else b) ≤ (r : ℝ) * a + (n : ℝ) * b := by
  classical
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
    nsmul_eq_mul]
  have h1 : ((Finset.univ.filter p).card : ℝ) * a ≤ (r : ℝ) * a :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hr) ha
  have h2 : ((Finset.univ.filter fun i => ¬ p i).card : ℝ) * b
      ≤ (n : ℝ) * b := by
    refine mul_le_mul_of_nonneg_right ?_ hb
    have h := Finset.card_filter_le Finset.univ fun i : Fin n => ¬ p i
    have h' : (Finset.univ : Finset (Fin n)).card = n := by simp
    exact_mod_cast h.trans_eq h'
  linarith

/-- `n·(√C/√n) = √n·√C`, the `u`-side cancellation. -/
private lemma cast_mul_div_sqrt {m C : ℕ} (hm : 0 < m) :
    (m : ℝ) * (Real.sqrt C / Real.sqrt m) = Real.sqrt m * Real.sqrt C := by
  have hs : Real.sqrt m * Real.sqrt m = (m : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg m)
  have hne : Real.sqrt m ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hm)).ne'
  rw [← mul_div_assoc, div_eq_iff hne]
  linear_combination (-(Real.sqrt C)) * hs

/-- **The `u` mass of the scan dual at one input with at most `C` changes**:
`4((n−r)·√C/√n + r·√n/√C) ≤ 8√(nC)`. -/
lemma scan_u_mass_le (g : Q → O) {C : ℕ} (hn : 0 < n) (hC : 0 < C)
    {x : Fin n → σ} (hx : changeCount q₀ δ x ≤ C) :
    (4 : ℝ) * ∑ i, (bcWeight n C i ((boundedScan q₀ δ g).col x i))⁻¹
      ≤ 8 * Real.sqrt ((n : ℝ) * (C : ℝ)) := by
  classical
  have hsplit : Real.sqrt ((n : ℝ) * (C : ℝ))
      = Real.sqrt n * Real.sqrt C := Real.sqrt_mul (Nat.cast_nonneg n) _
  have hkeyn : (n : ℝ) * (Real.sqrt C / Real.sqrt n)
      = Real.sqrt n * Real.sqrt C := cast_mul_div_sqrt hn
  have hkeyC : (C : ℝ) * (Real.sqrt n / Real.sqrt C)
      = Real.sqrt n * Real.sqrt C := by
    rw [cast_mul_div_sqrt hC]
    ring
  have hfilter : (Finset.univ.filter fun i =>
      (boundedScan q₀ δ g).col x i = true).card ≤ C := hx
  have hsum : (∑ i, (bcWeight n C i ((boundedScan q₀ δ g).col x i))⁻¹)
      ≤ (C : ℝ) * (Real.sqrt n / Real.sqrt C)
        + (n : ℝ) * (Real.sqrt C / Real.sqrt n) := by
    simp only [bcWeight_inv]
    exact sum_ite_le (by positivity) (by positivity) hfilter
  calc (4 : ℝ) * ∑ i, (bcWeight n C i ((boundedScan q₀ δ g).col x i))⁻¹
      ≤ 4 * ((C : ℝ) * (Real.sqrt n / Real.sqrt C)
          + (n : ℝ) * (Real.sqrt C / Real.sqrt n)) := by linarith
    _ = 8 * Real.sqrt ((n : ℝ) * (C : ℝ)) := by
        rw [hkeyn, hkeyC, hsplit]
        ring

/-- **The `v` mass of the scan dual at one input with at most `C` changes**:
`4(n·√C/√n + r·√n/√C) ≤ 8√(nC)`. -/
lemma scan_v_mass_le (g : Q → O) {C : ℕ} (hn : 0 < n) (hC : 0 < C)
    {y : Fin n → σ} (hy : changeCount q₀ δ y ≤ C) :
    (4 : ℝ) * ∑ i, (bcWeight n C i true
        + if (boundedScan q₀ δ g).col y i then bcWeight n C i false else 0)
      ≤ 8 * Real.sqrt ((n : ℝ) * (C : ℝ)) := by
  classical
  have hsplit : Real.sqrt ((n : ℝ) * (C : ℝ))
      = Real.sqrt n * Real.sqrt C := Real.sqrt_mul (Nat.cast_nonneg n) _
  have hkeyn : (n : ℝ) * (Real.sqrt C / Real.sqrt n)
      = Real.sqrt n * Real.sqrt C := cast_mul_div_sqrt hn
  have hkeyC : (C : ℝ) * (Real.sqrt n / Real.sqrt C)
      = Real.sqrt n * Real.sqrt C := by
    rw [cast_mul_div_sqrt hC]
    ring
  have hfilter : (Finset.univ.filter fun i =>
      (boundedScan q₀ δ g).col y i = true).card ≤ C := hy
  have hsum : (∑ i, (bcWeight n C i true
        + if (boundedScan q₀ δ g).col y i then bcWeight n C i false
          else 0))
      ≤ (n : ℝ) * (Real.sqrt C / Real.sqrt n)
        + (C : ℝ) * (Real.sqrt n / Real.sqrt C) := by
    have hterm : ∀ i : Fin n,
        (bcWeight n C i true
          + if (boundedScan q₀ δ g).col y i then bcWeight n C i false
            else 0)
        = Real.sqrt C / Real.sqrt n
          + if (boundedScan q₀ δ g).col y i = true
            then Real.sqrt n / Real.sqrt C else 0 := by
      intro i
      by_cases hcol : (boundedScan q₀ δ g).col y i = true <;>
        simp [bcWeight, hcol]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
      Finset.sum_const]
    have h1 : ((Finset.univ : Finset (Fin n)).card : ℝ)
        * (Real.sqrt C / Real.sqrt n)
        = (n : ℝ) * (Real.sqrt C / Real.sqrt n) := by
      norm_num
    have h2 : (∑ i, if (boundedScan q₀ δ g).col y i = true
          then Real.sqrt n / Real.sqrt C else 0)
        ≤ (C : ℝ) * (Real.sqrt n / Real.sqrt C) + (n : ℝ) * 0 :=
      sum_ite_le (by positivity) le_rfl hfilter
    rw [nsmul_eq_mul, h1]
    rw [mul_zero, add_zero] at h2
    linarith
  calc (4 : ℝ) * ∑ i, (bcWeight n C i true
        + if (boundedScan q₀ δ g).col y i then bcWeight n C i false
          else 0)
      ≤ 4 * ((n : ℝ) * (Real.sqrt C / Real.sqrt n)
          + (C : ℝ) * (Real.sqrt n / Real.sqrt C)) := by linarith
    _ = 8 * Real.sqrt ((n : ℝ) * (C : ℝ)) := by
        rw [hkeyn, hkeyC, hsplit]
        ring

/-! ## The theorem -/

/-- **The bounded-change scan**: a sequential summary whose trajectory changes at
most `C` times on every input yields an explicit dual of cost `8√(nC)` for
`f = g ∘ (final state)`.  The degenerate cases are included: at `C = 0` or
`n = 0` the output is constant and the bound is exactly `0`. -/
theorem hasDual_scan (g : Q → O) {C : ℕ}
    (hC : ∀ x : Fin n → σ, changeCount q₀ δ x ≤ C) :
    HasDual (fun x : Fin n → σ => g (scanState q₀ δ x n))
      (8 * Real.sqrt ((n : ℝ) * (C : ℝ))) := by
  classical
  rcases Nat.eq_zero_or_pos C with hC0 | hCpos
  · -- `C = 0`: every trajectory is constant, so the output is constant
    subst hC0
    have hconst : ∀ x : Fin n → σ, g (scanState q₀ δ x n) = g q₀ := fun x =>
      congrArg g
        (scanState_eq_of_changeCount_zero q₀ δ (Nat.le_zero.mp (hC x)) n)
    exact (hasDual_const fun x y => by rw [hconst x, hconst y]).mono
      (by positivity)
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- `n = 0`: a one-point domain
    have hxy : ∀ x y : Fin n → σ, x = y := by
      subst hn0
      exact fun x y => funext fun i => i.elim0
    exact (hasDual_const fun x y => by rw [hxy x y]).mono (by positivity)
  -- the main case: the scan dual at the constant weights
  have hW : ∀ (i : Fin n) (c : Bool), 0 < bcWeight n C i c :=
    bcWeight_pos hnpos hCpos
  exact hasDual_of_dualPair ((boundedScan q₀ δ g).dual (bcWeight n C) hW)
    ((boundedScan q₀ δ g).dual_isCostLe (bcWeight n C) hW
      (fun x => scan_u_mass_le q₀ δ g hnpos hCpos (hC x))
      (fun y => scan_v_mass_le q₀ δ g hnpos hCpos (hC y)))

/-- **The bounded-change scan, promise-native**: on a promise `read : X → Fin n → σ`,
if every *promised* trajectory changes at most `C` times, the summary's
output has a promise dual of cost `8√(nC)`.  The total scan dual is
restricted to the promise; only the promised inputs' masses are charged. -/
theorem hasDualOn_scan {X : Type} [Fintype X] (read : X → Fin n → σ)
    (g : Q → O) {C : ℕ}
    (hC : ∀ x : X, changeCount q₀ δ (read x) ≤ C) :
    HasDualOn read (fun x : X => g (scanState q₀ δ (read x) n))
      (8 * Real.sqrt ((n : ℝ) * (C : ℝ))) := by
  classical
  rcases Nat.eq_zero_or_pos C with hC0 | hCpos
  · subst hC0
    have hconst : ∀ x : X, g (scanState q₀ δ (read x) n) = g q₀ := fun x =>
      congrArg g
        (scanState_eq_of_changeCount_zero q₀ δ (Nat.le_zero.mp (hC x)) n)
    exact (hasDualOn_of_dualPairOn
      (DualPairOn.const read _ fun x y => by rw [hconst x, hconst y])
      (DualPairOn.const_isCostLe _)).mono (by positivity)
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · have hxy : ∀ x y : X, read x = read y := by
      subst hn0
      exact fun x y => funext fun i => i.elim0
    exact (hasDualOn_of_dualPairOn
      (DualPairOn.const read _ fun x y => by rw [hxy x y])
      (DualPairOn.const_isCostLe _)).mono (by positivity)
  have hW : ∀ (i : Fin n) (c : Bool), 0 < bcWeight n C i c :=
    bcWeight_pos hnpos hCpos
  refine hasDualOn_of_dualPairOn
    (((boundedScan q₀ δ g).dual (bcWeight n C) hW).restrictTo read) ⟨?_, ?_⟩
  · intro x
    exact ((boundedScan q₀ δ g).sum_dual_u_sq (bcWeight n C) hW (read x)).trans_le
      (scan_u_mass_le q₀ δ g hnpos hCpos (hC x))
  · intro y
    exact ((boundedScan q₀ δ g).sum_dual_v_sq (bcWeight n C) hW (read y)).trans_le
      (scan_v_mass_le q₀ δ g hnpos hCpos (hC y))

end QuantumQueryComplexity
