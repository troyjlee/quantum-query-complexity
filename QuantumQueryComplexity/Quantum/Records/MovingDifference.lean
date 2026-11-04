import QuantumQueryComplexity.Quantum.Records.Interaction

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Moving a difference through an averaging operator: Lemma 4.6

Lemma 4.5 controls sums of `‖F Dᵢ f‖²`; query errors produce the other order, `Dᵢ F f`.  Lemma 4.6
of Cornelissen–Gilani–Zhou compares them for `F = (I + H/R)⁻¹`, `H = ∑ⱼ wⱼ Dⱼ`, when the weighted
interaction of `i` with the other coordinates is at most `d` outside an exceptional event of
probability at most `b`.  Unlike Lemma 4.5, the event may depend on every coordinate.

The proof first bounds `‖[Dᵢ, H] f‖²` (CGZ (4.29)) by a pointwise weighted Cauchy–Schwarz
inequality using (4.20) on the good event and (4.18), then moves `Dᵢ` through `F` with the
commutator identity, the energy bound and both contractions of Lemma 4.2, and finally absorbs
the `‖Dᵢ F f‖²` term using `pd ≤ 2/5`, `p ≤ 1/2` and `R ≥ 1`.

## Main results

* `CondBern.lemma_4_6` — Lemma 4.6, on every finite workspace.
-/

namespace QuantumQueryComplexity

open scoped Matrix MatrixOrder ComplexOrder
open Matrix

variable {ι A : Type} [Fintype ι] [DecidableEq ι] [Fintype A]

/-! ### Norm helpers -/

section NormHelpers

/-- A row of a joint vector has squared norm `ρ(x)` times that of its workspace vector. -/
private lemma qNormSq_row_eq {Ω : Type} [Fintype Ω] [DecidableEq Ω] (ρ : FinDist Ω)
    (f : JVec ρ.Supp A) (x : ρ.Supp) : qNormSq (f x) = ρ.mass x * qNormSq (ρ.wvec f x) := by
  classical
  conv_lhs => rw [← ρ.ofWvec_wvec f]
  rw [FinDist.ofWvec, qNormSq_smul, Complex.normSq_ofReal, Real.mul_self_sqrt (ρ.mass_nonneg x)]

private lemma jNormSq_smul' {X : Type} [Fintype X] (c : ℂ) (f : JVec X A) :
    jNormSq (c • f) = Complex.normSq c * jNormSq f := by
  classical
  unfold jNormSq
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => qNormSq_smul c (f x)

private lemma jNormSq_neg' {X : Type} [Fintype X] (f : JVec X A) : jNormSq (-f) = jNormSq f := by
  have h : -f = ((-1 : ℂ)) • f := by simp
  rw [h, jNormSq_smul']
  simp

private lemma qNormSq_add_le_two (u v : A → ℂ) :
    qNormSq (u + v) ≤ 2 * qNormSq u + 2 * qNormSq v := by
  classical
  have h := sqrt_qNormSq_add_le u v
  have hu := Real.sq_sqrt (qNormSq_nonneg u)
  have hv := Real.sq_sqrt (qNormSq_nonneg v)
  have huv := Real.sq_sqrt (qNormSq_nonneg (u + v))
  have h0 := Real.sqrt_nonneg (qNormSq (u + v))
  have h2 := mul_self_le_mul_self h0 h
  nlinarith [sq_nonneg (√(qNormSq u) - √(qNormSq v))]

/-- `‖f + g‖² ≤ 2‖f‖² + 2‖g‖²`. -/
private lemma jNormSq_add_le_two {X : Type} [Fintype X] (f g : JVec X A) :
    jNormSq (f + g) ≤ 2 * jNormSq f + 2 * jNormSq g := by
  unfold jNormSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun x _ => qNormSq_add_le_two (f x) (g x)

private lemma sqrt_qNormSq_sum_le' {β : Type*} (s : Finset β) (v : β → A → ℂ) :
    √(qNormSq (∑ j ∈ s, v j)) ≤ ∑ j ∈ s, √(qNormSq (v j)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb]
    exact (sqrt_qNormSq_add_le _ _).trans (by linarith)

/-- **Weighted Cauchy–Schwarz**: `‖∑ⱼ cⱼ uⱼ‖² ≤ (∑ⱼ cⱼ)(∑ⱼ cⱼ ‖uⱼ‖²)` for `cⱼ ≥ 0`. -/
private lemma qNormSq_sum_smul_le {β : Type*} (s : Finset β) (c : β → ℝ)
    (hc : ∀ j ∈ s, 0 ≤ c j) (u : β → A → ℂ) :
    qNormSq (∑ j ∈ s, ((c j : ℝ) : ℂ) • u j)
      ≤ (∑ j ∈ s, c j) * ∑ j ∈ s, c j * qNormSq (u j) := by
  classical
  have h1 : √(qNormSq (∑ j ∈ s, ((c j : ℝ) : ℂ) • u j))
      ≤ ∑ j ∈ s, c j * √(qNormSq (u j)) := by
    refine (sqrt_qNormSq_sum_le' s _).trans (le_of_eq (Finset.sum_congr rfl fun j hj => ?_))
    rw [qNormSq_smul, Complex.normSq_ofReal, Real.sqrt_mul (mul_self_nonneg _),
      Real.sqrt_mul_self (hc j hj)]
  have h2 : (∑ j ∈ s, c j * √(qNormSq (u j))) ^ 2
      ≤ (∑ j ∈ s, c j) * ∑ j ∈ s, c j * qNormSq (u j) := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hc
      (fun j hj => mul_nonneg (hc j hj) (qNormSq_nonneg _)) fun j hj => le_of_eq ?_
    rw [mul_pow, Real.sq_sqrt (qNormSq_nonneg _)]
    ring
  have h0 := Real.sqrt_nonneg (qNormSq (∑ j ∈ s, ((c j : ℝ) : ℂ) • u j))
  calc qNormSq (∑ j ∈ s, ((c j : ℝ) : ℂ) • u j)
      = (√(qNormSq (∑ j ∈ s, ((c j : ℝ) : ℂ) • u j))) ^ 2 :=
        (Real.sq_sqrt (qNormSq_nonneg _)).symm
    _ ≤ (∑ j ∈ s, c j * √(qNormSq (u j))) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := h2

end NormHelpers

namespace CondBern

variable (μ : CondBern ι)

/-! ### The commutator `[Dᵢ, H]` (CGZ (4.29)) -/

/-- `[Dᵢ, H] = ∑_{j ≠ i} wⱼ [Dᵢ, Dⱼ]`. -/
private lemma condDiff_comm_varOp (w : ι → ℝ) (i : ι) :
    μ.dist.condDiff i * μ.dist.varOp w - μ.dist.varOp w * μ.dist.condDiff i
      = ∑ j ∈ Finset.univ.erase i, ((w j : ℝ) : ℂ) • μ.diffComm i j := by
  rw [Finset.sum_erase _ (by simp [diffComm])]
  simp only [FinDist.varOp, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    diffComm, smul_sub, ← Finset.sum_sub_distrib]

private lemma condDiff_comm_varOp_mul_apply (w : ι → ℝ) (i : ι) (g : JVec μ.dist.Supp A)
    (x : μ.dist.Supp) :
    ((μ.dist.condDiff i * μ.dist.varOp w - μ.dist.varOp w * μ.dist.condDiff i) * g) x
      = ∑ j ∈ Finset.univ.erase i, ((w j : ℝ) : ℂ) • (μ.diffComm i j * g) x := by
  rw [condDiff_comm_varOp, Matrix.sum_mul]
  funext a
  simp [Matrix.sum_apply, Matrix.smul_mul]

/-- The pointwise form of (4.29): weighted Cauchy–Schwarz with (4.20) on `G`, and the crude bound
`‖([Dᵢ, H] g)ˣ‖ ≤ 2p wmax ‖g‖∞` off `G`. -/
private lemma qNormSq_comm_row_le (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j) {wmax : ℝ}
    (hW : ∑ j, w j ≤ wmax) (i : ι) (G : (ι → Bool) → Prop) [DecidablePred G] {d : ℝ}
    (hd : ∀ x : μ.dist.Supp, G x.1 →
      ∑ j ∈ Finset.univ.erase i, w j * (if μ.Interact i j x.1 then 1 else 0) ≤ d)
    (hd0 : 0 ≤ d) (g : JVec μ.dist.Supp A) (x : μ.dist.Supp) :
    qNormSq (((μ.dist.condDiff i * μ.dist.varOp w - μ.dist.varOp w * μ.dist.condDiff i) * g) x)
      ≤ d * ∑ j ∈ Finset.univ.erase i, w j * qNormSq ((μ.diffComm i j * g) x)
        + (if G x.1 then 0
          else 4 * μ.p ^ 2 * wmax ^ 2 * μ.dist.infNormSq g * μ.dist.mass x) := by
  classical
  rw [condDiff_comm_varOp_mul_apply]
  set u : ι → A → ℂ := fun j => (μ.diffComm i j * g) x with hu
  set K := 4 * μ.p ^ 2 * μ.dist.infNormSq g * μ.dist.mass x with hK
  have hI := μ.dist.infNormSq_nonneg g
  have hm := μ.dist.mass_nonneg x
  have hK0 : 0 ≤ K := by positivity
  have h420 : ∀ j ∈ Finset.univ.erase i,
      qNormSq (u j) ≤ (if μ.Interact i j x.1 then 1 else 0) * K := by
    intro j hj
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    have h := μ.qNormSq_wvec_diffComm_le hij g x
    simp only [hu]
    rw [qNormSq_row_eq]
    calc μ.dist.mass x * qNormSq (μ.dist.wvec (μ.diffComm i j * g) x)
        ≤ μ.dist.mass x * (4 * μ.p ^ 2 * (if μ.Interact i j x.1 then 1 else 0)
          * μ.dist.infNormSq g) := mul_le_mul_of_nonneg_left h hm
      _ = _ := by rw [hK]; ring
  have hS0 : 0 ≤ ∑ j ∈ Finset.univ.erase i, w j * qNormSq (u j) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (qNormSq_nonneg _)
  have hW' : ∑ j ∈ Finset.univ.erase i, w j ≤ wmax :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun j _ _ => hw j).trans hW
  have hwmax : 0 ≤ wmax := (Finset.sum_nonneg fun j _ => hw j).trans hW
  by_cases hG : G x.1
  · simp only [hG, ↓reduceIte, add_zero]
    set c : ι → ℝ := fun j => w j * (if μ.Interact i j x.1 then 1 else 0) with hc_def
    have hc : ∀ j ∈ Finset.univ.erase i, 0 ≤ c j := fun j _ =>
      mul_nonneg (hw j) (by split_ifs <;> norm_num)
    have heq : ∑ j ∈ Finset.univ.erase i, ((w j : ℝ) : ℂ) • u j
        = ∑ j ∈ Finset.univ.erase i, ((c j : ℝ) : ℂ) • u j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      by_cases hA : μ.Interact i j x.1
      · simp [c, hA]
      · have h0 : qNormSq (u j) ≤ 0 := by simpa [hA] using h420 j hj
        have hu0 : u j = 0 := qNormSq_eq_zero_iff.mp (le_antisymm h0 (qNormSq_nonneg _))
        simp [hu0]
    rw [heq]
    refine (qNormSq_sum_smul_le _ c hc u).trans ?_
    have hcd : ∑ j ∈ Finset.univ.erase i, c j ≤ d := hd x hG
    have hcq : ∑ j ∈ Finset.univ.erase i, c j * qNormSq (u j)
        ≤ ∑ j ∈ Finset.univ.erase i, w j * qNormSq (u j) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
        (by simp only [c]; split_ifs <;> simp [hw j]) (qNormSq_nonneg _)
    have hcq0 : 0 ≤ ∑ j ∈ Finset.univ.erase i, c j * qNormSq (u j) :=
      Finset.sum_nonneg fun j hj => mul_nonneg (hc j hj) (qNormSq_nonneg _)
    calc _ ≤ d * ∑ j ∈ Finset.univ.erase i, c j * qNormSq (u j) :=
          mul_le_mul_of_nonneg_right hcd hcq0
      _ ≤ _ := mul_le_mul_of_nonneg_left hcq hd0
  · simp only [hG, ↓reduceIte]
    refine (qNormSq_sum_smul_le _ w (fun j _ => hw j) u).trans ?_
    have h1 : ∑ j ∈ Finset.univ.erase i, w j * qNormSq (u j) ≤ wmax * K := by
      calc _ ≤ ∑ j ∈ Finset.univ.erase i, w j * K :=
            Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ((h420 j hj).trans
              (by split_ifs <;> simp [hK0])) (hw j)
        _ = (∑ j ∈ Finset.univ.erase i, w j) * K := by rw [Finset.sum_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right hW' hK0
    have h2 : (∑ j ∈ Finset.univ.erase i, w j) * ∑ j ∈ Finset.univ.erase i, w j * qNormSq (u j)
        ≤ wmax * (wmax * K) := mul_le_mul hW' h1 hS0 hwmax
    have h3 : wmax * (wmax * K)
        = 4 * μ.p ^ 2 * wmax ^ 2 * μ.dist.infNormSq g * μ.dist.mass x := by rw [hK]; ring
    nlinarith [mul_nonneg hd0 hS0]

/-- Summing the pointwise bound: `‖[Dᵢ, H] g‖² ≤ d ∑_{j≠i} wⱼ ‖[Dᵢ, Dⱼ] g‖² + 4p²wmax²b ‖g‖∞²`. -/
private lemma jNormSq_comm_le_sum (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j) {wmax : ℝ}
    (hW : ∑ j, w j ≤ wmax) (i : ι) (G : (ι → Bool) → Prop) [DecidablePred G] {b d : ℝ}
    (hb : μ.dist.prob (Finset.univ.filter fun x : μ.dist.Supp => ¬ G x.1) ≤ b)
    (hd : ∀ x : μ.dist.Supp, G x.1 →
      ∑ j ∈ Finset.univ.erase i, w j * (if μ.Interact i j x.1 then 1 else 0) ≤ d)
    (hd0 : 0 ≤ d) (g : JVec μ.dist.Supp A) :
    jNormSq ((μ.dist.condDiff i * μ.dist.varOp w - μ.dist.varOp w * μ.dist.condDiff i) * g)
      ≤ d * ∑ j ∈ Finset.univ.erase i, w j * jNormSq (μ.diffComm i j * g)
        + 4 * μ.p ^ 2 * wmax ^ 2 * b * μ.dist.infNormSq g := by
  set K := 4 * μ.p ^ 2 * wmax ^ 2 * μ.dist.infNormSq g with hK
  have hK0 : 0 ≤ K := by have := μ.dist.infNormSq_nonneg g; positivity
  have e1 : ∑ x : μ.dist.Supp, d * ∑ j ∈ Finset.univ.erase i, w j * qNormSq ((μ.diffComm i j * g) x)
      = d * ∑ j ∈ Finset.univ.erase i, w j * jNormSq (μ.diffComm i j * g) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [jNormSq, Finset.mul_sum]
  have e2 : ∑ x : μ.dist.Supp, (if G x.1 then 0 else K * μ.dist.mass x)
      = K * μ.dist.prob (Finset.univ.filter fun x : μ.dist.Supp => ¬ G x.1) := by
    rw [FinDist.prob, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  calc jNormSq ((μ.dist.condDiff i * μ.dist.varOp w - μ.dist.varOp w * μ.dist.condDiff i) * g)
      ≤ ∑ x : μ.dist.Supp, (d * ∑ j ∈ Finset.univ.erase i, w j * qNormSq ((μ.diffComm i j * g) x)
          + (if G x.1 then 0 else K * μ.dist.mass x)) :=
        Finset.sum_le_sum fun x _ => μ.qNormSq_comm_row_le w hw hW i G hd hd0 g x
    _ = d * ∑ j ∈ Finset.univ.erase i, w j * jNormSq (μ.diffComm i j * g)
          + K * μ.dist.prob (Finset.univ.filter fun x : μ.dist.Supp => ¬ G x.1) := by
        rw [Finset.sum_add_distrib, e1, e2]
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hb hK0
        rw [hK] at this ⊢
        linarith

/-- (4.18) in norm form: `‖[Dᵢ, Dⱼ] g‖² ≤ p²(1+p)(‖AᵢⱼDᵢ g‖² + ‖AᵢⱼDⱼ g‖²)`. -/
private lemma jNormSq_diffComm_le {i j : ι} (hij : i ≠ j) (g : JVec μ.dist.Supp A) :
    jNormSq (μ.diffComm i j * g) ≤ μ.p ^ 2 * (1 + μ.p) *
      (jNormSq (μ.interactOp i j * (μ.dist.condDiff i * g))
        + jNormSq (μ.interactOp i j * (μ.dist.condDiff j * g))) := by
  have h := jNormSq_mul_le (μ.diffComm_sq_le_interact_condDiff hij) g
  refine h.trans (le_of_eq ?_)
  set P := μ.interactOp i j * μ.dist.condDiff i
  set Q := μ.interactOp i j * μ.dist.condDiff j
  have hP : jInner g (Pᴴ * P * g) = (jNormSq (P * g) : ℂ) := by
    rw [Matrix.mul_assoc, jInner_mul_right, Matrix.conjTranspose_conjTranspose, jInner_self]
  have hQ : jInner g (Qᴴ * Q * g) = (jNormSq (Q * g) : ℂ) := by
    rw [Matrix.mul_assoc, jInner_mul_right, Matrix.conjTranspose_conjTranspose, jInner_self]
  have e : jInner g ((((μ.p ^ 2 * (1 + μ.p) : ℝ)) : ℂ) • (Pᴴ * P + Qᴴ * Q) * g)
      = (((μ.p ^ 2 * (1 + μ.p) : ℝ)) : ℂ) * (jInner g (Pᴴ * P * g) + jInner g (Qᴴ * Q * g)) := by
    rw [jInner_eq_trace, jInner_eq_trace, jInner_eq_trace, Matrix.smul_mul, Matrix.add_mul,
      Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul]
  rw [e, hP, hQ, Matrix.mul_assoc, Matrix.mul_assoc]
  simp only [← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- `‖Aᵢⱼ h‖² = ∑ₓ Aᵢⱼ(x) ‖h x‖²`. -/
private lemma jNormSq_interactOp_mul (i j : ι) (h : JVec μ.dist.Supp A) :
    jNormSq (μ.interactOp i j * h)
      = ∑ x : μ.dist.Supp, (if μ.Interact i j x.1 then 1 else 0) * qNormSq (h x) := by
  classical
  unfold jNormSq
  refine Finset.sum_congr rfl fun x _ => ?_
  have e : (μ.interactOp i j * h) x
      = ((if μ.Interact i j x.1 then 1 else 0 : ℂ)) • h x := by
    funext a
    simp [interactOp, Matrix.diagonal_mul]
  rw [e, qNormSq_smul]
  split_ifs <;> simp

/-- `‖Aᵢⱼ h‖ ≤ ‖h‖`. -/
private lemma jNormSq_interactOp_mul_le (i j : ι) (h : JVec μ.dist.Supp A) :
    jNormSq (μ.interactOp i j * h) ≤ jNormSq h := by
  have hle : (μ.interactOp i j)ᴴ * μ.interactOp i j
      ≤ ((1 : ℝ) : ℂ) • (1 : Matrix μ.dist.Supp μ.dist.Supp ℂ) := by
    rw [(μ.interactOp_isHermitian i j).eq, μ.interactOp_mul_self, Complex.ofReal_one, one_smul]
    exact μ.interactOp_le_one i j
  simpa using jNormSq_mul_le_smul hle h

/-- `∑_{j≠i} wⱼ ‖AᵢⱼDᵢ g‖² ≤ d ‖Dᵢ g‖² + 4 wmax b ‖g‖∞²`, splitting on `G`. -/
private lemma sum_jNormSq_interactOp_condDiff_le (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j) {wmax : ℝ}
    (hW : ∑ j, w j ≤ wmax) (i : ι) (G : (ι → Bool) → Prop) [DecidablePred G] {b d : ℝ}
    (hb : μ.dist.prob (Finset.univ.filter fun x : μ.dist.Supp => ¬ G x.1) ≤ b)
    (hd : ∀ x : μ.dist.Supp, G x.1 →
      ∑ j ∈ Finset.univ.erase i, w j * (if μ.Interact i j x.1 then 1 else 0) ≤ d)
    (hd0 : 0 ≤ d) (g : JVec μ.dist.Supp A) :
    ∑ j ∈ Finset.univ.erase i, w j * jNormSq (μ.interactOp i j * (μ.dist.condDiff i * g))
      ≤ d * jNormSq (μ.dist.condDiff i * g) + 4 * wmax * b * μ.dist.infNormSq g := by
  classical
  set h := μ.dist.condDiff i * g with hh
  set K := 4 * wmax * μ.dist.infNormSq g with hK
  have hwmax : 0 ≤ wmax := (Finset.sum_nonneg fun j _ => hw j).trans hW
  have hK0 : 0 ≤ K := by have := μ.dist.infNormSq_nonneg g; positivity
  have hW' : ∑ j ∈ Finset.univ.erase i, w j ≤ wmax :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun j _ _ => hw j).trans hW
  have hq : ∀ x : μ.dist.Supp, qNormSq (h x) ≤ 4 * μ.dist.infNormSq g * μ.dist.mass x := by
    intro x
    rw [qNormSq_row_eq]
    have := (μ.dist.qNormSq_wvec_le_infNormSq h x).trans (μ.dist.infNormSq_condDiff_mul_le i g)
    nlinarith [μ.dist.mass_nonneg x]
  have hpt : ∀ x : μ.dist.Supp,
      (∑ j ∈ Finset.univ.erase i, w j * (if μ.Interact i j x.1 then 1 else 0)) * qNormSq (h x)
        ≤ d * qNormSq (h x) + (if G x.1 then 0 else K * μ.dist.mass x) := by
    intro x
    have hq0 := qNormSq_nonneg (h x)
    by_cases hG : G x.1
    · simp only [hG, ↓reduceIte, add_zero]
      exact mul_le_mul_of_nonneg_right (hd x hG) hq0
    · simp only [hG, ↓reduceIte]
      have h1 : ∑ j ∈ Finset.univ.erase i, w j * (if μ.Interact i j x.1 then 1 else 0) ≤ wmax :=
        (Finset.sum_le_sum fun j _ => by split_ifs <;> simp [hw j]).trans hW'
      have h2 := mul_le_mul h1 (hq x) hq0 hwmax
      have h3 : wmax * (4 * μ.dist.infNormSq g * μ.dist.mass x) = K * μ.dist.mass x := by
        rw [hK]; ring
      nlinarith [mul_nonneg hd0 hq0]
  have e1 : ∑ j ∈ Finset.univ.erase i, w j * jNormSq (μ.interactOp i j * h)
      = ∑ x : μ.dist.Supp,
        (∑ j ∈ Finset.univ.erase i, w j * (if μ.Interact i j x.1 then 1 else 0))
          * qNormSq (h x) := by
    simp only [jNormSq_interactOp_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ x : μ.dist.Supp, (if G x.1 then 0 else K * μ.dist.mass x)
      = K * μ.dist.prob (Finset.univ.filter fun x : μ.dist.Supp => ¬ G x.1) := by
    rw [FinDist.prob, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  rw [e1]
  calc _ ≤ ∑ x : μ.dist.Supp, (d * qNormSq (h x) + (if G x.1 then 0 else K * μ.dist.mass x)) :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = d * jNormSq h
          + K * μ.dist.prob (Finset.univ.filter fun x : μ.dist.Supp => ¬ G x.1) := by
        rw [Finset.sum_add_distrib, e2, ← Finset.mul_sum]
        rfl
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hb hK0
        rw [hK] at this ⊢
        linarith

/-- **CGZ (4.29)**: `‖[Dᵢ, H] g‖² ≤ (1+p)(pd)²‖Dᵢ g‖² + (1+p)p²d ⟨g, Hg⟩ + 16p²wmax²b ‖g‖∞²`. -/
private lemma jNormSq_comm_le (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j) {wmax : ℝ}
    (hW : ∑ j, w j ≤ wmax) (i : ι) (G : (ι → Bool) → Prop) [DecidablePred G] {b d : ℝ}
    (hb : μ.dist.prob (Finset.univ.filter fun x : μ.dist.Supp => ¬ G x.1) ≤ b)
    (hd : ∀ x : μ.dist.Supp, G x.1 →
      ∑ j ∈ Finset.univ.erase i, w j * (if μ.Interact i j x.1 then 1 else 0) ≤ d)
    (hd0 : 0 ≤ d) (hdW : d ≤ wmax) (g : JVec μ.dist.Supp A) :
    jNormSq ((μ.dist.condDiff i * μ.dist.varOp w - μ.dist.varOp w * μ.dist.condDiff i) * g)
      ≤ (1 + μ.p) * (μ.p * d) ^ 2 * jNormSq (μ.dist.condDiff i * g)
        + (1 + μ.p) * μ.p ^ 2 * d * (jInner g (μ.dist.varOp w * g)).re
        + 16 * μ.p ^ 2 * wmax ^ 2 * b * μ.dist.infNormSq g := by
  have hp0 := μ.p_pos
  have hp1 := μ.p_le_half
  have hI := μ.dist.infNormSq_nonneg g
  have hb0 : 0 ≤ b :=
    (Finset.sum_nonneg fun x _ => μ.dist.mass_nonneg x : 0 ≤ μ.dist.prob _).trans hb
  have hwmax : 0 ≤ wmax := (Finset.sum_nonneg fun j _ => hw j).trans hW
  set c := μ.p ^ 2 * (1 + μ.p) with hc
  have hc0 : 0 ≤ c := by positivity
  set S := ∑ j ∈ Finset.univ.erase i, w j * jNormSq (μ.diffComm i j * g)
  set T1 := ∑ j ∈ Finset.univ.erase i, w j * jNormSq (μ.interactOp i j * (μ.dist.condDiff i * g))
  set T2 := ∑ j ∈ Finset.univ.erase i, w j * jNormSq (μ.interactOp i j * (μ.dist.condDiff j * g))
  set E := (jInner g (μ.dist.varOp w * g)).re
  set X := jNormSq (μ.dist.condDiff i * g)
  have hA1 := μ.jNormSq_comm_le_sum w hw hW i G hb hd hd0 g
  have hA2 : S ≤ c * (T1 + T2) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j hj => ?_
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    have := mul_le_mul_of_nonneg_left (μ.jNormSq_diffComm_le hij g) (hw j)
    linarith
  have hA3 : T1 ≤ d * X + 4 * wmax * b * μ.dist.infNormSq g :=
    μ.sum_jNormSq_interactOp_condDiff_le w hw hW i G hb hd hd0 g
  have hA4 : T2 ≤ E := by
    calc T2 ≤ ∑ j ∈ Finset.univ.erase i, w j * jNormSq (μ.dist.condDiff j * g) :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (μ.jNormSq_interactOp_mul_le i j _) (hw j)
      _ ≤ ∑ j, w j * jNormSq (μ.dist.condDiff j * g) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun j _ _ => mul_nonneg (hw j) (jNormSq_nonneg _)
      _ = E := (μ.dist.jInner_varOp_mul w g).symm
  have hT : T1 + T2 ≤ d * X + 4 * wmax * b * μ.dist.infNormSq g + E := by linarith
  have h1 : d * S ≤ d * (c * (d * X + 4 * wmax * b * μ.dist.infNormSq g + E)) :=
    mul_le_mul_of_nonneg_left (hA2.trans (mul_le_mul_of_nonneg_left hT hc0)) hd0
  have hdp : d * (1 + μ.p) ≤ 3 / 2 * wmax := by nlinarith
  have h2 : d * c * (4 * wmax * b * μ.dist.infNormSq g)
      ≤ 6 * μ.p ^ 2 * wmax ^ 2 * b * μ.dist.infNormSq g := by
    have := mul_le_mul_of_nonneg_left hdp
      (by positivity : 0 ≤ 4 * μ.p ^ 2 * wmax * b * μ.dist.infNormSq g)
    rw [hc]
    nlinarith
  have h3 : 0 ≤ μ.p ^ 2 * wmax ^ 2 * b * μ.dist.infNormSq g := by positivity
  rw [hc] at h1 h2
  nlinarith

/-- **Lemma 4.6 (moving a difference through an averaging operator).** Let `H = ∑ⱼ wⱼ Dⱼ` with
`wⱼ ≥ 0` and `∑ⱼ wⱼ ≤ wmax`, fix a coordinate `i`, and let `G` be an event (it may depend on all
coordinates) failing with `μ`-probability at most `b`, such that
`∑_{j≠i} wⱼ Aᵢⱼ(x) ≤ d` at every support point `x` in `G`, where `0 ≤ d ≤ wmax` and
`pd ≤ 2/5`.  Then for `R ≥ 1`, `F = (I + H/R)⁻¹`, and joint vectors on every finite workspace,
`‖Dᵢ F f‖² ≤ 4‖F Dᵢ f‖² + (p/R)‖f‖² + (64 p² wmax² b / R²)‖f‖∞²`. -/
theorem lemma_4_6 (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j) {wmax : ℝ} (hW : ∑ j, w j ≤ wmax) (i : ι)
    (G : (ι → Bool) → Prop) [DecidablePred G] {b d R : ℝ}
    (hb : μ.dist.prob (Finset.univ.filter fun x : μ.dist.Supp => ¬ G x.1) ≤ b)
    (hd : ∀ x : μ.dist.Supp, G x.1 →
      ∑ j ∈ Finset.univ.erase i, w j * (if μ.Interact i j x.1 then 1 else 0) ≤ d)
    (hd0 : 0 ≤ d) (hdW : d ≤ wmax) (hpd : μ.p * d ≤ 2 / 5) (hR : 1 ≤ R)
    (f : JVec μ.dist.Supp A) :
    jNormSq (μ.dist.condDiff i * (resolvent R (μ.dist.varOp w) * f))
      ≤ 4 * jNormSq (resolvent R (μ.dist.varOp w) * (μ.dist.condDiff i * f))
        + μ.p / R * jNormSq f + 64 * μ.p ^ 2 * wmax ^ 2 * b / R ^ 2 * μ.dist.infNormSq f := by
  have hR0 : 0 < R := by linarith
  have hH := FinDist.varOp_posSemidef (ρ := μ.dist) hw
  have hp0 := μ.p_pos
  have hp1 := μ.p_le_half
  have hb0 : 0 ≤ b :=
    (Finset.sum_nonneg fun x _ => μ.dist.mass_nonneg x : 0 ≤ μ.dist.prob _).trans hb
  have hwmax : 0 ≤ wmax := (Finset.sum_nonneg fun j _ => hw j).trans hW
  set F := resolvent R (μ.dist.varOp w) with hF
  set Di := μ.dist.condDiff i with hDi
  set M := Di * μ.dist.varOp w - μ.dist.varOp w * Di with hM
  set r : ℝ := R⁻¹ with hr
  have hcomm := commutator_resolvent hR0 hH Di
  -- `Dᵢ F f = F Dᵢ f + [Dᵢ, F] f` with `[Dᵢ, F] = -R⁻¹ F [Dᵢ, H] F` (4.9)
  have hsplit : Di * (F * f) = F * (Di * f) + -(((r : ℝ) : ℂ) • (F * (M * (F * f)))) := by
    have e1 : Di * (F * f) = F * (Di * f) + (Di * F - F * Di) * f := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      abel
    rw [e1, hcomm, hM]
    congr 1
    simp only [Matrix.smul_mul, Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, smul_sub,
      neg_sub]
    rfl
  have hX : jNormSq (Di * (F * f))
      ≤ 2 * jNormSq (F * (Di * f)) + 2 * (r * r * jNormSq (F * (M * (F * f)))) := by
    have := jNormSq_add_le_two (F * (Di * f)) (-(((r : ℝ) : ℂ) • (F * (M * (F * f)))))
    rwa [← hsplit, jNormSq_neg', jNormSq_smul', Complex.normSq_ofReal] at this
  have hW1 : jNormSq (F * (M * (F * f))) ≤ jNormSq (M * (F * f)) :=
    FinDist.jNormSq_resolvent_mul_le hR0 hw (M * (F * f))
  -- (4.29) applied to `F f`
  have hV : jNormSq (M * (F * f))
      ≤ (1 + μ.p) * (μ.p * d) ^ 2 * jNormSq (Di * (F * f))
        + (1 + μ.p) * μ.p ^ 2 * d * (jInner (F * f) (μ.dist.varOp w * (F * f))).re
        + 16 * μ.p ^ 2 * wmax ^ 2 * b * μ.dist.infNormSq (F * f) :=
    μ.jNormSq_comm_le w hw hW i G hb hd hd0 hdW (F * f)
  have hE : (jInner (F * f) (μ.dist.varOp w * (F * f))).re ≤ R / 4 * jNormSq f :=
    FinDist.jInner_resolvent_varOp_le hR0 hw f
  have hI : μ.dist.infNormSq (F * f) ≤ μ.dist.infNormSq f :=
    FinDist.infNormSq_resolvent_mul_le hR0 hw f
  -- the arithmetic
  set X := jNormSq (Di * (F * f))
  set Y := jNormSq (F * (Di * f))
  set N := jNormSq f
  set I := μ.dist.infNormSq f
  set E := (jInner (F * f) (μ.dist.varOp w * (F * f))).re
  set α := (1 + μ.p) * (μ.p * d) ^ 2 with hα_def
  set β := (1 + μ.p) * μ.p ^ 2 * d with hβ_def
  set γ := 16 * μ.p ^ 2 * wmax ^ 2 * b with hγ_def
  have hX0 : 0 ≤ X := jNormSq_nonneg _
  have hN0 : 0 ≤ N := jNormSq_nonneg _
  have hI0 : 0 ≤ I := μ.dist.infNormSq_nonneg _
  have hr0 : 0 < r := inv_pos.mpr hR0
  have hr1 : r ≤ 1 := inv_le_one_of_one_le₀ hR
  have hrR : r * R = 1 := inv_mul_cancel₀ hR0.ne'
  have hpd0 : 0 ≤ μ.p * d := mul_nonneg hp0.le hd0
  have hα0 : 0 ≤ α := by positivity
  have hβ0 : 0 ≤ β := by positivity
  have hγ0 : 0 ≤ γ := by positivity
  have hα : r * r * α ≤ 1 / 4 := by
    have h1 : (μ.p * d) ^ 2 ≤ (2 / 5) ^ 2 := pow_le_pow_left₀ hpd0 hpd 2
    have h2 : α ≤ 3 / 2 * (2 / 5) ^ 2 :=
      mul_le_mul (by linarith) h1 (sq_nonneg _) (by norm_num)
    have h3 : r * r ≤ 1 := by nlinarith
    calc r * r * α ≤ 1 * α := mul_le_mul_of_nonneg_right h3 hα0
      _ ≤ 1 / 4 := by linarith
  have hβ : β ≤ 3 / 5 * μ.p := by
    have h1 : (1 + μ.p) * (μ.p * d) ≤ 3 / 2 * (2 / 5) :=
      mul_le_mul (by linarith) hpd hpd0 (by norm_num)
    have h2 : β = μ.p * ((1 + μ.p) * (μ.p * d)) := by rw [hβ_def]; ring
    rw [h2]
    nlinarith
  have hV' : jNormSq (M * (F * f)) ≤ α * X + β * (R / 4 * N) + γ * I := by
    have := mul_le_mul_of_nonneg_left hE hβ0
    have := mul_le_mul_of_nonneg_left hI hγ0
    linarith
  have hrr0 : 0 ≤ r * r := by positivity
  have k1 : r * r * jNormSq (F * (M * (F * f))) ≤ r * r * (α * X + β * (R / 4 * N) + γ * I) :=
    mul_le_mul_of_nonneg_left (hW1.trans hV') hrr0
  have k2 : r * r * (α * X) ≤ 1 / 4 * X := by
    have := mul_le_mul_of_nonneg_right hα hX0
    linarith [show r * r * (α * X) = r * r * α * X by ring]
  have k3 : r * r * (β * (R / 4 * N)) ≤ 3 / 20 * (r * μ.p * N) := by
    have e : r * r * (β * (R / 4 * N)) = (r * R) * (r * β * N) / 4 := by ring
    rw [e, hrR, one_mul]
    have := mul_le_mul_of_nonneg_left hβ (mul_nonneg hr0.le hN0)
    nlinarith
  have k4 : 0 ≤ r * μ.p * N := by positivity
  have key : X ≤ 4 * Y + r * μ.p * N + 4 * (r * r * (γ * I)) := by
    have e : r * r * (α * X + β * (R / 4 * N) + γ * I)
        = r * r * (α * X) + r * r * (β * (R / 4 * N)) + r * r * (γ * I) := by ring
    linarith
  have g1 : μ.p / R * N = r * μ.p * N := by rw [hr, div_eq_mul_inv]; ring
  have g2 : 64 * μ.p ^ 2 * wmax ^ 2 * b / R ^ 2 * I = 4 * (r * r * (γ * I)) := by
    rw [hr, hγ_def, div_eq_mul_inv, ← inv_pow]; ring
  rw [g1, g2]
  exact key

end CondBern

end QuantumQueryComplexity
