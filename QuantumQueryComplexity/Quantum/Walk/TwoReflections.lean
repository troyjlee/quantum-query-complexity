import QuantumQueryComplexity.Quantum.Walk.Gap
import QuantumQueryComplexity.Quantum.Amplitude.Geometry
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The product of two reflections, and its gap

Two orthonormal families `a b : V → (H → ℂ)` with Gram matrix `⟨a u, b v⟩ = D u v`, `D` Hermitian
with `D r = r` for a unit vector `r` (`r = √π`) and `‖D x‖ ≤ (1−δ)‖x‖` on `r^⊥`.  With
`A x = ∑ x u • a u`, `B y = ∑ y u • b u`, `Π_A = ∑ |a u⟩⟨a u|`, `Π_B`, and the walk
`W = (2Π_B − 1)(2Π_A − 1)`:

* `WalkFam.s_eq` — the stationary vector `s = A r = B r`, a unit vector fixed by `W`;
* `WalkFam.K` — the subspace `{A x + B y | x ⊥ r, y ⊥ r}`, orthogonal to `s`, **invariant under
  `W`**, and `A x = ⟨r, x⟩ s + (element of K)`;
* `WalkFam.gap` — for `v ∈ K`: `4δ‖v‖² ≤ ‖(1 − W)v‖²`, via `‖(1−W)v‖ = 2‖(Π_A − Π_B)v‖` and the
  Hermitian inequality of `Gap.lean`.

Nothing is claimed off `span s ⊕ K`: the orthogonal complement of `A + B` is fixed by `W`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {H V : Type} [Fintype H] [DecidableEq H] [Fintype V] [DecidableEq V]

/-- The linear combination of a family. -/
noncomputable def lin (f : V → (H → ℂ)) (x : V → ℂ) : H → ℂ := ∑ u, x u • f u

lemma lin_add (f : V → (H → ℂ)) (x y : V → ℂ) : lin f (x + y) = lin f x + lin f y := by
  simp only [lin, Pi.add_apply, add_smul, Finset.sum_add_distrib]

lemma lin_sub (f : V → (H → ℂ)) (x y : V → ℂ) : lin f (x - y) = lin f x - lin f y := by
  simp only [lin, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

lemma lin_smul (f : V → (H → ℂ)) (c : ℂ) (x : V → ℂ) : lin f (c • x) = c • lin f x := by
  simp only [lin, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

lemma lin_zero (f : V → (H → ℂ)) : lin f 0 = 0 := by simp [lin]

lemma lin_neg (f : V → (H → ℂ)) (x : V → ℂ) : lin f (-x) = -lin f x := by
  simp only [lin, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]

lemma qInner_lin_lin (f g : V → (H → ℂ)) (x y : V → ℂ) :
    qInner (lin f x) (lin g y) = ∑ u, ∑ v, star (x u) * y v * qInner (f u) (g v) := by
  rw [lin, lin, qInner_sum_left]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [qInner_smul_left, qInner_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [qInner_smul_right]; ring

lemma sum_mul_ite_one (c : V → ℂ) (u : V) : ∑ v, c v * (if u = v then (1 : ℂ) else 0) = c u := by
  simp [mul_ite, Finset.sum_ite_eq]

/-- The pair `(x, y)` as one vector. -/
def pairV (x y : V → ℂ) : Bool × V → ℂ := fun p => if p.1 then y p.2 else x p.2

lemma qInner_pairV (x y x' y' : V → ℂ) :
    qInner (pairV x y) (pairV x' y') = qInner x x' + qInner y y' := by
  simp only [qInner_def, Fintype.sum_prod_type, Fintype.sum_bool, pairV, if_true,
    Bool.false_eq_true, if_false]
  ring

lemma qNormSq_pairV (x y : V → ℂ) : qNormSq (pairV x y) = qNormSq x + qNormSq y := by
  have h := qInner_pairV x y x y
  rw [qInner_self, qInner_self, qInner_self] at h
  exact_mod_cast h

lemma pairV_add (x y x' y' : V → ℂ) : pairV x y + pairV x' y' = pairV (x + x') (y + y') := by
  funext p; simp only [Pi.add_apply, pairV]; split_ifs <;> rfl

lemma pairV_sub (x y x' y' : V → ℂ) : pairV x y - pairV x' y' = pairV (x - x') (y - y') := by
  funext p; simp only [Pi.sub_apply, pairV]; split_ifs <;> rfl

/-- **The data of a two-reflection walk.** -/
structure WalkFam (a b : V → (H → ℂ)) (D : Matrix V V ℂ) (r : V → ℂ) (δ : ℝ) : Prop where
  orthA : ∀ u v, qInner (a u) (a v) = if u = v then 1 else 0
  orthB : ∀ u v, qInner (b u) (b v) = if u = v then 1 else 0
  gram : ∀ u v, qInner (a u) (b v) = D u v
  herm : Dᴴ = D
  r_unit : IsQState r
  D_r : D *ᵥ r = r
  δ_pos : 0 < δ
  δ_le : δ ≤ 1
  gap_D : ∀ x, qInner r x = 0 → qNormSq (D *ᵥ x) ≤ (1 - δ) ^ 2 * qNormSq x

namespace WalkFam

variable {a b : V → (H → ℂ)} {D : Matrix V V ℂ} {r : V → ℂ} {δ : ℝ} (h : WalkFam a b D r δ)

include h

lemma qInner_A_A (x y : V → ℂ) : qInner (lin a x) (lin a y) = qInner x y := by
  rw [qInner_lin_lin]
  simp only [h.orthA]
  rw [qInner_def]
  refine Finset.sum_congr rfl fun u _ => ?_
  exact sum_mul_ite_one (fun v => star (x u) * y v) u

lemma qInner_B_B (x y : V → ℂ) : qInner (lin b x) (lin b y) = qInner x y := by
  rw [qInner_lin_lin]
  simp only [h.orthB]
  rw [qInner_def]
  refine Finset.sum_congr rfl fun u _ => ?_
  exact sum_mul_ite_one (fun v => star (x u) * y v) u

lemma qInner_A_B (x y : V → ℂ) : qInner (lin a x) (lin b y) = qInner x (D *ᵥ y) := by
  rw [qInner_lin_lin]
  simp only [h.gram]
  rw [qInner_def]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => by ring

lemma qInner_D_left (x y : V → ℂ) : qInner (D *ᵥ x) y = qInner x (D *ᵥ y) := by
  rw [qInner_mulVec_left, h.herm]

lemma qInner_B_A (x y : V → ℂ) : qInner (lin b x) (lin a y) = qInner x (D *ᵥ y) := by
  rw [← qInner_conj, h.qInner_A_B, ← h.qInner_D_left, qInner_conj]

omit h in
/-- The projector onto the span of `a`. -/
noncomputable def projA (a : V → (H → ℂ)) : Matrix H H ℂ := ∑ u, ketbra (a u)

omit h in
lemma projA_mulVec (f : V → (H → ℂ)) (ψ : H → ℂ) :
    projA f *ᵥ ψ = lin f fun u => qInner (f u) ψ := by
  rw [projA, Matrix.sum_mulVec, lin]
  exact Finset.sum_congr rfl fun u _ => ketbra_mulVec _ _

lemma projA_A (x : V → ℂ) : projA a *ᵥ lin a x = lin a x := by
  rw [projA_mulVec]
  congr 1; funext u
  rw [lin, qInner_sum_right]
  simp only [qInner_smul_right, h.orthA]
  exact sum_mul_ite_one x u

lemma projA_B (y : V → ℂ) : projA a *ᵥ lin b y = lin a (D *ᵥ y) := by
  rw [projA_mulVec]
  congr 1; funext u
  rw [lin, qInner_sum_right, Matrix.mulVec, dotProduct]
  simp only [qInner_smul_right, h.gram]
  exact Finset.sum_congr rfl fun v _ => mul_comm _ _

lemma projB_B (y : V → ℂ) : projA b *ᵥ lin b y = lin b y := by
  rw [projA_mulVec]
  congr 1; funext u
  rw [lin, qInner_sum_right]
  simp only [qInner_smul_right, h.orthB]
  exact sum_mul_ite_one y u

lemma projB_A (x : V → ℂ) : projA b *ᵥ lin a x = lin b (D *ᵥ x) := by
  rw [projA_mulVec]
  congr 1; funext u
  rw [lin, qInner_sum_right, Matrix.mulVec, dotProduct]
  simp only [qInner_smul_right]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← qInner_conj, h.gram]
  have : star (D v u) = D u v := by
    have := congrFun (congrFun h.herm u) v
    rwa [Matrix.conjTranspose_apply] at this
  rw [this, mul_comm]

omit h in
lemma isQProjector_projA {f : V → (H → ℂ)}
    (hf : ∀ u v, qInner (f u) (f v) = if u = v then 1 else 0) : IsQProjector (projA f) := by
  constructor
  · rw [projA, Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun u _ => (isQProjector_ketbra (by
      have := hf u u; rw [if_pos rfl, qInner_self] at this; exact_mod_cast this)).1
  · refine matrix_ext_of_mulVec_qBasis fun p => ?_
    rw [← Matrix.mulVec_mulVec, projA_mulVec, projA_mulVec]
    congr 1; funext u
    rw [lin, qInner_sum_right]
    simp only [qInner_smul_right, hf]
    exact sum_mul_ite_one _ u

/-- **The walk.** -/
noncomputable def walkOp (a b : V → (H → ℂ)) : Matrix H H ℂ := qRefl (projA b) * qRefl (projA a)

lemma walkOp_mem_unitaryGroup : walkOp a b ∈ Matrix.unitaryGroup H ℂ :=
  mul_mem_qUnitary (qRefl_mem_unitaryGroup (isQProjector_projA h.orthB))
    (qRefl_mem_unitaryGroup (isQProjector_projA h.orthA))

omit h in
lemma qRefl_mulVec' (P : Matrix H H ℂ) (ψ : H → ℂ) : qRefl P *ᵥ ψ = (2 : ℂ) • (P *ᵥ ψ) - ψ := by
  rw [qRefl, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- The walk on `A x + B y`. -/
theorem walkOp_AB (x y : V → ℂ) :
    walkOp a b *ᵥ (lin a x + lin b y)
      = lin a (-x - (2 : ℂ) • (D *ᵥ y))
        + lin b ((2 : ℂ) • (D *ᵥ x) + (4 : ℂ) • (D *ᵥ (D *ᵥ y)) - y) := by
  rw [walkOp, ← Matrix.mulVec_mulVec, qRefl_mulVec' (projA a), Matrix.mulVec_add, h.projA_A,
    h.projA_B]
  have e1 : (2 : ℂ) • (lin a x + lin a (D *ᵥ y)) - (lin a x + lin b y)
      = lin a (x + (2 : ℂ) • (D *ᵥ y)) - lin b y := by
    rw [lin_add, lin_smul]; module
  rw [e1, qRefl_mulVec' (projA b), Matrix.mulVec_sub, h.projB_A, h.projB_B]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, lin_add, lin_smul, lin_sub, lin_neg]
  module

/-! ## The stationary vector -/

/-- The stationary vector. -/
noncomputable def s (_ : WalkFam a b D r δ) : H → ℂ := lin a r

lemma s_eq_B : h.s = lin b r := by
  have hn : qNormSq (lin a r - lin b r) = 0 := by
    have e : lin a r - lin b r = lin a r + (-1 : ℂ) • lin b r := by rw [neg_one_smul, sub_eq_add_neg]
    rw [e, qNormSq_add, qNormSq_smul, qInner_smul_right, h.qInner_A_B, h.D_r, qInner_self,
      h.r_unit]
    have h1 : qNormSq (lin a r) = 1 := by
      have := h.qInner_A_A r r; rw [qInner_self, qInner_self, h.r_unit] at this; exact_mod_cast this
    have h2 : qNormSq (lin b r) = 1 := by
      have := h.qInner_B_B r r; rw [qInner_self, qInner_self, h.r_unit] at this; exact_mod_cast this
    rw [h1, h2]
    simp
    norm_num
  exact sub_eq_zero.mp (qNormSq_eq_zero_iff.mp hn)

lemma s_unit : IsQState h.s := by
  have := h.qInner_A_A r r
  rw [qInner_self, qInner_self, h.r_unit] at this
  exact_mod_cast this

lemma walkOp_s : walkOp a b *ᵥ h.s = h.s := by
  have e : h.s = lin a r + lin b 0 := by rw [lin_zero, add_zero]; rfl
  rw [e, h.walkOp_AB, Matrix.mulVec_zero, h.D_r]
  simp only [smul_zero, Matrix.mulVec_zero, sub_zero, add_zero]
  rw [lin_neg, lin_smul, lin_zero, add_zero]
  have hb : lin b r = lin a r := h.s_eq_B.symm
  rw [hb]
  module

/-! ## The invariant subspace -/

/-- `{A x + B y | x ⊥ r, y ⊥ r}`. -/
noncomputable def K (_ : WalkFam a b D r δ) : Submodule ℂ (H → ℂ) where
  carrier := {v | ∃ x y, qInner r x = 0 ∧ qInner r y = 0 ∧ v = lin a x + lin b y}
  zero_mem' := ⟨0, 0, by simp [qInner_def], by simp [qInner_def], by simp [lin_zero]⟩
  add_mem' := by
    rintro v w ⟨x, y, hx, hy, rfl⟩ ⟨x', y', hx', hy', rfl⟩
    refine ⟨x + x', y + y', ?_, ?_, ?_⟩
    · rw [qInner_add_right, hx, hx', add_zero]
    · rw [qInner_add_right, hy, hy', add_zero]
    · rw [lin_add, lin_add]; abel
  smul_mem' := by
    rintro c v ⟨x, y, hx, hy, rfl⟩
    refine ⟨c • x, c • y, ?_, ?_, ?_⟩
    · rw [qInner_smul_right, hx, mul_zero]
    · rw [qInner_smul_right, hy, mul_zero]
    · rw [lin_smul, lin_smul, smul_add]

lemma qInner_r_D {x : V → ℂ} (hx : qInner r x = 0) : qInner r (D *ᵥ x) = 0 := by
  rw [← h.qInner_D_left, h.D_r, hx]

/-- **`W` preserves `K`.** -/
theorem walkOp_mem_K {v : H → ℂ} (hv : v ∈ h.K) : walkOp a b *ᵥ v ∈ h.K := by
  obtain ⟨x, y, hx, hy, rfl⟩ := hv
  rw [h.walkOp_AB]
  refine ⟨_, _, ?_, ?_, rfl⟩
  · have e : -x - (2 : ℂ) • (D *ᵥ y) = (-1 : ℂ) • x + (-2 : ℂ) • (D *ᵥ y) := by module
    rw [e, qInner_add_right, qInner_smul_right, qInner_smul_right, hx, h.qInner_r_D hy]; simp
  · rw [qInner_sub_right, qInner_add_right, qInner_smul_right, qInner_smul_right,
      h.qInner_r_D hx, h.qInner_r_D (h.qInner_r_D hy), hy]; simp

/-- `s ⊥ K`. -/
theorem qInner_s_K {v : H → ℂ} (hv : v ∈ h.K) : qInner h.s v = 0 := by
  obtain ⟨x, y, hx, hy, rfl⟩ := hv
  rw [qInner_add_right, s, h.qInner_A_A, h.qInner_A_B, h.qInner_r_D hy, hx, add_zero]

/-- **The decomposition of `A x`**: `⟨r, x⟩ s + (element of K)`. -/
theorem A_decomp (x : V → ℂ) :
    lin a x = qInner r x • h.s + lin a (x - qInner r x • r)
    ∧ lin a (x - qInner r x • r) ∈ h.K := by
  refine ⟨?_, x - qInner r x • r, 0, ?_, by simp [qInner_def], by simp [lin_zero]⟩
  · rw [lin_sub, lin_smul]; simp only [s]; abel
  · rw [qInner_sub_right, qInner_smul_right, qInner_self, h.r_unit]; simp

/-! ## The gap -/

lemma qNormSq_A_sub_B (x y : V → ℂ) :
    qNormSq (lin a x - lin b y) = qNormSq x + qNormSq y - 2 * (qInner x (D *ᵥ y)).re := by
  have e : lin a x - lin b y = lin a x + (-1 : ℂ) • lin b y := by rw [neg_one_smul, sub_eq_add_neg]
  rw [e, qNormSq_add, qNormSq_smul, qInner_smul_right, h.qInner_A_B]
  have h1 : qNormSq (lin a x) = qNormSq x := by
    have := h.qInner_A_A x x; rw [qInner_self, qInner_self] at this; exact_mod_cast this
  have h2 : qNormSq (lin b y) = qNormSq y := by
    have := h.qInner_B_B y y; rw [qInner_self, qInner_self] at this; exact_mod_cast this
  rw [h1, h2]
  simp
  ring

lemma qNormSq_A_add_B (x y : V → ℂ) :
    qNormSq (lin a x + lin b y) = qNormSq x + qNormSq y + 2 * (qInner x (D *ᵥ y)).re := by
  rw [qNormSq_add, h.qInner_A_B]
  have h1 : qNormSq (lin a x) = qNormSq x := by
    have := h.qInner_A_A x x; rw [qInner_self, qInner_self] at this; exact_mod_cast this
  have h2 : qNormSq (lin b y) = qNormSq y := by
    have := h.qInner_B_B y y; rw [qInner_self, qInner_self] at this; exact_mod_cast this
  rw [h1, h2]

/-- `‖(1 − W)v‖ = 2‖(Π_A − Π_B)v‖`. -/
lemma qNormSq_one_sub_walkOp (v : H → ℂ) :
    qNormSq ((1 - walkOp a b) *ᵥ v)
      = 4 * qNormSq (projA a *ᵥ v - projA b *ᵥ v) := by
  have hB := qRefl_mem_unitaryGroup (isQProjector_projA h.orthB)
  have hBB : qRefl (projA b) * qRefl (projA b) = 1 := qRefl_mul_self (isQProjector_projA h.orthB)
  have e : (1 - walkOp a b) *ᵥ v = qRefl (projA b) *ᵥ ((qRefl (projA b) - qRefl (projA a)) *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, hBB, walkOp]
  rw [e, qNormSq_mulVec hB, Matrix.sub_mulVec, qRefl_mulVec', qRefl_mulVec']
  have e2 : (2 : ℂ) • (projA b *ᵥ v) - v - ((2 : ℂ) • (projA a *ᵥ v) - v)
      = (-2 : ℂ) • (projA a *ᵥ v - projA b *ᵥ v) := by module
  rw [e2, qNormSq_smul]
  norm_num [Complex.normSq_apply]

/-- **The gap on `K`**: `4δ‖v‖² ≤ ‖(1 − W)v‖²`. -/
theorem gap {v : H → ℂ} (hv : v ∈ h.K) : 4 * δ * qNormSq v ≤ qNormSq ((1 - walkOp a b) *ᵥ v) := by
  obtain ⟨x, y, hx, hy, rfl⟩ := hv
  rw [h.qNormSq_one_sub_walkOp, Matrix.mulVec_add, Matrix.mulVec_add, h.projA_A, h.projA_B,
    h.projB_A, h.projB_B, show lin a x + lin a (D *ᵥ y) - (lin b (D *ᵥ x) + lin b y)
      = lin a (x + D *ᵥ y) - lin b (D *ᵥ x + y) by rw [lin_add, lin_add], h.qNormSq_A_sub_B,
    h.qNormSq_A_add_B]
  -- the Hermitian inequality with `z₀ = (x, y)`, `z₁ = (D y, D x)`, `z₂ = (D²x, D²y)`
  have hlam : (1 - δ) ^ 2 ≤ 1 := by nlinarith [h.δ_pos, h.δ_le]
  have hDx := h.qInner_r_D hx
  have hDy := h.qInner_r_D hy
  have key := gap_ineq_aux hlam (pairV x y) (pairV (D *ᵥ y) (D *ᵥ x))
    (pairV (D *ᵥ (D *ᵥ x)) (D *ᵥ (D *ᵥ y)))
    (by
      rw [qInner_pairV, qNormSq_pairV, Complex.add_re, ← h.qInner_D_left x (D *ᵥ x),
        ← h.qInner_D_left y (D *ᵥ y), qInner_self, qInner_self, Complex.ofReal_re,
        Complex.ofReal_re, add_comm])
    (by
      rw [qNormSq_pairV, qNormSq_pairV]
      linarith [h.gap_D y hy, h.gap_D x hx])
    (by
      rw [pairV_add, pairV_add, qNormSq_pairV, qNormSq_pairV, ← Matrix.mulVec_add,
        ← Matrix.mulVec_add]
      have h1 := h.gap_D (y + D *ᵥ x) (by rw [qInner_add_right, hy, hDx, add_zero])
      have h2 := h.gap_D (x + D *ᵥ y) (by rw [qInner_add_right, hx, hDy, add_zero])
      linarith)
  rw [pairV_add, pairV_add, pairV_sub, qInner_pairV, qInner_pairV, Complex.add_re,
    Complex.add_re] at key
  -- rewrite the two sides
  have hsym2 : (qInner y (D *ᵥ x)).re = (qInner x (D *ᵥ y)).re := by
    rw [← h.qInner_D_left y x, ← qInner_conj, Complex.star_def, Complex.conj_re]
  have hL : (qInner x (x + D *ᵥ y)).re + (qInner y (y + D *ᵥ x)).re
      = qNormSq x + qNormSq y + 2 * (qInner x (D *ᵥ y)).re := by
    rw [qInner_add_right, qInner_add_right, qInner_self, qInner_self]
    simp only [Complex.add_re, Complex.ofReal_re]
    rw [hsym2]; ring
  have hsym : (qInner (D *ᵥ x + y) (D *ᵥ (x + D *ᵥ y))).re
      = (qInner (x + D *ᵥ y) (D *ᵥ (D *ᵥ x + y))).re := by
    rw [← h.qInner_D_left (D *ᵥ x + y) (x + D *ᵥ y), ← qInner_conj, Complex.star_def,
      Complex.conj_re]
  have hR : (qInner (x + D *ᵥ y) (x + D *ᵥ y - (D *ᵥ y + D *ᵥ (D *ᵥ x)))).re
        + (qInner (y + D *ᵥ x) (y + D *ᵥ x - (D *ᵥ x + D *ᵥ (D *ᵥ y)))).re
      = qNormSq (x + D *ᵥ y) + qNormSq (D *ᵥ x + y)
        - 2 * (qInner (x + D *ᵥ y) (D *ᵥ (D *ᵥ x + y))).re := by
    have e1 : x + D *ᵥ y - (D *ᵥ y + D *ᵥ (D *ᵥ x)) = (x + D *ᵥ y) - D *ᵥ (D *ᵥ x + y) := by
      rw [Matrix.mulVec_add]; abel
    have e2 : y + D *ᵥ x - (D *ᵥ x + D *ᵥ (D *ᵥ y)) = (D *ᵥ x + y) - D *ᵥ (x + D *ᵥ y) := by
      rw [Matrix.mulVec_add]; abel
    rw [e1, e2, show y + D *ᵥ x = D *ᵥ x + y by abel, qInner_sub_right, qInner_sub_right,
      qInner_self, qInner_self]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re]
    rw [hsym]; ring
  rw [hL, hR] at key
  have hδ : 4 * δ ≤ 4 * (1 - (1 - δ) ^ 2) := by nlinarith [h.δ_pos, h.δ_le]
  have hnn : 0 ≤ qNormSq x + qNormSq y + 2 * (qInner x (D *ᵥ y)).re := by
    rw [← h.qNormSq_A_add_B]; exact qNormSq_nonneg _
  nlinarith

end WalkFam

end QuantumQueryComplexity
