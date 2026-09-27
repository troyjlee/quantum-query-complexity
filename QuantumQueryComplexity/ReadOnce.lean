import QuantumQueryComplexity.WeightedDual
import QuantumQueryComplexity.Pad
set_option linter.style.header false

/-!
# Read-once formulas over `AND`/`OR` gates have adversary bound `√n`

A *two-sided certificate* `Cert f c` bundles a primal adversary witness of
norm `c` with unit masked norms together with a **one-dimensional** dual
solution of cost `c`.  By weak duality a certificate pins the value:
`Cert f c → HasAdvValue f c`.

Certificates are closed under everything a read-once formula needs:

* `certOrN`, `certAndN` — the gates themselves, value `√(fan-in)`;
* `Cert.not`, `Cert.flipAll`, `Cert.relabel` — relabelling;
* `Cert.pad` — adding dummy variables;
* `Cert.orNode`, `Cert.andNode` — a gate applied to certified sub-formulas,
  combining values as `√(∑ᵢ cᵢ²)`.

Keeping the dual one-dimensional throughout is what makes the node step work:
composing `Unit`-dimensional duals gives `Unit × Unit`, which reindexes back
to `Unit`, so a whole formula never needs dual-dimension bookkeeping.

`HasROCert f n` packages "`f` is computed by a read-once formula with `n`
leaves", and `HasROCert.hasAdvValue` concludes `ADV±(f) = √n`.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-! ## Two-sided certificates -/

/-- A primal witness of norm `c` with unit masked norms, together with a
one-dimensional dual solution of cost `c`. -/
structure Cert {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → Bool) (c : ℝ) where
  /-- The primal adversary matrix. -/
  Γ : Matrix (ι → Bool) (ι → Bool) ℝ
  /-- It is an adversary matrix for `f`. -/
  isAdv : IsAdvMatrix f Γ
  /-- Its masked norms are at most one. -/
  feas : ∀ i, ‖Γ ⊙ advD i‖ ≤ 1
  /-- Its norm is the certified value. -/
  norm_eq : ‖Γ‖ = c
  /-- The dual solution. -/
  P : DualPair Unit f
  /-- Its cost is the certified value. -/
  cost : P.IsCostLe c

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A certificate pins the adversary bound: weak duality closes the
sandwich. -/
theorem Cert.hasAdvValue {f : (ι → Bool) → Bool} {c : ℝ} (C : Cert f c)
    (hc : 0 ≤ c) : HasAdvValue f c :=
  hasAdvValue_of_le (C.norm_eq ▸ le_advPM C.isAdv C.feas)
    (advDual_le_of_dualPair C.P hc C.cost)

/-! ## The gates -/

/-- The `n`-bit `OR` gate is certified with value `√n`. -/
noncomputable def certOrN [Nonempty ι] :
    Cert (orN : (ι → Bool) → Bool) (Real.sqrt (Fintype.card ι : ℝ)) where
  Γ := starMatrix unitSet zeroVec
  isAdv := orN_isAdvMatrix
  feas := orN_feasible
  norm_eq := by
    have hne : (unitSet : Finset (ι → Bool)).Nonempty := by
      obtain ⟨i⟩ := ‹Nonempty ι›
      exact ⟨unitVec i, mem_unitSet.mpr ⟨i, rfl⟩⟩
    rw [norm_starMatrix zeroVec_notMem_unitSet hne, card_unitSet]
  P := orNDual
  cost := orNDual_isCostLe

/-- Negating the output preserves a certificate. -/
noncomputable def Cert.not {f : (ι → Bool) → Bool} {c : ℝ} (C : Cert f c) :
    Cert (fun x => !(f x)) c where
  Γ := C.Γ
  isAdv := isAdvMatrix_not.mpr C.isAdv
  feas := C.feas
  norm_eq := C.norm_eq
  P := C.P.notFun
  cost := ⟨C.cost.1, C.cost.2⟩

/-- Negating all input bits preserves a certificate. -/
noncomputable def Cert.negInputs {f : (ι → Bool) → Bool} {c : ℝ}
    (C : Cert f c) : Cert (fun x => f (_root_.QuantumQueryComplexity.flipAll x)) c where
  Γ := C.Γ.submatrix _root_.QuantumQueryComplexity.flipAll _root_.QuantumQueryComplexity.flipAll
  isAdv := by
    refine ⟨?_, fun x y hxy => ?_⟩
    · show (C.Γ.submatrix flipAll flipAll)ᴴ = _
      ext a b
      simp only [Matrix.conjTranspose_apply, Matrix.submatrix_apply,
        star_trivial]
      exact (isHermitian_apply_symm C.isAdv.isHermitian _ _).symm
    · exact C.isAdv.apply_eq_zero hxy
  feas := by
    intro i
    rw [submatrix_flipAll_hadamard, l2_opNorm_submatrix_equiv]
    exact C.feas i
  norm_eq := by rw [l2_opNorm_submatrix_equiv]; exact C.norm_eq
  P := C.P.compFlipAll
  cost := ⟨fun x => C.cost.1 (_root_.QuantumQueryComplexity.flipAll x),
    fun x => C.cost.2 (_root_.QuantumQueryComplexity.flipAll x)⟩

/-- The `n`-bit `AND` gate is certified with value `√n`. -/
noncomputable def certAndN [Nonempty ι] :
    Cert (andN : (ι → Bool) → Bool) (Real.sqrt (Fintype.card ι : ℝ)) := by
  rw [andN_eq]
  exact (certOrN (ι := ι)).negInputs.not

/-! ## Padding -/

/-- Adding dummy variables preserves a certificate. -/
noncomputable def Cert.pad {γ : Type} [Fintype γ] [DecidableEq γ]
    {f : (ι → Bool) → Bool} {c : ℝ} (hc : 0 ≤ c) (C : Cert f c) :
    Cert (padFun (γ := γ) f) c where
  Γ := padMatrix C.Γ
  isAdv := padMatrix_isAdvMatrix C.isAdv
  feas := by
    rintro (i | j)
    · rw [padMatrix_hadamard_inl, norm_padMatrix]
      exact C.feas i
    · rw [padMatrix_hadamard_inr, norm_zero]
      exact zero_le_one
  norm_eq := by rw [norm_padMatrix]; exact C.norm_eq
  P := C.P.pad
  cost := C.P.pad_isCostLe hc C.cost

/-! ## Relabelling the variables -/

section Relabel

variable {ι' : Type} [Fintype ι'] [DecidableEq ι']

/-- The bijection on inputs induced by a bijection of variables. -/
def relabelInput (e : ι' ≃ ι) : (ι' → Bool) ≃ (ι → Bool) where
  toFun x := fun i => x (e.symm i)
  invFun y := fun i' => y (e i')
  left_inv x := by funext i'; simp
  right_inv y := by funext i; simp

@[simp] lemma relabelInput_apply (e : ι' ≃ ι) (x : ι' → Bool) (i : ι) :
    relabelInput e x i = x (e.symm i) := rfl

/-- Relabelling the variables of a function along `e : ι' ≃ ι`. -/
def relabelFun (e : ι' ≃ ι) (f : (ι → Bool) → Bool) : (ι' → Bool) → Bool :=
  fun x => f (relabelInput e x)

lemma submatrix_relabel_hadamard (Γ : Matrix (ι → Bool) (ι → Bool) ℝ)
    (e : ι' ≃ ι) (i' : ι') :
    (Γ.submatrix (relabelInput e) (relabelInput e)) ⊙ advD i'
      = (Γ ⊙ advD (e i')).submatrix (relabelInput e) (relabelInput e) := by
  ext x y
  simp only [Matrix.hadamard_apply, Matrix.submatrix_apply, advD_apply,
    relabelInput_apply, Equiv.symm_apply_apply]

/-- Relabelling the variables preserves a certificate. -/
noncomputable def Cert.relabel {f : (ι → Bool) → Bool} {c : ℝ} (e : ι' ≃ ι)
    (C : Cert f c) : Cert (relabelFun e f) c where
  Γ := C.Γ.submatrix (relabelInput e) (relabelInput e)
  isAdv := by
    refine ⟨?_, fun x y hxy => ?_⟩
    · show (C.Γ.submatrix (relabelInput e) (relabelInput e))ᴴ = _
      ext a b
      simp only [Matrix.conjTranspose_apply, Matrix.submatrix_apply,
        star_trivial]
      exact (isHermitian_apply_symm C.isAdv.isHermitian _ _).symm
    · exact C.isAdv.apply_eq_zero hxy
  feas := by
    intro i'
    rw [submatrix_relabel_hadamard, l2_opNorm_submatrix_equiv]
    exact C.feas (e i')
  norm_eq := by rw [l2_opNorm_submatrix_equiv]; exact C.norm_eq
  P :=
    { u x i' k := C.P.u (relabelInput e x) (e i') k
      v x i' k := C.P.v (relabelInput e x) (e i') k
      constraint x y := by
        trans (if f (relabelInput e x) = f (relabelInput e y) then (0:ℝ)
          else 1)
        · rw [← C.P.constraint (relabelInput e x) (relabelInput e y)]
          exact Fintype.sum_equiv e _ _ fun i' => by
            simp only [relabelInput_apply, Equiv.symm_apply_apply]
        · rfl }
  cost := by
    constructor <;> intro x
    · refine le_trans (le_of_eq ?_) (C.cost.1 (relabelInput e x))
      exact Fintype.sum_equiv e _ _ fun i' => rfl
    · refine le_trans (le_of_eq ?_) (C.cost.2 (relabelInput e x))
      exact Fintype.sum_equiv e _ _ fun i' => rfl

end Relabel

/-! ## Composing a gate with certified sub-formulas -/

/-- `Unit × Unit ≃ Unit`, used to keep composed duals one-dimensional. -/
def unitProdEquiv : (Unit × Unit) ≃ Unit where
  toFun _ := ()
  invFun _ := ((), ())
  left_inv := by rintro ⟨⟨⟩, ⟨⟩⟩; rfl
  right_inv := by rintro ⟨⟩; rfl

section Node

variable {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α]
  [Fintype β] [DecidableEq β]

/-- The masked norm of a composed matrix, split at the outer coordinate. -/
lemma norm_compose_hadamard_le {g : α → (β → Bool) → Bool}
    {Γf : Matrix (α → Bool) (α → Bool) ℝ}
    {M : α → Matrix (β → Bool) (β → Bool) ℝ} (hf : Γf.IsHermitian)
    (hM : ∀ i, IsAdvMatrix (g i) (M i)) (p : α) (q : β) :
    ‖compose g Γf M ⊙ advD (p, q)‖
      ≤ ‖Γf ⊙ advD p‖ *
        (‖M p ⊙ advD q‖ * ∏ i ∈ Finset.univ.erase p, ‖M i‖) := by
  classical
  rw [compose_hadamard_advD g Γf M hM p q]
  have hshape : ∀ i, IsAdvMatrix (g i)
      (Function.update M p (M p ⊙ advD q) i) := by
    intro i
    by_cases hip : i = p
    · subst hip
      rw [Function.update_self]
      exact (hM i).hadamard_advD q
    · rw [Function.update_of_ne hip]
      exact hM i
  refine (norm_compose_le (hf.hadamard (advD_isHermitian p)) hshape).trans ?_
  have hprod : ∏ i, ‖Function.update M p (M p ⊙ advD q) i‖
      = ‖M p ⊙ advD q‖ * ∏ i ∈ Finset.univ.erase p, ‖M i‖ := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p), Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [hprod]

/-- **An `OR` gate applied to certified sub-formulas.** -/
noncomputable def Cert.orNode {g : α → (β → Bool) → Bool} {c : α → ℝ}
    (hc : ∀ i, 0 < c i) (C : ∀ i, Cert (g i) (c i)) :
    Cert (composeFunFam (orN : (α → Bool) → Bool) g) (orWVal c) := by
  classical
  set M : α → Matrix (β → Bool) (β → Bool) ℝ := fun i => (C i).Γ with hM
  have hMnorm : ∀ i, ‖M i‖ = c i := fun i => (C i).norm_eq
  have hMadv : ∀ i, IsAdvMatrix (g i) (M i) := fun i => (C i).isAdv
  have hD : 0 < ∏ i, c i := Finset.prod_pos fun i _ => hc i
  have hV : 0 < orWVal c := orWVal_pos c hc
  have hprodM : ∏ i, ‖M i‖ = ∏ i, c i :=
    Finset.prod_congr rfl fun i _ => hMnorm i
  have hVsq : 0 < ∑ i, c i * c i := by
    obtain ⟨i₀⟩ := ‹Nonempty α›
    exact Finset.sum_pos' (fun i _ => (mul_pos (hc i) (hc i)).le)
      ⟨i₀, Finset.mem_univ _, mul_pos (hc i₀) (hc i₀)⟩
  have hnorm : ‖compose g (orWStar c) M‖ = orWVal c * ∏ i, c i := by
    rw [norm_compose (orWStar_isHermitian c) hMadv, hprodM,
      norm_orWStar hVsq]
    rfl
  exact
  { Γ := (1 / ∏ i, c i) • compose g (orWStar c) M
    isAdv := (isAdvMatrix_compose (orWStar_isAdvMatrix c) hMadv).smul _
    feas := by
      rintro ⟨p, q⟩
      rw [Matrix.smul_hadamard, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      have hmask := norm_compose_hadamard_le (orWStar_isHermitian c) hMadv p q
      have herase : (∏ i ∈ Finset.univ.erase p, ‖M i‖) * c p = ∏ i, c i := by
        rw [Finset.prod_congr rfl fun i _ => hMnorm i, mul_comm]
        exact Finset.mul_prod_erase Finset.univ (fun i => c i)
          (Finset.mem_univ p)
      have hep : 0 < ∏ i ∈ Finset.univ.erase p, ‖M i‖ := by
        rw [Finset.prod_congr rfl fun i _ => hMnorm i]
        exact Finset.prod_pos fun i _ => hc i
      have hstep : ‖compose g (orWStar c) M ⊙ advD (p, q)‖ ≤ ∏ i, c i := by
        refine hmask.trans ?_
        rw [norm_orWStar_hadamard, abs_of_pos (hc p)]
        calc c p * (‖M p ⊙ advD q‖ * ∏ i ∈ Finset.univ.erase p, ‖M i‖)
            ≤ c p * (1 * ∏ i ∈ Finset.univ.erase p, ‖M i‖) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right ((C p).feas q) hep.le) (hc p).le
          _ = (∏ i ∈ Finset.univ.erase p, ‖M i‖) * c p := by ring
          _ = ∏ i, c i := herase
      calc 1 / (∏ i, c i) * ‖compose g (orWStar c) M ⊙ advD (p, q)‖
          ≤ 1 / (∏ i, c i) * ∏ i, c i :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = 1 := by field_simp
    norm_eq := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hnorm]
      field_simp
    P := ((orWDual hc).compose (fun i => (C i).P)).reindex unitProdEquiv
    cost := DualPair.reindex_isCostLe
      ((orWDual hc).compose_isWeightedCostLe (orWDual_isWeightedCostLe hc)
        (fun i => (C i).cost)) _ }

/-- **An `AND` gate applied to certified sub-formulas.** -/
noncomputable def Cert.andNode {g : α → (β → Bool) → Bool} {c : α → ℝ}
    (hc : ∀ i, 0 < c i) (C : ∀ i, Cert (g i) (c i)) :
    Cert (composeFunFam (andN : (α → Bool) → Bool) g) (orWVal c) := by
  rw [composeFunFam_andN_eq]
  exact (Cert.orNode hc fun i => (C i).not).not

end Node

/-! ## Read-once formulas -/

/-- `HasROCert f n` : `f` is computed by a read-once `AND`/`OR` formula with
`n` leaves — witnessed by a two-sided certificate of value `√n`. -/
def HasROCert {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → Bool) (n : ℕ) : Prop :=
  0 < n ∧ Nonempty (Cert f (Real.sqrt (n : ℝ)))

/-- **The read-once theorem**: `ADV±(f) = √n` for a read-once formula with
`n` leaves, certified on both sides. -/
theorem HasROCert.hasAdvValue {f : (ι → Bool) → Bool} {n : ℕ}
    (h : HasROCert f n) : HasAdvValue f (Real.sqrt (n : ℝ)) :=
  h.2.elim fun C => C.hasAdvValue (Real.sqrt_nonneg _)

/-- A single variable is a read-once formula with one leaf. -/
theorem hasROCert_var : HasROCert (orN : (Unit → Bool) → Bool) 1 :=
  ⟨Nat.one_pos, ⟨by
    have h : (Fintype.card Unit : ℝ) = (1 : ℕ) := by simp
    exact h ▸ certOrN⟩⟩

theorem HasROCert.pad {γ : Type} [Fintype γ] [DecidableEq γ]
    {f : (ι → Bool) → Bool} {n : ℕ} (h : HasROCert f n) :
    HasROCert (padFun (γ := γ) f) n :=
  ⟨h.1, h.2.elim fun C => ⟨C.pad (Real.sqrt_nonneg _)⟩⟩

theorem HasROCert.relabel {ι' : Type} [Fintype ι'] [DecidableEq ι']
    {f : (ι → Bool) → Bool} {n : ℕ} (e : ι' ≃ ι) (h : HasROCert f n) :
    HasROCert (relabelFun e f) n :=
  ⟨h.1, h.2.elim fun C => ⟨C.relabel e⟩⟩

section Nodes

variable {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α]
  [Fintype β] [DecidableEq β]

lemma orWVal_sqrt_nat {m : α → ℕ} (hm : ∀ i, 0 < m i) :
    orWVal (fun i => Real.sqrt (m i : ℝ))
      = Real.sqrt ((∑ i, m i : ℕ) : ℝ) := by
  rw [orWVal]
  congr 1
  push_cast
  exact Finset.sum_congr rfl fun i _ =>
    Real.mul_self_sqrt (Nat.cast_nonneg _)

/-- An `OR` gate over read-once sub-formulas is read-once, with the leaf
counts adding. -/
theorem HasROCert.orNode {g : α → (β → Bool) → Bool} {m : α → ℕ}
    (h : ∀ i, HasROCert (g i) (m i)) :
    HasROCert (composeFunFam (orN : (α → Bool) → Bool) g) (∑ i, m i) := by
  classical
  refine ⟨?_, ?_⟩
  · exact Finset.sum_pos (fun i _ => (h i).1) Finset.univ_nonempty
  · have hc : ∀ i, 0 < Real.sqrt (m i : ℝ) := fun i =>
      Real.sqrt_pos.mpr (by exact_mod_cast (h i).1)
    have C : ∀ i, Cert (g i) (Real.sqrt (m i : ℝ)) := fun i => (h i).2.some
    exact ⟨(orWVal_sqrt_nat (fun i => (h i).1)) ▸ Cert.orNode hc C⟩

/-- The same for an `AND` gate. -/
theorem HasROCert.andNode {g : α → (β → Bool) → Bool} {m : α → ℕ}
    (h : ∀ i, HasROCert (g i) (m i)) :
    HasROCert (composeFunFam (andN : (α → Bool) → Bool) g) (∑ i, m i) := by
  classical
  refine ⟨?_, ?_⟩
  · exact Finset.sum_pos (fun i _ => (h i).1) Finset.univ_nonempty
  · have hc : ∀ i, 0 < Real.sqrt (m i : ℝ) := fun i =>
      Real.sqrt_pos.mpr (by exact_mod_cast (h i).1)
    have C : ∀ i, Cert (g i) (Real.sqrt (m i : ℝ)) := fun i => (h i).2.some
    exact ⟨(orWVal_sqrt_nat (fun i => (h i).1)) ▸ Cert.andNode hc C⟩

end Nodes

/-! ## Example: a non-uniform read-once formula

`OR₂(x₀, AND₂(x₁, x₂))` — the two sub-formulas have *different* sizes (one
leaf and two leaves), which is exactly the case the padding and relabelling
machinery exists for.  Here we build it the easy way: an `OR` gate over two
sub-formulas both presented on the common variable type `Bool`, the first a
single variable padded with one dummy, the second an `AND₂` gate.
-/

section Example

/-- A single variable, padded to the two-element variable type
`Unit ⊕ Unit`: still one leaf. -/
theorem hasROCert_var_pad :
    HasROCert (padFun (ι₀ := Unit) (γ := Unit)
      (orN : (Unit → Bool) → Bool)) 1 :=
  hasROCert_var.pad

/-- `AND` on the two-element variable type `Unit ⊕ Unit`: two leaves. -/
theorem hasROCert_and2 :
    HasROCert (andN : ((Unit ⊕ Unit) → Bool) → Bool) 2 :=
  ⟨by norm_num, ⟨by
    have h : (Fintype.card (Unit ⊕ Unit) : ℝ) = ((2 : ℕ) : ℝ) := by simp
    exact h ▸ certAndN⟩⟩

/-- **`OR₂(x₀, AND₂(x₁, x₂))`**: an `OR` gate over sub-formulas of *different*
sizes (one leaf and two leaves), so the smaller one is padded.  Three leaves,
hence adversary bound `√3`. -/
theorem advPM_example {g : Bool → ((Unit ⊕ Unit) → Bool) → Bool}
    (h0 : g false = padFun (ι₀ := Unit) (γ := Unit) orN)
    (h1 : g true = andN) :
    advPM (composeFunFam (orN : (Bool → Bool) → Bool) g)
      = Real.sqrt ((3 : ℕ) : ℝ) := by
  have hsub : ∀ b : Bool, HasROCert (g b) (if b then 2 else 1) := by
    intro b
    cases b
    · rw [h0]
      exact hasROCert_var_pad
    · rw [h1]
      exact hasROCert_and2
  have h := HasROCert.orNode hsub
  have hsum : (∑ b : Bool, if b then 2 else 1) = 3 := by decide
  rw [hsum] at h
  exact h.hasAdvValue.1

end Example

end QuantumQueryComplexity
