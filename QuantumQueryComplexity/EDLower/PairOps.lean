import QuantumQueryComplexity.EDLower.Cells
set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The collision-pair operators and their Grams

The blocks of Belovs' adversary matrix carry, on the collision pair `(a, b)`,
one of four explicit pair-cell factors `σ → σ × σ → ℝ` (writing
`δ v u := [u = v]` and `q := card σ`):

    edF0 v (u,w) = q^{-1/2} · q⁻¹                       (the `F₀` part)
    edF1 v (u,w) = q^{-1/2} · (δ v u + δ v w − 2/q)     (the `F₁` part)
    edF  v (u,w) = q^{-1/2} · (δ v u + δ v w − 1/q)     (`F = F₀ + F₁`)
    edF' v (u,w) = q^{-1/2} · (δ v w − 1/q)             (mask at the first slot)
    edF''v (u,w) = q^{-1/2} · (δ v u − 1/q)             (mask at the second slot)

`edF` agrees with `edF'` off the diagonal of the first slot and with `edF''`
off the second — the entrywise fact behind the `Δ_i`-modification.

A *block term* is the square matrix on inputs with rows guarded by
`x a = x b`, the pair factor at `(a,b)`, and an `E₁/E₀` scheme pattern on
the remaining cells.  Its Gram against another block term factorizes
(`blockTerm_transpose_mul`): the collision value sums into the `q² × q²`
Gram `pairGram φ ψ` of the pair factors, and each remaining cell multiplies.
The `pairGram`s of the concrete factors are computed here entrywise; the
recognition of the resulting matrices as `schemeProd`s (possibly reindexed
by the coordinate transposition) is `QuantumQueryComplexity/EDLower/Gram.lean`'s job.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-! ## The pair-cell factors -/

/-- The `F₀` factor: constant `q^{-3/2}`. -/
noncomputable def edF0 (_ : σ) (_ : σ × σ) : ℝ :=
  (Real.sqrt (Fintype.card σ))⁻¹ * (Fintype.card σ : ℝ)⁻¹

/-- The `F₁` factor. -/
noncomputable def edF1 (v : σ) (s : σ × σ) : ℝ :=
  (Real.sqrt (Fintype.card σ))⁻¹ *
    ((if s.1 = v then (1 : ℝ) else 0) + (if s.2 = v then (1 : ℝ) else 0)
      - 2 * (Fintype.card σ : ℝ)⁻¹)

/-- The full collision factor `F = F₀ + F₁`. -/
noncomputable def edF (v : σ) (s : σ × σ) : ℝ :=
  (Real.sqrt (Fintype.card σ))⁻¹ *
    ((if s.1 = v then (1 : ℝ) else 0) + (if s.2 = v then (1 : ℝ) else 0)
      - (Fintype.card σ : ℝ)⁻¹)

/-- The `Δ`-modified factor when the queried cell is the *first* slot. -/
noncomputable def edF' (v : σ) (s : σ × σ) : ℝ :=
  (Real.sqrt (Fintype.card σ))⁻¹ *
    ((if s.2 = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹)

/-- The `Δ`-modified factor when the queried cell is the *second* slot. -/
noncomputable def edF'' (v : σ) (s : σ × σ) : ℝ :=
  (Real.sqrt (Fintype.card σ))⁻¹ *
    ((if s.1 = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹)

lemma edF0_add_edF1 (v : σ) (s : σ × σ) : edF0 v s + edF1 v s = edF v s := by
  rw [edF0, edF1, edF, ← mul_add]
  congr 1
  ring

/-- Off the diagonal of the first slot, `F` and `F'` agree. -/
lemma edF_eq_edF' {v u w : σ} (h : v ≠ u) : edF v (u, w) = edF' v (u, w) := by
  rw [edF, edF',
    if_neg (show ¬ ((u, w).1 = v) from fun hc => h hc.symm)]
  ring

/-- Off the diagonal of the second slot, `F` and `F''` agree. -/
lemma edF_eq_edF'' {v u w : σ} (h : v ≠ w) : edF v (u, w) = edF'' v (u, w) := by
  rw [edF, edF'',
    if_neg (show ¬ ((u, w).2 = v) from fun hc => h hc.symm)]
  ring

lemma cellE0_symm (u v : σ) : cellE0 u v = cellE0 v u := rfl

lemma cellE1_symm (u v : σ) : cellE1 u v = cellE1 v u := by
  rw [show cellE1 u v = (cellE1 (σ := σ))ᵀ v u from rfl, cellE1_transpose]

/-! ## Sums of shifted indicators -/

/-- The basic collision-value sum: two centred indicators contract to a
`cellE1` entry. -/
lemma sum_indicator_shift [Nonempty σ] (w w' : σ) :
    (∑ v : σ, ((if w = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹)
      * ((if w' = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹))
    = (if w = w' then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹ := by
  have hq : ((Fintype.card σ : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hexp : ∀ v : σ,
      ((if w = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹)
        * ((if w' = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹)
      = (if w = v then (1 : ℝ) else 0) * (if w' = v then (1 : ℝ) else 0)
        - (Fintype.card σ : ℝ)⁻¹ * (if w = v then (1 : ℝ) else 0)
        - (Fintype.card σ : ℝ)⁻¹ * (if w' = v then (1 : ℝ) else 0)
        + (Fintype.card σ : ℝ)⁻¹ * (Fintype.card σ : ℝ)⁻¹ := fun v => by ring
  rw [Finset.sum_congr rfl fun v _ => hexp v]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have h1 : (∑ v : σ, (if w = v then (1 : ℝ) else 0)
      * (if w' = v then (1 : ℝ) else 0))
      = if w = w' then 1 else 0 := by
    rw [Finset.sum_congr rfl fun v (_ : v ∈ Finset.univ) =>
      show (if w = v then (1 : ℝ) else 0) * (if w' = v then (1 : ℝ) else 0)
        = if w = v then (if w = w' then (1 : ℝ) else 0) else 0 from by
        by_cases h1 : w = v
        · rw [if_pos h1, one_mul, if_pos h1]
          by_cases h2 : w = w'
          · rw [if_pos (by rw [← h1, h2]), if_pos h2]
          · rw [if_neg (fun hc => h2 (by rw [h1, ← hc])), if_neg h2]
        · rw [if_neg h1, zero_mul, if_neg h1],
      Finset.sum_ite_eq Finset.univ w
        fun _ => if w = w' then (1 : ℝ) else 0,
      if_pos (Finset.mem_univ _)]
  have h2 : (∑ v : σ, (Fintype.card σ : ℝ)⁻¹
      * (if w = v then (1 : ℝ) else 0)) = (Fintype.card σ : ℝ)⁻¹ := by
    rw [← Finset.mul_sum,
      Finset.sum_ite_eq Finset.univ w fun _ => (1 : ℝ),
      if_pos (Finset.mem_univ _), mul_one]
  have h3 : (∑ v : σ, (Fintype.card σ : ℝ)⁻¹
      * (if w' = v then (1 : ℝ) else 0)) = (Fintype.card σ : ℝ)⁻¹ := by
    rw [← Finset.mul_sum,
      Finset.sum_ite_eq Finset.univ w' fun _ => (1 : ℝ),
      if_pos (Finset.mem_univ _), mul_one]
  have h4 : (∑ _v : σ, (Fintype.card σ : ℝ)⁻¹ * (Fintype.card σ : ℝ)⁻¹)
      = (Fintype.card σ : ℝ)⁻¹ := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [h1, h2, h3, h4]
  ring

/-- A single centred indicator sums to zero. -/
lemma sum_indicator_center [Nonempty σ] (w : σ) :
    (∑ v : σ, ((if w = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹)) = 0 := by
  have hq : ((Fintype.card σ : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Finset.sum_sub_distrib,
    Finset.sum_ite_eq Finset.univ w fun _ => (1 : ℝ),
    if_pos (Finset.mem_univ _), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_inv_cancel₀ hq]
  exact sub_self 1

/-! ## Splitting a full-cell product at the pair -/

lemma prod_univ_pair_compl {a b : ι} (hab : a ≠ b) (f : ι → ℝ) :
    (∏ c, f c) = f a * f b * ∏ c ∈ ({a, b} : Finset ι)ᶜ, f c := by
  have herase : (Finset.univ.erase a).erase b = ({a, b} : Finset ι)ᶜ := by
    ext c
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_compl,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hcb, hca⟩ (h | h)
      · exact hca h
      · exact hcb h
    · intro h
      exact ⟨fun hc => h (Or.inr hc), fun hc => h (Or.inl hc)⟩
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ a),
    ← Finset.mul_prod_erase (Finset.univ.erase a) f
      (Finset.mem_erase.mpr ⟨fun h => hab h.symm, Finset.mem_univ b⟩),
    herase, mul_assoc]

/-- **The collision-guarded Fubini**: summing a row over all inputs with a
collision at `(a, b)` factorizes into the collision-value sum times the
per-cell sums. -/
lemma sum_pair_guard {a b : ι} (hab : a ≠ b) (F : σ → ℝ) (g : ι → σ → ℝ) :
    (∑ x : ι → σ, (if x a = x b then (1 : ℝ) else 0) * F (x a)
        * ∏ c ∈ ({a, b} : Finset ι)ᶜ, g c (x c))
      = (∑ v, F v) * ∏ c ∈ ({a, b} : Finset ι)ᶜ, (∑ s, g c s) := by
  have hsplit : ∀ x : ι → σ,
      (if x a = x b then (1 : ℝ) else 0) * F (x a)
        * ∏ c ∈ ({a, b} : Finset ι)ᶜ, g c (x c)
      = ∑ v : σ, F v * ((if x a = v then (1 : ℝ) else 0)
          * ((if x b = v then (1 : ℝ) else 0)
            * ∏ c ∈ ({a, b} : Finset ι)ᶜ, g c (x c))) := by
    intro x
    rw [Finset.sum_congr rfl fun v (_ : v ∈ Finset.univ) =>
      show F v * ((if x a = v then (1 : ℝ) else 0)
          * ((if x b = v then (1 : ℝ) else 0)
            * ∏ c ∈ ({a, b} : Finset ι)ᶜ, g c (x c)))
        = if x a = v then (if x a = x b then (1 : ℝ) else 0) * F (x a)
            * ∏ c ∈ ({a, b} : Finset ι)ᶜ, g c (x c) else 0 from by
        by_cases h1 : x a = v
        · rw [if_pos h1, if_pos h1, ← h1]
          by_cases h2 : x b = x a
          · rw [if_pos h2, if_pos h2.symm]
            ring
          · rw [if_neg h2, if_neg fun hc => h2 hc.symm]
            ring
        · rw [if_neg h1, if_neg h1, zero_mul, mul_zero],
      Finset.sum_ite_eq Finset.univ (x a) _, if_pos (Finset.mem_univ _)]
  rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => hsplit x,
    Finset.sum_comm]
  have hinner : ∀ v : σ,
      (∑ x : ι → σ, F v * ((if x a = v then (1 : ℝ) else 0)
          * ((if x b = v then (1 : ℝ) else 0)
            * ∏ c ∈ ({a, b} : Finset ι)ᶜ, g c (x c))))
      = F v * ∏ c ∈ ({a, b} : Finset ι)ᶜ, (∑ s, g c s) := by
    intro v
    rw [← Finset.mul_sum]
    congr 1
    set H : ι → σ → ℝ := Function.update
      (Function.update g a fun s => if s = v then (1 : ℝ) else 0)
      b (fun s => if s = v then (1 : ℝ) else 0) with hH
    have hHa : H a = fun s => if s = v then (1 : ℝ) else 0 := by
      rw [hH, Function.update_of_ne hab, Function.update_self]
    have hHb : H b = fun s => if s = v then (1 : ℝ) else 0 := by
      rw [hH, Function.update_self]
    have hHc : ∀ c ∈ ({a, b} : Finset ι)ᶜ, H c = g c := by
      intro c hc
      have hc' := Finset.mem_compl.mp hc
      rw [hH,
        Function.update_of_ne (show c ≠ b from fun h => hc' (by
          rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b))),
        Function.update_of_ne (show c ≠ a from fun h => hc' (by
          rw [h]; exact Finset.mem_insert_self a {b}))]
    calc (∑ x : ι → σ, (if x a = v then (1 : ℝ) else 0)
          * ((if x b = v then (1 : ℝ) else 0)
            * ∏ c ∈ ({a, b} : Finset ι)ᶜ, g c (x c)))
        = ∑ x : ι → σ, ∏ c, H c (x c) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [prod_univ_pair_compl hab (fun c => H c (x c)),
            show H a (x a) = if x a = v then (1 : ℝ) else 0 from by
              rw [hHa],
            show H b (x b) = if x b = v then (1 : ℝ) else 0 from by
              rw [hHb],
            Finset.prod_congr rfl fun c hc =>
              show H c (x c) = g c (x c) from by rw [hHc c hc]]
          ring
      _ = ∏ c, ∑ s : σ, H c s := by
          rw [show (∑ x : ι → σ, ∏ c, H c (x c))
            = ∑ x ∈ Fintype.piFinset fun _ : ι => (Finset.univ : Finset σ),
              ∏ c, H c (x c) from by rw [Fintype.piFinset_univ]]
          exact Finset.sum_prod_piFinset Finset.univ H
      _ = ∏ c ∈ ({a, b} : Finset ι)ᶜ, (∑ s, g c s) := by
          rw [prod_univ_pair_compl hab (fun c => ∑ s, H c s),
            show (∑ s, H a s) = 1 from by
              rw [hHa, Finset.sum_ite_eq' Finset.univ v fun _ => (1 : ℝ),
                if_pos (Finset.mem_univ _)],
            show (∑ s, H b s) = 1 from by
              rw [hHb, Finset.sum_ite_eq' Finset.univ v fun _ => (1 : ℝ),
                if_pos (Finset.mem_univ _)],
            Finset.prod_congr rfl fun c hc =>
              show (∑ s, H c s) = ∑ s, g c s from by rw [hHc c hc]]
          ring
  rw [Finset.sum_congr rfl fun v (_ : v ∈ Finset.univ) => hinner v,
    ← Finset.sum_mul]

/-! ## Block terms and their Grams -/

/-- A block term: collision guard at `(a, b)`, pair factor `φ`, `E₁` on the
cells of `T` and `E₀` on the remaining cells. -/
noncomputable def blockTerm (a b : ι) (φ : σ → σ × σ → ℝ) (T : Finset ι) :
    Matrix (ι → σ) (ι → σ) ℝ :=
  Matrix.of fun x y =>
    (if x a = x b then (1 : ℝ) else 0) * φ (x a) (y a, y b)
      * ∏ c ∈ ({a, b} : Finset ι)ᶜ,
          (if c ∈ T then cellE1 (x c) (y c) else cellE0 (x c) (y c))

/-- The `q² × q²` Gram of two pair factors. -/
noncomputable def pairGram (φ ψ : σ → σ × σ → ℝ) :
    Matrix (σ × σ) (σ × σ) ℝ :=
  Matrix.of fun s t => ∑ v, φ v s * ψ v t

/-- **The Gram factorization**: the collision value contracts into
`pairGram`, and each remaining cell multiplies. -/
lemma blockTerm_transpose_mul {a b : ι} (hab : a ≠ b)
    (φ ψ : σ → σ × σ → ℝ) (T U : Finset ι) :
    (blockTerm a b φ T)ᵀ * blockTerm a b ψ U
      = Matrix.of fun y z => pairGram φ ψ (y a, y b) (z a, z b)
          * ∏ c ∈ ({a, b} : Finset ι)ᶜ,
              (((if c ∈ T then cellE1 else cellE0)
                * (if c ∈ U then cellE1 else cellE0) : Matrix σ σ ℝ)
                (y c) (z c)) := by
  ext y z
  simp only [Matrix.mul_apply, Matrix.transpose_apply, blockTerm,
    Matrix.of_apply]
  calc ∑ x : ι → σ,
        ((if x a = x b then (1 : ℝ) else 0) * φ (x a) (y a, y b)
          * ∏ c ∈ ({a, b} : Finset ι)ᶜ,
              (if c ∈ T then cellE1 (x c) (y c) else cellE0 (x c) (y c)))
        * ((if x a = x b then (1 : ℝ) else 0) * ψ (x a) (z a, z b)
          * ∏ c ∈ ({a, b} : Finset ι)ᶜ,
              (if c ∈ U then cellE1 (x c) (z c) else cellE0 (x c) (z c)))
      = ∑ x : ι → σ, (if x a = x b then (1 : ℝ) else 0)
          * (φ (x a) (y a, y b) * ψ (x a) (z a, z b))
          * ∏ c ∈ ({a, b} : Finset ι)ᶜ,
              ((if c ∈ T then cellE1 (x c) (y c) else cellE0 (x c) (y c))
                * (if c ∈ U then cellE1 (x c) (z c) else cellE0 (x c) (z c))) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.prod_mul_distrib]
        by_cases h : x a = x b
        · rw [if_pos h]
          ring
        · rw [if_neg h]
          ring
    _ = (∑ v, φ v (y a, y b) * ψ v (z a, z b))
          * ∏ c ∈ ({a, b} : Finset ι)ᶜ, (∑ s,
              (if c ∈ T then cellE1 s (y c) else cellE0 s (y c))
                * (if c ∈ U then cellE1 s (z c) else cellE0 s (z c))) :=
        sum_pair_guard hab (fun v => φ v (y a, y b) * ψ v (z a, z b))
          (fun c s => (if c ∈ T then cellE1 s (y c) else cellE0 s (y c))
            * (if c ∈ U then cellE1 s (z c) else cellE0 s (z c)))
    _ = pairGram φ ψ (y a, y b) (z a, z b)
          * ∏ c ∈ ({a, b} : Finset ι)ᶜ,
              (((if c ∈ T then cellE1 else cellE0)
                * (if c ∈ U then cellE1 else cellE0) : Matrix σ σ ℝ)
                (y c) (z c)) := by
        congr 1
        refine Finset.prod_congr rfl fun c _ => ?_
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun s _ => ?_
        by_cases hcT : c ∈ T <;> by_cases hcU : c ∈ U
        · rw [if_pos hcT, if_pos hcT, if_pos hcU, if_pos hcU,
            cellE1_symm s (y c)]
        · rw [if_pos hcT, if_pos hcT, if_neg hcU, if_neg hcU,
            cellE1_symm s (y c)]
        · rw [if_neg hcT, if_neg hcT, if_pos hcU, if_pos hcU,
            cellE0_symm s (y c)]
        · rw [if_neg hcT, if_neg hcT, if_neg hcU, if_neg hcU,
            cellE0_symm s (y c)]

/-! ## The concrete pair Grams -/

/-- `F₀` against `F₀`: the all-`E₀` tensor. -/
lemma pairGram_edF0_edF0 [Nonempty σ] :
    pairGram (edF0 (σ := σ)) edF0
      = Matrix.of fun s t => cellE0 s.1 t.1 * cellE0 s.2 t.2 := by
  ext s t
  have hq : (0 : ℝ) < (Fintype.card σ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  simp only [pairGram, Matrix.of_apply, edF0, cellE0]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [show (Real.sqrt (Fintype.card σ))⁻¹ * (Fintype.card σ : ℝ)⁻¹
      * ((Real.sqrt (Fintype.card σ))⁻¹ * (Fintype.card σ : ℝ)⁻¹)
      = ((Real.sqrt (Fintype.card σ) * Real.sqrt (Fintype.card σ)))⁻¹
        * ((Fintype.card σ : ℝ)⁻¹ * (Fintype.card σ : ℝ)⁻¹) from by
    rw [mul_inv]
    ring,
    Real.mul_self_sqrt hq.le]
  field_simp

/-- `F₀` against `F₁`: zero (the two parts are orthogonal). -/
lemma pairGram_edF0_edF1 [Nonempty σ] :
    pairGram (edF0 (σ := σ)) edF1 = 0 := by
  ext s t
  simp only [pairGram, Matrix.of_apply, edF0, edF1, Matrix.zero_apply]
  rw [Finset.sum_congr rfl fun v (_ : v ∈ Finset.univ) => show
      (Real.sqrt (Fintype.card σ))⁻¹ * (Fintype.card σ : ℝ)⁻¹
        * ((Real.sqrt (Fintype.card σ))⁻¹
          * ((if t.1 = v then (1 : ℝ) else 0) + (if t.2 = v then (1 : ℝ) else 0)
            - 2 * (Fintype.card σ : ℝ)⁻¹))
      = ((Real.sqrt (Fintype.card σ))⁻¹ * (Fintype.card σ : ℝ)⁻¹
          * (Real.sqrt (Fintype.card σ))⁻¹)
        * (((if t.1 = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹)
          + ((if t.2 = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹)) from by
    ring,
    ← Finset.mul_sum, Finset.sum_add_distrib,
    sum_indicator_center t.1, sum_indicator_center t.2]
  ring

/-- `F'` against `F'`: the `E₀ ⊗ E₁` tensor. -/
lemma pairGram_edF'_edF' [Nonempty σ] :
    pairGram (edF' (σ := σ)) edF'
      = Matrix.of fun s t => cellE0 s.1 t.1 * cellE1 s.2 t.2 := by
  ext s t
  have hq : (0 : ℝ) < (Fintype.card σ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  simp only [pairGram, Matrix.of_apply, edF', cellE0, cellE1]
  rw [Finset.sum_congr rfl fun v (_ : v ∈ Finset.univ) => show
      (Real.sqrt (Fintype.card σ))⁻¹
          * ((if s.2 = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹)
        * ((Real.sqrt (Fintype.card σ))⁻¹
          * ((if t.2 = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹))
      = ((Real.sqrt (Fintype.card σ))⁻¹ * (Real.sqrt (Fintype.card σ))⁻¹)
        * (((if s.2 = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹)
          * ((if t.2 = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹)) from by
    ring,
    ← Finset.mul_sum, sum_indicator_shift s.2 t.2, ← mul_inv,
    Real.mul_self_sqrt hq.le]

/-- `F''` against `F''`: the `E₁ ⊗ E₀` tensor. -/
lemma pairGram_edF''_edF'' [Nonempty σ] :
    pairGram (edF'' (σ := σ)) edF''
      = Matrix.of fun s t => cellE1 s.1 t.1 * cellE0 s.2 t.2 := by
  ext s t
  have hq : (0 : ℝ) < (Fintype.card σ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  simp only [pairGram, Matrix.of_apply, edF'', cellE0, cellE1]
  rw [Finset.sum_congr rfl fun v (_ : v ∈ Finset.univ) => show
      (Real.sqrt (Fintype.card σ))⁻¹
          * ((if s.1 = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹)
        * ((Real.sqrt (Fintype.card σ))⁻¹
          * ((if t.1 = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹))
      = ((Real.sqrt (Fintype.card σ))⁻¹ * (Real.sqrt (Fintype.card σ))⁻¹)
        * (((if s.1 = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹)
          * ((if t.1 = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹)) from by
    ring,
    ← Finset.mul_sum, sum_indicator_shift s.1 t.1, ← mul_inv,
    Real.mul_self_sqrt hq.le]
  ring

/-- `F₁` against `F₁`: the two diagonal tensors plus the two swap couplings. -/
lemma pairGram_edF1_edF1 [Nonempty σ] :
    pairGram (edF1 (σ := σ)) edF1
      = Matrix.of fun s t =>
          cellE1 s.1 t.1 * cellE0 s.2 t.2 + cellE0 s.1 t.1 * cellE1 s.2 t.2
          + (cellE1 s.1 t.2 * cellE0 s.2 t.1 + cellE1 s.2 t.1 * cellE0 s.1 t.2) := by
  ext s t
  have hq : (0 : ℝ) < (Fintype.card σ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  simp only [pairGram, Matrix.of_apply, edF1, cellE0, cellE1]
  rw [Finset.sum_congr rfl fun v (_ : v ∈ Finset.univ) => show
      (Real.sqrt (Fintype.card σ))⁻¹
          * ((if s.1 = v then (1 : ℝ) else 0) + (if s.2 = v then (1 : ℝ) else 0)
            - 2 * (Fintype.card σ : ℝ)⁻¹)
        * ((Real.sqrt (Fintype.card σ))⁻¹
          * ((if t.1 = v then (1 : ℝ) else 0) + (if t.2 = v then (1 : ℝ) else 0)
            - 2 * (Fintype.card σ : ℝ)⁻¹))
      = ((Real.sqrt (Fintype.card σ))⁻¹ * (Real.sqrt (Fintype.card σ))⁻¹)
        * ((((if s.1 = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹)
              * ((if t.1 = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹)
            + ((if s.1 = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹)
              * ((if t.2 = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹))
          + (((if s.2 = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹)
              * ((if t.1 = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹)
            + ((if s.2 = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹)
              * ((if t.2 = v then (1 : ℝ) else 0) - (Fintype.card σ : ℝ)⁻¹))) from by
    ring,
    ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, sum_indicator_shift s.1 t.1,
    sum_indicator_shift s.1 t.2, sum_indicator_shift s.2 t.1,
    sum_indicator_shift s.2 t.2, ← mul_inv, Real.mul_self_sqrt hq.le]
  ring

end QuantumQueryComplexity
