import QuantumQueryComplexity.Promise.Post
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Packet parity: hidden instructions cost `Ω(m·√L)`

The generic lower bound behind "parity programs give product lower bounds"
There are `m = |ρ|` **packets** of
`L` positions.  Packet `c` carries one **instruction letter** `a c b`, for a
hidden bit `b`, at a hidden position, and the blank letter `e` everywhere else.
The task is the **parity** of the hidden bits.  Then

`sqrt_mul_le_advPMOn_packetParity : m·√L/2 ≤ ADV±(parity on the packet promise)`

whenever the two instruction letters of each packet differ.

The certificate is the Kronecker sum of one all-ones bipartite block per
packet, `Γ = ∑_c (agree off c) ⊗ (opposite bits at c)`, weighted by
`w = 1/(2√L)`:

* the all-ones vector is an eigenvector with eigenvalue `m·L·w`
  (`packetΓ_mulVec_one`; each summand has constant row sum `L`);
* a query at position `(c₀, j)` kills every summand but `c₀` and, in that
  summand, keeps only the pairs one of whose hidden positions is `j`.  Split
  by which one: the part with `x`'s position at `j` has pairwise orthogonal
  rows, the other pairwise orthogonal columns, each of squared norm `≤ L·w²`,
  so the filtered norm is at most `2·w·√L = 1`
  (`packetΓ_hadamard_le_one`, through `l2_opNorm_le_sqrt_of_rows_orthogonal`).

`sqrt_mul_le_advPMOn_of_packetParity` is the form consumers use: any function
of the reading that determines the parity by a postprocessing inherits the
bound (`advPMOn_comp_le`).  The monoid instance — a parity program `∏_c a_c(b_c)`
read off by a Boolean map — and the `min{n, √(nm)}` bookkeeping are the
paper's business.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-! ## A norm bound for matrices with orthogonal rows -/

section Orthogonal

variable {n : Type} [Fintype n] [DecidableEq n]

/-- **Pairwise orthogonal rows**: `‖A‖ ≤ √t` when distinct rows are orthogonal
and every row has squared norm at most `t`.  (`A·Aᵀ` is diagonal.) -/
theorem l2_opNorm_le_sqrt_of_rows_orthogonal (A : Matrix n n ℝ) {t : ℝ} (ht : 0 ≤ t)
    (horth : ∀ x x', x ≠ x' → ∑ y, A x y * A x' y = 0)
    (hrow : ∀ x, ∑ y, A x y * A x y ≤ t) : ‖A‖ ≤ Real.sqrt t := by
  have hdiag : A * Aᵀ = Matrix.diagonal fun x => ∑ y, A x y * A x y := by
    ext x x'
    rw [Matrix.mul_apply, Matrix.diagonal_apply]
    split_ifs with h
    · subst h
      rfl
    · exact horth x x' h
  have hnorm : ‖A‖ * ‖A‖ ≤ t := by
    have h1 : ‖(Aᵀ)ᴴ * Aᵀ‖ = ‖Aᵀ‖ * ‖Aᵀ‖ := Matrix.l2_opNorm_conjTranspose_mul_self Aᵀ
    have hAT : ‖Aᵀ‖ = ‖A‖ := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose]
    have h2 : (Aᵀ)ᴴ = A := by
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
    rw [hAT, h2, hdiag, Matrix.l2_opNorm_diagonal] at h1
    rw [← h1]
    refine (pi_norm_le_iff_of_nonneg ht).mpr fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun y _ => mul_self_nonneg _)]
    exact hrow x
  have := Real.sqrt_le_sqrt hnorm
  rwa [Real.sqrt_mul_self (norm_nonneg _)] at this

/-- The column version: `‖A‖ ≤ √t` when distinct columns are orthogonal. -/
theorem l2_opNorm_le_sqrt_of_cols_orthogonal (A : Matrix n n ℝ) {t : ℝ} (ht : 0 ≤ t)
    (horth : ∀ y y', y ≠ y' → ∑ x, A x y * A x y' = 0)
    (hcol : ∀ y, ∑ x, A x y * A x y ≤ t) : ‖A‖ ≤ Real.sqrt t := by
  have h := l2_opNorm_le_sqrt_of_rows_orthogonal Aᵀ ht
    (fun y y' hne => by simpa [Matrix.transpose_apply] using horth y y' hne)
    (fun y => by simpa [Matrix.transpose_apply] using hcol y)
  rwa [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose] at h

end Orthogonal

/-! ## Packets -/

section Packets

variable {ρ : Type} [Fintype ρ] [DecidableEq ρ] {L : ℕ} {σ : Type} [Fintype σ] [DecidableEq σ]

/-- The reading of the packets: the instruction letter of the hidden bit at the
hidden position of each packet, the blank `e` elsewhere. -/
def packetRead (a : ρ → Bool → σ) (e : σ) (x : ρ → Bool × Fin L) : ρ × Fin L → σ :=
  fun p => if p.2 = (x p.1).2 then a p.1 (x p.1).1 else e

/-- The parity of the hidden bits. -/
def packetParity (x : ρ → Bool × Fin L) : Bool :=
  decide (Odd (Finset.univ.filter fun c => (x c).1 = true).card)

/-- `x` and `y` agree off packet `c` and carry opposite bits in it. -/
def PacketFlip (c : ρ) (x y : ρ → Bool × Fin L) : Prop :=
  (∀ c', c' ≠ c → x c' = y c') ∧ (x c).1 ≠ (y c).1

instance (c : ρ) (x y : ρ → Bool × Fin L) : Decidable (PacketFlip c x y) := by
  unfold PacketFlip
  infer_instance

lemma PacketFlip.symm {c : ρ} {x y : ρ → Bool × Fin L} (h : PacketFlip c x y) :
    PacketFlip c y x :=
  ⟨fun c' hc' => (h.1 c' hc').symm, h.2.symm⟩

lemma packetFlip_comm (c : ρ) (x y : ρ → Bool × Fin L) :
    PacketFlip c x y ↔ PacketFlip c y x :=
  ⟨PacketFlip.symm, PacketFlip.symm⟩

/-- A flip changes the parity. -/
lemma packetParity_ne_of_flip {c : ρ} {x y : ρ → Bool × Fin L} (h : PacketFlip c x y) :
    packetParity x ≠ packetParity y := by
  classical
  set S : (ρ → Bool × Fin L) → Finset ρ := fun z => Finset.univ.filter fun c' => (z c').1 = true
    with hS
  have hoff : ∀ c', c' ≠ c → ((x c').1 = true ↔ (y c').1 = true) := fun c' hc' => by
    rw [h.1 c' hc']
  have hcard : (S x).card = (S y).card + 1 ∨ (S y).card = (S x).card + 1 := by
    cases hx : (x c).1
    · have hy : (y c).1 = true := by
        cases hy : (y c).1
        · exact absurd (hx.trans hy.symm) h.2
        · rfl
      right
      have : S y = insert c (S x) := by
        ext c'
        by_cases hc' : c' = c
        · subst hc'
          simp [S, hy]
        · simp [S, hc', hoff c' hc']
      rw [this, Finset.card_insert_of_notMem (by simp [S, hx])]
    · have hy : (y c).1 = false := by
        cases hy : (y c).1
        · rfl
        · exact absurd (hx.trans hy.symm) h.2
      left
      have : S x = insert c (S y) := by
        ext c'
        by_cases hc' : c' = c
        · subst hc'
          simp [S, hx]
        · simp [S, hc', hoff c' hc']
      rw [this, Finset.card_insert_of_notMem (by simp [S, hy])]
  simp only [packetParity]
  rcases hcard with hc | hc
  · rw [show (Finset.univ.filter fun c' => (x c').1 = true) = S x from rfl,
      show (Finset.univ.filter fun c' => (y c').1 = true) = S y from rfl, hc]
    intro heq
    have := (decide_eq_decide.mp heq)
    rw [Nat.odd_add_one] at this
    exact this.mp (by tauto) |> fun h' => by tauto
  · rw [show (Finset.univ.filter fun c' => (x c').1 = true) = S x from rfl,
      show (Finset.univ.filter fun c' => (y c').1 = true) = S y from rfl, hc]
    intro heq
    have := (decide_eq_decide.mp heq)
    rw [Nat.odd_add_one] at this
    tauto

/-- The flips of `x` in packet `c` are the `L` relocations of the opposite bit. -/
lemma card_filter_packetFlip (c : ρ) (x : ρ → Bool × Fin L) :
    (Finset.univ.filter fun y => PacketFlip c x y).card = L := by
  classical
  have hinj : Function.Injective fun p : Fin L => Function.update x c (!(x c).1, p) := by
    intro p p' h
    have := congrFun h c
    simp only [Function.update_self, Prod.mk.injEq] at this
    exact this.2
  have hset : (Finset.univ.filter fun y => PacketFlip c x y)
      = Finset.univ.image fun p : Fin L => Function.update x c (!(x c).1, p) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hy
      refine ⟨(y c).2, ?_⟩
      funext c'
      by_cases hc' : c' = c
      · subst hc'
        rw [Function.update_self]
        refine Prod.ext ?_ rfl
        have hne := hy.2
        cases hx : (x c').1 <;> cases hy' : (y c').1 <;> simp_all
      · rw [Function.update_of_ne hc']
        exact hy.1 c' hc'
    · rintro ⟨p, rfl⟩
      refine ⟨fun c' hc' => (Function.update_of_ne hc' _ _).symm, ?_⟩
      rw [Function.update_self]
      cases (x c).1 <;> simp
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-! ## The adversary matrix -/

variable (ρ L)

/-- The Kronecker sum of the per-packet all-ones bipartite blocks, at weight
`w`. -/
def packetΓ (w : ℝ) : Matrix (ρ → Bool × Fin L) (ρ → Bool × Fin L) ℝ :=
  Matrix.of fun x y => ∑ c, if PacketFlip c x y then w else 0

variable {ρ L}

lemma packetΓ_apply (w : ℝ) (x y : ρ → Bool × Fin L) :
    packetΓ ρ L w x y = ∑ c, if PacketFlip c x y then w else 0 := rfl

lemma packetΓ_symm (w : ℝ) (x y : ρ → Bool × Fin L) : packetΓ ρ L w x y = packetΓ ρ L w y x := by
  simp only [packetΓ_apply, packetFlip_comm]

lemma packetΓ_isHermitian (w : ℝ) : (packetΓ ρ L w).IsHermitian :=
  Matrix.IsHermitian.ext fun x y => by rw [star_trivial, packetΓ_symm]

lemma packetΓ_apply_eq_zero (w : ℝ) {x y : ρ → Bool × Fin L}
    (h : packetParity x = packetParity y) : packetΓ ρ L w x y = 0 := by
  rw [packetΓ_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [if_neg]
  exact fun hf => packetParity_ne_of_flip hf h

/-- **The degree eigenvector**: every row sums to `m·L·w`. -/
lemma packetΓ_mulVec_one (w : ℝ) :
    packetΓ ρ L w *ᵥ (fun _ => (1 : ℝ))
      = ((Fintype.card ρ : ℝ) * L * w) • fun _ => (1 : ℝ) := by
  funext x
  simp only [Matrix.mulVec, dotProduct, packetΓ_apply, mul_one, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  have : ∀ c : ρ, (∑ y, if PacketFlip c x y then w else 0) = L * w := by
    intro c
    rw [← Finset.sum_filter, Finset.sum_const, card_filter_packetFlip, nsmul_eq_mul]
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

lemma one_fn_ne_zero' [Nonempty (ρ → Bool × Fin L)] :
    (fun _ : ρ → Bool × Fin L => (1 : ℝ)) ≠ 0 := by
  intro hh
  have := congrFun hh (Classical.arbitrary _)
  norm_num at this

lemma mul_le_norm_packetΓ (hL : 0 < L) {w : ℝ} (hw : 0 ≤ w) :
    (Fintype.card ρ : ℝ) * L * w ≤ ‖packetΓ ρ L w‖ := by
  have : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  have h := abs_eigenvalue_le_norm (packetΓ_mulVec_one (ρ := ρ) (L := L) w) one_fn_ne_zero'
  exact (le_abs_self _).trans h

/-! ## The query masks -/

variable (a : ρ → Bool → σ) (e : σ)

/-- Readings differ at `(c₀, j)` only if `j` is one of the two hidden positions. -/
lemma pos_eq_of_packetRead_ne {x y : ρ → Bool × Fin L} {c₀ : ρ} {j : Fin L}
    (h : packetRead a e x (c₀, j) ≠ packetRead a e y (c₀, j)) :
    j = (x c₀).2 ∨ j = (y c₀).2 := by
  by_contra hne
  push Not at hne
  apply h
  simp only [packetRead, if_neg hne.1, if_neg hne.2]

/-- Inputs that agree in packet `c₀` read alike throughout it. -/
lemma packetRead_eq_of_apply_eq {x y : ρ → Bool × Fin L} {c₀ : ρ} (h : x c₀ = y c₀)
    (j : Fin L) : packetRead a e x (c₀, j) = packetRead a e y (c₀, j) := by
  simp only [packetRead, h]

/-- Under the mask at `(c₀, j)` only the `c₀` summand survives. -/
lemma packetΓ_hadamard_apply (w : ℝ) (c₀ : ρ) (j : Fin L) (x y : ρ → Bool × Fin L) :
    (packetΓ ρ L w ⊙ advDOn (packetRead a e) (c₀, j)) x y
      = if PacketFlip c₀ x y ∧ packetRead a e x (c₀, j) ≠ packetRead a e y (c₀, j)
        then w else 0 := by
  rw [Matrix.hadamard_apply, advDOn_apply, packetΓ_apply]
  by_cases hread : packetRead a e x (c₀, j) = packetRead a e y (c₀, j)
  · rw [if_pos hread, mul_zero, if_neg (fun h => h.2 hread)]
  · rw [if_neg hread, mul_one]
    have hoff : ∀ c ∈ Finset.univ, c ≠ c₀ → (if PacketFlip c x y then w else 0) = 0 := by
      intro c _ hc
      rw [if_neg]
      intro hf
      exact hread (packetRead_eq_of_apply_eq a e (hf.1 c₀ (Ne.symm hc)) j)
    rw [Finset.sum_eq_single c₀ hoff (fun h => absurd (Finset.mem_univ c₀) h)]
    by_cases hf : PacketFlip c₀ x y
    · rw [if_pos hf, if_pos ⟨hf, hread⟩]
    · rw [if_neg hf, if_neg (fun h => hf h.1)]

/-- The masked matrix, restricted to the pairs whose *row* hides its letter at `j`. -/
def maskRow (w : ℝ) (c₀ : ρ) (j : Fin L) : Matrix (ρ → Bool × Fin L) (ρ → Bool × Fin L) ℝ :=
  Matrix.of fun x y => if (x c₀).2 = j then
    (packetΓ ρ L w ⊙ advDOn (packetRead a e) (c₀, j)) x y else 0

/-- ... and to the pairs whose row does not (so the *column* does). -/
def maskCol (w : ℝ) (c₀ : ρ) (j : Fin L) : Matrix (ρ → Bool × Fin L) (ρ → Bool × Fin L) ℝ :=
  Matrix.of fun x y => if (x c₀).2 = j then 0 else
    (packetΓ ρ L w ⊙ advDOn (packetRead a e) (c₀, j)) x y

lemma hadamard_eq_maskRow_add_maskCol (w : ℝ) (c₀ : ρ) (j : Fin L) :
    packetΓ ρ L w ⊙ advDOn (packetRead a e) (c₀, j)
      = maskRow a e w c₀ j + maskCol a e w c₀ j := by
  ext x y
  simp only [maskRow, maskCol, Matrix.add_apply, Matrix.of_apply]
  split_ifs <;> simp

/-- Two flips of `y` in packet `c₀` with the same hidden position coincide. -/
lemma eq_of_flip_flip {c₀ : ρ} {x x' y : ρ → Bool × Fin L}
    (hx : PacketFlip c₀ x y) (hx' : PacketFlip c₀ x' y) (hpos : (x c₀).2 = (x' c₀).2) :
    x = x' := by
  funext c
  by_cases hc : c = c₀
  · subst hc
    refine Prod.ext ?_ hpos
    have hne := hx.2
    have hne' := hx'.2
    cases h1 : (x c).1 <;> cases h2 : (x' c).1 <;> cases h3 : (y c).1 <;> simp_all
  · rw [hx.1 c hc, hx'.1 c hc]

lemma maskRow_rows_orthogonal (w : ℝ) (c₀ : ρ) (j : Fin L) {x x' : ρ → Bool × Fin L}
    (hne : x ≠ x') : ∑ y, maskRow a e w c₀ j x y * maskRow a e w c₀ j x' y = 0 := by
  refine Finset.sum_eq_zero fun y _ => ?_
  simp only [maskRow, Matrix.of_apply, packetΓ_hadamard_apply]
  split_ifs with h1 h2 h3 h4 <;> try simp
  exact absurd (eq_of_flip_flip h2.1 h4.1 (h1.trans h3.symm)) hne

lemma maskRow_row_le (w : ℝ) (c₀ : ρ) (j : Fin L) (x : ρ → Bool × Fin L) :
    ∑ y, maskRow a e w c₀ j x y * maskRow a e w c₀ j x y ≤ L * (w * w) := by
  calc ∑ y, maskRow a e w c₀ j x y * maskRow a e w c₀ j x y
      ≤ ∑ y, if PacketFlip c₀ x y then w * w else 0 := by
        refine Finset.sum_le_sum fun y _ => ?_
        simp only [maskRow, Matrix.of_apply, packetΓ_hadamard_apply]
        by_cases hf : PacketFlip c₀ x y
        · rw [if_pos hf]
          split_ifs <;> nlinarith [mul_self_nonneg w]
        · simp [hf]
    _ = L * (w * w) := by
        rw [← Finset.sum_filter, Finset.sum_const, card_filter_packetFlip, nsmul_eq_mul]

lemma maskCol_cols_orthogonal (w : ℝ) (c₀ : ρ) (j : Fin L) {y y' : ρ → Bool × Fin L}
    (hne : y ≠ y') : ∑ x, maskCol a e w c₀ j x y * maskCol a e w c₀ j x y' = 0 := by
  refine Finset.sum_eq_zero fun x _ => ?_
  simp only [maskCol, Matrix.of_apply, packetΓ_hadamard_apply]
  split_ifs with h1 h2 h3 <;> try simp
  · exfalso
    have hy : j = (y c₀).2 := by
      rcases pos_eq_of_packetRead_ne a e h2.2 with h | h
      · exact absurd h.symm h1
      · exact h
    have hy' : j = (y' c₀).2 := by
      rcases pos_eq_of_packetRead_ne a e h3.2 with h | h
      · exact absurd h.symm h1
      · exact h
    exact hne (eq_of_flip_flip h2.1.symm h3.1.symm (hy.symm.trans hy'))

lemma maskCol_col_le (w : ℝ) (c₀ : ρ) (j : Fin L) (y : ρ → Bool × Fin L) :
    ∑ x, maskCol a e w c₀ j x y * maskCol a e w c₀ j x y ≤ L * (w * w) := by
  calc ∑ x, maskCol a e w c₀ j x y * maskCol a e w c₀ j x y
      ≤ ∑ x, if PacketFlip c₀ y x then w * w else 0 := by
        refine Finset.sum_le_sum fun x _ => ?_
        simp only [maskCol, Matrix.of_apply, packetΓ_hadamard_apply, packetFlip_comm c₀ x y]
        by_cases hf : PacketFlip c₀ y x
        · rw [if_pos hf]
          split_ifs <;> nlinarith [mul_self_nonneg w]
        · simp [hf]
    _ = L * (w * w) := by
        rw [← Finset.sum_filter, Finset.sum_const, card_filter_packetFlip, nsmul_eq_mul]

/-- **The mask bound**: `‖Γ ⊙ D_{(c₀,j)}‖ ≤ 2·w·√L`. -/
lemma packetΓ_hadamard_le (w : ℝ) (hw : 0 ≤ w) (c₀ : ρ) (j : Fin L) :
    ‖packetΓ ρ L w ⊙ advDOn (packetRead a e) (c₀, j)‖ ≤ 2 * w * Real.sqrt L := by
  have hsq : Real.sqrt ((L : ℝ) * (w * w)) = w * Real.sqrt L := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_mul_self hw, mul_comm]
  have h1 : ‖maskRow a e w c₀ j‖ ≤ w * Real.sqrt L := by
    rw [← hsq]
    exact l2_opNorm_le_sqrt_of_rows_orthogonal _ (by positivity)
      (fun x x' hne => maskRow_rows_orthogonal a e w c₀ j hne)
      (maskRow_row_le a e w c₀ j)
  have h2 : ‖maskCol a e w c₀ j‖ ≤ w * Real.sqrt L := by
    rw [← hsq]
    exact l2_opNorm_le_sqrt_of_cols_orthogonal _ (by positivity)
      (fun y y' hne => maskCol_cols_orthogonal a e w c₀ j hne)
      (maskCol_col_le a e w c₀ j)
  rw [hadamard_eq_maskRow_add_maskCol]
  calc ‖maskRow a e w c₀ j + maskCol a e w c₀ j‖
      ≤ ‖maskRow a e w c₀ j‖ + ‖maskCol a e w c₀ j‖ := norm_add_le _ _
    _ ≤ w * Real.sqrt L + w * Real.sqrt L := add_le_add h1 h2
    _ = 2 * w * Real.sqrt L := by ring

/-! ## The certificate -/

/-- Distinct instruction letters make the parity a function of the reading. -/
lemma packetParity_det (ha : ∀ c, a c false ≠ a c true) {x y : ρ → Bool × Fin L}
    (h : packetRead a e x = packetRead a e y) : packetParity x = packetParity y := by
  have hbit : ∀ c, (x c).1 = (y c).1 := by
    intro c
    by_contra hne
    have h1 := congrFun h (c, (x c).2)
    have h2 := congrFun h (c, (y c).2)
    simp only [packetRead, if_true] at h1 h2
    have key : a c (x c).1 = a c (y c).1 := by
      by_cases hp : (x c).2 = (y c).2
      · rw [if_pos hp] at h1
        exact h1
      · rw [if_neg hp] at h1
        rw [if_neg (Ne.symm hp)] at h2
        exact h1.trans h2
    cases hx : (x c).1 <;> cases hy : (y c).1
    · exact hne (hx.trans hy.symm)
    · rw [hx, hy] at key
      exact ha c key
    · rw [hx, hy] at key
      exact ha c key.symm
    · exact hne (hx.trans hy.symm)
  have hset : (Finset.univ.filter fun c => (x c).1 = true)
      = Finset.univ.filter fun c => (y c).1 = true := by
    ext c
    simp [hbit c]
  unfold packetParity
  rw [hset]

/-- **Packet parity costs `m·√L/2`** (adversary form): for `m = |ρ|` packets of `L ≥ 1` positions with distinct
instruction letters, `m·√L/2 ≤ ADV±(parity on the packet promise)`. -/
theorem sqrt_mul_le_advPMOn_packetParity (hL : 0 < L) (ha : ∀ c, a c false ≠ a c true) :
    (Fintype.card ρ : ℝ) * Real.sqrt L / 2
      ≤ advPMOn (packetRead a e (L := L)) (packetParity (ρ := ρ) (L := L)) := by
  have hsqrt : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr (by exact_mod_cast hL)
  set w : ℝ := 1 / (2 * Real.sqrt L) with hw
  have hw0 : 0 ≤ w := by positivity
  have h1 : IsAdvMatrixOn (packetParity (ρ := ρ) (L := L)) (packetΓ ρ L w) :=
    ⟨packetΓ_isHermitian w, fun x y hf => packetΓ_apply_eq_zero w hf⟩
  have h2 : ∀ i, ‖packetΓ ρ L w ⊙ advDOn (packetRead a e) i‖ ≤ 1 := by
    rintro ⟨c₀, j⟩
    refine (packetΓ_hadamard_le a e w hw0 c₀ j).trans (le_of_eq ?_)
    rw [hw]
    field_simp
  have h3 := norm_div_le_advPMOn (fun x y hxy => packetParity_det a e ha hxy) h1 h2 one_pos
  rw [div_one] at h3
  have hL' : Real.sqrt L * Real.sqrt L = (L : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hdiv : (L : ℝ) / (2 * Real.sqrt L) = Real.sqrt L / 2 := by
    rw [div_eq_div_iff (by positivity) (by norm_num)]
    linear_combination (-2 : ℝ) * hL'
  have heq : (Fintype.card ρ : ℝ) * L * w = (Fintype.card ρ : ℝ) * Real.sqrt L / 2 := by
    rw [hw, mul_assoc, mul_one_div, hdiv]
    ring
  rw [← heq]
  exact (mul_le_norm_packetΓ hL hw0).trans h3

/-- **The consumer form**: any function of the reading that determines the
parity by a postprocessing `π` inherits the bound. -/
theorem sqrt_mul_le_advPMOn_of_packetParity (hL : 0 < L) (ha : ∀ c, a c false ≠ a c true)
    {O : Type} [DecidableEq O] {g : (ρ → Bool × Fin L) → O}
    (hdet : ∀ x y, packetRead a e x = packetRead a e y → g x = g y)
    (π : O → Bool) (hπ : ∀ x, π (g x) = packetParity x) :
    (Fintype.card ρ : ℝ) * Real.sqrt L / 2 ≤ advPMOn (packetRead a e) g := by
  refine (sqrt_mul_le_advPMOn_packetParity a e hL ha).trans ?_
  have h := advPMOn_comp_le hdet π
  have hfun : (fun x => π (g x)) = packetParity (ρ := ρ) (L := L) := funext hπ
  rwa [hfun] at h

end Packets

end QuantumQueryComplexity
