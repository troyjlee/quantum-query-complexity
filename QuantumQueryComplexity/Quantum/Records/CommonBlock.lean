import QuantumQueryComplexity.Quantum.Records.Interaction
import QuantumQueryComplexity.Quantum.Records.SumProjections

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# A common block of coordinates: Lemma 4.5

For a block `B` of coordinates, `L_B = ∑_{i∈B} Dᵢ` (`CondBern.blockOp`) and
`F_B = (I + L_B/R)⁻¹`.  If each coordinate of `B` interacts with at most `d` others of `B`
(`N_{i,B}(x) ≤ d`, `CondBern.blockInteract`) wherever a good event `G_B` holds, and `G_B` depends
only on the coordinates outside `B` and fails with probability at most `b`, then
`∑_{i∈B} ⟨Dᵢ f, F_B Dᵢ f⟩ ≤ 3R‖f‖² + |B| b ‖f‖∞²` (Lemma 4.5 of Cornelissen–Gilani–Zhou).

## Proof route

Where the paper conditions on each outside assignment and re-applies Lemma 4.3 to the
conditional distribution on `B`, we use the diagonal projection `P_G` onto the inputs satisfying
`G_B`.  Since `G_B` depends only on coordinates outside `B`, `P_G` commutes with every `Dᵢ`
(`i ∈ B`), with `L_B` and with `F_B`.  On the range of `P_G`, Lemma 4.3 for `μ` itself gives
`L_B² ≥ (1 − pd) L_B` and `∑_{i∈B} ‖[Dᵢ, L_B] g‖² ≤ 2(1 + p)(pd)² ⟨g, L_B g⟩`, and Lemma 4.4 applied
to the projections `Dᵢ P_G` gives the bound `3R‖P_G f‖²`.  The complementary part is at most
`∑_{i∈B} ‖Dᵢ P_G^c f‖² ≤ |B| ‖P_G^c f‖² ≤ |B| b ‖f‖∞²`.  This changes the proof, not the
statement.

## Main results

* `CondBern.lemma_4_5` — Lemma 4.5, on every finite workspace.
-/

namespace QuantumQueryComplexity

open scoped Matrix MatrixOrder ComplexOrder
open Matrix

variable {ι A : Type} [Fintype ι] [DecidableEq ι] [Fintype A]

/-! ## Matrix helpers -/

namespace CommonBlockAux

variable {n : Type} [Fintype n] [DecidableEq n]

private lemma smul_le_smul_real {c : ℝ} (hc : 0 ≤ c) {M N : Matrix n n ℂ} (h : M ≤ N) :
    (c : ℂ) • M ≤ (c : ℂ) • N := by
  rw [le_iff] at h ⊢
  rw [← smul_sub]
  exact h.smul (Complex.zero_le_real.mpr hc)

private lemma smul_nonneg_real {c : ℝ} (hc : 0 ≤ c) {M : Matrix n n ℂ} (h : 0 ≤ M) :
    0 ≤ (c : ℂ) • M := by
  simpa using smul_le_smul_real hc h

private lemma nonneg_of_add_self {M : Matrix n n ℂ} (h : 0 ≤ M + M) : 0 ≤ M := by
  have e : M = ((1 / 2 : ℝ) : ℂ) • (M + M) := by
    rw [← two_smul ℂ M, smul_smul]; norm_num
  rw [e]; exact smul_nonneg_real (by norm_num) h

/-- A nonnegative matrix commuting with a Hermitian projection stays nonnegative after
multiplication by the projection. -/
private lemma mul_proj_nonneg {M P : Matrix n n ℂ} (hM : 0 ≤ M) (hc : Commute M P)
    (hPh : Pᴴ = P) (hPP : P * P = P) : 0 ≤ M * P := by
  have e : M * P = star P * M * P := by
    rw [star_eq_conjTranspose, hPh, ← hc.eq, mul_assoc, hPP]
  rw [e]
  exact star_left_conjugate_nonneg hM P

private lemma diagonal_ofReal_le {u v : n → ℝ} (h : ∀ x, u x ≤ v x) :
    diagonal (fun x => (u x : ℂ)) ≤ diagonal (fun x => (v x : ℂ)) := by
  rw [le_iff, diagonal_sub, posSemidef_diagonal_iff]
  intro x
  rw [← Complex.ofReal_sub]
  exact Complex.zero_le_real.mpr (sub_nonneg.mpr (h x))

/-- **Weighted Cauchy–Schwarz.** If commuting Hermitian projections `aⱼ` satisfy `aⱼ Wⱼ = Wⱼ`
and `∑ⱼ aⱼ ≤ c`, then `(∑ⱼ Wⱼ)†(∑ⱼ Wⱼ) ≤ c ∑ⱼ Wⱼ†Wⱼ`. -/
private lemma sq_sum_le_of_weights {κ : Type} (s : Finset κ) (a W : κ → Matrix n n ℂ) (c : ℝ)
    (ha : ∀ j ∈ s, (a j)ᴴ = a j) (haa : ∀ j ∈ s, a j * a j = a j)
    (hac : ∀ j ∈ s, ∀ l ∈ s, a j * a l = a l * a j)
    (haW : ∀ j ∈ s, a j * W j = W j)
    (hN : ∑ j ∈ s, a j ≤ (c : ℂ) • 1) :
    (∑ j ∈ s, W j)ᴴ * (∑ j ∈ s, W j) ≤ (c : ℂ) • ∑ j ∈ s, (W j)ᴴ * W j := by
  have hWa : ∀ j ∈ s, (W j)ᴴ * a j = (W j)ᴴ := by
    intro j hj
    conv_rhs => rw [← haW j hj]
    rw [conjTranspose_mul, ha j hj]
  have key : ∀ j ∈ s, ∀ l ∈ s,
      (a l * W j - a j * W l)ᴴ * (a l * W j - a j * W l)
        = ((W j)ᴴ * a l * W j + (W l)ᴴ * a j * W l) - ((W j)ᴴ * W l + (W l)ᴴ * W j) := by
    intro j hj l hl
    rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, ha j hj, ha l hl]
    simp only [sub_mul, mul_sub]
    have t1 : (W j)ᴴ * a l * (a l * W j) = (W j)ᴴ * a l * W j := by
      rw [mul_assoc, ← mul_assoc (a l), haa l hl, ← mul_assoc]
    have t2 : (W j)ᴴ * a l * (a j * W l) = (W j)ᴴ * W l := by
      rw [mul_assoc, ← mul_assoc (a l), hac l hl j hj, mul_assoc, haW l hl, ← mul_assoc,
        hWa j hj]
    have t3 : (W l)ᴴ * a j * (a l * W j) = (W l)ᴴ * W j := by
      rw [mul_assoc, ← mul_assoc (a j), hac j hj l hl, mul_assoc, haW j hj, ← mul_assoc,
        hWa l hl]
    have t4 : (W l)ᴴ * a j * (a j * W l) = (W l)ᴴ * a j * W l := by
      rw [mul_assoc, ← mul_assoc (a j), haa j hj, ← mul_assoc]
    rw [t1, t2, t3, t4]; abel
  set X1 := ∑ j ∈ s, ∑ l ∈ s, (W j)ᴴ * a l * W j
  set X2 := ∑ j ∈ s, ∑ l ∈ s, (W j)ᴴ * W l
  have e1 : ∑ j ∈ s, ∑ l ∈ s, (W l)ᴴ * a j * W l = X1 := Finset.sum_comm
  have e2 : ∑ j ∈ s, ∑ l ∈ s, (W l)ᴴ * W j = X2 := Finset.sum_comm
  have e3 : ∑ j ∈ s, (W j)ᴴ * (∑ l ∈ s, a l) * W j = X1 := by
    simp only [X1, Finset.mul_sum, Finset.sum_mul]
  have e4 : (∑ j ∈ s, W j)ᴴ * (∑ j ∈ s, W j) = X2 := by
    rw [conjTranspose_sum, Finset.sum_mul_sum]
  have hsum : ∑ j ∈ s, ∑ l ∈ s, (a l * W j - a j * W l)ᴴ * (a l * W j - a j * W l)
      = (∑ j ∈ s, (W j)ᴴ * (∑ l ∈ s, a l) * W j - (∑ j ∈ s, W j)ᴴ * (∑ j ∈ s, W j))
        + (∑ j ∈ s, (W j)ᴴ * (∑ l ∈ s, a l) * W j - (∑ j ∈ s, W j)ᴴ * (∑ j ∈ s, W j)) := by
    rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => key j hj l hl]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [e1, e2, e3, e4]; abel
  have h0 : 0 ≤ ∑ j ∈ s, (W j)ᴴ * (∑ l ∈ s, a l) * W j
      - (∑ j ∈ s, W j)ᴴ * (∑ j ∈ s, W j) := by
    apply nonneg_of_add_self
    rw [← hsum]
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => by
      simpa [star_eq_conjTranspose] using star_mul_self_nonneg (a l * W j - a j * W l)
  have h1 : ∑ j ∈ s, (W j)ᴴ * (∑ l ∈ s, a l) * W j ≤ (c : ℂ) • ∑ j ∈ s, (W j)ᴴ * W j := by
    rw [Finset.smul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have := star_left_conjugate_le_conjugate hN (W j)
    simpa [star_eq_conjTranspose, smul_mul_assoc, mul_smul_comm] using this
  exact (sub_nonneg.mp h0).trans h1

/-- Swapping the roles of `i` and `j` in a sum over ordered pairs of distinct elements. -/
private lemma sum_sum_erase_swap {κ M : Type} [DecidableEq κ] [AddCommGroup M] (s : Finset κ)
    (g : κ → κ → M) :
    ∑ i ∈ s, ∑ j ∈ s.erase i, g i j = ∑ i ∈ s, ∑ j ∈ s.erase i, g j i := by
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_erase_eq_sub (f := g i) hi,
    Finset.sum_congr rfl fun i hi => Finset.sum_erase_eq_sub (f := fun j => g j i) hi,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_comm]

private lemma proj_mul_proj_mul {P : Matrix n n ℂ} (hPP : P * P = P) (c : Matrix n n ℂ) :
    P * (P * c) = P * c := by
  rw [← mul_assoc, hPP]

private lemma smul_one_le_smul_one {a b : ℝ} (h : a ≤ b) :
    (a : ℂ) • (1 : Matrix n n ℂ) ≤ (b : ℂ) • 1 := by
  rw [smul_one_eq_diagonal, smul_one_eq_diagonal]
  exact diagonal_ofReal_le fun _ => h

private lemma jInner_sum_right' {X κ : Type} [Fintype X] [DecidableEq X] (s : Finset κ)
    (f : JVec X A) (g : κ → JVec X A) : jInner f (∑ k ∈ s, g k) = ∑ k ∈ s, jInner f (g k) := by
  simp only [jInner_eq_trace, Matrix.mul_sum, Matrix.trace_sum]

private lemma jInner_add_right' {X : Type} [Fintype X] [DecidableEq X] (f g h : JVec X A) :
    jInner f (g + h) = jInner f g + jInner f h := by
  simp only [jInner_eq_trace, Matrix.mul_add, Matrix.trace_add]

private lemma jInner_smul_right' {X : Type} [Fintype X] [DecidableEq X] (c : ℂ) (f g : JVec X A) :
    jInner f (c • g) = c * jInner f g := by
  simp only [jInner_eq_trace, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

end CommonBlockAux

open CommonBlockAux

namespace CondBern

variable (μ : CondBern ι)

/-- `L_B = ∑_{i∈B} Dᵢ`. -/
noncomputable def blockOp (B : Finset ι) : Matrix μ.dist.Supp μ.dist.Supp ℂ :=
  ∑ i ∈ B, μ.dist.condDiff i

/-- `N_{i,B}(x) = ∑_{j ∈ B∖{i}} Aᵢⱼ(x)`: the number of coordinates of `B` interacting with `i`
at `x`. -/
noncomputable def blockInteract (B : Finset ι) (i : ι) (x : ι → Bool) : ℝ :=
  ∑ j ∈ B.erase i, if μ.Interact i j x then 1 else 0

/-! ## The projection onto a good event -/

/-- The diagonal projection onto the support points satisfying an event. -/
private noncomputable def evProj (G : (ι → Bool) → Prop) [DecidablePred G] :
    Matrix μ.dist.Supp μ.dist.Supp ℂ :=
  diagonal fun x => ((if G x.1 then 1 else 0 : ℝ) : ℂ)

private lemma evProj_conjTranspose (G : (ι → Bool) → Prop) [DecidablePred G] :
    (μ.evProj G)ᴴ = μ.evProj G := by
  unfold evProj
  rw [diagonal_conjTranspose]
  congr 1
  funext x
  simp

private lemma evProj_mul_self (G : (ι → Bool) → Prop) [DecidablePred G] :
    μ.evProj G * μ.evProj G = μ.evProj G := by
  unfold evProj
  rw [diagonal_mul_diagonal]
  congr 1
  funext x
  split_ifs <;> simp

private lemma evProj_add_not (G : (ι → Bool) → Prop) [DecidablePred G] :
    μ.evProj G + μ.evProj (fun x => ¬ G x) = 1 := by
  unfold evProj
  rw [diagonal_add, ← diagonal_one]
  congr 1
  funext x
  split_ifs <;> simp_all

private lemma evProj_le_one (G : (ι → Bool) → Prop) [DecidablePred G] : μ.evProj G ≤ 1 := by
  have e : (1 : Matrix μ.dist.Supp μ.dist.Supp ℂ) = diagonal fun _ => ((1 : ℝ) : ℂ) := by
    rw [← diagonal_one]; simp
  rw [e]
  exact diagonal_ofReal_le fun x => by split_ifs <;> norm_num

private lemma commute_evProj_condDiff {B : Finset ι} {G : (ι → Bool) → Prop} [DecidablePred G]
    (hG : ∀ x y : ι → Bool, (∀ k ∉ B, x k = y k) → (G x ↔ G y)) {i : ι} (hi : i ∈ B) :
    Commute (μ.evProj G) (μ.dist.condDiff i) := by
  refine (FinDist.commute_condDiff_diagonal μ.dist i ?_).symm
  intro x y hxy
  have h : G x.1 ↔ G y.1 := hG x.1 y.1 fun k hk => hxy k fun hki => hk (hki ▸ hi)
  simp only [h]

private lemma commute_evProj_interactOp (G : (ι → Bool) → Prop) [DecidablePred G] (i j : ι) :
    Commute (μ.evProj G) (μ.interactOp i j) := by
  unfold evProj interactOp
  exact commute_diagonal _ _

private lemma blockOp_nonneg (B : Finset ι) : 0 ≤ μ.blockOp B :=
  Finset.sum_nonneg fun i _ => μ.dist.condDiff_nonneg i

private lemma commute_evProj_blockOp {B : Finset ι} {G : (ι → Bool) → Prop} [DecidablePred G]
    (hG : ∀ x y : ι → Bool, (∀ k ∉ B, x k = y k) → (G x ↔ G y)) :
    Commute (μ.evProj G) (μ.blockOp B) :=
  Commute.sum_right _ _ _ fun _ hi => μ.commute_evProj_condDiff hG hi

private lemma interactOp_symm_cb (i j : ι) : μ.interactOp i j = μ.interactOp j i := by
  unfold interactOp
  congr 1
  funext x
  exact if_congr (μ.interact_comm i j x.1) rfl rfl

private lemma sum_interactOp_cb (B : Finset ι) (i : ι) :
    ∑ j ∈ B.erase i, μ.interactOp i j
      = diagonal fun x => ((μ.blockInteract B i x.1 : ℝ) : ℂ) := by
  ext x y
  rw [Matrix.sum_apply]
  by_cases h : x = y
  · subst h
    simp [interactOp, blockInteract]
  · simp [interactOp, diagonal_apply_ne _ h]

private lemma commute_sum_interactOp_condDiff_cb (B : Finset ι) (i : ι) :
    Commute (∑ j ∈ B.erase i, μ.interactOp i j) (μ.dist.condDiff i) :=
  Commute.sum_left _ _ _ fun j _ => μ.commute_interactOp_condDiff_left i j

/-- `[Dᵢ, Dⱼ]` vanishes off the interaction indicator, from (4.17). -/
private lemma interactOp_mul_diffComm_cb {i j : ι} (hij : i ≠ j) :
    μ.interactOp i j * μ.diffComm i j = μ.diffComm i j := by
  set K := μ.diffComm i j with hKdef
  set Aij := μ.interactOp i j with hAdef
  have hA : Aijᴴ = Aij := μ.interactOp_isHermitian i j
  have hK : Kᴴ = -K := by
    rw [hKdef, diffComm, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul,
      (μ.dist.condDiff_isHermitian i).eq, (μ.dist.condDiff_isHermitian j).eq, neg_sub]
  have h0 : (K * (1 - Aij))ᴴ * (K * (1 - Aij)) = 0 := by
    apply le_antisymm
    · have h : star (1 - Aij) * (Kᴴ * K) * (1 - Aij)
          ≤ star (1 - Aij) * (((μ.p ^ 2 : ℝ) : ℂ) • Aij) * (1 - Aij) :=
        star_left_conjugate_le_conjugate (μ.diffComm_sq_le_interactOp hij) _
      have e1 : star (1 - Aij) * (Kᴴ * K) * (1 - Aij) = (K * (1 - Aij))ᴴ * (K * (1 - Aij)) := by
        rw [star_eq_conjTranspose, conjTranspose_mul]; simp only [mul_assoc]
      have e2 : star (1 - Aij) * (((μ.p ^ 2 : ℝ) : ℂ) • Aij) * (1 - Aij) = 0 := by
        rw [mul_smul_comm, smul_mul_assoc, mul_assoc, mul_sub, mul_one, hAdef,
          μ.interactOp_mul_self, sub_self, mul_zero, smul_zero]
      rw [e1, e2] at h
      exact h
    · simpa [star_eq_conjTranspose] using star_mul_self_nonneg (K * (1 - Aij))
  have h1 : K * (1 - Aij) = 0 := conjTranspose_mul_self_eq_zero.mp h0
  have h2 : K = K * Aij := by
    rw [mul_sub, mul_one, sub_eq_zero] at h1
    exact h1
  have h3 : Kᴴ = Aij * Kᴴ := by
    conv_lhs => rw [h2]
    rw [conjTranspose_mul, hA]
  rw [hK, mul_neg] at h3
  exact (neg_inj.mp h3).symm

/-- On the good event, `N_{i,B} P ≤ d P`. -/
private lemma sum_interactOp_mul_evProj_le {B : Finset ι} {G : (ι → Bool) → Prop}
    [DecidablePred G] {d : ℝ}
    (hN : ∀ i ∈ B, ∀ x : μ.dist.Supp, G x.1 → μ.blockInteract B i x.1 ≤ d) {i : ι}
    (hi : i ∈ B) :
    (∑ j ∈ B.erase i, μ.interactOp i j) * μ.evProj G ≤ (d : ℂ) • μ.evProj G := by
  have e1 : (∑ j ∈ B.erase i, μ.interactOp i j) * μ.evProj G
      = diagonal fun x => ((μ.blockInteract B i x.1 * (if G x.1 then 1 else 0) : ℝ) : ℂ) := by
    rw [sum_interactOp_cb, evProj, diagonal_mul_diagonal]
    congr 1
    funext x
    push_cast
    ring
  have e2 : (d : ℂ) • μ.evProj G
      = diagonal fun x => ((d * (if G x.1 then 1 else 0) : ℝ) : ℂ) := by
    rw [evProj, ← diagonal_smul]
    congr 1
    funext x
    by_cases hx : G x.1 <;> simp [hx]
  rw [e1, e2]
  refine diagonal_ofReal_le fun x => ?_
  by_cases hx : G x.1
  · simp [hx, hN i hi x hx]
  · simp [hx]

/-- **The spectral gap on the good event** (from (4.19)):
`(1 − pd) L_B P ≤ (L_B P)²`. -/
private lemma blockOp_evProj_sq_ge (B : Finset ι) (G : (ι → Bool) → Prop) [DecidablePred G]
    (hG : ∀ x y : ι → Bool, (∀ k ∉ B, x k = y k) → (G x ↔ G y)) {d : ℝ}
    (hN : ∀ i ∈ B, ∀ x : μ.dist.Supp, G x.1 → μ.blockInteract B i x.1 ≤ d) :
    ((1 - μ.p * d : ℝ) : ℂ) • (μ.blockOp B * μ.evProj G)
      ≤ (μ.blockOp B * μ.evProj G) * (μ.blockOp B * μ.evProj G) := by
  have hPh := μ.evProj_conjTranspose G
  have hPP := μ.evProj_mul_self G
  have hPD : ∀ i ∈ B, Commute (μ.evProj G) (μ.dist.condDiff i) :=
    fun i hi => μ.commute_evProj_condDiff hG hi
  have hPL : Commute (μ.evProj G) (μ.blockOp B) := μ.commute_evProj_blockOp hG
  set P := μ.evProj G with hPdef
  set L := μ.blockOp B with hLdef
  set S := ∑ i ∈ B, ∑ j ∈ B.erase i, μ.dist.condDiff i * μ.dist.condDiff j with hSdef
  set T := ∑ i ∈ B, ∑ j ∈ B.erase i, μ.interactOp i j * μ.dist.condDiff i with hTdef
  -- `L² = L + S`
  have hLL : L * L = L + S := by
    rw [hLdef, hSdef, blockOp, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.add_sum_erase B _ hi, μ.dist.condDiff_mul_self]
  -- `S + pT ≥ 0`, from (4.19)
  have hST : 0 ≤ S + ((μ.p : ℝ) : ℂ) • T := by
    apply nonneg_of_add_self
    have each : ∀ i ∈ B, ∀ j ∈ B.erase i, 0 ≤ μ.dist.condDiff i * μ.dist.condDiff j
        + μ.dist.condDiff j * μ.dist.condDiff i + ((μ.p : ℝ) : ℂ) •
          (μ.interactOp i j * μ.dist.condDiff i + μ.interactOp i j * μ.dist.condDiff j) := by
      intro i _ j hj
      have h := μ.anticomm_ge (Finset.ne_of_mem_erase hj).symm
      rw [mul_add] at h
      have h' := sub_nonneg.mpr h
      rwa [sub_neg_eq_add] at h'
    have hsum := Finset.sum_nonneg fun i hi => Finset.sum_nonneg (each i hi)
    have eb : ∑ i ∈ B, ∑ j ∈ B.erase i, μ.dist.condDiff j * μ.dist.condDiff i = S :=
      (sum_sum_erase_swap B fun i j => μ.dist.condDiff i * μ.dist.condDiff j).symm
    have ee : ∑ i ∈ B, ∑ j ∈ B.erase i, ((μ.p : ℝ) : ℂ) • (μ.interactOp i j * μ.dist.condDiff j)
        = ∑ i ∈ B, ∑ j ∈ B.erase i, ((μ.p : ℝ) : ℂ) • (μ.interactOp i j * μ.dist.condDiff i) := by
      refine (sum_sum_erase_swap B
        fun i j => ((μ.p : ℝ) : ℂ) • (μ.interactOp i j * μ.dist.condDiff j)).trans ?_
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [μ.interactOp_symm_cb]
    convert hsum using 1
    simp only [smul_add, Finset.sum_add_distrib]
    rw [eb, ee, hTdef, Finset.smul_sum]
    simp only [Finset.smul_sum]
    abel
  -- `T = ∑ᵢ Nᵢ Dᵢ`
  have hT : T = ∑ i ∈ B, (∑ j ∈ B.erase i, μ.interactOp i j) * μ.dist.condDiff i := by
    rw [hTdef]
    exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
  -- `∑ᵢ (d − Nᵢ) P Dᵢ = d L P − T P`
  have hX : ∑ i ∈ B, ((d : ℂ) • 1 - ∑ j ∈ B.erase i, μ.interactOp i j) * P * μ.dist.condDiff i
      = (d : ℂ) • (L * P) - T * P := by
    rw [hT, Finset.sum_mul, hLdef, blockOp, Finset.sum_mul, Finset.smul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [sub_mul, smul_mul_assoc, one_mul, mul_assoc, (hPD i hi).eq]
  have hXnn : 0 ≤ ∑ i ∈ B,
      ((d : ℂ) • 1 - ∑ j ∈ B.erase i, μ.interactOp i j) * P * μ.dist.condDiff i := by
    refine Finset.sum_nonneg fun i hi => ?_
    refine mul_proj_nonneg ?_ ?_ (μ.dist.condDiff_isHermitian i).eq (μ.dist.condDiff_mul_self i)
    · rw [sub_mul, smul_mul_assoc, one_mul, sub_nonneg]
      exact μ.sum_interactOp_mul_evProj_le hN hi
    · refine Commute.mul_left (Commute.sub_left ?_ ?_) (hPD i hi)
      · exact Commute.smul_left (Commute.one_left _) _
      · exact μ.commute_sum_interactOp_condDiff_cb B i
  have hSTP : 0 ≤ (S + ((μ.p : ℝ) : ℂ) • T) * P := by
    refine mul_proj_nonneg hST ?_ hPh hPP
    refine Commute.add_left ?_ (Commute.smul_left ?_ _)
    · refine Commute.sum_left _ _ _ fun i hi => Commute.sum_left _ _ _ fun j hj => ?_
      exact ((hPD i hi).symm).mul_left (hPD j (Finset.mem_of_mem_erase hj)).symm
    · refine Commute.sum_left _ _ _ fun i hi => Commute.sum_left _ _ _ fun j _ => ?_
      exact ((μ.commute_evProj_interactOp G i j).symm).mul_left (hPD i hi).symm
  have hLPLP : (L * P) * (L * P) = (L * L) * P := by
    rw [mul_assoc, ← mul_assoc P, hPL.eq, mul_assoc, hPP, ← mul_assoc]
  have key : (L * P) * (L * P) - ((1 - μ.p * d : ℝ) : ℂ) • (L * P)
      = (S + ((μ.p : ℝ) : ℂ) • T) * P + ((μ.p : ℝ) : ℂ) • ∑ i ∈ B,
        ((d : ℂ) • 1 - ∑ j ∈ B.erase i, μ.interactOp i j) * P * μ.dist.condDiff i := by
    rw [hX, hLPLP, hLL, add_mul, add_mul, smul_mul_assoc]
    push_cast
    module
  rw [← sub_nonneg, key]
  exact add_nonneg hSTP (smul_nonneg_real μ.p_pos.le hXnn)

/-- **The commutator bound on the good event** (from (4.17) and (4.18)):
`∑_{i∈B} [Dᵢ P, L_B P]†[Dᵢ P, L_B P] ≤ 2(1 + p)(pd)² L_B P`. -/
private lemma blockOp_evProj_comm_le (B : Finset ι) (G : (ι → Bool) → Prop) [DecidablePred G]
    (hG : ∀ x y : ι → Bool, (∀ k ∉ B, x k = y k) → (G x ↔ G y)) {d : ℝ} (hd : 0 ≤ d)
    (hN : ∀ i ∈ B, ∀ x : μ.dist.Supp, G x.1 → μ.blockInteract B i x.1 ≤ d) :
    ∑ i ∈ B, (μ.dist.condDiff i * μ.evProj G * (μ.blockOp B * μ.evProj G)
        - μ.blockOp B * μ.evProj G * (μ.dist.condDiff i * μ.evProj G))ᴴ
      * (μ.dist.condDiff i * μ.evProj G * (μ.blockOp B * μ.evProj G)
        - μ.blockOp B * μ.evProj G * (μ.dist.condDiff i * μ.evProj G))
      ≤ ((2 * (1 + μ.p) * (μ.p * d) ^ 2 : ℝ) : ℂ) • (μ.blockOp B * μ.evProj G) := by
  have hPh := μ.evProj_conjTranspose G
  have hPP := μ.evProj_mul_self G
  have hPD : ∀ i ∈ B, Commute (μ.evProj G) (μ.dist.condDiff i) :=
    fun i hi => μ.commute_evProj_condDiff hG hi
  have hPL : Commute (μ.evProj G) (μ.blockOp B) := μ.commute_evProj_blockOp hG
  have hPA : ∀ i j, Commute (μ.evProj G) (μ.interactOp i j) := μ.commute_evProj_interactOp G
  set P := μ.evProj G with hPdef
  set L := μ.blockOp B with hLdef
  have hc0 : 0 ≤ μ.p ^ 2 * (1 + μ.p) := by have := μ.p_pos; positivity
  -- the commutator `[Dᵢ P, L P] = ∑_{j ∈ B∖i} [Dᵢ, Dⱼ] P`
  have hA : ∀ i ∈ B, μ.dist.condDiff i * P * (L * P) - L * P * (μ.dist.condDiff i * P)
      = ∑ j ∈ B.erase i, μ.diffComm i j * P := by
    intro i hi
    have h1 : μ.dist.condDiff i * P * (L * P) = μ.dist.condDiff i * L * P := by
      calc μ.dist.condDiff i * P * (L * P) = μ.dist.condDiff i * (P * L) * P := by
            simp only [mul_assoc]
        _ = μ.dist.condDiff i * L * (P * P) := by rw [hPL.eq]; simp only [mul_assoc]
        _ = _ := by rw [hPP]
    have h2 : L * P * (μ.dist.condDiff i * P) = L * μ.dist.condDiff i * P := by
      calc L * P * (μ.dist.condDiff i * P) = L * (P * μ.dist.condDiff i) * P := by
            simp only [mul_assoc]
        _ = L * μ.dist.condDiff i * (P * P) := by rw [(hPD i hi).eq]; simp only [mul_assoc]
        _ = _ := by rw [hPP]
    rw [h1, h2, ← sub_mul, ← Finset.sum_mul]
    congr 1
    rw [Finset.sum_erase B (f := μ.diffComm i) (sub_self _), hLdef, blockOp,
      Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    rfl
  -- weighted Cauchy–Schwarz: at most `d` of the terms are nonzero at each good point
  have hB : ∀ i ∈ B, (∑ j ∈ B.erase i, μ.diffComm i j * P)ᴴ
        * (∑ j ∈ B.erase i, μ.diffComm i j * P)
      ≤ (d : ℂ) • ∑ j ∈ B.erase i, (μ.diffComm i j * P)ᴴ * (μ.diffComm i j * P) := by
    intro i hi
    refine sq_sum_le_of_weights (B.erase i) (fun j => μ.interactOp i j * P)
      (fun j => μ.diffComm i j * P) d ?_ ?_ ?_ ?_ ?_
    · intro j _
      rw [conjTranspose_mul, hPh, (μ.interactOp_isHermitian i j).eq, (hPA i j).eq]
    · intro j _
      calc μ.interactOp i j * P * (μ.interactOp i j * P)
          = μ.interactOp i j * (P * μ.interactOp i j) * P := by simp only [mul_assoc]
        _ = (μ.interactOp i j * μ.interactOp i j) * (P * P) := by
            rw [(hPA i j).eq]; simp only [mul_assoc]
        _ = _ := by rw [μ.interactOp_mul_self, hPP]
    · intro j _ l _
      simp only [hPdef, evProj, interactOp, diagonal_mul_diagonal]
      congr 1
      funext x
      ring
    · intro j hj
      have hjB := Finset.mem_of_mem_erase hj
      have hKP : Commute P (μ.diffComm i j) :=
        Commute.sub_right ((hPD i hi).mul_right (hPD j hjB)) ((hPD j hjB).mul_right (hPD i hi))
      calc μ.interactOp i j * P * (μ.diffComm i j * P)
          = μ.interactOp i j * (P * μ.diffComm i j) * P := by simp only [mul_assoc]
        _ = (μ.interactOp i j * μ.diffComm i j) * (P * P) := by
            rw [hKP.eq]; simp only [mul_assoc]
        _ = _ := by rw [μ.interactOp_mul_diffComm_cb (Finset.ne_of_mem_erase hj).symm, hPP]
    · rw [← Finset.sum_mul]
      exact (μ.sum_interactOp_mul_evProj_le hN hi).trans (smul_le_smul_real hd (μ.evProj_le_one G))
  -- (4.18), conjugated by `P`
  have hC : ∀ i ∈ B, ∀ j ∈ B.erase i, (μ.diffComm i j * P)ᴴ * (μ.diffComm i j * P)
      ≤ ((μ.p ^ 2 * (1 + μ.p) : ℝ) : ℂ) •
        (P * ((μ.interactOp i j * μ.dist.condDiff i)ᴴ * (μ.interactOp i j * μ.dist.condDiff i)
          + (μ.interactOp i j * μ.dist.condDiff j)ᴴ * (μ.interactOp i j * μ.dist.condDiff j))
          * P) := by
    intro i _ j hj
    have h := star_left_conjugate_le_conjugate
      (μ.diffComm_sq_le_interact_condDiff (Finset.ne_of_mem_erase hj).symm) P
    rw [star_eq_conjTranspose, hPh, mul_smul_comm, smul_mul_assoc] at h
    convert h using 1
    rw [conjTranspose_mul, hPh]
    simp only [mul_assoc]
  have hD : ∀ i ∈ B, (μ.dist.condDiff i * P * (L * P) - L * P * (μ.dist.condDiff i * P))ᴴ
        * (μ.dist.condDiff i * P * (L * P) - L * P * (μ.dist.condDiff i * P))
      ≤ (d : ℂ) • ∑ j ∈ B.erase i, ((μ.p ^ 2 * (1 + μ.p) : ℝ) : ℂ) •
        (P * ((μ.interactOp i j * μ.dist.condDiff i)ᴴ * (μ.interactOp i j * μ.dist.condDiff i)
          + (μ.interactOp i j * μ.dist.condDiff j)ᴴ * (μ.interactOp i j * μ.dist.condDiff j))
          * P) := by
    intro i hi
    rw [hA i hi]
    exact (hB i hi).trans (smul_le_smul_real hd (Finset.sum_le_sum (hC i hi)))
  -- the diagonal terms
  have hXterm : ∀ i ∈ B, ∀ j ∈ B.erase i,
      P * ((μ.interactOp i j * μ.dist.condDiff i)ᴴ * (μ.interactOp i j * μ.dist.condDiff i)) * P
        = μ.dist.condDiff i * (μ.interactOp i j * P) * μ.dist.condDiff i := by
    intro i hi j _
    rw [conjTranspose_mul, (μ.dist.condDiff_isHermitian i).eq, (μ.interactOp_isHermitian i j).eq]
    simp only [mul_assoc, (hPD i hi).left_comm, (hPA i j).left_comm, (hPD i hi).eq, hPP,
      proj_mul_proj_mul (μ.interactOp_mul_self i j)]
  set Z := ∑ i ∈ B, ∑ j ∈ B.erase i,
    P * ((μ.interactOp i j * μ.dist.condDiff i)ᴴ * (μ.interactOp i j * μ.dist.condDiff i)) * P
    with hZdef
  have hZ : Z ≤ (d : ℂ) • (L * P) := by
    rw [hZdef, hLdef, blockOp, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have e : ∑ j ∈ B.erase i, P * ((μ.interactOp i j * μ.dist.condDiff i)ᴴ
          * (μ.interactOp i j * μ.dist.condDiff i)) * P
        = star (μ.dist.condDiff i) * ((∑ j ∈ B.erase i, μ.interactOp i j) * P)
          * μ.dist.condDiff i := by
      rw [Finset.sum_congr rfl (hXterm i hi), star_eq_conjTranspose,
        (μ.dist.condDiff_isHermitian i).eq]
      simp only [Finset.mul_sum, Finset.sum_mul]
    rw [e]
    refine (star_left_conjugate_le_conjugate (μ.sum_interactOp_mul_evProj_le hN hi) _).trans
      (le_of_eq ?_)
    rw [star_eq_conjTranspose, (μ.dist.condDiff_isHermitian i).eq, mul_smul_comm, smul_mul_assoc,
      mul_assoc, (hPD i hi).eq, ← mul_assoc, μ.dist.condDiff_mul_self]
  have hY : ∑ i ∈ B, ∑ j ∈ B.erase i,
      P * ((μ.interactOp i j * μ.dist.condDiff j)ᴴ * (μ.interactOp i j * μ.dist.condDiff j)) * P
        = Z := by
    refine (sum_sum_erase_swap B fun i j => P * ((μ.interactOp i j * μ.dist.condDiff j)ᴴ
      * (μ.interactOp i j * μ.dist.condDiff j)) * P).trans ?_
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [μ.interactOp_symm_cb]
  calc _ ≤ ∑ i ∈ B, (d : ℂ) • ∑ j ∈ B.erase i, ((μ.p ^ 2 * (1 + μ.p) : ℝ) : ℂ) •
        (P * ((μ.interactOp i j * μ.dist.condDiff i)ᴴ * (μ.interactOp i j * μ.dist.condDiff i)
          + (μ.interactOp i j * μ.dist.condDiff j)ᴴ * (μ.interactOp i j * μ.dist.condDiff j))
          * P) := Finset.sum_le_sum hD
    _ = ((d * (μ.p ^ 2 * (1 + μ.p)) : ℝ) : ℂ) • (Z + ∑ i ∈ B, ∑ j ∈ B.erase i,
      P * ((μ.interactOp i j * μ.dist.condDiff j)ᴴ * (μ.interactOp i j * μ.dist.condDiff j))
        * P) := by
        rw [hZdef]
        simp only [Finset.smul_sum, smul_add, Matrix.mul_add, Matrix.add_mul,
          Finset.sum_add_distrib, smul_smul]
        push_cast
        rfl
    _ ≤ ((d * (μ.p ^ 2 * (1 + μ.p)) : ℝ) : ℂ) • ((d : ℂ) • (L * P) + (d : ℂ) • (L * P)) := by
        rw [hY]
        exact smul_le_smul_real (mul_nonneg hd hc0) (add_le_add hZ hZ)
    _ = _ := by
        push_cast
        module

private lemma re_jInner_evProj (G : (ι → Bool) → Prop) [DecidablePred G]
    (f : JVec μ.dist.Supp A) :
    (jInner f (μ.evProj G * f)).re
      = ∑ x ∈ Finset.univ.filter (fun x : μ.dist.Supp => G x.1), qNormSq (f x) := by
  classical
  rw [Finset.sum_filter, jInner, Complex.re_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have e : (μ.evProj G * f) x = ((if G x.1 then 1 else 0 : ℝ) : ℂ) • f x := by
    ext a
    simp [evProj, diagonal_mul]
  rw [e, qInner_smul_right, qInner_self]
  split_ifs <;> simp

/-- On the range of `P`, the resolvent of `L_B P` agrees with that of `L_B`. -/
private lemma resolvent_mul_evProj (B : Finset ι) (G : (ι → Bool) → Prop) [DecidablePred G]
    (hG : ∀ x y : ι → Bool, (∀ k ∉ B, x k = y k) → (G x ↔ G y)) {R : ℝ} (hR : 0 < R) :
    resolvent R (μ.blockOp B * μ.evProj G) * μ.evProj G
      = resolvent R (μ.blockOp B) * μ.evProj G := by
  have hPh := μ.evProj_conjTranspose G
  have hPP := μ.evProj_mul_self G
  have hPL : Commute (μ.evProj G) (μ.blockOp B) := μ.commute_evProj_blockOp hG
  have hL : (μ.blockOp B).PosSemidef := (μ.blockOp_nonneg B).posSemidef
  set P := μ.evProj G with hPdef
  set L := μ.blockOp B with hLdef
  have hLP : (L * P).PosSemidef := by
    have e : L * P = Pᴴ * L * P := by rw [hPh, hPL.eq, mul_assoc, hPP]
    rw [e]
    exact hL.conjTranspose_mul_mul_same P
  have h1 := resolvent_mul_one_add_smul hR hLP
  have h2 := one_add_smul_mul_resolvent hR hL
  have h3 : (1 + ((R⁻¹ : ℝ) : ℂ) • (L * P)) * P = (1 + ((R⁻¹ : ℝ) : ℂ) • L) * P := by
    rw [add_mul, add_mul, one_mul, smul_mul_assoc, smul_mul_assoc, mul_assoc, hPP]
  have h4 : Commute P (1 + ((R⁻¹ : ℝ) : ℂ) • L) :=
    (Commute.one_right P).add_right (hPL.smul_right _)
  have h5 : Commute (resolvent R L) P := commute_resolvent_of_commute hPL.symm
  calc resolvent R (L * P) * P
      = resolvent R (L * P) * (P * ((1 + ((R⁻¹ : ℝ) : ℂ) • L) * resolvent R L)) := by
        rw [h2, mul_one]
    _ = resolvent R (L * P) * ((1 + ((R⁻¹ : ℝ) : ℂ) • L) * P) * resolvent R L := by
        rw [← mul_assoc P, h4.eq]; simp only [mul_assoc]
    _ = resolvent R (L * P) * ((1 + ((R⁻¹ : ℝ) : ℂ) • (L * P)) * P) * resolvent R L := by
        rw [h3]
    _ = (resolvent R (L * P) * (1 + ((R⁻¹ : ℝ) : ℂ) • (L * P))) * (P * resolvent R L) := by
        simp only [mul_assoc]
    _ = resolvent R L * P := by rw [h1, one_mul, h5.eq]

/-- **The good part** (Lemma 4.4 applied to the projections `Dᵢ P`):
`∑_{i∈B} P Dᵢ F_B Dᵢ P ≤ 3R I`. -/
private lemma good_part (B : Finset ι) (G : (ι → Bool) → Prop) [DecidablePred G]
    (hG : ∀ x y : ι → Bool, (∀ k ∉ B, x k = y k) → (G x ↔ G y)) {d R : ℝ}
    (hd : 0 ≤ d) (hpd : μ.p * d ≤ 1 / 10)
    (hN : ∀ i ∈ B, ∀ x : μ.dist.Supp, G x.1 → μ.blockInteract B i x.1 ≤ d) (hR : 0 < R) :
    ∑ i ∈ B, μ.evProj G * (μ.dist.condDiff i * resolvent R (μ.blockOp B) * μ.dist.condDiff i)
        * μ.evProj G
      ≤ ((3 * R : ℝ) : ℂ) • (1 : Matrix μ.dist.Supp μ.dist.Supp ℂ) := by
  have hPh := μ.evProj_conjTranspose G
  have hPP := μ.evProj_mul_self G
  have hPD : ∀ i ∈ B, Commute (μ.evProj G) (μ.dist.condDiff i) :=
    fun i hi => μ.commute_evProj_condDiff hG hi
  have hPF : Commute (μ.evProj G) (resolvent R (μ.blockOp B)) :=
    (commute_resolvent_of_commute (μ.commute_evProj_blockOp hG).symm).symm
  have hFP := μ.resolvent_mul_evProj B G hG hR
  set P := μ.evProj G with hPdef
  set L := μ.blockOp B with hLdef
  have hp := μ.p_pos
  have hp2 := μ.p_le_half
  have hpd0 : 0 ≤ μ.p * d := mul_nonneg hp.le hd
  set γ : ℝ := 1 - μ.p * d with hγdef
  set κ : ℝ := Real.sqrt (2 * (1 + μ.p) * (μ.p * d) ^ 2) with hκdef
  have hκ2 : κ ^ 2 = 2 * (1 + μ.p) * (μ.p * d) ^ 2 := Real.sq_sqrt (by positivity)
  have hγ : 0 < γ := by rw [hγdef]; linarith
  have hsum : ∑ k : B, μ.dist.condDiff k.1 * P = L * P := by
    rw [Finset.sum_coe_sort B (fun i => μ.dist.condDiff i * P), hLdef, blockOp, Finset.sum_mul]
  have hPh' : ∀ k : B, (μ.dist.condDiff k.1 * P).IsHermitian := by
    intro k
    change (μ.dist.condDiff k.1 * P)ᴴ = μ.dist.condDiff k.1 * P
    rw [conjTranspose_mul, hPh, (μ.dist.condDiff_isHermitian k.1).eq, (hPD k.1 k.2).eq]
  have hPi' : ∀ k : B, μ.dist.condDiff k.1 * P * (μ.dist.condDiff k.1 * P)
      = μ.dist.condDiff k.1 * P := by
    intro k
    calc μ.dist.condDiff k.1 * P * (μ.dist.condDiff k.1 * P)
        = μ.dist.condDiff k.1 * (P * μ.dist.condDiff k.1) * P := by simp only [mul_assoc]
      _ = (μ.dist.condDiff k.1 * μ.dist.condDiff k.1) * (P * P) := by
          rw [(hPD k.1 k.2).eq]; simp only [mul_assoc]
      _ = _ := by rw [μ.dist.condDiff_mul_self, hPP]
  have hL' : ((γ : ℝ) : ℂ) • (∑ k : B, μ.dist.condDiff k.1 * P)
      ≤ (∑ k : B, μ.dist.condDiff k.1 * P) * (∑ k : B, μ.dist.condDiff k.1 * P) := by
    rw [hsum]
    exact μ.blockOp_evProj_sq_ge B G hG hN
  have hcomm' : ∑ k : B, (μ.dist.condDiff k.1 * P * (∑ k' : B, μ.dist.condDiff k'.1 * P)
        - (∑ k' : B, μ.dist.condDiff k'.1 * P) * (μ.dist.condDiff k.1 * P))ᴴ
      * (μ.dist.condDiff k.1 * P * (∑ k' : B, μ.dist.condDiff k'.1 * P)
        - (∑ k' : B, μ.dist.condDiff k'.1 * P) * (μ.dist.condDiff k.1 * P))
      ≤ ((κ ^ 2 : ℝ) : ℂ) • (∑ k : B, μ.dist.condDiff k.1 * P) := by
    rw [hsum, hκ2, Finset.sum_coe_sort B (fun i => (μ.dist.condDiff i * P * (L * P)
        - L * P * (μ.dist.condDiff i * P))ᴴ
      * (μ.dist.condDiff i * P * (L * P) - L * P * (μ.dist.condDiff i * P)))]
    exact μ.blockOp_evProj_comm_le B G hG hd hN
  have h44 : ∑ k : B, μ.dist.condDiff k.1 * P
        * resolvent R (∑ k' : B, μ.dist.condDiff k'.1 * P) * (μ.dist.condDiff k.1 * P)
      ≤ (((2 + κ ^ 2 / γ ^ 2) * R : ℝ) : ℂ) • (1 : Matrix μ.dist.Supp μ.dist.Supp ℂ) :=
    lemma_4_4 (fun k : B => μ.dist.condDiff k.1 * P) hPh' hPi' hγ hR hL' hcomm'
  rw [hsum, Finset.sum_coe_sort B (fun i => μ.dist.condDiff i * P
    * resolvent R (L * P) * (μ.dist.condDiff i * P))] at h44
  have hconst : (2 + κ ^ 2 / γ ^ 2) * R ≤ 3 * R := by
    have h1 : (μ.p * d) ^ 2 ≤ 1 / 100 := by nlinarith
    have h2 : 81 / 100 ≤ γ ^ 2 := by rw [hγdef]; nlinarith
    have h3 : κ ^ 2 ≤ γ ^ 2 := by
      rw [hκ2]
      have : 2 * (1 + μ.p) * (μ.p * d) ^ 2 ≤ 2 * (3 / 2) * (1 / 100) := by
        gcongr
        linarith
      linarith
    have h4 : κ ^ 2 / γ ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; exact h3
    nlinarith
  refine le_trans (le_of_eq ?_) (h44.trans (smul_one_le_smul_one hconst))
  refine Finset.sum_congr rfl fun i hi => ?_
  have e1 : μ.dist.condDiff i * P * resolvent R (L * P) * (μ.dist.condDiff i * P)
      = μ.dist.condDiff i * P * (resolvent R (L * P) * P) * μ.dist.condDiff i := by
    rw [← (hPD i hi).eq]
    simp only [mul_assoc]
  rw [e1, hFP]
  simp only [mul_assoc, (hPD i hi).left_comm, hPF.left_comm, (hPD i hi).eq, hPP]

/-- **Lemma 4.5 (a common block of coordinates).** Let `B` be a block of coordinates and `G` an
event determined by the coordinates outside `B`, failing with `μ`-probability at most `b`.
Suppose `d ≥ 0`, `pd ≤ 1/10`, and `N_{i,B}(x) ≤ d` for every `i ∈ B` and every support point
`x` in `G`.  Let `Hᵢ ≥ L_B` for `i ∈ B`, `R > 0`, `F_B = (I + L_B/R)⁻¹` and
`Fᵢ = (I + Hᵢ/R)⁻¹`.  Then for joint vectors on every finite workspace,
`∑_{i∈B} ‖Fᵢ Dᵢ f‖² ≤ ∑_{i∈B} ⟨Dᵢ f, F_B Dᵢ f⟩ ≤ 3R‖f‖² + |B| b ‖f‖∞²`. -/
theorem lemma_4_5 (B : Finset ι) (G : (ι → Bool) → Prop) [DecidablePred G]
    (hG : ∀ x y : ι → Bool, (∀ k ∉ B, x k = y k) → (G x ↔ G y))
    {b d R : ℝ} (hb : μ.dist.prob (Finset.univ.filter fun x : μ.dist.Supp => ¬ G x.1) ≤ b)
    (hd : 0 ≤ d) (hpd : μ.p * d ≤ 1 / 10)
    (hN : ∀ i ∈ B, ∀ x : μ.dist.Supp, G x.1 → μ.blockInteract B i x.1 ≤ d)
    (H : ι → Matrix μ.dist.Supp μ.dist.Supp ℂ) (hH : ∀ i ∈ B, μ.blockOp B ≤ H i)
    (hR : 0 < R) (f : JVec μ.dist.Supp A) :
    ∑ i ∈ B, jNormSq (resolvent R (H i) * (μ.dist.condDiff i * f))
        ≤ ∑ i ∈ B, (jInner (μ.dist.condDiff i * f)
            (resolvent R (μ.blockOp B) * (μ.dist.condDiff i * f))).re ∧
      ∑ i ∈ B, (jInner (μ.dist.condDiff i * f)
            (resolvent R (μ.blockOp B) * (μ.dist.condDiff i * f))).re
        ≤ 3 * R * jNormSq f + B.card * b * μ.dist.infNormSq f := by
  have hL0 := μ.blockOp_nonneg B
  have hLpsd : (μ.blockOp B).PosSemidef := hL0.posSemidef
  refine ⟨Finset.sum_le_sum fun i hi => ?_, ?_⟩
  · -- `Fᵢ² ≤ Fᵢ ≤ F_B`
    have hHi : (H i).PosSemidef := (hL0.trans (hH i hi)).posSemidef
    have hF : (resolvent R (H i))ᴴ * resolvent R (H i) ≤ resolvent R (μ.blockOp B) := by
      rw [(resolvent_isHermitian hR hHi).eq]
      exact (resolvent_sq_le hR hHi).trans (resolvent_le_resolvent hR hLpsd (hH i hi))
    exact jNormSq_mul_le hF _
  · have hG' : ∀ x y : ι → Bool, (∀ k ∉ B, x k = y k) → ((¬ G x) ↔ (¬ G y)) :=
      fun x y h => not_congr (hG x y h)
    have hPP := μ.evProj_mul_self G
    have hQh := μ.evProj_conjTranspose (fun x => ¬ G x)
    have hQQ := μ.evProj_mul_self (fun x => ¬ G x)
    have hPQ := μ.evProj_add_not G
    have hPD : ∀ i ∈ B, Commute (μ.evProj G) (μ.dist.condDiff i) :=
      fun i hi => μ.commute_evProj_condDiff hG hi
    have hQD : ∀ i ∈ B, Commute (μ.evProj fun x => ¬ G x) (μ.dist.condDiff i) :=
      fun i hi => μ.commute_evProj_condDiff hG' hi
    have hPF : Commute (μ.evProj G) (resolvent R (μ.blockOp B)) :=
      (commute_resolvent_of_commute (μ.commute_evProj_blockOp hG).symm).symm
    have hQF : Commute (μ.evProj fun x => ¬ G x) (resolvent R (μ.blockOp B)) :=
      (commute_resolvent_of_commute (μ.commute_evProj_blockOp hG').symm).symm
    have hgood := μ.good_part B G hG hd hpd hN hR
    have hQf : (jInner f (μ.evProj (fun x => ¬ G x) * f)).re ≤ b * μ.dist.infNormSq f := by
      rw [re_jInner_evProj]
      exact (μ.dist.sum_qNormSq_le_prob_mul_infNormSq _ f).trans
        (mul_le_mul_of_nonneg_right hb (μ.dist.infNormSq_nonneg f))
    set P := μ.evProj G with hPdef
    set Q := μ.evProj (fun x => ¬ G x) with hQdef
    set F := resolvent R (μ.blockOp B) with hFdef
    -- split each term along `P + Q = 1`
    have hsplit : ∀ i ∈ B, (jInner (μ.dist.condDiff i * f) (F * (μ.dist.condDiff i * f))).re
        = (jInner f ((P * (μ.dist.condDiff i * F * μ.dist.condDiff i) * P) * f)).re
          + (jInner f ((Q * (μ.dist.condDiff i * F * μ.dist.condDiff i) * Q) * f)).re := by
      intro i hi
      have hcP : Commute P (μ.dist.condDiff i * F * μ.dist.condDiff i) :=
        ((hPD i hi).mul_right hPF).mul_right (hPD i hi)
      have hcQ : Commute Q (μ.dist.condDiff i * F * μ.dist.condDiff i) :=
        ((hQD i hi).mul_right hQF).mul_right (hQD i hi)
      have hM : P * (μ.dist.condDiff i * F * μ.dist.condDiff i) * P
          + Q * (μ.dist.condDiff i * F * μ.dist.condDiff i) * Q
          = μ.dist.condDiff i * F * μ.dist.condDiff i := by
        rw [hcP.eq, hcQ.eq, mul_assoc _ P P, mul_assoc _ Q Q, hPP, hQQ, ← mul_add, hPQ, mul_one]
      rw [← Complex.add_re, ← jInner_add_right', ← Matrix.add_mul, hM, jInner_eq_trace,
        jInner_eq_trace, conjTranspose_mul, (μ.dist.condDiff_isHermitian i).eq]
      simp only [Matrix.mul_assoc]
    -- the bad part: `Q Dᵢ F_B Dᵢ Q ≤ Q`
    have hbad : ∑ i ∈ B, Q * (μ.dist.condDiff i * F * μ.dist.condDiff i) * Q
        ≤ ((B.card : ℝ) : ℂ) • Q := by
      have hle : ∀ i ∈ B, Q * (μ.dist.condDiff i * F * μ.dist.condDiff i) * Q ≤ Q := by
        intro i _
        have hM1 : μ.dist.condDiff i * F * μ.dist.condDiff i ≤ 1 := by
          have h := star_left_conjugate_le_conjugate (resolvent_le_one hR hLpsd)
            (μ.dist.condDiff i)
          rw [star_eq_conjTranspose, (μ.dist.condDiff_isHermitian i).eq, mul_one,
            μ.dist.condDiff_mul_self] at h
          exact h.trans (μ.dist.condDiff_le_one i)
        have h := star_left_conjugate_le_conjugate hM1 Q
        rwa [star_eq_conjTranspose, hQh, mul_one, hQQ] at h
      refine (Finset.sum_le_sum hle).trans_eq ?_
      rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, Complex.ofReal_natCast]
    calc ∑ i ∈ B, (jInner (μ.dist.condDiff i * f) (F * (μ.dist.condDiff i * f))).re
        = (jInner f ((∑ i ∈ B, P * (μ.dist.condDiff i * F * μ.dist.condDiff i) * P) * f)).re
          + (jInner f ((∑ i ∈ B, Q * (μ.dist.condDiff i * F * μ.dist.condDiff i) * Q)
            * f)).re := by
          rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Matrix.sum_mul, Matrix.sum_mul,
            jInner_sum_right', jInner_sum_right', Complex.re_sum, Complex.re_sum]
      _ ≤ (jInner f ((((3 * R : ℝ) : ℂ) • (1 : Matrix μ.dist.Supp μ.dist.Supp ℂ)) * f)).re
          + (jInner f ((((B.card : ℝ) : ℂ) • Q) * f)).re :=
          add_le_add (jInner_le_of_le hgood f) (jInner_le_of_le hbad f)
      _ = 3 * R * jNormSq f + B.card * (jInner f (Q * f)).re := by
          rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, jInner_smul_right',
            jInner_smul_right', jInner_self, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
            Complex.ofReal_re]
      _ ≤ 3 * R * jNormSq f + B.card * (b * μ.dist.infNormSq f) := by
          gcongr
      _ = 3 * R * jNormSq f + B.card * b * μ.dist.infNormSq f := by ring

end CondBern

end QuantumQueryComplexity
