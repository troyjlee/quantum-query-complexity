import QuantumQueryComplexity.Quantum.LowerBound.Bridge
import QuantumQueryComplexity.Quantum.Algorithm
import QuantumQueryComplexity.Promise.Defs
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The adversary progress measure

For an adversary matrix `Γ`, a weight vector `δ`, and a family of states `ψ x`
indexed by the promise domain, the **progress** is

  `progress Γ δ δ' ψ = ∑ x, ∑ y, Γ x y · Re ⟪δ x • ψ x, δ' y • ψ y⟫`.

The two weight vectors are **not** a generalization for its own sake: they are
what lets the endgame use the bilinear characterization of the operator norm
(`l2_opNorm_le_of_forall_dotProduct`, already in `Spectral.lean`) instead of a
norm-attaining eigenvector, which the project does not have and which would
need the spectral theorem.

Three facts drive the lower bound, and they are the three theorems here:

* `progress_mulVec` — an **input-independent** unitary does not change it.  This
  is why only queries can make progress.
* `progress_const` — at time zero all the states coincide, so the progress is
  `δ ⬝ᵥ Γ *ᵥ δ'`, which the bilinear characterization can make as close to
  `‖Γ‖` as one likes.
* `abs_progress_oracle_sub_le` — **one query changes it by at most
  `2c √(∑ δ²) √(∑ δ'²)`**, where `c` bounds every `‖Γ ⊙ advDOn read i‖`.

The query step is where the model meets the adversary matrix.  Decompose a state
by its query-index register, `ψ = ∑_o qRestrict idxOf o ψ` over `o : Option ι`.
The oracle preserves each sector, acts as the identity on the idle sector
`none`, and on the sector `some i` depends on the input only through its `i`-th
letter.  So a pair `x, y` contributes to the *change* only through sectors `i`
with `read x i ≠ read y i` — precisely the support of the mask `advDOn read i`.
Replacing `Γ` by `Γ ⊙ advDOn read i` on the sector `i` is therefore free, and
the bridge bounds each of the two resulting Gram forms by `‖Γ ⊙ advDOn read i‖`
times that sector's weight.  Summing over sectors needs only that the sector
weights add up to the total, plus one Cauchy–Schwarz over the sectors.
-/

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X] [DecidableEq X]
variable {W : Type} [Fintype W] [DecidableEq W]
variable {H : Type} [Fintype H] [DecidableEq H]

/-! ## The Gram form -/

/-- A real matrix contracted against two families of complex vectors. -/
noncomputable def gramForm (Γ : Matrix X X ℝ) (u v : X → (H → ℂ)) : ℝ :=
  ∑ x, ∑ y, Γ x y * (qInner (u x) (v y)).re

/-- The bridge, in `gramForm` notation. -/
lemma abs_gramForm_le (Γ : Matrix X X ℝ) (u v : X → (H → ℂ)) :
    |gramForm Γ u v|
      ≤ ‖Γ‖ * Real.sqrt (∑ x, qNormSq (u x)) * Real.sqrt (∑ y, qNormSq (v y)) :=
  abs_sum_gram_re_le Γ u v

/-- The self-paired case, where the two square roots collapse. -/
lemma abs_gramForm_self_le (Γ : Matrix X X ℝ) (u : X → (H → ℂ)) :
    |gramForm Γ u u| ≤ ‖Γ‖ * ∑ x, qNormSq (u x) := by
  have h := abs_gramForm_le Γ u u
  have hnn : 0 ≤ ∑ x, qNormSq (u x) :=
    Finset.sum_nonneg fun x _ => qNormSq_nonneg _
  rwa [mul_assoc, Real.mul_self_sqrt hnn] at h

lemma gramForm_add_left (Γ : Matrix X X ℝ) (u u' v : X → (H → ℂ)) :
    gramForm Γ (fun x => u x + u' x) v = gramForm Γ u v + gramForm Γ u' v := by
  simp only [gramForm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [qInner_add_left, Complex.add_re, mul_add]

lemma gramForm_add_right (Γ : Matrix X X ℝ) (u v v' : X → (H → ℂ)) :
    gramForm Γ u (fun y => v y + v' y) = gramForm Γ u v + gramForm Γ u v' := by
  simp only [gramForm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [qInner_add_right, Complex.add_re, mul_add]

/-- **Masking is free** when the masked-out pairs contribute equally to both
Gram forms. -/
lemma gramForm_sub_eq_mask {Γ M : Matrix X X ℝ} {p : X → X → Prop} [DecidableRel p]
    {u v u' v' : X → (H → ℂ)}
    (hM : ∀ x y, M x y = if p x y then 0 else Γ x y)
    (hzero : ∀ x y, p x y →
      (qInner (u x) (v y)).re = (qInner (u' x) (v' y)).re) :
    gramForm Γ u v - gramForm Γ u' v' = gramForm M u v - gramForm M u' v' := by
  simp only [gramForm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hM]
  by_cases h : p x y
  · rw [if_pos h, hzero x y h]
    ring
  · rw [if_neg h]

/-! ## Sector decomposition by the query-index register -/

/-- The query-index register, used as a readout map. -/
def idxOf : QBasis ι σ W → Option ι := fun p => p.1

@[simp] lemma idxOf_apply (p : QBasis ι σ W) : idxOf p = p.1 := rfl

/-- The Gram form decomposes over the sectors. -/
lemma gramForm_eq_sum_sector (Γ : Matrix X X ℝ) (u v : X → (QBasis ι σ W → ℂ)) :
    gramForm Γ u v = ∑ o : Option ι,
      gramForm Γ (fun x => qRestrict idxOf o (u x))
        (fun y => qRestrict idxOf o (v y)) := by
  have hre : ∀ x y, Γ x y * (qInner (u x) (v y)).re
      = ∑ o : Option ι,
          Γ x y * (qInner (qRestrict idxOf o (u x)) (qRestrict idxOf o (v y))).re := by
    intro x y
    rw [qInner_eq_sum_qRestrict idxOf, Complex.re_sum, Finset.mul_sum]
  calc gramForm Γ u v
      = ∑ x, ∑ y, ∑ o : Option ι,
          Γ x y * (qInner (qRestrict idxOf o (u x)) (qRestrict idxOf o (v y))).re :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hre x y
    _ = ∑ x, ∑ o : Option ι, ∑ y,
          Γ x y * (qInner (qRestrict idxOf o (u x)) (qRestrict idxOf o (v y))).re :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ o : Option ι, ∑ x, ∑ y,
          Γ x y * (qInner (qRestrict idxOf o (u x)) (qRestrict idxOf o (v y))).re :=
        Finset.sum_comm

/-! ## How the oracle acts on the sectors -/

/-- The oracle preserves each sector. -/
lemma qRestrict_idxOf_oracleMat (a : ι → σ) (o : Option ι) (ψ : QBasis ι σ W → ℂ) :
    qRestrict idxOf o (oracleMat a *ᵥ ψ) = oracleMat a *ᵥ (qRestrict idxOf o ψ) := by
  funext p
  rw [qRestrict, oracleMat_mulVec_apply, oracleMat_mulVec_apply, qRestrict,
    idxOf_apply, idxOf_apply, oracleMap_fst]

/-- On the idle sector the oracle is the identity. -/
lemma oracleMat_mulVec_qRestrict_none (a : ι → σ) (ψ : QBasis ι σ W → ℂ) :
    oracleMat a *ᵥ (qRestrict idxOf none ψ) = qRestrict idxOf none ψ := by
  funext p
  rw [oracleMat_mulVec_apply, qRestrict, qRestrict, idxOf_apply, idxOf_apply,
    oracleMap_fst]
  obtain ⟨(_ | i), t, w⟩ := p
  · rw [if_pos rfl, if_pos rfl, oracleMap_none]
  · rw [if_neg (by simp), if_neg (by simp)]

/-- On the sector `some i` the oracle depends on the input only through its
`i`-th letter. -/
lemma oracleMat_mulVec_qRestrict_some {a b : ι → σ} {i : ι} (hab : a i = b i)
    (ψ : QBasis ι σ W → ℂ) :
    oracleMat a *ᵥ (qRestrict idxOf (some i) ψ)
      = oracleMat b *ᵥ (qRestrict idxOf (some i) ψ) := by
  funext p
  rw [oracleMat_mulVec_apply, oracleMat_mulVec_apply, qRestrict, qRestrict,
    idxOf_apply, idxOf_apply, oracleMap_fst, oracleMap_fst]
  by_cases hp : p.1 = some i
  · rw [if_pos hp, if_pos hp]
    obtain ⟨k, t, w⟩ := p
    simp only at hp
    subst hp
    rw [oracleMap_some, oracleMap_some, hab]
  · rw [if_neg hp, if_neg hp]

/-! ## The progress measure -/

/-- The weighted family `x ↦ δ x • ψ x`. -/
noncomputable def qScale (δ : X → ℝ) (ψ : X → (H → ℂ)) : X → (H → ℂ) :=
  fun x => (δ x : ℂ) • ψ x

lemma qScale_apply (δ : X → ℝ) (ψ : X → (H → ℂ)) (x : X) :
    qScale δ ψ x = (δ x : ℂ) • ψ x := rfl

lemma qNormSq_qScale (δ : X → ℝ) (ψ : X → (H → ℂ)) (x : X) :
    qNormSq (qScale δ ψ x) = δ x ^ 2 * qNormSq (ψ x) :=
  qNormSq_real_smul _ _

lemma qScale_add (δ : X → ℝ) (u v : X → (H → ℂ)) (x : X) :
    qScale δ (fun x => u x + v x) x = qScale δ u x + qScale δ v x := by
  rw [qScale_apply, qScale_apply, qScale_apply, smul_add]

lemma qScale_mulVec (U : Matrix H H ℂ) (δ : X → ℝ) (ψ : X → (H → ℂ)) (x : X) :
    qScale δ (fun x => U *ᵥ ψ x) x = U *ᵥ (qScale δ ψ x) := by
  rw [qScale_apply, qScale_apply, Matrix.mulVec_smul]

/-- **The progress measure.** -/
noncomputable def progress (Γ : Matrix X X ℝ) (δ δ' : X → ℝ)
    (ψ : X → (H → ℂ)) : ℝ :=
  gramForm Γ (qScale δ ψ) (qScale δ' ψ)

/-- The master bound on the progress. -/
lemma abs_progress_le (Γ : Matrix X X ℝ) (δ δ' : X → ℝ) (ψ : X → (H → ℂ)) :
    |progress Γ δ δ' ψ|
      ≤ ‖Γ‖ * Real.sqrt (∑ x, δ x ^ 2 * qNormSq (ψ x))
          * Real.sqrt (∑ y, δ' y ^ 2 * qNormSq (ψ y)) := by
  have h := abs_gramForm_le Γ (qScale δ ψ) (qScale δ' ψ)
  rwa [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => qNormSq_qScale δ ψ x,
    Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => qNormSq_qScale δ' ψ y] at h

/-- **An input-independent unitary does not change the progress.** -/
theorem progress_mulVec {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (Γ : Matrix X X ℝ) (δ δ' : X → ℝ) (ψ : X → (H → ℂ)) :
    progress Γ δ δ' (fun x => U *ᵥ ψ x) = progress Γ δ δ' ψ := by
  simp only [progress, gramForm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [qScale_mulVec, qScale_mulVec, qInner_mulVec_mulVec hU]

/-- **At time zero the progress is `δ ⬝ᵥ Γ *ᵥ δ'`.** -/
theorem progress_const (Γ : Matrix X X ℝ) (δ δ' : X → ℝ) {ψ₀ : H → ℂ}
    (hψ : IsQState ψ₀) : progress Γ δ δ' (fun _ => ψ₀) = δ ⬝ᵥ Γ *ᵥ δ' := by
  have hval : ∀ x y : X,
      Γ x y * (qInner (qScale δ (fun _ => ψ₀) x) (qScale δ' (fun _ => ψ₀) y)).re
        = δ x * Γ x y * δ' y := by
    intro x y
    have h1 : qInner (qScale δ (fun _ => ψ₀) x) (qScale δ' (fun _ => ψ₀) y)
        = ((δ x * δ' y : ℝ) : ℂ) := by
      rw [qScale_apply, qScale_apply, qInner_smul_left, qInner_smul_right,
        qInner_self, hψ]
      push_cast
      rw [RCLike.star_def, Complex.conj_ofReal]
      ring
    rw [h1, Complex.ofReal_re]
    ring
  rw [dotProduct_mulVec_eq_sum]
  simp only [progress, gramForm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hval x y

/-! ## The query step -/

section Query

variable (read : X → ι → σ) (Γ : Matrix X X ℝ) (δ : X → ℝ)
  (ψ : X → (QBasis ι σ W → ℂ))

/-- The weighted family restricted to the sector `o`. -/
noncomputable def sectFam (o : Option ι) (δ : X → ℝ)
    (ψ : X → (QBasis ι σ W → ℂ)) : X → (QBasis ι σ W → ℂ) :=
  fun x => (δ x : ℂ) • qRestrict idxOf o (ψ x)

lemma sectFam_apply (o : Option ι) (x : X) :
    sectFam o δ ψ x = (δ x : ℂ) • qRestrict idxOf o (ψ x) := rfl

lemma qScale_restrict_eq_sectFam (o : Option ι) (x : X) :
    qRestrict idxOf o (qScale δ ψ x) = sectFam o δ ψ x := by
  funext p
  rw [qRestrict, qScale_apply, sectFam_apply, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul, qRestrict]
  by_cases hp : idxOf p = o
  · rw [if_pos hp, if_pos hp]
  · rw [if_neg hp, if_neg hp, mul_zero]

/-- The oracle acts on the sector families through the state family. -/
lemma sectFam_oracle (o : Option ι) (x : X) :
    sectFam o δ (fun x => oracleMat (read x) *ᵥ ψ x) x
      = oracleMat (read x) *ᵥ sectFam o δ ψ x := by
  rw [sectFam_apply, sectFam_apply, qRestrict_idxOf_oracleMat, Matrix.mulVec_smul]

/-- The weight carried by the sector `o`. -/
noncomputable def sectorWeight (δ : X → ℝ) (ψ : X → (QBasis ι σ W → ℂ))
    (o : Option ι) : ℝ :=
  ∑ x, qNormSq (sectFam o δ ψ x)

lemma sectorWeight_nonneg (o : Option ι) : 0 ≤ sectorWeight δ ψ o :=
  Finset.sum_nonneg fun _ _ => qNormSq_nonneg _

/-- The sector weights sum to the total weight. -/
lemma sum_sectorWeight :
    ∑ o : Option ι, sectorWeight δ ψ o = ∑ x, δ x ^ 2 * qNormSq (ψ x) := by
  calc ∑ o : Option ι, sectorWeight δ ψ o
      = ∑ o : Option ι, ∑ x, δ x ^ 2 * qNormSq (qRestrict idxOf o (ψ x)) := by
        refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun x _ => ?_
        rw [sectFam_apply, qNormSq_real_smul]
    _ = ∑ x, ∑ o : Option ι, δ x ^ 2 * qNormSq (qRestrict idxOf o (ψ x)) :=
        Finset.sum_comm
    _ = ∑ x, δ x ^ 2 * qNormSq (ψ x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        rw [← sum_qProb (idxOf (ι := ι) (σ := σ) (W := W)) (ψ x)]
        exact Finset.sum_congr rfl fun o _ => (qProb_eq_qNormSq_qRestrict _ _ _).symm

/-- **One query changes the progress by at most `2c` times the two weights.** -/
theorem abs_progress_oracle_sub_le (δ' : X → ℝ) {c : ℝ}
    (hc : ∀ i, ‖Γ ⊙ advDOn read i‖ ≤ c) (hc0 : 0 ≤ c) :
    |progress Γ δ δ' (fun x => oracleMat (read x) *ᵥ ψ x) - progress Γ δ δ' ψ|
      ≤ 2 * c * (Real.sqrt (∑ x, δ x ^ 2 * qNormSq (ψ x))
          * Real.sqrt (∑ y, δ' y ^ 2 * qNormSq (ψ y))) := by
  classical
  set ψ' : X → (QBasis ι σ W → ℂ) := fun x => oracleMat (read x) *ᵥ ψ x with hψ'
  -- the oracle is unitary, so it does not change any sector weight
  have hweight : ∀ (e : X → ℝ) (o : Option ι),
      ∑ x, qNormSq (sectFam o e ψ' x) = sectorWeight e ψ o := by
    intro e o
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hψ', sectFam_oracle, qNormSq_mulVec (oracleMat_mem_unitaryGroup _)]
  -- both progresses, decomposed over sectors
  have hdecomp : progress Γ δ δ' ψ' - progress Γ δ δ' ψ
      = ∑ o : Option ι,
          (gramForm Γ (sectFam o δ ψ') (sectFam o δ' ψ')
            - gramForm Γ (sectFam o δ ψ) (sectFam o δ' ψ)) := by
    rw [progress, progress, gramForm_eq_sum_sector, gramForm_eq_sum_sector,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [funext fun x => qScale_restrict_eq_sectFam δ ψ o x,
      funext fun x => qScale_restrict_eq_sectFam δ' ψ o x,
      funext fun x => qScale_restrict_eq_sectFam δ ψ' o x,
      funext fun x => qScale_restrict_eq_sectFam δ' ψ' o x]
  -- each sector's contribution
  have hsector : ∀ o : Option ι,
      |gramForm Γ (sectFam o δ ψ') (sectFam o δ' ψ')
        - gramForm Γ (sectFam o δ ψ) (sectFam o δ' ψ)|
        ≤ 2 * c * (Real.sqrt (sectorWeight δ ψ o) * Real.sqrt (sectorWeight δ' ψ o)) := by
    intro o
    have hw := sectorWeight_nonneg δ ψ o
    have hw' := sectorWeight_nonneg δ' ψ o
    have hprod : 0 ≤ Real.sqrt (sectorWeight δ ψ o) * Real.sqrt (sectorWeight δ' ψ o) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    cases o with
    | none =>
        -- the oracle acts trivially on the idle sector
        have hfam : ∀ e : X → ℝ, sectFam none e ψ' = sectFam none e ψ := by
          intro e
          funext x
          rw [hψ', sectFam_oracle, sectFam_apply, Matrix.mulVec_smul,
            oracleMat_mulVec_qRestrict_none]
        rw [hfam δ, hfam δ', sub_self, abs_zero]
        have : (0 : ℝ) ≤ 2 * c := by linarith
        exact mul_nonneg this hprod
    | some i =>
        -- pairs agreeing at `i` contribute equally, so the mask is free
        have hmask : gramForm Γ (sectFam (some i) δ ψ') (sectFam (some i) δ' ψ')
            - gramForm Γ (sectFam (some i) δ ψ) (sectFam (some i) δ' ψ)
            = gramForm (Γ ⊙ advDOn read i) (sectFam (some i) δ ψ')
                (sectFam (some i) δ' ψ')
              - gramForm (Γ ⊙ advDOn read i) (sectFam (some i) δ ψ)
                (sectFam (some i) δ' ψ) := by
          refine gramForm_sub_eq_mask (p := fun x y => read x i = read y i)
            (fun x y => hadamard_advDOn_apply read Γ i x y) ?_
          intro x y hagree
          have hxy : oracleMat (read y) *ᵥ sectFam (some i) δ' ψ y
              = oracleMat (read x) *ᵥ sectFam (some i) δ' ψ y := by
            rw [sectFam_apply, Matrix.mulVec_smul, Matrix.mulVec_smul,
              oracleMat_mulVec_qRestrict_some hagree.symm]
          congr 1
          rw [sectFam_oracle, sectFam_oracle, hxy,
            qInner_mulVec_mulVec (oracleMat_mem_unitaryGroup _)]
        rw [hmask]
        have h1 := abs_gramForm_le (Γ ⊙ advDOn read i) (sectFam (some i) δ ψ')
          (sectFam (some i) δ' ψ')
        have h2 := abs_gramForm_le (Γ ⊙ advDOn read i) (sectFam (some i) δ ψ)
          (sectFam (some i) δ' ψ)
        rw [hweight δ (some i), hweight δ' (some i)] at h1
        rw [show (∑ x, qNormSq (sectFam (some i) δ ψ x)) = sectorWeight δ ψ (some i) from rfl,
          show (∑ y, qNormSq (sectFam (some i) δ' ψ y)) = sectorWeight δ' ψ (some i) from rfl]
          at h2
        have htri : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := by
          intro a b
          rw [sub_eq_add_neg]
          exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
        have hmul : ‖Γ ⊙ advDOn read i‖
              * Real.sqrt (sectorWeight δ ψ (some i))
              * Real.sqrt (sectorWeight δ' ψ (some i))
            ≤ c * (Real.sqrt (sectorWeight δ ψ (some i))
              * Real.sqrt (sectorWeight δ' ψ (some i))) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (hc i) hprod
        have := htri (gramForm (Γ ⊙ advDOn read i) (sectFam (some i) δ ψ')
            (sectFam (some i) δ' ψ'))
          (gramForm (Γ ⊙ advDOn read i) (sectFam (some i) δ ψ) (sectFam (some i) δ' ψ))
        linarith
  calc |progress Γ δ δ' ψ' - progress Γ δ δ' ψ|
      = |∑ o : Option ι, (gramForm Γ (sectFam o δ ψ') (sectFam o δ' ψ')
            - gramForm Γ (sectFam o δ ψ) (sectFam o δ' ψ))| := by rw [hdecomp]
    _ ≤ ∑ o : Option ι, |gramForm Γ (sectFam o δ ψ') (sectFam o δ' ψ')
            - gramForm Γ (sectFam o δ ψ) (sectFam o δ' ψ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ o : Option ι, 2 * c *
          (Real.sqrt (sectorWeight δ ψ o) * Real.sqrt (sectorWeight δ' ψ o)) :=
        Finset.sum_le_sum fun o _ => hsector o
    _ = 2 * c * ∑ o : Option ι,
          (Real.sqrt (sectorWeight δ ψ o) * Real.sqrt (sectorWeight δ' ψ o)) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * c * (Real.sqrt (∑ o : Option ι, sectorWeight δ ψ o)
          * Real.sqrt (∑ o : Option ι, sectorWeight δ' ψ o)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        exact Real.sum_sqrt_mul_sqrt_le _ (fun o => sectorWeight_nonneg δ ψ o)
          (fun o => sectorWeight_nonneg δ' ψ o)
    _ = 2 * c * (Real.sqrt (∑ x, δ x ^ 2 * qNormSq (ψ x))
          * Real.sqrt (∑ y, δ' y ^ 2 * qNormSq (ψ y))) := by
        rw [sum_sectorWeight, sum_sectorWeight]

end Query

end QuantumQueryComplexity
