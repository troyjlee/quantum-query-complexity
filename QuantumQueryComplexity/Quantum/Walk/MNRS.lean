import QuantumQueryComplexity.Quantum.Walk.GlobalInv
import QuantumQueryComplexity.Quantum.RobustSearch.Public
set_option synthInstance.maxSize 3200
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Quantum-walk search (Magniez–Nayak–Roland–Santha)

The caller supplies a `WalkSetup`: routines `prepV` (setup, `S` queries), `updA`, `updB` (the
row update and the reversed-row update, `U` queries each), `markV` (an exact phase marker on
the vertex register, `C` queries); the input-independent chain data `r = √π`, the discriminant
`D`, the absolute gap `δ`; and a clock length `T` with `4 ≤ T²δ`.  The compiled algorithm
`walkSearch S K` is built from these alone — it never sees an input.

`WalkOK S x Marked` is what the routines must satisfy on the input `x`: they prepare `√π`,
the row states have Gram matrix `D` and blank query registers, the updates commute with the
query-blank flag, and `markV` is the phase flip of `Marked` on the vertex register.  Then:

* `walkSearch_pr_unmarked` — an unmarked vertex is returned with probability `0`;
* `two_thirds_le_walkSearch` — if the stationary marked mass `∑_{v marked} π v` is at least
  `ε` and `⌈1/ε⌉ ≤ 9^K`, a marked vertex is returned with probability `≥ 2/3`;
* `walkSearch_pr_none_of_empty` — with no marked vertex, `none` is returned surely;
* `walkSearch_q` — the exact budget `110 · passLen S C r (K+1)`, with
  `r (j+1) = 2U_A + 2(j+10)(T−1)·(2U_A + 2U_B)`, and `walkSearch_q_le`:
  `q ≤ 110·(S + C + 2·3^{K+2}·(2C + 21ρ))`, `ρ = 2U_A + 2(T−1)(2U_A+2U_B)` — the setup is
  charged `110` times whatever `K`, and no logarithm appears.

The walk `W = R_B R_A` costs `2U_A + 2U_B`: each row reflection is an update, the free
reflection about the blank vertex encoding, and the inverse update.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ V : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype V] [DecidableEq V]

/-- **The caller's data.** -/
structure WalkSetup (ι σ V : Type) [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    [Fintype V] [DecidableEq V] where
  prepV : QRoutine ι σ V
  initV : QBasis ι σ V → ℂ
  hinit : IsQState initV
  updA : QRoutine ι σ (V × Option V)
  updB : QRoutine ι σ (V × Option V)
  markV : QRoutine ι σ V
  r : V → ℂ
  D : Matrix V V ℂ
  δ : ℝ
  T : ℕ
  hT0 : 0 < T
  hT : 4 ≤ (T : ℝ) ^ 2 * δ

/-- The blank vertex encoding. -/
def vertBlank : QBasis ι σ (V × Option V) → Bool := fun q =>
  decide (q.1 = none ∧ q.2.1 = none ∧ q.2.2.2 = none)

lemma vertE_injective : Function.Injective (vertE (ι := ι) (σ := σ) (V := V)) := by
  intro u v huv
  simp only [vertE, Prod.mk.injEq] at huv
  exact huv.2.2.1

lemma flagProj_vertBlank :
    flagProj (vertBlank (ι := ι) (σ := σ) (V := V)) = WalkFam.projA fun u => qBasis (vertE u) := by
  refine matrix_ext_of_mulVec_qBasis fun p => ?_
  rw [flagProj_mulVec, WalkFam.projA_mulVec]
  funext q
  rw [goodPart_apply]
  simp only [lin, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, qInner_qBasis_left, qBasis_apply]
  by_cases hq : q = p
  · subst hq
    obtain ⟨k, t, u, nb⟩ := q
    by_cases hb : vertBlank ((k, t, (u, nb)) : QBasis ι σ (V × Option V)) = true
    · rw [if_pos hb, if_pos rfl]
      simp only [vertBlank, decide_eq_true_eq] at hb
      obtain ⟨rfl, rfl, rfl⟩ := hb
      rw [Finset.sum_eq_single u]
      · simp [vertE]
      · intro v _ hv
        have : vertE (ι := ι) (σ := σ) v ≠ (none, none, (u, none)) :=
          fun h => hv (vertE_injective h)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hb]
      refine (Finset.sum_eq_zero fun v _ => ?_).symm
      have : vertE (ι := ι) (σ := σ) v ≠ (k, t, (u, nb)) := by
        intro h; apply hb
        simp only [vertE, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        simp [vertBlank]
      simp [this]
  · rw [if_neg hq, ite_self]
    refine (Finset.sum_eq_zero fun v _ => ?_).symm
    by_cases h1 : vertE v = p
    · rw [if_pos h1, if_neg (fun h2 => hq (h2.trans h1)), mul_zero]
    · rw [if_neg h1, zero_mul]

lemma isQProjector_flagProj_vertBlank :
    IsQProjector (flagProj (vertBlank (ι := ι) (σ := σ) (V := V))) :=
  ⟨flagProj_conjTranspose _, flagProj_mul_self _⟩

/-- The free reflection about the blank vertex encoding. -/
noncomputable def blankRefl : Matrix (QBasis ι σ (V × Option V)) (QBasis ι σ (V × Option V)) ℂ :=
  qRefl (flagProj vertBlank)

lemma blankRefl_mem_unitaryGroup :
    blankRefl (ι := ι) (σ := σ) (V := V) ∈ Matrix.unitaryGroup _ ℂ :=
  qRefl_mem_unitaryGroup isQProjector_flagProj_vertBlank

/-- `U (2P − 1) U† = 2 UPU† − 1`. -/
lemma mul_qRefl_mul_conjTranspose {H : Type} [Fintype H] [DecidableEq H]
    {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) (P : Matrix H H ℂ) :
    U * qRefl P * Uᴴ = qRefl (U * P * Uᴴ) := by
  have hUU : U * Uᴴ = 1 := by
    have := conjTranspose_mul_self_of_unitary (conjTranspose_mem_qUnitary hU)
    rwa [Matrix.conjTranspose_conjTranspose] at this
  rw [qRefl, qRefl, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hUU]

lemma conj_projA {H : Type} [Fintype H] [DecidableEq H] (U : Matrix H H ℂ)
    (f : V → (H → ℂ)) : U * WalkFam.projA f * Uᴴ = WalkFam.projA fun u => U *ᵥ f u := by
  rw [WalkFam.projA, WalkFam.projA, Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl fun u _ => mul_ketbra_mul_conjTranspose U (f u)

namespace WalkSetup

variable (S : WalkSetup ι σ V)

/-- The row reflection: update, free reflection, inverse update. -/
noncomputable def reflAR : QRoutine ι σ (V × Option V) :=
  S.updA.inv.conjFixed blankRefl blankRefl_mem_unitaryGroup

noncomputable def reflBR : QRoutine ι σ (V × Option V) :=
  S.updB.inv.conjFixed blankRefl blankRefl_mem_unitaryGroup

/-- **The walk routine** `R_B R_A`. -/
noncomputable def walkR : QRoutine ι σ (V × Option V) := S.reflAR.comp S.reflBR

@[simp] lemma walkR_len : S.walkR.len = 2 * S.updA.len + 2 * S.updB.len := by
  simp [walkR, reflAR, reflBR]

/-- The row states. -/
noncomputable def rowA (x : ι → σ) (u : V) : QBasis ι σ (V × Option V) → ℂ :=
  S.updA.run x *ᵥ qBasis (vertE u)

noncomputable def rowB (x : ι → σ) (u : V) : QBasis ι σ (V × Option V) → ℂ :=
  S.updB.run x *ᵥ qBasis (vertE u)

lemma reflAR_run (x : ι → σ) : S.reflAR.run x = qRefl (WalkFam.projA (S.rowA x)) := by
  rw [reflAR, QRoutine.conjFixed_run, QRoutine.inv_run, Matrix.conjTranspose_conjTranspose,
    ← Matrix.mul_assoc, blankRefl, mul_qRefl_mul_conjTranspose (S.updA.run_mem_unitaryGroup x),
    flagProj_vertBlank, conj_projA]
  rfl

lemma reflBR_run (x : ι → σ) : S.reflBR.run x = qRefl (WalkFam.projA (S.rowB x)) := by
  rw [reflBR, QRoutine.conjFixed_run, QRoutine.inv_run, Matrix.conjTranspose_conjTranspose,
    ← Matrix.mul_assoc, blankRefl, mul_qRefl_mul_conjTranspose (S.updB.run_mem_unitaryGroup x),
    flagProj_vertBlank, conj_projA]
  rfl

theorem walkR_run (x : ι → σ) : S.walkR.run x = WalkFam.walkOp (S.rowA x) (S.rowB x) := by
  rw [walkR, QRoutine.comp_run, reflAR_run, reflBR_run, WalkFam.walkOp]

/-- The routines of the compiled algorithm, from the data alone. -/
noncomputable def lvl (k : ℕ) : QRoutine ι σ (ClockWork ι (k * (S.T - 1) + 1) (V × Option V)) :=
  lvlRoutine S.updA S.walkR S.T k S.hT0

noncomputable def blockRefl (Lc : ℕ) (j : Fin Lc) : QRoutine ι σ (Wg ι V Lc S.T (WalkGlobal.kkG Lc)) :=
  (S.lvl (WalkGlobal.kkG Lc j)).kronLift (blkEquiv j)

noncomputable def reflG (Lc : ℕ) (n : ℕ) : QRoutine ι σ (Wg ι V Lc S.T (WalkGlobal.kkG Lc)) :=
  if h : 0 < n ∧ n - 1 < Lc then S.blockRefl Lc ⟨n - 1, h.2⟩ else QRoutine.identity

noncomputable def markG (Lc : ℕ) : QRoutine ι σ (Wg ι V Lc S.T (WalkGlobal.kkG Lc)) :=
  S.markV.liftReg (∀ j, Blk ι V Lc S.T (WalkGlobal.kkG Lc) j)

noncomputable def prepG (Lc : ℕ) : QRoutine ι σ (Wg ι V Lc S.T (WalkGlobal.kkG Lc)) :=
  S.prepV.liftReg (∀ j, Blk ι V Lc S.T (WalkGlobal.kkG Lc) j)

noncomputable def initG (Lc : ℕ) : QBasis ι σ (Wg ι V Lc S.T (WalkGlobal.kkG Lc)) → ℂ :=
  embedReg (blankAll ι V Lc S.T (WalkGlobal.kkG Lc)) S.initV

lemma initG_unit (Lc : ℕ) : IsQState (S.initG Lc) := by
  rw [IsQState, initG, qNormSq_embedReg]; exact S.hinit

/-- **The quantum-walk search algorithm** with scale cutoff `K`. -/
noncomputable def walkSearch (K : ℕ) : OTrial ι σ V :=
  approxSearch (S.prepG (K + 1)) (S.initG (K + 1)) (S.initG_unit (K + 1)) (S.markG (K + 1))
    (S.reflG (K + 1)) (cleanG (V := V) (Lc := K + 1) (T := S.T) (kk := WalkGlobal.kkG (K + 1)))
    (vtxG (ι := ι) (σ := σ) (V := V) (Lc := K + 1) (T := S.T) (kk := WalkGlobal.kkG (K + 1))) K

/-- The stationary mass of the marked vertices. -/
noncomputable def markedMass (Marked : V → Prop) [DecidablePred Marked] : ℝ :=
  ∑ v, if Marked v then Complex.normSq (S.r v) else 0

end WalkSetup

/-! ## The contract on an input -/

/-- **What the routines must satisfy on the input `x`.** -/
structure WalkOK (S : WalkSetup ι σ V) (x : ι → σ) (Marked : V → Prop) [DecidablePred Marked] :
    Prop where
  prep_run : S.prepV.run x *ᵥ S.initV = sqrtPiV S.r
  gram : ∀ u v, qInner (S.rowA x u) (S.rowB x v) = S.D u v
  herm : S.Dᴴ = S.D
  r_unit : IsQState S.r
  D_r : S.D *ᵥ S.r = S.r
  δ_pos : 0 < S.δ
  δ_le : S.δ ≤ 1
  gap_D : ∀ y, qInner S.r y = 0 → qNormSq (S.D *ᵥ y) ≤ (1 - S.δ) ^ 2 * qNormSq y
  a_supp : ∀ u, SuppIn {q | QbSys q = true} (S.rowA x u)
  b_supp : ∀ u, SuppIn {q | QbSys q = true} (S.rowB x u)
  updA_comm : S.updA.run x * flagProj QbSys = flagProj QbSys * S.updA.run x
  updB_comm : S.updB.run x * flagProj QbSys = flagProj QbSys * S.updB.run x
  mark_flip : ∀ φ, S.markV.run x *ᵥ φ = phaseFlip (fun p : QBasis ι σ V => p.2.2) Marked φ

namespace WalkOK

variable {S : WalkSetup ι σ V} {x : ι → σ} {Marked : V → Prop} [DecidablePred Marked]
  (h : WalkOK S x Marked)

lemma qInner_rows_of_unitary {U : Matrix (QBasis ι σ (V × Option V)) (QBasis ι σ (V × Option V)) ℂ}
    (hU : U ∈ Matrix.unitaryGroup _ ℂ) (u v : V) :
    qInner (U *ᵥ qBasis (vertE u)) (U *ᵥ qBasis (vertE v)) = if u = v then 1 else 0 := by
  rw [qInner_mulVec_mulVec hU, qInner_qBasis_left, qBasis_apply]
  by_cases huv : u = v
  · subst huv; simp
  · rw [if_neg huv, if_neg (fun h => huv (vertE_injective h))]

include h

/-- The level data of the walk on `x`. -/
noncomputable def level : LevelData ι σ (V × Option V) V x where
  a := S.rowA x
  b := S.rowB x
  D := S.D
  r := S.r
  δ := S.δ
  fam := ⟨qInner_rows_of_unitary (S.updA.run_mem_unitaryGroup x),
    qInner_rows_of_unitary (S.updB.run_mem_unitaryGroup x), h.gram, h.herm, h.r_unit, h.D_r,
    h.δ_pos, h.δ_le, h.gap_D⟩
  walkR := S.walkR
  walk_run := S.walkR_run x
  upd := S.updA
  e := vertE
  e_inj := vertE_injective
  upd_e := fun _ => rfl
  Qb := QbSys
  Qb_e := fun _ => by simp [QbSys, vertE]
  a_supp := h.a_supp
  b_supp := h.b_supp
  upd_comm := h.updA_comm

/-- The global data of the walk on `x`. -/
noncomputable def global : WalkGlobal ι σ V x where
  L := h.level
  he := rfl
  hQ := rfl
  T := S.T
  hT0 := S.hT0
  hT := S.hT
  markV := S.markV
  Marked := Marked
  mark_flip := h.mark_flip
  prepV := S.prepV
  initV := S.initV
  hinit := S.hinit
  prep_run := h.prep_run

lemma global_reflG (Lc : ℕ) : h.global.reflG Lc = S.reflG Lc := rfl
lemma global_prepG (Lc : ℕ) : h.global.prepG Lc = S.prepG Lc := rfl
lemma global_markG (Lc : ℕ) : h.global.markG Lc = S.markG Lc := rfl
lemma global_initG (Lc : ℕ) : h.global.initG Lc = S.initG Lc := rfl

/-- **The search contract holds for the walk data**, up to any level. -/
theorem searchInv (Lc : ℕ) :
    SearchInvUpTo (vtxG (ι := ι) (σ := σ) (V := V) (Lc := Lc) (T := S.T) (kk := WalkGlobal.kkG Lc)) Marked Lc
      (S.markG Lc) (S.reflG Lc) (cleanG (V := V) (Lc := Lc) (T := S.T) (kk := WalkGlobal.kkG Lc)) x
      ((S.prepG Lc).run x *ᵥ S.initG Lc) (fun j => (1 / 2) ^ (j + 8))
      (FG (V := V) (Lc := Lc) (T := S.T) (kk := WalkGlobal.kkG Lc)) :=
  h.global.searchInv Lc

omit h in
lemma qNormSq_sum_qBasis {H : Type} [Fintype H] [DecidableEq H] {f : V → H}
    (hf : Function.Injective f) (c : V → ℂ) :
    qNormSq (∑ u, c u • qBasis (f u)) = ∑ u, Complex.normSq (c u) := by
  have hq : qInner (∑ u, c u • qBasis (f u)) (∑ u, c u • qBasis (f u))
      = ((∑ u, Complex.normSq (c u) : ℝ) : ℂ) := by
    rw [qInner_sum_left]
    push_cast
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [qInner_smul_left, qInner_sum_right, Finset.sum_eq_single u]
    · rw [qInner_smul_right, qInner_qBasis_left, qBasis_apply, if_pos rfl, mul_one,
        Complex.normSq_eq_conj_mul_self, Complex.star_def]
    · intro v _ hv
      rw [qInner_smul_right, qInner_qBasis_left, qBasis_apply, if_neg (fun h => hv (hf h).symm),
        mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [qInner_self] at hq
  exact_mod_cast hq

omit h in
lemma goodPart_smul_qBasis {H O : Type} [Fintype H] [DecidableEq H] (rd : H → O) (G : O → Prop)
    [DecidablePred G] (c : ℂ) (p : H) :
    goodPart rd G (c • qBasis p) = (if G (rd p) then c else 0) • qBasis p := by
  funext q
  rw [goodPart_apply]
  by_cases hq : q = p
  · subst hq; simp
  · simp [qBasis_apply, hq]

omit h in
lemma goodPart_sum' {H O α : Type} [Fintype H] [DecidableEq H] (rd : H → O) (G : O → Prop)
    [DecidablePred G] (s : Finset α) (f : α → H → ℂ) :
    goodPart rd G (∑ i ∈ s, f i) = ∑ i ∈ s, goodPart rd G (f i) := by
  funext q
  rw [goodPart_apply, Finset.sum_apply, Finset.sum_apply]
  simp only [goodPart_apply]
  split_ifs <;> simp

/-- The marked mass of the prepared state is the stationary marked mass. -/
theorem goodProb_prepG (Lc : ℕ) :
    goodProb (vtxG (ι := ι) (σ := σ) (V := V) (Lc := Lc) (T := S.T) (kk := WalkGlobal.kkG Lc))
      Marked ((S.prepG Lc).run x *ᵥ S.initG Lc) = S.markedMass Marked := by
  have this : (S.prepG Lc).run x *ᵥ S.initG Lc
      = ∑ u, S.r u • qBasis (gPt (ι := ι) (σ := σ) (Lc := Lc) (T := S.T)
          (kk := WalkGlobal.kkG Lc) u) := h.global.prepG_run Lc
  rw [this, ← qNormSq_goodPart, goodPart_sum']
  simp only [goodPart_smul_qBasis]
  rw [qNormSq_sum_qBasis (fun u v huv =>
    congrArg (fun q : QBasis ι σ (Wg ι V Lc S.T (WalkGlobal.kkG Lc)) => q.2.2.2) huv),
    WalkSetup.markedMass]
  refine Finset.sum_congr rfl fun u _ => ?_
  show Complex.normSq (if Marked u then S.r u else 0) = _
  split_ifs <;> simp

/-! ## The public theorems -/

variable (K : ℕ)

/-- **An unmarked vertex is never returned.** -/
theorem walkSearch_pr_unmarked {v : V} (hv : ¬ Marked v) :
    (S.walkSearch K).pr x (some v) = 0 :=
  approxSearch_pr_unmarked_upTo (h.searchInv (K + 1)) le_rfl hv

/-- **A marked vertex is found with probability at least `2/3`** under the marked-mass
promise `ε ≤ ∑_{v marked} π v`, `⌈1/ε⌉ ≤ 9^K`. -/
theorem two_thirds_le_walkSearch {ε : ℝ} (hε : 0 < ε) (hm : ε ≤ S.markedMass Marked)
    (hK : ⌈1 / ε⌉₊ ≤ 9 ^ K) :
    2 / 3 ≤ (S.walkSearch K).good Marked x :=
  two_thirds_le_approxSearch_upTo (h.searchInv (K + 1)) le_rfl hε
    (by rw [h.goodProb_prepG]; exact hm) hK

/-- **With no marked vertex, `none` is returned surely.** -/
theorem walkSearch_pr_none_of_empty (hno : ∀ v, ¬ Marked v) :
    (S.walkSearch K).pr x none = 1 :=
  approxSearch_pr_none_of_empty_upTo (h.searchInv (K + 1)) le_rfl hno

end WalkOK

/-! ## The budget -/

namespace WalkSetup

variable (S : WalkSetup ι σ V)


end WalkSetup

/-! ## The budget -/

lemma lvlRoutine_len {W : Type} [Fintype W] [DecidableEq W] (upd walkR : QRoutine ι σ W)
    (T k : ℕ) (hT0 : 0 < T) :
    (lvlRoutine upd walkR T k hT0).len = 2 * upd.len + 2 * (k * (T - 1) * walkR.len) := by
  simp only [lvlRoutine, QRoutine.comp_len, liftClk_len, LevelData.prepR, LevelData.prepRH,
    QRoutine.ofUnitary_len, wDetector_len, QRoutine.inv_len, Nat.add_sub_cancel]
  ring

namespace WalkSetup

variable (S : WalkSetup ι σ V)

/-- The cost of one reflection unit: `ρ = 2U_A + 2(T−1)(2U_A + 2U_B)`. -/
def ρ : ℕ := 2 * S.updA.len + 2 * ((S.T - 1) * (2 * S.updA.len + 2 * S.updB.len))

lemma reflG_len_le (Lc n : ℕ) : (S.reflG Lc n).len ≤ S.ρ * (n + 9) := by
  rw [reflG]
  split_ifs with h
  · show (S.lvl _).len ≤ _
    rw [lvl, lvlRoutine_len, walkR_len, ρ]
    show 2 * S.updA.len + 2 * ((n - 1 + 10) * (S.T - 1) * (2 * S.updA.len + 2 * S.updB.len)) ≤ _
    have : n - 1 + 10 = n + 9 := by omega
    rw [this]
    nlinarith [Nat.zero_le (S.updA.len), Nat.zero_le ((S.T - 1) * (2 * S.updA.len + 2 * S.updB.len))]
  · exact Nat.zero_le _

/-- **The exact budget.** -/
theorem walkSearch_q (K : ℕ) :
    (S.walkSearch K).q
      = 110 * passLen S.prepV.len S.markV.len (fun l => (S.reflG (K + 1) l).len) (K + 1) :=
  approxSearch_q _ _ _ _ _ _ _ K

/-- **`q ≤ 110·(S + C + 2·3^{K+2}·(2C + 21ρ))`**: the setup once per pass, no logarithm. -/
theorem walkSearch_q_le (K : ℕ) :
    (S.walkSearch K).q
      ≤ 110 * (S.prepV.len + S.markV.len + 2 * 3 ^ (K + 2) * (2 * S.markV.len + 21 * S.ρ)) := by
  rw [walkSearch_q]
  have h := passLen_le (S := S.prepV.len) (C := S.markV.len) (ρ := S.ρ)
    (fun l => S.reflG_len_le (K + 1) l) (K + 1)
  rw [show K + 1 + 1 = K + 2 from rfl] at h
  omega

end WalkSetup

/-! ## The real-valued form -/

/-- `⌈√⌈1/ε⌉⌉ ≤ 2⌈1/√ε⌉` for `0 < ε ≤ 1`. -/
lemma ceil_sqrt_ceil_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ⌈Real.sqrt (⌈1 / ε⌉₊ : ℝ)⌉₊ ≤ 2 * ⌈1 / Real.sqrt ε⌉₊ := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hs1 : Real.sqrt ε ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hε1
  have h1 : (1 : ℝ) ≤ 1 / Real.sqrt ε := by rw [le_div_iff₀ hs]; linarith
  have hR : (1 : ℝ) ≤ ⌈1 / Real.sqrt ε⌉₊ := h1.trans (Nat.le_ceil _)
  have hm : (⌈1 / ε⌉₊ : ℝ) ≤ 1 / ε + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have h2 : Real.sqrt (⌈1 / ε⌉₊ : ℝ) ≤ 1 / Real.sqrt ε + 1 := by
    refine (Real.sqrt_le_sqrt hm).trans ?_
    rw [Real.sqrt_le_left (by positivity)]
    have hsε : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
    have hinv : (1 / Real.sqrt ε) ^ 2 = 1 / ε := by rw [div_pow, one_pow, hsε]
    have h0 : 0 ≤ 1 / Real.sqrt ε := by positivity
    nlinarith [hinv, h0]
  have h3 : Real.sqrt (⌈1 / ε⌉₊ : ℝ) ≤ ((2 * ⌈1 / Real.sqrt ε⌉₊ : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.le_ceil (1 / Real.sqrt ε)]
  exact Nat.ceil_le.mpr h3

/-- **The MNRS bound**: with `K = ⌈log₉ ⌈1/ε⌉⌉`, `T ≤ 2⌈1/√δ⌉`, update costs `≤ U`,

    q ≤ 110·S + 4490640·⌈1/√ε⌉·(⌈1/√δ⌉·U + C). -/
theorem WalkSetup.walkSearch_q_le_real (S : WalkSetup ι σ V) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {Tδ U : ℕ} (hTδ : 1 ≤ Tδ) (hT : S.T ≤ 2 * Tδ) (hA : S.updA.len ≤ U) (hB : S.updB.len ≤ U) :
    (S.walkSearch (Nat.clog 9 ⌈1 / ε⌉₊)).q
      ≤ 110 * S.prepV.len + 4490640 * (⌈1 / Real.sqrt ε⌉₊ * (Tδ * U + S.markV.len)) := by
  have hm : 0 < ⌈1 / ε⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have h3 := three_pow_clog_le hm
  have h6 := ceil_sqrt_ceil_le hε hε1
  have hR : 1 ≤ ⌈1 / Real.sqrt ε⌉₊ := by
    rw [Nat.one_le_ceil_iff]
    have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    have hs1 : Real.sqrt ε ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hε1
    rw [lt_div_iff₀ hs]; linarith
  have hq := S.walkSearch_q_le (Nat.clog 9 ⌈1 / ε⌉₊)
  set R := ⌈1 / Real.sqrt ε⌉₊ with hRdef
  set K := Nat.clog 9 ⌈1 / ε⌉₊ with hKdef
  set C := S.markV.len with hCdef
  have hρ : S.ρ ≤ 18 * (Tδ * U) := by
    rw [WalkSetup.ρ]
    have hT1 : S.T - 1 ≤ 2 * Tδ := by omega
    have h1 : S.updA.len ≤ Tδ * U := hA.trans (Nat.le_mul_of_pos_left U hTδ)
    have h2 : (S.T - 1) * (2 * S.updA.len + 2 * S.updB.len) ≤ (2 * Tδ) * (4 * U) :=
      Nat.mul_le_mul hT1 (by omega)
    nlinarith [h1, h2]
  have hpow : 3 ^ (K + 2) ≤ 54 * R := by
    rw [pow_add]
    have : 3 ^ K ≤ 6 * R := h3.trans (by omega)
    nlinarith
  have hbr : 2 * C + 21 * S.ρ ≤ 2 * C + 378 * (Tδ * U) := by omega
  have hmain : 2 * 3 ^ (K + 2) * (2 * C + 21 * S.ρ)
      ≤ 2 * (54 * R) * (2 * C + 378 * (Tδ * U)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hpow) hbr
  have hC : C ≤ R * C := Nat.le_mul_of_pos_left _ hR
  have hX : 2 * (54 * R) * (2 * C + 378 * (Tδ * U))
      = 216 * (R * C) + 40824 * (R * (Tδ * U)) := by ring
  have hRHS : 4490640 * (R * (Tδ * U + C))
      = 4490640 * (R * (Tδ * U)) + 4490640 * (R * C) := by ring
  rw [hX] at hmain
  rw [hRHS]
  omega

end QuantumQueryComplexity
