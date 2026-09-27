import QuantumQueryComplexity.Quantum.Amplitude.CleanControl
import QuantumQueryComplexity.Quantum.Amplitude.Tolerant
set_option synthInstance.maxSize 1600
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The compiled recursion, and its contract from support invariants

`chainR mark refl clean j` is the level-`j` routine of `Recursive.lean`, compiled:

    chainR 0 = identity
    chainR (j+1) = chainR j ; mark ; (chainR j)⁻¹ ; cleanRefl (clean j) (refl (j+1)) ; chainR j

(`;` is sequencing), and `stageR j = (chainR j)⁻¹ ; cleanRefl … ; chainR j` is the stage of the
tolerant protocol.  All of it lives on the one workspace `CtrlWork ι W`: the control bit and
the parking register are shared by every level.

* `chainLen C r`, `chainR_len`, `stageR_len` — exact costs: `q_{j+1} = 3q_j + C + r_{j+1}`,
  stage `2q_j + r_{j+1}`.  Inverses, the dirty branch and the marker are all charged.
* `chainR_run`, `stageR_run` — on a clean control bit they act as `chainA`, `chainM` for the
  operators `S = mark.run a`, `R (j+1) = cleanMat (clean j) ((refl (j+1)).run a)`.

`SearchInv` is the caller-facing contract, in terms of **supports**: a vector is *allowed at
level `j`* when it is supported on the set `F j` of basis states (encoded logical content,
reflection ancillas of the levels above `j` blank).  `SearchInv.chainOK` and
`SearchInv.contV_dom` derive everything `Recursive.lean` and `Tolerant.lean` assume.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W]

/-! ## Supports -/

section Supp

variable {H : Type} [Fintype H] [DecidableEq H]

/-- `w` is supported on the set `F` of basis states. -/
def SuppIn (F : Set H) (w : H → ℂ) : Prop := ∀ h, w h ≠ 0 → h ∈ F

/-- The operator `U` preserves the vectors supported on `F`. -/
def Preserves (U : Matrix H H ℂ) (F : Set H) : Prop := ∀ w, SuppIn F w → SuppIn F (U *ᵥ w)

lemma SuppIn.mono {F F' : Set H} (hF : F ⊆ F') {w : H → ℂ} (h : SuppIn F w) : SuppIn F' w :=
  fun x hx => hF (h x hx)

lemma SuppIn.sub {F : Set H} {v w : H → ℂ} (hv : SuppIn F v) (hw : SuppIn F w) :
    SuppIn F (v - w) := fun x hx => by
  by_contra hF
  have h1 : v x = 0 := by by_contra h; exact hF (hv x h)
  have h2 : w x = 0 := by by_contra h; exact hF (hw x h)
  exact hx (by rw [Pi.sub_apply, h1, h2, sub_zero])

variable {O : Type} (rd : H → O) (G : O → Prop) [DecidablePred G]

lemma SuppIn.goodPart {F : Set H} {w : H → ℂ} (h : SuppIn F w) : SuppIn F (goodPart rd G w) :=
  fun x hx => h x fun h0 => hx (by rw [goodPart_apply, h0, ite_self])

lemma SuppIn.badPart {F : Set H} {w : H → ℂ} (h : SuppIn F w) : SuppIn F (badPart rd G w) :=
  fun x hx => h x fun h0 => hx (by rw [badPart_apply, h0, ite_self])

lemma SuppIn.phaseFlip {F : Set H} {w : H → ℂ} (h : SuppIn F w) : SuppIn F (phaseFlip rd G w) :=
  (h.badPart rd G).sub (h.goodPart rd G)

lemma preserves_one (F : Set H) : Preserves (1 : Matrix H H ℂ) F := fun w hw => by
  rwa [Matrix.one_mulVec]

lemma Preserves.mul {U V : Matrix H H ℂ} {F : Set H} (hU : Preserves U F) (hV : Preserves V F) :
    Preserves (U * V) F := fun w hw => by
  rw [← Matrix.mulVec_mulVec]; exact hU _ (hV _ hw)

lemma Preserves.cleanMat {U : Matrix H H ℂ} {F : Set H} (hU : Preserves U F) (c : H → Bool) :
    Preserves (cleanMat c U) F := fun w hw => by
  rw [cleanMat_mulVec]
  exact (hU _ (hw.goodPart c (· = true))).sub (hw.badPart c (· = true))

end Supp

/-! ## The routines -/

/-- The compiled level routine. -/
noncomputable def chainR (mark : QRoutine ι σ W) (refl : ℕ → QRoutine ι σ W)
    (clean : ℕ → QBasis ι σ W → Bool) : ℕ → QRoutine ι σ (CtrlWork ι W)
  | 0 => QRoutine.identity
  | j + 1 => (chainR mark refl clean j).comp ((liftCtrl mark).comp
      ((chainR mark refl clean j).inv.comp
        ((cleanRefl (clean j) (refl (j + 1))).comp (chainR mark refl clean j))))

/-- The compiled stage of the tolerant protocol. -/
noncomputable def stageR (mark : QRoutine ι σ W) (refl : ℕ → QRoutine ι σ W)
    (clean : ℕ → QBasis ι σ W → Bool) (j : ℕ) : QRoutine ι σ (CtrlWork ι W) :=
  (chainR mark refl clean j).inv.comp
    ((cleanRefl (clean j) (refl (j + 1))).comp (chainR mark refl clean j))

/-- The query count of level `j`: marker cost `C`, reflection costs `r`. -/
def chainLen (C : ℕ) (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => 3 * chainLen C r j + C + r (j + 1)

variable (mark : QRoutine ι σ W) (refl : ℕ → QRoutine ι σ W) (clean : ℕ → QBasis ι σ W → Bool)

theorem chainR_len (j : ℕ) :
    (chainR mark refl clean j).len = chainLen mark.len (fun l => (refl l).len) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [chainR, QRoutine.comp_len, QRoutine.inv_len, liftCtrl_len, cleanRefl_len, ih,
        chainLen]
      ring

theorem stageR_len (j : ℕ) :
    (stageR mark refl clean j).len
      = 2 * chainLen mark.len (fun l => (refl l).len) j + (refl (j + 1)).len := by
  simp only [stageR, QRoutine.comp_len, QRoutine.inv_len, cleanRefl_len, chainR_len]
  ring

/-- The reflection operators of the abstract recursion. -/
noncomputable def cleanOps (a : ι → σ) : ℕ → Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ
  | 0 => 1
  | j + 1 => cleanMat (clean j) ((refl (j + 1)).run a)

variable {mark refl clean}

/-- A routine acting as a unitary on the clean sector has its inverse acting as the
adjoint. -/
lemma inv_run_embedCtrl_false {X : QRoutine ι σ (CtrlWork ι W)} {a : ι → σ}
    {A : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ} (hA : A ∈ Matrix.unitaryGroup _ ℂ)
    (hX : ∀ φ, X.run a *ᵥ embedCtrl false φ = embedCtrl false (A *ᵥ φ)) (φ : QBasis ι σ W → ℂ) :
    X.inv.run a *ᵥ embedCtrl false φ = embedCtrl false (Aᴴ *ᵥ φ) := by
  have hAA : A * Aᴴ = 1 := by
    have := conjTranspose_mul_self_of_unitary (conjTranspose_mem_qUnitary hA)
    rwa [Matrix.conjTranspose_conjTranspose] at this
  have h1 := hX (Aᴴ *ᵥ φ)
  rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec] at h1
  rw [QRoutine.inv_run, ← h1, Matrix.mulVec_mulVec,
    conjTranspose_mul_self_of_unitary (X.run_mem_unitaryGroup a), Matrix.one_mulVec]

section Run

variable {a : ι → σ}
  (hcomm : ∀ j, (refl (j + 1)).run a * flagProj (clean j) = flagProj (clean j) * (refl (j + 1)).run a)

include hcomm

lemma cleanOps_mem_unitaryGroup (j : ℕ) :
    cleanOps refl clean a j ∈ Matrix.unitaryGroup (QBasis ι σ W) ℂ := by
  cases j with
  | zero => exact one_mem_qUnitary
  | succ j => exact cleanMat_mem_unitaryGroup ((refl (j + 1)).run_mem_unitaryGroup a) (hcomm j)

/-- **The compiled level routine is the abstract level operator.** -/
theorem chainR_run (j : ℕ) (φ : QBasis ι σ W → ℂ) :
    (chainR mark refl clean j).run a *ᵥ embedCtrl false φ
      = embedCtrl false (chainA (mark.run a) (cleanOps refl clean a) j *ᵥ φ) := by
  induction j generalizing φ with
  | zero =>
      rw [chainR, QRoutine.identity_run, Matrix.one_mulVec, chainA, Matrix.one_mulVec]
  | succ j ih =>
      have hAu := chainA_mem_unitaryGroup (mark.run_mem_unitaryGroup a)
        (cleanOps_mem_unitaryGroup hcomm) j
      have hinv := inv_run_embedCtrl_false hAu ih
      rw [chainR, QRoutine.comp_run, QRoutine.comp_run, QRoutine.comp_run, QRoutine.comp_run,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, ih, liftCtrl_run, hinv, cleanRefl_run _ _ _ (hcomm j), ih,
        chainA]
      simp only [Matrix.mulVec_mulVec, cleanOps, Matrix.mul_assoc]

/-- **The compiled stage is the abstract approximate reflection `M_j`.** -/
theorem stageR_run (j : ℕ) (φ : QBasis ι σ W → ℂ) :
    (stageR mark refl clean j).run a *ᵥ embedCtrl false φ
      = embedCtrl false (chainM (mark.run a) (cleanOps refl clean a) j *ᵥ φ) := by
  have hAu := chainA_mem_unitaryGroup (mark.run_mem_unitaryGroup a)
    (cleanOps_mem_unitaryGroup hcomm) j
  have hinv := inv_run_embedCtrl_false hAu (chainR_run (mark := mark) hcomm j)
  rw [stageR, QRoutine.comp_run, QRoutine.comp_run, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hinv, cleanRefl_run _ _ _ (hcomm j), chainR_run hcomm, chainM]
  simp only [Matrix.mulVec_mulVec, cleanOps, Matrix.mul_assoc]

end Run

end QuantumQueryComplexity
