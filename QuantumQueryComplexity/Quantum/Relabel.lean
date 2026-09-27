import QuantumQueryComplexity.Quantum.Complexity
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Renaming the oracle alphabet costs nothing

A bijection `e : σ ≃ σ'` of answer alphabets is a *relabelling*: the oracle
that answers `e (read x i)` is the same oracle read through a change of
names.  Transporting an algorithm along the induced basis bijection
`QBasis ι σ W ≃ QBasis ι σ' W` (`basisRelabel`) therefore costs **zero
queries** — every step becomes a `submatrix` along the bijection, which
preserves unitarity, and the transposition oracles correspond because
conjugating a transposition by a bijection transposes the images
(`oracleMap_relabel`).

Headline: `qQueryOn_relabel`,

    qQueryOn (fun x i => e (read x i)) f ε = qQueryOn read f ε,

an equality, not an inequality.  This is what lets a statement about an
*allowed alphabet* `G` be read as a statement about its image `σ(G)` under a
relabelling, rather than only about a common abstract label type.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ σ' O W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [DecidableEq σ] [Fintype σ'] [DecidableEq σ'] [Fintype W] [DecidableEq W]

/-! ## Generic transport along a basis bijection -/

lemma qNormSq_comp_equiv {H H' : Type} [Fintype H] [DecidableEq H]
    [Fintype H'] [DecidableEq H'] (f : H' ≃ H) (ψ : H → ℂ) :
    qNormSq (fun p => ψ (f p)) = qNormSq ψ := by
  rw [qNormSq_def, qNormSq_def]
  exact Equiv.sum_comp f fun h => Complex.normSq (ψ h)

lemma qProb_comp_equiv {H H' : Type} [Fintype H] [DecidableEq H]
    [Fintype H'] [DecidableEq H'] [DecidableEq O]
    (f : H' ≃ H) (r : H → O) (ψ : H → ℂ) (o : O) :
    qProb (fun p => r (f p)) (fun p => ψ (f p)) o = qProb r ψ o := by
  rw [qProb, qProb]
  exact Equiv.sum_comp f fun h => if r h = o then Complex.normSq (ψ h) else 0

lemma submatrix_mem_unitaryGroup {H H' : Type} [Fintype H] [DecidableEq H]
    [Fintype H'] [DecidableEq H'] (f : H' ≃ H) {M : Matrix H H ℂ}
    (hM : M ∈ Matrix.unitaryGroup H ℂ) :
    M.submatrix f f ∈ Matrix.unitaryGroup H' ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    conjTranspose_mul_self_of_unitary hM, Matrix.submatrix_one_equiv]

lemma submatrix_mulVec_comp {H H' : Type} [Fintype H] [Fintype H']
    [DecidableEq H] [DecidableEq H'] (f : H' ≃ H) (M : Matrix H H ℂ)
    (ψ : H → ℂ) :
    M.submatrix f f *ᵥ (fun p => ψ (f p)) = fun p => (M *ᵥ ψ) (f p) := by
  have hcomp : (fun p => ψ (f p)) ∘ (f.symm : H → H') = ψ := by
    funext q
    show ψ (f (f.symm q)) = ψ q
    rw [Equiv.apply_symm_apply]
  rw [Matrix.submatrix_mulVec_equiv, hcomp]
  rfl

/-! ## The alphabet relabelling -/

/-- A bijection of alphabets renames the answer register. -/
def basisRelabel (e : σ ≃ σ') : QBasis ι σ W ≃ QBasis ι σ' W :=
  (Equiv.refl (Option ι)).prodCongr (e.optionCongr.prodCongr (Equiv.refl W))

@[simp] lemma basisRelabel_apply (e : σ ≃ σ') (i : Option ι) (s : Option σ)
    (w : W) :
    basisRelabel (W := W) e ((i, s, w) : QBasis ι σ W) = (i, s.map e, w) := rfl

/-- Conjugating a transposition by a bijection transposes the images. -/
lemma option_map_swap (e : σ ≃ σ') (c : σ) (s : Option σ) :
    Option.map e (Equiv.swap none (some c) s)
      = Equiv.swap none (some (e c)) (Option.map e s) := by
  cases s with
  | none =>
      rw [Equiv.swap_apply_left]
      change (some (e c) : Option σ') = Equiv.swap none (some (e c)) none
      rw [Equiv.swap_apply_left]
  | some x =>
      by_cases hx : x = c
      · subst hx
        rw [Equiv.swap_apply_right]
        change (none : Option σ') = Equiv.swap none (some (e x)) (some (e x))
        rw [Equiv.swap_apply_right]
      · have h1 : (some x : Option σ) ≠ none := Option.some_ne_none x
        have h2 : (some x : Option σ) ≠ some c :=
          fun h => hx (Option.some_injective _ h)
        have h3 : (some (e x) : Option σ') ≠ none := Option.some_ne_none _
        have h4 : (some (e x) : Option σ') ≠ some (e c) :=
          fun h => hx (e.injective (Option.some_injective _ h))
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
        change (some (e x) : Option σ')
          = Equiv.swap none (some (e c)) (some (e x))
        rw [Equiv.swap_apply_of_ne_of_ne h3 h4]

/-- **The relabelled oracle is the oracle relabelled.** -/
lemma oracleMap_relabel (e : σ ≃ σ') (a : ι → σ) (p : QBasis ι σ W) :
    oracleMap (fun i => e (a i)) (basisRelabel e p)
      = basisRelabel e (oracleMap a p) := by
  obtain ⟨i, s, w⟩ := p
  cases i with
  | none => rfl
  | some i =>
      rw [basisRelabel_apply, oracleMap_some, oracleMap_some,
        basisRelabel_apply, option_map_swap]

lemma oracleMap_relabel_symm (e : σ ≃ σ') (a : ι → σ)
    (p : QBasis ι σ' W) :
    (basisRelabel (W := W) e).symm (oracleMap (fun i => e (a i)) p)
      = oracleMap a ((basisRelabel e).symm p) := by
  conv_lhs => rw [show p = basisRelabel (W := W) e ((basisRelabel e).symm p) from
    (Equiv.apply_symm_apply _ _).symm]
  rw [oracleMap_relabel, Equiv.symm_apply_apply]

/-! ## The transported algorithm -/

variable [DecidableEq O]

/-- The same algorithm, run against the relabelled oracle. -/
def QAlg.relabel (e : σ ≃ σ') (A : QAlg ι σ O W) : QAlg ι σ' O W where
  init p := A.init ((basisRelabel e).symm p)
  init_isQState := by
    rw [IsQState, qNormSq_comp_equiv]
    exact A.init_isQState
  step t := (A.step t).submatrix (basisRelabel e).symm (basisRelabel e).symm
  step_unitary t := submatrix_mem_unitaryGroup _ (A.step_unitary t)
  readout p := A.readout ((basisRelabel e).symm p)

lemma relabel_state (e : σ ≃ σ') (A : QAlg ι σ O W) (a : ι → σ) (t : ℕ) :
    (A.relabel e).state (fun i => e (a i)) t
      = fun p => A.state a t ((basisRelabel e).symm p) := by
  induction t with
  | zero =>
      show (A.step 0).submatrix (basisRelabel e).symm (basisRelabel e).symm
          *ᵥ (fun p => A.init ((basisRelabel e).symm p)) = _
      rw [submatrix_mulVec_comp]
      rfl
  | succ t ih =>
      show (A.step (t + 1)).submatrix (basisRelabel e).symm
            (basisRelabel e).symm
          *ᵥ (oracleMat (fun i => e (a i))
            *ᵥ (A.relabel e).state (fun i => e (a i)) t) = _
      rw [ih]
      have horacle : oracleMat (fun i => e (a i))
            *ᵥ (fun p => A.state a t ((basisRelabel e).symm p))
          = fun p => (oracleMat a *ᵥ A.state a t)
              ((basisRelabel e).symm p) := by
        funext p
        rw [oracleMat_mulVec_apply, oracleMat_mulVec_apply,
          oracleMap_relabel_symm]
      rw [horacle, submatrix_mulVec_comp]
      rfl

/-! ## Zero-query invariance -/

variable {X : Type} [Fintype X]

theorem computesWithErrorOn_relabel (e : σ ≃ σ') {A : QAlg ι σ O W} {q : ℕ}
    {read : X → ι → σ} {f : X → O} {ε : ℝ}
    (h : ComputesWithErrorOn A q read f ε) :
    ComputesWithErrorOn (A.relabel e) q (fun x i => e (read x i)) f ε := by
  intro x
  rw [QAlg.prob, relabel_state]
  show 1 - ε ≤ qProb (fun p => A.readout ((basisRelabel e).symm p))
    (fun p => A.state (read x) q ((basisRelabel e).symm p)) (f x)
  rw [qProb_comp_equiv]
  exact h x

theorem queryCounts_relabel (e : σ ≃ σ') (read : X → ι → σ) (f : X → O)
    (ε : ℝ) :
    QueryCounts read f ε ⊆ QueryCounts (fun x i => e (read x i)) f ε := by
  rintro q ⟨W', hW, hW', A, hA⟩
  exact ⟨W', hW, hW', A.relabel e, computesWithErrorOn_relabel e hA⟩

theorem qQueryOn_relabel_le (e : σ ≃ σ') (read : X → ι → σ) (f : X → O)
    {ε : ℝ} (hne : (QueryCounts read f ε).Nonempty) :
    qQueryOn (fun x i => e (read x i)) f ε ≤ qQueryOn read f ε :=
  Nat.sInf_le (queryCounts_relabel e read f ε (Nat.sInf_mem hne))

/-- **Renaming the oracle alphabet is free**, in both directions. -/
theorem qQueryOn_relabel (e : σ ≃ σ') (read : X → ι → σ) (f : X → O) {ε : ℝ}
    (hne : (QueryCounts read f ε).Nonempty) :
    qQueryOn (fun x i => e (read x i)) f ε = qQueryOn read f ε := by
  refine le_antisymm (qQueryOn_relabel_le e read f hne) ?_
  have hback := qQueryOn_relabel_le e.symm (fun x i => e (read x i)) f
    (hne.mono (queryCounts_relabel e read f ε))
  have hid : (fun x i => e.symm (e (read x i))) = read := by
    funext x i
    rw [Equiv.symm_apply_apply]
  rwa [hid] at hback

end QuantumQueryComplexity
