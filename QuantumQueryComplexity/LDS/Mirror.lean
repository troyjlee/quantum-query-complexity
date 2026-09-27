import QuantumQueryComplexity.LDS.Search
import QuantumQueryComplexity.LDS.Node
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The truncation anchor `ρ` as a mirrored binary search

`LDS/Search.lean` gives the dual solution for `Λ_a(j)`, the leftmost distinct
start.  A node also needs the mirror `ρ_b(l)`, the rightmost end `r ≤ b` with
`[l, r]` distinct: it is the *truncation* descriptor (both
the normalization's `j₂` and the per-part `y'_ℓ` of Corollary 35).

No second binary search is needed.  Reversing the word is an injective
change of query coordinates, so `HasDualOn.pullbackCoord` moves a solution
written for the reversed word back to the original promise at the *same*
cost, and

    ρ_b(l) = rev (Λ_{rev b}(rev l))    on the reversed word

recodes one anchor into the other — an injective recoding, hence free
(`ofKer`). The reversal here is used inside a single node's descriptor;
the recursion itself needs no orientation step.
-/

namespace QuantumQueryComplexity

variable {n : ℕ} {σ : Type} [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X] [DecidableEq X]

/-- **The mirror identity**: `ρ` of a word is `Λ` of its reversal, read
backwards. -/
theorem rhoFun_eq_revIdx_lambdaFun (β : Fin n → σ) {l b : Fin n} (hlb : l ≤ b) :
    rhoFun β l b = revIdx (lambdaFun (revWord β) (revIdx b) (revIdx l)) := by
  have hrev : revIdx b ≤ revIdx l := revIdx_le_revIdx.mpr hlb
  have hmem := lambdaFun_mem (α := revWord β) hrev
  rw [mem_lambdaSet] at hmem
  obtain ⟨⟨h1, h2⟩, hd⟩ := hmem
  -- the candidate `revIdx (Λ …)` is a distinct end in `[l, b]`
  have hd' : IsDistinct β l (revIdx (lambdaFun (revWord β) (revIdx b) (revIdx l))) := by
    have := isDistinct_revWord.mp hd
    rwa [revIdx_revIdx] at this
  have hlr : l ≤ revIdx (lambdaFun (revWord β) (revIdx b) (revIdx l)) := by
    have := revIdx_le_revIdx.mpr h2
    rwa [revIdx_revIdx] at this
  have hrb : revIdx (lambdaFun (revWord β) (revIdx b) (revIdx l)) ≤ b := by
    have := revIdx_le_revIdx.mpr h1
    rwa [revIdx_revIdx] at this
  refine le_antisymm ?_ (le_rhoFun_of_isDistinct hlr hrb hd')
  -- and it is the largest such: minimality of `Λ` on the reversed word
  have hmax := rhoFun_mem (α := β) hlb
  rw [mem_rhoSet] at hmax
  obtain ⟨⟨hm1, hm2⟩, hmd⟩ := hmax
  have hdr : IsDistinct (revWord β) (revIdx (rhoFun β l b)) (revIdx l) := by
    rw [isDistinct_revWord]
    simp only [revIdx_revIdx]
    exact hmd
  have := lambdaFun_le_of_isDistinct (α := revWord β)
    (revIdx_le_revIdx.mpr hm2) (revIdx_le_revIdx.mpr hm1) hdr
  have h := revIdx_le_revIdx.mpr this
  rwa [revIdx_revIdx] at h

/-- **The truncation dual**: on any promise, `ρ_b(l)` has a feasible dual
solution of cost `L · 8 s^{2/3}`, where `s = b - l + 1 ≤ 2 ^ L` — the same
bound as the anchor `Λ`, by reversal. -/
theorem hasDualOn_rhoFun (read : X → Fin n → σ) {l b : Fin n} (hlb : l ≤ b)
    {L : ℕ} (hL : winLen l b ≤ 2 ^ L) :
    HasDualOn read (fun x => rhoFun (read x) l b)
      ((L : ℝ) * (8 * (winLen l b : ℝ) ^ ((2 : ℝ) / 3))) := by
  have hrev : revIdx b ≤ revIdx l := revIdx_le_revIdx.mpr hlb
  have hwin : winLen (revIdx b) (revIdx l) = winLen l b := winLen_revIdx l b
  -- solve `Λ` on the reversed promise …
  have hlam := hasDualOn_lambdaFun (σ := σ)
    (read := fun x k => read x (revIdx k)) (a := revIdx b) (j := revIdx l) hrev
    (L := L) (by rw [hwin]; exact hL)
  rw [hwin] at hlam
  -- … which is a solution on the original promise, at the same cost
  have hpull := hlam.pullbackCoord (e := fun k : Fin n => revIdx k) revIdx_injective
  -- … and reading the answer backwards is an injective recoding
  refine hpull.ofKer fun x y => ?_
  have hx : rhoFun (read x) l b
      = revIdx (lambdaFun (fun k => read x (revIdx k)) (revIdx b) (revIdx l)) :=
    rhoFun_eq_revIdx_lambdaFun _ hlb
  have hy : rhoFun (read y) l b
      = revIdx (lambdaFun (fun k => read y (revIdx k)) (revIdx b) (revIdx l)) :=
    rhoFun_eq_revIdx_lambdaFun _ hlb
  constructor
  · intro h
    rw [hx, hy, h]
  · intro h
    rw [hx, hy] at h
    exact revIdx_injective h

end QuantumQueryComplexity
