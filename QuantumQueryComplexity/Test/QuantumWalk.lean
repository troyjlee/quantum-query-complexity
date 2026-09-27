import QuantumQueryComplexity.Quantum.Amplitude.ApproxSearch
import QuantumQueryComplexity.Quantum.Amplitude.Routine
import QuantumQueryComplexity.Quantum.Amplitude.NoisyRefl
import QuantumQueryComplexity.Quantum.RobustSearch.Defs
import QuantumQueryComplexity.Quantum.Walk.MNRS
import QuantumQueryComplexity.Quantum.Walk.Chain

set_option synthInstance.maxSize 3200
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Acceptance: search with an approximate reflection

1. The contract and its conjugation: `A R A†` is an approximate reflection about the actual
   `A s` with the *same* `β`; one step is `|√m' − |3−4m|√m| ≤ 2β√m`.
2. **The dirty-history branch**: `cleanRefl c R` is `R` where the flag holds and `−1` elsewhere,
   and costs `R.len` on both branches.
3. **Finite histories against sequential projectors**: the continuing vector is the product of
   projectors and stage operators, unnormalized; mass is conserved stage by stage (zero-
   probability branches included); the compiled pass realizes it, `Pr[none] = ‖ν‖²`, and an
   unmarked value is never read.
4. The compiled search: budget, no invalid vertex, `≥ 2/3` under the marked-mass promise,
   `none` surely on the empty set.  **The setup cost enters the budget with no level-dependent
   multiplier.**
5. **Exact reflections as a specialization**: for an exact phase marker and the exact
   reflection `prepRefl` (`β = 0`, every flag trivially clean, every vector allowed) the
   contract holds, so the theorems apply to ordinary amplitude amplification data.
6. **The contract restricted to the levels in use** (`SearchInvUpTo L`, `K + 1 ≤ L`), with its
   extension lemma.
7. **A reflection with a genuine error and nontrivial clean/dirty ancillas**: a qubit
   `s = (3/5)|0⟩ + (4/5)|1⟩`, marked `|1⟩`, two ancilla bits.  The level-`j` reflection is
   `noisyRefl s t t'_j`, where `t'_j` is `t = s^⊥` with ancilla `j` rotated by
   `sin = 2n/(n²+1)`, `n = 2^13`: it fixes `s` exactly, is *not* the exact reflection (it leaks
   amplitude into ancilla `j`), and has error `≤ 4‖t'−t‖ ≤ 2^{-10}`.  Level `2` is controlled on
   ancilla `1` being blank; supports `{both blank} ⊆ {ancilla 2 blank} ⊆ everything`.  The
   finite contract `SearchInvUpTo 2` is proved and the search theorem applied at `K = 1`.
8. **Quantum-walk search (MNRS)**: from `WalkOK` — actual routines with their semantic
   equations on the input — the final theorems on the actual `QAlg` output probabilities of the
   input-independent `walkSearch`, and the budget in all of `S, U, C, ε, δ`.  The spectral
   layer: the gap on the invariant subspace only (the complement of the row spaces is fixed
   by the walk and no gap is claimed there), the complete-resampling chain (rank one, gap `1`),
   the lazy two-state chain (absolute gap `2p`, the proof needing `p ≤ 1/2`), the one-vertex
   chain.
-/

namespace QuantumQueryComplexity
namespace QuantumWalkAcceptance

open scoped Matrix
open Matrix

variable {ι σ W V : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]

/-! ## 1. The contract -/

section Contract

variable {H O : Type} [Fintype H] [DecidableEq H]

theorem acceptance_conj {R : Matrix H H ℂ} {s : H → ℂ} {D : Set (H → ℂ)} {β : ℝ}
    (h : IsApproxRefl R s D β) {A : Matrix H H ℂ} (hA : A ∈ Matrix.unitaryGroup H ℂ) :
    IsApproxRefl (A * R * Aᴴ) (A *ᵥ s) {χ | Aᴴ *ᵥ χ ∈ D} β :=
  h.conj hA

theorem acceptance_step {rd : H → O} {G : O → Prop} [DecidablePred G] {ψ : H → ℂ}
    (hψ : IsQState ψ) {M : Matrix H H ℂ} {D : Set (H → ℂ)} {β : ℝ} (hM : IsApproxRefl M ψ D β)
    (hβ : 0 ≤ β) (hD : phaseFlip rd G ψ ∈ D) :
    |Real.sqrt (goodProb rd G (M *ᵥ phaseFlip rd G ψ))
        - |3 - 4 * goodProb rd G ψ| * Real.sqrt (goodProb rd G ψ)|
      ≤ 2 * β * Real.sqrt (goodProb rd G ψ) :=
  abs_sqrt_step_le hψ hM hβ hD

end Contract

/-! ## 2. The dirty-history branch -/

theorem acceptance_cleanRefl (c : QBasis ι σ W → Bool) (R : QRoutine ι σ W) (a : ι → σ)
    (hcomm : R.run a * flagProj c = flagProj c * R.run a) (φ : QBasis ι σ W → ℂ) :
    (cleanRefl c R).len = R.len
    ∧ (cleanRefl c R).run a *ᵥ embedCtrl false φ
        = embedCtrl false (R.run a *ᵥ goodPart c (· = true) φ - badPart c (· = true) φ) := by
  refine ⟨cleanRefl_len c R, ?_⟩
  rw [cleanRefl_run c R a hcomm, cleanMat_mulVec]

/-- On a dirty vector it is exactly `−1`. -/
example (c : QBasis ι σ W → Bool) (U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ)
    (φ : QBasis ι σ W → ℂ) (hφ : goodPart c (· = true) φ = 0) : cleanMat c U *ᵥ φ = -φ := by
  have hb : badPart c (· = true) φ = φ := by
    have := goodPart_add_badPart c (· = true) φ
    rwa [hφ, zero_add] at this
  rw [cleanMat_mulVec, hφ, hb, Matrix.mulVec_zero, zero_sub]

/-! ## 3. Histories against sequential projectors -/

section History

variable {H O : Type} [Fintype H] [DecidableEq H] (rd : H → O) (G : O → Prop) [DecidablePred G]
  (s : H → ℂ) (S : Matrix H H ℂ) (R : ℕ → Matrix H H ℂ)

/-- The continuing vector is the product of projectors and stage operators. -/
example (j : ℕ) :
    contV rd G s S R 0 = badPart rd G s
    ∧ contV rd G s S R (j + 1) = badPart rd G (chainM S R j *ᵥ contV rd G s S R j)
    ∧ chainM S R j = chainA S R j * R (j + 1) * (chainA S R j)ᴴ :=
  ⟨rfl, rfl, rfl⟩

/-- Mass conservation, stage by stage; nothing is normalized. -/
theorem acceptance_mass {rd : H → O} {G : O → Prop} [DecidablePred G] {s : H → ℂ}
    {S : Matrix H H ℂ} {R : ℕ → Matrix H H ℂ} {β : ℕ → ℝ} {Dom : ℕ → Set (H → ℂ)}
    (h : ChainOK rd G s S R β Dom) (j : ℕ) :
    qNormSq (contV rd G s S R (j + 1))
        + qNormSq (goodPart rd G (chainM S R j *ᵥ contV rd G s S R j))
      = qNormSq (contV rd G s S R j) :=
  h.qNormSq_contV_succ j

end History

section Pass

variable {prep mark : QRoutine ι σ W} {refl : ℕ → QRoutine ι σ W}
  {clean : ℕ → QBasis ι σ W → Bool} {vtx : QBasis ι σ W → V} {init : QBasis ι σ W → ℂ}
  {hinit : IsQState init} {Marked : V → Prop} [DecidablePred Marked] {a : ι → σ} {β : ℕ → ℝ}
  {F : ℕ → Set (QBasis ι σ W)}

/-- The compiled pass realizes the continuing vector under the empty history. -/
theorem acceptance_pass (h : SearchInv vtx Marked mark refl clean a (prep.run a *ᵥ init) β F)
    (K : ℕ) :
    (passTrial prep init hinit mark refl clean vtx K).pr a none
        = qNormSq (contV vtx Marked (prep.run a *ᵥ init) (mark.run a) (cleanOps refl clean a)
            (K + 1))
    ∧ ∀ v, ¬ Marked v → (passTrial prep init hinit mark refl clean vtx K).pr a (some v) = 0 :=
  ⟨passTrial_pr_none h K, fun _ hv => passTrial_pr_unmarked h K hv⟩

/-! ## 4. The compiled search -/

theorem acceptance_approxSearch
    (h : SearchInv vtx Marked mark refl clean a (prep.run a *ᵥ init) β F) (K : ℕ) :
    (approxSearch prep init hinit mark refl clean vtx K).q
        = 110 * passLen prep.len mark.len (fun l => (refl l).len) (K + 1)
    ∧ (∀ v, ¬ Marked v → (approxSearch prep init hinit mark refl clean vtx K).pr a (some v) = 0)
    ∧ (∀ ε : ℝ, 0 < ε → ε ≤ goodProb vtx Marked (prep.run a *ᵥ init) → ⌈1 / ε⌉₊ ≤ 9 ^ K →
        2 / 3 ≤ (approxSearch prep init hinit mark refl clean vtx K).good Marked a)
    ∧ ((∀ v, ¬ Marked v) →
        (approxSearch prep init hinit mark refl clean vtx K).pr a none = 1) :=
  ⟨approxSearch_q prep init hinit mark refl clean vtx K,
   fun _ hv => approxSearch_pr_unmarked h K hv,
   fun _ hε hm hK => two_thirds_le_approxSearch h hε hm hK,
   fun hno => approxSearch_pr_none_of_empty h hno K⟩

end Pass

/-- **No level-dependent multiplier on the setup cost**: it enters a pass once. -/
theorem passLen_setup (S C : ℕ) (r : ℕ → ℕ) (j : ℕ) :
    passLen S C r j = S + passLen 0 C r j := by
  induction j with
  | zero => simp [passLen]
  | succ j ih => rw [passLen, passLen, ih]; ring

/-- With reflections of cost `ρ·(j+9)`: one setup plus `O(3^K (C + ρ))`, no logarithm. -/
example {S C ρ : ℕ} {r : ℕ → ℕ} (hr : ∀ j, r j ≤ ρ * (j + 9)) (K : ℕ) :
    passLen S C r K + 2 * (2 * C + 21 * ρ) ≤ S + C + 2 * 3 ^ (K + 1) * (2 * C + 21 * ρ) :=
  passLen_le hr K

/-! ## 5. Exact reflections as a specialization -/

section Exact

variable {X : Type} [Fintype X] (P : AmpSetup ι σ W V) {read : X → ι → σ} {Good : X → V → Prop}
  [∀ x, DecidablePred (Good x)]

/-- For an exact phase marker and the exact reflection about the prepared state, the contract
holds with `β = 0`, trivial flags and no restriction on supports. -/
theorem searchInv_exact (hmark : IsPhaseMarker P.mark read Good P.readout) (x : X) :
    SearchInv P.readout (Good x) P.mark (fun _ => P.prepRefl) (fun _ _ => true) (read x)
      (P.prep.run (read x) *ᵥ P.init) (fun _ => 0) (fun _ => Set.univ) where
  unit := P.isQState_prepared (read x)
  mono := fun _ => le_rfl
  s_supp := fun _ _ => Set.mem_univ _
  s_clean := fun _ => by
    funext q; rw [goodPart_apply, if_pos rfl]
  mark_flip := fun _ w _ => hmark x w
  refl_comm := fun _ => by
    have : flagProj (fun _ : QBasis ι σ W => true) = 1 := by
      rw [flagProj, ← Matrix.diagonal_one]; congr 1
    rw [this, Matrix.mul_one, Matrix.one_mul]
  refl_pres := fun _ _ _ _ _ _ _ => Set.mem_univ _
  refl_pres_adj := fun _ _ _ _ _ _ _ => Set.mem_univ _
  β_nonneg := fun _ => le_rfl
  β_le := fun _ => by positivity
  refl_approx := fun _ => by
    have hrun : P.prepRefl.run (read x) = stateRefl (P.prep.run (read x) *ᵥ P.init) :=
      P.prepRefl_run (read x)
    rw [hrun]
    exact ⟨(isApproxRefl_stateRefl (P.isQState_prepared (read x))).fix,
      fun w _ => by rw [sub_self, qNorm_zero, zero_mul]⟩

/-- Hence the tolerant search applies to ordinary amplification data: with only a lower bound
`ε` on the success probability, `≥ 2/3`, never an invalid output, one preparation per pass. -/
theorem acceptance_exact (hmark : IsPhaseMarker P.mark read Good P.readout) (x : X) {ε : ℝ}
    (hε : 0 < ε) (hp : ε ≤ P.succProb read Good x) {K : ℕ} (hK : ⌈1 / ε⌉₊ ≤ 9 ^ K) :
    2 / 3 ≤ (approxSearch P.prep P.init P.init_isQState P.mark (fun _ => P.prepRefl)
        (fun _ _ => true) P.readout K).good (Good x) (read x)
    ∧ ∀ v, ¬ Good x v →
        (approxSearch P.prep P.init P.init_isQState P.mark (fun _ => P.prepRefl)
          (fun _ _ => true) P.readout K).pr (read x) (some v) = 0 :=
  ⟨two_thirds_le_approxSearch (searchInv_exact P hmark x) hε hp hK,
   fun _ hv => approxSearch_pr_unmarked (searchInv_exact P hmark x) K hv⟩

end Exact

/-! ## 6. The contract restricted to the levels in use -/

section UpTo

variable {prep mark : QRoutine ι σ W} {refl : ℕ → QRoutine ι σ W}
  {clean : ℕ → QBasis ι σ W → Bool} {vtx : QBasis ι σ W → V} {init : QBasis ι σ W → ℂ}
  {hinit : IsQState init} {Marked : V → Prop} [DecidablePred Marked] {a : ι → σ} {β : ℕ → ℝ}
  {F : ℕ → Set (QBasis ι σ W)} {L K : ℕ}

theorem acceptance_upTo
    (h : SearchInvUpTo vtx Marked L mark refl clean a (prep.run a *ᵥ init) β F)
    (hKL : K + 1 ≤ L) :
    (∀ v, ¬ Marked v → (approxSearch prep init hinit mark refl clean vtx K).pr a (some v) = 0)
    ∧ (∀ ε : ℝ, 0 < ε → ε ≤ goodProb vtx Marked (prep.run a *ᵥ init) → ⌈1 / ε⌉₊ ≤ 9 ^ K →
        2 / 3 ≤ (approxSearch prep init hinit mark refl clean vtx K).good Marked a)
    ∧ ((∀ v, ¬ Marked v) →
        (approxSearch prep init hinit mark refl clean vtx K).pr a none = 1) :=
  ⟨fun _ hv => approxSearch_pr_unmarked_upTo h hKL hv,
   fun _ hε hm hK => two_thirds_le_approxSearch_upTo h hKL hε hm hK,
   fun hno => approxSearch_pr_none_of_empty_upTo h hKL hno⟩

end UpTo

/-! ## 7. A reflection with a genuine error and dirty ancillas -/

namespace Noisy

/-- Ancilla `1`, ancilla `2`, the logical qubit. -/
abbrev Wx : Type := Bool × Bool × Fin 2

/-- A vector with blank query registers. -/
noncomputable def vec (f : Wx → ℂ) : QBasis ι σ Wx → ℂ :=
  fun p => if p.1 = none ∧ p.2.1 = none then f p.2.2 else 0

lemma sum_blank {M : Type} [AddCommMonoid M] (Ψ : QBasis ι σ Wx → M)
    (h : ∀ p, ¬ (p.1 = none ∧ p.2.1 = none) → Ψ p = 0) :
    ∑ p, Ψ p = ∑ w : Wx, Ψ (none, none, w) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single none]
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single none]
    · intro t _ ht
      exact Finset.sum_eq_zero fun w _ => h _ (by simp [ht])
    · intro hn; exact absurd (Finset.mem_univ _) hn
  · intro k _ hk
    exact Finset.sum_eq_zero fun y _ => h _ (by simp [hk])
  · intro hn; exact absurd (Finset.mem_univ _) hn

lemma qInner_vec (f g : Wx → ℂ) :
    qInner (vec (ι := ι) (σ := σ) f) (vec g) = ∑ w : Wx, star (f w) * g w := by
  rw [qInner_def, sum_blank]
  · simp [vec]
  · intro p hp; simp [vec, hp]

lemma isQState_of_qInner {H : Type} [Fintype H] [DecidableEq H] {v : H → ℂ} (h : qInner v v = 1) :
    IsQState v := by
  rw [qInner_self] at h
  exact_mod_cast h

lemma vec_sub (f g : Wx → ℂ) : vec (ι := ι) (σ := σ) f - vec g = vec (f - g) := by
  funext p; simp only [vec, Pi.sub_apply]; split_ifs <;> simp

lemma suppIn_vec {f : Wx → ℂ} {P : Wx → Prop} (h : ∀ w, f w ≠ 0 → P w) :
    SuppIn {p : QBasis ι σ Wx | P p.2.2} (vec f) := fun p hp => by
  simp only [vec] at hp
  split_ifs at hp with hb
  · exact h _ hp
  · exact absurd rfl hp

lemma goodPart_vec {f : Wx → ℂ} {c : Wx → Bool} (h : ∀ w, f w ≠ 0 → c w = true) :
    goodPart (fun p : QBasis ι σ Wx => c p.2.2) (· = true) (vec f) = vec f := by
  funext p
  rw [goodPart_apply]
  by_cases hc : c p.2.2 = true
  · rw [if_pos hc]
  · rw [if_neg hc]
    simp only [vec]
    split_ifs
    · by_contra hne; exact hc (h _ (Ne.symm hne))
    · rfl

/-- The rotation of an ancilla: `cos = (n²−1)/(n²+1)`, `sin = 2n/(n²+1)`, `n = 2^13`. -/
noncomputable def κ : ℂ := 67108863 / 67108865
noncomputable def μ : ℂ := 16384 / 67108865

/-- `s = (3/5)|0⟩ + (4/5)|1⟩`, ancillas blank. -/
noncomputable def fs : Wx → ℂ := fun w =>
  if w.1 = false ∧ w.2.1 = false then (if w.2.2 = 0 then 3 / 5 else 4 / 5) else 0

/-- `t = s^⊥`, ancillas blank. -/
noncomputable def ft : Wx → ℂ := fun w =>
  if w.1 = false ∧ w.2.1 = false then (if w.2.2 = 0 then -(4 / 5) else 3 / 5) else 0

/-- `t` with ancilla `1` rotated. -/
noncomputable def ft1 : Wx → ℂ := fun w =>
  if w.2.1 = false then (if w.1 then μ else κ) * (if w.2.2 = 0 then -(4 / 5) else 3 / 5) else 0

/-- `t` with ancilla `2` rotated. -/
noncomputable def ft2 : Wx → ℂ := fun w =>
  if w.1 = false then (if w.2.1 then μ else κ) * (if w.2.2 = 0 then -(4 / 5) else 3 / 5) else 0

local notation "sv" => vec (ι := ι) (σ := σ) fs
local notation "tv" => vec (ι := ι) (σ := σ) ft
local notation "t1v" => vec (ι := ι) (σ := σ) ft1
local notation "t2v" => vec (ι := ι) (σ := σ) ft2

lemma sum_Wx (g : Wx → ℂ) :
    ∑ w : Wx, g w = g (false, false, 0) + g (false, false, 1) + g (false, true, 0)
      + g (false, true, 1) + g (true, false, 0) + g (true, false, 1) + g (true, true, 0)
      + g (true, true, 1) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_two]
  ring

lemma unit_s : IsQState sv := isQState_of_qInner (by
  rw [qInner_vec, sum_Wx]; simp [fs]; norm_num)

lemma unit_t : IsQState tv := isQState_of_qInner (by
  rw [qInner_vec, sum_Wx]; simp [ft]; norm_num)

lemma unit_t1 : IsQState t1v := isQState_of_qInner (by
  rw [qInner_vec, sum_Wx]; simp [ft1, κ, μ]; norm_num)

lemma unit_t2 : IsQState t2v := isQState_of_qInner (by
  rw [qInner_vec, sum_Wx]; simp [ft2, κ, μ]; norm_num)

lemma orth_t : qInner tv sv = 0 := by rw [qInner_vec, sum_Wx]; simp [fs, ft]; norm_num
lemma orth_t1 : qInner t1v sv = 0 := by rw [qInner_vec, sum_Wx]; simp [fs, ft1]; ring
lemma orth_t2 : qInner t2v sv = 0 := by rw [qInner_vec, sum_Wx]; simp [fs, ft2]; ring

/-- `‖t'_j − t‖ ≤ 2^{-12}`. -/
lemma dist_t1 : qNorm (t1v - tv) ≤ (1 / 2) ^ 12 := by
  refine qNorm_le_of_qNormSq_le (by positivity) ?_
  have h : qInner (t1v - tv) (t1v - tv) = ((4 / 67108865 : ℝ) : ℂ) := by
    rw [vec_sub, qInner_vec, sum_Wx]; simp [ft, ft1, κ, μ]; norm_num
  rw [qInner_self] at h
  have h' : qNormSq (t1v - tv) = 4 / 67108865 := by exact_mod_cast h
  rw [h']; norm_num

lemma dist_t2 : qNorm (t2v - tv) ≤ (1 / 2) ^ 12 := by
  refine qNorm_le_of_qNormSq_le (by positivity) ?_
  have h : qInner (t2v - tv) (t2v - tv) = ((4 / 67108865 : ℝ) : ℂ) := by
    rw [vec_sub, qInner_vec, sum_Wx]; simp [ft, ft2, κ, μ]; norm_num
  rw [qInner_self] at h
  have h' : qNormSq (t2v - tv) = 4 / 67108865 := by exact_mod_cast h
  rw [h']; norm_num

/-- The marked flag: the logical qubit reads `1`. -/
def flagq : QBasis ι σ Wx → Bool := fun p => decide (p.2.2.2.2 = 1)

/-- The level-`j` reflection: a genuine error, leaking into ancilla `j`. -/
noncomputable def reflN : ℕ → QRoutine ι σ Wx
  | 1 => QRoutine.ofUnitary (noisyRefl sv tv t1v)
      (noisyRefl_mem_unitaryGroup unit_s unit_t unit_t1)
  | 2 => QRoutine.ofUnitary (noisyRefl sv tv t2v)
      (noisyRefl_mem_unitaryGroup unit_s unit_t unit_t2)
  | _ => QRoutine.identity

/-- Level `2` is controlled on ancilla `1` being blank. -/
def cleanN : ℕ → QBasis ι σ Wx → Bool
  | 1 => fun p => !p.2.2.1
  | _ => fun _ => true

/-- `{both ancillas blank} ⊆ {ancilla 2 blank} ⊆ everything`. -/
def FN : ℕ → Set (QBasis ι σ Wx)
  | 0 => {p | p.2.2.1 = false ∧ p.2.2.2.1 = false}
  | 1 => {p | p.2.2.2.1 = false}
  | _ => Set.univ

lemma fs_blank (w : Wx) (h : fs w ≠ 0) : w.1 = false ∧ w.2.1 = false := by
  by_contra hc; exact h (by simp only [fs, if_neg hc])

lemma ft_blank (w : Wx) (h : ft w ≠ 0) : w.1 = false ∧ w.2.1 = false := by
  by_contra hc; exact h (by simp only [ft, if_neg hc])

lemma ft1_blank (w : Wx) (h : ft1 w ≠ 0) : w.2.1 = false := by
  by_contra hc; exact h (by simp only [ft1, if_neg hc])

lemma ft2_blank (w : Wx) (h : ft2 w ≠ 0) : w.1 = false := by
  by_contra hc; exact h (by simp only [ft2, if_neg hc])

/-- **The error is genuine**: the level-1 reflection is not the exact reflection — applied to
the clean vector `t` it leaves amplitude in the dirty ancilla. -/
theorem reflN_ne_exact :
    noisyRefl sv tv t1v *ᵥ tv ≠ stateRefl sv *ᵥ tv := by
  intro h
  -- strip `stateRefl s`, then `stateRefl t`: it would follow that `stateRefl t1 t = t`
  have h1 := congrArg (fun x => stateRefl sv *ᵥ x) h
  simp only [noisyRefl, ← Matrix.mulVec_mulVec, stateRefl_stateRefl_mulVec unit_s] at h1
  have h2 := congrArg (fun x => stateRefl tv *ᵥ x) h1
  simp only [stateRefl_stateRefl_mulVec unit_t, stateRefl_mulVec_self unit_t] at h2
  -- evaluate at the dirty basis state `(a₁, a₂, q) = (1, 0, 1)`
  have h3 := congrFun h2 ((none, none, (true, false, 1)) : QBasis ι σ Wx)
  rw [stateRefl_mulVec, Pi.sub_apply, Pi.smul_apply, qInner_vec, sum_Wx] at h3
  simp [vec, ft, ft1, κ, μ] at h3
  norm_num at h3

/-- **The finite contract**, levels `1, 2`. -/
theorem contract (a : ι → σ) :
    SearchInvUpTo flagq (· = true) 2 (signMarker flagq) reflN cleanN a sv
      (fun j => (1 / 2) ^ (j + 8)) FN where
  unit := unit_s
  mono := fun j hj => by
    interval_cases j
    · exact fun p hp => hp.2
    · exact fun p _ => Set.mem_univ p
  s_supp := suppIn_vec (P := fun w => w.1 = false ∧ w.2.1 = false) fs_blank
  s_clean := fun j hj => by
    interval_cases j
    · funext q; rw [goodPart_apply, if_pos (show cleanN 0 q = true from rfl)]
    · exact goodPart_vec (c := fun w => !w.1) fun w hw => by simp [(fs_blank w hw).1]
  mark_flip := fun j _ w _ => signMarker_run flagq a w
  refl_comm := fun j hj => by
    interval_cases j
    · change _ * flagProj (fun _ => true) = flagProj (fun _ => true) * _
      rw [flagProj_true, Matrix.mul_one, Matrix.one_mul]
    · change (reflN 2).run a * _ = _ * (reflN 2).run a
      rw [reflN, QRoutine.ofUnitary_run]
      exact noisyRefl_comm_flagProj
        (goodPart_vec (c := fun w => !w.1) fun w hw => by simp [(fs_blank w hw).1])
        (goodPart_vec (c := fun w => !w.1) fun w hw => by simp [(ft_blank w hw).1])
        (goodPart_vec (c := fun w => !w.1) fun w hw => by simp [ft2_blank w hw])
  refl_pres := fun j l hjl hl => by
    have hl' : l = 1 ∨ l = 2 := by omega
    rcases hl' with rfl | rfl
    · have hj : j = 0 := by omega
      subst hj
      change Preserves ((reflN 1).run a) _
      rw [reflN, QRoutine.ofUnitary_run]
      exact preserves_noisyRefl
        (suppIn_vec (P := fun w => w.2.1 = false) fun w hw => (fs_blank w hw).2)
        (suppIn_vec (P := fun w => w.2.1 = false) fun w hw => (ft_blank w hw).2)
        (suppIn_vec (P := fun w => w.2.1 = false) ft1_blank)
    · exact fun w _ p _ => Set.mem_univ p
  refl_pres_adj := fun j l hjl hl => by
    have hl' : l = 1 ∨ l = 2 := by omega
    rcases hl' with rfl | rfl
    · have hj : j = 0 := by omega
      subst hj
      change Preserves ((reflN 1).run a)ᴴ _
      rw [reflN, QRoutine.ofUnitary_run]
      exact preserves_noisyRefl_adj unit_s unit_t unit_t1
        (suppIn_vec (P := fun w => w.2.1 = false) fun w hw => (fs_blank w hw).2)
        (suppIn_vec (P := fun w => w.2.1 = false) fun w hw => (ft_blank w hw).2)
        (suppIn_vec (P := fun w => w.2.1 = false) ft1_blank)
    · exact fun w _ p _ => Set.mem_univ p
  β_nonneg := fun j _ => by positivity
  β_le := fun j _ => le_rfl
  refl_approx := fun j hj => by
    interval_cases j
    · change IsApproxRefl ((reflN 1).run a) _ _ _
      rw [reflN, QRoutine.ofUnitary_run]
      exact (isApproxRefl_noisyRefl unit_s unit_t unit_t1 orth_t orth_t1 dist_t1).mono
        (Set.subset_univ _) (by norm_num)
    · change IsApproxRefl ((reflN 2).run a) _ _ _
      rw [reflN, QRoutine.ofUnitary_run]
      exact (isApproxRefl_noisyRefl unit_s unit_t unit_t2 orth_t orth_t2 dist_t2).mono
        (Set.subset_univ _) (by norm_num)

/-- The marked mass of the start state is `16/25`. -/
lemma goodProb_s : goodProb (flagq (ι := ι) (σ := σ)) (· = true) sv = 16 / 25 := by
  rw [goodProb_eq_sum_ite, sum_blank]
  · have : ∀ w : Wx, (if flagq ((none, none, w) : QBasis ι σ Wx) = true
        then Complex.normSq (sv (none, none, w)) else 0)
        = if w.2.2 = 1 then Complex.normSq (fs w) else 0 := fun w => by
      simp [flagq, vec]
    simp only [this]
    have hsum : ∀ g : Wx → ℝ, ∑ w : Wx, g w = g (false, false, 0) + g (false, false, 1)
        + g (false, true, 0) + g (false, true, 1) + g (true, false, 0) + g (true, false, 1)
        + g (true, true, 0) + g (true, true, 1) := fun g => by
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_two]; ring
    rw [hsum]
    simp [fs]
    norm_num
  · intro p hp; simp [vec, hp]

/-- **The search theorem applies**: zero-query preparation, noisy reflections with dirty
ancillas, `K = 1`, and a marked state is found with probability at least `2/3`; an unmarked
one never. -/
theorem noisy_search (a : ι → σ) :
    2 / 3 ≤ (approxSearch (QRoutine.identity (ι := ι) (σ := σ)) sv unit_s (signMarker flagq)
        reflN cleanN flagq 1).good (· = true) a
    ∧ (approxSearch (QRoutine.identity (ι := ι) (σ := σ)) sv unit_s (signMarker flagq)
        reflN cleanN flagq 1).pr a (some false) = 0 := by
  have hs : (QRoutine.identity (ι := ι) (σ := σ) (W := Wx)).run a *ᵥ sv = sv := by
    rw [QRoutine.identity_run, Matrix.one_mulVec]
  have hc := contract (ι := ι) (σ := σ) a
  rw [← hs] at hc
  refine ⟨two_thirds_le_approxSearch_upTo hc le_rfl (ε := 16 / 25) (by norm_num)
    (by rw [hs, goodProb_s]) ?_, approxSearch_pr_unmarked_upTo hc le_rfl (by simp)⟩
  rw [Nat.ceil_le]; norm_num

end Noisy

/-! ## 8. Quantum-walk search -/

section Walk

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The walk theorem on the actual algorithm**, from the routines' semantics on `x`. -/
theorem acceptance_walk (S : WalkSetup ι σ V) (x : ι → σ) (Marked : V → Prop)
    [DecidablePred Marked] (h : WalkOK S x Marked) (K : ℕ) :
    (∀ v, ¬ Marked v → (S.walkSearch K).pr x (some v) = 0)
    ∧ (∀ ε : ℝ, 0 < ε → ε ≤ S.markedMass Marked → ⌈1 / ε⌉₊ ≤ 9 ^ K →
        2 / 3 ≤ (S.walkSearch K).good Marked x)
    ∧ ((∀ v, ¬ Marked v) → (S.walkSearch K).pr x none = 1) :=
  ⟨fun _ hv => h.walkSearch_pr_unmarked K hv, fun _ hε hm hK => h.two_thirds_le_walkSearch K hε hm hK,
   fun hno => h.walkSearch_pr_none_of_empty K hno⟩

/-- **The budget contains all of `S, U, C, ε, δ`** (through `T ≤ 2⌈1/√δ⌉`) and nothing
depends on the input. -/
theorem acceptance_walk_budget (S : WalkSetup ι σ V) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {Tδ U : ℕ} (hTδ : 1 ≤ Tδ) (hT : S.T ≤ 2 * Tδ) (hA : S.updA.len ≤ U) (hB : S.updB.len ≤ U) :
    (S.walkSearch (Nat.clog 9 ⌈1 / ε⌉₊)).q
      ≤ 110 * S.prepV.len + 4490640 * (⌈1 / Real.sqrt ε⌉₊ * (Tδ * U + S.markV.len)) :=
  S.walkSearch_q_le_real hε hε1 hTδ hT hA hB

/-- The walk routine costs `2U_A + 2U_B` and `walkSearch` is a term in the setup alone. -/
example (S : WalkSetup ι σ V) : S.walkR.len = 2 * S.updA.len + 2 * S.updB.len := S.walkR_len

/-- **The gap is on the invariant subspace only.**  The stationary vector is fixed, and the
gap statement `WalkFam.gap` takes `v ∈ K`; nothing is claimed for the complement of the row
spaces. -/
example {H : Type} [Fintype H] [DecidableEq H] {a b : V → (H → ℂ)} {D : Matrix V V ℂ}
    {r : V → ℂ} {δ : ℝ} (h : WalkFam a b D r δ) (v : H → ℂ) (hv : v ∈ h.K) :
    WalkFam.walkOp a b *ᵥ h.s = h.s ∧ 4 * δ * qNormSq v ≤ qNormSq ((1 - WalkFam.walkOp a b) *ᵥ v) :=
  ⟨h.walkOp_s, h.gap hv⟩

/-- Complete resampling: certified gap `1`. -/
example (π : V → ℝ) (hπ : ∀ u, 0 < π u) (hs : ∑ u, π u = 1) (y : V → ℂ)
    (hy : qInner (resampling π hπ hs).r y = 0) :
    qNormSq ((resampling π hπ hs).disc *ᵥ y) ≤ (1 - 1) ^ 2 * qNormSq y :=
  resampling_gap π hπ hs y hy

/-- The lazy two-state chain at `p = 1/4`: absolute gap `1/2`. -/
example (y : Bool → ℂ) (hy : qInner (lazyTwo (1 / 4) (by norm_num) (by norm_num)).r y = 0) :
    qNormSq ((lazyTwo (1 / 4) (by norm_num) (by norm_num)).disc *ᵥ y)
      ≤ (1 - 1 / 2) ^ 2 * qNormSq y := by
  have := lazy_gap (1 / 4) (by norm_num) (by norm_num) y hy
  norm_num at this ⊢
  exact this

/-- The one-vertex chain: resampling on `Unit`, `π = 1`. -/
example : (resampling (fun _ : Unit => (1 : ℝ)) (fun _ => one_pos) (by simp)).r = fun _ => 1 := by
  funext u; simp [RevChain.r, resampling]

end Walk

end QuantumWalkAcceptance
end QuantumQueryComplexity
