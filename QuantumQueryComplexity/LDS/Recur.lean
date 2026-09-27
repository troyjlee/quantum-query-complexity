import QuantumQueryComplexity.LDS.Child
import QuantumQueryComplexity.LDS.Mirror
import QuantumQueryComplexity.Promise.Max
import QuantumQueryComplexity.Max.Defs
import Mathlib.Data.Fintype.Option

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# One step of the node recursion

This file assembles the combinatorics of a single
recursion step into the one identity the dual side consumes:

    bldsFun g β  =  max ( glue run , max over parts ( offset + child ) ).

The pieces are already proved; what is done here is the *normalization
bookkeeping* that connects them.

* `bldsFun_eq_normalized` — a raw node equals the glue run maxed with the
  node problem of the **normalized arena word** `normWord β g`, a contiguous
  sub-word `[Λ(g), ρ(g)]` re-indexed by `intervalEmb`.  Both anchors are
  single `Λ`/`ρ` computations, so on a descriptor fiber the whole reduction
  is by constants.
* `isDistinct_normWord_glue` — the normalized word satisfies the glue
  invariant, which is exactly the hypothesis Corollary 35 needs.
* `bldsFun_eq_maxFun_children` — the two combined, with the sup over parts
  rewritten as a `maxFun` over `Option (Fin h)`: the `none` slot carries the
  glue run (a constant on the fiber) and slot `ℓ` carries its child.  That is
  the shape `HasDualOn.maxMapFam` consumes, with value maps
  `(transcript, value) ↦ offset ℓ + value`.

The recursion normalizes, splits, and recurses, with a base case on the arena
size. It needs neither an orientation step nor a separate `n₂ = 1` search.
-/

namespace QuantumQueryComplexity

variable {m : ℕ} {σ : Type*} [DecidableEq σ]

/-! ## A maximum with one distinguished slot -/

/-- Splitting a `maxFun` over `Option P` into its `none` slot and the rest.
The `none` slot is where a node parks the constant part of its value. -/
lemma maxFun_option_elim {P : Type*} [Fintype P] {A : Type*} [LinearOrder A]
    [OrderBot A] (c : A) (f : P → A) :
    maxFun (fun s : Option P => s.elim c f) = max c (Finset.univ.sup f) := by
  refine le_antisymm (maxFun_le fun s => ?_) (max_le ?_ (Finset.sup_le fun p _ => ?_))
  · cases s with
    | none => exact le_max_left _ _
    | some p =>
      have h1 : f p ≤ Finset.univ.sup f := Finset.le_sup (Finset.mem_univ p)
      exact le_trans h1 (le_max_right c (Finset.univ.sup f))
  · exact le_maxFun (fun s : Option P => s.elim c f) none
  · exact le_maxFun (fun s : Option P => s.elim c f) (some p)

/-! ## The normalized arena -/

/-- The left end of the normalized arena: the longest distinct run ending at
the glue. -/
def normA (β : Fin m → σ) (g : Fin m) : Fin m := lambdaFun β (firstIdx g) g

/-- The right end of the normalized arena: the longest distinct run starting
at the glue. -/
def normB (β : Fin m → σ) (g : Fin m) : Fin m := rhoFun β g (lastIdx g)

lemma normA_le (β : Fin m → σ) (g : Fin m) : (normA β g : ℕ) ≤ (g : ℕ) :=
  lambdaFun_le (firstIdx_le' g g)

lemma le_normB (β : Fin m → σ) (g : Fin m) : (g : ℕ) ≤ (normB β g : ℕ) :=
  le_rhoFun (le_lastIdx g g)

/-- The size of the normalized arena. -/
def normSize (β : Fin m → σ) (g : Fin m) : ℕ := (normB β g : ℕ) + 1 - (normA β g : ℕ)

lemma normSize_pos (β : Fin m → σ) (g : Fin m) : 0 < normSize β g := by
  have h1 := normA_le β g
  have h2 := le_normB β g
  simp only [normSize]
  omega

lemma normSize_le (β : Fin m → σ) (g : Fin m) : normSize β g ≤ m := by
  have := (normB β g).isLt
  simp only [normSize]
  omega

/-- The normalized arena word. -/
def normWord (β : Fin m → σ) (g : Fin m) : Fin (normSize β g) → σ :=
  β ∘ intervalEmb (normA β g : ℕ) (normB β g : ℕ) (normB β g).isLt

/-- The glue, in normalized coordinates. -/
def normGlue (β : Fin m → σ) (g : Fin m) : Fin (normSize β g) :=
  ⟨(g : ℕ) - (normA β g : ℕ), by
    have h1 := normA_le β g
    have h2 := le_normB β g
    simp only [normSize]
    omega⟩

@[simp] lemma normGlue_val (β : Fin m → σ) (g : Fin m) :
    (normGlue β g : ℕ) = (g : ℕ) - (normA β g : ℕ) := rfl

/-- The run that dies at the glue (`n₂'`): the longest
distinct run starting one past the glue.  One `ρ` computation, hence again a
constant on a descriptor fiber. -/
def glueRun (β : Fin m → σ) (g : Fin m) : ℕ :=
  if h : (g : ℕ) + 1 < m then
    winLen (⟨(g : ℕ) + 1, h⟩ : Fin m) (rhoFun β ⟨(g : ℕ) + 1, h⟩ (lastIdx g))
  else 0

/-- **Normalization** (in the recursion's coordinates):
a raw node splits into its glue run and the node problem of the normalized
arena word. -/
theorem bldsFun_eq_normalized (β : Fin m → σ) (g : Fin m) :
    bldsFun g β = max (glueRun β g) (bldsFun (normGlue β g) (normWord β g)) := by
  have hA : firstIdx g ≤ g := firstIdx_le' g g
  have hB : g ≤ lastIdx g := le_lastIdx g g
  have hAv := normA_le β g
  have hBv := le_normB β g
  -- the glue run is the `afterGlue` term
  have hglue : afterGlue (firstIdx g) (lastIdx g) g β = glueRun β g := by
    by_cases hg : (g : ℕ) + 1 < m
    · rw [glueRun, dif_pos hg]
      refine afterGlue_eq hA rfl ?_ β
      rw [Fin.le_def, lastIdx_val]
      omega
    · rw [glueRun, dif_neg hg]
      refine le_antisymm (Finset.sup_le fun p _ => ?_) (Nat.zero_le _)
      split
      · rename_i hc
        have h1 := hc.2.1
        have h2 := hc.2.2.2.2
        rw [Fin.le_def, lastIdx_val] at h1
        have := g.isLt
        simp only [winLen]
        omega
      · exact Nat.zero_le _
  -- the normalized window, re-indexed
  have hsub : bldsIn (normA β g) (normB β g) g β
      = bldsFun (normGlue β g) (normWord β g) :=
    bldsIn_eq_bldsFun (by rw [Fin.le_def]; exact hAv) (by rw [Fin.le_def]; exact hBv)
  rw [bldsFun_eq_bldsIn g β, bldsIn_normalize hA hB β, hglue]
  exact congrArg _ hsub

/-- **The glue invariant of the normalized word** — the hypothesis Corollary
35 runs on. -/
theorem isDistinct_normWord_glue (β : Fin m → σ) (g : Fin m) :
    IsDistinct (normWord β g) (normGlue β g) (lastIdx (normGlue β g)) := by
  have hAv := normA_le β g
  have hBv := le_normB β g
  have hpos := normSize_pos β g
  have heg : intervalEmb (normA β g : ℕ) (normB β g : ℕ) (normB β g).isLt
      (normGlue β g) = g := by
    apply Fin.ext
    show (normA β g : ℕ) + ((g : ℕ) - (normA β g : ℕ)) = (g : ℕ)
    omega
  have heb : intervalEmb (normA β g : ℕ) (normB β g : ℕ) (normB β g).isLt
      (lastIdx (normGlue β g)) = normB β g := by
    apply Fin.ext
    show (normA β g : ℕ) + ((normB β g : ℕ) + 1 - (normA β g : ℕ) - 1)
      = (normB β g : ℕ)
    omega
  have key : IsDistinct β
      (intervalEmb (normA β g : ℕ) (normB β g : ℕ) (normB β g).isLt (normGlue β g))
      (intervalEmb (normA β g : ℕ) (normB β g : ℕ) (normB β g).isLt
        (lastIdx (normGlue β g))) := by
    rw [heg, heb]
    exact isDistinct_rhoFun (le_lastIdx g g)
  exact (isDistinct_intervalEmb (normB β g).isLt _ _).mpr key

/-- **The left invariant of the normalized word**: its left part is one
distinct run. -/
theorem isDistinct_normWord_left (β : Fin m → σ) (g : Fin m) :
    IsDistinct (normWord β g) (firstIdx (normGlue β g)) (normGlue β g) := by
  have hAv := normA_le β g
  have hBv := le_normB β g
  have hef : intervalEmb (normA β g : ℕ) (normB β g : ℕ) (normB β g).isLt
      (firstIdx (normGlue β g)) = normA β g := by
    apply Fin.ext
    show (normA β g : ℕ) + 0 = (normA β g : ℕ)
    omega
  have heg : intervalEmb (normA β g : ℕ) (normB β g : ℕ) (normB β g).isLt
      (normGlue β g) = g := by
    apply Fin.ext
    show (normA β g : ℕ) + ((g : ℕ) - (normA β g : ℕ)) = (g : ℕ)
    omega
  have key : IsDistinct β
      (intervalEmb (normA β g : ℕ) (normB β g : ℕ) (normB β g).isLt
        (firstIdx (normGlue β g)))
      (intervalEmb (normA β g : ℕ) (normB β g : ℕ) (normB β g).isLt
        (normGlue β g)) := by
    rw [hef, heg]
    exact isDistinct_lambdaFun (firstIdx_le' g g)
  exact (isDistinct_intervalEmb (normB β g).isLt _ _).mpr key

/-- Hence the anchor of the normalized word is its first index: normalization
is idempotent on the left. -/
theorem lambdaFun_normWord_eq (β : Fin m → σ) (g : Fin m) :
    lambdaFun (normWord β g) (firstIdx (normGlue β g)) (normGlue β g)
      = firstIdx (normGlue β g) :=
  le_antisymm
    (lambdaFun_le_of_isDistinct le_rfl (firstIdx_le' _ _) (isDistinct_normWord_left β g))
    (le_lambdaFun (firstIdx_le' _ _))

/-- **The empty-right-part node** — the recursion's other base case: when the
glue is the last index of the normalized arena, the node value is the whole
arena, with no children. -/
theorem bldsFun_normWord_of_glue_last (β : Fin m → σ) (g : Fin m)
    (hlast : (normGlue β g : ℕ) + 1 = normSize β g) :
    bldsFun (normGlue β g) (normWord β g) = normSize β g := by
  rw [bldsFun_of_glue_last hlast, lambdaFun_normWord_eq]
  simp only [winLen, firstIdx_val]
  omega

/-! ## The node identity -/

/-- **One recursion step** .  With the right part of the
normalized arena covered by parts `[x ℓ, y ℓ]` and the per-part anchors `p`,
caps `q` and truncations `y'` of Corollary 35, a node is the maximum of its
glue run and its shifted children — in the `maxFun`-over-`Option` shape that
`HasDualOn.maxMapFam` consumes.

All the hypotheses are the ones `LDS/Child.lean` asks for, transported to the
normalized word; on a descriptor fiber every quantity named here except the
children is a constant. -/
theorem bldsFun_eq_maxFun_children (β : Fin m → σ) (g : Fin m) {hh : ℕ}
    {x y p q qs y' : Fin hh → Fin (normSize β g)}
    (hgx : ∀ ℓ, (normGlue β g : ℕ) < (x ℓ : ℕ))
    (hxy : ∀ ℓ, (x ℓ : ℕ) ≤ (y ℓ : ℕ))
    (hpdist : ∀ ℓ, IsDistinct (normWord β g) (p ℓ) (predIdx (x ℓ)))
    (hpmin : ∀ ℓ, ∀ i : Fin (normSize β g), (i : ℕ) ≤ (x ℓ : ℕ) - 1 →
      IsDistinct (normWord β g) i (predIdx (x ℓ)) → (p ℓ : ℕ) ≤ (i : ℕ))
    (hpq : ∀ ℓ, (p ℓ : ℕ) ≤ (q ℓ : ℕ))
    (hqcap : ∀ ℓ, (q ℓ : ℕ) = min (normGlue β g : ℕ)
      ((p ℓ : ℕ) + winLen (x ℓ) (y ℓ) - 1))
    (hqs : ∀ ℓ, (qs ℓ : ℕ) = (q ℓ : ℕ) + 1)
    (hy'dist : ∀ ℓ, IsDistinct (normWord β g) (qs ℓ) (y' ℓ))
    (hy'le : ∀ ℓ, (y' ℓ : ℕ) ≤ (y ℓ : ℕ))
    (hy'max : ∀ ℓ, ∀ r : Fin (normSize β g), (r : ℕ) ≤ (y ℓ : ℕ) →
      IsDistinct (normWord β g) (qs ℓ) r → (r : ℕ) ≤ (y' ℓ : ℕ))
    (hcover : ∀ r : Fin (normSize β g), (normGlue β g : ℕ) ≤ (r : ℕ) →
      ∃ ℓ, (x ℓ : ℕ) - 1 ≤ (r : ℕ) ∧ (r : ℕ) ≤ (y ℓ : ℕ)) :
    bldsFun g β
      = maxFun fun s : Option (Fin hh) => s.elim (glueRun β g) fun ℓ =>
          ((x ℓ : ℕ) - (q ℓ : ℕ) - 1)
            + childVal (p ℓ : ℕ) (q ℓ : ℕ) (x ℓ : ℕ) (y' ℓ : ℕ) (hpq ℓ) (q ℓ).isLt
                (y' ℓ).isLt (normWord β g) := by
  rw [maxFun_option_elim, bldsFun_eq_normalized β g]
  exact congrArg _ (bldsFun_eq_sup_children (isDistinct_normWord_glue β g) hgx hxy
    hpdist hpmin hpq hqcap hqs hy'dist hy'le hy'max hcover)

/-! ## The split

The split uses parts of size `t`, as
many as it takes: the arity is whatever `hh` covers `n₂ ≤ hh · t`, which
avoids dividing by a variable arity and makes every boundary a plain multiple
of `t`.  All six quantities are clamped, hence total; the hypotheses
(`1 ≤ t`, every part nonempty, the parts covering) are used only in the
proofs.

The part sizes are `≤ t`, so `childSize_le_two_mul` bounds every child by
`2t` — that, and nothing about the `n₁/n₂` balance, is what shrinks the
recursion. -/

section Split

/-- The left end of part `ℓ`. -/
def splitLo (G : Fin m) (t ℓ : ℕ) : Fin m :=
  ⟨min ((G : ℕ) + 1 + ℓ * t) (m - 1), by have := G.isLt; omega⟩

/-- The right end of part `ℓ`. -/
def splitHi (G : Fin m) (t ℓ : ℕ) : Fin m :=
  ⟨min ((G : ℕ) + (ℓ + 1) * t) (m - 1), by have := G.isLt; omega⟩

/-- The anchor of part `ℓ` (`p_ℓ = Λ(x_ℓ - 1)`). -/
def splitP (W : Fin m → σ) (G : Fin m) (t ℓ : ℕ) : Fin m :=
  lambdaFun W (firstIdx G) (predIdx (splitLo G t ℓ))

/-- The cap of part `ℓ` (`q_ℓ = min(g, p_ℓ + t_ℓ - 1)`). -/
def splitQ (W : Fin m → σ) (G : Fin m) (t ℓ : ℕ) : Fin m :=
  ⟨min (G : ℕ) ((splitP W G t ℓ : ℕ) + winLen (splitLo G t ℓ) (splitHi G t ℓ) - 1),
    by have := G.isLt; omega⟩

/-- The successor of the cap, clamped. -/
def splitQs (W : Fin m → σ) (G : Fin m) (t ℓ : ℕ) : Fin m :=
  ⟨min ((splitQ W G t ℓ : ℕ) + 1) (m - 1), by have := G.isLt; omega⟩

/-- The truncation of part `ℓ` (`y'_ℓ = ρ_{y_ℓ}(q_ℓ + 1)`). -/
def splitY (W : Fin m → σ) (G : Fin m) (t ℓ : ℕ) : Fin m :=
  rhoFun W (splitQs W G t ℓ) (splitHi G t ℓ)

variable {W : Fin m → σ} {G : Fin m} {t : ℕ}

lemma splitLo_val_min (G : Fin m) (t ℓ : ℕ) :
    (splitLo G t ℓ : ℕ) = min ((G : ℕ) + 1 + ℓ * t) (m - 1) := rfl

lemma splitQ_val_min (W : Fin m → σ) (G : Fin m) (t ℓ : ℕ) :
    (splitQ W G t ℓ : ℕ)
      = min (G : ℕ) ((splitP W G t ℓ : ℕ)
          + winLen (splitLo G t ℓ) (splitHi G t ℓ) - 1) := rfl

lemma splitQs_val_min (W : Fin m → σ) (G : Fin m) (t ℓ : ℕ) :
    (splitQs W G t ℓ : ℕ) = min ((splitQ W G t ℓ : ℕ) + 1) (m - 1) := rfl

lemma splitLo_val {ℓ : ℕ} (hℓ : ℓ * t < m - 1 - (G : ℕ)) :
    (splitLo G t ℓ : ℕ) = (G : ℕ) + 1 + ℓ * t := by
  have := G.isLt
  rw [splitLo_val_min]
  omega

lemma splitHi_val (ℓ : ℕ) :
    (splitHi G t ℓ : ℕ) = min ((G : ℕ) + (ℓ + 1) * t) (m - 1) := rfl

lemma lt_splitLo {ℓ : ℕ} (hℓ : ℓ * t < m - 1 - (G : ℕ)) :
    (G : ℕ) < (splitLo G t ℓ : ℕ) := by
  rw [splitLo_val hℓ]
  omega

lemma splitLo_le_splitHi {ℓ : ℕ} (ht : 1 ≤ t) (hℓ : ℓ * t < m - 1 - (G : ℕ)) :
    (splitLo G t ℓ : ℕ) ≤ (splitHi G t ℓ : ℕ) := by
  have := G.isLt
  have hmul : (ℓ + 1) * t = ℓ * t + t := by ring
  rw [splitLo_val hℓ, splitHi_val, hmul]
  omega

/-- Part `ℓ` is no longer than `t`. -/
lemma winLen_split_le {ℓ : ℕ} (hℓ : ℓ * t < m - 1 - (G : ℕ)) :
    winLen (splitLo G t ℓ) (splitHi G t ℓ) ≤ t := by
  have hmul : (ℓ + 1) * t = ℓ * t + t := by ring
  simp only [winLen]
  rw [splitLo_val hℓ, splitHi_val, hmul]
  omega

/-- **The anchor cannot escape the left part** — the glue invariant again. -/
lemma splitP_le_glue (hglue : IsDistinct W G (lastIdx G)) {ℓ : ℕ}
    (hℓ : ℓ * t < m - 1 - (G : ℕ)) : (splitP W G t ℓ : ℕ) ≤ (G : ℕ) := by
  have hlo := lt_splitLo (G := G) (t := t) hℓ
  have hG : G ≤ predIdx (splitLo G t ℓ) := by
    rw [Fin.le_def, predIdx_val]
    omega
  have := lambdaFun_le_of_isDistinct (α := W) (a := firstIdx G) (i := G)
    (j := predIdx (splitLo G t ℓ)) (firstIdx_le' G G) hG
    (hglue.mono le_rfl (le_lastIdx G _))
  rw [Fin.le_def] at this
  exact this

lemma splitQ_le_glue (W : Fin m → σ) (G : Fin m) (t ℓ : ℕ) :
    (splitQ W G t ℓ : ℕ) ≤ (G : ℕ) := by
  rw [splitQ_val_min]
  omega

lemma splitP_le_splitQ (hglue : IsDistinct W G (lastIdx G)) (ht : 1 ≤ t) {ℓ : ℕ}
    (hℓ : ℓ * t < m - 1 - (G : ℕ)) :
    (splitP W G t ℓ : ℕ) ≤ (splitQ W G t ℓ : ℕ) := by
  have h1 := splitP_le_glue hglue hℓ
  have h2 := splitLo_le_splitHi (G := G) ht hℓ
  have hw : 1 ≤ winLen (splitLo G t ℓ) (splitHi G t ℓ) := by
    simp only [winLen]
    omega
  rw [splitQ_val_min]
  omega

lemma splitQs_val {ℓ : ℕ} (hℓ : ℓ * t < m - 1 - (G : ℕ)) :
    (splitQs W G t ℓ : ℕ) = (splitQ W G t ℓ : ℕ) + 1 := by
  have hq := splitQ_le_glue W G t ℓ
  have hlo := lt_splitLo (G := G) (t := t) hℓ
  have := (splitLo G t ℓ).isLt
  rw [splitQs_val_min]
  omega

/-- **The parts cover the right endpoints past the glue.**  This is the only
place the division shows up, and it is a single `Nat.div_add_mod`. -/
lemma split_cover (ht : 1 ≤ t) {hh : ℕ} (hn : 1 ≤ m - 1 - (G : ℕ))
    (hcov : m - 1 - (G : ℕ) ≤ hh * t)
    (hne : ∀ ℓ : Fin hh, (ℓ : ℕ) * t < m - 1 - (G : ℕ))
    (r : Fin m) (hr : (G : ℕ) ≤ (r : ℕ)) :
    ∃ ℓ : Fin hh, (splitLo G t (ℓ : ℕ) : ℕ) - 1 ≤ (r : ℕ)
      ∧ (r : ℕ) ≤ (splitHi G t (ℓ : ℕ) : ℕ) := by
  have hm := r.isLt
  have hG := G.isLt
  have hhpos : 0 < hh := by
    rcases Nat.eq_zero_or_pos hh with h0 | hp
    · subst h0
      simp only [Nat.zero_mul] at hcov
      omega
    · exact hp
  rcases eq_or_lt_of_le hr with hrg | hrg
  · -- the glue itself is covered by the first part
    have hval : ((⟨0, hhpos⟩ : Fin hh) : ℕ) = 0 := rfl
    refine ⟨⟨0, hhpos⟩, ?_, ?_⟩
    · rw [hval, splitLo_val (by rw [← hval]; exact hne ⟨0, hhpos⟩)]
      omega
    · rw [hval, splitHi_val]
      have h01 : (0 + 1) * t = t := by ring
      omega
  · -- inside the right part: locate `r` by dividing its offset by `t`
    set j : ℕ := (r : ℕ) - (G : ℕ) - 1 with hj
    have hjn : j < m - 1 - (G : ℕ) := by omega
    have hdm := Nat.div_add_mod j t
    have hmod : j % t < t := Nat.mod_lt _ (by omega)
    have hklt : j / t < hh := by
      by_contra hcon
      have hcon' : hh ≤ j / t := Nat.le_of_not_lt hcon
      have : hh * t ≤ (j / t) * t := Nat.mul_le_mul_right t hcon'
      have hle : t * (j / t) ≤ j := by omega
      have : (j / t) * t ≤ j := by rw [mul_comm]; exact hle
      omega
    refine ⟨⟨j / t, hklt⟩, ?_, ?_⟩
    · have hval : ((⟨j / t, hklt⟩ : Fin hh) : ℕ) = j / t := rfl
      rw [hval, splitLo_val (by rw [← hval]; exact hne ⟨j / t, hklt⟩)]
      have hle : (j / t) * t ≤ j := by rw [mul_comm]; omega
      omega
    · have hval : ((⟨j / t, hklt⟩ : Fin hh) : ℕ) = j / t := rfl
      rw [hval, splitHi_val]
      have hmul : (j / t + 1) * t = (j / t) * t + t := by ring
      have hlt : j < (j / t) * t + t := by rw [mul_comm]; omega
      omega

/-- **The split, plugged into Corollary 35.** -/
theorem bldsFun_eq_sup_split (W : Fin m → σ) (G : Fin m) {t hh : ℕ}
    (hglue : IsDistinct W G (lastIdx G)) (ht : 1 ≤ t)
    (hn : 1 ≤ m - 1 - (G : ℕ)) (hcov : m - 1 - (G : ℕ) ≤ hh * t)
    (hne : ∀ ℓ : Fin hh, (ℓ : ℕ) * t < m - 1 - (G : ℕ)) :
    bldsFun G W = Finset.univ.sup fun ℓ : Fin hh =>
      ((splitLo G t (ℓ : ℕ) : ℕ) - (splitQ W G t (ℓ : ℕ) : ℕ) - 1)
        + childVal (splitP W G t (ℓ : ℕ) : ℕ) (splitQ W G t (ℓ : ℕ) : ℕ)
            (splitLo G t (ℓ : ℕ) : ℕ) (splitY W G t (ℓ : ℕ) : ℕ)
            (splitP_le_splitQ hglue ht (hne ℓ)) (splitQ W G t (ℓ : ℕ)).isLt
            (splitY W G t (ℓ : ℕ)).isLt W := by
  have hqsle : ∀ ℓ : Fin hh, splitQs W G t (ℓ : ℕ) ≤ splitHi G t (ℓ : ℕ) := by
    intro ℓ
    have h1 := splitQs_val (W := W) (hne ℓ)
    have h2 := splitQ_le_glue W G t (ℓ : ℕ)
    have h3 := lt_splitLo (G := G) (t := t) (hne ℓ)
    have h4 := splitLo_le_splitHi (G := G) ht (hne ℓ)
    rw [Fin.le_def]
    omega
  refine bldsFun_eq_sup_children hglue (fun ℓ => lt_splitLo (hne ℓ))
    (fun ℓ => splitLo_le_splitHi ht (hne ℓ))
    (fun ℓ => isDistinct_lambdaFun (firstIdx_le' G _)) (fun ℓ i hi hd => ?_)
    (fun ℓ => splitP_le_splitQ hglue ht (hne ℓ)) (fun ℓ => rfl)
    (fun ℓ => splitQs_val (hne ℓ))
    (fun ℓ => isDistinct_rhoFun (hqsle ℓ)) (fun ℓ => rhoFun_le (hqsle ℓ))
    (fun ℓ r hr hd => ?_) (fun r hr => split_cover ht hn hcov hne r hr)
  · have := lambdaFun_le_of_isDistinct (α := W) (a := firstIdx G) (i := i)
      (j := predIdx (splitLo G t (ℓ : ℕ))) (firstIdx_le' G i)
      (by rw [Fin.le_def, predIdx_val]; exact hi) hd
    rw [Fin.le_def] at this
    exact this
  · rcases le_or_gt (splitQs W G t (ℓ : ℕ) : ℕ) (r : ℕ) with hqr | hqr
    · have := le_rhoFun_of_isDistinct (α := W) (l := splitQs W G t (ℓ : ℕ)) (r := r)
        (b := splitHi G t (ℓ : ℕ)) (by rw [Fin.le_def]; exact hqr)
        (by rw [Fin.le_def]; exact hr) hd
      rw [Fin.le_def] at this
      exact this
    · have hge : (splitQs W G t (ℓ : ℕ) : ℕ) ≤ (splitY W G t (ℓ : ℕ) : ℕ) := by
        have := le_rhoFun (α := W) (hqsle ℓ)
        rw [Fin.le_def] at this
        exact this
      omega

/-- **Every child is at most `2t`** — the bound the recursion shrinks by. -/
lemma splitSize_le (ht : 1 ≤ t) {ℓ : ℕ}
    (hℓ : ℓ * t < m - 1 - (G : ℕ)) :
    ((splitQ W G t ℓ : ℕ) + 1 - (splitP W G t ℓ : ℕ))
        + ((splitY W G t ℓ : ℕ) + 1 - (splitLo G t ℓ : ℕ)) ≤ 2 * t := by
  have hy'le : (splitY W G t ℓ : ℕ) ≤ (splitHi G t ℓ : ℕ) := by
    have hqs : (splitQs W G t ℓ : ℕ) = (splitQ W G t ℓ : ℕ) + 1 := splitQs_val hℓ
    have h2 := splitQ_le_glue W G t ℓ
    have h3 := lt_splitLo (G := G) (t := t) hℓ
    have h4 := splitLo_le_splitHi (G := G) ht hℓ
    have hle : (splitY W G t ℓ : ℕ) ≤ (splitHi G t ℓ : ℕ) := by
      have := rhoFun_le (α := W) (l := splitQs W G t ℓ) (b := splitHi G t ℓ)
        (by rw [Fin.le_def]; omega)
      rw [Fin.le_def] at this
      exact this
    exact hle
  have hsize := childSize_le_two_mul (x := splitLo G t ℓ) (y := splitHi G t ℓ)
    (p := splitP W G t ℓ) (q := splitQ W G t ℓ) (y' := splitY W G t ℓ)
    (gv := (G : ℕ)) (splitLo_le_splitHi (G := G) ht hℓ) rfl hy'le
  have hwin := winLen_split_le (G := G) (t := t) hℓ
  omega

/-- **A node with a nonempty right part**, fully concrete: normalize, split
into `hh` parts of size `t`, recurse.  This is the identity the dual step
consumes, with `HasDualOn.maxMapFam` over `Option (Fin hh)` — `none` carrying
the glue run, slot `ℓ` carrying its child. -/
theorem bldsFun_eq_maxFun_split (β : Fin m → σ) (g : Fin m) {t hh : ℕ}
    (ht : 1 ≤ t) (hn : 1 ≤ normSize β g - 1 - (normGlue β g : ℕ))
    (hcov : normSize β g - 1 - (normGlue β g : ℕ) ≤ hh * t)
    (hne : ∀ ℓ : Fin hh, (ℓ : ℕ) * t < normSize β g - 1 - (normGlue β g : ℕ)) :
    bldsFun g β = maxFun fun s : Option (Fin hh) => s.elim (glueRun β g) fun ℓ =>
      ((splitLo (normGlue β g) t (ℓ : ℕ) : ℕ)
          - (splitQ (normWord β g) (normGlue β g) t (ℓ : ℕ) : ℕ) - 1)
        + childVal (splitP (normWord β g) (normGlue β g) t (ℓ : ℕ) : ℕ)
            (splitQ (normWord β g) (normGlue β g) t (ℓ : ℕ) : ℕ)
            (splitLo (normGlue β g) t (ℓ : ℕ) : ℕ)
            (splitY (normWord β g) (normGlue β g) t (ℓ : ℕ) : ℕ)
            (splitP_le_splitQ (isDistinct_normWord_glue β g) ht (hne ℓ))
            (splitQ (normWord β g) (normGlue β g) t (ℓ : ℕ)).isLt
            (splitY (normWord β g) (normGlue β g) t (ℓ : ℕ)).isLt (normWord β g) := by
  rw [maxFun_option_elim, bldsFun_eq_normalized β g]
  exact congrArg _ (bldsFun_eq_sup_split (normWord β g) (normGlue β g)
    (isDistinct_normWord_glue β g) ht hn hcov hne)

end Split

/-! ## The child as a sub-family of the parent's coordinates

A child's arena is the normalized window `[a, b]` followed by the two-interval
sub-arena `[p, q] ∪ [x, y']`, so its positions sit inside the parent's arena
through the composite of two injections.  Composing them once, here, is what
lets a single `HasDualOn.pullbackCoord` carry a child's solution — stated in
the child's own coordinates, which is what the induction hypothesis provides —
to the parent's promise at the same cost. -/

section ChildEmb

/-- The child's positions inside the parent's arena. -/
def childEmb (a b : Fin m) (p q x y' : ℕ) (hq : q < (b : ℕ) + 1 - (a : ℕ))
    (hy' : y' < (b : ℕ) + 1 - (a : ℕ)) :
    Fin ((q + 1 - p) + (y' + 1 - x)) → Fin m :=
  fun k => intervalEmb (a : ℕ) (b : ℕ) b.isLt (pairEmb p q x y' hq hy' k)

lemma childEmb_strictMono {a b : Fin m} {p q x y' : ℕ} (hpq : p ≤ q) (hqx : q < x)
    (hq : q < (b : ℕ) + 1 - (a : ℕ)) (hy' : y' < (b : ℕ) + 1 - (a : ℕ)) :
    StrictMono (childEmb a b p q x y' hq hy') := fun _ _ hkk =>
  intervalEmb_strictMono b.isLt (pairEmb_strictMono hpq hqx hq hy' hkk)

lemma childEmb_injective {a b : Fin m} {p q x y' : ℕ} (hpq : p ≤ q) (hqx : q < x)
    (hq : q < (b : ℕ) + 1 - (a : ℕ)) (hy' : y' < (b : ℕ) + 1 - (a : ℕ)) :
    Function.Injective (childEmb a b p q x y' hq hy') :=
  (childEmb_strictMono hpq hqx hq hy').injective

/-- **The child value is `bldsFun` of the child's word.**  This is the form
the induction hypothesis speaks about; `childVal` is the same thing read
through the parent's arena. -/
lemma childVal_eq_bldsFun_childEmb (β : Fin m → σ) (a b : Fin m) (p q x y' : ℕ)
    (hpq : p ≤ q) (hq : q < (b : ℕ) + 1 - (a : ℕ)) (hy' : y' < (b : ℕ) + 1 - (a : ℕ)) :
    childVal p q x y' hpq hq hy' (β ∘ intervalEmb (a : ℕ) (b : ℕ) b.isLt)
      = bldsFun (⟨q - p, by omega⟩ : Fin ((q + 1 - p) + (y' + 1 - x)))
          (β ∘ childEmb a b p q x y' hq hy') := rfl

end ChildEmb

section ChildDual

variable {σ' : Type} [DecidableEq σ'] {X : Type} [Fintype X] [DecidableEq X]

/-- **Transporting a child's solution to the parent's promise.**  The child's
query coordinates are a sub-family of the parent's, so its solution costs the
same in the parent's coordinates (using `pullbackCoord`). -/
theorem hasDualOn_of_child {V : Type} [DecidableEq V] {read : X → Fin m → σ'}
    {a b : Fin m} {p q x y' : ℕ} (hpq : p ≤ q) (hqx : q < x)
    {hq : q < (b : ℕ) + 1 - (a : ℕ)} {hy' : y' < (b : ℕ) + 1 - (a : ℕ)}
    {F : X → V} {c : ℝ}
    (h : HasDualOn (fun z k => read z (childEmb a b p q x y' hq hy' k)) F c) :
    HasDualOn read F c :=
  h.pullbackCoord (childEmb_injective hpq hqx hq hy')

end ChildDual

/-! ## The normalization descriptor, on the dual side

The three quantities a node computes before it splits — the two ends of the
normalized arena and the end of the glue run — are one descriptor, at three
anchor costs.  `HasDualOn.pair` is what makes the three add rather than
multiply: conditioning on the first two, the third is solved by the ambient
solution on each fiber.

Everything else a node does before recursing (`normSize`, `normWord`'s domain,
`normGlue`, `glueRun`, and hence the parts) is a *function of this descriptor*,
so on its fibers the reduction of `bldsFun_eq_maxFun_children` is by
constants. -/

section Dual

variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X] [DecidableEq X]

/-- The successor of the glue, clamped — so that it is total.  When the glue
is the last index the clamp makes the third anchor redundant, which is
harmless: the glue run is `0` there. -/
def glueSucc (g : Fin m) : Fin m :=
  ⟨min ((g : ℕ) + 1) (m - 1), by have := g.isLt; omega⟩

lemma glueSucc_le_last (g : Fin m) : glueSucc g ≤ lastIdx g := by
  have := g.isLt
  rw [Fin.le_def, lastIdx_val]
  simp only [glueSucc]
  omega

lemma glueSucc_eq {g : Fin m} (hg : (g : ℕ) + 1 < m) :
    glueSucc g = (⟨(g : ℕ) + 1, hg⟩ : Fin m) := by
  apply Fin.ext
  simp only [glueSucc]
  omega

/-- **The normalization descriptor** of a node: the two ends of the normalized
arena and the end of the glue run. -/
def normDesc (β : Fin m → σ) (g : Fin m) : Fin m × Fin m × Fin m :=
  (normA β g, normB β g, rhoFun β (glueSucc g) (lastIdx g))

/-- The glue run is determined by the descriptor. -/
lemma glueRun_eq_of_normDesc {β γ : Fin m → σ} {g : Fin m}
    (h : normDesc β g = normDesc γ g) : glueRun β g = glueRun γ g := by
  by_cases hg : (g : ℕ) + 1 < m
  · have h3 : rhoFun β (glueSucc g) (lastIdx g) = rhoFun γ (glueSucc g) (lastIdx g) :=
      congrArg (fun t => t.2.2) h
    rw [glueSucc_eq hg] at h3
    rw [glueRun, dif_pos hg, glueRun, dif_pos hg, h3]
  · rw [glueRun, dif_neg hg, glueRun, dif_neg hg]

/-- The normalized arena is determined by the descriptor. -/
lemma normA_eq_of_normDesc {β γ : Fin m → σ} {g : Fin m}
    (h : normDesc β g = normDesc γ g) : normA β g = normA γ g :=
  congrArg (fun t => t.1) h

lemma normB_eq_of_normDesc {β γ : Fin m → σ} {g : Fin m}
    (h : normDesc β g = normDesc γ g) : normB β g = normB γ g :=
  congrArg (fun t => t.2.1) h

lemma normSize_eq_of_normDesc {β γ : Fin m → σ} {g : Fin m}
    (h : normDesc β g = normDesc γ g) : normSize β g = normSize γ g := by
  simp only [normSize, normA_eq_of_normDesc h, normB_eq_of_normDesc h]

/-- Every anchor of a node is a search inside its arena, hence costs at most
the arena-size bound. -/
private lemma anchor_cost_le {L : ℕ} (a j : Fin m) :
    (L : ℝ) * (8 * ((winLen a j : ℕ) : ℝ) ^ ((2 : ℝ) / 3))
      ≤ (L : ℝ) * (8 * (m : ℝ) ^ ((2 : ℝ) / 3)) := by
  have h1 : ((winLen a j : ℕ) : ℝ) ^ ((2 : ℝ) / 3) ≤ (m : ℝ) ^ ((2 : ℝ) / 3) := by
    refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ (by norm_num)
    exact_mod_cast winLen_le a j
  have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  have h8 : (0 : ℝ) ≤ 8 := by norm_num
  gcongr

/-- **An anchor read through an arena embedding.**  A node's level-2 and
level-3 descriptors are `Λ`/`ρ` of the *normalized* word, i.e. of the ambient
word composed with an injection; `pullbackCoord` puts the solution back on the
ambient promise at the same cost. -/
theorem hasDualOn_lambdaFun_arena {s : ℕ} {e : Fin s → Fin m}
    (he : Function.Injective e) (read : X → Fin m → σ) {a j : Fin s} (haj : a ≤ j)
    {L : ℕ} (hL : winLen a j ≤ 2 ^ L) :
    HasDualOn read (fun z => lambdaFun (fun k => read z (e k)) a j)
      ((L : ℝ) * (8 * (winLen a j : ℝ) ^ ((2 : ℝ) / 3))) :=
  (hasDualOn_lambdaFun (fun z k => read z (e k)) haj hL).pullbackCoord he

theorem hasDualOn_rhoFun_arena {s : ℕ} {e : Fin s → Fin m}
    (he : Function.Injective e) (read : X → Fin m → σ) {l b : Fin s} (hlb : l ≤ b)
    {L : ℕ} (hL : winLen l b ≤ 2 ^ L) :
    HasDualOn read (fun z => rhoFun (fun k => read z (e k)) l b)
      ((L : ℝ) * (8 * (winLen l b : ℝ) ^ ((2 : ℝ) / 3))) :=
  (hasDualOn_rhoFun (fun z k => read z (e k)) hlb hL).pullbackCoord he

/-- **The normalization descriptor has a dual of cost `3 g_L(m)`** on any
promise, where `g_L(m) = ⌈log₂ m⌉ · 8 m^{2/3}` is the anchor cost. -/
theorem hasDualOn_normDesc (read : X → Fin m → σ) (g : Fin m) {L : ℕ}
    (hL : m ≤ 2 ^ L) :
    HasDualOn read (fun x => normDesc (read x) g)
      (3 * ((L : ℝ) * (8 * (m : ℝ) ^ ((2 : ℝ) / 3)))) := by
  have hwin : ∀ a j : Fin m, winLen a j ≤ 2 ^ L := fun a j =>
    le_trans (winLen_le a j) hL
  have hA : HasDualOn read (fun x => normA (read x) g)
      ((L : ℝ) * (8 * (m : ℝ) ^ ((2 : ℝ) / 3))) :=
    (hasDualOn_lambdaFun read (firstIdx_le' g g) (hwin _ _)).mono (anchor_cost_le _ _)
  have hB : HasDualOn read (fun x => normB (read x) g)
      ((L : ℝ) * (8 * (m : ℝ) ^ ((2 : ℝ) / 3))) :=
    (hasDualOn_rhoFun read (le_lastIdx g g) (hwin _ _)).mono (anchor_cost_le _ _)
  have hC : HasDualOn read (fun x => rhoFun (read x) (glueSucc g) (lastIdx g))
      ((L : ℝ) * (8 * (m : ℝ) ^ ((2 : ℝ) / 3))) :=
    (hasDualOn_rhoFun read (glueSucc_le_last g) (hwin _ _)).mono (anchor_cost_le _ _)
  exact (hA.pair (hB.pair hC)).mono (by ring_nf; exact le_rfl)

end Dual

end QuantumQueryComplexity
