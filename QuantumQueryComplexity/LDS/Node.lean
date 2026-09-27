import QuantumQueryComplexity.LDS.Defs
import Mathlib.Data.Fin.VecNotation

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# The node problem in arena coordinates

A node of the longest-distinct-substring recursion works on a *glued* pair of
intervals of the input word.  The paper carries that as a quadruple
`(I1, I2, I3, I4)` with a glue-crossing successor relation. Listing the arena's
positions in order and passing to the **arena word** `β = α ∘ e` expresses
all of it to one word and one index:

* glued windows are contiguous windows of `β`;
* glued distinctness is `IsDistinct β`;
* the touch condition is "the window contains `g` or `g + 1`";
* `prev`/`succ` (Def 33) are `r - 1` / `r + 1`;
* the anchors `L`, `R` are `Λ` of `β` and its mirror — so `LDS/Search.lean`
  applies unchanged, with no arena analogue needed;
* children are sub-arenas, i.e. composites of coordinate injections, which
  `HasDualOn.pullbackCoord` transports on the dual side.

So the node problem is `bldsFun g β`, for `g : Fin m` and `β : Fin m → σ`.

`Touches` is stated uniformly as `l ≤ g + 1 ∧ g ≤ r`, with **no** case split
on whether the right part is empty: when `g` is the last index, `l ≤ g + 1`
is vacuous and `g ≤ r` forces `r = g`, so the definition degenerates on its
own to the longest distinct suffix at `g`, the empty-right-part convention.
-/

namespace QuantumQueryComplexity

variable {m : ℕ} {σ : Type*} [DecidableEq σ]

/-! ## The node problem -/

/-- The first index, witnessed by any element of `Fin m`.  `Λ` needs a left
barrier and the node problem always wants the barrier at `0`; carrying the
witness avoids a `NeZero m` instance on every statement. -/
def firstIdx (k : Fin m) : Fin m := ⟨0, by have := k.isLt; omega⟩

@[simp] lemma firstIdx_val (k : Fin m) : (firstIdx k : ℕ) = 0 := rfl

lemma firstIdx_le (k : Fin m) : firstIdx k ≤ k := by
  rw [Fin.le_def]
  exact Nat.zero_le _

/-- The barrier `0` is below every index, whichever witness carries it. -/
lemma firstIdx_le' (k r : Fin m) : firstIdx k ≤ r := by
  rw [Fin.le_def]
  exact Nat.zero_le _

/-- The last index, witnessed by any element of `Fin m`. -/
def lastIdx (k : Fin m) : Fin m := ⟨m - 1, by have := k.isLt; omega⟩

@[simp] lemma lastIdx_val (k : Fin m) : (lastIdx k : ℕ) = m - 1 := rfl

lemma le_lastIdx (k r : Fin m) : r ≤ lastIdx k := by
  have := r.isLt
  rw [Fin.le_def, lastIdx_val]
  omega

/-- The window `[l, r]` meets the glue at `g`: it contains `g` or `g + 1`.
Stated uniformly — see the module docstring for why no case split on the
existence of `g + 1` is needed. -/
def Touches (g l r : Fin m) : Prop :=
  (l : ℕ) ≤ (g : ℕ) + 1 ∧ (g : ℕ) ≤ (r : ℕ)

instance (g l r : Fin m) : Decidable (Touches g l r) :=
  inferInstanceAs (Decidable (_ ∧ _))

lemma touches_self (g : Fin m) : Touches g g g := ⟨by omega, le_rfl⟩

/-- **The node problem** (in arena coordinates): the longest
distinct window of `β` meeting the glue at `g`. -/
def bldsFun (g : Fin m) (β : Fin m → σ) : ℕ :=
  Finset.univ.sup fun p : Fin m × Fin m =>
    if IsDistinct β p.1 p.2 ∧ Touches g p.1 p.2 then winLen p.1 p.2 else 0

/-- Every distinct window meeting the glue is a witness. -/
lemma le_bldsFun {β : Fin m → σ} {g l r : Fin m} (hd : IsDistinct β l r)
    (ht : Touches g l r) : winLen l r ≤ bldsFun g β := by
  have hle := Finset.le_sup (f := fun p : Fin m × Fin m =>
    if IsDistinct β p.1 p.2 ∧ Touches g p.1 p.2 then winLen p.1 p.2 else 0)
    (Finset.mem_univ (l, r))
  simp only [hd, ht, and_self, if_true] at hle
  exact hle

/-- Upper bounds on the node problem are checked window by window. -/
lemma bldsFun_le_of {β : Fin m → σ} {g : Fin m} {c : ℕ}
    (h : ∀ l r : Fin m, IsDistinct β l r → Touches g l r → winLen l r ≤ c) :
    bldsFun g β ≤ c := by
  unfold bldsFun
  refine Finset.sup_le fun p _ => ?_
  split
  · rename_i hc
    exact h p.1 p.2 hc.1 hc.2
  · exact Nat.zero_le _

/-- The node problem never exceeds the whole word's answer. -/
lemma bldsFun_le_ldsFun (g : Fin m) (β : Fin m → σ) :
    bldsFun g β ≤ ldsFun β := by
  unfold bldsFun
  refine Finset.sup_le fun p _ => ?_
  split
  · rename_i h
    exact le_ldsFun h.1
  · exact Nat.zero_le _

lemma bldsFun_le (g : Fin m) (β : Fin m → σ) : bldsFun g β ≤ m :=
  (bldsFun_le_ldsFun g β).trans (ldsFun_le β)

/-- The singleton window at the glue is always available. -/
lemma one_le_bldsFun (g : Fin m) (β : Fin m → σ) : 1 ≤ bldsFun g β := by
  simpa using le_bldsFun (isDistinct_self β g) (touches_self g)

/-! ## The sliding-window form

The two-pointer form used by every identity downstream: only the *leftmost*
distinct start matters at each right endpoint, so the node value is a sup
over right endpoints alone. -/

theorem bldsFun_eq_sup_lambda (g : Fin m) (β : Fin m → σ) :
    bldsFun g β = Finset.univ.sup fun r : Fin m =>
      if (g : ℕ) ≤ (r : ℕ) ∧ (lambdaFun β (firstIdx r) r : ℕ) ≤ (g : ℕ) + 1
      then winLen (lambdaFun β (firstIdx r) r) r else 0 := by
  have hzero : ∀ r : Fin m, firstIdx r ≤ r := firstIdx_le
  refine le_antisymm ?_ (Finset.sup_le fun r _ => ?_)
  · unfold bldsFun
    refine Finset.sup_le fun p _ => ?_
    by_cases hc : IsDistinct β p.1 p.2 ∧ Touches g p.1 p.2
    · rw [if_pos hc]
      refine le_trans ?_ (Finset.le_sup (Finset.mem_univ p.2))
      rcases le_or_gt p.1 p.2 with hle | hlt
      · have hmin : (lambdaFun β (firstIdx p.2) p.2 : ℕ) ≤ (p.1 : ℕ) :=
          lambdaFun_le_of_isDistinct (firstIdx_le p.1) hle hc.1
        have hcond : (g : ℕ) ≤ (p.2 : ℕ)
            ∧ (lambdaFun β (firstIdx p.2) p.2 : ℕ) ≤ (g : ℕ) + 1 := by
          refine ⟨hc.2.2, ?_⟩
          have := hc.2.1
          omega
        rw [if_pos hcond]
        simp only [winLen]
        omega
      · have h1 : (p.2 : ℕ) < (p.1 : ℕ) := hlt
        have : winLen p.1 p.2 = 0 := by simp only [winLen]; omega
        rw [this]
        exact Nat.zero_le _
    · rw [if_neg hc]
      exact Nat.zero_le _
  · by_cases hc : (g : ℕ) ≤ (r : ℕ)
        ∧ (lambdaFun β (firstIdx r) r : ℕ) ≤ (g : ℕ) + 1
    · rw [if_pos hc]
      exact le_bldsFun (isDistinct_lambdaFun (hzero r)) ⟨hc.2, hc.1⟩
    · rw [if_neg hc]
      exact Nat.zero_le _

/-- **The empty-right-part case** : when the glue
is the last index, the node value is the longest distinct suffix at `g`. -/
theorem bldsFun_of_glue_last {g : Fin m} (hg : (g : ℕ) + 1 = m)
    (β : Fin m → σ) :
    bldsFun g β = winLen (lambdaFun β (firstIdx g) g) g := by
  have hzero : firstIdx g ≤ g := firstIdx_le g
  have htouch : Touches g (lambdaFun β (firstIdx g) g) g := by
    refine ⟨?_, le_rfl⟩
    have := lambdaFun_le (α := β) hzero
    rw [Fin.le_def] at this
    omega
  refine le_antisymm ?_ (le_bldsFun (isDistinct_lambdaFun hzero) htouch)
  rw [bldsFun_eq_sup_lambda]
  refine Finset.sup_le fun r _ => ?_
  by_cases hc : (g : ℕ) ≤ (r : ℕ)
      ∧ (lambdaFun β (firstIdx r) r : ℕ) ≤ (g : ℕ) + 1
  · rw [if_pos hc]
    have hr : r = g := by
      have := r.isLt
      exact Fin.ext (by omega)
    rw [hr]
  · rw [if_neg hc]
    exact Nat.zero_le _

/-! ## Normalization

A node first shrinks its arena: the left part to the
longest distinct run ending at the glue, the right part to the longest
distinct run starting at it.  What makes this sound is a two-class split of
the touching windows.  A touching window either

* **contains `g`** — and then it is trapped inside `[Λ_a(g), ρ_b(g)]`, since
  its left half `[l, g]` and right half `[g, r]` are both distinct; or
* **misses `g`** — and then, touching, it must start exactly at `g + 1`.

The first class is what survives normalization; the second is the run that
dies at the glue, denoted `n₂'`. Both classes are needed: dropping the second
loses inside-right windows past the truncation point.

Windows are cut to `[a, b]` of the ambient word rather than re-indexed, so
no type depends on the input: on a descriptor fiber `a`, `b` and `g` are
constants, which is exactly the form the recursion consumes. -/

/-- The node problem restricted to the sub-window `[a, b]`. -/
def bldsIn (a b g : Fin m) (β : Fin m → σ) : ℕ :=
  Finset.univ.sup fun p : Fin m × Fin m =>
    if a ≤ p.1 ∧ p.2 ≤ b ∧ IsDistinct β p.1 p.2 ∧ Touches g p.1 p.2
    then winLen p.1 p.2 else 0

lemma le_bldsIn {β : Fin m → σ} {a b g l r : Fin m} (hal : a ≤ l) (hrb : r ≤ b)
    (hd : IsDistinct β l r) (ht : Touches g l r) : winLen l r ≤ bldsIn a b g β := by
  have hle := Finset.le_sup (f := fun p : Fin m × Fin m =>
    if a ≤ p.1 ∧ p.2 ≤ b ∧ IsDistinct β p.1 p.2 ∧ Touches g p.1 p.2
    then winLen p.1 p.2 else 0) (Finset.mem_univ (l, r))
  simp only [hal, hrb, hd, ht, and_self, if_true] at hle
  exact hle

/-- Shrinking the window can only lose candidates. -/
lemma bldsIn_mono {β : Fin m → σ} {a a' b b' g : Fin m} (ha : a ≤ a')
    (hb : b' ≤ b) : bldsIn a' b' g β ≤ bldsIn a b g β := by
  unfold bldsIn
  refine Finset.sup_le fun p _ => ?_
  split
  · rename_i h
    exact le_bldsIn (ha.trans h.1) (h.2.1.trans hb) h.2.2.1 h.2.2.2
  · exact Nat.zero_le _

/-- The unrestricted node problem is the window `[first, last]`. -/
lemma bldsFun_eq_bldsIn (g : Fin m) (β : Fin m → σ) :
    bldsFun g β = bldsIn (firstIdx g) (lastIdx g) g β := by
  have hlast : ∀ r : Fin m, r ≤ lastIdx g := fun r => le_lastIdx g r
  refine le_antisymm ?_ ?_
  · unfold bldsFun
    refine Finset.sup_le fun p _ => ?_
    split
    · rename_i h
      exact le_bldsIn (firstIdx_le p.1) (hlast p.2) h.1 h.2
    · exact Nat.zero_le _
  · unfold bldsIn
    refine Finset.sup_le fun p _ => ?_
    split
    · rename_i h
      exact le_bldsFun h.2.2.1 h.2.2.2
    · exact Nat.zero_le _

/-- The touching windows that **miss** the glue: those starting at `g + 1`.
This is the run that dies at the glue (`n₂'`). -/
def afterGlue (a b g : Fin m) (β : Fin m → σ) : ℕ :=
  Finset.univ.sup fun p : Fin m × Fin m =>
    if a ≤ p.1 ∧ p.2 ≤ b ∧ IsDistinct β p.1 p.2 ∧ Touches g p.1 p.2
        ∧ (p.1 : ℕ) = (g : ℕ) + 1
    then winLen p.1 p.2 else 0

lemma afterGlue_le_bldsIn (a b g : Fin m) (β : Fin m → σ) :
    afterGlue a b g β ≤ bldsIn a b g β := by
  unfold afterGlue
  refine Finset.sup_le fun p _ => ?_
  split
  · rename_i h
    exact le_bldsIn h.1 h.2.1 h.2.2.1 h.2.2.2.1
  · exact Nat.zero_le _

/-- The glue run is one anchor: it is the longest distinct run starting at
`g + 1`, clipped to the window.  So on a descriptor fiber it is a constant. -/
theorem afterGlue_eq {a b g gs : Fin m} (hag : a ≤ g) (hgs : (gs : ℕ) = (g : ℕ) + 1)
    (hgb : gs ≤ b) (β : Fin m → σ) :
    afterGlue a b g β = winLen gs (rhoFun β gs b) := by
  refine le_antisymm (Finset.sup_le fun p _ => ?_) ?_
  · split
    · rename_i h
      obtain ⟨hal, hrb, hd, -, hl⟩ := h
      have hlgs : p.1 = gs := Fin.ext (by omega)
      rcases le_or_gt (p.1 : ℕ) (p.2 : ℕ) with hle | hlt
      · have hmax : p.2 ≤ rhoFun β gs b :=
          le_rhoFun_of_isDistinct (by rw [← hlgs]; exact (Fin.le_def).mpr hle) hrb
            (by rw [← hlgs]; exact hd)
        rw [Fin.le_def] at hmax
        simp only [winLen]
        omega
      · simp only [winLen]
        omega
    · exact Nat.zero_le _
  · have hd : IsDistinct β gs (rhoFun β gs b) := isDistinct_rhoFun hgb
    have hrb : rhoFun β gs b ≤ b := rhoFun_le hgb
    have hlr : gs ≤ rhoFun β gs b := le_rhoFun hgb
    have hle := Finset.le_sup (f := fun p : Fin m × Fin m =>
      if a ≤ p.1 ∧ p.2 ≤ b ∧ IsDistinct β p.1 p.2 ∧ Touches g p.1 p.2
          ∧ (p.1 : ℕ) = (g : ℕ) + 1
      then winLen p.1 p.2 else 0) (Finset.mem_univ (gs, rhoFun β gs b))
    have hcond : a ≤ gs ∧ rhoFun β gs b ≤ b ∧ IsDistinct β gs (rhoFun β gs b)
        ∧ Touches g gs (rhoFun β gs b) ∧ (gs : ℕ) = (g : ℕ) + 1 := by
      refine ⟨?_, hrb, hd, ⟨by omega, ?_⟩, hgs⟩
      · rw [Fin.le_def]
        have := (Fin.le_def).mp hag
        omega
      · have := (Fin.le_def).mp hlr
        omega
    rw [if_pos hcond] at hle
    exact hle

/-- **Truncation soundness plus the glue run**: the
node value splits into the run that dies at the glue and the value of the
*normalized* window `[Λ_a(g), ρ_b(g)]`. -/
theorem bldsIn_normalize {a b g : Fin m} (hag : a ≤ g) (hgb : g ≤ b)
    (β : Fin m → σ) :
    bldsIn a b g β
      = max (afterGlue a b g β)
          (bldsIn (lambdaFun β a g) (rhoFun β g b) g β) := by
  refine le_antisymm ?_ ?_
  · unfold bldsIn
    refine Finset.sup_le fun p _ => ?_
    by_cases hc : a ≤ p.1 ∧ p.2 ≤ b ∧ IsDistinct β p.1 p.2 ∧ Touches g p.1 p.2
    · rw [if_pos hc]
      obtain ⟨hal, hrb, hd, ht⟩ := hc
      rcases le_or_gt (p.1 : ℕ) (g : ℕ) with hlg | hgl
      · -- the window contains the glue: it is trapped in the normalized range
        refine le_trans ?_ (le_max_right _ _)
        have hlg' : p.1 ≤ g := by rw [Fin.le_def]; exact hlg
        have hgr : g ≤ p.2 := by rw [Fin.le_def]; exact ht.2
        have hleft : lambdaFun β a g ≤ p.1 :=
          lambdaFun_le_of_isDistinct hal hlg' (hd.mono le_rfl hgr)
        have hright : p.2 ≤ rhoFun β g b :=
          le_rhoFun_of_isDistinct hgr hrb (hd.mono hlg' le_rfl)
        exact le_bldsIn hleft hright hd ht
      · -- the window misses the glue: touching forces it to start at `g + 1`
        refine le_trans ?_ (le_max_left _ _)
        have heq : (p.1 : ℕ) = (g : ℕ) + 1 := by
          have := ht.1
          omega
        have hle := Finset.le_sup (f := fun q : Fin m × Fin m =>
          if a ≤ q.1 ∧ q.2 ≤ b ∧ IsDistinct β q.1 q.2 ∧ Touches g q.1 q.2
              ∧ (q.1 : ℕ) = (g : ℕ) + 1
          then winLen q.1 q.2 else 0) (Finset.mem_univ p)
        simp only [hal, hrb, hd, ht, heq, and_self, if_true] at hle
        exact hle
    · rw [if_neg hc]
      exact Nat.zero_le _
  · refine max_le (afterGlue_le_bldsIn a b g β) ?_
    exact bldsIn_mono (le_lambdaFun hag) (rhoFun_le hgb)

/-- **The left invariant** established by normalization: the normalized left
part is distinct. -/
theorem isDistinct_normalized_left {a g : Fin m} (hag : a ≤ g)
    (β : Fin m → σ) : IsDistinct β (lambdaFun β a g) g :=
  isDistinct_lambdaFun hag

/-- **The glue invariant** established by normalization: the glue letter
together with the normalized right part is distinct.  This is what forces
every later anchor into the left part, keeping children two-interval
(it is *not* reversal-symmetric, hence the re-normalization
after reversing). -/
theorem isDistinct_normalized_right {b g : Fin m} (hgb : g ≤ b)
    (β : Fin m → σ) : IsDistinct β g (rhoFun β g b) :=
  isDistinct_rhoFun hgb

/-! ### Life after normalization

Once the glue invariant holds, the touch condition is no longer a constraint:
every window ending past the glue already starts at `g + 1` or earlier, so the
node problem is a plain scan over right endpoints.  This is the form the child
recursion consumes (`LDS/Child.lean`). -/

/-- Under the glue invariant every `Λ` past the glue lands in the left part. -/
lemma lambdaFun_le_glue {β : Fin m → σ} {g r : Fin m}
    (hglue : IsDistinct β g (lastIdx g)) (hgr : (g : ℕ) ≤ (r : ℕ)) :
    (lambdaFun β (firstIdx g) r : ℕ) ≤ (g : ℕ) + 1 := by
  have hrm := r.isLt
  rcases le_or_gt ((g : ℕ) + 1) (r : ℕ) with hc | hc
  · have hgp : (g : ℕ) + 1 < m := by omega
    have := lambdaFun_le_of_isDistinct (α := β) (a := firstIdx g)
      (i := (⟨(g : ℕ) + 1, hgp⟩ : Fin m)) (j := r) (firstIdx_le' g _)
      (by rw [Fin.le_def]; exact hc)
      (hglue.mono (by rw [Fin.le_def]; exact Nat.le_succ _) (le_lastIdx g r))
    rw [Fin.le_def] at this
    exact this
  · have := lambdaFun_le (α := β) (a := firstIdx g) (j := r) (firstIdx_le' g r)
    rw [Fin.le_def] at this
    omega

/-- **The normalized node is a scan** over the right endpoints past the glue:
the touch condition is implied by the glue invariant. -/
theorem bldsFun_eq_sup_lambda_of_glue {β : Fin m → σ} {g : Fin m}
    (hglue : IsDistinct β g (lastIdx g)) :
    bldsFun g β
      = (Finset.Icc g (lastIdx g)).sup fun r => winLen (lambdaFun β (firstIdx g) r) r := by
  refine le_antisymm (bldsFun_le_of fun l r hd ht => ?_) (Finset.sup_le fun r hr => ?_)
  · rcases le_or_gt (l : ℕ) (r : ℕ) with hlr | hlr
    · have hmem : r ∈ Finset.Icc g (lastIdx g) :=
        Finset.mem_Icc.mpr ⟨by rw [Fin.le_def]; exact ht.2, le_lastIdx g r⟩
      have hlam := lambdaFun_le_of_isDistinct (α := β) (a := firstIdx g) (i := l) (j := r)
        (firstIdx_le' g l) (by rw [Fin.le_def]; exact hlr) hd
      rw [Fin.le_def] at hlam
      have hsup := Finset.le_sup (f := fun r => winLen (lambdaFun β (firstIdx g) r) r) hmem
      simp only [winLen] at hsup ⊢
      omega
    · simp only [winLen]
      omega
  · rw [Finset.mem_Icc] at hr
    have hgr : (g : ℕ) ≤ (r : ℕ) := hr.1
    exact le_bldsFun (isDistinct_lambdaFun (firstIdx_le' g r))
      ⟨lambdaFun_le_glue hglue hgr, hgr⟩

/-! ## Reversal

Orientation is part of the descriptor chain, so the
node needs the reversal identity.  In arena coordinates it is clean: reverse
the word and send the glue `g` to `m - 2 - g`, the last index of what was the
right part. The index transformation is part of the identity. -/

/-- The order-reversing involution of `Fin m`. -/
def revIdx (k : Fin m) : Fin m :=
  ⟨m - 1 - (k : ℕ), by have := k.isLt; omega⟩

@[simp] lemma revIdx_val (k : Fin m) : (revIdx k : ℕ) = m - 1 - (k : ℕ) := rfl

@[simp] lemma revIdx_revIdx (k : Fin m) : revIdx (revIdx k) = k := by
  have := k.isLt
  exact Fin.ext (by simp only [revIdx_val]; omega)

lemma revIdx_injective : Function.Injective (revIdx (m := m)) := by
  intro a b h
  rw [← revIdx_revIdx a, ← revIdx_revIdx b, h]

lemma revIdx_le_revIdx {a b : Fin m} : revIdx a ≤ revIdx b ↔ b ≤ a := by
  have := a.isLt
  have := b.isLt
  rw [Fin.le_def, Fin.le_def, revIdx_val, revIdx_val]
  omega

/-- The reversed word. -/
def revWord (β : Fin m → σ) : Fin m → σ := fun k => β (revIdx k)

lemma isDistinct_revWord {β : Fin m → σ} {l r : Fin m} :
    IsDistinct (revWord β) l r ↔ IsDistinct β (revIdx r) (revIdx l) := by
  have hmem : ∀ a : Fin m, a ∈ Finset.Icc l r
      ↔ revIdx a ∈ Finset.Icc (revIdx r) (revIdx l) := by
    intro a
    rw [Finset.mem_Icc, Finset.mem_Icc, revIdx_le_revIdx, revIdx_le_revIdx]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  constructor
  · intro h a ha b hb hab
    have h' := h (revIdx a) ((hmem (revIdx a)).mpr (by simpa using ha))
      (revIdx b) ((hmem (revIdx b)).mpr (by simpa using hb))
      (by simpa [revWord] using hab)
    exact revIdx_injective (by simpa using h')
  · intro h a ha b hb hab
    exact revIdx_injective (h (revIdx a) ((hmem a).mp ha) (revIdx b)
      ((hmem b).mp hb) hab)

lemma winLen_revIdx (l r : Fin m) : winLen (revIdx r) (revIdx l) = winLen l r := by
  have := l.isLt
  have := r.isLt
  simp only [winLen, revIdx_val]
  omega

/-- **The reversal identity**. Reversing the arena word sends
the glue `g` to `m - 2 - g`. -/
theorem bldsFun_revWord {g : Fin m} (hg : (g : ℕ) + 1 < m) (β : Fin m → σ) :
    bldsFun g β = bldsFun ⟨m - 2 - (g : ℕ), by omega⟩ (revWord β) := by
  have key : ∀ (γ : Fin m → σ) (a b : Fin m), (a : ℕ) + 1 < m →
      (b : ℕ) = m - 2 - (a : ℕ) →
      bldsFun a γ ≤ bldsFun b (revWord γ) := by
    intro γ a b hab hb
    unfold bldsFun
    refine Finset.sup_le fun p _ => ?_
    by_cases hc : IsDistinct γ p.1 p.2 ∧ Touches a p.1 p.2
    · rw [if_pos hc]
      have hd : IsDistinct (revWord γ) (revIdx p.2) (revIdx p.1) := by
        rw [isDistinct_revWord]
        simpa using hc.1
      have ht : Touches b (revIdx p.2) (revIdx p.1) := by
        have h1 := hc.2.1
        have h2 := hc.2.2
        have := p.1.isLt
        have := p.2.isLt
        constructor <;> simp only [revIdx_val] <;> omega
      exact (le_of_eq (winLen_revIdx p.1 p.2).symm).trans (le_bldsFun hd ht)
    · rw [if_neg hc]
      exact Nat.zero_le _
  refine le_antisymm (key β g ⟨m - 2 - (g : ℕ), by omega⟩ hg rfl) ?_
  have hback := key (revWord β) ⟨m - 2 - (g : ℕ), by omega⟩ g (by simp; omega)
    (by simp; omega)
  have hrev : revWord (revWord β) = β := by
    funext k
    simp [revWord]
  rwa [hrev] at hback

/-! ## Sanity checks

Concrete values pin the behavior of `bldsFun` under refactoring. -/

section Sanity

set_option maxRecDepth 8000

example : bldsFun (2 : Fin 6) ![0, 1, 1, 1, 2, 3] = 3 := by decide
example : bldsFun (0 : Fin 4) ![0, 0, 0, 1] = 1 := by decide
example : bldsFun (2 : Fin 5) ![0, 1, 2, 0, 1] = 3 := by decide

/-- The glue-last case really is the longest distinct suffix. -/
example : bldsFun (3 : Fin 4) ![0, 0, 0, 1]
    = winLen (lambdaFun ![0, 0, 0, 1] (firstIdx (3 : Fin 4)) 3) 3 := by decide

/-- Reversal moves the glue from `g` to `m - 2 - g`. -/
example : bldsFun (1 : Fin 5) ![0, 1, 2, 0, 1]
    = bldsFun (2 : Fin 5) ![1, 0, 2, 1, 0] := by decide

end Sanity

end QuantumQueryComplexity
