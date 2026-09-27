import QuantumQueryComplexity.LDS.Node
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# Children of a node: two-interval sub-arenas and Proposition 34

A node splits its right part into intervals `[x, y]`
and hands each one to a child.  The child's arena is *not* a contiguous window
of the parent's: it is the **two-interval sub-arena**

    [p, q] ∪ [x, y'],       p = Λ(x-1),  q = min(g, p + t - 1),  y' = ρ_y(q+1)

(`t = y - x + 1`), glued at `q`.  Passing to arena coordinates (`LDS/Node.lean`)
means the child is the parent word composed with the strictly monotone listing
`pairEmb` of those positions, so the dual side transports along a coordinate
injection (`HasDualOn.pullbackCoord`) and the recursion can be run on the child
word alone.

The main theorem is `sup_lambda_eq_childVal`, Proposition 34 in arena form:

    max_{r ∈ [x-1, y]} (r - Λ(r) + 1)  =  (x - q - 1) + BLDS(child)

Both directions rest on the three facts that the anchor and the truncation buy:

* `[p, x-1]` is distinct — so a child window's left half glues to the gap;
* `[q+1, y']` is distinct — so it glues to the gap on the right;
* the child window is distinct — so the two halves do not clash with each
  other.

Those three cover all six ways a repeat could sit inside `[l, r]`, which is
exactly `isDistinct_of_glue`; without either the cap `q ≤ g` or the truncation
`y' ≤ ρ(q+1)` the statement is false.
-/

namespace QuantumQueryComplexity

variable {m : ℕ} {σ : Type*} [DecidableEq σ]

/-! ## Reindexing -/

/-- Distinctness transports along any strictly monotone reindexing: a window of
the sub-arena sits inside the corresponding window of the parent. -/
lemma IsDistinct.comp_strictMono {m' : ℕ} {β : Fin m → σ} {e : Fin m' → Fin m}
    (he : StrictMono e) {k k' : Fin m'} (h : IsDistinct β (e k) (e k')) :
    IsDistinct (β ∘ e) k k' := by
  intro a ha b hb hab
  rw [Finset.mem_Icc] at ha hb
  exact he.injective (h (e a)
    (Finset.mem_Icc.mpr ⟨he.monotone ha.1, he.monotone ha.2⟩) (e b)
    (Finset.mem_Icc.mpr ⟨he.monotone hb.1, he.monotone hb.2⟩) hab)

/-- The predecessor of an index, clamped at `0`. -/
def predIdx (x : Fin m) : Fin m := ⟨(x : ℕ) - 1, by have := x.isLt; omega⟩

@[simp] lemma predIdx_val (x : Fin m) : (predIdx x : ℕ) = (x : ℕ) - 1 := rfl

/-! ## Two-interval sub-arenas -/

/-- The sub-arena `[p, q] ∪ [x, y]`, listed in increasing order, as a map into
the parent arena.  The left part contributes the first `q + 1 - p` indices. -/
def pairEmb (p q x y : ℕ) (hq : q < m) (hy : y < m)
    (k : Fin ((q + 1 - p) + (y + 1 - x))) : Fin m :=
  if h : (k : ℕ) < q + 1 - p then ⟨p + (k : ℕ), by omega⟩
  else ⟨x + ((k : ℕ) - (q + 1 - p)), by have := k.isLt; omega⟩

lemma pairEmb_val {p q x y : ℕ} (hq : q < m) (hy : y < m)
    (k : Fin ((q + 1 - p) + (y + 1 - x))) :
    (pairEmb p q x y hq hy k : ℕ)
      = if (k : ℕ) < q + 1 - p then p + (k : ℕ) else x + ((k : ℕ) - (q + 1 - p)) := by
  by_cases h : (k : ℕ) < q + 1 - p
  · simp only [pairEmb, dif_pos h, if_pos h]
  · simp only [pairEmb, dif_neg h, if_neg h]

lemma pairEmb_strictMono {p q x y : ℕ} (hpq : p ≤ q) (hqx : q < x)
    (hq : q < m) (hy : y < m) : StrictMono (pairEmb p q x y hq hy) := by
  intro a b hab
  rw [Fin.lt_def] at hab ⊢
  rw [pairEmb_val, pairEmb_val]
  have := a.isLt
  have := b.isLt
  split_ifs <;> omega

/-- A parent position of the left part, read as a child index. -/
lemma pairEmb_mk_left {p q x y : ℕ} (hq : q < m) (hy : y < m) {z : Fin m}
    (hpz : p ≤ (z : ℕ)) (hzq : (z : ℕ) ≤ q)
    (h : (z : ℕ) - p < (q + 1 - p) + (y + 1 - x)) :
    pairEmb p q x y hq hy ⟨(z : ℕ) - p, h⟩ = z := by
  apply Fin.ext
  rw [pairEmb_val]
  have hv : ((⟨(z : ℕ) - p, h⟩ : Fin ((q + 1 - p) + (y + 1 - x))) : ℕ) = (z : ℕ) - p := rfl
  rw [hv]
  split_ifs <;> omega

/-- A parent position of the right part, read as a child index. -/
lemma pairEmb_mk_right {p q x y : ℕ} (hq : q < m) (hy : y < m) {z : Fin m}
    (hxz : x ≤ (z : ℕ)) (_hzy : (z : ℕ) ≤ y)
    (h : (q + 1 - p) + ((z : ℕ) - x) < (q + 1 - p) + (y + 1 - x)) :
    pairEmb p q x y hq hy ⟨(q + 1 - p) + ((z : ℕ) - x), h⟩ = z := by
  apply Fin.ext
  rw [pairEmb_val]
  have hv : ((⟨(q + 1 - p) + ((z : ℕ) - x), h⟩ :
      Fin ((q + 1 - p) + (y + 1 - x))) : ℕ) = (q + 1 - p) + ((z : ℕ) - x) := rfl
  rw [hv]
  split_ifs <;> omega

/-! ## The child node problem -/

/-- **The child**: the node problem on the sub-arena `[p, q] ∪ [x, y']`, glued
at `q`, as a function of the *parent* word.  As a function of the *child* word
it is plain `bldsFun`, which is what the recursion and `pullbackCoord` see. -/
def childVal (p q x y' : ℕ) (hpq : p ≤ q) (hq : q < m) (hy' : y' < m)
    (β : Fin m → σ) : ℕ :=
  bldsFun (⟨q - p, by omega⟩ : Fin ((q + 1 - p) + (y' + 1 - x)))
    (β ∘ pairEmb p q x y' hq hy')

lemma childVal_eq {p q x y' : ℕ} (hpq : p ≤ q) (hq : q < m) (hy' : y' < m)
    (β : Fin m → σ) :
    childVal p q x y' hpq hq hy' β
      = bldsFun (⟨q - p, by omega⟩ : Fin ((q + 1 - p) + (y' + 1 - x)))
          (β ∘ pairEmb p q x y' hq hy') := rfl

/-- Every distinct child window meeting the child's glue is a witness. -/
lemma le_childVal {p q x y' : ℕ} {hpq : p ≤ q} {hq : q < m} {hy' : y' < m}
    (hqx : q < x) {β : Fin m → σ} {k k' : Fin ((q + 1 - p) + (y' + 1 - x))}
    (hd : IsDistinct β (pairEmb p q x y' hq hy' k) (pairEmb p q x y' hq hy' k'))
    (hk : (k : ℕ) ≤ q - p + 1) (hk' : q - p ≤ (k' : ℕ)) :
    winLen k k' ≤ childVal p q x y' hpq hq hy' β :=
  le_bldsFun (hd.comp_strictMono (pairEmb_strictMono hpq hqx hq hy')) ⟨hk, hk'⟩

/-- Upper bounds on the child are checked window by window. -/
lemma childVal_le_of {p q x y' : ℕ} {hpq : p ≤ q} {hq : q < m} {hy' : y' < m}
    {β : Fin m → σ} {c : ℕ}
    (h : ∀ k k' : Fin ((q + 1 - p) + (y' + 1 - x)),
      IsDistinct (β ∘ pairEmb p q x y' hq hy') k k' →
      (k : ℕ) ≤ q - p + 1 → q - p ≤ (k' : ℕ) → winLen k k' ≤ c) :
    childVal p q x y' hpq hq hy' β ≤ c :=
  bldsFun_le_of fun k k' hd ht => h k k' hd ht.1 ht.2

/-! ### Child witnesses

The three shapes of child window used by Proposition 34: the whole left part,
a window inside the left part reaching the glue, and one that crosses into the
right part. -/

/-- A parent window `[l, q]` inside the left part. -/
lemma childVal_ge_left {p q x y' : ℕ} {hpq : p ≤ q} {hq : q < m} {hy' : y' < m}
    (hqx : q < x) {β : Fin m → σ} {l qq : Fin m} (hpl : p ≤ (l : ℕ))
    (hlq : (l : ℕ) ≤ q) (hqq : (qq : ℕ) = q) (hd : IsDistinct β l qq) :
    q - (l : ℕ) + 1 ≤ childVal p q x y' hpq hq hy' β := by
  have hk : (l : ℕ) - p < (q + 1 - p) + (y' + 1 - x) := by omega
  have hk' : q - p < (q + 1 - p) + (y' + 1 - x) := by omega
  have hel : pairEmb p q x y' hq hy' ⟨(l : ℕ) - p, hk⟩ = l :=
    pairEmb_mk_left hq hy' hpl hlq hk
  have heq : pairEmb p q x y' hq hy' ⟨q - p, hk'⟩ = qq := by
    apply Fin.ext
    rw [pairEmb_val]
    have hv : ((⟨q - p, hk'⟩ : Fin ((q + 1 - p) + (y' + 1 - x))) : ℕ) = q - p := rfl
    rw [hv]
    split_ifs <;> omega
  have := le_childVal (hpq := hpq) (hq := hq) (hy' := hy') hqx
    (k := ⟨(l : ℕ) - p, hk⟩) (k' := ⟨q - p, hk'⟩) (by rw [hel, heq]; exact hd)
    (by simpa using by omega) (by simp)
  simp only [winLen] at this
  omega

/-- A parent window `[l, r]` with `l` in the left part and `r` in the right. -/
lemma childVal_ge_both {p q x y' : ℕ} {hpq : p ≤ q} {hq : q < m} {hy' : y' < m}
    (hqx : q < x) {β : Fin m → σ} {l r : Fin m} (hpl : p ≤ (l : ℕ))
    (hlq : (l : ℕ) ≤ q) (hxr : x ≤ (r : ℕ)) (hry : (r : ℕ) ≤ y')
    (hd : IsDistinct β l r) :
    (q - (l : ℕ) + 1) + ((r : ℕ) - x + 1) ≤ childVal p q x y' hpq hq hy' β := by
  have hk : (l : ℕ) - p < (q + 1 - p) + (y' + 1 - x) := by omega
  have hk' : (q + 1 - p) + ((r : ℕ) - x) < (q + 1 - p) + (y' + 1 - x) := by omega
  have hel : pairEmb p q x y' hq hy' ⟨(l : ℕ) - p, hk⟩ = l :=
    pairEmb_mk_left hq hy' hpl hlq hk
  have her : pairEmb p q x y' hq hy' ⟨(q + 1 - p) + ((r : ℕ) - x), hk'⟩ = r :=
    pairEmb_mk_right hq hy' hxr hry hk'
  have := le_childVal (hpq := hpq) (hq := hq) (hy' := hy') hqx
    (k := ⟨(l : ℕ) - p, hk⟩) (k' := ⟨(q + 1 - p) + ((r : ℕ) - x), hk'⟩)
    (by rw [hel, her]; exact hd) (by simpa using by omega) (by simpa using by omega)
  simp only [winLen] at this
  omega

/-- A parent window `[x, r]` inside the right part: it still meets the child's
glue, since `x` is the child's successor of `q`. -/
lemma childVal_ge_right {p q x y' : ℕ} {hpq : p ≤ q} {hq : q < m} {hy' : y' < m}
    (hqx : q < x) {β : Fin m → σ} {xx r : Fin m} (hxx : (xx : ℕ) = x)
    (hxr : x ≤ (r : ℕ)) (hry : (r : ℕ) ≤ y') (hd : IsDistinct β xx r) :
    (r : ℕ) - x + 1 ≤ childVal p q x y' hpq hq hy' β := by
  have hk : (q + 1 - p) + ((xx : ℕ) - x) < (q + 1 - p) + (y' + 1 - x) := by omega
  have hk' : (q + 1 - p) + ((r : ℕ) - x) < (q + 1 - p) + (y' + 1 - x) := by omega
  have hex : pairEmb p q x y' hq hy' ⟨(q + 1 - p) + ((xx : ℕ) - x), hk⟩ = xx :=
    pairEmb_mk_right hq hy' (by omega) (by omega) hk
  have her : pairEmb p q x y' hq hy' ⟨(q + 1 - p) + ((r : ℕ) - x), hk'⟩ = r :=
    pairEmb_mk_right hq hy' hxr hry hk'
  have := le_childVal (hpq := hpq) (hq := hq) (hy' := hy') hqx
    (k := ⟨(q + 1 - p) + ((xx : ℕ) - x), hk⟩)
    (k' := ⟨(q + 1 - p) + ((r : ℕ) - x), hk'⟩)
    (by rw [hex, her]; exact hd) (by simpa using by omega) (by simpa using by omega)
  simp only [winLen] at this
  omega

/-! ## Gluing

The converse transfer: a child window is distinct *as a child window*, which
says nothing about the parent positions the child deleted.  Three facts close
the gap — and they are exactly what the anchor, the cap and the truncation
establish. -/

/-- **Gluing.**  A repeat inside `[l, r]` has both ends in `[l, x-1]`, both in
`[q+1, r]`, or one in each of `[l, q]` and `[x, r]`; the three hypotheses kill
the three cases. -/
lemma isDistinct_of_glue {β : Fin m → σ} {l qq xx rr qs : Fin m}
    (hqs : (qs : ℕ) = (qq : ℕ) + 1)
    (hleft : IsDistinct β l (predIdx xx)) (hright : IsDistinct β qs rr)
    (hcross : ∀ a b : Fin m, (l : ℕ) ≤ (a : ℕ) → (a : ℕ) ≤ (qq : ℕ) →
      (xx : ℕ) ≤ (b : ℕ) → (b : ℕ) ≤ (rr : ℕ) → β a ≠ β b) :
    IsDistinct β l rr := by
  have key : ∀ a b : Fin m, (l : ℕ) ≤ (a : ℕ) → (b : ℕ) ≤ (rr : ℕ) →
      (a : ℕ) ≤ (b : ℕ) → β a = β b → a = b := by
    intro a b hla hbr hab hval
    by_cases hb2 : (b : ℕ) ≤ (xx : ℕ) - 1
    · exact hleft a (Finset.mem_Icc.mpr ⟨hla, by rw [Fin.le_def, predIdx_val]; omega⟩)
        b (Finset.mem_Icc.mpr ⟨by rw [Fin.le_def]; omega,
          by rw [Fin.le_def, predIdx_val]; omega⟩) hval
    · by_cases ha3 : (qq : ℕ) < (a : ℕ)
      · exact hright a (Finset.mem_Icc.mpr ⟨by rw [Fin.le_def]; omega,
          by rw [Fin.le_def]; omega⟩)
          b (Finset.mem_Icc.mpr ⟨by rw [Fin.le_def]; omega, by rw [Fin.le_def]; omega⟩) hval
      · exact absurd hval (hcross a b hla (by omega) (by omega) hbr)
  intro a ha b hb hval
  rw [Finset.mem_Icc] at ha hb
  have hla : (l : ℕ) ≤ (a : ℕ) := ha.1
  have har : (a : ℕ) ≤ (rr : ℕ) := ha.2
  have hlb : (l : ℕ) ≤ (b : ℕ) := hb.1
  have hbr : (b : ℕ) ≤ (rr : ℕ) := hb.2
  rcases le_total (a : ℕ) (b : ℕ) with hab | hab
  · exact key a b hla hbr hab hval
  · exact (key b a hlb har hab hval.symm).symm

/-! ## Proposition 34 -/

/-- **Proposition 34 in arena coordinates**. For a part `[x, y]` of the node's
right part, the parent's
contribution from right endpoints in `K⁺ = {x-1} ∪ [x, y]` is the child's value
shifted by the constant `x - q - 1` — the number of parent positions the child
deletes.

The hypotheses are the *properties* of the anchor `p = Λ(x-1)`, the cap
`q = min(g, p + t - 1)` and the truncation `y' = ρ_y(q+1)`, so that the caller
supplies them from `LDS/Defs.lean` and no definitional unfolding leaks into the
recursion. -/
theorem sup_lambda_eq_childVal
    {β : Fin m → σ} {g x y p q qs y' : Fin m}
    (hglue : IsDistinct β g (lastIdx g))
    (hgx : (g : ℕ) < (x : ℕ)) (hxy : (x : ℕ) ≤ (y : ℕ))
    (hpdist : IsDistinct β p (predIdx x))
    (hpmin : ∀ i : Fin m, (i : ℕ) ≤ (x : ℕ) - 1 → IsDistinct β i (predIdx x) →
      (p : ℕ) ≤ (i : ℕ))
    (hpq : (p : ℕ) ≤ (q : ℕ))
    (hqcap : (q : ℕ) = min (g : ℕ) ((p : ℕ) + winLen x y - 1))
    (hqs : (qs : ℕ) = (q : ℕ) + 1)
    (hy'dist : IsDistinct β qs y') (hy'le : (y' : ℕ) ≤ (y : ℕ))
    (hy'max : ∀ r : Fin m, (r : ℕ) ≤ (y : ℕ) → IsDistinct β qs r → (r : ℕ) ≤ (y' : ℕ)) :
    (Finset.Icc (predIdx x) y).sup (fun r => winLen (lambdaFun β (firstIdx g) r) r)
      = ((x : ℕ) - (q : ℕ) - 1)
        + childVal (p : ℕ) (q : ℕ) (x : ℕ) (y' : ℕ) hpq q.isLt y'.isLt β := by
  have hgm := g.isLt
  have hxlt := x.isLt
  have hylt := y.isLt
  have hqlt := q.isLt
  have hy'lt := y'.isLt
  simp only [winLen] at hqcap
  have hqg : (q : ℕ) ≤ (g : ℕ) := by omega
  have hqx : (q : ℕ) < (x : ℕ) := by omega
  have hfirst : ∀ r : Fin m, firstIdx g ≤ r := firstIdx_le' g
  -- the glue invariant forces the anchor into the left part
  have hpg : (p : ℕ) ≤ (g : ℕ) :=
    hpmin g (by omega) (hglue.mono le_rfl (le_lastIdx g _))
  have hqy' : (q : ℕ) + 1 ≤ (y' : ℕ) := by
    have := hy'max qs (by omega) (isDistinct_self β qs)
    omega
  -- the anchor's window reaches the cap, so `Λ(x-1) ≤ q`
  have hlamq : (lambdaFun β (firstIdx g) (predIdx x) : ℕ) ≤ (q : ℕ) := by
    have := lambdaFun_le_of_isDistinct (α := β) (a := firstIdx g) (i := q)
      (j := predIdx x) (hfirst q) (by rw [Fin.le_def, predIdx_val]; omega)
      (hpdist.mono (by rw [Fin.le_def]; omega) le_rfl)
    rw [Fin.le_def] at this
    exact this
  refine le_antisymm ?_ ?_
  · -- every parent window is captured by the child, up to the offset
    refine Finset.sup_le fun r hr => ?_
    rw [Finset.mem_Icc] at hr
    have hxmr : (x : ℕ) - 1 ≤ (r : ℕ) := by
      have := hr.1
      rw [Fin.le_def, predIdx_val] at this
      exact this
    have hry : (r : ℕ) ≤ (y : ℕ) := hr.2
    have hlr : (lambdaFun β (firstIdx g) r : ℕ) ≤ (r : ℕ) := lambdaFun_le (hfirst r)
    have hld : IsDistinct β (lambdaFun β (firstIdx g) r) r := isDistinct_lambdaFun (hfirst r)
    have hpl : (p : ℕ) ≤ (lambdaFun β (firstIdx g) r : ℕ) := by
      by_cases hc : (lambdaFun β (firstIdx g) r : ℕ) ≤ (x : ℕ) - 1
      · exact hpmin _ hc (hld.mono le_rfl (by rw [Fin.le_def, predIdx_val]; omega))
      · omega
    -- the glue invariant caps the anchor at `g + 1`
    have hlg : (lambdaFun β (firstIdx g) r : ℕ) ≤ (g : ℕ) + 1 :=
      lambdaFun_le_glue hglue (by omega)
    rcases le_or_gt (lambdaFun β (firstIdx g) r : ℕ) ((q : ℕ) + 1) with hcase | hcase
    · rcases le_or_gt (x : ℕ) (r : ℕ) with hxr | hxr
      · -- the window crosses into the right part; the truncation does not cut it
        have hry' : (r : ℕ) ≤ (y' : ℕ) :=
          hy'max r hry (hld.mono (by rw [Fin.le_def]; omega) le_rfl)
        rcases le_or_gt (lambdaFun β (firstIdx g) r : ℕ) (q : ℕ) with hlq | hlq
        · have := childVal_ge_both (hpq := hpq) (hq := q.isLt) (hy' := y'.isLt) hqx
            (l := lambdaFun β (firstIdx g) r) (r := r) hpl hlq hxr hry' hld
          simp only [winLen]
          omega
        · have := childVal_ge_right (hpq := hpq) (hq := q.isLt) (hy' := y'.isLt) hqx
            (xx := x) (r := r) rfl hxr hry'
            (hld.mono (by rw [Fin.le_def]; omega) le_rfl)
          simp only [winLen]
          omega
      · -- the window stops at `x - 1`: only the child's left part is used
        rcases le_or_gt (lambdaFun β (firstIdx g) r : ℕ) (q : ℕ) with hlq | hlq
        · have := childVal_ge_left (hpq := hpq) (hq := q.isLt) (hy' := y'.isLt) hqx
            (l := lambdaFun β (firstIdx g) r) (qq := q) hpl hlq rfl
            (hld.mono le_rfl (by rw [Fin.le_def]; omega))
          simp only [winLen]
          omega
        · simp only [winLen]
          omega
    · -- the cap binds: the window lives past `q + 1`, hence is short
      have hqlt' : (q : ℕ) < (g : ℕ) := by omega
      have hleft := childVal_ge_left (hpq := hpq) (hq := q.isLt) (hy' := y'.isLt) hqx
        (l := p) (qq := q) le_rfl hpq rfl
        (hpdist.mono le_rfl (by rw [Fin.le_def, predIdx_val]; omega))
      simp only [winLen]
      omega
  · -- every child window comes from a parent window with the same endpoints
    have hoff : (x : ℕ) - (q : ℕ) - 1
        < (Finset.Icc (predIdx x) y).sup (fun r => winLen (lambdaFun β (firstIdx g) r) r) := by
      have hmem : predIdx x ∈ Finset.Icc (predIdx x) y :=
        Finset.mem_Icc.mpr ⟨le_rfl, by rw [Fin.le_def, predIdx_val]; omega⟩
      have hle := Finset.le_sup (f := fun r => winLen (lambdaFun β (firstIdx g) r) r) hmem
      have hw : winLen (lambdaFun β (firstIdx g) (predIdx x)) (predIdx x)
          = (x : ℕ) - (lambdaFun β (firstIdx g) (predIdx x) : ℕ) := by
        simp only [winLen, predIdx_val]
        omega
      omega
    have key : childVal (p : ℕ) (q : ℕ) (x : ℕ) (y' : ℕ) hpq q.isLt y'.isLt β
        ≤ (Finset.Icc (predIdx x) y).sup (fun r => winLen (lambdaFun β (firstIdx g) r) r)
            - ((x : ℕ) - (q : ℕ) - 1) := by
      refine childVal_le_of fun k k' hd hk hk' => ?_
      rcases le_or_gt (k : ℕ) (k' : ℕ) with hkk | hkk
      · have hkv := pairEmb_val (p := (p : ℕ)) (q := (q : ℕ)) (x := (x : ℕ))
          (y := (y' : ℕ)) q.isLt y'.isLt k
        have hk'v := pairEmb_val (p := (p : ℕ)) (q := (q : ℕ)) (x := (x : ℕ))
          (y := (y' : ℕ)) q.isLt y'.isLt k'
        have hkS := k.isLt
        have hk'S := k'.isLt
        rcases le_or_gt (k' : ℕ) ((q : ℕ) - (p : ℕ)) with hk'left | hk'right
        · -- the child window sits inside the left part and ends at the glue
          rw [if_pos (by omega)] at hkv hk'v
          have hkq : (pairEmb (p : ℕ) (q : ℕ) (x : ℕ) (y' : ℕ) q.isLt y'.isLt k : ℕ)
              ≤ (x : ℕ) - 1 := by omega
          have hdp : IsDistinct β (pairEmb (p : ℕ) (q : ℕ) (x : ℕ) (y' : ℕ) q.isLt y'.isLt k)
              (predIdx x) :=
            hpdist.mono (by rw [Fin.le_def]; omega) le_rfl
          have hlam := lambdaFun_le_of_isDistinct (α := β) (a := firstIdx g)
            (i := pairEmb (p : ℕ) (q : ℕ) (x : ℕ) (y' : ℕ) q.isLt y'.isLt k)
            (j := predIdx x) (hfirst _) (by rw [Fin.le_def, predIdx_val]; omega) hdp
          rw [Fin.le_def] at hlam
          have hmem : predIdx x ∈ Finset.Icc (predIdx x) y :=
            Finset.mem_Icc.mpr ⟨le_rfl, by rw [Fin.le_def, predIdx_val]; omega⟩
          have hsup := Finset.le_sup (f := fun r => winLen (lambdaFun β (firstIdx g) r) r) hmem
          simp only [winLen, predIdx_val] at hsup
          simp only [winLen]
          omega
        · -- the child window crosses into the right part
          rw [if_neg (by omega)] at hk'v
          have hrx : (x : ℕ)
              ≤ (pairEmb (p : ℕ) (q : ℕ) (x : ℕ) (y' : ℕ) q.isLt y'.isLt k' : ℕ) := by omega
          have hry' : (pairEmb (p : ℕ) (q : ℕ) (x : ℕ) (y' : ℕ) q.isLt y'.isLt k' : ℕ)
              ≤ (y' : ℕ) := by omega
          have hmem : pairEmb (p : ℕ) (q : ℕ) (x : ℕ) (y' : ℕ) q.isLt y'.isLt k'
              ∈ Finset.Icc (predIdx x) y :=
            Finset.mem_Icc.mpr ⟨by rw [Fin.le_def, predIdx_val]; omega,
              by rw [Fin.le_def]; omega⟩
          have hsup := Finset.le_sup
            (f := fun r => winLen (lambdaFun β (firstIdx g) r) r) hmem
          simp only [winLen] at hsup
          rcases le_or_gt (k : ℕ) ((q : ℕ) - (p : ℕ)) with hkleft | hkright
          · -- ... starting in the left part: glue the two halves
            rw [if_pos (by omega)] at hkv
            have hcross : ∀ a b : Fin m,
                (pairEmb (p : ℕ) (q : ℕ) (x : ℕ) (y' : ℕ) q.isLt y'.isLt k : ℕ) ≤ (a : ℕ) →
                (a : ℕ) ≤ (q : ℕ) → (x : ℕ) ≤ (b : ℕ) →
                (b : ℕ) ≤ (pairEmb (p : ℕ) (q : ℕ) (x : ℕ) (y' : ℕ) q.isLt y'.isLt k' : ℕ) →
                β a ≠ β b := by
              intro a b hka haq hxb hbk hval
              have hab : (a : ℕ) - (p : ℕ)
                  < ((q : ℕ) + 1 - (p : ℕ)) + ((y' : ℕ) + 1 - (x : ℕ)) := by omega
              have hbb : ((q : ℕ) + 1 - (p : ℕ)) + ((b : ℕ) - (x : ℕ))
                  < ((q : ℕ) + 1 - (p : ℕ)) + ((y' : ℕ) + 1 - (x : ℕ)) := by omega
              have hea : pairEmb (p : ℕ) (q : ℕ) (x : ℕ) (y' : ℕ) q.isLt y'.isLt
                  ⟨(a : ℕ) - (p : ℕ), hab⟩ = a :=
                pairEmb_mk_left q.isLt y'.isLt (by omega) haq hab
              have heb : pairEmb (p : ℕ) (q : ℕ) (x : ℕ) (y' : ℕ) q.isLt y'.isLt
                  ⟨((q : ℕ) + 1 - (p : ℕ)) + ((b : ℕ) - (x : ℕ)), hbb⟩ = b :=
                pairEmb_mk_right q.isLt y'.isLt hxb (by omega) hbb
              have hva : ((⟨(a : ℕ) - (p : ℕ), hab⟩ :
                  Fin (((q : ℕ) + 1 - (p : ℕ)) + ((y' : ℕ) + 1 - (x : ℕ)))) : ℕ)
                  = (a : ℕ) - (p : ℕ) := rfl
              have hvb : ((⟨((q : ℕ) + 1 - (p : ℕ)) + ((b : ℕ) - (x : ℕ)), hbb⟩ :
                  Fin (((q : ℕ) + 1 - (p : ℕ)) + ((y' : ℕ) + 1 - (x : ℕ)))) : ℕ)
                  = ((q : ℕ) + 1 - (p : ℕ)) + ((b : ℕ) - (x : ℕ)) := rfl
              have hmema : (⟨(a : ℕ) - (p : ℕ), hab⟩ :
                  Fin (((q : ℕ) + 1 - (p : ℕ)) + ((y' : ℕ) + 1 - (x : ℕ))))
                  ∈ Finset.Icc k k' :=
                Finset.mem_Icc.mpr ⟨by rw [Fin.le_def]; omega, by rw [Fin.le_def]; omega⟩
              have hmemb : (⟨((q : ℕ) + 1 - (p : ℕ)) + ((b : ℕ) - (x : ℕ)), hbb⟩ :
                  Fin (((q : ℕ) + 1 - (p : ℕ)) + ((y' : ℕ) + 1 - (x : ℕ))))
                  ∈ Finset.Icc k k' :=
                Finset.mem_Icc.mpr ⟨by rw [Fin.le_def]; omega, by rw [Fin.le_def]; omega⟩
              have := hd _ hmema _ hmemb (by
                change β (pairEmb (p : ℕ) (q : ℕ) (x : ℕ) (y' : ℕ) q.isLt y'.isLt _)
                  = β (pairEmb (p : ℕ) (q : ℕ) (x : ℕ) (y' : ℕ) q.isLt y'.isLt _)
                rw [hea, heb]
                exact hval)
              have := congrArg Fin.val this
              simp only at this
              omega
            have hpar : IsDistinct β
                (pairEmb (p : ℕ) (q : ℕ) (x : ℕ) (y' : ℕ) q.isLt y'.isLt k)
                (pairEmb (p : ℕ) (q : ℕ) (x : ℕ) (y' : ℕ) q.isLt y'.isLt k') :=
              isDistinct_of_glue (qq := q) (xx := x) (qs := qs) hqs
                (hpdist.mono (by rw [Fin.le_def]; omega) le_rfl)
                (hy'dist.mono le_rfl (by rw [Fin.le_def]; omega)) hcross
            have hlam := lambdaFun_le_of_isDistinct (α := β) (a := firstIdx g)
              (i := pairEmb (p : ℕ) (q : ℕ) (x : ℕ) (y' : ℕ) q.isLt y'.isLt k)
              (j := pairEmb (p : ℕ) (q : ℕ) (x : ℕ) (y' : ℕ) q.isLt y'.isLt k')
              (hfirst _) (by rw [Fin.le_def]; omega) hpar
            rw [Fin.le_def] at hlam
            simp only [winLen]
            omega
          · -- ... starting at the child's successor of the glue
            rw [if_neg (by omega)] at hkv
            have hkx : (pairEmb (p : ℕ) (q : ℕ) (x : ℕ) (y' : ℕ) q.isLt y'.isLt k : ℕ)
                = (x : ℕ) := by omega
            have hlam := lambdaFun_le_of_isDistinct (α := β) (a := firstIdx g) (i := qs)
              (j := pairEmb (p : ℕ) (q : ℕ) (x : ℕ) (y' : ℕ) q.isLt y'.isLt k')
              (hfirst _) (by rw [Fin.le_def]; omega)
              (hy'dist.mono le_rfl (by rw [Fin.le_def]; omega))
            rw [Fin.le_def] at hlam
            simp only [winLen]
            omega
      · -- a degenerate child window
        simp only [winLen]
        omega
    omega

/-- **The child is at most twice its part**: the
cap keeps the left part shorter than `t = |[x, y]|` and the truncation keeps
the right part shorter than `t`, so an `h`-way split shrinks the arena by
`h / 2`. -/
lemma childSize_le_two_mul {x y p q y' : Fin m} {gv : ℕ} (hxy : (x : ℕ) ≤ (y : ℕ))
    (hqcap : (q : ℕ) = min gv ((p : ℕ) + winLen x y - 1))
    (hy'le : (y' : ℕ) ≤ (y : ℕ)) :
    ((q : ℕ) + 1 - (p : ℕ)) + ((y' : ℕ) + 1 - (x : ℕ)) ≤ 2 * winLen x y := by
  simp only [winLen] at hqcap ⊢
  omega

/-! ## Corollary 35

The node value is the maximum over the parts of the shifted child values.  The
parts must cover the right endpoints past the glue — with `K⁺_ℓ` reaching one
position to the left of the part, so the first part covers the glue itself —
but they need not be disjoint: overlapping covers are harmless for a maximum,
which is what lets every part use `{x_ℓ - 1} ∪ [x_ℓ, y_ℓ]`. -/

/-- **Corollary 35 in arena coordinates**. On the fixed-descriptor promise
the offsets are constants, so
this exhibits a normalized node as a maximum of shifted children — the shape
the weighted scan consumes. -/
theorem bldsFun_eq_sup_children {ι : Type*} [Fintype ι]
    {β : Fin m → σ} {g : Fin m} {x y p q qs y' : ι → Fin m}
    (hglue : IsDistinct β g (lastIdx g))
    (hgx : ∀ ℓ, (g : ℕ) < (x ℓ : ℕ)) (hxy : ∀ ℓ, (x ℓ : ℕ) ≤ (y ℓ : ℕ))
    (hpdist : ∀ ℓ, IsDistinct β (p ℓ) (predIdx (x ℓ)))
    (hpmin : ∀ ℓ, ∀ i : Fin m, (i : ℕ) ≤ (x ℓ : ℕ) - 1 → IsDistinct β i (predIdx (x ℓ)) →
      (p ℓ : ℕ) ≤ (i : ℕ))
    (hpq : ∀ ℓ, (p ℓ : ℕ) ≤ (q ℓ : ℕ))
    (hqcap : ∀ ℓ, (q ℓ : ℕ) = min (g : ℕ) ((p ℓ : ℕ) + winLen (x ℓ) (y ℓ) - 1))
    (hqs : ∀ ℓ, (qs ℓ : ℕ) = (q ℓ : ℕ) + 1)
    (hy'dist : ∀ ℓ, IsDistinct β (qs ℓ) (y' ℓ))
    (hy'le : ∀ ℓ, (y' ℓ : ℕ) ≤ (y ℓ : ℕ))
    (hy'max : ∀ ℓ, ∀ r : Fin m, (r : ℕ) ≤ (y ℓ : ℕ) → IsDistinct β (qs ℓ) r →
      (r : ℕ) ≤ (y' ℓ : ℕ))
    (hcover : ∀ r : Fin m, (g : ℕ) ≤ (r : ℕ) →
      ∃ ℓ, (x ℓ : ℕ) - 1 ≤ (r : ℕ) ∧ (r : ℕ) ≤ (y ℓ : ℕ)) :
    bldsFun g β = Finset.univ.sup fun ℓ : ι =>
      ((x ℓ : ℕ) - (q ℓ : ℕ) - 1)
        + childVal (p ℓ : ℕ) (q ℓ : ℕ) (x ℓ : ℕ) (y' ℓ : ℕ) (hpq ℓ) (q ℓ).isLt
            (y' ℓ).isLt β := by
  have hpart : ∀ ℓ : ι,
      (Finset.Icc (predIdx (x ℓ)) (y ℓ)).sup (fun r => winLen (lambdaFun β (firstIdx g) r) r)
        = ((x ℓ : ℕ) - (q ℓ : ℕ) - 1)
          + childVal (p ℓ : ℕ) (q ℓ : ℕ) (x ℓ : ℕ) (y' ℓ : ℕ) (hpq ℓ) (q ℓ).isLt
              (y' ℓ).isLt β := fun ℓ =>
    sup_lambda_eq_childVal hglue (hgx ℓ) (hxy ℓ) (hpdist ℓ) (hpmin ℓ) (hpq ℓ) (hqcap ℓ)
      (hqs ℓ) (hy'dist ℓ) (hy'le ℓ) (hy'max ℓ)
  rw [bldsFun_eq_sup_lambda_of_glue hglue]
  refine le_antisymm (Finset.sup_le fun r hr => ?_) (Finset.sup_le fun ℓ _ => ?_)
  · rw [Finset.mem_Icc] at hr
    have hgr : (g : ℕ) ≤ (r : ℕ) := hr.1
    obtain ⟨ℓ, hl1, hl2⟩ := hcover r hgr
    refine le_trans ?_ (Finset.le_sup (f := fun ℓ : ι =>
      ((x ℓ : ℕ) - (q ℓ : ℕ) - 1)
        + childVal (p ℓ : ℕ) (q ℓ : ℕ) (x ℓ : ℕ) (y' ℓ : ℕ) (hpq ℓ) (q ℓ).isLt
            (y' ℓ).isLt β) (Finset.mem_univ ℓ))
    rw [← hpart ℓ]
    exact Finset.le_sup (f := fun r => winLen (lambdaFun β (firstIdx g) r) r)
      (Finset.mem_Icc.mpr ⟨by rw [Fin.le_def, predIdx_val]; omega, by rw [Fin.le_def]; omega⟩)
  · rw [← hpart ℓ]
    refine Finset.sup_le fun r hr => ?_
    rw [Finset.mem_Icc] at hr
    have hxr : (x ℓ : ℕ) - 1 ≤ (r : ℕ) := by
      have := hr.1
      rw [Fin.le_def, predIdx_val] at this
      exact this
    have := hgx ℓ
    exact Finset.le_sup (f := fun r => winLen (lambdaFun β (firstIdx g) r) r)
      (Finset.mem_Icc.mpr ⟨by rw [Fin.le_def]; omega, le_lastIdx g r⟩)

/-! ## The normalized window as a sub-arena

Normalization shrinks the arena to a *contiguous* window `[a, b]`, which
`LDS/Node.lean` records without re-indexing (`bldsIn`).  The recursion,
however, hands the normalized arena to Corollary 35 as a word in its own
right, so the two views have to be identified once: `bldsIn a b g β` is
`bldsFun` of the sub-word, with the glue at `g - a`.

Unlike the two-interval case, here distinctness transfers in **both**
directions — the image of a child window is the parent window itself, not a
proper subset of it — so no gluing hypothesis is needed. -/

/-- The contiguous sub-arena `[a, b]`. -/
def intervalEmb (a b : ℕ) (hb : b < m) (k : Fin (b + 1 - a)) : Fin m :=
  ⟨a + (k : ℕ), by have := k.isLt; omega⟩

@[simp] lemma intervalEmb_val {a b : ℕ} (hb : b < m) (k : Fin (b + 1 - a)) :
    (intervalEmb a b hb k : ℕ) = a + (k : ℕ) := rfl

lemma intervalEmb_strictMono {a b : ℕ} (hb : b < m) :
    StrictMono (intervalEmb a b hb) := by
  intro k k' hkk
  rw [Fin.lt_def] at hkk ⊢
  simp only [intervalEmb_val]
  omega

/-- Distinctness of a window of the sub-word is distinctness of the
corresponding window of the parent — both ways. -/
lemma isDistinct_intervalEmb {β : Fin m → σ} {a b : ℕ} (hb : b < m)
    (k k' : Fin (b + 1 - a)) :
    IsDistinct (β ∘ intervalEmb a b hb) k k'
      ↔ IsDistinct β (intervalEmb a b hb k) (intervalEmb a b hb k') := by
  refine ⟨fun h z hz w hw hzw => ?_,
    fun h => h.comp_strictMono (intervalEmb_strictMono hb)⟩
  rw [Finset.mem_Icc, Fin.le_def, Fin.le_def] at hz hw
  simp only [intervalEmb_val] at hz hw
  have hk := k.isLt
  have hk' := k'.isLt
  have hzb : (z : ℕ) - a < b + 1 - a := by omega
  have hwb : (w : ℕ) - a < b + 1 - a := by omega
  have hez : intervalEmb a b hb ⟨(z : ℕ) - a, hzb⟩ = z := by
    apply Fin.ext
    simp only [intervalEmb_val]
    omega
  have hew : intervalEmb a b hb ⟨(w : ℕ) - a, hwb⟩ = w := by
    apply Fin.ext
    simp only [intervalEmb_val]
    omega
  have := h ⟨(z : ℕ) - a, hzb⟩ (Finset.mem_Icc.mpr
      ⟨by rw [Fin.le_def]; simp only; omega, by rw [Fin.le_def]; simp only; omega⟩)
    ⟨(w : ℕ) - a, hwb⟩ (Finset.mem_Icc.mpr
      ⟨by rw [Fin.le_def]; simp only; omega, by rw [Fin.le_def]; simp only; omega⟩)
    (by change β (intervalEmb a b hb _) = β (intervalEmb a b hb _)
        rw [hez, hew]; exact hzw)
  have := congrArg Fin.val this
  simp only at this
  exact Fin.ext (by omega)

/-- **The normalized window, re-indexed**: the node problem cut to `[a, b]` is
the node problem of the sub-word, glued at `g - a`. -/
theorem bldsIn_eq_bldsFun {β : Fin m → σ} {a b g : Fin m} (hag : a ≤ g)
    (hgb : g ≤ b) :
    bldsIn a b g β
      = bldsFun (⟨(g : ℕ) - (a : ℕ), by have := b.isLt; rw [Fin.le_def] at hag hgb; omega⟩ :
          Fin ((b : ℕ) + 1 - (a : ℕ)))
          (β ∘ intervalEmb (a : ℕ) (b : ℕ) b.isLt) := by
  rw [Fin.le_def] at hag hgb
  have hbm := b.isLt
  refine le_antisymm (Finset.sup_le fun p _ => ?_) (bldsFun_le_of fun k k' hd ht => ?_)
  · split
    · rename_i h
      obtain ⟨hal, hrb, hdd, ht⟩ := h
      rw [Fin.le_def] at hal hrb
      rcases le_or_gt (p.1 : ℕ) (p.2 : ℕ) with hle | hlt
      swap
      · simp only [winLen]
        omega
      have hkb : (p.1 : ℕ) - (a : ℕ) < (b : ℕ) + 1 - (a : ℕ) := by omega
      have hk'b : (p.2 : ℕ) - (a : ℕ) < (b : ℕ) + 1 - (a : ℕ) := by omega
      have hel : intervalEmb (a : ℕ) (b : ℕ) b.isLt ⟨(p.1 : ℕ) - (a : ℕ), hkb⟩ = p.1 :=
        Fin.ext (by simp only [intervalEmb_val]; omega)
      have her : intervalEmb (a : ℕ) (b : ℕ) b.isLt ⟨(p.2 : ℕ) - (a : ℕ), hk'b⟩ = p.2 :=
        Fin.ext (by simp only [intervalEmb_val]; omega)
      have hdc : IsDistinct (β ∘ intervalEmb (a : ℕ) (b : ℕ) b.isLt)
          ⟨(p.1 : ℕ) - (a : ℕ), hkb⟩ ⟨(p.2 : ℕ) - (a : ℕ), hk'b⟩ := by
        rw [isDistinct_intervalEmb, hel, her]
        exact hdd
      have htc : Touches (⟨(g : ℕ) - (a : ℕ), by omega⟩ :
          Fin ((b : ℕ) + 1 - (a : ℕ))) ⟨(p.1 : ℕ) - (a : ℕ), hkb⟩
            ⟨(p.2 : ℕ) - (a : ℕ), hk'b⟩ := by
        obtain ⟨ht1, ht2⟩ := ht
        constructor <;> simp only <;> omega
      have := le_bldsFun hdc htc
      simp only [winLen] at this ⊢
      omega
    · exact Nat.zero_le _
  · have hk := k.isLt
    have hk' := k'.isLt
    rw [isDistinct_intervalEmb] at hd
    obtain ⟨ht1, ht2⟩ := ht
    simp only at ht1 ht2
    have := le_bldsIn (a := a) (b := b) (g := g)
      (l := intervalEmb (a : ℕ) (b : ℕ) b.isLt k)
      (r := intervalEmb (a : ℕ) (b : ℕ) b.isLt k')
      (by rw [Fin.le_def]; simp only [intervalEmb_val]; omega)
      (by rw [Fin.le_def]; simp only [intervalEmb_val]; omega) hd
      ⟨by simp only [intervalEmb_val]; omega, by simp only [intervalEmb_val]; omega⟩
    simp only [winLen, intervalEmb_val] at this ⊢
    omega

/-! ## Sanity checks

Concrete values pin the behavior of `pairEmb` and `childVal` under refactoring. -/

section Sanity

set_option maxRecDepth 10000

/-- The child of `β = 01201` at the glue `2` for the part `[3, 4]`: the anchor
is `p = 0`, the cap gives `q = 1` and the truncation is inactive, so the child
arena is `[0,1] ∪ [3,4]`, i.e. the word `0101` glued at `1`. -/
example : childVal 0 1 3 4 (by omega) (by omega) (by omega) ![0, 1, 2, 0, 1] = 2 := by decide

/-- **Proposition 34** on that instance: the parent's right endpoints in
`{2} ∪ [3, 4]` give `3`, and the child gives `2` with offset `x - q - 1 = 1`. -/
example : (Finset.Icc (predIdx (3 : Fin 5)) 4).sup
      (fun r => winLen (lambdaFun ![0, 1, 2, 0, 1] (firstIdx (2 : Fin 5)) r) r)
    = 1 + childVal 0 1 3 4 (by omega) (by omega) (by omega) ![0, 1, 2, 0, 1] := by decide

/-- The truncation can delete the child's whole right part (`y' < x`): for
`β = 0121` at the glue `2` with the part `[3, 3]`, the child is the single
letter `0`.  The empty right part needs no special case — the arena type is
`Fin 1` and `bldsFun` degenerates on its own. -/
example : childVal 0 0 3 2 (by omega) (by omega) (by omega) ![0, 1, 2, 1] = 1 := by decide

example : (Finset.Icc (predIdx (3 : Fin 4)) 3).sup
      (fun r => winLen (lambdaFun ![0, 1, 2, 1] (firstIdx (2 : Fin 4)) r) r)
    = 2 + childVal 0 0 3 2 (by omega) (by omega) (by omega) ![0, 1, 2, 1] := by decide

end Sanity

end QuantumQueryComplexity
