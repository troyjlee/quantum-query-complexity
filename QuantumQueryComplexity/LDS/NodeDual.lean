import QuantumQueryComplexity.LDS.Recur
import QuantumQueryComplexity.LDS.Cost
import QuantumQueryComplexity.Promise.Transport
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The node recursion on the dual side

This file carries the ingredients of the induction:

* `exists_natEncode` — on a finite promise domain any output can be recoded to
  `ℕ` with the same kernel, so a node can export its descriptor chain as a
  plain natural number.  This is what makes the **export type uniform** across
  arena sizes, which the outer scan needs (its slots must share one alphabet)
  while the joint-output discipline forbids projecting the chain away.
* `nodePartSize`/`nodeParts` — the split parameters, chosen so that the number
  of parts never exceeds `nodeArity` (that is what the cost function budgets)
  and the part size stays below `n₂/h + 1` (that is what makes the children
  shrink).  Ceiling division is spelled out with `Nat.div_mul_le_self` rather
  than a `⌈⌉` API, so every step is `omega`-checkable.
* `hasDualOn_bldsFun_small` — the base case: on a small arena the
  read-everything dual is within budget.
-/

namespace QuantumQueryComplexity

/-! ## Uniform export type -/

/-- **Recoding a finite-domain output to `ℕ`.**  Same kernel, so `ofKer`
transports any dual solution at the same cost. -/
lemma exists_natEncode {X V : Type} [Fintype X] [DecidableEq X] [DecidableEq V]
    (F : X → V) : ∃ F' : X → ℕ, ∀ x y, F x = F y ↔ F' x = F' y := by
  classical
  refine ⟨fun x => ((Fintype.equivFin {v // v ∈ Finset.image F Finset.univ})
    ⟨F x, Finset.mem_image_of_mem _ (Finset.mem_univ x)⟩ : Fin _), fun x y => ?_⟩
  constructor
  · intro h
    simp only [h]
  · intro h
    have hfin : (Fintype.equivFin {v // v ∈ Finset.image F Finset.univ})
        ⟨F x, Finset.mem_image_of_mem _ (Finset.mem_univ x)⟩
        = (Fintype.equivFin {v // v ∈ Finset.image F Finset.univ})
          ⟨F y, Finset.mem_image_of_mem _ (Finset.mem_univ y)⟩ := Fin.ext h
    exact congrArg Subtype.val ((Fintype.equivFin _).injective hfin)

/-! ## The split parameters -/

/-- The part size of a node whose right part has `n₂` positions: `⌈n₂ / h⌉`,
never `0`. -/
def nodePartSize (n : ℕ) : ℕ := max 1 ((n + nodeArity - 1) / nodeArity)

/-- The number of parts: `⌈n₂ / t⌉`. -/
def nodeParts (n : ℕ) : ℕ := (n + nodePartSize n - 1) / nodePartSize n

lemma nodeArity_pos : 0 < nodeArity := by
  unfold nodeArity
  positivity

lemma one_le_nodePartSize (n : ℕ) : 1 ≤ nodePartSize n := le_max_left _ _

/-- The parts cover the right part. -/
lemma nodeRight_le (n : ℕ) : n ≤ nodeParts n * nodePartSize n := by
  have ht := one_le_nodePartSize n
  have hdm := Nat.div_add_mod (n + nodePartSize n - 1) (nodePartSize n)
  have hmod : (n + nodePartSize n - 1) % nodePartSize n < nodePartSize n :=
    Nat.mod_lt _ (by omega)
  have hcomm : nodeParts n * nodePartSize n
      = nodePartSize n * ((n + nodePartSize n - 1) / nodePartSize n) := by
    rw [nodeParts, Nat.mul_comm]
  omega

/-- Every part is nonempty. -/
lemma nodeParts_lt (n : ℕ) {ℓ : ℕ} (hℓ : ℓ < nodeParts n) :
    ℓ * nodePartSize n < n := by
  have ht := one_le_nodePartSize n
  have hle : nodeParts n * nodePartSize n ≤ n + nodePartSize n - 1 :=
    Nat.div_mul_le_self _ _
  have hmul : (ℓ + 1) * nodePartSize n ≤ nodeParts n * nodePartSize n :=
    Nat.mul_le_mul_right _ hℓ
  have hexp : (ℓ + 1) * nodePartSize n = ℓ * nodePartSize n + nodePartSize n := by ring
  omega

/-- The arity is never exceeded — this is what the cost function budgets. -/
lemma nodeParts_le_arity (n : ℕ) : nodeParts n ≤ nodeArity := by
  have ht := one_le_nodePartSize n
  have hA := nodeArity_pos
  -- `t · h ≥ n`, since `t ≥ ⌈n/h⌉`
  have hth : n ≤ nodePartSize n * nodeArity := by
    rcases le_or_gt ((n + nodeArity - 1) / nodeArity) 1 with hsmall | hbig
    · have hdm := Nat.div_add_mod (n + nodeArity - 1) nodeArity
      have hmod : (n + nodeArity - 1) % nodeArity < nodeArity := Nat.mod_lt _ hA
      have h1 : nodePartSize n = 1 := by
        rw [nodePartSize]
        omega
      have hmul : nodeArity * ((n + nodeArity - 1) / nodeArity) ≤ nodeArity * 1 :=
        Nat.mul_le_mul_left _ hsmall
      rw [h1]
      omega
    · have hps : nodePartSize n = (n + nodeArity - 1) / nodeArity := by
        rw [nodePartSize]
        omega
      have hdm := Nat.div_add_mod (n + nodeArity - 1) nodeArity
      have hmod : (n + nodeArity - 1) % nodeArity < nodeArity := Nat.mod_lt _ hA
      have hcomm : nodePartSize n * nodeArity
          = nodeArity * ((n + nodeArity - 1) / nodeArity) := by
        rw [hps, Nat.mul_comm]
      omega
  -- and `q · t ≤ n + t - 1`, so `q < h + 1`
  have hqt : nodeParts n * nodePartSize n ≤ n + nodePartSize n - 1 :=
    Nat.div_mul_le_self _ _
  by_contra hcon
  have hlt : nodeArity + 1 ≤ nodeParts n := by omega
  have hmul : (nodeArity + 1) * nodePartSize n ≤ nodeParts n * nodePartSize n :=
    Nat.mul_le_mul_right _ hlt
  have hexp : (nodeArity + 1) * nodePartSize n
      = nodeArity * nodePartSize n + nodePartSize n := by ring
  have hcomm : nodeArity * nodePartSize n = nodePartSize n * nodeArity := by ring
  omega

/-- The part size stays below `n₂/h + 1` — this is what makes the children
shrink. -/
lemma nodePartSize_mul_arity_le (n : ℕ) :
    nodePartSize n * nodeArity ≤ n + nodeArity := by
  have hA := nodeArity_pos
  rcases le_or_gt ((n + nodeArity - 1) / nodeArity) 1 with hsmall | hbig
  · have h1 : nodePartSize n = 1 := by
      rw [nodePartSize]
      omega
    rw [h1]
    omega
  · have hps : nodePartSize n = (n + nodeArity - 1) / nodeArity := by
      rw [nodePartSize]
      omega
    have hle : ((n + nodeArity - 1) / nodeArity) * nodeArity ≤ n + nodeArity - 1 :=
      Nat.div_mul_le_self _ _
    rw [hps]
    omega

/-- The child-size bound in the form `LDS/Cost.lean` wants. -/
lemma two_mul_nodePartSize_le {n m : ℕ} (hn : n ≤ m) :
    ((2 * nodePartSize n : ℕ) : ℝ) ≤ 2 * m / nodeArity + 2 := by
  have hA : (0 : ℝ) < (nodeArity : ℝ) := by
    have := nodeArity_pos
    exact_mod_cast this
  have hkey : nodePartSize n * nodeArity ≤ n + nodeArity := nodePartSize_mul_arity_le n
  have hkey' : ((nodePartSize n : ℝ)) * nodeArity ≤ (n : ℝ) + nodeArity := by
    exact_mod_cast hkey
  have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hn
  rw [div_add' _ _ _ (ne_of_gt hA), le_div_iff₀ hA]
  push_cast
  nlinarith

lemma nodePartSize_mono {n n' : ℕ} (h : n ≤ n') : nodePartSize n ≤ nodePartSize n' := by
  simp only [nodePartSize]
  exact max_le_max le_rfl (Nat.div_le_div_right (by omega))

/-- Children are strictly smaller than their parent — the recursion's measure. -/
lemma two_mul_nodePartSize_lt {m : ℕ} (hm : nodeArity < m) : 2 * nodePartSize m < m := by
  have h := nodePartSize_mul_arity_le m
  have h1 := one_le_nodePartSize m
  unfold nodeArity at *
  omega

/-! ## Transporting a node problem across equal sizes -/

/-- Two node problems with the same size, the same glue and the same letters
are the same problem.  The arena size is a type index, so this is the only way
to move between two descriptions of one child. -/
lemma bldsFun_congr {σ : Type*} [DecidableEq σ] {m₁ m₂ : ℕ} (h : m₁ = m₂)
    {g₁ : Fin m₁} {g₂ : Fin m₂} (hg : (g₁ : ℕ) = (g₂ : ℕ))
    {β₁ : Fin m₁ → σ} {β₂ : Fin m₂ → σ}
    (hβ : ∀ (k₁ : Fin m₁) (k₂ : Fin m₂), (k₁ : ℕ) = (k₂ : ℕ) → β₁ k₁ = β₂ k₂) :
    bldsFun g₁ β₁ = bldsFun g₂ β₂ := by
  subst h
  have hgg : g₁ = g₂ := Fin.ext hg
  have hββ : β₁ = β₂ := funext fun k => hβ k k rfl
  rw [hgg, hββ]

/-! ## The base case -/

section Dual

variable {σ : Type} [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X] [DecidableEq X]

/-- **The base case of the recursion**: on a small arena the read-everything
dual is within budget, and the exported descriptor chain is empty. -/
theorem hasDualOn_bldsFun_small {m L : ℕ} (hL : 1 ≤ L) (hm : m ≤ nodeArity)
    (g : Fin m) (read : X → Fin m → σ) :
    ∃ T : X → ℕ, HasDualOn read (fun x => (T x, bldsFun g (read x))) (nodeCost L m) := by
  refine ⟨fun _ => 0, ?_⟩
  have h1 : HasDualOn read (fun x => bldsFun g (read x)) (2 * (m : ℝ)) := by
    have h := (hasDual_two_mul_card (ι := Fin m) (σ := σ)
      (fun β => bldsFun g β)).restrictToOn read
    simpa [Fintype.card_fin] using h
  refine (h1.ofKer ?_).mono ?_
  · intro x y
    exact ⟨fun h => by rw [h], fun h => congrArg Prod.snd h⟩
  · have hbase := nodeCost_base (L := L) (m := m) hL hm
    linarith

/-! ## The per-part anchors, on the level-1 fiber

A node's second descriptor level is the family of part anchors `p_ℓ`.  Their
windows depend on the *first* level (the normalized arena), so they are
adaptive; on a level-1 fiber they are ordinary fixed-window anchors of the
arena word, which is what `hasDualOn_lambdaFun_arena` solves.

The bridge between the two views is `ambP_eq_ambPof`: stated with the arena
ends `a`, `b` as **variables**, the word-computed anchor and the
`(a,b)`-computed one are the same term after `subst`, so no transport across
the size equality is needed anywhere. -/

variable {m : ℕ}

/-- Any anchor of a sub-arena costs at most the ambient arena's bound. -/
private lemma anchor_cost_le' {s : ℕ} (a j : Fin s) (hsm : s ≤ m) {L : ℕ} :
    (L : ℝ) * (8 * ((winLen a j : ℕ) : ℝ) ^ ((2 : ℝ) / 3))
      ≤ (L : ℝ) * (8 * (m : ℝ) ^ ((2 : ℝ) / 3)) := by
  have h1 : ((winLen a j : ℕ) : ℝ) ^ ((2 : ℝ) / 3) ≤ (m : ℝ) ^ ((2 : ℝ) / 3) := by
    refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ (by norm_num)
    exact_mod_cast le_trans (winLen_le a j) hsm
  have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  have h8 : (0 : ℝ) ≤ 8 := by norm_num
  gcongr

/-- The ambient position of a normalized-arena index. -/
def ambOf (β : Fin m → σ) (g : Fin m) : Fin (normSize β g) → Fin m :=
  intervalEmb (normA β g : ℕ) (normB β g : ℕ) (normB β g).isLt

/-- The size of a node's right part. -/
def nodeRight (β : Fin m → σ) (g : Fin m) : ℕ :=
  normSize β g - 1 - (normGlue β g : ℕ)

/-- A node's part size. -/
def nodeT (β : Fin m → σ) (g : Fin m) : ℕ := nodePartSize (nodeRight β g)

/-- The `ℓ`-th part anchor of a node, in ambient coordinates. -/
def ambP (g : Fin m) (β : Fin m → σ) (ℓ : ℕ) : Fin m :=
  ambOf β g (splitP (normWord β g) (normGlue β g) (nodeT β g) ℓ)

/-- The same anchor, computed from the arena ends `a`, `b` given as data. -/
def ambPof (a b g : Fin m) (hag : (a : ℕ) ≤ (g : ℕ)) (hgb : (g : ℕ) ≤ (b : ℕ))
    (β : Fin m → σ) (ℓ : ℕ) : Fin m :=
  intervalEmb (a : ℕ) (b : ℕ) b.isLt
    (splitP (fun k => β (intervalEmb (a : ℕ) (b : ℕ) b.isLt k))
      ⟨(g : ℕ) - (a : ℕ), by omega⟩
      (nodePartSize (((b : ℕ) + 1 - (a : ℕ)) - 1 - ((g : ℕ) - (a : ℕ)))) ℓ)

lemma ambP_eq_ambPof (g : Fin m) (β : Fin m → σ) (ℓ : ℕ) :
    ambP g β ℓ
      = ambPof (normA β g) (normB β g) g (normA_le β g) (le_normB β g) β ℓ := rfl

@[simp] lemma ambOf_val (β : Fin m → σ) (g : Fin m) (k : Fin (normSize β g)) :
    (ambOf β g k : ℕ) = (normA β g : ℕ) + (k : ℕ) := rfl

/-- The cap of part `ℓ`, computed from a given anchor rather than from the
word — on a level-2 fiber the anchor is data, not a search. -/
def capOf {M : ℕ} (G : Fin M) (t ℓ : ℕ) (P : Fin M) : Fin M :=
  ⟨min (G : ℕ) ((P : ℕ) + winLen (splitLo G t ℓ) (splitHi G t ℓ) - 1), by
    have := G.isLt; omega⟩

/-- Its successor, clamped. -/
def capSuccOf {M : ℕ} (G : Fin M) (t ℓ : ℕ) (P : Fin M) : Fin M :=
  ⟨min ((capOf G t ℓ P : ℕ) + 1) (M - 1), by have := G.isLt; omega⟩

/-- The cap's successor never passes the part's right end. -/
lemma capSuccOf_le_splitHi {M : ℕ} (G : Fin M) {t : ℕ} (ht : 1 ≤ t) (ℓ : ℕ)
    (P : Fin M) : (capSuccOf G t ℓ P : ℕ) ≤ (splitHi G t ℓ : ℕ) := by
  have hG := G.isLt
  have hmul : 1 ≤ (ℓ + 1) * t := Nat.one_le_iff_ne_zero.mpr (by positivity)
  simp only [capSuccOf, capOf, splitHi]
  omega

/-- The `ℓ`-th truncation of a node, in ambient coordinates. -/
def ambY (g : Fin m) (β : Fin m → σ) (ℓ : ℕ) : Fin m :=
  ambOf β g (splitY (normWord β g) (normGlue β g) (nodeT β g) ℓ)

/-! ## The node identity in ambient endpoints

`bldsFun_eq_maxFun_split` states a node's children in *normalized* arena
coordinates, which is where the combinatorics lives.  A descriptor fiber,
however, fixes the **ambient** positions of the anchors (`ambP`, `ambY`), and
a child's index type depends on its four boundary numbers — so carrying
normalized coordinates through a fiber would need a transport at every step.

Restating the identity with the four endpoints as *ambient numbers supplied
by the caller* removes that entirely: the normalized-vs-ambient shift is done
here, once, where `normA` is word-computed and no fiber is in sight, and a
child becomes `pairEmb` on the ambient word directly — the composite
`intervalEmb ∘ pairEmb` is itself a `pairEmb`, shifted.  The fiber step then
only has to say that its endpoints are the descriptor's. -/

/-- The `ℓ`-th cap, in ambient coordinates. -/
def ambQ (g : Fin m) (β : Fin m → σ) (ℓ : ℕ) : Fin m :=
  ambOf β g (splitQ (normWord β g) (normGlue β g) (nodeT β g) ℓ)

/-- The `ℓ`-th part start, in ambient coordinates. -/
def ambX (g : Fin m) (β : Fin m → σ) (ℓ : ℕ) : Fin m :=
  ambOf β g (splitLo (normGlue β g) (nodeT β g) ℓ)

@[simp] lemma childEmb_val (a b : Fin m) (p q x y' : ℕ)
    (hq : q < (b : ℕ) + 1 - (a : ℕ)) (hy' : y' < (b : ℕ) + 1 - (a : ℕ))
    (k : Fin ((q + 1 - p) + (y' + 1 - x))) :
    (childEmb a b p q x y' hq hy' k : ℕ)
      = (a : ℕ) + (pairEmb p q x y' hq hy' k : ℕ) := rfl

/-- **The node identity, with the children read off ambient endpoints.**  The
caller supplies the four boundary numbers of each child — on a descriptor
fiber they are constants — together with the fact that they are the node's
own anchors. -/
theorem bldsFun_eq_maxFun_ambient (β : Fin m → σ) (g : Fin m) {hh : ℕ}
    (P Q X Y : Fin hh → ℕ)
    (hP : ∀ ℓ, P ℓ = (ambP g β (ℓ : ℕ) : ℕ))
    (hQ : ∀ ℓ, Q ℓ = (ambQ g β (ℓ : ℕ) : ℕ))
    (hX : ∀ ℓ, X ℓ = (ambX g β (ℓ : ℕ) : ℕ))
    (hY : ∀ ℓ, Y ℓ = (ambY g β (ℓ : ℕ) : ℕ))
    (hPQ : ∀ ℓ, P ℓ ≤ Q ℓ) (hQm : ∀ ℓ, Q ℓ < m) (hYm : ∀ ℓ, Y ℓ < m)
    (hn : 1 ≤ nodeRight β g) (hcov : nodeRight β g ≤ hh * nodeT β g)
    (hlt : ∀ ℓ : Fin hh, (ℓ : ℕ) * nodeT β g < nodeRight β g) :
    bldsFun g β = maxFun fun s : Option (Fin hh) => s.elim (glueRun β g) fun ℓ =>
      (X ℓ - Q ℓ - 1)
        + bldsFun (⟨Q ℓ - P ℓ, by have := hPQ ℓ; omega⟩ :
            Fin ((Q ℓ + 1 - P ℓ) + (Y ℓ + 1 - X ℓ)))
            (β ∘ pairEmb (P ℓ) (Q ℓ) (X ℓ) (Y ℓ) (hQm ℓ) (hYm ℓ)) := by
  have hslot : ∀ ℓ : Fin hh,
      ((splitLo (normGlue β g) (nodeT β g) (ℓ : ℕ) : ℕ)
          - (splitQ (normWord β g) (normGlue β g) (nodeT β g) (ℓ : ℕ) : ℕ) - 1)
        + childVal (splitP (normWord β g) (normGlue β g) (nodeT β g) (ℓ : ℕ) : ℕ)
            (splitQ (normWord β g) (normGlue β g) (nodeT β g) (ℓ : ℕ) : ℕ)
            (splitLo (normGlue β g) (nodeT β g) (ℓ : ℕ) : ℕ)
            (splitY (normWord β g) (normGlue β g) (nodeT β g) (ℓ : ℕ) : ℕ)
            (splitP_le_splitQ (isDistinct_normWord_glue β g) (one_le_nodePartSize _) (hlt ℓ))
            (splitQ (normWord β g) (normGlue β g) (nodeT β g) (ℓ : ℕ)).isLt
            (splitY (normWord β g) (normGlue β g) (nodeT β g) (ℓ : ℕ)).isLt (normWord β g)
      = (X ℓ - Q ℓ - 1)
        + bldsFun (⟨Q ℓ - P ℓ, by have := hPQ ℓ; omega⟩ :
            Fin ((Q ℓ + 1 - P ℓ) + (Y ℓ + 1 - X ℓ)))
            (β ∘ pairEmb (P ℓ) (Q ℓ) (X ℓ) (Y ℓ) (hQm ℓ) (hYm ℓ)) := by
    intro ℓ
    have hpv : (ambP g β (ℓ : ℕ) : ℕ) = (normA β g : ℕ)
        + (splitP (normWord β g) (normGlue β g) (nodeT β g) (ℓ : ℕ) : ℕ) := rfl
    have hqv : (ambQ g β (ℓ : ℕ) : ℕ) = (normA β g : ℕ)
        + (splitQ (normWord β g) (normGlue β g) (nodeT β g) (ℓ : ℕ) : ℕ) := rfl
    have hxv : (ambX g β (ℓ : ℕ) : ℕ) = (normA β g : ℕ)
        + (splitLo (normGlue β g) (nodeT β g) (ℓ : ℕ) : ℕ) := rfl
    have hyv : (ambY g β (ℓ : ℕ) : ℕ) = (normA β g : ℕ)
        + (splitY (normWord β g) (normGlue β g) (nodeT β g) (ℓ : ℕ) : ℕ) := rfl
    have hPl := hP ℓ
    have hQl := hQ ℓ
    have hXl := hX ℓ
    have hYl := hY ℓ
    have hchild : childVal (splitP (normWord β g) (normGlue β g) (nodeT β g) (ℓ : ℕ) : ℕ)
        (splitQ (normWord β g) (normGlue β g) (nodeT β g) (ℓ : ℕ) : ℕ)
        (splitLo (normGlue β g) (nodeT β g) (ℓ : ℕ) : ℕ)
        (splitY (normWord β g) (normGlue β g) (nodeT β g) (ℓ : ℕ) : ℕ)
        (splitP_le_splitQ (isDistinct_normWord_glue β g) (one_le_nodePartSize _) (hlt ℓ))
        (splitQ (normWord β g) (normGlue β g) (nodeT β g) (ℓ : ℕ)).isLt
        (splitY (normWord β g) (normGlue β g) (nodeT β g) (ℓ : ℕ)).isLt (normWord β g)
        = bldsFun (⟨Q ℓ - P ℓ, by have := hPQ ℓ; omega⟩ :
            Fin ((Q ℓ + 1 - P ℓ) + (Y ℓ + 1 - X ℓ)))
            (β ∘ pairEmb (P ℓ) (Q ℓ) (X ℓ) (Y ℓ) (hQm ℓ) (hYm ℓ)) := by
      refine Eq.trans (childVal_eq_bldsFun_childEmb β (normA β g) (normB β g) _ _ _ _ _ _ _) ?_
      refine bldsFun_congr (by omega) ?_ ?_
      · change (splitQ (normWord β g) (normGlue β g) (nodeT β g) (ℓ : ℕ) : ℕ)
            - (splitP (normWord β g) (normGlue β g) (nodeT β g) (ℓ : ℕ) : ℕ) = Q ℓ - P ℓ
        omega
      intro k₁ k₂ hk
      refine congrArg β (Fin.ext ?_)
      refine (childEmb_val _ _ _ _ _ _ _ _ k₁).trans ?_
      have hk1 := pairEmb_val (m := (normB β g : ℕ) + 1 - (normA β g : ℕ))
        (splitQ (normWord β g) (normGlue β g) (nodeT β g) (ℓ : ℕ)).isLt
        (splitY (normWord β g) (normGlue β g) (nodeT β g) (ℓ : ℕ)).isLt k₁
      rw [hk1]
      simp only [pairEmb_val]
      split_ifs <;> omega
    have hoff : (splitLo (normGlue β g) (nodeT β g) (ℓ : ℕ) : ℕ)
        - (splitQ (normWord β g) (normGlue β g) (nodeT β g) (ℓ : ℕ) : ℕ) - 1
        = X ℓ - Q ℓ - 1 := by omega
    rw [hchild, hoff]
  rw [bldsFun_eq_maxFun_split β g (t := nodeT β g) (one_le_nodePartSize _) hn hcov hlt,
    funext hslot]

/-! ## Fiber-constant values -/

lemma nodeRight_eq_of_normDesc {β γ : Fin m → σ} {g : Fin m}
    (h : normDesc β g = normDesc γ g) : nodeRight β g = nodeRight γ g := by
  simp only [nodeRight, normSize_eq_of_normDesc h, normGlue_val, normA_eq_of_normDesc h]

/-- **A node with an empty right part is a descriptor constant**: its value is
the whole normalized arena, maxed with the glue run, and both are read off the
level-1 descriptor.  This is the recursion's other base case, and on a fiber it
costs nothing. -/
lemma bldsFun_eq_of_normDesc_of_empty {β γ : Fin m → σ} {g : Fin m}
    (h : normDesc β g = normDesc γ g) (hβ : nodeRight β g = 0) :
    bldsFun g β = bldsFun g γ := by
  have hγ : nodeRight γ g = 0 := (nodeRight_eq_of_normDesc h) ▸ hβ
  have hlβ : (normGlue β g : ℕ) + 1 = normSize β g := by
    have := (normGlue β g).isLt
    simp only [nodeRight] at hβ
    omega
  have hlγ : (normGlue γ g : ℕ) + 1 = normSize γ g := by
    have := (normGlue γ g).isLt
    simp only [nodeRight] at hγ
    omega
  rw [bldsFun_eq_normalized β g, bldsFun_eq_normalized γ g,
    bldsFun_normWord_of_glue_last β g hlβ, bldsFun_normWord_of_glue_last γ g hlγ,
    glueRun_eq_of_normDesc h, normSize_eq_of_normDesc h]

/-- A child depends on its four boundary numbers only, so equal numbers give
equal children — the bridge between the fiber's data and the word's. -/
lemma childVal_congr (β : Fin m → σ) {p q x y' p' q' x' y2 : ℕ}
    (hp : p = p') (hq : q = q') (hx : x = x') (hy : y' = y2)
    (h1 : p ≤ q) (h2 : q < m) (h3 : y' < m)
    (h1' : p' ≤ q') (h2' : q' < m) (h3' : y2 < m) :
    childVal p q x y' h1 h2 h3 β = childVal p' q' x' y2 h1' h2' h3' β := by
  subst hp
  subst hq
  subst hx
  subst hy
  rfl

/-- **The level-2 descriptor has an anchor's dual on every level-1 fiber.** -/
theorem hasDualOn_ambP (g : Fin m) (read : X → Fin m → σ) {L : ℕ} (hm : m ≤ 2 ^ L)
    (d : Fin m × Fin m × Fin m) (ℓ : ℕ) :
    HasDualOn (fiberRead read (fun x => normDesc (read x) g) d)
      (fun z => ambP g (read z.val) ℓ)
      ((L : ℝ) * (8 * (m : ℝ) ^ ((2 : ℝ) / 3))) := by
  classical
  by_cases hne : Nonempty (Fiber (fun x => normDesc (read x) g) d)
  · obtain ⟨z₀⟩ := hne
    obtain ⟨a, ha₀⟩ : ∃ a, normA (read z₀.val) g = a := ⟨_, rfl⟩
    obtain ⟨b, hb₀⟩ : ∃ b, normB (read z₀.val) g = b := ⟨_, rfl⟩
    have hag : (a : ℕ) ≤ (g : ℕ) := ha₀ ▸ normA_le _ _
    have hgb : (g : ℕ) ≤ (b : ℕ) := hb₀ ▸ le_normB _ _
    -- every input of the fiber has the same arena
    have hfib : ∀ z : Fiber (fun x => normDesc (read x) g) d,
        normA (read z.val) g = a ∧ normB (read z.val) g = b := by
      intro z
      have hz : normDesc (read z.val) g = normDesc (read z₀.val) g :=
        z.2.trans z₀.2.symm
      exact ⟨(normA_eq_of_normDesc hz).trans ha₀, (normB_eq_of_normDesc hz).trans hb₀⟩
    -- on that fixed arena the anchor is an ordinary windowed search
    have hinj : Function.Injective (intervalEmb (a : ℕ) (b : ℕ) b.isLt) :=
      (intervalEmb_strictMono b.isLt).injective
    have hwin : winLen (firstIdx (⟨(g : ℕ) - (a : ℕ), by omega⟩ :
          Fin ((b : ℕ) + 1 - (a : ℕ))))
        (predIdx (splitLo (⟨(g : ℕ) - (a : ℕ), by omega⟩ :
          Fin ((b : ℕ) + 1 - (a : ℕ)))
          (nodePartSize (((b : ℕ) + 1 - (a : ℕ)) - 1 - ((g : ℕ) - (a : ℕ)))) ℓ)) ≤ m := by
      refine le_trans (winLen_le _ _) ?_
      have := b.isLt
      omega
    have hbase := hasDualOn_lambdaFun_arena (m := m) (s := (b : ℕ) + 1 - (a : ℕ))
      (e := intervalEmb (a : ℕ) (b : ℕ) b.isLt) hinj
      (fiberRead read (fun x => normDesc (read x) g) d)
      (a := firstIdx (⟨(g : ℕ) - (a : ℕ), by omega⟩ : Fin ((b : ℕ) + 1 - (a : ℕ))))
      (j := predIdx (splitLo (⟨(g : ℕ) - (a : ℕ), by omega⟩ :
        Fin ((b : ℕ) + 1 - (a : ℕ)))
        (nodePartSize (((b : ℕ) + 1 - (a : ℕ)) - 1 - ((g : ℕ) - (a : ℕ)))) ℓ))
      (firstIdx_le' _ _) (le_trans hwin hm)
    -- wrap the answer back into ambient coordinates, and match the descriptor
    refine ((hbase.ofKer (f' := fun z => ambPof a b g hag hgb (read z.val) ℓ)
      fun z w => ?_).ofEq fun z => ?_).mono ?_
    · exact ⟨fun h => congrArg _ h, fun h => hinj h⟩
    · obtain ⟨hA, hB⟩ := hfib z
      subst hA
      subst hB
      rfl
    · exact anchor_cost_le' _ _ (by have := b.isLt; omega)
  · refine (hasDualOn_of_const (fiberRead read (fun x => normDesc (read x) g) d)
      (f := fun z => ambP g (read z.val) ℓ) fun z w => absurd ⟨z⟩ hne).mono ?_
    positivity


/-- The `ℓ`-th truncation, computed from the arena ends and the level-2 anchor
given as *data* — which is what a level-2 fiber supplies. -/
def ambYof (a b g : Fin m) (hag : (a : ℕ) ≤ (g : ℕ)) (hgb : (g : ℕ) ≤ (b : ℕ))
    (P : Fin ((b : ℕ) + 1 - (a : ℕ))) (β : Fin m → σ) (ℓ : ℕ) : Fin m :=
  intervalEmb (a : ℕ) (b : ℕ) b.isLt
    (rhoFun (fun k => β (intervalEmb (a : ℕ) (b : ℕ) b.isLt k))
      (capSuccOf ⟨(g : ℕ) - (a : ℕ), by omega⟩
        (nodePartSize (((b : ℕ) + 1 - (a : ℕ)) - 1 - ((g : ℕ) - (a : ℕ)))) ℓ P)
      (splitHi ⟨(g : ℕ) - (a : ℕ), by omega⟩
        (nodePartSize (((b : ℕ) + 1 - (a : ℕ)) - 1 - ((g : ℕ) - (a : ℕ)))) ℓ))

lemma ambY_eq_ambYof (g : Fin m) (β : Fin m → σ) (ℓ : ℕ) :
    ambY g β ℓ = ambYof (normA β g) (normB β g) g (normA_le β g) (le_normB β g)
      (splitP (normWord β g) (normGlue β g) (nodeT β g) ℓ) β ℓ := rfl

/-- **The level-3 descriptor has an anchor's dual on every level-(1,2)
fiber.**  Unlike the level-2 anchors, the ρ-window's left end is not
recomputable from the arena alone — it is the cap built from the level-2
anchor, which the fiber supplies as data. -/
theorem hasDualOn_ambY (g : Fin m) (read : X → Fin m → σ) {L : ℕ} (hm : m ≤ 2 ^ L)
    (d : (Fin m × Fin m × Fin m) × (Fin nodeArity → Fin m)) (ℓ : Fin nodeArity) :
    HasDualOn (fiberRead read
        (fun x => (normDesc (read x) g, fun i : Fin nodeArity => ambP g (read x) i)) d)
      (fun z => ambY g (read z.val) (ℓ : ℕ))
      ((L : ℝ) * (8 * (m : ℝ) ^ ((2 : ℝ) / 3))) := by
  classical
  by_cases hne : Nonempty (Fiber (fun x => (normDesc (read x) g,
      fun i : Fin nodeArity => ambP g (read x) i)) d)
  · obtain ⟨z₀⟩ := hne
    obtain ⟨a, ha₀⟩ : ∃ a, normA (read z₀.val) g = a := ⟨_, rfl⟩
    obtain ⟨b, hb₀⟩ : ∃ b, normB (read z₀.val) g = b := ⟨_, rfl⟩
    have hag : (a : ℕ) ≤ (g : ℕ) := ha₀ ▸ normA_le _ _
    have hgb : (g : ℕ) ≤ (b : ℕ) := hb₀ ▸ le_normB _ _
    have hbm := b.isLt
    have hGlt : ((g : ℕ) - (a : ℕ)) < (b : ℕ) + 1 - (a : ℕ) := by omega
    -- the fiber fixes the arena and the level-2 anchor
    have hfib : ∀ z : Fiber (fun x => (normDesc (read x) g,
        fun i : Fin nodeArity => ambP g (read x) i)) d,
        normA (read z.val) g = a ∧ normB (read z.val) g = b
          ∧ ambP g (read z.val) (ℓ : ℕ) = d.2 ℓ := by
      intro z
      have hz : normDesc (read z.val) g = normDesc (read z₀.val) g :=
        congrArg Prod.fst (z.2.trans z₀.2.symm)
      exact ⟨(normA_eq_of_normDesc hz).trans ha₀, (normB_eq_of_normDesc hz).trans hb₀,
        congrFun (congrArg Prod.snd z.2) ℓ⟩
    -- the level-2 anchor, read in normalized coordinates
    have hnorm₀ : normSize (read z₀.val) g = (b : ℕ) + 1 - (a : ℕ) := by
      simp only [normSize, ha₀, hb₀]
    have hd2₀ : (d.2 ℓ : ℕ) = (a : ℕ)
        + (splitP (normWord (read z₀.val) g) (normGlue (read z₀.val) g)
            (nodeT (read z₀.val) g) (ℓ : ℕ) : ℕ) := by
      have h := (hfib z₀).2.2
      rw [← h]
      simp only [ambP, ambOf_val, ha₀]
    have hPlt : ((d.2 ℓ : ℕ) - (a : ℕ)) < (b : ℕ) + 1 - (a : ℕ) := by
      have hlt := (splitP (normWord (read z₀.val) g) (normGlue (read z₀.val) g)
        (nodeT (read z₀.val) g) (ℓ : ℕ)).isLt
      omega
    have hinj : Function.Injective (intervalEmb (a : ℕ) (b : ℕ) b.isLt) :=
      (intervalEmb_strictMono b.isLt).injective
    have hle : (capSuccOf (⟨(g : ℕ) - (a : ℕ), hGlt⟩ : Fin ((b : ℕ) + 1 - (a : ℕ)))
          (nodePartSize (((b : ℕ) + 1 - (a : ℕ)) - 1 - ((g : ℕ) - (a : ℕ)))) (ℓ : ℕ)
          (⟨(d.2 ℓ : ℕ) - (a : ℕ), hPlt⟩ : Fin ((b : ℕ) + 1 - (a : ℕ))))
        ≤ splitHi (⟨(g : ℕ) - (a : ℕ), hGlt⟩ : Fin ((b : ℕ) + 1 - (a : ℕ)))
          (nodePartSize (((b : ℕ) + 1 - (a : ℕ)) - 1 - ((g : ℕ) - (a : ℕ)))) (ℓ : ℕ) := by
      rw [Fin.le_def]
      exact capSuccOf_le_splitHi _ (one_le_nodePartSize _) _ _
    have hwin : winLen (capSuccOf (⟨(g : ℕ) - (a : ℕ), hGlt⟩ : Fin ((b : ℕ) + 1 - (a : ℕ)))
          (nodePartSize (((b : ℕ) + 1 - (a : ℕ)) - 1 - ((g : ℕ) - (a : ℕ)))) (ℓ : ℕ)
          (⟨(d.2 ℓ : ℕ) - (a : ℕ), hPlt⟩ : Fin ((b : ℕ) + 1 - (a : ℕ))))
        (splitHi (⟨(g : ℕ) - (a : ℕ), hGlt⟩ : Fin ((b : ℕ) + 1 - (a : ℕ)))
          (nodePartSize (((b : ℕ) + 1 - (a : ℕ)) - 1 - ((g : ℕ) - (a : ℕ)))) (ℓ : ℕ)) ≤ m :=
      le_trans (winLen_le _ _) (by omega)
    have hbase := hasDualOn_rhoFun_arena (m := m) (s := (b : ℕ) + 1 - (a : ℕ))
      (e := (intervalEmb (a : ℕ) (b : ℕ) b.isLt)) hinj
      (fiberRead read (fun x => (normDesc (read x) g,
        fun i : Fin nodeArity => ambP g (read x) i)) d)
      (l := capSuccOf (⟨(g : ℕ) - (a : ℕ), hGlt⟩ : Fin ((b : ℕ) + 1 - (a : ℕ)))
        (nodePartSize (((b : ℕ) + 1 - (a : ℕ)) - 1 - ((g : ℕ) - (a : ℕ)))) (ℓ : ℕ)
        (⟨(d.2 ℓ : ℕ) - (a : ℕ), hPlt⟩ : Fin ((b : ℕ) + 1 - (a : ℕ))))
      (b := splitHi (⟨(g : ℕ) - (a : ℕ), hGlt⟩ : Fin ((b : ℕ) + 1 - (a : ℕ)))
        (nodePartSize (((b : ℕ) + 1 - (a : ℕ)) - 1 - ((g : ℕ) - (a : ℕ)))) (ℓ : ℕ)) hle
      (le_trans hwin hm)
    refine ((hbase.ofKer (f' := fun z => ambYof a b g hag hgb
        (⟨(d.2 ℓ : ℕ) - (a : ℕ), hPlt⟩ : Fin ((b : ℕ) + 1 - (a : ℕ))) (read z.val) (ℓ : ℕ))
      fun z w => ?_).ofEq fun z => ?_).mono ?_
    · exact ⟨fun h => congrArg _ h, fun h => hinj h⟩
    · obtain ⟨hA, hB, hP⟩ := hfib z
      subst hA
      subst hB
      have hval : (d.2 ℓ : ℕ) = (normA (read z.val) g : ℕ)
          + (splitP (normWord (read z.val) g) (normGlue (read z.val) g)
              (nodeT (read z.val) g) (ℓ : ℕ) : ℕ) := by
        rw [← hP]
        simp only [ambP, ambOf_val]
      have hPeq : (⟨(d.2 ℓ : ℕ) - (normA (read z.val) g : ℕ), hPlt⟩ :
            Fin ((normB (read z.val) g : ℕ) + 1 - (normA (read z.val) g : ℕ)))
          = splitP (normWord (read z.val) g) (normGlue (read z.val) g)
              (nodeT (read z.val) g) (ℓ : ℕ) := by
        apply Fin.ext
        simp only []
        omega
      rw [ambY_eq_ambYof]
      exact congrArg (fun P => ambYof (normA (read z.val) g) (normB (read z.val) g) g
        (normA_le _ _) (le_normB _ _) P (read z.val) (ℓ : ℕ)) hPeq
    · exact anchor_cost_le' _ _ (by omega)
  · refine (hasDualOn_of_const (fiberRead read (fun x => (normDesc (read x) g,
      fun i : Fin nodeArity => ambP g (read x) i)) d)
      (f := fun z => ambY g (read z.val) (ℓ : ℕ)) fun z w => absurd ⟨z⟩ hne).mono ?_
    positivity

/-! ## What a descriptor determines

The level-1 descriptor fixes the arena, hence the part boundaries; together
with the level-2 anchors it fixes the caps too.  All of this is stated at the
`ℕ` level — the normalized quantities live in `Fin (normSize …)`, a type that
changes with the word, while their ambient positions do not. -/

lemma nodeT_eq_of_normDesc {β γ : Fin m → σ} {g : Fin m}
    (h : normDesc β g = normDesc γ g) : nodeT β g = nodeT γ g := by
  simp only [nodeT, nodeRight_eq_of_normDesc h]

lemma normGlue_val_eq_of_normDesc {β γ : Fin m → σ} {g : Fin m}
    (h : normDesc β g = normDesc γ g) : (normGlue β g : ℕ) = (normGlue γ g : ℕ) := by
  simp only [normGlue_val, normA_eq_of_normDesc h]

lemma splitLo_val_eq_of_normDesc {β γ : Fin m → σ} {g : Fin m}
    (h : normDesc β g = normDesc γ g) (ℓ : ℕ) :
    (splitLo (normGlue β g) (nodeT β g) ℓ : ℕ)
      = (splitLo (normGlue γ g) (nodeT γ g) ℓ : ℕ) := by
  rw [splitLo_val_min, splitLo_val_min, normGlue_val_eq_of_normDesc h,
    nodeT_eq_of_normDesc h, normSize_eq_of_normDesc h]

lemma splitHi_val_eq_of_normDesc {β γ : Fin m → σ} {g : Fin m}
    (h : normDesc β g = normDesc γ g) (ℓ : ℕ) :
    (splitHi (normGlue β g) (nodeT β g) ℓ : ℕ)
      = (splitHi (normGlue γ g) (nodeT γ g) ℓ : ℕ) := by
  rw [splitHi_val, splitHi_val, normGlue_val_eq_of_normDesc h,
    nodeT_eq_of_normDesc h, normSize_eq_of_normDesc h]

lemma ambX_val_eq_of_normDesc {β γ : Fin m → σ} {g : Fin m}
    (h : normDesc β g = normDesc γ g) (ℓ : ℕ) :
    (ambX g β ℓ : ℕ) = (ambX g γ ℓ : ℕ) := by
  change (normA β g : ℕ) + (splitLo (normGlue β g) (nodeT β g) ℓ : ℕ)
    = (normA γ g : ℕ) + (splitLo (normGlue γ g) (nodeT γ g) ℓ : ℕ)
  rw [normA_eq_of_normDesc h, splitLo_val_eq_of_normDesc h]

/-- The level-2 anchor pins the normalized anchor, the arena being fixed. -/
lemma splitP_val_eq_of_ambP {β γ : Fin m → σ} {g : Fin m}
    (h : normDesc β g = normDesc γ g) {ℓ : ℕ}
    (hP : (ambP g β ℓ : ℕ) = (ambP g γ ℓ : ℕ)) :
    (splitP (normWord β g) (normGlue β g) (nodeT β g) ℓ : ℕ)
      = (splitP (normWord γ g) (normGlue γ g) (nodeT γ g) ℓ : ℕ) := by
  have h1 : (ambP g β ℓ : ℕ) = (normA β g : ℕ)
      + (splitP (normWord β g) (normGlue β g) (nodeT β g) ℓ : ℕ) := rfl
  have h2 : (ambP g γ ℓ : ℕ) = (normA γ g : ℕ)
      + (splitP (normWord γ g) (normGlue γ g) (nodeT γ g) ℓ : ℕ) := rfl
  have h3 := normA_eq_of_normDesc h
  omega

/-- Hence the cap is fixed as well: it is a function of the arena and the
level-2 anchor, so it costs the recursion nothing to know it. -/
lemma ambQ_val_eq_of_ambP {β γ : Fin m → σ} {g : Fin m}
    (h : normDesc β g = normDesc γ g) {ℓ : ℕ}
    (hP : (ambP g β ℓ : ℕ) = (ambP g γ ℓ : ℕ)) :
    (ambQ g β ℓ : ℕ) = (ambQ g γ ℓ : ℕ) := by
  have hlo := splitLo_val_eq_of_normDesc h ℓ
  have hhi := splitHi_val_eq_of_normDesc h ℓ
  have hp := splitP_val_eq_of_ambP h hP
  have hg := normGlue_val_eq_of_normDesc h
  have hA := normA_eq_of_normDesc h
  change (normA β g : ℕ) + (splitQ (normWord β g) (normGlue β g) (nodeT β g) ℓ : ℕ)
    = (normA γ g : ℕ) + (splitQ (normWord γ g) (normGlue γ g) (nodeT γ g) ℓ : ℕ)
  rw [splitQ_val_min, splitQ_val_min, hA]
  simp only [winLen]
  omega

/-! ## The value step

On a full descriptor fiber every quantity a node computes is a constant except
its children, so the node's value is a maximum of `hh + 1` slots — the glue run
and the shifted children — and `HasDualOn.maxMapConst` applies with the
children supplied by the induction hypothesis.

The descriptor itself is abstract here: all that matters is that it determines
the arena and the two anchor families (`hDet`).  That keeps the statement free
of the concrete descriptor type, whose `Fintype` instance would otherwise block
every rewrite. -/

theorem hasDualOn_value {Δ : Type} [Fintype Δ] [DecidableEq Δ] (g : Fin m)
    (read : X → Fin m → σ) {L : ℕ} (hL : 1 ≤ L) (hbig : nodeArity < m)
    (ih : ∀ m' : ℕ, m' < m → ∀ (g' : Fin m') {Y : Type} [Fintype Y] [DecidableEq Y]
      (rd : Y → Fin m' → σ), ∃ T : Y → ℕ,
        HasDualOn rd (fun y => (T y, bldsFun g' (rd y))) (nodeCost L m'))
    (D : X → Δ) (d : Δ)
    (hDet : ∀ x y : X, D x = D y →
      normDesc (read x) g = normDesc (read y) g
      ∧ (∀ i, i < nodeArity → (ambP g (read x) i : ℕ) = (ambP g (read y) i : ℕ))
      ∧ (∀ i, i < nodeArity → (ambY g (read x) i : ℕ) = (ambY g (read y) i : ℕ))) :
    HasDualOn (fiberRead read D d) (fun z => bldsFun g (read z.val))
      (16 * (nodeCost L (2 * nodePartSize m) * Real.sqrt ((nodeArity : ℝ) + 1))) := by
  classical
  have hc0pos : 0 < nodeCost L (2 * nodePartSize m) := by
    have h3 : 0 < 2 * nodePartSize m := by have := one_le_nodePartSize m; omega
    have h4 : (0 : ℝ) < ((2 * nodePartSize m : ℕ) : ℝ) := by exact_mod_cast h3
    have h5 : (0 : ℝ) < ((2 * nodePartSize m : ℕ) : ℝ) ^ ((2 : ℝ) / 3) :=
      Real.rpow_pos_of_pos h4 _
    have h2 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    have h1 : (0 : ℝ) < nodeConst := nodeConst_pos
    have hLpos : (0 : ℝ) < (L : ℝ) := by linarith
    unfold nodeCost
    exact mul_pos (mul_pos h1 hLpos) h5
  have hsq : (0 : ℝ) ≤ Real.sqrt ((nodeArity : ℝ) + 1) := Real.sqrt_nonneg _
  have hcost0 : (0 : ℝ)
      ≤ 16 * (nodeCost L (2 * nodePartSize m) * Real.sqrt ((nodeArity : ℝ) + 1)) := by
    have := mul_nonneg hc0pos.le hsq
    linarith
  by_cases hne : Nonempty (Fiber D d)
  · obtain ⟨z₀⟩ := hne
    have hfib : ∀ z : Fiber D d,
        normDesc (read z.val) g = normDesc (read z₀.val) g
        ∧ (∀ i, i < nodeArity → (ambP g (read z.val) i : ℕ) = (ambP g (read z₀.val) i : ℕ))
        ∧ (∀ i, i < nodeArity → (ambY g (read z.val) i : ℕ) = (ambY g (read z₀.val) i : ℕ)) :=
      fun z => hDet z.val z₀.val (z.2.trans z₀.2.symm)
    by_cases hempty : nodeRight (read z₀.val) g = 0
    · refine (hasDualOn_of_const (fiberRead read D d)
        (f := fun z => bldsFun g (read z.val)) ?_).mono hcost0
      intro z w
      have hz := (hfib z).1
      have hw := (hfib w).1
      refine bldsFun_eq_of_normDesc_of_empty (hz.trans hw.symm) ?_
      rw [nodeRight_eq_of_normDesc hz]
      exact hempty
    · -- the split
      have hne0 : 1 ≤ nodeRight (read z₀.val) g := Nat.one_le_iff_ne_zero.mpr hempty
      obtain ⟨hh, hhdef⟩ : ∃ hh, nodeParts (nodeRight (read z₀.val) g) = hh := ⟨_, rfl⟩
      have hhA : hh ≤ nodeArity := hhdef ▸ nodeParts_le_arity _
      have hcast : ∀ ℓ : Fin hh, (ℓ : ℕ) < nodeArity := fun ℓ => lt_of_lt_of_le ℓ.isLt hhA
      have hPz : ∀ (z : Fiber D d) (ℓ : Fin hh),
          (ambP g (read z₀.val) (ℓ : ℕ) : ℕ) = (ambP g (read z.val) (ℓ : ℕ) : ℕ) :=
        fun z ℓ => ((hfib z).2.1 (ℓ : ℕ) (hcast ℓ)).symm
      have hYz : ∀ (z : Fiber D d) (ℓ : Fin hh),
          (ambY g (read z₀.val) (ℓ : ℕ) : ℕ) = (ambY g (read z.val) (ℓ : ℕ) : ℕ) :=
        fun z ℓ => ((hfib z).2.2 (ℓ : ℕ) (hcast ℓ)).symm
      have hQz : ∀ (z : Fiber D d) (ℓ : Fin hh),
          (ambQ g (read z₀.val) (ℓ : ℕ) : ℕ) = (ambQ g (read z.val) (ℓ : ℕ) : ℕ) :=
        fun z ℓ => ambQ_val_eq_of_ambP (hfib z).1.symm (hPz z ℓ)
      have hXz : ∀ (z : Fiber D d) (ℓ : Fin hh),
          (ambX g (read z₀.val) (ℓ : ℕ) : ℕ) = (ambX g (read z.val) (ℓ : ℕ) : ℕ) :=
        fun z ℓ => ambX_val_eq_of_normDesc (hfib z).1.symm _
      have hltz₀ : ∀ ℓ : Fin hh,
          (ℓ : ℕ) * nodeT (read z₀.val) g < nodeRight (read z₀.val) g :=
        fun ℓ => nodeParts_lt _ (hhdef ▸ ℓ.isLt)
      have hPQ : ∀ ℓ : Fin hh,
          (ambP g (read z₀.val) (ℓ : ℕ) : ℕ) ≤ (ambQ g (read z₀.val) (ℓ : ℕ) : ℕ) := by
        intro ℓ
        have h := splitP_le_splitQ (W := normWord (read z₀.val) g)
          (G := normGlue (read z₀.val) g) (t := nodeT (read z₀.val) g)
          (isDistinct_normWord_glue (read z₀.val) g) (one_le_nodePartSize _) (hltz₀ ℓ)
        have e1 : (ambP g (read z₀.val) (ℓ : ℕ) : ℕ) = (normA (read z₀.val) g : ℕ)
            + (splitP (normWord (read z₀.val) g) (normGlue (read z₀.val) g)
                (nodeT (read z₀.val) g) (ℓ : ℕ) : ℕ) := rfl
        have e2 : (ambQ g (read z₀.val) (ℓ : ℕ) : ℕ) = (normA (read z₀.val) g : ℕ)
            + (splitQ (normWord (read z₀.val) g) (normGlue (read z₀.val) g)
                (nodeT (read z₀.val) g) (ℓ : ℕ) : ℕ) := rfl
        omega
      have hQX : ∀ ℓ : Fin hh,
          (ambQ g (read z₀.val) (ℓ : ℕ) : ℕ) < (ambX g (read z₀.val) (ℓ : ℕ) : ℕ) := by
        intro ℓ
        have h1 := splitQ_le_glue (normWord (read z₀.val) g) (normGlue (read z₀.val) g)
          (nodeT (read z₀.val) g) (ℓ : ℕ)
        have h2 := lt_splitLo (G := normGlue (read z₀.val) g)
          (t := nodeT (read z₀.val) g) (hltz₀ ℓ)
        have e1 : (ambQ g (read z₀.val) (ℓ : ℕ) : ℕ) = (normA (read z₀.val) g : ℕ)
            + (splitQ (normWord (read z₀.val) g) (normGlue (read z₀.val) g)
                (nodeT (read z₀.val) g) (ℓ : ℕ) : ℕ) := rfl
        have e2 : (ambX g (read z₀.val) (ℓ : ℕ) : ℕ) = (normA (read z₀.val) g : ℕ)
            + (splitLo (normGlue (read z₀.val) g) (nodeT (read z₀.val) g) (ℓ : ℕ) : ℕ) := rfl
        omega
      have hsz : ∀ ℓ : Fin hh,
          ((ambQ g (read z₀.val) (ℓ : ℕ) : ℕ) + 1 - (ambP g (read z₀.val) (ℓ : ℕ) : ℕ))
            + ((ambY g (read z₀.val) (ℓ : ℕ) : ℕ) + 1 - (ambX g (read z₀.val) (ℓ : ℕ) : ℕ))
          ≤ 2 * nodePartSize m := by
        intro ℓ
        have h := splitSize_le (W := normWord (read z₀.val) g)
          (G := normGlue (read z₀.val) g) (t := nodeT (read z₀.val) g)
          (one_le_nodePartSize _) (hltz₀ ℓ)
        have e1 : (ambP g (read z₀.val) (ℓ : ℕ) : ℕ) = (normA (read z₀.val) g : ℕ)
            + (splitP (normWord (read z₀.val) g) (normGlue (read z₀.val) g)
                (nodeT (read z₀.val) g) (ℓ : ℕ) : ℕ) := rfl
        have e2 : (ambQ g (read z₀.val) (ℓ : ℕ) : ℕ) = (normA (read z₀.val) g : ℕ)
            + (splitQ (normWord (read z₀.val) g) (normGlue (read z₀.val) g)
                (nodeT (read z₀.val) g) (ℓ : ℕ) : ℕ) := rfl
        have e3 : (ambX g (read z₀.val) (ℓ : ℕ) : ℕ) = (normA (read z₀.val) g : ℕ)
            + (splitLo (normGlue (read z₀.val) g) (nodeT (read z₀.val) g) (ℓ : ℕ) : ℕ) := rfl
        have e4 : (ambY g (read z₀.val) (ℓ : ℕ) : ℕ) = (normA (read z₀.val) g : ℕ)
            + (splitY (normWord (read z₀.val) g) (normGlue (read z₀.val) g)
                (nodeT (read z₀.val) g) (ℓ : ℕ) : ℕ) := rfl
        have hmono : nodeT (read z₀.val) g ≤ nodePartSize m := by
          refine nodePartSize_mono ?_
          have hb := normSize_le (read z₀.val) g
          simp only [nodeRight]
          omega
        omega
      -- the value identity, with the endpoints read off the representative
      have hid : ∀ z : Fiber D d, bldsFun g (read z.val)
          = maxFun fun s : Option (Fin hh) => s.elim (glueRun (read z.val) g) fun ℓ =>
              ((ambX g (read z₀.val) (ℓ : ℕ) : ℕ) - (ambQ g (read z₀.val) (ℓ : ℕ) : ℕ) - 1)
                + bldsFun (⟨(ambQ g (read z₀.val) (ℓ : ℕ) : ℕ)
                      - (ambP g (read z₀.val) (ℓ : ℕ) : ℕ), by have := hPQ ℓ; omega⟩ :
                    Fin (((ambQ g (read z₀.val) (ℓ : ℕ) : ℕ) + 1
                        - (ambP g (read z₀.val) (ℓ : ℕ) : ℕ))
                      + ((ambY g (read z₀.val) (ℓ : ℕ) : ℕ) + 1
                        - (ambX g (read z₀.val) (ℓ : ℕ) : ℕ))))
                    (read z.val ∘ pairEmb (ambP g (read z₀.val) (ℓ : ℕ) : ℕ)
                      (ambQ g (read z₀.val) (ℓ : ℕ) : ℕ)
                      (ambX g (read z₀.val) (ℓ : ℕ) : ℕ)
                      (ambY g (read z₀.val) (ℓ : ℕ) : ℕ)
                      (ambQ g (read z₀.val) (ℓ : ℕ)).isLt
                      (ambY g (read z₀.val) (ℓ : ℕ)).isLt) := by
        intro z
        refine bldsFun_eq_maxFun_ambient (read z.val) g _ _ _ _ (hPz z) (hQz z) (hXz z)
          (hYz z) hPQ (fun ℓ => (ambQ g (read z₀.val) (ℓ : ℕ)).isLt)
          (fun ℓ => (ambY g (read z₀.val) (ℓ : ℕ)).isLt) ?_ ?_ ?_
        · rw [nodeRight_eq_of_normDesc (hfib z).1]
          exact hne0
        · rw [nodeRight_eq_of_normDesc (hfib z).1, nodeT_eq_of_normDesc (hfib z).1, ← hhdef]
          exact nodeRight_le _
        · intro ℓ
          rw [nodeRight_eq_of_normDesc (hfib z).1, nodeT_eq_of_normDesc (hfib z).1]
          exact hltz₀ ℓ
      -- the children, from the induction hypothesis
      have hchild : ∀ ℓ : Fin hh, ∃ T : Fiber D d → ℕ,
          HasDualOn (fiberRead read D d)
            (fun z => (T z, bldsFun (⟨(ambQ g (read z₀.val) (ℓ : ℕ) : ℕ)
                  - (ambP g (read z₀.val) (ℓ : ℕ) : ℕ), by have := hPQ ℓ; omega⟩ :
                Fin (((ambQ g (read z₀.val) (ℓ : ℕ) : ℕ) + 1
                    - (ambP g (read z₀.val) (ℓ : ℕ) : ℕ))
                  + ((ambY g (read z₀.val) (ℓ : ℕ) : ℕ) + 1
                    - (ambX g (read z₀.val) (ℓ : ℕ) : ℕ))))
                (read z.val ∘ pairEmb (ambP g (read z₀.val) (ℓ : ℕ) : ℕ)
                  (ambQ g (read z₀.val) (ℓ : ℕ) : ℕ) (ambX g (read z₀.val) (ℓ : ℕ) : ℕ)
                  (ambY g (read z₀.val) (ℓ : ℕ) : ℕ)
                  (ambQ g (read z₀.val) (ℓ : ℕ)).isLt (ambY g (read z₀.val) (ℓ : ℕ)).isLt)))
            (nodeCost L (2 * nodePartSize m)) := by
        intro ℓ
        obtain ⟨T, hT⟩ := ih _ (lt_of_le_of_lt (hsz ℓ) (two_mul_nodePartSize_lt hbig))
          (⟨(ambQ g (read z₀.val) (ℓ : ℕ) : ℕ) - (ambP g (read z₀.val) (ℓ : ℕ) : ℕ), by
            have := hPQ ℓ; omega⟩ :
            Fin (((ambQ g (read z₀.val) (ℓ : ℕ) : ℕ) + 1
                - (ambP g (read z₀.val) (ℓ : ℕ) : ℕ))
              + ((ambY g (read z₀.val) (ℓ : ℕ) : ℕ) + 1
                - (ambX g (read z₀.val) (ℓ : ℕ) : ℕ))))
          (fun (z : Fiber D d) k => read z.val
            (pairEmb (ambP g (read z₀.val) (ℓ : ℕ) : ℕ) (ambQ g (read z₀.val) (ℓ : ℕ) : ℕ)
              (ambX g (read z₀.val) (ℓ : ℕ) : ℕ) (ambY g (read z₀.val) (ℓ : ℕ) : ℕ)
              (ambQ g (read z₀.val) (ℓ : ℕ)).isLt (ambY g (read z₀.val) (ℓ : ℕ)).isLt k))
        exact ⟨T, HasDualOn.pullbackCoord
          (pairEmb_strictMono (hPQ ℓ) (hQX ℓ) (ambQ g (read z₀.val) (ℓ : ℕ)).isLt
            (ambY g (read z₀.val) (ℓ : ℕ)).isLt).injective
          (hT.mono (nodeCost_mono L (hsz ℓ)))⟩
      choose Tc hTc using hchild
      -- the node is the maximum of its glue run and its shifted children
      have hslot : ∀ s : Option (Fin hh), HasDualOn (fiberRead read D d)
          (s.elim (fun z : Fiber D d => ((0 : ℕ), glueRun (read z.val) g))
            fun ℓ z => (Tc ℓ z, bldsFun (⟨(ambQ g (read z₀.val) (ℓ : ℕ) : ℕ)
                  - (ambP g (read z₀.val) (ℓ : ℕ) : ℕ), by have := hPQ ℓ; omega⟩ :
                Fin (((ambQ g (read z₀.val) (ℓ : ℕ) : ℕ) + 1
                    - (ambP g (read z₀.val) (ℓ : ℕ) : ℕ))
                  + ((ambY g (read z₀.val) (ℓ : ℕ) : ℕ) + 1
                    - (ambX g (read z₀.val) (ℓ : ℕ) : ℕ))))
                (read z.val ∘ pairEmb (ambP g (read z₀.val) (ℓ : ℕ) : ℕ)
                  (ambQ g (read z₀.val) (ℓ : ℕ) : ℕ) (ambX g (read z₀.val) (ℓ : ℕ) : ℕ)
                  (ambY g (read z₀.val) (ℓ : ℕ) : ℕ)
                  (ambQ g (read z₀.val) (ℓ : ℕ)).isLt (ambY g (read z₀.val) (ℓ : ℕ)).isLt)))
          (nodeCost L (2 * nodePartSize m)) := by
        intro s
        cases s with
        | none =>
          refine (hasDualOn_of_const (fiberRead read D d)
            (f := fun z : Fiber D d => ((0 : ℕ), glueRun (read z.val) g)) ?_).mono hc0pos.le
          intro z w
          have hz := (hfib z).1
          have hw := (hfib w).1
          rw [Prod.mk.injEq]
          exact ⟨rfl, glueRun_eq_of_normDesc (hz.trans hw.symm)⟩
        | some ℓ => exact hTc ℓ
      have hscan := HasDualOn.maxMapConst (P := Option (Fin hh)) (V := ℕ × ℕ) (A := ℕ)
        (read := fiberRead read D d) hc0pos
        (m := fun s => s.elim (fun v : ℕ × ℕ => v.2)
          fun ℓ v => ((ambX g (read z₀.val) (ℓ : ℕ) : ℕ)
            - (ambQ g (read z₀.val) (ℓ : ℕ) : ℕ) - 1) + v.2) hslot
      refine (hscan.ofEq fun z => ?_).mono ?_
      · refine Eq.trans (congrArg maxFun (funext fun p => ?_)) (hid z).symm
        cases p with
        | none => rfl
        | some ℓ => rfl
      have hcard : (Fintype.card (Option (Fin hh)) : ℝ) = (hh : ℝ) + 1 := by
        simp [Fintype.card_option]
      have hsqle : Real.sqrt ((Fintype.card (Option (Fin hh)) : ℝ))
          ≤ Real.sqrt ((nodeArity : ℝ) + 1) := by
        rw [hcard]
        refine Real.sqrt_le_sqrt ?_
        have : (hh : ℝ) ≤ (nodeArity : ℝ) := by exact_mod_cast hhA
        linarith
      have := mul_le_mul_of_nonneg_left hsqle hc0pos.le
      nlinarith
  · exact (hasDualOn_of_const (fiberRead read D d)
      (f := fun z => bldsFun g (read z.val)) fun z w => absurd ⟨z⟩ hne).mono hcost0

/-! ## The recursion

Three nested descriptor compositions — the normalization anchors, then the
part anchors, then the truncations — and the value on the resulting fiber.
The descriptor chain is exported as a single natural number
(`exists_natEncode`), which is what keeps the type of a node's output
independent of its arena size, as the parent's scan requires. -/

theorem hasDualOn_bldsFun (L : ℕ) (hL : 1 ≤ L) :
    ∀ m : ℕ, m ≤ 2 ^ L → ∀ (g : Fin m) {X : Type} [Fintype X] [DecidableEq X]
      (read : X → Fin m → σ),
      ∃ T : X → ℕ, HasDualOn read (fun x => (T x, bldsFun g (read x))) (nodeCost L m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm g X _ _ read
  by_cases hsmall : m ≤ nodeArity
  · exact hasDualOn_bldsFun_small hL hsmall g read
  · rw [not_le] at hsmall
    -- level 1: the normalized arena
    have h1 := hasDualOn_normDesc read g hm
    -- level 2: the part anchors
    have h2 := h1.descriptorCompose
      (T := fun x => fun i : Fin nodeArity => ambP g (read x) (i : ℕ))
      (c := (nodeArity : ℝ) * ((L : ℝ) * (8 * (m : ℝ) ^ ((2 : ℝ) / 3))))
      fun dd => hasDualOn_family (fun i (z : Fiber (fun x => normDesc (read x) g) dd) =>
        ambP g (read z.val) (i : ℕ)) g fun i => hasDualOn_ambP g read hm dd (i : ℕ)
    -- level 3: the truncations
    have h3 := h2.descriptorCompose
      (T := fun x => fun i : Fin nodeArity => ambY g (read x) (i : ℕ))
      (c := (nodeArity : ℝ) * ((L : ℝ) * (8 * (m : ℝ) ^ ((2 : ℝ) / 3))))
      fun dd => hasDualOn_family (fun i (z : Fiber (fun x => (normDesc (read x) g,
        fun i : Fin nodeArity => ambP g (read x) (i : ℕ))) dd) =>
        ambY g (read z.val) (i : ℕ)) g fun i => hasDualOn_ambY g read hm dd i
    -- the value on the full fiber
    have h4 := h3.descriptorCompose (T := fun x => bldsFun g (read x))
      (c := 16 * (nodeCost L (2 * nodePartSize m) * Real.sqrt ((nodeArity : ℝ) + 1)))
      fun dd => hasDualOn_value g read hL hsmall
        (fun m' hm' g' Y _ _ rd => ih m' hm' (le_trans hm'.le hm) g' rd) _ dd
        (fun x y hxy => by
          refine ⟨congrArg (fun w => w.1.1) hxy, fun i hi => ?_, fun i hi => ?_⟩
          · exact congrArg Fin.val
              (congrFun (congrArg (fun w => w.1.2) hxy) ⟨i, hi⟩)
          · exact congrArg Fin.val (congrFun (congrArg (fun w => w.2) hxy) ⟨i, hi⟩))
    -- export the descriptor chain as a natural number
    obtain ⟨T, hT⟩ := exists_natEncode (fun x => ((normDesc (read x) g,
      fun i : Fin nodeArity => ambP g (read x) (i : ℕ)),
      fun i : Fin nodeArity => ambY g (read x) (i : ℕ)))
    refine ⟨T, (h4.ofKer fun x y => ?_).mono ?_⟩
    · constructor
      · intro hxy
        rw [Prod.mk.injEq] at hxy ⊢
        exact ⟨(hT x y).mp hxy.1, hxy.2⟩
      · intro hxy
        rw [Prod.mk.injEq] at hxy ⊢
        exact ⟨(hT x y).mpr hxy.1, hxy.2⟩
    · have hstep := nodeCost_step (L := L) (m := m) (m' := 2 * nodePartSize m)
        hsmall.le (two_mul_nodePartSize_le (le_refl m))
      have hcast : ((3 + 2 * nodeArity : ℕ) : ℝ) = 3 + 2 * (nodeArity : ℝ) := by push_cast; ring
      rw [hcast] at hstep
      nlinarith [hstep]

/-- **The node problem's adversary bound.**  Specialising the recursion to the
total promise and projecting the descriptor chain away — legal here because the
projection happens *outside* any dual construction, on the value of `advPM`
itself (`advPM_postcompose_le`), not by recoding a joint output. -/
theorem advPM_bldsFun_le {L m : ℕ} (hL : 1 ≤ L) (hm : m ≤ 2 ^ L) (g : Fin m) :
    advPM (fun β : Fin m → σ => bldsFun g β) ≤ nodeCost L m := by
  obtain ⟨T, hT⟩ := hasDualOn_bldsFun (σ := σ) L hL m hm g (X := Fin m → σ) id
  have hjoint : advPMOn (fun β : Fin m → σ => β) (fun β => (T β, bldsFun g β))
      ≤ nodeCost L m :=
    advPMOn_le_of_hasDualOn (nodeCost_nonneg L m) hT
  have hproj : advPM (fun β : Fin m → σ => bldsFun g β)
      ≤ advPM (fun β : Fin m → σ => (T β, bldsFun g β)) :=
    advPM_postcompose_le (g := fun β : Fin m → σ => (T β, bldsFun g β))
      (fun p : ℕ × ℕ => p.2)
  have hid : advPM (fun β : Fin m → σ => (T β, bldsFun g β))
      = advPMOn (fun β : Fin m → σ => β) (fun β => (T β, bldsFun g β)) := rfl
  rw [hid] at hproj
  exact le_trans hproj hjoint

end Dual

end QuantumQueryComplexity
