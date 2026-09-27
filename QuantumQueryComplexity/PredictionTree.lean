import QuantumQueryComplexity.FirstDiff
import QuantumQueryComplexity.HasDual
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Prediction trees: the layered guessing dual

The decision-tree guessing method of Beigi–Taghavi, in a weighted form:
a deterministic query procedure that at
each node reads a coordinate, branches on a **label** of the letter it finds,
and designates at most one label as **predicted**, has a dual whose load along
an execution is `4/w` per predicted answer and `4w` per unpredicted one (`w` the
node's weight).  Partitioning the nodes into layers with at most `T_j` queries
and `G_j` unpredicted answers per execution and choosing `w_j = √(T_j/G_j)`
gives cost `8 ∑_j √(T_j·G_j)` (`hasDual_eval_layered`).

Compared with `DecisionTree.lean` (Boolean labels that *are* the queried
value, unit cost per node) this construction follows the paper's transcript
argument rather than masking the subtrees:

* a node's own block sits on its coordinate and is the tensor of three
  gadgets — the **colour** gadget `colU/colV` (inner product `1` unless both
  answers are predicted), the **label** gadget `phiVec (lab (x i))`
  (inner product `[labels differ]`) and the **output** gadget `phiVec (f x)`
  (inner product `[outputs differ]`);
* each child's solution is embedded, unmasked, in the block of its label.

For inputs `x, y` whose labels at the node agree, the node block vanishes
(label gadget) and both inputs continue into the same child, whose constraint
gives `[f x ≠ f y]`; when the labels differ, the children's blocks are
orthogonal, the coordinate is genuinely queried, and the node block alone
delivers `[f x ≠ f y]` — the colour factor is `1` because two different labels
cannot both be the prediction.  No coordinate is ever masked, so a subtree may
re-query a coordinate freely.

The loads are **input-dependent** (`uLoad`, `vLoad`), which is what the paper
remarks a worst-case bound alone would not give.
-/

namespace QuantumQueryComplexity

/-! ## The colour gadget -/

section Colour

/-- The `u`-side colour vector: `(1/√w, 0)` for a predicted answer,
`(0, √w)` for an unpredicted one. -/
noncomputable def colU (w : ℝ) (unpred : Bool) : Bool → ℝ :=
  fun s => if unpred then (if s then Real.sqrt w else 0) else (if s then 0 else 1 / Real.sqrt w)

/-- The `v`-side colour vector: `(0, 1/√w)` for a predicted answer,
`(√w, 1/√w)` for an unpredicted one. -/
noncomputable def colV (w : ℝ) (unpred : Bool) : Bool → ℝ :=
  fun s => if unpred then (if s then 1 / Real.sqrt w else Real.sqrt w)
    else (if s then 1 / Real.sqrt w else 0)

lemma sum_colU_mul_colV {w : ℝ} (hw : 0 < w) (cx cy : Bool) :
    (∑ s : Bool, colU w cx s * colV w cy s) = if cx = false ∧ cy = false then 0 else 1 := by
  have hs : Real.sqrt w ≠ 0 := (Real.sqrt_pos.mpr hw).ne'
  cases cx <;> cases cy <;> simp [colU, colV, Fintype.sum_bool, hs]

lemma sum_colU_sq {w : ℝ} (hw : 0 < w) (c : Bool) :
    (∑ s : Bool, colU w c s * colU w c s) = if c then w else 1 / w := by
  have hs : Real.sqrt w * Real.sqrt w = w := Real.mul_self_sqrt hw.le
  have hinv : (Real.sqrt w)⁻¹ * (Real.sqrt w)⁻¹ = w⁻¹ := by rw [← mul_inv, hs]
  cases c <;> simp [colU, hs, hinv]

lemma sum_colV_sq {w : ℝ} (hw : 0 < w) (c : Bool) :
    (∑ s : Bool, colV w c s * colV w c s) = if c then w + 1 / w else 1 / w := by
  have hs : Real.sqrt w * Real.sqrt w = w := Real.mul_self_sqrt hw.le
  have hinv : (Real.sqrt w)⁻¹ * (Real.sqrt w)⁻¹ = w⁻¹ := by rw [← mul_inv, hs]
  cases c <;> simp [colV, hs, hinv, add_comm]

/-- Distributing a product of three gadgets over the three index sums. -/
lemma sum_prod3_mul {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (a a' : A → ℝ) (b b' : B → ℝ) (c c' : C → ℝ) :
    (∑ p : A × B × C, (a p.1 * b p.2.1 * c p.2.2) * (a' p.1 * b' p.2.1 * c' p.2.2))
      = (∑ s, a s * a' s) * (∑ t, b t * b' t) * (∑ t, c t * c' t) := by
  have h1 : ∀ p : A × B × C, (a p.1 * b p.2.1 * c p.2.2) * (a' p.1 * b' p.2.1 * c' p.2.2)
      = (a p.1 * a' p.1) * ((b p.2.1 * b' p.2.1) * (c p.2.2 * c' p.2.2)) := fun p => by ring
  simp only [h1]
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [← Finset.sum_mul_sum, Fintype.sum_prod_type]
  dsimp only
  rw [← Finset.sum_mul_sum, mul_assoc]

end Colour

/-! ## Prediction trees -/

/-- A deterministic query procedure with predicted answers.  A `query` node
names the coordinate it reads, the label map applied to the letter found, the
predicted label (if any), its layer, and the continuation for each label. -/
inductive PredTree (ι σ α J O : Type) where
  /-- Stop and answer. -/
  | leaf : O → PredTree ι σ α J O
  /-- Read coordinate `i`, label the letter, and continue. -/
  | query : ι → (σ → α) → Option α → J → (α → PredTree ι σ α J O) → PredTree ι σ α J O

namespace PredTree

variable {ι σ α J O : Type}

/-- Running the procedure. -/
def eval : PredTree ι σ α J O → (ι → σ) → O
  | leaf o, _ => o
  | query i lab _ _ k, x => (k (lab (x i))).eval x

@[simp] lemma eval_leaf (o : O) (x : ι → σ) : (leaf o : PredTree ι σ α J O).eval x = o := rfl

@[simp] lemma eval_query (i : ι) (lab : σ → α) (pred : Option α) (j : J)
    (k : α → PredTree ι σ α J O) (x : ι → σ) :
    (query i lab pred j k).eval x = (k (lab (x i))).eval x := rfl

variable [DecidableEq α]

/-- The answer at a node is unpredicted. -/
def unpred (pred : Option α) (a : α) : Bool := decide (pred ≠ some a)

/-- The `u`-side load of an execution, with per-layer weights `w`:
`4/w` at a predicted answer, `4·w` at an unpredicted one. -/
noncomputable def uLoad (w : J → ℝ) : PredTree ι σ α J O → (ι → σ) → ℝ
  | leaf _, _ => 0
  | query i lab pred j k, x =>
      (if unpred pred (lab (x i)) then 4 * w j else 4 / w j) + (k (lab (x i))).uLoad w x

/-- The `v`-side load: `4/w` at a predicted answer, `4·(w + 1/w)` at an
unpredicted one. -/
noncomputable def vLoad (w : J → ℝ) : PredTree ι σ α J O → (ι → σ) → ℝ
  | leaf _, _ => 0
  | query i lab pred j k, x =>
      (if unpred pred (lab (x i)) then 4 * (w j + 1 / w j) else 4 / w j)
        + (k (lab (x i))).vLoad w x

/-- The number of visited nodes of layer `j₀`. -/
def visits (j₀ : J) [DecidableEq J] : PredTree ι σ α J O → (ι → σ) → ℕ
  | leaf _, _ => 0
  | query i lab _ j k, x => (if j = j₀ then 1 else 0) + (k (lab (x i))).visits j₀ x

/-- The number of unpredicted answers received in layer `j₀`. -/
def unpreds (j₀ : J) [DecidableEq J] : PredTree ι σ α J O → (ι → σ) → ℕ
  | leaf _, _ => 0
  | query i lab pred j k, x =>
      (if j = j₀ ∧ unpred pred (lab (x i)) then 1 else 0) + (k (lab (x i))).unpreds j₀ x

/-- Relabelling the leaves. -/
def mapOut {O' : Type} (φ : O → O') : PredTree ι σ α J O → PredTree ι σ α J O'
  | leaf o => leaf (φ o)
  | query i lab pred j k => query i lab pred j fun a => (k a).mapOut φ

@[simp] lemma eval_mapOut {O' : Type} (φ : O → O') (T : PredTree ι σ α J O) (x : ι → σ) :
    (T.mapOut φ).eval x = φ (T.eval x) := by
  induction T with
  | leaf o => rfl
  | query i lab pred j k ih => exact ih (lab (x i))

@[simp] lemma visits_mapOut {O' : Type} [DecidableEq J] (φ : O → O') (j₀ : J)
    (T : PredTree ι σ α J O) (x : ι → σ) : (T.mapOut φ).visits j₀ x = T.visits j₀ x := by
  induction T with
  | leaf o => rfl
  | query i lab pred j k ih =>
      simp only [mapOut, visits]
      rw [ih]

@[simp] lemma unpreds_mapOut {O' : Type} [DecidableEq J] (φ : O → O') (j₀ : J)
    (T : PredTree ι σ α J O) (x : ι → σ) : (T.mapOut φ).unpreds j₀ x = T.unpreds j₀ x := by
  induction T with
  | leaf o => rfl
  | query i lab pred j k ih =>
      simp only [mapOut, unpreds]
      rw [ih]

/-- **Sequencing**: run `T`, then continue with the tree chosen by its output
(every leaf `o` is replaced by `k o`). -/
def bind {O' : Type} : PredTree ι σ α J O → (O → PredTree ι σ α J O') → PredTree ι σ α J O'
  | leaf o, k => k o
  | query i lab pred j c, k => query i lab pred j fun a => (c a).bind k

@[simp] lemma bind_leaf {O' : Type} (o : O) (k : O → PredTree ι σ α J O') :
    (leaf o : PredTree ι σ α J O).bind k = k o := rfl

@[simp] lemma eval_bind {O' : Type} (T : PredTree ι σ α J O) (k : O → PredTree ι σ α J O')
    (x : ι → σ) : (T.bind k).eval x = (k (T.eval x)).eval x := by
  induction T with
  | leaf o => rfl
  | query i lab pred j c ih => exact ih (lab (x i))

/-- Visits add up along a sequencing. -/
lemma visits_bind {O' : Type} [DecidableEq J] (j₀ : J) (T : PredTree ι σ α J O)
    (k : O → PredTree ι σ α J O') (x : ι → σ) :
    (T.bind k).visits j₀ x = T.visits j₀ x + (k (T.eval x)).visits j₀ x := by
  induction T with
  | leaf o => simp [visits]
  | query i lab pred j c ih =>
      simp only [bind, visits, eval_query]
      rw [ih, add_assoc]

/-- Unpredicted answers add up along a sequencing. -/
lemma unpreds_bind {O' : Type} [DecidableEq J] (j₀ : J) (T : PredTree ι σ α J O)
    (k : O → PredTree ι σ α J O') (x : ι → σ) :
    (T.bind k).unpreds j₀ x = T.unpreds j₀ x + (k (T.eval x)).unpreds j₀ x := by
  induction T with
  | leaf o => simp [unpreds]
  | query i lab pred j c ih =>
      simp only [bind, unpreds, eval_query]
      rw [ih, add_assoc]

/-- A leaf makes no queries. -/
@[simp] lemma visits_leaf [DecidableEq J] (j₀ : J) (o : O) (x : ι → σ) :
    (leaf o : PredTree ι σ α J O).visits j₀ x = 0 := rfl

@[simp] lemma unpreds_leaf [DecidableEq J] (j₀ : J) (o : O) (x : ι → σ) :
    (leaf o : PredTree ι σ α J O).unpreds j₀ x = 0 := rfl

lemma visits_query [DecidableEq J] (j₀ : J) (i : ι) (lab : σ → α) (pred : Option α) (j : J)
    (k : α → PredTree ι σ α J O) (x : ι → σ) :
    (query i lab pred j k).visits j₀ x = (if j = j₀ then 1 else 0) + (k (lab (x i))).visits j₀ x :=
  rfl

lemma unpreds_query [DecidableEq J] (j₀ : J) (i : ι) (lab : σ → α) (pred : Option α) (j : J)
    (k : α → PredTree ι σ α J O) (x : ι → σ) :
    (query i lab pred j k).unpreds j₀ x
      = (if j = j₀ ∧ unpred pred (lab (x i)) then 1 else 0) + (k (lab (x i))).unpreds j₀ x :=
  rfl

end PredTree

/-! ## The dual of one node -/

section Node

variable {ι σ α O : Type} [Fintype ι] [DecidableEq ι] [DecidableEq σ]
  [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable {K : α → Type} [∀ a, Fintype (K a)]

open PredTree

/-- The vector family of a node: the children's solutions in the blocks of
their labels, plus the three-gadget block on the queried coordinate. -/
noncomputable def nodeVec (i : ι) (lab : σ → α) (pred : Option α) (w : ℝ)
    (col : ℝ → Bool → Bool → ℝ) (gad : ∀ {β : Type} [DecidableEq β], β → Option β → ℝ)
    (wv : (a : α) → (ι → σ) → ι → K a → ℝ) (g : (ι → σ) → O)
    (x : ι → σ) (j : ι) : (Σ a, K a) ⊕ (Bool × Option α × Option O) → ℝ :=
  Sum.elim
    (fun ak => if ak.1 = lab (x i) then wv ak.1 x j ak.2 else 0)
    (fun st => if j = i then
      col w (unpred pred (lab (x i))) st.1 * gad (lab (x i)) st.2.1 * gad (g x) st.2.2
      else 0)

variable {f : (ι → σ) → O}

/-- **The dual solution of one node.** -/
noncomputable def nodeDual (i : ι) (lab : σ → α) (pred : Option α) {w : ℝ} (hw : 0 < w)
    {fk : α → (ι → σ) → O} (hf : ∀ x, f x = fk (lab (x i)) x)
    (P : ∀ a, DualPair (K a) (fk a)) :
    DualPair ((Σ a, K a) ⊕ (Bool × Option α × Option O)) f where
  u := nodeVec i lab pred w colU (fun {_} [_] => phiVec) (fun a => (P a).u) f
  v := nodeVec i lab pred w colV (fun {_} [_] => psiVec) (fun a => (P a).v) f
  constraint x y := by
    classical
    -- the coordinate-`j` inner product, split into the children's part and the node part
    have hinner : ∀ j : ι,
        (∑ k, nodeVec i lab pred w colU (fun {_} [_] => phiVec) (fun a => (P a).u) f x j k
          * nodeVec i lab pred w colV (fun {_} [_] => psiVec) (fun a => (P a).v) f y j k)
        = (if lab (x i) = lab (y i)
            then ∑ k, (P (lab (x i))).u x j k * (P (lab (x i))).v y j k else 0)
          + (if j = i then
              (∑ s : Bool, colU w (unpred pred (lab (x i))) s * colV w (unpred pred (lab (y i))) s)
              * (∑ t, phiVec (lab (x i)) t * psiVec (lab (y i)) t)
              * (∑ t, phiVec (f x) t * psiVec (f y) t) else 0) := by
      intro j
      rw [Fintype.sum_sum_type]
      congr 1
      · -- the children's blocks
        rw [Fintype.sum_sigma]
        simp only [nodeVec, Sum.elim_inl]
        by_cases hl : lab (x i) = lab (y i)
        · rw [if_pos hl]
          rw [Finset.sum_eq_single (lab (x i))]
          · simp [hl]
          · intro a _ ha
            refine Finset.sum_eq_zero fun k _ => ?_
            rw [if_neg ha, zero_mul]
          · exact fun h => absurd (Finset.mem_univ _) h
        · rw [if_neg hl]
          refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun k _ => ?_
          by_cases ha : a = lab (x i)
          · rw [if_neg (show ¬ a = lab (y i) from fun h => hl (ha.symm.trans h)), mul_zero]
          · rw [if_neg ha, zero_mul]
      · -- the node block
        simp only [nodeVec, Sum.elim_inr]
        by_cases hj : j = i
        · rw [if_pos hj]
          simp only [if_pos hj]
          exact sum_prod3_mul _ _ _ _ _ _
        · rw [if_neg hj]
          simp [hj]
    simp only [hinner]
    by_cases hl : lab (x i) = lab (y i)
    · -- same label: the child's constraint, the node block vanishes
      have hfx : f x = fk (lab (x i)) x := hf x
      have hfy : f y = fk (lab (x i)) y := by rw [hf y, hl]
      rw [hfx, hfy, ← (P (lab (x i))).constraint x y]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hxy : x j = y j
      · rw [if_pos hxy, if_pos hxy]
      · rw [if_neg hxy, if_neg hxy, if_pos hl]
        have hlab : (∑ t, phiVec (lab (x i)) t * psiVec (lab (y i)) t) = 0 := by
          rw [sum_phiVec_mul_psiVec, if_pos hl]
        rw [hlab]
        simp
    · -- different labels: only the node block, at the queried coordinate
      have hxi : x i ≠ y i := fun h => hl (by rw [h])
      rw [Finset.sum_eq_single i]
      · rw [if_neg hxi, if_neg hl, zero_add, if_pos rfl, sum_colU_mul_colV hw,
          sum_phiVec_mul_psiVec, sum_phiVec_mul_psiVec, if_neg hl]
        have hcol : ¬ (unpred pred (lab (x i)) = false ∧ unpred pred (lab (y i)) = false) := by
          rintro ⟨h1, h2⟩
          simp only [unpred, decide_eq_false_iff_not, not_not] at h1 h2
          exact hl (Option.some.inj (h1.symm.trans h2))
        rw [if_neg hcol]
        ring
      · intro j _ hj
        by_cases hxy : x j = y j
        · rw [if_pos hxy]
        · rw [if_neg hxy, if_neg hl, if_neg hj, add_zero]
      · exact fun h => absurd (Finset.mem_univ i) h

/-- The `u`-load of the node family: the node's own `4/w` or `4w`, plus the
child the input takes. -/
lemma nodeVec_u_load (i : ι) (lab : σ → α) (pred : Option α) {w : ℝ} (hw : 0 < w)
    (wv : (a : α) → (ι → σ) → ι → K a → ℝ) (g : (ι → σ) → O) (x : ι → σ) :
    (∑ j, ∑ k, nodeVec i lab pred w colU (fun {_} [_] => phiVec) wv g x j k
        * nodeVec i lab pred w colU (fun {_} [_] => phiVec) wv g x j k)
      = (if unpred pred (lab (x i)) then 4 * w else 4 / w)
        + ∑ j, ∑ k, wv (lab (x i)) x j k * wv (lab (x i)) x j k := by
  classical
  have hj : ∀ j : ι,
      (∑ k, nodeVec i lab pred w colU (fun {_} [_] => phiVec) wv g x j k
        * nodeVec i lab pred w colU (fun {_} [_] => phiVec) wv g x j k)
      = (if j = i then (if unpred pred (lab (x i)) then 4 * w else 4 / w) else 0)
        + ∑ k, wv (lab (x i)) x j k * wv (lab (x i)) x j k := by
    intro j
    rw [Fintype.sum_sum_type, add_comm]
    congr 1
    · simp only [nodeVec, Sum.elim_inr]
      by_cases hji : j = i
      · rw [if_pos hji]
        simp only [if_pos hji]
        rw [sum_prod3_mul, sum_colU_sq hw, sum_phiVec_sq, sum_phiVec_sq]
        split_ifs <;> ring
      · rw [if_neg hji]
        simp [hji]
    · rw [Fintype.sum_sigma]
      simp only [nodeVec, Sum.elim_inl]
      rw [Finset.sum_eq_single (lab (x i))]
      · simp
      · intro a _ ha
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [if_neg ha, zero_mul]
      · exact fun h => absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i)]

/-- The `v`-load of the node family. -/
lemma nodeVec_v_load (i : ι) (lab : σ → α) (pred : Option α) {w : ℝ} (hw : 0 < w)
    (wv : (a : α) → (ι → σ) → ι → K a → ℝ) (g : (ι → σ) → O) (x : ι → σ) :
    (∑ j, ∑ k, nodeVec i lab pred w colV (fun {_} [_] => psiVec) wv g x j k
        * nodeVec i lab pred w colV (fun {_} [_] => psiVec) wv g x j k)
      = (if unpred pred (lab (x i)) then 4 * (w + 1 / w) else 4 / w)
        + ∑ j, ∑ k, wv (lab (x i)) x j k * wv (lab (x i)) x j k := by
  classical
  have hj : ∀ j : ι,
      (∑ k, nodeVec i lab pred w colV (fun {_} [_] => psiVec) wv g x j k
        * nodeVec i lab pred w colV (fun {_} [_] => psiVec) wv g x j k)
      = (if j = i then (if unpred pred (lab (x i)) then 4 * (w + 1 / w) else 4 / w) else 0)
        + ∑ k, wv (lab (x i)) x j k * wv (lab (x i)) x j k := by
    intro j
    rw [Fintype.sum_sum_type, add_comm]
    congr 1
    · simp only [nodeVec, Sum.elim_inr]
      by_cases hji : j = i
      · rw [if_pos hji]
        simp only [if_pos hji]
        rw [sum_prod3_mul, sum_colV_sq hw, sum_psiVec_sq, sum_psiVec_sq]
        split_ifs <;> ring
      · rw [if_neg hji]
        simp [hji]
    · rw [Fintype.sum_sigma]
      simp only [nodeVec, Sum.elim_inl]
      rw [Finset.sum_eq_single (lab (x i))]
      · simp
      · intro a _ ha
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [if_neg ha, zero_mul]
      · exact fun h => absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i)]

end Node

/-! ## The dual of a tree -/

namespace PredTree

variable {ι σ α J O : Type} [Fintype ι] [DecidableEq ι] [DecidableEq σ]
  [Fintype α] [DecidableEq α] [DecidableEq O]

/-- **The input-dependent dual**: for positive layer weights, `T.eval` has a
dual solution whose `u`-load at `x` is at most `uLoad w T x` and whose `v`-load
at `y` is at most `vLoad w T y`. -/
theorem exists_dualPair_of_fintype [Fintype O] (w : J → ℝ) (hw : ∀ j, 0 < w j)
    (T : PredTree ι σ α J O) :
    ∃ (K : Type) (_ : Fintype K) (P : DualPair K T.eval),
      (∀ x, ∑ i, ∑ k, P.u x i k * P.u x i k ≤ T.uLoad w x) ∧
      (∀ y, ∑ i, ∑ k, P.v y i k * P.v y i k ≤ T.vLoad w y) := by
  classical
  induction T with
  | leaf o =>
      refine ⟨Unit, inferInstance,
        ⟨fun _ _ _ => 0, fun _ _ _ => 0, fun x y => by simp⟩, ?_, ?_⟩
      · intro x; simp [uLoad]
      · intro y; simp [vLoad]
  | query i lab pred j k ih =>
      choose K instK P hP using ih
      refine ⟨(Σ a, K a) ⊕ (Bool × Option α × Option O), inferInstance,
        nodeDual i lab pred (hw j) (fk := fun a => (k a).eval) (fun x => rfl) P, ?_, ?_⟩
      · intro x
        show (∑ i', ∑ k', nodeVec i lab pred (w j) colU (fun {_} [_] => phiVec)
            (fun a => (P a).u) (query i lab pred j k).eval x i' k'
          * nodeVec i lab pred (w j) colU (fun {_} [_] => phiVec)
            (fun a => (P a).u) (query i lab pred j k).eval x i' k') ≤ _
        rw [nodeVec_u_load i lab pred (hw j)]
        simp only [uLoad]
        exact add_le_add (le_refl _) ((hP (lab (x i))).1 x)
      · intro y
        show (∑ i', ∑ k', nodeVec i lab pred (w j) colV (fun {_} [_] => psiVec)
            (fun a => (P a).v) (query i lab pred j k).eval y i' k'
          * nodeVec i lab pred (w j) colV (fun {_} [_] => psiVec)
            (fun a => (P a).v) (query i lab pred j k).eval y i' k') ≤ _
        rw [nodeVec_v_load i lab pred (hw j)]
        simp only [vLoad]
        exact add_le_add (le_refl _) ((hP (lab (y i))).2 y)

/-- **The tree dual, from uniform load bounds**: if every execution has
`u`-load and `v`-load at most `V`, then `HasDual T.eval V`. -/
theorem hasDual_eval_of_loads [Fintype O] (w : J → ℝ) (hw : ∀ j, 0 < w j)
    (T : PredTree ι σ α J O) {V : ℝ}
    (hu : ∀ x, T.uLoad w x ≤ V) (hv : ∀ y, T.vLoad w y ≤ V) :
    HasDual T.eval V := by
  obtain ⟨K, hK, P, hPu, hPv⟩ := exists_dualPair_of_fintype w hw T
  exact ⟨K, hK, P, fun x => (hPu x).trans (hu x), fun y => (hPv y).trans (hv y)⟩

/-! ### Layer budgets -/

variable [DecidableEq J] [Fintype J]

/-- The `u`-load is at most the layerwise count. -/
lemma uLoad_le_sum (w : J → ℝ) (hw : ∀ j, 0 < w j) (T : PredTree ι σ α J O) (x : ι → σ) :
    T.uLoad w x ≤ ∑ j, (4 / w j * (T.visits j x : ℝ) + 4 * w j * (T.unpreds j x : ℝ)) := by
  induction T with
  | leaf o => simp [uLoad, visits, unpreds]
  | query i lab pred j k ih =>
      simp only [uLoad, visits, unpreds]
      push_cast
      simp only [mul_add, Finset.sum_add_distrib]
      have hnode : (if unpred pred (lab (x i)) then 4 * w j else 4 / w j)
          ≤ ∑ j', (4 / w j' * (if j = j' then (1 : ℝ) else 0)
              + 4 * w j' * (if j = j' ∧ unpred pred (lab (x i)) then (1 : ℝ) else 0)) := by
        rw [Finset.sum_add_distrib]
        have h1 : (∑ j', 4 / w j' * (if j = j' then (1 : ℝ) else 0)) = 4 / w j := by
          simp [Finset.sum_ite_eq]
        have h2 : (∑ j', 4 * w j' * (if j = j' ∧ unpred pred (lab (x i)) then (1 : ℝ) else 0))
            = if unpred pred (lab (x i)) then 4 * w j else 0 := by
          by_cases hu : unpred pred (lab (x i)) = true
          · simp [hu, Finset.sum_ite_eq]
          · simp [hu]
        rw [h1, h2]
        have hpos : 0 ≤ 4 / w j := by have := hw j; positivity
        have hpos' : 0 ≤ 4 * w j := by have := hw j; positivity
        split_ifs <;> linarith
      have hsum : ∑ j', (4 / w j' * ((if j = j' then (1 : ℝ) else 0) + (k (lab (x i))).visits j' x)
            + 4 * w j' * ((if j = j' ∧ unpred pred (lab (x i)) then (1 : ℝ) else 0)
              + (k (lab (x i))).unpreds j' x))
          = ∑ j', (4 / w j' * (if j = j' then (1 : ℝ) else 0)
              + 4 * w j' * (if j = j' ∧ unpred pred (lab (x i)) then (1 : ℝ) else 0))
            + ∑ j', (4 / w j' * ((k (lab (x i))).visits j' x : ℝ)
              + 4 * w j' * ((k (lab (x i))).unpreds j' x : ℝ)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j' _ => ?_
        ring
      calc (if unpred pred (lab (x i)) then 4 * w j else 4 / w j) + (k (lab (x i))).uLoad w x
          ≤ (∑ j', (4 / w j' * (if j = j' then (1 : ℝ) else 0)
              + 4 * w j' * (if j = j' ∧ unpred pred (lab (x i)) then (1 : ℝ) else 0)))
            + ∑ j', (4 / w j' * ((k (lab (x i))).visits j' x : ℝ)
              + 4 * w j' * ((k (lab (x i))).unpreds j' x : ℝ)) :=
            add_le_add hnode (ih (lab (x i)))
        _ = _ := by
            rw [← hsum]
            simp only [mul_add, Finset.sum_add_distrib]

/-- The `v`-load is at most the layerwise count, with the extra `4/w` per
unpredicted answer absorbed into the visit count. -/
lemma vLoad_le_sum (w : J → ℝ) (hw : ∀ j, 0 < w j) (T : PredTree ι σ α J O) (x : ι → σ) :
    T.vLoad w x ≤ ∑ j, (4 / w j * (T.visits j x : ℝ) + 4 * w j * (T.unpreds j x : ℝ)) := by
  induction T with
  | leaf o => simp [vLoad, visits, unpreds]
  | query i lab pred j k ih =>
      simp only [vLoad, visits, unpreds]
      push_cast
      have hnode : (if unpred pred (lab (x i)) then 4 * (w j + 1 / w j) else 4 / w j)
          ≤ ∑ j', (4 / w j' * (if j = j' then (1 : ℝ) else 0)
              + 4 * w j' * (if j = j' ∧ unpred pred (lab (x i)) then (1 : ℝ) else 0)) := by
        rw [Finset.sum_add_distrib]
        have h1 : (∑ j', 4 / w j' * (if j = j' then (1 : ℝ) else 0)) = 4 / w j := by
          simp [Finset.sum_ite_eq]
        have h2 : (∑ j', 4 * w j' * (if j = j' ∧ unpred pred (lab (x i)) then (1 : ℝ) else 0))
            = if unpred pred (lab (x i)) then 4 * w j else 0 := by
          by_cases hu : unpred pred (lab (x i)) = true
          · simp [hu, Finset.sum_ite_eq]
          · simp [hu]
        rw [h1, h2]
        have hpos : 0 ≤ 4 / w j := by have := hw j; positivity
        split_ifs
        · have : 4 * (w j + 1 / w j) = 4 / w j + 4 * w j := by ring
          rw [this]
        · linarith
      have hsum : ∑ j', (4 / w j' * ((if j = j' then (1 : ℝ) else 0) + (k (lab (x i))).visits j' x)
            + 4 * w j' * ((if j = j' ∧ unpred pred (lab (x i)) then (1 : ℝ) else 0)
              + (k (lab (x i))).unpreds j' x))
          = ∑ j', (4 / w j' * (if j = j' then (1 : ℝ) else 0)
              + 4 * w j' * (if j = j' ∧ unpred pred (lab (x i)) then (1 : ℝ) else 0))
            + ∑ j', (4 / w j' * ((k (lab (x i))).visits j' x : ℝ)
              + 4 * w j' * ((k (lab (x i))).unpreds j' x : ℝ)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j' _ => ?_
        ring
      calc (if unpred pred (lab (x i)) then 4 * (w j + 1 / w j) else 4 / w j)
            + (k (lab (x i))).vLoad w x
          ≤ (∑ j', (4 / w j' * (if j = j' then (1 : ℝ) else 0)
              + 4 * w j' * (if j = j' ∧ unpred pred (lab (x i)) then (1 : ℝ) else 0)))
            + ∑ j', (4 / w j' * ((k (lab (x i))).visits j' x : ℝ)
              + 4 * w j' * ((k (lab (x i))).unpreds j' x : ℝ)) :=
            add_le_add hnode (ih (lab (x i)))
        _ = _ := by rw [← hsum]

/-- The arithmetic of the weight choice `w = √(T/G)`:
`4T/w + 4Gw = 8√(TG)`. -/
lemma budget_eq {T G : ℝ} (hT : 0 < T) (hG : 0 < G) :
    4 / Real.sqrt (T / G) * T + 4 * Real.sqrt (T / G) * G = 8 * Real.sqrt (T * G) := by
  have hs : Real.sqrt (T / G) = Real.sqrt T / Real.sqrt G := Real.sqrt_div hT.le G
  have hT' : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT.le
  have hG' : Real.sqrt G * Real.sqrt G = G := Real.mul_self_sqrt hG.le
  have hTG : Real.sqrt (T * G) = Real.sqrt T * Real.sqrt G := Real.sqrt_mul hT.le G
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hsG : 0 < Real.sqrt G := Real.sqrt_pos.mpr hG
  rw [hs, hTG]
  field_simp
  nlinarith [hT', hG']

/-- **Lemma `lem:prediction`**: a prediction tree whose every
execution makes at most `T j` queries and receives at most `G j` unpredicted
answers in layer `j` (all `T j, G j > 0`) has a dual of cost
`8 ∑_j √(T j · G j)`, at the weights `w j = √(T j / G j)`. -/
theorem hasDual_eval_layered [Fintype O] (Tr : PredTree ι σ α J O) {T G : J → ℝ}
    (hT : ∀ j, 0 < T j) (hG : ∀ j, 0 < G j)
    (hvis : ∀ x j, (Tr.visits j x : ℝ) ≤ T j)
    (hunp : ∀ x j, (Tr.unpreds j x : ℝ) ≤ G j) :
    HasDual Tr.eval (8 * ∑ j, Real.sqrt (T j * G j)) := by
  set w : J → ℝ := fun j => Real.sqrt (T j / G j) with hw
  have hwpos : ∀ j, 0 < w j := fun j => Real.sqrt_pos.mpr (div_pos (hT j) (hG j))
  have hbound : ∀ x, (∑ j, (4 / w j * (Tr.visits j x : ℝ) + 4 * w j * (Tr.unpreds j x : ℝ)))
      ≤ 8 * ∑ j, Real.sqrt (T j * G j) := by
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← budget_eq (hT j) (hG j)]
    have h1 : 4 / w j * (Tr.visits j x : ℝ) ≤ 4 / Real.sqrt (T j / G j) * T j :=
      mul_le_mul_of_nonneg_left (hvis x j) (by have := hwpos j; positivity)
    have h2 : 4 * w j * (Tr.unpreds j x : ℝ) ≤ 4 * Real.sqrt (T j / G j) * G j :=
      mul_le_mul_of_nonneg_left (hunp x j) (by have := hwpos j; positivity)
    linarith
  exact hasDual_eval_of_loads w hwpos Tr
    (fun x => (uLoad_le_sum w hwpos Tr x).trans (hbound x))
    (fun y => (vLoad_le_sum w hwpos Tr y).trans (hbound y))

/-- The same with an arbitrary output type: the reachable outputs are recoded
into a finite type at no cost. -/
theorem hasDual_eval_layered' (Tr : PredTree ι σ α J O) {T G : J → ℝ}
    (hT : ∀ j, 0 < T j) (hG : ∀ j, 0 < G j)
    (hvis : ∀ x j, (Tr.visits j x : ℝ) ≤ T j)
    (hunp : ∀ x j, (Tr.unpreds j x : ℝ) ≤ G j) [Fintype σ] :
    HasDual Tr.eval (8 * ∑ j, Real.sqrt (T j * G j)) := by
  classical
  set S : Finset O := Finset.image Tr.eval Finset.univ with hS
  have hmem : ∀ x : ι → σ, Tr.eval x ∈ S := fun x =>
    Finset.mem_image_of_mem _ (Finset.mem_univ x)
  set φ : O → Option {o // o ∈ S} :=
    fun o => if h : o ∈ S then some ⟨o, h⟩ else none with hφ
  have hbase := hasDual_eval_layered (Tr.mapOut φ) hT hG
    (fun x j => by rw [visits_mapOut]; exact hvis x j)
    (fun x j => by rw [unpreds_mapOut]; exact hunp x j)
  refine hbase.ofKer fun x y => ?_
  rw [eval_mapOut, eval_mapOut, hφ]
  simp only [dif_pos (hmem x), dif_pos (hmem y), Option.some.injEq, Subtype.mk.injEq]

end PredTree

end QuantumQueryComplexity
