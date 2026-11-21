import QuantumQueryComplexity.Quantum.ProductRun
import QuantumQueryComplexity.Quantum.Relation
import QuantumQueryComplexity.Quantum.ReadGadget

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Decision trees over the swap oracle, and derived oracles

A **decision tree** `ReadTree ι σ O` reads letters of an input `x : ι → σ` adaptively: a node
names an index `i`, and the subtree to continue with is chosen by the letter `x i`; a leaf
outputs a value in `O`. `eval` runs it on an input, and `depth` bounds the number of reads: a
leaf has depth `0` and a node has depth one more than the largest depth of its subtrees (the
maximum over all letters, including letters no input produces; `0` if there are none).
(`QueryTree` in `QuantumQueryComplexity/DecisionTree.lean` is a different object: a tree over
Boolean labels used to build adversary duals.)

**Classical procedures cost what they read** (`ReadTree.realizes`). A tree can be run with
exactly `T` swap queries for any `T` at least its depth, by an algorithm fixed before the input,
and its output is the tree's value with probability one, in the sense of `Realizes`
(`ProductRun.lean`). The output type may be infinite but must be nonempty (an algorithm's readout
is a total function on a nonempty basis). So a deterministic classical procedure enters
`Realizes.pair`, `Realizes.bind` and `Realizes.map` like any other stage, under their own
hypotheses: `Realizes.bind` needs a finite type for the outcome that selects the next stage, and
`Realizes.map` a finite source type (and both `[Fintype X]` on the promise type); a stored list
that selects a later stage should therefore be encoded in a finite type (fixed-length tuples, a
finite subtype), while a final stage may output an ordinary list.

**Derived oracles** (`exists_treeSim`). Suppose every letter `y j` of a derived input
`y : ι' → σ'` is computed by a decision tree of depth at most `T` over `x`:
`y = treeInput t x`, `y j = (t j).eval x`. Then every algorithm `A` making swap queries to `y`
has a simulation `B` making swap queries to `x`, fixed before `x` (and before the query count),
with `2T` queries to `x` per query to `y` and **the same success probability for every relation
on outputs**. Each simulated query computes `y j` into scratch registers (at most `T` adaptive
reads, padded with idle queries to exactly `T`), applies `A`'s swap oracle with the computed
letter on `A`'s registers, and uncomputes the reads with `T` more queries. `0 < T` is needed
because `B` is the same for every query count: with `T = 0` the left side would not depend on
`q`. `Realizes.treeSim` is the same statement for outcome laws, and `exists_readsSim` is the
non-adaptive case (`k` fixed reads per letter, `2k` queries per query), the swap-oracle analogue
of `exists_wordSim` of the companion repository `quantum-query-problems`.

The trees branch on letters `σ`, not on `Option σ`: a read of `x i` into a blank answer register
always returns `some (x i)` (`oracleMap_blank`). The derived input is defined from the trees for
every `x`, so the statements hold for every input, valid or not.

## Main statements

* `ReadTree.realizes` — a tree of depth `≤ T`, nonempty output type: exactly `T` queries, output a
  point mass.
* `exists_treeSim` — derived oracles by decision trees of depth `≤ T`, `0 < T`: `2Tq` queries
  simulate `q`, for every `q` by one algorithm.
* `Realizes.treeSim` — the same, for realizable outcome laws on a promise.
* `exists_readsSim` — non-adaptive reads, `0 < k`: `2kq` queries simulate `q`.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

/-- **A deterministic decision tree** reading an input `x : ι → σ` and outputting a value in
`O`: a leaf outputs its value; a node reads the letter `x i` and continues with the subtree
`k (x i)`. -/
inductive ReadTree (ι σ O : Type) : Type where
  /-- Stop and output `o`. -/
  | leaf (o : O) : ReadTree ι σ O
  /-- Read the letter at index `i`, then continue with the subtree `k` of that letter. -/
  | node (i : ι) (k : σ → ReadTree ι σ O) : ReadTree ι σ O

namespace ReadTree

variable {ι σ O O' : Type}

/-- **Running the tree** on the input `x`: follow the letters read from the root to a leaf and
output the leaf's value. -/
def eval : ReadTree ι σ O → (ι → σ) → O
  | leaf o, _ => o
  | node i k, x => (k (x i)).eval x

@[simp] theorem eval_leaf (o : O) (x : ι → σ) : (leaf o : ReadTree ι σ O).eval x = o := rfl

@[simp] theorem eval_node (i : ι) (k : σ → ReadTree ι σ O) (x : ι → σ) :
    (node i k).eval x = (k (x i)).eval x := rfl

/-- **The depth**, by the recurrence: a leaf has depth `0`, and a node has depth one more than
the largest depth of its subtrees, the maximum taken over all letters `s : σ` (including letters
no input produces, and `0` when `σ` is empty). It bounds the number of reads on every run. -/
def depth [Fintype σ] : ReadTree ι σ O → ℕ
  | leaf _ => 0
  | node _ k => (Finset.univ.sup fun s => (k s).depth) + 1

@[simp] theorem depth_leaf [Fintype σ] (o : O) : (leaf o : ReadTree ι σ O).depth = 0 := rfl

@[simp] theorem depth_node [Fintype σ] (i : ι) (k : σ → ReadTree ι σ O) :
    (node i k).depth = (Finset.univ.sup fun s => (k s).depth) + 1 := rfl

/-- A node whose subtrees all have depth at most `T` has depth at most `T + 1`. -/
theorem depth_node_le [Fintype σ] {i : ι} {k : σ → ReadTree ι σ O} {T : ℕ}
    (hk : ∀ s, (k s).depth ≤ T) : (node i k).depth ≤ T + 1 := by
  sorry

/-- **Sequential composition**: run `t`, then the tree `f o` chosen by its output `o`. -/
def bind : ReadTree ι σ O → (O → ReadTree ι σ O') → ReadTree ι σ O'
  | leaf o, f => f o
  | node i k, f => node i fun s => (k s).bind f

/-- Running `t.bind f` runs `t`, then `f` of its output. -/
theorem eval_bind (t : ReadTree ι σ O) (f : O → ReadTree ι σ O') (x : ι → σ) :
    (t.bind f).eval x = (f (t.eval x)).eval x := by
  sorry

/-- Depths add under sequential composition: if `t` has depth at most `T₁` and every `f o` has
depth at most `T₂`, then `t.bind f` has depth at most `T₁ + T₂`. -/
theorem depth_bind_le [Fintype σ] {t : ReadTree ι σ O} {f : O → ReadTree ι σ O'} {T₁ T₂ : ℕ}
    (ht : t.depth ≤ T₁) (hf : ∀ o, (f o).depth ≤ T₂) : (t.bind f).depth ≤ T₁ + T₂ := by
  sorry

/-- **Non-adaptive reads**: read the letters at the `k` fixed addresses `addr 0, …, addr (k − 1)`
in order, then output `dec` of the `k` letters read. -/
def reads : (k : ℕ) → (Fin k → ι) → ((Fin k → σ) → O) → ReadTree ι σ O
  | 0, _, dec => leaf (dec Fin.elim0)
  | k + 1, addr, dec =>
      node (addr 0) fun s => reads k (fun j => addr j.succ) fun v => dec (Fin.cons s v)

/-- The non-adaptive tree outputs `dec` of the letters at its addresses. -/
theorem eval_reads (k : ℕ) (addr : Fin k → ι) (dec : (Fin k → σ) → O) (x : ι → σ) :
    (reads k addr dec).eval x = dec fun j => x (addr j) := by
  sorry

/-- The non-adaptive tree with `k` addresses has depth at most `k`. -/
theorem depth_reads_le [Fintype σ] (k : ℕ) (addr : Fin k → ι) (dec : (Fin k → σ) → O) :
    (reads k addr dec).depth ≤ k := by
  sorry

end ReadTree

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {ι' σ' O W : Type} [Fintype ι'] [DecidableEq ι'] [Fintype σ'] [DecidableEq σ']
  [Fintype W] [DecidableEq W]

/-- **A classical decision tree can be run with exactly `T` queries, for any `T` at least its
depth** (G1). Let `t` be a decision tree over inputs `ι → σ` with `t.depth ≤ T`, and output type
`O` nonempty (possibly infinite). For every promise `read : X → ι → σ`, some algorithm makes
exactly `T` swap queries and outputs `t.eval (read x)` with probability `1` on every promise
input `x`: the outcome law is the point mass at the tree's value. (Taking `read = id` gives one
algorithm for all inputs, which then serves every promise.) `[Nonempty O]` is needed: with
`σ` and `O` empty, the tree `node i Empty.elim` has depth `1`, but no algorithm has a readout
into an empty type. -/
theorem ReadTree.realizes {O : Type} [DecidableEq O] [Nonempty O] {X : Type} (read : X → ι → σ)
    (t : ReadTree ι σ O) {T : ℕ} (hT : t.depth ≤ T) :
    Realizes read T fun x o => if o = t.eval (read x) then (1 : ℝ) else 0 := by
  sorry

/-- **The derived input** read through the trees `t`: letter `j` is `(t j).eval x`. -/
def treeInput (t : ι' → ReadTree ι σ σ') (x : ι → σ) : ι' → σ' := fun j => (t j).eval x

/-- **Derived oracles** (G2). Let every letter of a derived input be computed by a decision tree
`t j` over `x` of depth at most `T`, with `0 < T` (needed for one `B` to serve every `q`: with
`T = 0` the derived input is constant and `B` would be observed at time `0` for every `q`).
Every algorithm `A` making swap queries to inputs `ι' → σ'` has a simulation `B` making swap
queries to inputs `ι → σ`, on a larger finite workspace and built from `A`, `t` and `T` alone
(before the input and the query count), such that for **every** query count `q`, every input
`x : ι → σ` and every relation `G` on outputs, `B` after `2Tq` queries to `x` succeeds with
exactly the probability that `A` succeeds after `q` queries to the derived input
`treeInput t x`. -/
theorem exists_treeSim {T : ℕ} (hT : 0 < T) (t : ι' → ReadTree ι σ σ')
    (ht : ∀ j, (t j).depth ≤ T) (A : QAlg ι' σ' O W) :
    ∃ (W' : Type) (_ : Fintype W') (_ : DecidableEq W') (B : QAlg ι σ O W'),
      ∀ (q : ℕ) (x : ι → σ) (G : O → Prop) [DecidablePred G],
        goodProb B.readout G (B.state x (2 * T * q)) =
          goodProb A.readout G (A.state (treeInput t x) q) := by
  sorry

/-- **Derived oracles, for outcome laws.** If the law `P` is realized with `q` queries to the
derived inputs `treeInput t (read x)` of a promise `read : X → ι → σ`, through trees of depth at
most `T` with `0 < T`, then `P` is realized with `2Tq` queries to the inputs `read x`
themselves. -/
theorem Realizes.treeSim [DecidableEq O] {X : Type} {T : ℕ} (hT : 0 < T)
    (t : ι' → ReadTree ι σ σ') (ht : ∀ j, (t j).depth ≤ T) {read : X → ι → σ} {q : ℕ}
    {P : X → O → ℝ} (h : Realizes (fun x => treeInput t (read x)) q P) :
    Realizes read (2 * T * q) P := by
  obtain ⟨V, _, _, A, hA⟩ := h
  obtain ⟨W', hW', hW'', B, hB⟩ := exists_treeSim hT t ht A
  refine ⟨W', hW', hW'', B, fun x o => ?_⟩
  rw [QAlg.prob, ← goodProb_eq, hB, goodProb_eq]
  exact hA x o

/-- **Non-adaptive derived oracles.** Let letter `j` of a derived input be `d j` of the letters
of `x` at the `k` fixed addresses `e j 0, …, e j (k − 1)`, with `0 < k`. Every algorithm `A`
making swap queries to inputs `ι' → σ'` has a simulation `B`, built from `A`, `e` and `d` alone,
such that for every query count `q`, every input `x : ι → σ` and every relation `G` on outputs,
`B` after `2kq` swap queries to `x` succeeds with exactly the probability that `A` succeeds
after `q` swap queries to `j ↦ d j (m ↦ x (e j m))`. -/
theorem exists_readsSim {k : ℕ} (hk : 0 < k) (e : ι' → Fin k → ι)
    (d : ι' → (Fin k → σ) → σ') (A : QAlg ι' σ' O W) :
    ∃ (W' : Type) (_ : Fintype W') (_ : DecidableEq W') (B : QAlg ι σ O W'),
      ∀ (q : ℕ) (x : ι → σ) (G : O → Prop) [DecidablePred G],
        goodProb B.readout G (B.state x (2 * k * q)) =
          goodProb A.readout G (A.state (fun j => d j fun m => x (e j m)) q) := by
  obtain ⟨W', hW', hW'', B, hB⟩ := exists_treeSim hk (fun j => ReadTree.reads k (e j) (d j))
    (fun j => ReadTree.depth_reads_le k (e j) (d j)) A
  refine ⟨W', hW', hW'', B, fun q x G _ => ?_⟩
  rw [hB q x G]
  congr 3
  funext j
  exact ReadTree.eval_reads k (e j) (d j) x

end QuantumQueryComplexity
