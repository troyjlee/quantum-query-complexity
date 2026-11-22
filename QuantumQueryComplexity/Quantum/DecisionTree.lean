import QuantumQueryComplexity.Quantum.ProductRun
import QuantumQueryComplexity.Quantum.Relation
import QuantumQueryComplexity.Quantum.ReadGadget
import QuantumQueryComplexity.Quantum.Program
import QuantumQueryComplexity.Quantum.PostQuery

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
hypotheses: all three need `[Fintype X]` on the promise type, `Realizes.bind` also needs a finite
type for the outcome that selects the next stage, and `Realizes.map` a finite source type. A
stored list that selects a later stage should therefore be encoded in a finite type
(fixed-length tuples, a finite subtype), while a final stage may output an ordinary list; on an
infinite promise type, compose on the full input type `ι → σ` (`read = id`) and restrict.

**Derived oracles** (`exists_treeSim`). Suppose every letter `y j` of a derived input
`y : ι' → σ'` is computed by a decision tree of depth at most `T` over `x`:
`y = treeInput t x`, `y j = (t j).eval x`. Then every algorithm `A` making swap queries to `y`
has a simulation `B` making swap queries to `x`, fixed before `x` (and before the query count),
with `2T` queries to `x` per query to `y` and **the same success probability for every relation
on outputs**. Each simulated query reads the letters of `x` along the path of `t j` into scratch
registers (at most `T` adaptive reads, padded with idle queries to exactly `T`); the scratch holds
the letters returned by the physical queries, not `y j` itself. Following that transcript from the
root of `t j` reaches the leaf `y j`, which is swapped into `A`'s answer register by `A`'s swap
oracle; then the reads are uncomputed with `T` more queries. `0 < T` is needed
because `B` is the same for every query count: with `T = 0` the left side would not depend on
`q`. `Realizes.treeSim` is the same statement for outcome laws, and `exists_readsSim` is the
non-adaptive case (`k` fixed reads per letter, `2k` queries per query), the swap-oracle analogue
of `exists_wordSim` of the companion repository `quantum-query-problems`.

The trees branch on letters `σ`, not on `Option σ`: a read of `x i` into a blank answer register
always returns `some (x i)` (`oracleMap_blank`). The derived input is defined from the trees for
every `x`, so the statements hold for every input, valid or not.

## Proofs

`ReadTree.realizes` compiles the tree into an adaptive program of one-query reads
(`ReadTree.toProg`, `Prog` of `Program.lean`) and pads it to `T` queries. `exists_treeSim` builds
an adaptive version of the read gadget of `ReadGadget.lean`, in which the index read into each
scratch slot depends on the letters in the earlier slots (namespace `TreeSim`; see the section
note there).

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
    (hk : ∀ s, (k s).depth ≤ T) : (node i k).depth ≤ T + 1 :=
  Nat.add_le_add_right (Finset.sup_le fun s _ => hk s) 1

/-- **Sequential composition**: run `t`, then the tree `f o` chosen by its output `o`. -/
def bind : ReadTree ι σ O → (O → ReadTree ι σ O') → ReadTree ι σ O'
  | leaf o, f => f o
  | node i k, f => node i fun s => (k s).bind f

/-- Running `t.bind f` runs `t`, then `f` of its output. -/
theorem eval_bind (t : ReadTree ι σ O) (f : O → ReadTree ι σ O') (x : ι → σ) :
    (t.bind f).eval x = (f (t.eval x)).eval x := by
  induction t with
  | leaf o => rfl
  | node i k ih => exact ih (x i)

/-- Depths add under sequential composition: if `t` has depth at most `T₁` and every `f o` has
depth at most `T₂`, then `t.bind f` has depth at most `T₁ + T₂`. -/
theorem depth_bind_le [Fintype σ] {t : ReadTree ι σ O} {f : O → ReadTree ι σ O'} {T₁ T₂ : ℕ}
    (ht : t.depth ≤ T₁) (hf : ∀ o, (f o).depth ≤ T₂) : (t.bind f).depth ≤ T₁ + T₂ := by
  induction t generalizing T₁ with
  | leaf o => exact (hf o).trans (Nat.le_add_left _ _)
  | node i k ih =>
    rw [depth_node] at ht
    have hsub : ∀ s, ((k s).bind f).depth ≤ (Finset.univ.sup fun s => (k s).depth) + T₂ :=
      fun s => ih s (Finset.le_sup (f := fun v => (k v).depth) (Finset.mem_univ s))
    have hnode := depth_node_le (i := i) hsub
    change (node i fun s => (k s).bind f).depth ≤ _ at hnode ⊢
    omega

/-- **Non-adaptive reads**: read the letters at the `k` fixed addresses `addr 0, …, addr (k − 1)`
in order, then output `dec` of the `k` letters read. -/
def reads : (k : ℕ) → (Fin k → ι) → ((Fin k → σ) → O) → ReadTree ι σ O
  | 0, _, dec => leaf (dec Fin.elim0)
  | k + 1, addr, dec =>
      node (addr 0) fun s => reads k (fun j => addr j.succ) fun v => dec (Fin.cons s v)

/-- The non-adaptive tree outputs `dec` of the letters at its addresses. -/
theorem eval_reads (k : ℕ) (addr : Fin k → ι) (dec : (Fin k → σ) → O) (x : ι → σ) :
    (reads k addr dec).eval x = dec fun j => x (addr j) := by
  induction k with
  | zero => exact congrArg dec (Subsingleton.elim _ _)
  | succ k ih =>
    rw [reads, eval_node, ih]
    congr 1
    funext j
    exact Fin.cases rfl (fun _ => rfl) j

/-- The non-adaptive tree with `k` addresses has depth at most `k`. -/
theorem depth_reads_le [Fintype σ] (k : ℕ) (addr : Fin k → ι) (dec : (Fin k → σ) → O) :
    (reads k addr dec).depth ≤ k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [reads]
    exact depth_node_le fun _ => ih _ _

end ReadTree

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {ι' σ' O W : Type} [Fintype ι'] [DecidableEq ι'] [Fintype σ'] [DecidableEq σ']
  [Fintype W] [DecidableEq W]

namespace ReadTree

/-! ### Running a tree: the proof of `ReadTree.realizes`

A node is one call of `projAlg` (one query, answer `some (x i)` with probability one), so the
tree compiles to an adaptive program (`Prog`, `Program.lean`) of budget at most its depth.
Programs need a finite output type, so the outputs are encoded in the finite set of values the
tree takes, plus one default value; padding (`padAlg`) brings the count up to exactly `T`. -/

/-- The law of one read of the letter at `i`: the answer `some (x i)` with probability one. -/
noncomputable def readLaw (i : ι) (x : ι → σ) (a : Option σ) : ℝ :=
  if a = some (x i) then 1 else 0

/-- One read costs one query. -/
theorem realizes_readLaw (i : ι) : Realizes (id : (ι → σ) → ι → σ) 1 (readLaw i) := by
  refine ⟨Unit, inferInstance, inferInstance, projAlg σ i, fun x o => ?_⟩
  simp [QAlg.prob, projAlg, readLaw, oracleMat_mulVec_qBasis, eq_comm]

/-- The tree as an adaptive program, its outputs encoded by `encode` in `K`. A node calls one
read; the blank answer, which has probability zero, returns `fallback`. -/
noncomputable def toProg {K : Type} (fallback : K) (encode : O → K) :
    ReadTree ι σ O → Prog ι σ K
  | leaf o => .ret (encode o)
  | node i k => .call (Option σ) 1 (readLaw i) (realizes_readLaw i) fun
      | none => .ret fallback
      | some s => toProg fallback encode (k s)

theorem budget_toProg_le {K : Type} (fallback : K) (encode : O → K) (t : ReadTree ι σ O) :
    (toProg fallback encode t).budget ≤ t.depth := by
  induction t with
  | leaf o => exact Nat.zero_le _
  | node i k ih =>
    rw [toProg, Prog.budget_call, depth_node, Nat.add_comm 1]
    apply Nat.add_le_add_right
    refine Finset.sup_le fun a _ => ?_
    cases a with
    | none => exact Nat.zero_le _
    | some s => exact (ih s).trans (Finset.le_sup (f := fun z => (k z).depth) (Finset.mem_univ s))

theorem law_toProg {K : Type} [DecidableEq K] (fallback : K) (encode : O → K)
    (t : ReadTree ι σ O) (x : ι → σ) (u : K) :
    (toProg fallback encode t).law x u = if u = encode (t.eval x) then 1 else 0 := by
  induction t with
  | leaf o => rfl
  | node i k ih =>
    rw [toProg, Prog.law_call, eval_node, Fintype.sum_eq_single (some (x i)) fun a ha => by
      simp [readLaw, ha]]
    simp [readLaw, ih]

end ReadTree

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
  classical
  let d : O := Classical.choice inferInstance
  let S : Finset O := insert d (Finset.univ.image t.eval)
  let fallback : S := ⟨d, Finset.mem_insert_self _ _⟩
  let encode (o : O) : S := if h : o ∈ S then ⟨o, h⟩ else fallback
  have decode (x : ι → σ) : (encode (t.eval x) : O) = t.eval x := by
    have hx : t.eval x ∈ S :=
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ x))
    simp [encode, hx]
  let p := ReadTree.toProg fallback encode t
  have hO : Realizes (id : (ι → σ) → ι → σ) p.budget
      fun x o => if o = t.eval x then (1 : ℝ) else 0 := by
    refine ((p.realizes.congr (ReadTree.law_toProg fallback encode t)).map
      (fun z : S => (z : O))).congr fun x o => ?_
    simp [decode, eq_comm]
  obtain ⟨V, _, _, A, hA⟩ := hO
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le ((ReadTree.budget_toProg_le fallback encode t).trans hT)
  refine ⟨CtrlWork ι V, inferInstance, inferInstance, padAlg A p.budget n, fun x o => ?_⟩
  rw [hn, padAlg_prob]
  exact hA (read x) o

/-- **The derived input** read through the trees `t`: letter `j` is `(t j).eval x`. -/
def treeInput (t : ι' → ReadTree ι σ σ') (x : ι → σ) : ι' → σ' := fun j => (t j).eval x

namespace TreeSim

/-! ### Derived oracles: the proof of `exists_treeSim`

One query to the derived input `y = treeInput t x` is simulated by a reversible block of `2T`
queries to `x` (`blockPerm`, `implements_blockPerm`), on `T` scratch slots next to `A`'s
registers. A **gathering pass** (`gatherPerm`) fills the slots in order: before slot `j`, the
tree `t u` of the simulated query index `u` is followed along the letters in the slots before `j`
(`follow`), and the letter of `x` at the index of the node reached is read into slot `j`; nothing
is read once a leaf is reached, or when the simulated index is idle. So the slots hold the letters
returned by the physical queries (the transcript), not the derived letter. The routing of each
read depends only on the earlier slots, so it is a fixed involution and the pass is reversible:
this is the adaptive form of the read gadget (`ReadGadget.lean`). After `T` reads, following the
transcript from the root of `t u` reaches the leaf `y u` (`leafValue_followInput`, as the depth
is at most `T`), and a fixed permutation (`answerMap`) swaps that leaf value into `A`'s answer
register by `A`'s swap oracle. Then the gathering pass is undone. On the parked sector (scratch
blank, query registers of `x` idle and blank) the block acts as `A`'s oracle for `y`
(`blockPerm_mulVec_parkVec`).

The simulation runs `A`'s unitaries on the parked sector between blocks and merges the boundary
gates of the blocks into them (`clockStep`): a clock of period `2T`, so that one algorithm serves
every query count. -/

-- The decidable equality of the simulation's basis is a deep instance search.
set_option synthInstance.maxSize 100000

/-- A position in a tree: `some t'` for the subtree `t'` reached, `none` when there is nothing
to follow (the simulated query index is idle, or a blank letter was read at a node). -/
abbrev Cursor (ι σ σ' : Type) : Type := Option (ReadTree ι σ σ')

/-- Move along a read letter: at a node, take the subtree of the letter (`none` for a blank
letter); a leaf and the empty cursor stay put. -/
def advance : Cursor ι σ σ' → Option σ → Cursor ι σ σ'
  | some (.node _ k), v => v.map k
  | c, _ => c

/-- The index read next: the index of the node, `none` at a leaf or at the empty cursor. -/
def nextAddr : Cursor ι σ σ' → Option ι
  | some (.node i _) => some i
  | _ => none

/-- The value at a leaf, `none` elsewhere. -/
def leafValue : Cursor ι σ σ' → Option σ'
  | some (.leaf y) => some y
  | _ => none

/-- The cursor after following the first `n` letters of `tape` from `seed`. -/
def follow (seed : Cursor ι σ σ') (tape : ℕ → Option σ) : ℕ → Cursor ι σ σ'
  | 0 => seed
  | n + 1 => advance (follow seed tape n) (tape n)

/-- Following `n` letters reads only the first `n` letters of the tape. -/
theorem follow_congr (seed : Cursor ι σ σ') (u v : ℕ → Option σ) (n : ℕ)
    (h : ∀ m, m < n → u m = v m) : follow seed u n = follow seed v n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [follow, follow, ih fun m hm => h m (by omega), h n (by omega)]

/-- The cursor after `n` honest reads of the input `x` from `seed`. -/
def followInput (x : ι → σ) (seed : Cursor ι σ σ') : ℕ → Cursor ι σ σ'
  | 0 => seed
  | n + 1 => advance (followInput x seed n) ((nextAddr (followInput x seed n)).map x)

/-- The letter read at step `n` of the honest walk (blank when nothing is read). -/
def honestTape (x : ι → σ) (seed : Cursor ι σ σ') (n : ℕ) : Option σ :=
  (nextAddr (followInput x seed n)).map x

theorem follow_honestTape (x : ι → σ) (seed : Cursor ι σ σ') (n : ℕ) :
    follow seed (honestTape x seed) n = followInput x seed n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [follow, ih, honestTape, followInput]

theorem followInput_succ' (x : ι → σ) (seed : Cursor ι σ σ') (n : ℕ) :
    followInput x seed (n + 1) = followInput x (advance seed ((nextAddr seed).map x)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [followInput, ih, followInput]

theorem followInput_none (x : ι → σ) (n : ℕ) : followInput (σ' := σ') x none n = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [followInput, ih]; rfl

theorem followInput_leaf (x : ι → σ) (y : σ') (n : ℕ) :
    followInput x (some (.leaf y)) n = some (.leaf y) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [followInput, ih]; rfl

/-- **An honest walk of at least the depth reaches the tree's value.** -/
theorem leafValue_followInput (x : ι → σ) (t : ReadTree ι σ σ') (n : ℕ) (h : t.depth ≤ n) :
    leafValue (followInput x (some t) n) = some (t.eval x) := by
  induction n generalizing t with
  | zero =>
    cases t with
    | leaf y => rfl
    | node i k => simp at h
  | succ n ih =>
    cases t with
    | leaf y => rw [followInput_leaf]; rfl
    | node i k =>
      rw [followInput_succ']
      apply ih (k (x i))
      have hs := Finset.le_sup (f := fun v => (k v).depth) (Finset.mem_univ (x i))
      rw [ReadTree.depth_node] at h
      omega

/-- The scratch slots read as a tape, blank past the last slot. -/
def slotTape {T : ℕ} (s : ReadScratch σ T) (n : ℕ) : Option σ :=
  if h : n < T then s ⟨n, h⟩ else none

/-- The simulation's workspace: `T` scratch slots, then `A`'s basis. -/
abbrev SimWork (σ ι' σ' W : Type) (T : ℕ) : Type := ReadScratch σ T × QBasis ι' σ' W

variable (t : ι' → ReadTree ι σ σ') {T : ℕ}

/-- **Routing for slot `j`**: exchange the idle query index with the index that the tree of the
simulated index `u` reads after the letters in the slots before `j`, and the answer register
with slot `j`. -/
def route (j : Fin T) : QBasis ι σ (SimWork σ ι' σ' W T) → QBasis ι σ (SimWork σ ι' σ' W T)
  | (i, a, s, u, b, w) =>
    (Equiv.swap none (nextAddr (follow (u.map t) (slotTape s) j.val)) i, s j,
      Function.update s j a, u, b, w)

/-- Writing slot `j` does not change the walk along the slots before `j`. -/
theorem follow_update (seed : Cursor ι σ σ') (j : Fin T) (s : ReadScratch σ T) (a : Option σ) :
    follow seed (slotTape (Function.update s j a)) j.val = follow seed (slotTape s) j.val := by
  apply follow_congr
  intro m hm
  have h : m < T := lt_trans hm j.isLt
  have hn : (⟨m, h⟩ : Fin T) ≠ j := fun e => (Nat.ne_of_lt hm) (congrArg Fin.val e)
  simp [slotTape, h, Function.update_of_ne hn]

/-- The routing is an involution, since it does not change the slots before `j`. -/
theorem route_involutive (j : Fin T) : Function.Involutive (route (W := W) t j) := by
  rintro ⟨i, a, s, u, b, w⟩
  simp [route, follow_update, Function.update_idem]

/-- One read into slot `j`: route, query, route back. -/
def callPerm (x : ι → σ) (j : Fin T) : Equiv.Perm (QBasis ι σ (SimWork σ ι' σ' W T)) :=
  (((route_involutive t j).toPerm _).trans (oraclePerm x)).trans ((route_involutive t j).toPerm _)

/-- The basis state with the query registers idle and blank, scratch `s` and `A`'s basis state
`p`. -/
def parkedAt (s : ReadScratch σ T) (p : QBasis ι' σ' W) : QBasis ι σ (SimWork σ ι' σ' W T) :=
  (none, none, s, p)

/-- A read into a blank slot `j` writes there the letter at the index the walk reads next. -/
theorem callPerm_parkedAt (x : ι → σ) (j : Fin T) (s : ReadScratch σ T) (p : QBasis ι' σ' W)
    (h : s j = none) :
    callPerm t x j (parkedAt s p) =
      parkedAt (Function.update s j ((nextAddr (follow (p.1.map t) (slotTape s) j.val)).map x))
        p := by
  rcases p with ⟨u, b, w⟩
  change route t j (oracleMap x (route t j (parkedAt s (u, b, w)))) = _
  cases ha : nextAddr (follow (u.map t) (slotTape s) j.val) <;>
    simp [parkedAt, route, follow_update, ha, h, oracleMap, Function.update_idem]

/-- **The gathering pass**: reads into the slots `0, …, n − 1` in order. -/
def gatherPerm (x : ι → σ) : ℕ → Equiv.Perm (QBasis ι σ (SimWork σ ι' σ' W T))
  | 0 => Equiv.refl _
  | n + 1 => if h : n < T then (gatherPerm x n).trans (callPerm t x ⟨n, h⟩) else gatherPerm x n

/-- The letters of the first `n` honest reads, the other slots blank. -/
def snapshot (x : ι → σ) (seed : Cursor ι σ σ') (n : ℕ) : ReadScratch σ T :=
  fun j => if j.val < n then honestTape x seed j.val else none

theorem follow_snapshot (x : ι → σ) (seed : Cursor ι σ σ') (n : ℕ) (h : n ≤ T) :
    follow seed (slotTape (snapshot (T := T) x seed n)) n = followInput x seed n := by
  rw [← follow_honestTape]
  apply follow_congr
  intro m hm
  simp [slotTape, snapshot, hm, lt_of_lt_of_le hm h]

/-- On a parked basis state the gathering pass writes the honest reads of the simulated
index's tree. -/
theorem gatherPerm_parkedAt (x : ι → σ) (p : QBasis ι' σ' W) (n : ℕ) (h : n ≤ T) :
    gatherPerm (T := T) t x n (parkedAt blankScratch p) =
      parkedAt (snapshot x (p.1.map t) n) p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : n < T := h
    let j : Fin T := ⟨n, hn⟩
    have blank : snapshot x (p.1.map t) n j = none := by simp [snapshot, j]
    rw [gatherPerm, dite_eq_left hn, Equiv.trans_apply, ih hn.le, callPerm_parkedAt _ _ j _ _ blank,
      follow_snapshot x _ n hn.le]
    congr 1
    funext i
    by_cases hi : i = j
    · subst i
      simp [snapshot, j, honestTape]
    · have hne : i.val ≠ n := fun e => hi (Fin.ext e)
      simp [Function.update_of_ne hi, snapshot, show (i.val < n + 1) ↔ i.val < n by omega]

/-- **The answer gate**: `A`'s swap oracle on `A`'s answer register, with the letter at the leaf
that the walk along all `T` slots reaches (no change when there is none). -/
def answerMap : QBasis ι σ (SimWork σ ι' σ' W T) → QBasis ι σ (SimWork σ ι' σ' W T)
  | (i, a, s, u, b, w) =>
    (i, a, s, u, Equiv.swap none (leafValue (follow (u.map t) (slotTape s) T)) b, w)

theorem answerMap_involutive : Function.Involutive (answerMap (W := W) (T := T) t) := by
  rintro ⟨i, a, s, u, b, w⟩
  simp [answerMap]

/-- After the gathering pass, the answer gate is `A`'s oracle for the derived input. -/
theorem answerMap_snapshot (ht : ∀ j, (t j).depth ≤ T) (x : ι → σ) (p : QBasis ι' σ' W) :
    answerMap t (parkedAt (T := T) (snapshot x (p.1.map t) T) p) =
      parkedAt (snapshot x ((oracleMap (treeInput t x) p).1.map t) T)
        (oracleMap (treeInput t x) p) := by
  rcases p with ⟨_ | u, b, w⟩
  · simp [answerMap, parkedAt, follow_snapshot x _ T le_rfl, followInput_none, leafValue,
      oracleMap]
  · simp [answerMap, parkedAt, follow_snapshot x _ T le_rfl, leafValue_followInput x _ T (ht u),
      oracleMap, treeInput]

/-- **The simulated query**: gather, answer, ungather. -/
def blockPerm (x : ι → σ) : Equiv.Perm (QBasis ι σ (SimWork σ ι' σ' W T)) :=
  ((gatherPerm t x T).trans ((answerMap_involutive t).toPerm _)).trans (gatherPerm t x T).symm

/-- On the parked basis states the block is `A`'s oracle for the derived input, on every basis
state of `A`. -/
theorem blockPerm_parkedAt (ht : ∀ j, (t j).depth ≤ T) (x : ι → σ) (p : QBasis ι' σ' W) :
    blockPerm (T := T) t x (parkedAt blankScratch p) =
      parkedAt blankScratch (oracleMap (treeInput t x) p) := by
  rw [blockPerm, Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_eq,
    gatherPerm_parkedAt _ _ _ T le_rfl, gatherPerm_parkedAt _ _ _ T le_rfl,
    Function.Involutive.coe_toPerm, answerMap_snapshot _ ht]

/-- Composing permutations multiplies their matrices in the opposite order. -/
theorem qPerm_trans {H : Type} [Fintype H] [DecidableEq H] (p q : Equiv.Perm H) :
    qPerm (p.trans q) = qPerm q * qPerm p :=
  qPerm_mul q p

/-- `R` makes `n` queries, its first gate is a permutation, and it runs as the permutation
`f x` on every input `x`. -/
def Implements (n : ℕ) (f : (ι → σ) → Equiv.Perm (QBasis ι σ (SimWork σ ι' σ' W T))) : Prop :=
  ∃ (R : QRoutine ι σ (SimWork σ ι' σ' W T)) (p : Equiv.Perm (QBasis ι σ (SimWork σ ι' σ' W T))),
    R.len = n ∧ R.step 0 = qPerm p ∧ ∀ x, R.run x = qPerm (f x)

theorem implements_free (p : Equiv.Perm (QBasis ι σ (SimWork σ ι' σ' W T))) :
    Implements 0 fun _ => p :=
  ⟨QRoutine.ofUnitary _ (qPerm_mem_unitaryGroup p), p, rfl, rfl, fun _ => rfl⟩

theorem implements_trans {m n : ℕ}
    {f g : (ι → σ) → Equiv.Perm (QBasis ι σ (SimWork σ ι' σ' W T))}
    (hf : Implements m f) (hg : Implements n g) :
    Implements (m + n) fun x => (f x).trans (g x) := by
  obtain ⟨R, p, hlen, hp, hR⟩ := hf
  obtain ⟨V, s, vlen, hs, hV⟩ := hg
  have h0 : ∃ u, (R.comp V).step 0 = qPerm u := by
    rcases Nat.eq_zero_or_pos R.len with h | h
    · refine ⟨p.trans s, ?_⟩
      have := QRoutine.comp_step_self R V
      rw [h, hp, hs] at this
      rw [this, qPerm_trans]
    · exact ⟨p, (QRoutine.comp_step_of_lt R V h).trans hp⟩
  obtain ⟨u, hu⟩ := h0
  exact ⟨R.comp V, u, by simp [hlen, vlen], hu, fun x => by
    rw [QRoutine.comp_run, hR, hV, qPerm_trans]⟩

theorem implements_callPerm (j : Fin T) : Implements (W := W) 1 fun x => callPerm t x j := by
  let g := (route_involutive (W := W) t j).toPerm _
  let R : QRoutine ι σ (SimWork σ ι' σ' W T) :=
    ⟨1, fun _ => qPerm g, fun _ => qPerm_mem_unitaryGroup _⟩
  refine ⟨R, g, rfl, rfl, fun x => ?_⟩
  change qPerm g * (qPerm (oraclePerm x) * qPerm g) = qPerm ((g.trans (oraclePerm x)).trans g)
  rw [qPerm_trans, qPerm_trans]

theorem implements_gatherPerm (m : ℕ) (h : m ≤ T) :
    Implements (W := W) (T := T) m (fun x => gatherPerm t x m) ∧
      Implements (W := W) (T := T) m (fun x => (gatherPerm t x m).symm) := by
  induction m with
  | zero => exact ⟨implements_free (Equiv.refl _), implements_free (Equiv.refl _)⟩
  | succ m ih =>
    have hj : m < T := h
    obtain ⟨f, b⟩ := ih hj.le
    have s := implements_callPerm (W := W) t ⟨m, hj⟩
    constructor
    · simpa only [gatherPerm, dite_eq_left hj] using implements_trans f s
    · have heq : (fun x => (gatherPerm (W := W) t x (m + 1)).symm) =
          fun x => (callPerm t x ⟨m, hj⟩).trans (gatherPerm t x m).symm := by
        funext x
        rw [gatherPerm, dite_eq_left hj]
        exact Equiv.ext fun _ => rfl
      rw [heq, Nat.add_comm m 1]
      exact implements_trans s b

/-- **The simulated query costs `2T` queries.** -/
theorem implements_blockPerm : Implements (W := W) (T := T) (2 * T) fun x => blockPerm t x := by
  obtain ⟨f, b⟩ := implements_gatherPerm (W := W) t T le_rfl
  simpa only [Nat.add_zero, two_mul, blockPerm] using
    implements_trans (implements_trans f (implements_free ((answerMap_involutive t).toPerm _))) b

/-- `A`'s vector `ψ`, parked: scratch blank, query registers of `x` idle and blank. -/
def parkVec (ψ : QBasis ι' σ' W → ℂ) : QBasis ι σ (SimWork σ ι' σ' W T) → ℂ :=
  ∑ p, ψ p • qBasis (parkedAt blankScratch p)

/-- **On the parked sector the block is `A`'s oracle for the derived input.** -/
theorem blockPerm_mulVec_parkVec (ht : ∀ j, (t j).depth ≤ T) (x : ι → σ)
    (ψ : QBasis ι' σ' W → ℂ) :
    qPerm (blockPerm t x) *ᵥ parkVec (ι := ι) (σ := σ) (T := T) ψ =
      parkVec (oracleMat (treeInput t x) *ᵥ ψ) := by
  simp only [parkVec, Matrix.mulVec_sum, Matrix.mulVec_smul, qPerm_mulVec_qBasis,
    blockPerm_parkedAt t ht, oracleMat_mulVec_apply]
  let u := oraclePerm (W := W) (treeInput t x)
  have inv (p : QBasis ι' σ' W) : u (u p) = p := oracleMap_involutive _ p
  have e := Equiv.sum_comp u fun p =>
    ψ (u p) • qBasis (parkedAt (ι := ι) (T := T) (blankScratch (σ := σ)) p)
  simp only [inv] at e
  exact e

/-- The simulation's basis split into `A`'s basis and the rest. -/
def splitEquiv :
    QBasis ι σ (SimWork σ ι' σ' W T) ≃ QBasis ι' σ' W × (Option ι × Option σ × ReadScratch σ T)
    where
  toFun p := (p.2.2.2, p.1, p.2.1, p.2.2.1)
  invFun q := (q.2.1, q.2.2.1, q.2.2.2, q.1)
  left_inv _ := rfl
  right_inv _ := rfl

theorem parkVec_eq_splitVec (ψ : QBasis ι' σ' W → ℂ) :
    parkVec (ι := ι) (σ := σ) (T := T) ψ =
      splitVec splitEquiv ψ (qBasis ((none, none, blankScratch) : Option ι × Option σ × _)) := by
  rw [splitVec_qBasis_eq_sum]
  rfl

/-- `A`'s unitaries, lifted, act on parked vectors as on `A`'s vectors. -/
theorem kronLift_mulVec_parkVec (U : Matrix (QBasis ι' σ' W) (QBasis ι' σ' W) ℂ)
    (ψ : QBasis ι' σ' W → ℂ) :
    kronLift (splitEquiv (ι := ι) (σ := σ) (T := T)) U *ᵥ parkVec ψ = parkVec (U *ᵥ ψ) := by
  simp only [parkVec_eq_splitVec, kronLift_mulVec_splitVec]

/-- Measuring `qPerm p` of a parked vector with `A`'s readout after undoing `p` gives `A`'s
success probability. -/
theorem goodProb_qPerm_parkVec {O : Type} (p : Equiv.Perm (QBasis ι σ (SimWork σ ι' σ' W T)))
    (r : QBasis ι' σ' W → O) (G : O → Prop) [DecidablePred G] (ψ : QBasis ι' σ' W → ℂ) :
    goodProb (fun b => r (p.symm b).2.2.2) G (qPerm p *ᵥ parkVec ψ) = goodProb r G ψ := by
  let f := fun z : QBasis ι' σ' W => p (parkedAt blankScratch z)
  have inj : Function.Injective f := fun _ _ h => congrArg (fun v => v.2.2.2) (p.injective h)
  simp only [parkVec, Matrix.mulVec_sum, Matrix.mulVec_smul, qPerm_mulVec_qBasis]
  rw [goodProb, qProb_sum_smul_qBasis _ f inj, goodProb_eq_sum_ite]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [f, parkedAt]

/-- **The clock**: `R` once per period, `U n` merged into its boundary gate at the start of
period `n`. -/
def clockStep (R : QRoutine ι σ (SimWork σ ι' σ' W T))
    (U : ℕ → Matrix (QBasis ι σ (SimWork σ ι' σ' W T)) (QBasis ι σ (SimWork σ ι' σ' W T)) ℂ)
    (n : ℕ) : Matrix (QBasis ι σ (SimWork σ ι' σ' W T)) (QBasis ι σ (SimWork σ ι' σ' W T)) ℂ :=
  if n = 0 then R.step 0 * U 0
  else if n % R.len = 0 then R.step 0 * (U (n / R.len) * R.step R.len)
  else R.step (n % R.len)

theorem clockStep_mem_unitaryGroup (R : QRoutine ι σ (SimWork σ ι' σ' W T))
    {U : ℕ → Matrix (QBasis ι σ (SimWork σ ι' σ' W T)) (QBasis ι σ (SimWork σ ι' σ' W T)) ℂ}
    (h : ∀ n, U n ∈ Matrix.unitaryGroup (QBasis ι σ (SimWork σ ι' σ' W T)) ℂ) (n : ℕ) :
    clockStep R U n ∈ Matrix.unitaryGroup (QBasis ι σ (SimWork σ ι' σ' W T)) ℂ := by
  unfold clockStep
  split_ifs
  · exact mul_mem (R.step_unitary _) (h _)
  · exact mul_mem (R.step_unitary _) (mul_mem (h _) (R.step_unitary _))
  · exact R.step_unitary _

end TreeSim

set_option synthInstance.maxSize 100000 in
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
  open TreeSim in
  obtain ⟨R, p, hlen, hp, hR⟩ := implements_blockPerm (W := W) (T := T) t
  have hL : 0 < R.len := by omega
  let U := fun n => kronLift (splitEquiv (ι := ι) (σ := σ) (T := T)) (A.step n)
  let B : QAlg ι σ O (SimWork σ ι' σ' W T) :=
    { init := parkVec A.init
      init_isQState := by
        change qNormSq _ = 1
        rw [parkVec_eq_splitVec, qNormSq_splitVec, qNormSq_qBasis,
          show qNormSq A.init = 1 from A.init_isQState, mul_one]
      step := clockStep R U
      step_unitary := clockStep_mem_unitaryGroup R fun n =>
        kronLift_mem_unitaryGroup _ (A.step_unitary n)
      readout := fun b => A.readout (p.symm b).2.2.2 }
  refine ⟨_, inferInstance, inferInstance, B, fun q x G _ => ?_⟩
  -- Inside period `q`, `B` runs `R` on a vector that starts as `R.step 0` of a parked one.
  have interior (q : ℕ) (ψ : QBasis ι' σ' W → ℂ)
      (start : B.state x (R.len * q) = R.step 0 *ᵥ parkVec ψ) :
      ∀ n, n < R.len → B.state x (R.len * q + n) = R.runUpto x n *ᵥ parkVec ψ := by
    intro n
    induction n with
    | zero => intro _; exact start
    | succ n ih =>
      intro hn
      have hm : (R.len * q + (n + 1)) % R.len = n + 1 := by simp [Nat.mod_eq_of_lt hn]
      have gate_eq : B.step (R.len * q + (n + 1)) = R.step (n + 1) := by
        simp [B, clockStep, hm]
      change B.step (R.len * q + (n + 1)) *ᵥ (oracleMat x *ᵥ B.state x (R.len * q + n)) = _
      rw [gate_eq, ih (by omega), QRoutine.runUpto_succ, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec]
  -- At the start of period `q`, `B` holds `A`'s state after `q` queries to the derived input.
  have boundary (q : ℕ) :
      B.state x (R.len * q) = R.step 0 *ᵥ parkVec (A.state (treeInput t x) q) := by
    induction q with
    | zero =>
      simp only [Nat.mul_zero, QAlg.state_zero, B, clockStep, ite_true, ← Matrix.mulVec_mulVec,
        U, kronLift_mulVec_parkVec]
    | succ q ih =>
      let n := R.len - 1
      have hn : R.len = n + 1 := by omega
      have last := interior q _ ih n (by omega)
      have gate_eq : B.step (R.len * (q + 1)) = R.step 0 * (U (q + 1) * R.step R.len) := by
        simp [B, clockStep, hL.ne', Nat.mul_div_cancel_left _ hL]
      have htime : R.len * (q + 1) = R.len * q + n + 1 := by rw [Nat.mul_succ]; omega
      have finish : R.step R.len * (oracleMat x * R.runUpto x n) = qPerm (blockPerm t x) := by
        convert hR x using 1
        rw [QRoutine.run, hn, QRoutine.runUpto_succ]
      have effect (ψ : QBasis ι' σ' W → ℂ) :
          R.step R.len *ᵥ (oracleMat x *ᵥ (R.runUpto x n *ᵥ parkVec ψ)) =
            parkVec (oracleMat (treeInput t x) *ᵥ ψ) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, finish,
          blockPerm_mulVec_parkVec t ht]
      rw [htime, QAlg.state_succ, ← htime, gate_eq, last]
      simp only [← Matrix.mulVec_mulVec, effect, U, kronLift_mulVec_parkVec, QAlg.state_succ]
  rw [← hlen, boundary, hp]
  exact goodProb_qPerm_parkVec p A.readout G _

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
