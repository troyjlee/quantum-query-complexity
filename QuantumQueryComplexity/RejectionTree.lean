import QuantumQueryComplexity.PredictionTree
import QuantumQueryComplexity.HasDual

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Bounded rejection draws as prediction trees

A **draw program** makes `D` draws; each draw examines up to `k` proposals in
turn and accepts the first one that is *live* for the current state.  Proposals
are entries of a virtual input `z : Fin D × Fin k → E` (one slot per proposal),
so the procedure is a decision tree over that table.  At every slot the label is
`none` (rejected) or `some e` (accepted), and the prediction is `none`: a
rejected proposal is forgotten and every rejection at a node has the same
continuation, so on **every** table the tree visits at most `D·k` slots and
receives at most `D` unpredicted answers (the prediction is `some none`: the
answer `none`, rejection, is the predicted one).  The layered prediction theorem then
gives a dual of cost `8·D·√k`, and shared composition with fixed-seed candidate
functions of dual cost `T` gives `8·T·D·√k` (`hasDual_run`).
-/

namespace QuantumQueryComplexity

/-! ## Scanning a row of proposals -/

/-- The first live entry of a row of proposals. -/
def firstLive {E : Type} (live : E → Bool) : {k : ℕ} → (Fin k → E) → Option E
  | 0, _ => none
  | _ + 1, row => if live (row 0) then some (row 0) else firstLive live (Fin.tail row)

@[simp] lemma firstLive_zero {E : Type} (live : E → Bool) (row : Fin 0 → E) :
    firstLive live row = none := rfl

lemma firstLive_cons {E : Type} (live : E → Bool) {k : ℕ} (e : E) (row : Fin k → E) :
    firstLive live (Fin.cons e row) = if live e then some e else firstLive live row := by
  simp [firstLive, Fin.tail_cons]

/-- Scanning a row from proposal `t` onwards. -/
def scanRow {E : Type} {k : ℕ} (live : E → Bool) (row : Fin k → E) (t : ℕ) : Option E :=
  if h : t < k then
    (if live (row ⟨t, h⟩) then some (row ⟨t, h⟩) else scanRow live row (t + 1))
  else none
termination_by k - t

lemma scanRow_of_le {E : Type} {k : ℕ} (live : E → Bool) (row : Fin k → E) {t : ℕ}
    (h : k ≤ t) : scanRow live row t = none := by
  rw [scanRow, dif_neg (by omega)]

lemma scanRow_cons_succ {E : Type} {k : ℕ} (live : E → Bool) (e : E) (row : Fin k → E)
    (t : ℕ) : scanRow live (Fin.cons e row) (t + 1) = scanRow live row t := by
  conv_lhs => rw [scanRow]
  conv_rhs => rw [scanRow]
  by_cases h : t < k
  · rw [dif_pos (by omega : t + 1 < k + 1), dif_pos h]
    have hc : (Fin.cons e row : Fin (k + 1) → E) ⟨t + 1, by omega⟩ = row ⟨t, h⟩ := rfl
    rw [hc]
    split_ifs
    · rfl
    · exact scanRow_cons_succ live e row (t + 1)
  · rw [dif_neg (by omega), dif_neg h]
termination_by k - t

lemma scanRow_zero {E : Type} (live : E → Bool) :
    ∀ {k : ℕ} (row : Fin k → E), scanRow live row 0 = firstLive live row
  | 0, row => by rw [scanRow, dif_neg (by omega)]; rfl
  | k + 1, row => by
    rw [scanRow, dif_pos (Nat.succ_pos k)]
    have h0 : (⟨0, Nat.succ_pos k⟩ : Fin (k + 1)) = 0 := rfl
    rw [h0, ← Fin.cons_self_tail row, firstLive_cons, Fin.cons_zero]
    split_ifs
    · rfl
    · rw [scanRow_cons_succ, scanRow_zero live (Fin.tail row)]

/-- A bounded rejection procedure: which proposals are live, and how an accepted
proposal updates the state.  Both may depend on the draw index. -/
structure DrawProgram (S E : Type) where
  /-- `live s d e`: proposal `e` is accepted at draw `d` in state `s`. -/
  live : S → ℕ → E → Bool
  /-- The state after accepting `e` at draw `d`. -/
  accept : S → ℕ → E → S

namespace DrawProgram

variable {S E : Type} (prog : DrawProgram S E) (D k : ℕ)

/-- The decision tree, by fuel: `d` is the current draw, `t` the current proposal.
The output is the final state and a success flag (`false` when some draw
rejected all its `k` proposals). -/
def tree : ℕ → S → ℕ → ℕ → PredTree (Fin D × Fin k) E (Option E) Unit (S × Bool)
  | 0, s, _, _ => PredTree.leaf (s, false)
  | fuel + 1, s, d, t =>
      if hd : d < D then
        if ht : t < k then
          PredTree.query (⟨d, hd⟩, ⟨t, ht⟩) (fun e => if prog.live s d e then some e else none)
            (some none) () (fun a => a.elim (tree fuel s d (t + 1))
              (fun e => tree fuel (prog.accept s d e) (d + 1) 0))
        else PredTree.leaf (s, false)
      else PredTree.leaf (s, true)

/-- The procedure from state `s₀`, with enough fuel for every path. -/
def run (s₀ : S) : PredTree (Fin D × Fin k) E (Option E) Unit (S × Bool) :=
  tree prog D k (D * k + 1) s₀ 0 0

variable {prog D k}

/-! ## Evaluation -/

lemma tree_zero (s : S) (d t : ℕ) : tree prog D k 0 s d t = PredTree.leaf (s, false) := rfl

lemma eval_tree_succ (fuel : ℕ) (s : S) (d t : ℕ) (z : Fin D × Fin k → E) :
    (tree prog D k (fuel + 1) s d t).eval z
      = if hd : d < D then
          if ht : t < k then
            (if prog.live s d (z (⟨d, hd⟩, ⟨t, ht⟩)) then
              (tree prog D k fuel (prog.accept s d (z (⟨d, hd⟩, ⟨t, ht⟩))) (d + 1) 0).eval z
            else (tree prog D k fuel s d (t + 1)).eval z)
          else (s, false)
        else (s, true) := by
  simp only [tree]
  split_ifs with hd ht hl
  · rw [PredTree.eval_query, if_pos hl]; rfl
  · rw [PredTree.eval_query, if_neg hl]; rfl
  · rfl
  · rfl

/-! ## Row-level semantics -/

variable (prog)

/-- The semantic twin of `tree`. -/
def scan (z : Fin D × Fin k → E) : ℕ → S → ℕ → ℕ → S × Bool
  | 0, s, _, _ => (s, false)
  | fuel + 1, s, d, t =>
      if hd : d < D then
        if ht : t < k then
          (if prog.live s d (z (⟨d, hd⟩, ⟨t, ht⟩)) then
            scan z fuel (prog.accept s d (z (⟨d, hd⟩, ⟨t, ht⟩))) (d + 1) 0
          else scan z fuel s d (t + 1))
        else (s, false)
      else (s, true)

lemma eval_tree_eq_scan (z : Fin D × Fin k → E) :
    ∀ (fuel : ℕ) (s : S) (d t : ℕ), (tree prog D k fuel s d t).eval z = scan prog z fuel s d t
  | 0, _, _, _ => rfl
  | fuel + 1, s, d, t => by
    rw [eval_tree_succ, scan]
    split_ifs with hd ht hl
    · exact eval_tree_eq_scan z fuel _ _ _
    · exact eval_tree_eq_scan z fuel _ _ _
    · rfl
    · rfl

/-- **The fold over rows**: from draw `d₀`, consume `m` rows of the table `rows`
(row `d` serves draw `d`); each draw accepts the first live proposal of its row. -/
def foldRows (rows : Fin D → Fin k → E) : ℕ → ℕ → S → S × Bool
  | _, 0, s => (s, true)
  | d₀, m + 1, s =>
      if h : d₀ < D then
        match firstLive (prog.live s d₀) (rows ⟨d₀, h⟩) with
        | none => (s, false)
        | some e => foldRows rows (d₀ + 1) m (prog.accept s d₀ e)
      else (s, true)

lemma foldRows_zero (rows : Fin D → Fin k → E) (d₀ : ℕ) (s : S) :
    foldRows prog rows d₀ 0 s = (s, true) := rfl

lemma foldRows_succ (rows : Fin D → Fin k → E) (d₀ m : ℕ) (s : S) :
    foldRows prog rows d₀ (m + 1) s
      = if h : d₀ < D then
          match firstLive (prog.live s d₀) (rows ⟨d₀, h⟩) with
          | none => (s, false)
          | some e => foldRows prog rows (d₀ + 1) m (prog.accept s d₀ e)
        else (s, true) := rfl

/-- **The scan from `(d, t)` is the row scan of draw `d` followed by the fold.** -/
theorem scan_eq_foldRows (z : Fin D × Fin k → E) :
    ∀ (fuel : ℕ) (s : S) (d t : ℕ), (D - d) * k - t + 1 ≤ fuel → t ≤ k →
      scan prog z fuel s d t
        = if hd : d < D then
            match scanRow (prog.live s d) (fun t' => z (⟨d, hd⟩, t')) t with
            | none => (s, false)
            | some e => foldRows prog (fun d' t' => z (d', t')) (d + 1) (D - (d + 1))
                (prog.accept s d e)
          else (s, true)
  | 0, _, _, _, hfuel, _ => by omega
  | fuel + 1, s, d, t, hfuel, htk => by
    rw [scan]
    by_cases hd : d < D
    · rw [dif_pos hd, dif_pos hd]
      have hk1 : k ≤ (D - d) * k := Nat.le_mul_of_pos_left k (by omega)
      have hsplit : (D - d) * k = (D - (d + 1)) * k + k := by
        rw [show D - d = D - (d + 1) + 1 by omega, add_mul, one_mul]
      obtain ⟨A, hA⟩ : ∃ A, (D - d) * k = A := ⟨_, rfl⟩
      obtain ⟨B, hB⟩ : ∃ B, (D - (d + 1)) * k = B := ⟨_, rfl⟩
      rw [hA] at hfuel hk1 hsplit
      rw [hB] at hsplit
      by_cases ht : t < k
      · rw [dif_pos ht, scanRow, dif_pos ht]
        by_cases hl : prog.live s d (z (⟨d, hd⟩, ⟨t, ht⟩)) = true
        · rw [if_pos hl, if_pos hl]
          rw [scan_eq_foldRows z fuel _ (d + 1) 0 (by rw [hB]; omega) (by omega)]
          show _ = foldRows prog (fun d' t' => z (d', t')) (d + 1) (D - (d + 1))
            (prog.accept s d (z (⟨d, hd⟩, ⟨t, ht⟩)))
          by_cases hd1 : d + 1 < D
          · rw [dif_pos hd1, show D - (d + 1) = (D - (d + 2)) + 1 by omega, foldRows_succ,
              dif_pos hd1, scanRow_zero]
          · rw [dif_neg hd1, show D - (d + 1) = 0 by omega, foldRows_zero]
        · rw [if_neg hl, if_neg hl]
          rw [scan_eq_foldRows z fuel s d (t + 1) (by rw [hA]; omega) (by omega), dif_pos hd]
      · rw [dif_neg ht, scanRow_of_le _ _ (by omega)]
    · rw [dif_neg hd, dif_neg hd]

/-- **The run is the fold over rows.** -/
theorem eval_run_eq_foldRows (s₀ : S) (z : Fin D × Fin k → E) :
    (run prog D k s₀).eval z = foldRows prog (fun d t => z (d, t)) 0 D s₀ := by
  rw [run, eval_tree_eq_scan, scan_eq_foldRows prog z _ s₀ 0 0 (by simp) (Nat.zero_le k)]
  rcases D with _ | D'
  · rw [dif_neg (by omega), foldRows_zero]
  · rw [dif_pos (Nat.succ_pos D'), foldRows_succ, dif_pos (Nat.succ_pos D'), scanRow_zero]
    rfl

variable {prog}

/-! ## Path bounds -/

variable [DecidableEq E]

/-- At most one visit per slot: `(D − d)·k − t` from `(d, t)`. -/
lemma visits_tree_le (fuel : ℕ) (s : S) (d t : ℕ) (z : Fin D × Fin k → E) :
    (tree prog D k fuel s d t).visits () z ≤ (D - d) * k - t := by
  induction fuel generalizing s d t with
  | zero => simp [tree, PredTree.visits]
  | succ fuel ih =>
    by_cases hd : d < D
    · by_cases ht : t < k
      · have hk1 : k ≤ (D - d) * k := Nat.le_mul_of_pos_left k (by omega)
        have hsplit : (D - d) * k = (D - (d + 1)) * k + k := by
          rw [show D - d = D - (d + 1) + 1 by omega, add_mul, one_mul]
        simp only [tree, dif_pos hd, dif_pos ht, PredTree.visits, if_true]
        by_cases hl : prog.live s d (z (⟨d, hd⟩, ⟨t, ht⟩)) = true
        · rw [if_pos hl]
          simp only [Option.elim]
          have := ih (prog.accept s d (z (⟨d, hd⟩, ⟨t, ht⟩))) (d + 1) 0
          omega
        · rw [if_neg hl]
          simp only [Option.elim]
          have := ih s d (t + 1)
          omega
      · simp [tree, dif_pos hd, dif_neg ht, PredTree.visits]
    · simp [tree, dif_neg hd, PredTree.visits]

/-- At most one unpredicted answer per draw: `D − d` from draw `d`. -/
lemma unpreds_tree_le (fuel : ℕ) (s : S) (d t : ℕ) (z : Fin D × Fin k → E) :
    (tree prog D k fuel s d t).unpreds () z ≤ D - d := by
  induction fuel generalizing s d t with
  | zero => simp [tree, PredTree.unpreds]
  | succ fuel ih =>
    by_cases hd : d < D
    · by_cases ht : t < k
      · simp only [tree, dif_pos hd, dif_pos ht, PredTree.unpreds]
        by_cases hl : prog.live s d (z (⟨d, hd⟩, ⟨t, ht⟩)) = true
        · rw [if_pos hl]
          simp only [Option.elim]
          have hu : PredTree.unpred (α := Option E) (some none) (some (z (⟨d, hd⟩, ⟨t, ht⟩)))
              = true := by simp [PredTree.unpred]
          rw [if_pos ⟨trivial, hu⟩]
          have := ih (prog.accept s d (z (⟨d, hd⟩, ⟨t, ht⟩))) (d + 1) 0
          omega
        · rw [if_neg hl]
          simp only [Option.elim]
          have hu : PredTree.unpred (α := Option E) (some none) none = false := by
            simp [PredTree.unpred]
          rw [if_neg (fun h => by rw [hu] at h; exact absurd h.2 (by decide))]
          have := ih s d (t + 1)
          omega
      · simp [tree, dif_pos hd, dif_neg ht, PredTree.unpreds]
    · simp [tree, dif_neg hd, PredTree.unpreds]

lemma visits_run_le (s₀ : S) (z : Fin D × Fin k → E) :
    (run prog D k s₀).visits () z ≤ D * k := by
  have := visits_tree_le (prog := prog) (D * k + 1) s₀ 0 0 z
  simpa [run] using this

lemma unpreds_run_le (s₀ : S) (z : Fin D × Fin k → E) :
    (run prog D k s₀).unpreds () z ≤ D := by
  have := unpreds_tree_le (prog := prog) (D * k + 1) s₀ 0 0 z
  simpa [run] using this

/-! ## The duals -/

variable [Fintype E]

/-- **The rejection tree has a dual of cost `8·D·√k`** on the virtual table. -/
theorem hasDual_run_eval [DecidableEq S] (hD : 1 ≤ D) (hk : 1 ≤ k) (s₀ : S) :
    HasDual (run prog D k s₀).eval (8 * (D : ℝ) * Real.sqrt k) := by
  have hDk : (0 : ℝ) < (D : ℝ) * k := by
    have : (1 : ℝ) ≤ D := by exact_mod_cast hD
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    positivity
  have h := PredTree.hasDual_eval_layered' (run prog D k s₀)
    (T := fun _ : Unit => (D : ℝ) * k) (G := fun _ : Unit => (D : ℝ))
    (fun _ => hDk) (fun _ => by exact_mod_cast hD)
    (fun z _ => by have := visits_run_le (prog := prog) s₀ z; exact_mod_cast this)
    (fun z _ => by have := unpreds_run_le (prog := prog) s₀ z; exact_mod_cast this)
  refine h.mono (le_of_eq ?_)
  rw [Fintype.sum_unique]
  have hD0 : (0 : ℝ) ≤ D := by positivity
  have hk0 : (0 : ℝ) ≤ k := by positivity
  rw [show (D : ℝ) * k * D = (D : ℝ) ^ 2 * k by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq hD0]
  ring

/-- **Fixed-seed candidates composed with the rejection tree** (`(R)` of the
plan): if every proposal slot is filled by a function of the input with a dual
of cost `T`, the whole procedure has a dual of cost `8·T·D·√k`. -/
theorem hasDual_run {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    [DecidableEq S]
    (hD : 1 ≤ D) (hk : 1 ≤ k) (s₀ : S) (g : Fin D × Fin k → (ι → σ) → E) {T : ℝ}
    (hT : 0 ≤ T) (hg : ∀ p, HasDual (g p) T) :
    HasDual (fun x : ι → σ => (run prog D k s₀).eval fun p => g p x)
      (8 * T * D * Real.sqrt k) := by
  have h := ((hasDual_run_eval (prog := prog) hD hk s₀).weighted_const hT).composeShared
    (fun _ => hT) hg
  refine h.mono (le_of_eq ?_)
  ring

end DrawProgram

end QuantumQueryComplexity
