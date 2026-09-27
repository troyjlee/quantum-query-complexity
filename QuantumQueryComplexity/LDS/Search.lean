import QuantumQueryComplexity.LDS.Window
import QuantumQueryComplexity.BinarySearch
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The anchor `Λ` as a descriptor chain

`Λ_a(j)` — the leftmost start `i ≥ a` with `[i, j]` distinct — is the
threshold of a monotone predicate: `[i, j]` distinct is *increasing* in `i`,
and `Λ_a(j) ≤ i` exactly when `[i, j]` is distinct.  So the abstract binary
search of `QuantumQueryComplexity/BinarySearch.lean` applies verbatim, with the threshold
tests supplied by the windowed distinctness duals of `LDS/Window.lean`:

  **`hasDualOn_lambdaOffset`** — `Λ_a(j)` has a dual solution of cost
  `⌈log₂ s⌉ · 8 s^{2/3}` on any promise, where `s = j - a + 1`.

This is the dual-side form of the paper's Fact 36 (noisy binary search over
Ambainis' element distinctness), with no error bookkeeping: the descriptor
chain is exact.  The glued-arena variant that the node recursion needs
 is the same argument with the window replaced by an arena; the
search half will not change.

Test positions are clamped into `Fin n` (`startAt`): past the right end of
the window the test window is degenerate, hence distinct, which is exactly
what the threshold predicate says there, so clamping is sound rather than a
special case.
-/

namespace QuantumQueryComplexity

variable {n : ℕ} {σ : Type} [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X] [DecidableEq X]

/-- The test position `a + q`, clamped into `Fin n`. -/
def startAt (a : Fin n) (q : ℕ) : Fin n :=
  ⟨min ((a : ℕ) + q) (n - 1), by
    have := a.isLt
    omega⟩

lemma le_startAt (a : Fin n) (q : ℕ) : a ≤ startAt a q := by
  have := a.isLt
  simp only [startAt, Fin.le_def]
  omega

lemma startAt_le (a : Fin n) (q : ℕ) : (startAt a q : ℕ) ≤ (a : ℕ) + q := by
  simp only [startAt]
  omega

/-- **The threshold characterization of `Λ`**: the window starting at the
clamped position `a + q` is distinct exactly when `Λ_a(j) - a ≤ q`. -/
lemma isDistinct_startAt_iff (α : Fin n → σ) {a j : Fin n} (haj : a ≤ j)
    (q : ℕ) :
    IsDistinct α (startAt a q) j ↔ (lambdaFun α a j : ℕ) - (a : ℕ) ≤ q := by
  have hla : a ≤ lambdaFun α a j := le_lambdaFun haj
  have hlj : lambdaFun α a j ≤ j := lambdaFun_le haj
  have hstart := le_startAt a q
  have hsval : (startAt a q : ℕ) = min ((a : ℕ) + q) (n - 1) := rfl
  have hjn : (j : ℕ) < n := j.isLt
  rw [Fin.le_def] at hla hlj haj hstart
  constructor
  · intro h
    have hle : (lambdaFun α a j : ℕ) ≤ (startAt a q : ℕ) := by
      rcases le_or_gt (startAt a q) j with hsj | hsj
      · have := lambdaFun_le_of_isDistinct (le_startAt a q) hsj h
        rw [Fin.le_def] at this
        exact this
      · rw [Fin.lt_def] at hsj
        omega
    omega
  · intro h
    have hle : lambdaFun α a j ≤ startAt a q := by
      rw [Fin.le_def]
      omega
    exact (isDistinct_lambdaFun haj).mono hle le_rfl

/-- Every test window is contained in `[a, j]`, so its distinctness dual is at
most as expensive. -/
private lemma winLen_startAt_le (a j : Fin n) (q : ℕ) :
    winLen (startAt a q) j ≤ winLen a j := by
  have := le_startAt a q
  rw [Fin.le_def] at this
  simp only [winLen]
  omega

/-- **The anchor dual**: on any promise, the offset
`Λ_a(j) - a` has a feasible dual solution of cost `L · 8 s^{2/3}`, where
`s = j - a + 1` is the window length and `s ≤ 2 ^ L`. -/
theorem hasDualOn_lambdaOffset (read : X → Fin n → σ) {a j : Fin n}
    (haj : a ≤ j) {L : ℕ} (hL : winLen a j ≤ 2 ^ L) :
    HasDualOn read (fun x => (lambdaFun (read x) a j : ℕ) - (a : ℕ))
      ((L : ℝ) * (8 * (winLen a j : ℝ) ^ ((2 : ℝ) / 3))) := by
  classical
  -- the answer fits in `L` bits
  have hans : ∀ x, (lambdaFun (read x) a j : ℕ) - (a : ℕ) < 2 ^ L := by
    intro x
    have hlj := lambdaFun_le (α := read x) haj
    have hla := le_lambdaFun (α := read x) haj
    rw [Fin.le_def] at hlj hla
    have hw : winLen a j = (j : ℕ) + 1 - (a : ℕ) := rfl
    omega
  -- each threshold test is a windowed distinctness test
  have hcost : ∀ q : ℕ,
      HasDualOn read (fun x => decide (IsDistinct (read x) (startAt a q) j))
        (8 * (winLen a j : ℝ) ^ ((2 : ℝ) / 3)) := by
    intro q
    refine ((hasDual_isDistinct (σ := σ) (startAt a q) j).restrictToOn read).mono ?_
    have hmono : ((winLen (startAt a q) j : ℕ) : ℝ) ^ ((2 : ℝ) / 3)
        ≤ ((winLen a j : ℕ) : ℝ) ^ ((2 : ℝ) / 3) := by
      refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ (by norm_num)
      exact_mod_cast winLen_startAt_le a j q
    linarith
  refine hasDualOn_thresholdSearch hans ?_ hcost
  intro q x
  exact decide_eq_decide.mpr (isDistinct_startAt_iff (read x) haj q)

/-- The same bound for the anchor itself: recoding `Λ_a(j) - a` to `Λ_a(j)`
is free, the two having the same level sets on the promise. -/
theorem hasDualOn_lambdaFun (read : X → Fin n → σ) {a j : Fin n}
    (haj : a ≤ j) {L : ℕ} (hL : winLen a j ≤ 2 ^ L) :
    HasDualOn read (fun x => lambdaFun (read x) a j)
      ((L : ℝ) * (8 * (winLen a j : ℝ) ^ ((2 : ℝ) / 3))) := by
  refine (hasDualOn_lambdaOffset read haj hL).ofKer fun x y => ?_
  have hx := le_lambdaFun (α := read x) haj
  have hy := le_lambdaFun (α := read y) haj
  rw [Fin.le_def] at hx hy
  constructor
  · intro h
    exact Fin.ext (by omega)
  · intro h
    rw [h]

end QuantumQueryComplexity
