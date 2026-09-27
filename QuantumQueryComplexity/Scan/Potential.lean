import QuantumQueryComplexity.Scan.Bounded

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Potential functions bound the change count of a scan

A scan whose trajectory carries a natural-number potential that never increases,
and strictly decreases at every state change, changes at most
`φ(q₀) − φ(final)` times (`changeCount_le_of_potential`).  The changed steps
inject into the interval of potential values through `i ↦ φ(state after i)`.
-/

namespace QuantumQueryComplexity

variable {n : ℕ} {σ : Type} [Fintype σ] [DecidableEq σ]
variable {Q : Type} [Fintype Q] [DecidableEq Q]
variable (q₀ : Q) (δ : Fin n → Q → σ → Q)

/-- Past the end of the word the state is frozen. -/
lemma scanState_succ_of_not_lt (x : Fin n → σ) {t : ℕ} (h : ¬ t < n) :
    scanState q₀ δ x (t + 1) = scanState q₀ δ x t := by
  rw [scanState, dif_neg h]

/-- A step-wise non-increasing potential is antitone along the trajectory. -/
lemma potential_antitone (x : Fin n → σ) (φ : Q → ℕ)
    (hmono : ∀ i : Fin n, φ (scanState q₀ δ x ((i : ℕ) + 1)) ≤ φ (scanState q₀ δ x i)) :
    ∀ s t, s ≤ t → φ (scanState q₀ δ x t) ≤ φ (scanState q₀ δ x s) := by
  intro s t hst
  induction t with
  | zero => rw [Nat.le_zero.1 hst]
  | succ t ih =>
      rcases Nat.eq_or_lt_of_le hst with h | h
      · rw [h]
      · refine le_trans ?_ (ih (by omega))
        by_cases ht : t < n
        · exact hmono ⟨t, ht⟩
        · rw [scanState_succ_of_not_lt q₀ δ x ht]

/-- **A decreasing potential bounds the change count.** -/
theorem changeCount_le_of_potential (x : Fin n → σ) (φ : Q → ℕ)
    (hmono : ∀ i : Fin n, φ (scanState q₀ δ x ((i : ℕ) + 1)) ≤ φ (scanState q₀ δ x i))
    (hstrict : ∀ i : Fin n, scanState q₀ δ x ((i : ℕ) + 1) ≠ scanState q₀ δ x i →
      φ (scanState q₀ δ x ((i : ℕ) + 1)) < φ (scanState q₀ δ x i)) :
    changeCount q₀ δ x ≤ φ q₀ - φ (scanState q₀ δ x n) := by
  classical
  have hanti := potential_antitone q₀ δ x φ hmono
  have hcol : ∀ i : Fin n, scanCol q₀ δ x i = true ↔
      scanState q₀ δ x ((i : ℕ) + 1) ≠ scanState q₀ δ x i := fun i => by
    simp [scanCol]
  have hmaps : Set.MapsTo (fun i : Fin n => φ (scanState q₀ δ x ((i : ℕ) + 1)))
      ↑(Finset.univ.filter fun i => scanCol q₀ δ x i = true)
      ↑(Finset.Ico (φ (scanState q₀ δ x n)) (φ q₀)) := by
    intro i hi
    rw [Finset.mem_coe, Finset.mem_filter] at hi
    have h1 := hstrict i ((hcol i).1 hi.2)
    have h2 := hanti 0 i (Nat.zero_le _)
    have h3 := hanti ((i : ℕ) + 1) n i.isLt
    rw [scanState_zero] at h2
    rw [Finset.mem_coe, Finset.mem_Ico]
    dsimp only
    exact ⟨h3, by omega⟩
  have hinj : Set.InjOn (fun i : Fin n => φ (scanState q₀ δ x ((i : ℕ) + 1)))
      ↑(Finset.univ.filter fun i => scanCol q₀ δ x i = true) := by
    intro i hi j hj hij
    rw [Finset.mem_coe, Finset.mem_filter] at hi hj
    dsimp only at hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := hanti ((i : ℕ) + 1) j (Nat.succ_le_of_lt (Fin.lt_def.mp hlt))
      have h2 := hstrict j ((hcol j).1 hj.2)
      omega
    · have h1 := hanti ((j : ℕ) + 1) i (Nat.succ_le_of_lt (Fin.lt_def.mp hlt))
      have h2 := hstrict i ((hcol i).1 hi.2)
      omega
  calc changeCount q₀ δ x
      ≤ (Finset.Ico (φ (scanState q₀ δ x n)) (φ q₀)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = φ q₀ - φ (scanState q₀ δ x n) := Nat.card_Ico _ _

end QuantumQueryComplexity
