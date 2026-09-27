import QuantumQueryComplexity.Quantum.PredictionTreeCompose
import QuantumQueryComplexity.RejectionTree

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Acceptance: compositional Beigi–Taghavi

Statement pins and scope checks for the prediction-tree composition
theorems.  Like the other pins, this file exists to be broken: a refactor
that changes a public statement fails here.

Pinned:

1. **Certificate form** `PredTree.hasDualOn_compose`: budgets only on the
   realizable tables, every `q, G : ℕ` and `A ≥ 0`, cost `8·A·√(q·G)`.
2. **Worst-case adversary form** `PredTree.hasDualOn_compose_of_advPMOn`:
   read-determined subroutines with `advPMOn ≤ T`, cost `24·T·√(q·G)`; the
   weak-duality corollary; the `sup'` budget for a nonempty family.
3. **The finite-output bridge** `exists_dualPairOn_of_two_mul_advPMOn_lt`
   (any decidable output type) and `hasDualOn_three_mul_advPMOn`.
4. **Quantum endpoints**: `8192·(1 + 8·A·√(q·G))` and
   `8192·(1 + 24·T·√(q·G))`, plus exact zero-query statements.

Scope checks:

* ordinary B–T is recovered by taking each subroutine to be one coordinate;
* the rejection-tree bound `8·T·D·√k` (`DrawProgram.hasDual_run`) is recovered
  from the total-table wrapper with `q = D·k`, `G = D`;
* subroutines may read identical positions, and one subroutine may be called
  repeatedly;
* branch grouping: a label map may identify several rejected values while
  keeping accepted values distinct;
* a promise example with budgets `(1, 1)` on the realizable tables but
  `(2, 2)` on arbitrary tables — the main theorem applies with no
  off-promise hypothesis;
* `q = 0`, `G = 0`, zero inner cost, empty `X`, empty `ι`, empty `P`;
* the adversary wrapper on a nonbinary return alphabet (`Fin 3`, a record).

The public bounds display `q`, `G` and the uniform inner budget only — no
alphabet, output, seed-count or subroutine-count factor appears in any pinned
statement.

Axioms (checked with `--trust=0`, 2026-09-21):

    #print axioms PredTree.hasDualOn_compose                    → [propext, Classical.choice, Quot.sound]
    #print axioms exists_dualPairOn_of_two_mul_advPMOn_lt       → [propext, Classical.choice, Quot.sound]
    #print axioms PredTree.hasDualOn_compose_of_advPMOn         → [propext, Classical.choice, Quot.sound]
    #print axioms PredTree.qQueryOn_third_compose_le            → [propext, Classical.choice, Quot.sound]
    #print axioms PredTree.qQueryOn_third_compose_le_of_advPMOn → [propext, Classical.choice, Quot.sound]
-/

namespace QuantumQueryComplexity
namespace PredictionTreeComposeAcceptance

open PredTree

/-! ## 1. The certificate form -/

theorem acceptance_certificate :
    ∀ {ι σ X P V α O : Type} [Fintype ι] [DecidableEq ι] [DecidableEq σ] [Fintype X]
      [DecidableEq X] [Fintype P] [DecidableEq P] [DecidableEq V] [Fintype α] [DecidableEq α]
      [DecidableEq O] (Tr : PredTree P V α Unit O) (read : X → ι → σ) (g : P → X → V)
      {A : ℝ}, 0 ≤ A → (∀ p, HasDualOn read (g p) A) →
      ∀ {q G : ℕ}, (∀ x, Tr.visits () (fun p => g p x) ≤ q) →
        (∀ x, Tr.unpreds () (fun p => g p x) ≤ G) →
        HasDualOn read (fun x => Tr.eval (fun p => g p x))
          (8 * A * Real.sqrt ((q : ℝ) * (G : ℝ))) :=
  fun Tr read g => fun hA hg => fun hvis hunp => hasDualOn_compose Tr read g hA hg hvis hunp

theorem acceptance_certificate_total :
    ∀ {ι σ P V α O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [Fintype P] [DecidableEq P] [DecidableEq V] [Fintype α] [DecidableEq α] [DecidableEq O]
      (Tr : PredTree P V α Unit O) (g : P → (ι → σ) → V) {A : ℝ}, 0 ≤ A →
      (∀ p, HasDual (g p) A) →
      ∀ {q G : ℕ}, (∀ x : ι → σ, Tr.visits () (fun p => g p x) ≤ q) →
        (∀ x : ι → σ, Tr.unpreds () (fun p => g p x) ≤ G) →
        HasDual (fun x => Tr.eval (fun p => g p x)) (8 * A * Real.sqrt ((q : ℝ) * (G : ℝ))) :=
  fun Tr g => fun hA hg => fun hvis hunp => hasDual_compose Tr g hA hg hvis hunp

/-! ## 2. The worst-case adversary form -/

theorem acceptance_adversary :
    ∀ {ι σ X P V α O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [Fintype X] [DecidableEq X] [Fintype P] [DecidableEq P] [DecidableEq V] [Fintype α]
      [DecidableEq α] [DecidableEq O] (Tr : PredTree P V α Unit O) (read : X → ι → σ)
      (g : P → X → V), (∀ p x y, read x = read y → g p x = g p y) →
      ∀ {T : ℝ}, 0 ≤ T → (∀ p, advPMOn read (g p) ≤ T) →
      ∀ {q G : ℕ}, (∀ x, Tr.visits () (fun p => g p x) ≤ q) →
        (∀ x, Tr.unpreds () (fun p => g p x) ≤ G) →
        HasDualOn read (fun x => Tr.eval (fun p => g p x))
            (24 * T * Real.sqrt ((q : ℝ) * (G : ℝ)))
          ∧ advPMOn read (fun x => Tr.eval (fun p => g p x))
            ≤ 24 * T * Real.sqrt ((q : ℝ) * (G : ℝ)) :=
  fun Tr read g hdet => fun hT hadv => fun hvis hunp =>
    ⟨hasDualOn_compose_of_advPMOn Tr read g hdet hT hadv hvis hunp,
     advPMOn_compose_le Tr read g hdet hT hadv hvis hunp⟩

theorem acceptance_adversary_sup :
    ∀ {ι σ X P V α O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [Fintype X] [DecidableEq X] [Fintype P] [DecidableEq P] [Nonempty P] [DecidableEq V]
      [Fintype α] [DecidableEq α] [DecidableEq O] (Tr : PredTree P V α Unit O)
      (read : X → ι → σ) (g : P → X → V), (∀ p x y, read x = read y → g p x = g p y) →
      ∀ {q G : ℕ}, (∀ x, Tr.visits () (fun p => g p x) ≤ q) →
        (∀ x, Tr.unpreds () (fun p => g p x) ≤ G) →
        HasDualOn read (fun x => Tr.eval (fun p => g p x))
          (24 * (Finset.univ.sup' Finset.univ_nonempty fun p => advPMOn read (g p))
            * Real.sqrt ((q : ℝ) * (G : ℝ))) :=
  fun Tr read g hdet => fun hvis hunp => hasDualOn_compose_of_advPMOn_sup Tr read g hdet hvis hunp

theorem acceptance_adversary_total :
    ∀ {ι σ P V α O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [Fintype P] [DecidableEq P] [DecidableEq V] [Fintype α] [DecidableEq α] [DecidableEq O]
      (Tr : PredTree P V α Unit O) (g : P → (ι → σ) → V) {T : ℝ}, 0 ≤ T →
      (∀ p, advPM (g p) ≤ T) →
      ∀ {q G : ℕ}, (∀ x : ι → σ, Tr.visits () (fun p => g p x) ≤ q) →
        (∀ x : ι → σ, Tr.unpreds () (fun p => g p x) ≤ G) →
        advPM (fun x => Tr.eval (fun p => g p x)) ≤ 24 * T * Real.sqrt ((q : ℝ) * (G : ℝ)) :=
  fun Tr g => fun hT hadv => fun hvis hunp => advPM_compose_le Tr g hT hadv hvis hunp

/-! ## 3. The finite-output bridge -/

theorem acceptance_bridge :
    ∀ {ι σ X O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype X]
      [DecidableEq X] [DecidableEq O] {read : X → ι → σ} {f : X → O},
      (∀ x y, read x = read y → f x = f y) →
      ∀ {c : ℝ}, 2 * advPMOn read f < c →
        ∃ (m : ℕ) (P : DualPairOn read (Fin m) f), P.IsCostLe c :=
  fun hdet => fun hc => exists_dualPairOn_of_two_mul_advPMOn_lt hdet hc

theorem acceptance_bridge_bundled :
    ∀ {ι σ X O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype X]
      [DecidableEq X] [DecidableEq O] {read : X → ι → σ} {f : X → O},
      (∀ x y, read x = read y → f x = f y) →
        HasDualOn read f (3 * advPMOn read f) :=
  fun hdet => hasDualOn_three_mul_advPMOn hdet

/-- The bridge on a nonbinary output type. -/
example {ι σ X : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype X]
    [DecidableEq X] {read : X → ι → σ} {f : X → Fin 3}
    (hdet : ∀ x y, read x = read y → f x = f y) {c : ℝ} (hc : 2 * advPMOn read f < c) :
    HasDualOn read f c :=
  hasDualOn_of_two_mul_advPMOn_lt hdet hc

/-! ## 4. Quantum endpoints -/

theorem acceptance_quantum :
    ∀ {ι σ X P V α O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [Fintype X] [DecidableEq X] [Fintype P] [DecidableEq P] [DecidableEq V] [Fintype α]
      [DecidableEq α] [DecidableEq O] [Nonempty O] (Tr : PredTree P V α Unit O)
      (read : X → ι → σ) (g : P → X → V) {A : ℝ}, 0 ≤ A → (∀ p, HasDualOn read (g p) A) →
      ∀ {q G : ℕ}, (∀ x, Tr.visits () (fun p => g p x) ≤ q) →
        (∀ x, Tr.unpreds () (fun p => g p x) ≤ G) →
        (qQueryOn read (fun x => Tr.eval (fun p => g p x)) (1 / 3) : ℝ)
          ≤ 8192 * (1 + 8 * A * Real.sqrt ((q : ℝ) * (G : ℝ))) :=
  fun Tr read g => fun hA hg => fun hvis hunp => qQueryOn_third_compose_le Tr read g hA hg hvis hunp

theorem acceptance_quantum_adversary :
    ∀ {ι σ X P V α O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [Fintype X] [DecidableEq X] [Fintype P] [DecidableEq P] [DecidableEq V] [Fintype α]
      [DecidableEq α] [DecidableEq O] [Nonempty O] (Tr : PredTree P V α Unit O)
      (read : X → ι → σ) (g : P → X → V), (∀ p x y, read x = read y → g p x = g p y) →
      ∀ {T : ℝ}, 0 ≤ T → (∀ p, advPMOn read (g p) ≤ T) →
      ∀ {q G : ℕ}, (∀ x, Tr.visits () (fun p => g p x) ≤ q) →
        (∀ x, Tr.unpreds () (fun p => g p x) ≤ G) →
        (qQueryOn read (fun x => Tr.eval (fun p => g p x)) (1 / 3) : ℝ)
          ≤ 8192 * (1 + 24 * T * Real.sqrt ((q : ℝ) * (G : ℝ))) :=
  fun Tr read g hdet => fun hT hadv => fun hvis hunp =>
    qQueryOn_third_compose_le_of_advPMOn Tr read g hdet hT hadv hvis hunp

theorem acceptance_quantum_zero :
    ∀ {ι σ X P V α O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [Fintype X] [DecidableEq X] [Fintype P] [DecidableEq P] [DecidableEq V] [Fintype α]
      [DecidableEq α] [DecidableEq O] [Nonempty O] (Tr : PredTree P V α Unit O)
      (read : X → ι → σ) (g : P → X → V) {ε : ℝ}, 0 ≤ ε →
      ((∀ x, Tr.visits () (fun p => g p x) ≤ 0) →
          qQueryOn read (fun x => Tr.eval (fun p => g p x)) ε = 0)
      ∧ ((∀ x, Tr.unpreds () (fun p => g p x) ≤ 0) →
          qQueryOn read (fun x => Tr.eval (fun p => g p x)) ε = 0)
      ∧ ((∀ p, HasDualOn read (g p) 0) →
          qQueryOn read (fun x => Tr.eval (fun p => g p x)) ε = 0) :=
  fun Tr read g => fun hε =>
    ⟨fun hvis => qQueryOn_compose_eq_zero_of_visits Tr read g hvis hε,
     fun hunp => qQueryOn_compose_eq_zero_of_unpreds Tr read g hunp hε,
     fun hg => qQueryOn_compose_eq_zero_of_cost_zero Tr read g hg hε⟩

/-! ## 5. Ordinary Beigi–Taghavi is a special case

Each subroutine is one coordinate (`hasDual_ofCoord`, cost `2`); the composite
is the tree run on the input itself. -/

example {ι σ α O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    [Fintype α] [DecidableEq α] [DecidableEq O] (Tr : PredTree ι σ α Unit O) {q G : ℕ}
    (hvis : ∀ x, Tr.visits () x ≤ q) (hunp : ∀ x, Tr.unpreds () x ≤ G) :
    HasDual Tr.eval (8 * 2 * Real.sqrt ((q : ℝ) * (G : ℝ))) :=
  hasDual_compose Tr (fun i x => x i) (by norm_num) (fun i => hasDual_ofCoord i id) hvis hunp

/-! ## 6. The rejection tree: `8·T·D·√k` from `q = D·k`, `G = D` -/

example {S E ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    [DecidableEq S] [Fintype E] [DecidableEq E] (prog : DrawProgram S E) {D k : ℕ}
    (hD : 1 ≤ D) (hk : 1 ≤ k) (s₀ : S) (g : Fin D × Fin k → (ι → σ) → E) {T : ℝ}
    (hT : 0 ≤ T) (hg : ∀ p, HasDual (g p) T) :
    HasDual (fun x : ι → σ => (DrawProgram.run prog D k s₀).eval fun p => g p x)
      (8 * T * D * Real.sqrt k) := by
  have h := hasDual_compose_of_table_bounds (DrawProgram.run prog D k s₀) g hT hg
    (q := D * k) (G := D) (Nat.mul_pos hD hk) hD
    (DrawProgram.visits_run_le s₀) (DrawProgram.unpreds_run_le s₀)
  refine h.mono (le_of_eq ?_)
  push_cast
  rw [show (D : ℝ) * k * D = (D : ℝ) ^ 2 * k by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by positivity)]
  ring

/-- The same, from the main theorem (budgets only on realizable tables are
of course implied by the table-wise ones). -/
example {S E ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    [DecidableEq S] [Fintype E] [DecidableEq E] (prog : DrawProgram S E) {D k : ℕ}
    (s₀ : S) (g : Fin D × Fin k → (ι → σ) → E) {T : ℝ}
    (hT : 0 ≤ T) (hg : ∀ p, HasDual (g p) T) :
    HasDual (fun x : ι → σ => (DrawProgram.run prog D k s₀).eval fun p => g p x)
      (8 * T * Real.sqrt (((D * k : ℕ) : ℝ) * (D : ℝ))) :=
  hasDual_compose (DrawProgram.run prog D k s₀) g hT hg
    (fun _ => DrawProgram.visits_run_le s₀ _) (fun _ => DrawProgram.unpreds_run_le s₀ _)

/-! ## 7. Overlapping inputs and repeated calls -/

/-- Two subroutines reading the very same coordinate. -/
example {ι σ α O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    [Fintype α] [DecidableEq α] [DecidableEq O] (Tr : PredTree (Fin 2) σ α Unit O) (i₀ : ι)
    {q G : ℕ} (hvis : ∀ x : ι → σ, Tr.visits () (fun _ => x i₀) ≤ q)
    (hunp : ∀ x : ι → σ, Tr.unpreds () (fun _ => x i₀) ≤ G) :
    HasDual (fun x => Tr.eval (fun _ => x i₀)) (8 * 2 * Real.sqrt ((q : ℝ) * (G : ℝ))) :=
  hasDual_compose Tr (fun _ x => x i₀) (by norm_num) (fun _ => hasDual_ofCoord i₀ id) hvis hunp

/-- The same subroutine called twice in a row (no prediction): two calls, two
unpredicted answers, cost `8·A·√4 = 16·A`. -/
def twice {V O : Type} (p : Unit) (o : V → V → O) : PredTree Unit V V Unit O :=
  PredTree.query p id none () fun v₁ =>
    PredTree.query p id none () fun v₂ => PredTree.leaf (o v₁ v₂)

example {ι σ X V O : Type} [Fintype ι] [DecidableEq ι] [DecidableEq σ] [Fintype X]
    [DecidableEq X] [Fintype V] [DecidableEq V] [DecidableEq O] (read : X → ι → σ)
    (h : X → V) (o : V → V → O) {A : ℝ} (hA : 0 ≤ A) (hh : HasDualOn read h A) :
    HasDualOn read (fun x => (twice () o).eval (fun _ => h x))
      (8 * A * Real.sqrt ((2 : ℕ) * (2 : ℕ))) :=
  hasDualOn_compose (twice () o) read (fun _ => h) hA (fun _ => hh)
    (fun x => by simp [twice, PredTree.visits])
    (fun x => by simp [twice, PredTree.unpreds, PredTree.unpred])

/-! ## 8. Branch grouping

The label map sends every rejected return value to the single predicted
label `none` and every accepted value `v` to its own label `some v`; the
continuation only sees the label, so rejected values are forgotten.
Rejections are predicted, so they cost nothing in `G`. -/

def grouped {V O : Type} (accept : V → Bool) (onAccept : V → O) (onReject : O) :
    PredTree Unit V (Option V) Unit O :=
  PredTree.query () (fun v => if accept v then some v else none) (some none) () fun l =>
    match l with
    | some v => PredTree.leaf (onAccept v)
    | none => PredTree.leaf onReject

/-- A rejected value is a predicted answer: no unpredicted answer, output
`onReject`. -/
example {V O : Type} [DecidableEq V] (accept : V → Bool) (onAccept : V → O) (onReject : O)
    (z : Unit → V) (hz : accept (z ()) = false) :
    (grouped accept onAccept onReject).unpreds () z = 0
      ∧ (grouped accept onAccept onReject).eval z = onReject := by
  constructor <;> simp [grouped, PredTree.unpreds, PredTree.unpred, hz]

/-- An accepted value costs one unpredicted answer and is passed on intact. -/
example {V O : Type} [DecidableEq V] (accept : V → Bool) (onAccept : V → O) (onReject : O)
    (z : Unit → V) (hz : accept (z ()) = true) :
    (grouped accept onAccept onReject).unpreds () z = 1
      ∧ (grouped accept onAccept onReject).eval z = onAccept (z ()) := by
  constructor <;> simp [grouped, PredTree.unpreds, PredTree.unpred, hz]

/-! ## 9. A promise example: small budgets on the realizable tables only

Subroutine `0` is constant `true` on the promise; the tree asks it first and
only asks subroutine `1` when the answer is `false`.  Every realizable table
makes one call and receives one unpredicted answer, while an arbitrary table
with `z 0 = false` makes two calls and receives two unpredicted answers.  The
main theorem applies with the budgets `(1, 1)` and no off-promise hypothesis;
the table-wise budgets would have been `(2, 2)`. -/

def promiseTree {O : Type} (o₁ o₂ o₃ : O) : PredTree (Fin 2) Bool Bool Unit O :=
  PredTree.query 0 id none () fun b =>
    if b then PredTree.leaf o₁
    else PredTree.query 1 id none () fun b' => PredTree.leaf (if b' then o₂ else o₃)

/-- The realizable tables have budget `(1, 1)`. -/
example {O : Type} (o₁ o₂ o₃ : O) (z : Fin 2 → Bool) (hz : z 0 = true) :
    (promiseTree o₁ o₂ o₃).visits () z = 1 ∧ (promiseTree o₁ o₂ o₃).unpreds () z = 1 := by
  constructor <;> simp [promiseTree, PredTree.visits, PredTree.unpreds, PredTree.unpred, hz]

/-- An off-promise table has budget `(2, 2)`. -/
example {O : Type} (o₁ o₂ o₃ : O) (z : Fin 2 → Bool) (hz : z 0 = false) :
    (promiseTree o₁ o₂ o₃).visits () z = 2 ∧ (promiseTree o₁ o₂ o₃).unpreds () z = 2 := by
  constructor <;> simp [promiseTree, PredTree.visits, PredTree.unpreds, PredTree.unpred, hz]

/-- The main theorem at budgets `(1, 1)`: cost `8·A`. -/
example {ι σ X O : Type} [Fintype ι] [DecidableEq ι] [DecidableEq σ] [Fintype X]
    [DecidableEq X] [DecidableEq O] (read : X → ι → σ) (h : X → Bool) (o₁ o₂ o₃ : O)
    {A : ℝ} (hA : 0 ≤ A) (hh : HasDualOn read h A) :
    HasDualOn read (fun x => (promiseTree o₁ o₂ o₃).eval (fun p => ![fun _ => true, h] p x))
      (8 * A * Real.sqrt ((1 : ℕ) * (1 : ℕ))) := by
  refine hasDualOn_compose (promiseTree o₁ o₂ o₃) read ![fun _ => true, h] hA ?_ ?_ ?_
  · intro p
    fin_cases p
    · exact (hasDualOn_of_const read fun _ _ => rfl).mono hA
    · exact hh
  · intro x
    simp [promiseTree, PredTree.visits]
  · intro x
    simp [promiseTree, PredTree.unpreds, PredTree.unpred]

/-! ## 10. Zero cases and empty types -/

/-- `q = 0`: the certificate costs `0`. -/
example {ι σ X P V α O : Type} [Fintype ι] [DecidableEq ι] [DecidableEq σ] [Fintype X]
    [DecidableEq X] [Fintype P] [DecidableEq P] [DecidableEq V] [Fintype α] [DecidableEq α]
    [DecidableEq O] (Tr : PredTree P V α Unit O) (read : X → ι → σ) (g : P → X → V)
    {A : ℝ} (hA : 0 ≤ A) (hg : ∀ p, HasDualOn read (g p) A) {G : ℕ}
    (hvis : ∀ x, Tr.visits () (fun p => g p x) ≤ 0)
    (hunp : ∀ x, Tr.unpreds () (fun p => g p x) ≤ G) :
    HasDualOn read (fun x => Tr.eval (fun p => g p x)) 0 := by
  have h := hasDualOn_compose Tr read g hA hg hvis hunp
  simpa using h

/-- `G = 0`: the certificate costs `0`. -/
example {ι σ X P V α O : Type} [Fintype ι] [DecidableEq ι] [DecidableEq σ] [Fintype X]
    [DecidableEq X] [Fintype P] [DecidableEq P] [DecidableEq V] [Fintype α] [DecidableEq α]
    [DecidableEq O] (Tr : PredTree P V α Unit O) (read : X → ι → σ) (g : P → X → V)
    {A : ℝ} (hA : 0 ≤ A) (hg : ∀ p, HasDualOn read (g p) A) {q : ℕ}
    (hvis : ∀ x, Tr.visits () (fun p => g p x) ≤ q)
    (hunp : ∀ x, Tr.unpreds () (fun p => g p x) ≤ 0) :
    HasDualOn read (fun x => Tr.eval (fun p => g p x)) 0 := by
  have h := hasDualOn_compose Tr read g hA hg hvis hunp
  simpa using h

/-- Zero inner cost: the certificate costs `0` and the output is constant. -/
example {ι σ X P V α O : Type} [Fintype ι] [DecidableEq ι] [DecidableEq σ] [Fintype X]
    [DecidableEq X] [Fintype P] [DecidableEq P] [DecidableEq V] [Fintype α] [DecidableEq α]
    [DecidableEq O] (Tr : PredTree P V α Unit O) (read : X → ι → σ) (g : P → X → V)
    (hg : ∀ p, HasDualOn read (g p) 0) {q G : ℕ}
    (hvis : ∀ x, Tr.visits () (fun p => g p x) ≤ q)
    (hunp : ∀ x, Tr.unpreds () (fun p => g p x) ≤ G) :
    HasDualOn read (fun x => Tr.eval (fun p => g p x)) 0
      ∧ ∀ x y, Tr.eval (fun p => g p x) = Tr.eval (fun p => g p y) := by
  refine ⟨?_, eval_eq_of_cost_zero Tr read g hg⟩
  have h := hasDualOn_compose Tr read g le_rfl hg hvis hunp
  simpa using h

/-- Adversary budget `T = 0`: cost `0`. -/
example {ι σ X P V α O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    [Fintype X] [DecidableEq X] [Fintype P] [DecidableEq P] [DecidableEq V] [Fintype α]
    [DecidableEq α] [DecidableEq O] (Tr : PredTree P V α Unit O) (read : X → ι → σ)
    (g : P → X → V) (hdet : ∀ p x y, read x = read y → g p x = g p y)
    (hadv : ∀ p, advPMOn read (g p) ≤ 0) {q G : ℕ}
    (hvis : ∀ x, Tr.visits () (fun p => g p x) ≤ q)
    (hunp : ∀ x, Tr.unpreds () (fun p => g p x) ≤ G) :
    HasDualOn read (fun x => Tr.eval (fun p => g p x)) 0 := by
  have h := hasDualOn_compose_of_advPMOn Tr read g hdet le_rfl hadv hvis hunp
  simpa using h

/-- Empty promise domain. -/
example {ι σ P V α O : Type} [Fintype ι] [DecidableEq ι] [DecidableEq σ] [Fintype P]
    [DecidableEq P] [DecidableEq V] [Fintype α] [DecidableEq α] [DecidableEq O]
    (Tr : PredTree P V α Unit O) (g : P → Empty → V) {A : ℝ} (hA : 0 ≤ A) {q G : ℕ} :
    HasDualOn (fun x : Empty => (x.elim : ι → σ)) (fun x => Tr.eval (fun p => g p x))
      (8 * A * Real.sqrt ((q : ℝ) * (G : ℝ))) :=
  hasDualOn_compose Tr (fun x : Empty => (x.elim : ι → σ)) g hA
    (fun p => (hasDualOn_of_const (fun x : Empty => (x.elim : ι → σ)) (f := g p)
      fun x => x.elim).mono hA) (fun x => x.elim) (fun x => x.elim)

/-- No query positions: read-determinacy makes every subroutine constant, the
adversary budget is `0`, and so is the certificate. -/
example {σ X P V α O : Type} [Fintype σ] [DecidableEq σ] [Fintype X] [DecidableEq X]
    [Fintype P] [DecidableEq P] [DecidableEq V] [Fintype α] [DecidableEq α] [DecidableEq O]
    (Tr : PredTree P V α Unit O) (g : P → X → V) (hconst : ∀ p x y, g p x = g p y)
    {q G : ℕ} (hvis : ∀ x, Tr.visits () (fun p => g p x) ≤ q)
    (hunp : ∀ x, Tr.unpreds () (fun p => g p x) ≤ G) :
    HasDualOn (fun (_ : X) (i : Empty) => (i.elim : σ)) (fun x => Tr.eval (fun p => g p x))
      (24 * 0 * Real.sqrt ((q : ℝ) * (G : ℝ))) :=
  hasDualOn_compose_of_advPMOn Tr (fun (_ : X) (i : Empty) => (i.elim : σ)) g
    (fun p x y _ => hconst p x y) le_rfl
    (fun p => advPMOn_le_of_hasDualOn le_rfl (hasDualOn_of_const _ (hconst p))) hvis hunp

/-- No subroutines at all. -/
example {ι σ X V α O : Type} [Fintype ι] [DecidableEq ι] [DecidableEq σ] [Fintype X]
    [DecidableEq X] [DecidableEq V] [Fintype α] [DecidableEq α] [DecidableEq O]
    (Tr : PredTree Empty V α Unit O) (read : X → ι → σ) (g : Empty → X → V) {A : ℝ}
    (hA : 0 ≤ A) {q G : ℕ} (hvis : ∀ x, Tr.visits () (fun p => g p x) ≤ q)
    (hunp : ∀ x, Tr.unpreds () (fun p => g p x) ≤ G) :
    HasDualOn read (fun x => Tr.eval (fun p => g p x)) (8 * A * Real.sqrt ((q : ℝ) * (G : ℝ))) :=
  hasDualOn_compose Tr read g hA (fun p => p.elim) hvis hunp

/-! ## 11. Nonbinary return alphabets -/

/-- The adversary wrapper with a three-valued return alphabet. -/
example {ι σ X P α O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    [Fintype X] [DecidableEq X] [Fintype P] [DecidableEq P] [Fintype α] [DecidableEq α]
    [DecidableEq O] (Tr : PredTree P (Fin 3) α Unit O) (read : X → ι → σ)
    (g : P → X → Fin 3) (hdet : ∀ p x y, read x = read y → g p x = g p y)
    {T : ℝ} (hT : 0 ≤ T) (hadv : ∀ p, advPMOn read (g p) ≤ T) {q G : ℕ}
    (hvis : ∀ x, Tr.visits () (fun p => g p x) ≤ q)
    (hunp : ∀ x, Tr.unpreds () (fun p => g p x) ≤ G) :
    HasDualOn read (fun x => Tr.eval (fun p => g p x))
      (24 * T * Real.sqrt ((q : ℝ) * (G : ℝ))) :=
  hasDualOn_compose_of_advPMOn Tr read g hdet hT hadv hvis hunp

/-- A record-valued return alphabet, and heterogeneous alphabets through the
sigma tagging (`HasDualOn.sigmaMk`). -/
example {ι σ X : Type} [Fintype ι] [DecidableEq ι] [DecidableEq σ] [Fintype X]
    [DecidableEq X] {read : X → ι → σ} {Γ : Fin 2 → Type} [∀ p, DecidableEq (Γ p)]
    (g : ∀ p, X → Γ p) {A : ℝ} (hg : ∀ p, HasDualOn read (g p) A) (p : Fin 2) :
    HasDualOn read (fun x => (⟨p, g p x⟩ : Σ p, Γ p)) A :=
  (hg p).sigmaMk

end PredictionTreeComposeAcceptance
end QuantumQueryComplexity
