import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Nat

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# Longest distinct substring: definitions and window combinatorics

`ldsFun α` is the maximum length of a *distinct window* of the word
`α : Fin n → σ` — a contiguous closed interval `[i, j]` on which `α` is
injective (Allcock–Bao–Belovs–Lee–Santha, arXiv:2311.16401, Problem 28).
`lambdaFun α a j` is the sliding-window quantity `Λ_a(j)`: the leftmost
start `i ∈ [a, j]` with `[i, j]` distinct.

Everything here is 0-based over `Fin n`; `LDS/Node.lean` expresses the node
combinatorics in these coordinates. The definitions specify windows directly.

Facts proved:
* `[Λ_a(j), j]` is distinct, lies in `[a, j]`, and is minimal such;
* `Λ_a` is monotone in the right endpoint `j`;
* barrier clipping `Λ_{a'}(j) = max a' (Λ_a(j))` for `a ≤ a' ≤ j`;
* `ldsFun α = max_j (j - Λ_0(j) + 1)`;
* `ldsFun α = n ↔ α` injective (the bridge `LDS/Lower.lean` rides).

Degenerate windows (`j < i`) are vacuously distinct and have `winLen = 0`
by truncated subtraction, so they never contribute to the maximum and no
`i ≤ j` side conditions have to be threaded through `ldsFun`.
-/

namespace QuantumQueryComplexity

variable {n : ℕ} {σ : Type*} [DecidableEq σ]

/-! ## Distinct windows -/

/-- The window `[i, j]` (closed, possibly degenerate) is *distinct* if `α`
is injective on it.  Bounded quantifiers keep it decidable. -/
def IsDistinct (α : Fin n → σ) (i j : Fin n) : Prop :=
  ∀ a ∈ Finset.Icc i j, ∀ b ∈ Finset.Icc i j, α a = α b → a = b

instance (α : Fin n → σ) (i j : Fin n) : Decidable (IsDistinct α i j) :=
  inferInstanceAs (Decidable (∀ a ∈ Finset.Icc i j, ∀ b ∈ Finset.Icc i j,
    α a = α b → a = b))

/-- Distinctness survives shrinking the window (interval inclusion form). -/
lemma IsDistinct.subset {α : Fin n → σ} {i j i' j' : Fin n}
    (h : IsDistinct α i j) (hsub : Finset.Icc i' j' ⊆ Finset.Icc i j) :
    IsDistinct α i' j' := fun a ha b hb hab => h a (hsub ha) b (hsub hb) hab

/-- Distinctness survives shrinking the window (endpoint form). -/
lemma IsDistinct.mono {α : Fin n → σ} {i j i' j' : Fin n}
    (h : IsDistinct α i j) (hi : i ≤ i') (hj : j' ≤ j) :
    IsDistinct α i' j' := h.subset (Finset.Icc_subset_Icc hi hj)

/-- Singleton windows are distinct. -/
lemma isDistinct_self (α : Fin n → σ) (i : Fin n) : IsDistinct α i i := by
  intro a ha b hb _
  rw [Finset.mem_Icc] at ha hb
  exact le_antisymm (ha.2.trans hb.1) (hb.2.trans ha.1)

/-- Degenerate windows are vacuously distinct. -/
lemma isDistinct_of_lt (α : Fin n → σ) {i j : Fin n} (h : j < i) :
    IsDistinct α i j := by
  intro a ha
  rw [Finset.mem_Icc] at ha
  exact absurd (ha.1.trans ha.2) (not_le.mpr h)

/-- An injective word has every window distinct. -/
lemma isDistinct_of_injective {α : Fin n → σ} (h : Function.Injective α)
    (i j : Fin n) : IsDistinct α i j := fun _ _ _ _ hab => h hab

/-! ## Window length and the longest distinct substring -/

/-- The length `j - i + 1` of the window `[i, j]`; truncated subtraction
makes degenerate windows have length `0`. -/
def winLen (i j : Fin n) : ℕ := (j : ℕ) + 1 - (i : ℕ)

@[simp] lemma winLen_self (i : Fin n) : winLen i i = 1 := by
  simp [winLen]

lemma winLen_le (i j : Fin n) : winLen i j ≤ n := by
  have := j.isLt
  simp only [winLen]
  omega

/-- **Longest distinct substring** (arXiv:2311.16401, Problem 28): the
maximum length of a distinct window of `α`. -/
def ldsFun (α : Fin n → σ) : ℕ :=
  Finset.univ.sup fun p : Fin n × Fin n =>
    if IsDistinct α p.1 p.2 then winLen p.1 p.2 else 0

/-- Every distinct window is a witness: its length bounds `ldsFun` below. -/
lemma le_ldsFun {α : Fin n → σ} {i j : Fin n} (h : IsDistinct α i j) :
    winLen i j ≤ ldsFun α := by
  have hle := Finset.le_sup (f := fun p : Fin n × Fin n =>
    if IsDistinct α p.1 p.2 then winLen p.1 p.2 else 0)
    (Finset.mem_univ (i, j))
  simp only [h, if_true] at hle
  exact hle

lemma ldsFun_le (α : Fin n → σ) : ldsFun α ≤ n := by
  unfold ldsFun
  refine Finset.sup_le fun p _ => ?_
  split
  · exact winLen_le p.1 p.2
  · exact Nat.zero_le n

/-- A nonempty word has a distinct window: its singletons. -/
lemma one_le_ldsFun (hn : 0 < n) (α : Fin n → σ) : 1 ≤ ldsFun α := by
  simpa using le_ldsFun (isDistinct_self α ⟨0, hn⟩)

/-- An injective word is one big distinct window. -/
lemma ldsFun_eq_of_injective {α : Fin n → σ}
    (h : Function.Injective α) : ldsFun α = n := by
  refine le_antisymm (ldsFun_le α) ?_
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · exact h0.le.trans (Nat.zero_le _)
  · have hw : winLen (⟨0, hn⟩ : Fin n) ⟨n - 1, by omega⟩ = n := by
      change n - 1 + 1 - 0 = n
      omega
    have := le_ldsFun (isDistinct_of_injective h ⟨0, hn⟩ ⟨n - 1, by omega⟩)
    rw [hw] at this
    exact this

/-- Conversely, a full-length distinct window forces injectivity. -/
lemma injective_of_ldsFun_eq {α : Fin n → σ}
    (h : ldsFun α = n) : Function.Injective α := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · exact fun a b _ => absurd a.isLt (by omega)
  · unfold ldsFun at h
    have hb : (⊥ : ℕ) < n := by
      rw [Nat.bot_eq_zero]
      exact hn
    obtain ⟨p, -, hp⟩ := (Finset.le_sup_iff hb).mp h.ge
    by_cases hd : IsDistinct α p.1 p.2
    · rw [if_pos hd] at hp
      have h2 := p.2.isLt
      have hv1 : (p.1 : ℕ) = 0 := by simp only [winLen] at hp; omega
      have hv2 : (p.2 : ℕ) = n - 1 := by simp only [winLen] at hp; omega
      intro a b hab
      have ha := a.isLt
      have hb := b.isLt
      refine hd a (Finset.mem_Icc.mpr ⟨?_, ?_⟩) b
        (Finset.mem_Icc.mpr ⟨?_, ?_⟩) hab <;> rw [Fin.le_def] <;> omega
    · rw [if_neg hd] at hp
      omega

/-- `ldsFun α = n` exactly on injective words: the bridge to element
distinctness (`LDS/Lower.lean`, plan §2). -/
lemma ldsFun_eq_iff_injective {α : Fin n → σ} :
    ldsFun α = n ↔ Function.Injective α :=
  ⟨injective_of_ldsFun_eq, ldsFun_eq_of_injective⟩

/-! ## The sliding-window quantity `Λ` -/

/-- The candidate starts for `Λ_a(j)`: positions `i ∈ [a, j]` with `[i, j]`
distinct. -/
def lambdaSet (α : Fin n → σ) (a j : Fin n) : Finset (Fin n) :=
  (Finset.Icc a j).filter fun i => IsDistinct α i j

lemma mem_lambdaSet {α : Fin n → σ} {a j i : Fin n} :
    i ∈ lambdaSet α a j ↔ (a ≤ i ∧ i ≤ j) ∧ IsDistinct α i j := by
  simp [lambdaSet, Finset.mem_Icc]

lemma lambdaSet_nonempty (α : Fin n → σ) {a j : Fin n} (haj : a ≤ j) :
    (lambdaSet α a j).Nonempty :=
  ⟨j, mem_lambdaSet.mpr ⟨⟨haj, le_rfl⟩, isDistinct_self α j⟩⟩

/-- `Λ_a(j)` (plan §0): the leftmost start `i ∈ [a, j]` with `[i, j]`
distinct.  Junk value `j` when `a > j`; every lemma below assumes `a ≤ j`. -/
def lambdaFun (α : Fin n → σ) (a j : Fin n) : Fin n :=
  if h : (lambdaSet α a j).Nonempty then (lambdaSet α a j).min' h else j

variable {α : Fin n → σ} {a a' i j j' : Fin n}

lemma lambdaFun_mem (haj : a ≤ j) : lambdaFun α a j ∈ lambdaSet α a j := by
  rw [lambdaFun, dif_pos (lambdaSet_nonempty α haj)]
  exact Finset.min'_mem _ _

lemma le_lambdaFun (haj : a ≤ j) : a ≤ lambdaFun α a j :=
  (mem_lambdaSet.mp (lambdaFun_mem haj)).1.1

lemma lambdaFun_le (haj : a ≤ j) : lambdaFun α a j ≤ j :=
  (mem_lambdaSet.mp (lambdaFun_mem haj)).1.2

/-- `[Λ_a(j), j]` is itself distinct. -/
lemma isDistinct_lambdaFun (haj : a ≤ j) :
    IsDistinct α (lambdaFun α a j) j :=
  (mem_lambdaSet.mp (lambdaFun_mem haj)).2

/-- Minimality of `Λ_a(j)` among distinct starts in `[a, j]`. -/
lemma lambdaFun_le_of_isDistinct (hi : a ≤ i) (hij : i ≤ j)
    (h : IsDistinct α i j) : lambdaFun α a j ≤ i := by
  rw [lambdaFun, dif_pos (lambdaSet_nonempty α (hi.trans hij))]
  exact Finset.min'_le _ _ (mem_lambdaSet.mpr ⟨⟨hi, hij⟩, h⟩)

/-- The window at `Λ` bounds `ldsFun` below — one half of the per-endpoint
scan identity. -/
lemma winLen_lambdaFun_le (haj : a ≤ j) :
    winLen (lambdaFun α a j) j ≤ ldsFun α :=
  le_ldsFun (isDistinct_lambdaFun haj)

/-- **Sliding-window monotonicity** (plan §0): `Λ_a` is monotone in the
right endpoint. -/
lemma lambdaFun_mono (haj : a ≤ j) (hjj : j ≤ j') :
    lambdaFun α a j ≤ lambdaFun α a j' := by
  have haj' : a ≤ j' := haj.trans hjj
  rcases le_or_gt (lambdaFun α a j') j with hle | hlt
  · exact lambdaFun_le_of_isDistinct (le_lambdaFun haj') hle
      ((isDistinct_lambdaFun haj').mono le_rfl hjj)
  · exact (lambdaFun_le haj).trans hlt.le

/-- **Barrier clipping**: raising the left barrier clips `Λ` at
the barrier, `Λ_{a'}(j) = max a' (Λ_a(j))` for `a ≤ a' ≤ j`. -/
lemma lambdaFun_eq_max (haa : a ≤ a') (ha'j : a' ≤ j) :
    lambdaFun α a' j = max a' (lambdaFun α a j) := by
  have haj : a ≤ j := haa.trans ha'j
  rcases le_or_gt a' (lambdaFun α a j) with h | h
  · rw [max_eq_right h]
    exact le_antisymm
      (lambdaFun_le_of_isDistinct h (lambdaFun_le haj)
        (isDistinct_lambdaFun haj))
      (lambdaFun_le_of_isDistinct (haa.trans (le_lambdaFun ha'j))
        (lambdaFun_le ha'j) (isDistinct_lambdaFun ha'j))
  · rw [max_eq_left h.le]
    exact le_antisymm
      (lambdaFun_le_of_isDistinct le_rfl ha'j
        ((isDistinct_lambdaFun haj).mono h.le le_rfl))
      (le_lambdaFun ha'j)

/-- The `a = 0` specialization:
`Λ_a(j) = max a (Λ_0(j))`. -/
lemma lambdaFun_eq_max_zero {α : Fin (n + 1) → σ} {a j : Fin (n + 1)}
    (haj : a ≤ j) : lambdaFun α a j = max a (lambdaFun α 0 j) :=
  lambdaFun_eq_max (Fin.zero_le a) haj

/-! ## The mirror of `Λ`

`ρ_b(l)` is the rightmost end `r ≤ b` with `[l, r]` distinct — the quantity
the node's *truncation* step uses, and the `R`-anchor
of the paper.  Everything mirrors the `Λ` section. -/

/-- The candidate ends for `ρ_b(l)`: positions `r ∈ [l, b]` with `[l, r]`
distinct. -/
def rhoSet (α : Fin n → σ) (l b : Fin n) : Finset (Fin n) :=
  (Finset.Icc l b).filter fun r => IsDistinct α l r

lemma mem_rhoSet {α : Fin n → σ} {l b r : Fin n} :
    r ∈ rhoSet α l b ↔ (l ≤ r ∧ r ≤ b) ∧ IsDistinct α l r := by
  simp [rhoSet, Finset.mem_Icc]

lemma rhoSet_nonempty (α : Fin n → σ) {l b : Fin n} (hlb : l ≤ b) :
    (rhoSet α l b).Nonempty :=
  ⟨l, mem_rhoSet.mpr ⟨⟨le_rfl, hlb⟩, isDistinct_self α l⟩⟩

/-- `ρ_b(l)`: the rightmost end `r ∈ [l, b]` with `[l, r]` distinct.  Junk
value `l` when `l > b`; every lemma below assumes `l ≤ b`. -/
def rhoFun (α : Fin n → σ) (l b : Fin n) : Fin n :=
  if h : (rhoSet α l b).Nonempty then (rhoSet α l b).max' h else l

lemma rhoFun_mem {α : Fin n → σ} {l b : Fin n} (hlb : l ≤ b) :
    rhoFun α l b ∈ rhoSet α l b := by
  rw [rhoFun, dif_pos (rhoSet_nonempty α hlb)]
  exact Finset.max'_mem _ _

lemma le_rhoFun {α : Fin n → σ} {l b : Fin n} (hlb : l ≤ b) :
    l ≤ rhoFun α l b := (mem_rhoSet.mp (rhoFun_mem hlb)).1.1

lemma rhoFun_le {α : Fin n → σ} {l b : Fin n} (hlb : l ≤ b) :
    rhoFun α l b ≤ b := (mem_rhoSet.mp (rhoFun_mem hlb)).1.2

/-- `[l, ρ_b(l)]` is itself distinct. -/
lemma isDistinct_rhoFun {α : Fin n → σ} {l b : Fin n} (hlb : l ≤ b) :
    IsDistinct α l (rhoFun α l b) := (mem_rhoSet.mp (rhoFun_mem hlb)).2

/-- **Maximality of `ρ`** among distinct ends in `[l, b]`. -/
lemma le_rhoFun_of_isDistinct {α : Fin n → σ} {l b r : Fin n} (hlr : l ≤ r)
    (hrb : r ≤ b) (h : IsDistinct α l r) : r ≤ rhoFun α l b := by
  rw [rhoFun, dif_pos (rhoSet_nonempty α (hlr.trans hrb))]
  exact Finset.le_max' _ _ (mem_rhoSet.mpr ⟨⟨hlr, hrb⟩, h⟩)

/-- **The per-endpoint scan identity** (plan §0):
`ldsFun α = max_j (j - Λ_0(j) + 1)`. -/
lemma ldsFun_eq_sup_lambda (α : Fin (n + 1) → σ) :
    ldsFun α
      = Finset.univ.sup fun j : Fin (n + 1) => winLen (lambdaFun α 0 j) j := by
  refine le_antisymm ?_
    (Finset.sup_le fun j _ => winLen_lambdaFun_le (Fin.zero_le j))
  unfold ldsFun
  refine Finset.sup_le fun p _ => ?_
  by_cases hd : IsDistinct α p.1 p.2
  · rw [if_pos hd]
    refine le_trans ?_ (Finset.le_sup (Finset.mem_univ p.2))
    rcases le_or_gt p.1 p.2 with hle | hlt
    · have hmin : (lambdaFun α 0 p.2 : ℕ) ≤ (p.1 : ℕ) :=
        lambdaFun_le_of_isDistinct (Fin.zero_le p.1) hle hd
      simp only [winLen]
      omega
    · have h1 : (p.2 : ℕ) < (p.1 : ℕ) := hlt
      simp only [winLen]
      omega
  · rw [if_neg hd]
    exact Nat.zero_le _

end QuantumQueryComplexity
