import QuantumQueryComplexity.Quantum.Walk.MNRS
import QuantumQueryComplexity.Quantum.Walk.Chain

set_option linter.style.header false
set_option synthInstance.maxSize 3200
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Walk search with input-dependent chains and approximate routines

[CGKLPZ26, Lemma 2.6 and the proof of Lemma 2.8; MNRS11]. The exact contract `WalkOK` asks for
exact setup, update and check routines. The walk of the paper's bipartite test uses approximate
coherent preparations and an approximate check, and its chain depends on the unknown input.

**The compiled algorithm is independent of the input.** It is `S.walkSearch K`, built from the
routines of a `WalkSetup` and the clock length only. Its analytical fields (`r`, `D`, `δ`) do not
enter it (`WalkSetup.walkSearch_congr`). The ideal chain, the marked set and the phases below
are analysis data for one input.

**The ideal chain on the input `x`** (`WalkChain V`) lives on **all** of `V`: `P` row-stochastic,
`π` a distribution, and `√π` fixed by the discriminant `D_{uv} = √(P_{uv} P_{vu})`. Neither
reversibility nor positivity of `π` is required. The configurations that cannot occur on `x`
(for example lists containing an unmarked vertex, or configurations with dirty scratch) are
part of `V` and get ideal rows like every other configuration. Typically `π` vanishes on them
and `D` splits as the reachable chain plus blocks of norm at most `1 − δ`, so the absolute gap
`δ` is still a statement on all of `V`.

Why all of `V`: the compiled walk applies the update to arbitrary states (inside the level
reflections it applies `upd⁻¹` to states that are not combinations of rows), so it reaches
configurations outside any input-dependent subset, and its check is applied there too. An ideal
on a subset would need preservation hypotheses that natural implementations do not satisfy (a
preparation applied to a non-blank register produces arbitrary labels).

**The contract** (`ApproxWalkOK S x Q Marked c c₀ δ ε`):
* every update row is within `ε` of `c` times its ideal row, `|u⟩ ⊗ ∑_v √P_{uv} |v⟩`
  (`idealRowA`) and `∑_w √P_{vw} |w⟩ ⊗ |v⟩` (`idealRowB`), with one common phase `‖c‖ = 1`;
* the setup is within `ε` of `c₀ · √π` (`idealPrep`), `‖c₀‖ = 1`;
* the check is within `ε·‖φ‖` of the phase flip of `Marked` on **every** vector `φ` with blank
  query registers, whatever its configurations;
* structurally, as in `WalkOK`: rows with blank query registers, updates commuting with the
  blank flag; and the row of `u` stays in the block of `u` (`a_block`, `b_block`);
* the absolute gap `δ` of `D` on `√π`'s complement, and `4 ≤ T²δ`.

**The phases are harmless.** The proof compares `S` with a frozen ideal setup for `x` whose
rows are exactly `c·idealRowA`, `c·idealRowB` (Gram matrix `|c|² D = D`) and whose stationary
vector is `c₀·√π` (fixed by `D`, same gap, same stationary masses).

**Conclusions.** With `walkErr T K ε = 4ε · walkUses T K`, where `walkUses` bounds the number of
routine applications of `walkSearch K`:
* if the marked configurations have stationary mass at least `η > 0` and `⌈1/η⌉ ≤ 9^K`, a marked
  configuration is returned with probability at least `2/3 − walkErr`
  (`ApproxWalkOK.two_thirds_sub_le`);
* an unmarked configuration is returned with probability at most `walkErr`
  (`ApproxWalkOK.bad_le`);
* if nothing is marked, `none` is returned with probability at least `1 − walkErr`
  (`ApproxWalkOK.one_sub_le_none`).
The query budget is the one of `WalkSetup.walkSearch_q_le_real`.

Proof plan: the block structure gives a block-diagonal unitary `W_A` with `‖W_A − 1‖ ≤ √2·ε`
carrying each actual row to `c` times its ideal row, and likewise `W_B`. The frozen setup with
updates `W_A·updA`, `W_B·updB`, the exact phase flip, and a preparation of `c₀√π` satisfies
`WalkOK` for `x` and `Marked`, so the library's exact theorems apply to it. Every routine of the
frozen walk keeps the query registers blank, so the check is only ever compared on vectors
with blank query registers. A telescoping hybrid over the routine applications of one pass
bounds the distance of the final states by `2ε` per application, hence each pass's outcome law
by `4ε` per application in total variation, and `firstOf` adds these over the `110` passes.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

/-- **An ideal walk chain on all of `V`**: `P` row-stochastic, `π` a distribution with `√π` fixed
by the discriminant `D_{uv} = √(P_{uv} P_{vu})`. No reversibility or positivity is required:
`π` may vanish on configurations that cannot occur on the input. -/
structure WalkChain (V : Type) [Fintype V] where
  P : Matrix V V ℝ
  π : V → ℝ
  P_nonneg : ∀ u v, 0 ≤ P u v
  P_row : ∀ u, ∑ v, P u v = 1
  π_nonneg : ∀ u, 0 ≤ π u
  π_sum : ∑ u, π u = 1
  fix : ∀ u, ∑ v, Real.sqrt (P u v * P v u) * Real.sqrt (π v) = Real.sqrt (π u)

namespace WalkChain

variable {V : Type} [Fintype V] (Q : WalkChain V)

/-- `√π`. -/
noncomputable def r : V → ℂ := fun u => ((Real.sqrt (Q.π u) : ℝ) : ℂ)

/-- The discriminant `D_{uv} = √(P_{uv} P_{vu})`. -/
noncomputable def disc : Matrix V V ℂ := fun u v => ((Real.sqrt (Q.P u v * Q.P v u) : ℝ) : ℂ)

end WalkChain

variable {ι σ V : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype V] [DecidableEq V]

/-- For a reversible chain, `√(P_{uv} P_{vu}) = √π_u P_{uv} / √π_v`. -/
private lemma wsm_sqrt_PP (M : RevChain V) (u v : V) :
    Real.sqrt (M.P u v * M.P v u) = Real.sqrt (M.π u) * M.P u v / Real.sqrt (M.π v) := by
  have hu := M.π_pos u
  have hv := M.π_pos v
  have hsv := M.sqrt_pos v
  have hPvu : M.P v u = M.π u * M.P u v / M.π v := by
    rw [M.balance u v]; field_simp
  have hsq : M.P u v * M.P v u = (Real.sqrt (M.π u) * M.P u v / Real.sqrt (M.π v)) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hu.le, Real.sq_sqrt hv.le, hPvu]
    ring
  rw [hsq, Real.sqrt_sq]
  exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (M.P_nonneg u v)) hsv.le

/-- **A reversible chain is an ideal walk chain**, with the same discriminant. -/
theorem RevChain.exists_walkChain (M : RevChain V) :
    ∃ Q : WalkChain V, Q.P = M.P ∧ Q.π = M.π ∧ Q.disc = M.disc := by
  refine ⟨{ P := M.P, π := M.π, P_nonneg := M.P_nonneg, P_row := M.P_row
            π_nonneg := fun u => (M.π_pos u).le, π_sum := M.π_sum
            fix := fun u => ?_ }, rfl, rfl, ?_⟩
  · have h := congrFun M.disc_r u
    rw [Matrix.mulVec, dotProduct] at h
    simp only [RevChain.disc, RevChain.r, ← Complex.ofReal_mul, ← Complex.ofReal_sum,
      Complex.ofReal_inj] at h
    simpa only [wsm_sqrt_PP] using h
  · funext u v
    simp only [WalkChain.disc, RevChain.disc, wsm_sqrt_PP]

/-- **The compiled walk depends only on the routines, the start state and the clock length**,
not on the analytical fields `r`, `D`, `δ` of the setup. -/
theorem WalkSetup.walkSearch_congr {S S' : WalkSetup ι σ V} (hP : S.prepV = S'.prepV)
    (hI : S.initV = S'.initV) (hA : S.updA = S'.updA) (hB : S.updB = S'.updB)
    (hM : S.markV = S'.markV) (hT : S.T = S'.T) (K : ℕ) :
    S.walkSearch K = S'.walkSearch K := by
  cases S
  cases S'
  dsimp only at hP hI hA hB hM hT
  subst hP hI hA hB hM hT
  rfl

/-- **The ideal setup state**: `√π`, query registers blank. -/
noncomputable def idealPrep (Q : WalkChain V) : QBasis ι σ V → ℂ := sqrtPiV Q.r

/-- **The ideal row** of `u`: `|u⟩ ⊗ ∑_v √P_{uv} |v⟩`, query registers blank. -/
noncomputable def idealRowA (Q : WalkChain V) (u : V) : QBasis ι σ (V × Option V) → ℂ := fun p =>
  if p.1 = none ∧ p.2.1 = none ∧ p.2.2.1 = u then
    (match p.2.2.2 with
      | some v => ((Real.sqrt (Q.P u v) : ℝ) : ℂ)
      | none => 0)
  else 0

/-- **The ideal row of the other side** for `v`: `∑_w √P_{vw} |w⟩ ⊗ |v⟩`. -/
noncomputable def idealRowB (Q : WalkChain V) (v : V) : QBasis ι σ (V × Option V) → ℂ := fun p =>
  if p.1 = none ∧ p.2.1 = none ∧ p.2.2.2 = some v then ((Real.sqrt (Q.P v p.2.2.1) : ℝ) : ℂ)
  else 0

/-- **The contract of an approximate walk on the input `x`**: an ideal chain `Q` on all of `V`
with absolute gap `δ`, update rows within `ε` of `c` times the ideal rows, the setup within `ε`
of `c₀·√π`, and the check within `ε` of the phase flip of `Marked` on every vector with blank
query registers. -/
structure ApproxWalkOK (S : WalkSetup ι σ V) (x : ι → σ) (Q : WalkChain V) (Marked : V → Prop)
    [DecidablePred Marked] (c c₀ : ℂ) (δ ε : ℝ) : Prop where
  c_norm : ‖c‖ = 1
  c₀_norm : ‖c₀‖ = 1
  δ_pos : 0 < δ
  δ_le : δ ≤ 1
  gap : ∀ y : V → ℂ, qInner Q.r y = 0 → qNormSq (Q.disc *ᵥ y) ≤ (1 - δ) ^ 2 * qNormSq y
  hT : 4 ≤ (S.T : ℝ) ^ 2 * δ
  a_supp : ∀ u, SuppIn {q | QbSys q = true} (S.rowA x u)
  b_supp : ∀ u, SuppIn {q | QbSys q = true} (S.rowB x u)
  a_block : ∀ u, SuppIn {q | q.2.2.1 = u} (S.rowA x u)
  b_block : ∀ u, SuppIn {q | q.2.2.2 = some u} (S.rowB x u)
  updA_comm : S.updA.run x * flagProj QbSys = flagProj QbSys * S.updA.run x
  updB_comm : S.updB.run x * flagProj QbSys = flagProj QbSys * S.updB.run x
  prep_close : qNorm (S.prepV.run x *ᵥ S.initV - c₀ • idealPrep Q) ≤ ε
  rowA_close : ∀ u, qNorm (S.rowA x u - c • idealRowA Q u) ≤ ε
  rowB_close : ∀ v, qNorm (S.rowB x v - c • idealRowB Q v) ≤ ε
  mark_close : ∀ φ : QBasis ι σ V → ℂ, SuppIn {p | p.1 = none ∧ p.2.1 = none} φ →
    qNorm (S.markV.run x *ᵥ φ - phaseFlip (fun p : QBasis ι σ V => p.2.2) Marked φ)
      ≤ ε * qNorm φ

/-- **A bound on the number of routine applications** in `walkSearch K` with clock length `T`:
the budget formula of `walkSearch_q_le` with every routine of length one. -/
def walkUses (T K : ℕ) : ℕ := 110 * (2 + 2 * 3 ^ (K + 2) * (2 + 21 * (2 + 8 * T)))

/-- **The total implementation error** of `walkSearch K`: `4ε` per routine application. -/
def walkErr (T K : ℕ) (ε : ℝ) : ℝ := 4 * ε * walkUses T K

/-! ## Part 1. Closeness of two operators on a support -/

section Close

variable {H : Type} [Fintype H] [DecidableEq H]

/-- `A` is within `e` of the frozen operator `F` on the vectors supported on `G`, and `F`
preserves `G`. -/
private def awk_Close (A F : Matrix H H ℂ) (G : Set H) (e : ℝ) : Prop :=
  0 ≤ e ∧ Preserves F G ∧ ∀ φ, SuppIn G φ → qNorm (A *ᵥ φ - F *ᵥ φ) ≤ e * qNorm φ

/-- **A unitary preserving a coordinate support preserves it under its adjoint too.** -/
private theorem awk_preserves_adj {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) {G : Set H}
    (h : Preserves U G) : Preserves Uᴴ G := by
  classical
  have hent : ∀ p q, q ∈ G → p ∉ G → U p q = 0 := by
    intro p q hq hp
    by_contra hne
    have hs : SuppIn G (qBasis q) := fun r hr => by
      by_contra hrG
      apply hr
      rw [qBasis_apply]
      split_ifs with hrq
      · exact absurd (hrq ▸ hq) hrG
      · rfl
    refine hp (h _ hs p ?_)
    simpa [Matrix.mulVec, dotProduct, qBasis_apply] using hne
  have hUU : U * Uᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  have hUU' : Uᴴ * U = 1 := conjTranspose_mul_self_of_unitary hU
  have hrow : ∀ r, ∑ c, Complex.normSq (U r c) = 1 := fun r => by
    have h1 := congrFun (congrFun hUU r) r
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    have h2 : ((∑ c, Complex.normSq (U r c) : ℝ) : ℂ) = 1 := by
      rw [← h1]; push_cast
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self, mul_comm]; rfl
    exact_mod_cast h2
  have hcol : ∀ c, ∑ r, Complex.normSq (U r c) = 1 := fun c => by
    have h1 := congrFun (congrFun hUU' c) c
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    have h2 : ((∑ r, Complex.normSq (U r c) : ℝ) : ℂ) = 1 := by
      rw [← h1]; push_cast
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self]; rfl
    exact_mod_cast h2
  set Gf := Finset.univ.filter (· ∈ G) with hGf
  have hA : ∑ r ∈ Gf, ∑ c, Complex.normSq (U r c) = Gf.card := by
    simp [hrow]
  have hB : ∑ c ∈ Gf, ∑ r, Complex.normSq (U r c) = Gf.card := by
    simp [hcol]
  have hB' : ∀ c ∈ Gf, ∑ r, Complex.normSq (U r c) = ∑ r ∈ Gf, Complex.normSq (U r c) := by
    intro c hc
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ G)]
    have : ∑ r ∈ Finset.univ.filter (fun r => r ∉ G), Complex.normSq (U r c) = 0 :=
      Finset.sum_eq_zero fun r hr => by
        rw [hent r c (Finset.mem_filter.mp hc).2 (Finset.mem_filter.mp hr).2, map_zero]
    rw [this, add_zero]
  have hA' : ∀ r, ∑ c, Complex.normSq (U r c)
      = ∑ c ∈ Gf, Complex.normSq (U r c)
        + ∑ c ∈ Finset.univ.filter (fun c => c ∉ G), Complex.normSq (U r c) := fun r =>
    (Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ G) _).symm
  have key : ∑ r ∈ Gf, ∑ c ∈ Finset.univ.filter (fun c => c ∉ G), Complex.normSq (U r c)
      = 0 := by
    have e1 : ∑ r ∈ Gf, ∑ c, Complex.normSq (U r c)
        = ∑ r ∈ Gf, ∑ c ∈ Gf, Complex.normSq (U r c)
          + ∑ r ∈ Gf, ∑ c ∈ Finset.univ.filter (fun c => c ∉ G), Complex.normSq (U r c) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun r _ => hA' r
    have e2 : ∑ c ∈ Gf, ∑ r, Complex.normSq (U r c)
        = ∑ r ∈ Gf, ∑ c ∈ Gf, Complex.normSq (U r c) := by
      rw [Finset.sum_congr rfl hB', Finset.sum_comm]
    linarith
  have hzero : ∀ r ∈ G, ∀ c, c ∉ G → U r c = 0 := by
    intro r hr c hc
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => Finset.sum_nonneg
      fun c _ => Complex.normSq_nonneg (U r c))).mp key r
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => Complex.normSq_nonneg (U r c))).mp h1
      c (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    exact Complex.normSq_eq_zero.mp h2
  intro w hw p hp
  by_contra hpG
  apply hp
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases hr : r ∈ G
  · rw [Matrix.conjTranspose_apply, hzero r hr p hpG, star_zero, zero_mul]
  · have : w r = 0 := by by_contra hne; exact hr (hw r hne)
    rw [this, mul_zero]

/-- A larger error bound is still a bound. -/
private lemma awk_Close.mono {A F : Matrix H H ℂ} {G : Set H} {e e' : ℝ} (h : awk_Close A F G e)
    (he : e ≤ e') : awk_Close A F G e' :=
  ⟨h.1.trans he, h.2.1, fun φ hφ =>
    (h.2.2 φ hφ).trans (mul_le_mul_of_nonneg_right he (qNorm_nonneg φ))⟩

/-- An operator preserving the support is within `0` of itself. -/
private lemma awk_Close.exact {U : Matrix H H ℂ} {G : Set H} (hU : Preserves U G) :
    awk_Close U U G 0 :=
  ⟨le_rfl, hU, fun φ _ => by rw [sub_self, qNorm_zero, zero_mul]⟩

/-- **Errors add under products** (`A₁` first). -/
private theorem awk_Close.mul {A₁ F₁ A₂ F₂ : Matrix H H ℂ} {G : Set H} {e₁ e₂ : ℝ}
    (hA₂ : A₂ ∈ Matrix.unitaryGroup H ℂ) (hF₁ : F₁ ∈ Matrix.unitaryGroup H ℂ)
    (h₁ : awk_Close A₁ F₁ G e₁) (h₂ : awk_Close A₂ F₂ G e₂) :
    awk_Close (A₂ * A₁) (F₂ * F₁) G (e₁ + e₂) := by
  refine ⟨add_nonneg h₁.1 h₂.1, h₂.2.1.mul h₁.2.1, fun φ hφ => ?_⟩
  refine (qNorm_mulVec_sub_le hA₂ A₁ F₂ F₁ φ).trans ?_
  have e1 := h₁.2.2 φ hφ
  have e2 := h₂.2.2 (F₁ *ᵥ φ) (h₁.2.1 φ hφ)
  rw [qNorm_mulVec hF₁] at e2
  linarith

/-- **Adjoints keep the error.** -/
private theorem awk_Close.adj {A F : Matrix H H ℂ} {G : Set H} {e : ℝ}
    (hA : A ∈ Matrix.unitaryGroup H ℂ) (hF : F ∈ Matrix.unitaryGroup H ℂ)
    (h : awk_Close A F G e) : awk_Close Aᴴ Fᴴ G e := by
  have hpres := awk_preserves_adj hF h.2.1
  refine ⟨h.1, hpres, fun φ hφ => ?_⟩
  have hFF : F * Fᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hF
    rwa [Matrix.star_eq_conjTranspose] at this
  have h1 : Aᴴ * F * Fᴴ = Aᴴ := by rw [Matrix.mul_assoc, hFF, Matrix.mul_one]
  have h2 : Aᴴ * A * Fᴴ = Fᴴ := by rw [conjTranspose_mul_self_of_unitary hA, Matrix.one_mul]
  have hsplit : Aᴴ *ᵥ φ - Fᴴ *ᵥ φ = Aᴴ *ᵥ (F *ᵥ (Fᴴ *ᵥ φ) - A *ᵥ (Fᴴ *ᵥ φ)) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, h1, h2]
  rw [hsplit, qNorm_mulVec (conjTranspose_mem_qUnitary hA), qNorm_sub_comm]
  have := h.2.2 (Fᴴ *ᵥ φ) (hpres φ hφ)
  rwa [qNorm_mulVec (conjTranspose_mem_qUnitary hF)] at this

/-- **Diagonal operators preserve every support.** -/
private lemma awk_preserves_diagonal (d : H → ℂ) (G : Set H) : Preserves (Matrix.diagonal d) G :=
  fun w hw p hp => hw p fun h0 => hp (by rw [Matrix.mulVec_diagonal, h0, mul_zero])

/-- **Basis permutations preserve a support whose preimages stay inside.** -/
private lemma awk_preserves_of_apply {M : Matrix H H ℂ} {G : Set H} (f : H → H)
    (hM : ∀ ψ p, (M *ᵥ ψ) p = ψ (f p)) (hf : ∀ p, f p ∈ G → p ∈ G) : Preserves M G :=
  fun w hw p hp => hf p (hw (f p) (by rw [← hM w p]; exact hp))

/-- A flag projector commuting with `U` makes `U` preserve the flag. -/
private lemma awk_preserves_of_comm {U : Matrix H H ℂ} {f : H → Bool}
    (hU : U * flagProj f = flagProj f * U) : Preserves U {q | f q = true} := by
  intro w hw
  have hw' : goodPart f (· = true) w = w := by
    funext q
    rw [goodPart_apply]
    split_ifs with hq
    · rfl
    · by_contra hne
      exact hq (hw q (Ne.symm hne))
  have hU' : U *ᵥ w = goodPart f (· = true) (U *ᵥ w) := by
    rw [← flagProj_mulVec, Matrix.mulVec_mulVec, ← hU, ← Matrix.mulVec_mulVec, flagProj_mulVec,
      hw']
  intro q hq
  by_contra hQ
  apply hq
  rw [hU', goodPart_apply]
  simp only [Set.mem_ofPred_eq] at hQ
  simp [hQ]

/-- **One hybrid step**: an actual unitary applied to the actual state, against the frozen
operator applied to a frozen state in the support. -/
private lemma awk_hybrid_step {A F : Matrix H H ℂ} {G : Set H} {e : ℝ}
    (hA : A ∈ Matrix.unitaryGroup H ℂ) (h : awk_Close A F G e) {ψ ψ' : H → ℂ}
    (hψ' : SuppIn G ψ') :
    qNorm (A *ᵥ ψ - F *ᵥ ψ') ≤ qNorm (ψ - ψ') + e * qNorm ψ' ∧ SuppIn G (F *ᵥ ψ') := by
  refine ⟨?_, h.2.1 ψ' hψ'⟩
  have hsplit : A *ᵥ ψ - F *ᵥ ψ' = A *ᵥ (ψ - ψ') + (A *ᵥ ψ' - F *ᵥ ψ') := by
    rw [Matrix.mulVec_sub]; abel
  rw [hsplit]
  refine (qNorm_add_le _ _).trans ?_
  rw [qNorm_mulVec hA]
  linarith [h.2.2 ψ' hψ']

end Close

section KronClose

variable {β γ δ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] [Fintype δ]
  [DecidableEq δ]

/-- Pythagoras over the environment sectors of a factorization. -/
private lemma awk_qNormSq_kSector (eq : β ≃ γ × δ) (ψ : β → ℂ) :
    qNormSq ψ = ∑ d, qNormSq (kSector eq d ψ) := by
  rw [qNormSq_def, ← Equiv.sum_comp eq.symm, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- The lifted operator acts on each environment sector. -/
private lemma awk_kSector_kronLift (eq : β ≃ γ × δ) (M : Matrix γ γ ℂ) (ψ : β → ℂ) (d : δ) :
    kSector eq d (QuantumQueryComplexity.kronLift eq M *ᵥ ψ) = M *ᵥ kSector eq d ψ := by
  conv_lhs => rw [eq_sum_splitVec_kSector eq ψ]
  rw [Matrix.mulVec_sum]
  simp only [kronLift_mulVec_splitVec]
  funext c
  simp only [kSector, Finset.sum_apply, splitVec_apply, Equiv.apply_symm_apply]
  rw [Finset.sum_eq_single d]
  · simp [qBasis]
  · intro d' _ hd'
    simp [qBasis, Pi.single_eq_of_ne (Ne.symm hd')]
  · simp

/-- **Closeness lifts along a factorization.** -/
private theorem awk_Close.kronLift (eq : β ≃ γ × δ) (P : δ → Prop)
    {A F : Matrix γ γ ℂ} {Gγ : Set γ} {er : ℝ} (h : awk_Close A F Gγ er) :
    awk_Close (QuantumQueryComplexity.kronLift eq A) (QuantumQueryComplexity.kronLift eq F)
      {p | (eq p).1 ∈ Gγ ∧ P (eq p).2} er := by
  refine ⟨h.1, preserves_kronLift eq h.2.1 P, fun ψ hψ => ?_⟩
  have hsec : ∀ d, qNormSq (A *ᵥ kSector eq d ψ - F *ᵥ kSector eq d ψ)
      ≤ er ^ 2 * qNormSq (kSector eq d ψ) := by
    intro d
    by_cases hd : P d
    · have hs : SuppIn Gγ (kSector eq d ψ) := fun c hc => by
        have := (hψ _ hc).1
        rwa [Equiv.apply_symm_apply] at this
      have := h.2.2 _ hs
      rw [← qNorm_sq, ← qNorm_sq, ← mul_pow]
      exact pow_le_pow_left₀ (qNorm_nonneg _) this 2
    · have h0 : kSector eq d ψ = 0 := by
        funext c
        by_contra hc
        exact hd (by have := (hψ _ hc).2; rwa [Equiv.apply_symm_apply] at this)
      rw [h0]
      simp
  refine qNorm_le_of_qNormSq_le (mul_nonneg h.1 (qNorm_nonneg _)) ?_
  rw [awk_qNormSq_kSector eq (QuantumQueryComplexity.kronLift eq A *ᵥ ψ
    - QuantumQueryComplexity.kronLift eq F *ᵥ ψ), mul_pow, qNorm_sq, awk_qNormSq_kSector eq ψ,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  have hlin : kSector eq d (QuantumQueryComplexity.kronLift eq A *ᵥ ψ
      - QuantumQueryComplexity.kronLift eq F *ᵥ ψ)
      = A *ᵥ kSector eq d ψ - F *ᵥ kSector eq d ψ := by
    rw [← awk_kSector_kronLift, ← awk_kSector_kronLift]
    rfl
  rw [hlin]
  exact hsec d

end KronClose

/-! ## Part 2. Closeness of two routines -/

section Routines

variable {W : Type} [Fintype W] [DecidableEq W]

/-- **Two routines are close on a support** on the input `a`. -/
private def awk_RClose (R R' : QRoutine ι σ W) (a : ι → σ) (G : Set (QBasis ι σ W)) (e : ℝ) :
    Prop :=
  awk_Close (R.run a) (R'.run a) G e

/-- The extra register arbitrary, the rest in `G`. -/
private def awk_Gs (U : Type) (G : Set (QBasis ι σ W)) : Set (QBasis ι σ (U × W)) :=
  {p | (p.1, p.2.1, p.2.2.2) ∈ G}

/-- The parking register blank, the rest in `G` (control bit arbitrary). -/
private def awk_Gc (G : Set (QBasis ι σ W)) : Set (QBasis ι σ (CtrlWork ι W)) :=
  {p | p.2.2.2.1 = none ∧ (p.1, p.2.1, p.2.2.2.2) ∈ G}

variable {R R' R₁ R₁' R₂ R₂' : QRoutine ι σ W} {a : ι → σ} {G G' : Set (QBasis ι σ W)}
  {e e' e₁ e₂ : ℝ}

/-- Rewrite the error bound. -/
private lemma awk_RClose.of_eq (h : awk_RClose R R' a G e) (he : e = e') : awk_RClose R R' a G e' :=
  he ▸ h

/-- Rewrite the support. -/
private lemma awk_RClose.congr_set (h : awk_RClose R R' a G e) (hG : G = G') :
    awk_RClose R R' a G' e :=
  hG ▸ h

/-- A routine preserving the support is within `0` of itself. -/
private lemma awk_RClose.self (R : QRoutine ι σ W) (h : Preserves (R.run a) G) :
    awk_RClose R R a G 0 :=
  awk_Close.exact h

/-- **Errors add under composition** (`R₁` first). -/
private lemma awk_RClose.comp (h₁ : awk_RClose R₁ R₁' a G e₁) (h₂ : awk_RClose R₂ R₂' a G e₂) :
    awk_RClose (R₁.comp R₂) (R₁'.comp R₂') a G (e₁ + e₂) := by
  unfold awk_RClose
  rw [QRoutine.comp_run, QRoutine.comp_run]
  exact awk_Close.mul (R₂.run_mem_unitaryGroup a) (R₁'.run_mem_unitaryGroup a) h₁ h₂

/-- **Inverses keep the error.** -/
private lemma awk_RClose.inv (h : awk_RClose R R' a G e) : awk_RClose R.inv R'.inv a G e := by
  unfold awk_RClose
  rw [QRoutine.inv_run, QRoutine.inv_run]
  exact h.adj (R.run_mem_unitaryGroup a) (R'.run_mem_unitaryGroup a)

/-- `liftReg` is a `kronLift` along `regEquiv`. -/
private lemma awk_liftReg_eq_kronLift (U : Type) [Fintype U] [DecidableEq U]
    (M : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ) :
    QuantumQueryComplexity.liftReg U M = QuantumQueryComplexity.kronLift regEquiv M := by
  ext p q
  simp only [QuantumQueryComplexity.liftReg, blockFam, QuantumQueryComplexity.kronLift,
    Matrix.submatrix_apply, Matrix.blockDiagonal_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply]
  split_ifs <;> simp

/-- **Closeness lifts past an extra register.** -/
private theorem awk_Close.liftReg (U : Type) [Fintype U] [DecidableEq U] (P : U → Prop)
    {A F : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ} (h : awk_Close A F G e) :
    awk_Close (QuantumQueryComplexity.liftReg U A) (QuantumQueryComplexity.liftReg U F)
      {p : QBasis ι σ (U × W) | (p.1, p.2.1, p.2.2.2) ∈ G ∧ P p.2.2.1} e := by
  rw [awk_liftReg_eq_kronLift, awk_liftReg_eq_kronLift]
  exact awk_Close.kronLift regEquiv P h

/-- Routine closeness lifts past an extra register. -/
private lemma awk_RClose.liftReg (U : Type) [Fintype U] [DecidableEq U] (P : U → Prop)
    (h : awk_RClose R R' a G e) :
    awk_RClose (R.liftReg U) (R'.liftReg U) a
      {p : QBasis ι σ (U × W) | (p.1, p.2.1, p.2.2.2) ∈ G ∧ P p.2.2.1} e := by
  unfold awk_RClose
  rw [QRoutine.liftReg_run, QRoutine.liftReg_run]
  exact awk_Close.liftReg U P h

/-- Routine closeness lifts past an extra register left arbitrary. -/
private lemma awk_RClose.liftReg' (U : Type) [Fintype U] [DecidableEq U]
    (h : awk_RClose R R' a G e) : awk_RClose (R.liftReg U) (R'.liftReg U) a (awk_Gs U G) e :=
  (h.liftReg U (fun _ => True)).congr_set (by ext p; simp [awk_Gs])

/-- Routine closeness lifts past the control bit and the blank parking register. -/
private lemma awk_RClose.liftCtrl (h : awk_RClose R R' a G e) :
    awk_RClose (liftCtrl R) (liftCtrl R') a (awk_Gc G) e :=
  ((h.liftReg (Option ι) (· = none)).liftReg Bool (fun _ => True)).congr_set (by
    ext p; simp [awk_Gc, and_comm])

/-- The control sector `b` of a vector on `CtrlWork ι W`, parking register blank. -/
private def awk_ctrlSec (b : Bool) (φ : QBasis ι σ (CtrlWork ι W) → ℂ) : QBasis ι σ W → ℂ :=
  fun q => φ (q.1, q.2.1, (b, none, q.2.2))

/-- Re-embedding a control sector restricts to that control value. -/
private lemma awk_embedCtrl_ctrlSec {φ : QBasis ι σ (CtrlWork ι W) → ℂ} (hφ : SuppIn (awk_Gc G) φ)
    (b : Bool) :
    embedCtrl b (awk_ctrlSec b φ)
      = qRestrict (fun p : QBasis ι σ (CtrlWork ι W) => p.2.2.1) b φ := by
  funext p
  obtain ⟨k, t, b', pk, w⟩ := p
  rw [embedCtrl_apply]
  simp only [qRestrict, awk_ctrlSec]
  by_cases hb : b' = b
  · subst hb
    by_cases hpk : pk = none
    · subst hpk
      simp
    · have h0 : φ (k, t, (b', pk, w)) = 0 := by
        by_contra hne
        exact hpk (hφ _ hne).1
      simp [hpk, h0]
  · simp [hb]

/-- A parking-blank vector is the sum of its two control sectors. -/
private lemma awk_eq_ctrlSec {φ : QBasis ι σ (CtrlWork ι W) → ℂ} (hφ : SuppIn (awk_Gc G) φ) :
    φ = embedCtrl true (awk_ctrlSec true φ) + embedCtrl false (awk_ctrlSec false φ) := by
  rw [awk_embedCtrl_ctrlSec hφ, awk_embedCtrl_ctrlSec hφ]
  funext p
  obtain ⟨k, t, b, pk, w⟩ := p
  simp only [Pi.add_apply, qRestrict]
  cases b <;> simp

/-- The control sectors of a vector of `awk_Gc G` lie in `G`. -/
private lemma awk_ctrlSec_supp {φ : QBasis ι σ (CtrlWork ι W) → ℂ} (hφ : SuppIn (awk_Gc G) φ)
    (b : Bool) : SuppIn G (awk_ctrlSec b φ) := fun _ hq => (hφ _ hq).2

/-- Embedding a vector of `G` with a blank parking register lands in `awk_Gc G`. -/
private lemma awk_embedCtrl_supp {χ : QBasis ι σ W → ℂ} (hχ : SuppIn G χ) (b : Bool) :
    SuppIn (awk_Gc G) (embedCtrl b χ) := by
  intro p hp
  rw [embedCtrl_apply] at hp
  split_ifs at hp with h1
  · exact ⟨h1.2, hχ _ hp⟩
  · exact absurd rfl hp

/-- `embedCtrl` is an isometry. -/
private lemma awk_qNorm_embedCtrl (b : Bool) (χ : QBasis ι σ W → ℂ) :
    qNorm (embedCtrl b χ) = qNorm χ := by
  rw [qNorm, qNorm, qNormSq_embedCtrl]

/-- A control sector is no longer than the vector. -/
private lemma awk_qNorm_ctrlSec_le {φ : QBasis ι σ (CtrlWork ι W) → ℂ} (hφ : SuppIn (awk_Gc G) φ)
    (b : Bool) : qNorm (awk_ctrlSec b φ) ≤ qNorm φ := by
  have := qNorm_qRestrict_le (fun p : QBasis ι σ (CtrlWork ι W) => p.2.2.1) b φ
  rwa [← awk_embedCtrl_ctrlSec hφ, awk_qNorm_embedCtrl] at this

/-- **Closeness passes to controlled routines**, on parking-blank vectors. -/
private theorem awk_RClose.control (h : awk_RClose R R' a G e) :
    awk_RClose R.control R'.control a (awk_Gc G) e := by
  refine ⟨h.1, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · rw [awk_eq_ctrlSec hφ, Matrix.mulVec_add, control_run_true, control_run_false]
    exact (awk_embedCtrl_supp (h.2.1 _ (awk_ctrlSec_supp hφ true)) true).add
      (awk_embedCtrl_supp (awk_ctrlSec_supp hφ false) false)
  · have hd : R.control.run a *ᵥ φ - R'.control.run a *ᵥ φ
        = embedCtrl true (R.run a *ᵥ awk_ctrlSec true φ - R'.run a *ᵥ awk_ctrlSec true φ) := by
      conv_lhs => rw [awk_eq_ctrlSec hφ]
      rw [Matrix.mulVec_add, Matrix.mulVec_add, control_run_true, control_run_false,
        control_run_true, control_run_false, embedCtrl_sub]
      abel
    rw [hd, awk_qNorm_embedCtrl]
    exact (h.2.2 _ (awk_ctrlSec_supp hφ true)).trans
      (mul_le_mul_of_nonneg_left (awk_qNorm_ctrlSec_le hφ true) h.1)

/-- Routine closeness lifts along an oracle-compatible factorization. -/
private lemma awk_RClose.kronLift {W' D : Type} [Fintype W'] [DecidableEq W'] [Fintype D]
    [DecidableEq D] {eq : QBasis ι σ W' ≃ QBasis ι σ W × D} (he : OracleCompat eq)
    (P : D → Prop) (h : awk_RClose R R' a G e) :
    awk_RClose (R.kronLift eq) (R'.kronLift eq) a {p | (eq p).1 ∈ G ∧ P (eq p).2} e := by
  unfold awk_RClose
  rw [QRoutine.kronLift_run he, QRoutine.kronLift_run he]
  exact awk_Close.kronLift eq P h

/-- Conjugating a fixed unitary by close routines doubles the error. -/
private lemma awk_RClose.conjFixed (h : awk_RClose R R' a G e)
    {U : Matrix (QBasis ι σ W) (QBasis ι σ W) ℂ} (hU : U ∈ Matrix.unitaryGroup _ ℂ)
    (hUG : Preserves U G) : awk_RClose (R.conjFixed U hU) (R'.conjFixed U hU) a G (2 * e) :=
  ((h.comp (awk_RClose.self (QRoutine.ofUnitary U hU) hUG)).comp h.inv).of_eq (by ring)

end Routines

/-! ## Part 3. The clock and the level routine -/

section Level

variable {W : Type} [Fintype W] [DecidableEq W] {R R' : QRoutine ι σ W} {a : ι → σ}
  {G : Set (QBasis ι σ W)} {e : ℝ}

/-- The clock bit flip preserves the level support. -/
private lemma awk_preserves_clockXorMat (N j : ℕ) :
    Preserves (clockXorMat (ι := ι) (σ := σ) (W := W) (T := N) j)
      (awk_Gc (awk_Gs (Fin N) G)) :=
  awk_preserves_of_apply _ (clockXorMat_mulVec_apply j) (fun _ hp => hp)

/-- An operator on the clock register preserves the level support. -/
private lemma awk_preserves_clockReg {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    Preserves (QuantumQueryComplexity.liftReg Bool
      (QuantumQueryComplexity.liftReg (Option ι) (regOp (ι := ι) (σ := σ) (W := W) A)))
      (awk_Gc (awk_Gs (Fin N) G)) :=
  Preserves.congr_set (preserves_liftReg' (preserves_liftReg' (preserves_regOp A G) (· = none))
    (fun _ => True)) (by ext p; simp [awk_Gc, awk_Gs, and_comm])

/-- One clocked round: the error of one application of the routine. -/
private lemma awk_RClose.clockRound (h : awk_RClose R R' a G e) (N j : ℕ) :
    awk_RClose (clockRound R N j) (clockRound R' N j) a (awk_Gc (awk_Gs (Fin N) G)) e := by
  have hc := (h.liftReg' (Fin N)).control
  have hx := awk_RClose.self (a := a) (G := awk_Gc (awk_Gs (Fin N) G))
    (QRoutine.ofUnitary (clockXorMat (ι := ι) (σ := σ) (W := W) (T := N) j)
      (clockXorMat_mem_unitaryGroup j)) (awk_preserves_clockXorMat (G := G) N j)
  exact ((hx.comp hc).comp hx).of_eq (by ring)

/-- The first `n` clocked rounds: `n` applications. -/
private lemma awk_RClose.selectUpto (h : awk_RClose R R' a G e) (N n : ℕ) :
    awk_RClose (selectUpto R N n) (selectUpto R' N n) a (awk_Gc (awk_Gs (Fin N) G))
      (n * e) := by
  induction n with
  | zero =>
      exact (awk_RClose.self (QRoutine.identity) (preserves_one _)).of_eq (by
        rw [Nat.cast_zero, zero_mul])
  | succ n ih =>
      exact (ih.comp (h.clockRound N (n + 1))).of_eq (by push_cast; ring)

/-- Coherent powers: `N − 1` applications. -/
private lemma awk_RClose.selectPowers (h : awk_RClose R R' a G e) (N : ℕ) :
    awk_RClose (selectPowers R N) (selectPowers R' N) a (awk_Gc (awk_Gs (Fin N) G))
      ((N - 1 : ℕ) * e) :=
  h.selectUpto N (N - 1)

/-- The weighted detector: `2(N − 1)` applications. -/
private lemma awk_RClose.wDetector (h : awk_RClose R R' a G e) (N : ℕ) {α : Fin N → ℂ}
    (hα : IsQState α) :
    awk_RClose (wDetector R N hα) (wDetector R' N hα) a (awk_Gc (awk_Gs (Fin N) G))
      (2 * ((N - 1 : ℕ) * e)) :=
  (h.selectPowers N).conjFixed _ (LevelData.preserves_qRefl (awk_preserves_clockReg _))

/-- **The level routine**: `2` updates and `2k(T−1)` walk steps. -/
private theorem awk_RClose.lvlRoutine {upd upd' walkR walkR' : QRoutine ι σ W} {eU eW : ℝ}
    (hU : awk_RClose upd upd' a G eU) (hW : awk_RClose walkR walkR' a G eW) (T k : ℕ)
    (hT0 : 0 < T) :
    awk_RClose (lvlRoutine upd walkR T k hT0) (lvlRoutine upd' walkR' T k hT0) a
      (awk_Gc (awk_Gs (Fin (k * (T - 1) + 1)) G)) (2 * eU + 2 * ((k * (T - 1) : ℕ) * eW)) := by
  have hL : awk_RClose (liftClk (k * (T - 1) + 1) upd) (liftClk (k * (T - 1) + 1) upd') a
      (awk_Gc (awk_Gs (Fin (k * (T - 1) + 1)) G)) eU := (hU.liftReg' _).liftCtrl
  have hP := awk_RClose.self (a := a) (LevelData.prepR (ι := ι) (σ := σ) (W := W) T k hT0)
    (awk_preserves_clockReg (G := G) _)
  have hPH := awk_RClose.self (a := a) (G := awk_Gc (awk_Gs (Fin (k * (T - 1) + 1)) G))
    (LevelData.prepRH (ι := ι) (σ := σ) (W := W) T k hT0) (by
      change Preserves (clockPrep (kClock T k) (LevelData.t0 T k))ᴴ _
      rw [clockPrep, liftReg_conjTranspose, liftReg_conjTranspose, regOp_conjTranspose]
      exact awk_preserves_clockReg _)
  have hD := hW.wDetector (k * (T - 1) + 1) (isQState_kClock hT0 k)
  exact (hL.comp (hP.comp (hD.comp (hPH.comp hL.inv)))).of_eq (by
    rw [Nat.add_sub_cancel]; ring)

end Level

/-! ## Part 4. The compiled recursion and the pass -/

section Pass

variable {W : Type} [Fintype W] [DecidableEq W] {a : ι → σ} {G : Set (QBasis ι σ W)}

/-- The error of the compiled level `j` (cf. `chainLen`). -/
private def awk_chainErr (eM : ℝ) (eR : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => 3 * awk_chainErr eM eR j + eM + eR (j + 1)

/-- The error of a pass through the check of stage `j` (cf. `passLen`). -/
private def awk_passErr (eP eM : ℝ) (eR : ℕ → ℝ) : ℕ → ℝ
  | 0 => eP + eM
  | j + 1 => awk_passErr eP eM eR j + (2 * awk_chainErr eM eR j + eR (j + 1)) + eM

/-- With unit errors `2ε`, the chain error is `2ε` times `chainLen`. -/
private lemma awk_chainErr_unit (ε : ℝ) (r : ℕ → ℕ) (j : ℕ) :
    awk_chainErr (2 * ε) (fun l => 2 * ε * r l) j = 2 * ε * chainLen 1 r j := by
  induction j with
  | zero => simp [awk_chainErr, chainLen]
  | succ j ih => rw [awk_chainErr, ih, chainLen]; push_cast; ring

/-- With unit errors `2ε`, the pass error is `2ε` times `passLen`. -/
private lemma awk_passErr_unit (ε : ℝ) (r : ℕ → ℕ) (j : ℕ) :
    awk_passErr (2 * ε) (2 * ε) (fun l => 2 * ε * r l) j = 2 * ε * passLen 1 1 r j := by
  induction j with
  | zero => simp [awk_passErr, passLen]; ring
  | succ j ih => rw [awk_passErr, ih, awk_chainErr_unit, passLen]; push_cast; ring

/-- The control-bit flag flip preserves the support. -/
private lemma awk_preserves_flagXorMat (c : QBasis ι σ W → Bool) :
    Preserves (flagXorMat c) (awk_Gc G) :=
  awk_preserves_of_apply _ (flagXorMat_mulVec_apply c) (fun _ hp => hp)

/-- The clean-history reflection: the error of the reflection routine. -/
private lemma awk_RClose.cleanRefl {R R' : QRoutine ι σ W} {e : ℝ} (c : QBasis ι σ W → Bool)
    (h : awk_RClose R R' a G e) :
    awk_RClose (cleanRefl c R) (cleanRefl c R') a (awk_Gc G) e := by
  have hx := awk_RClose.self (a := a)
    (QRoutine.ofUnitary (flagXorMat c) (flagXorMat_mem_unitaryGroup c))
    (awk_preserves_flagXorMat (G := G) c)
  have hd := awk_RClose.self (a := a) (G := awk_Gc G)
    (QRoutine.ofUnitary (dirtySignMat c) (dirtySignMat_mem_unitaryGroup c))
    (awk_preserves_diagonal _ _)
  exact (hx.comp (h.control.comp (hx.comp hd))).of_eq (by ring)

variable {mark mark' : QRoutine ι σ W} {refl refl' : ℕ → QRoutine ι σ W}
  {clean : ℕ → QBasis ι σ W → Bool} {eM : ℝ} {eR : ℕ → ℝ}

/-- The compiled level `j`: error `awk_chainErr`. -/
private lemma awk_RClose.chainR (hM : awk_RClose mark mark' a G eM)
    (hR : ∀ l, awk_RClose (refl l) (refl' l) a G (eR l)) (j : ℕ) :
    awk_RClose (chainR mark refl clean j) (chainR mark' refl' clean j) a (awk_Gc G)
      (awk_chainErr eM eR j) := by
  induction j with
  | zero => exact (awk_RClose.self QRoutine.identity (preserves_one _)).of_eq rfl
  | succ j ih =>
      exact (ih.comp (hM.liftCtrl.comp (ih.inv.comp (((hR (j + 1)).cleanRefl
        (clean j)).comp ih)))).of_eq (by rw [awk_chainErr]; ring)

/-- The compiled stage `j`: two levels and one reflection. -/
private lemma awk_RClose.stageR (hM : awk_RClose mark mark' a G eM)
    (hR : ∀ l, awk_RClose (refl l) (refl' l) a G (eR l)) (j : ℕ) :
    awk_RClose (stageR mark refl clean j) (stageR mark' refl' clean j) a (awk_Gc G)
      (2 * awk_chainErr eM eR j + eR (j + 1)) := by
  have ih := awk_RClose.chainR (clean := clean) hM hR j
  exact (ih.inv.comp (((hR (j + 1)).cleanRefl (clean j)).comp ih)).of_eq (by ring)

/-- The Hadamard test of the marker: the error of the marker. -/
private lemma awk_RClose.flagRoutine (hM : awk_RClose mark mark' a G eM) :
    awk_RClose (flagRoutine mark) (flagRoutine mark') a (awk_Gc G) eM := by
  have hh := awk_RClose.self (a := a) (G := awk_Gc G)
    (QRoutine.ofUnitary ctrlHad ctrlHad_mem_unitaryGroup)
    (preserves_regOp hadMat {q : QBasis ι σ (Option ι × W) | q.2.2.1 = none
      ∧ (q.1, q.2.1, q.2.2.2) ∈ G})
  exact (hh.comp (hM.control.comp hh)).of_eq (by ring)

/-- Recording preserves the pass support. -/
private lemma awk_preserves_recordMat {N : ℕ} (vtx : QBasis ι σ W → V) (j : Fin N) :
    Preserves (recordMat vtx j) (awk_Gs (Slots N V) (awk_Gc G)) :=
  awk_preserves_of_apply _ (recordMat_mulVec_apply vtx j) (by
    rintro ⟨k, t, sl, b, pk, w⟩ hp
    exact hp)

/-- Check and record: the error of the marker. -/
private lemma awk_RClose.chkRec {N : ℕ} (vtx : QBasis ι σ W → V) (j : Fin N)
    (hM : awk_RClose mark mark' a G eM) :
    awk_RClose (chkRec mark vtx j) (chkRec mark' vtx j) a (awk_Gs (Slots N V) (awk_Gc G)) eM :=
  ((hM.flagRoutine.liftReg' (Slots N V)).comp (awk_RClose.self (a := a)
    (QRoutine.ofUnitary (recordMat vtx j) (recordMat_mem_unitaryGroup vtx j))
    (awk_preserves_recordMat vtx j))).of_eq (by ring)

/-- `embedReg` commutes with subtraction. -/
private lemma awk_embedReg_sub {U : Type} [Fintype U] [DecidableEq U] (u : U)
    (φ χ : QBasis ι σ W → ℂ) : embedReg u (φ - χ) = embedReg u φ - embedReg u χ := by
  funext p
  simp only [Pi.sub_apply, embedReg_apply]
  split_ifs <;> simp

/-- **The hybrid argument for one pass**: the actual and frozen final states differ by at
most the summed errors of the routine applications. -/
private theorem awk_pass_close {prep prep' : QRoutine ι σ W} {vtx : QBasis ι σ W → V}
    {init : QBasis ι σ W → ℂ} (hinit : IsQState init) {eP : ℝ}
    (hP : qNorm (prep.run a *ᵥ init - prep'.run a *ᵥ init) ≤ eP)
    (hPs : SuppIn G (prep'.run a *ᵥ init))
    (hM : awk_RClose mark mark' a G eM) (hR : ∀ l, awk_RClose (refl l) (refl' l) a G (eR l))
    {N : ℕ} (j : ℕ) (hj : j < N) :
    qNorm ((passUpTo (N := N) prep mark refl clean vtx j hj).run a
        *ᵥ embedReg (emptySlots N V) (embedCtrl false init)
      - (passUpTo (N := N) prep' mark' refl' clean vtx j hj).run a
        *ᵥ embedReg (emptySlots N V) (embedCtrl false init)) ≤ awk_passErr eP eM eR j := by
  have hn0 : qNorm (embedReg (emptySlots N V) (embedCtrl false init)) = 1 := by
    rw [qNorm, qNormSq_embedReg, qNormSq_embedCtrl, hinit, Real.sqrt_one]
  suffices H : ∀ j (hj : j < N),
      qNorm ((passUpTo (N := N) prep mark refl clean vtx j hj).run a
          *ᵥ embedReg (emptySlots N V) (embedCtrl false init)
        - (passUpTo (N := N) prep' mark' refl' clean vtx j hj).run a
          *ᵥ embedReg (emptySlots N V) (embedCtrl false init)) ≤ awk_passErr eP eM eR j
      ∧ SuppIn (awk_Gs (Slots N V) (awk_Gc G))
        ((passUpTo (N := N) prep' mark' refl' clean vtx j hj).run a
          *ᵥ embedReg (emptySlots N V) (embedCtrl false init)) from (H j hj).1
  intro j
  induction j with
  | zero =>
      intro hj
      have hC := awk_RClose.chkRec (N := N) vtx ⟨0, hj⟩ hM
      have hs : SuppIn (awk_Gs (Slots N V) (awk_Gc G))
          (embedReg (emptySlots N V) (embedCtrl false (prep'.run a *ᵥ init))) := by
        intro p hp
        rw [embedReg_apply] at hp
        split_ifs at hp with h1
        · rw [embedCtrl_apply] at hp
          split_ifs at hp with h2
          · exact ⟨h2.2, hPs _ hp⟩
          · exact absurd rfl hp
        · exact absurd rfl hp
      have hd : qNorm (embedReg (emptySlots N V) (embedCtrl false (prep.run a *ᵥ init))
          - embedReg (emptySlots N V) (embedCtrl false (prep'.run a *ᵥ init))) ≤ eP := by
        rw [← awk_embedReg_sub, ← embedCtrl_sub, qNorm, qNormSq_embedReg, qNormSq_embedCtrl]
        exact hP
      have hn : qNorm (embedReg (emptySlots N V) (embedCtrl false (prep'.run a *ᵥ init)))
          = 1 := by
        rw [qNorm, qNormSq_embedReg, qNormSq_embedCtrl, qNormSq_mulVec
          (prep'.run_mem_unitaryGroup a), hinit, Real.sqrt_one]
      obtain ⟨h1, h2⟩ := awk_hybrid_step (QRoutine.run_mem_unitaryGroup _ a) hC hs
        (ψ := embedReg (emptySlots N V) (embedCtrl false (prep.run a *ᵥ init)))
      have heq : ∀ (pr mk : QRoutine ι σ W) (rf : ℕ → QRoutine ι σ W),
          passUpTo (N := N) pr mk rf clean vtx 0 hj
            = ((liftCtrl pr).liftReg (Slots N V)).comp (chkRec mk vtx ⟨0, hj⟩) :=
        fun _ _ _ => rfl
      have hrun : ∀ (pr mk : QRoutine ι σ W) (rf : ℕ → QRoutine ι σ W),
          (passUpTo (N := N) pr mk rf clean vtx 0 hj).run a
            *ᵥ embedReg (emptySlots N V) (embedCtrl false init)
          = (chkRec mk vtx ⟨0, hj⟩).run a
            *ᵥ embedReg (emptySlots N V) (embedCtrl false (pr.run a *ᵥ init)) :=
        fun pr mk rf => by
          rw [heq, QRoutine.comp_run ((liftCtrl pr).liftReg (Slots N V)) _ a,
            ← Matrix.mulVec_mulVec, QRoutine.liftReg_run_embed, liftCtrl_run]
      rw [hrun, hrun]
      refine ⟨h1.trans ?_, h2⟩
      rw [hn, awk_passErr]
      linarith
  | succ j ih =>
      intro hj
      obtain ⟨ih1, ih2⟩ := ih (Nat.lt_of_succ_lt hj)
      have hX := ((awk_RClose.stageR (clean := clean) hM hR j).liftReg' (Slots N V)).comp
        (awk_RClose.chkRec (N := N) vtx ⟨j + 1, hj⟩ hM)
      obtain ⟨h1, h2⟩ := awk_hybrid_step (QRoutine.run_mem_unitaryGroup _ a) hX ih2
        (ψ := (passUpTo (N := N) prep mark refl clean vtx j (Nat.lt_of_succ_lt hj)).run a
          *ᵥ embedReg (emptySlots N V) (embedCtrl false init))
      have hn : qNorm ((passUpTo (N := N) prep' mark' refl' clean vtx j
          (Nat.lt_of_succ_lt hj)).run a *ᵥ embedReg (emptySlots N V) (embedCtrl false init))
          = 1 := by
        rw [qNorm_mulVec (QRoutine.run_mem_unitaryGroup _ a), hn0]
      have heq : ∀ (pr mk : QRoutine ι σ W) (rf : ℕ → QRoutine ι σ W),
          passUpTo (N := N) pr mk rf clean vtx (j + 1) hj
            = (passUpTo pr mk rf clean vtx j (Nat.lt_of_succ_lt hj)).comp
              (((stageR mk rf clean j).liftReg (Slots N V)).comp (chkRec mk vtx ⟨j + 1, hj⟩)) :=
        fun _ _ _ => rfl
      have hrun : ∀ (pr mk : QRoutine ι σ W) (rf : ℕ → QRoutine ι σ W),
          (passUpTo (N := N) pr mk rf clean vtx (j + 1) hj).run a
            *ᵥ embedReg (emptySlots N V) (embedCtrl false init)
          = (((stageR mk rf clean j).liftReg (Slots N V)).comp (chkRec mk vtx ⟨j + 1, hj⟩)).run a
            *ᵥ ((passUpTo pr mk rf clean vtx j (Nat.lt_of_succ_lt hj)).run a
              *ᵥ embedReg (emptySlots N V) (embedCtrl false init)) := fun pr mk rf => by
        rw [heq, QRoutine.comp_run (passUpTo pr mk rf clean vtx j _) _ a,
          ← Matrix.mulVec_mulVec]
      rw [hrun, hrun]
      refine ⟨h1.trans ?_, h2⟩
      rw [hn, awk_passErr]
      linarith

end Pass

/-! ## Part 5. Outcome laws -/

section Laws

variable {O : Type} [Fintype O] [DecidableEq O]

/-- The `ℓ¹` distance of the outcome laws of two trials on the input `a`. -/
private noncomputable def awk_tv (T T' : OTrial ι σ O) (a : ι → σ) : ℝ :=
  ∑ o, |T.pr a o - T'.pr a o|

/-- **The distance of first successes is at most the sum of the distances.** -/
private theorem awk_tv_orElse (T₁ T₁' T₂ T₂' : OTrial ι σ O) (a : ι → σ) :
    awk_tv (T₁.orElse T₂) (T₁'.orElse T₂') a ≤ awk_tv T₁ T₁' a + awk_tv T₂ T₂' a := by
  have key : ∀ o, |T₁.pr a none * T₂.pr a o - T₁'.pr a none * T₂'.pr a o|
      ≤ |T₁.pr a none - T₁'.pr a none| * T₂.pr a o + |T₂.pr a o - T₂'.pr a o| := by
    intro o
    have e : T₁.pr a none * T₂.pr a o - T₁'.pr a none * T₂'.pr a o
        = (T₁.pr a none - T₁'.pr a none) * T₂.pr a o
          + T₁'.pr a none * (T₂.pr a o - T₂'.pr a o) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
    · rw [abs_mul, abs_of_nonneg (T₂.pr_nonneg a o)]
    · rw [abs_mul, abs_of_nonneg (T₁'.pr_nonneg a none)]
      exact mul_le_of_le_one_left (abs_nonneg _) (T₁'.pr_le_one a none)
  have hsum := Finset.sum_le_sum fun o (_ : o ∈ Finset.univ) => key o
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, T₂.sum_pr a, mul_one] at hsum
  have hy : ∀ y, |T₁.pr a (some y) + T₁.pr a none * T₂.pr a (some y)
      - (T₁'.pr a (some y) + T₁'.pr a none * T₂'.pr a (some y))|
      ≤ |T₁.pr a (some y) - T₁'.pr a (some y)|
        + |T₁.pr a none * T₂.pr a (some y) - T₁'.pr a none * T₂'.pr a (some y)| := fun y => by
    have e : T₁.pr a (some y) + T₁.pr a none * T₂.pr a (some y)
        - (T₁'.pr a (some y) + T₁'.pr a none * T₂'.pr a (some y))
        = (T₁.pr a (some y) - T₁'.pr a (some y))
          + (T₁.pr a none * T₂.pr a (some y) - T₁'.pr a none * T₂'.pr a (some y)) := by ring
    rw [e]
    exact abs_add_le _ _
  have hys := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) => hy y
  rw [Finset.sum_add_distrib] at hys
  unfold awk_tv
  rw [Fintype.sum_option, Fintype.sum_option, Fintype.sum_option, OTrial.pr_orElse_none,
    OTrial.pr_orElse_none]
  simp only [OTrial.pr_orElse_some]
  rw [Fintype.sum_option, Fintype.sum_option] at hsum
  linarith

/-- **`n` repeated passes**: the distances add up. -/
private theorem awk_tv_firstOf_replicate (T T' : OTrial ι σ O) (a : ι → σ) (n : ℕ) :
    awk_tv (OTrial.firstOf (List.replicate n T)) (OTrial.firstOf (List.replicate n T')) a
      ≤ n * awk_tv T T' a := by
  induction n with
  | zero =>
      simp only [List.replicate_zero, OTrial.firstOf, awk_tv, sub_self, abs_zero,
        Finset.sum_const_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
      rw [List.replicate_succ, List.replicate_succ, OTrial.firstOf, OTrial.firstOf]
      refine (awk_tv_orElse _ _ _ _ a).trans ?_
      push_cast
      linarith

/-- `Pr[some valid]` moves by at most the `ℓ¹` distance. -/
private lemma awk_good_ge (G : O → Prop) [DecidablePred G] (T T' : OTrial ι σ O) (a : ι → σ) :
    T'.good G a - awk_tv T T' a ≤ T.good G a := by
  have h1 : T'.good G a - T.good G a ≤ ∑ y, |T.pr a (some y) - T'.pr a (some y)| := by
    rw [OTrial.good, OTrial.good, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun y _ => ?_
    split_ifs
    · rw [abs_sub_comm]
      exact le_abs_self _
    · simp
  have h2 : ∑ y, |T.pr a (some y) - T'.pr a (some y)| ≤ awk_tv T T' a := by
    rw [awk_tv, Fintype.sum_option]
    linarith [abs_nonneg (T.pr a none - T'.pr a none)]
  linarith

/-- `Pr[some invalid]` moves by at most the `ℓ¹` distance. -/
private lemma awk_bad_le (G : O → Prop) [DecidablePred G] (T T' : OTrial ι σ O) (a : ι → σ) :
    T.bad G a ≤ T'.bad G a + awk_tv T T' a := by
  have h1 : T.bad G a - T'.bad G a ≤ ∑ y, |T.pr a (some y) - T'.pr a (some y)| := by
    rw [OTrial.bad, OTrial.bad, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun y _ => ?_
    split_ifs
    · simp
    · exact le_abs_self _
  have h2 : ∑ y, |T.pr a (some y) - T'.pr a (some y)| ≤ awk_tv T T' a := by
    rw [awk_tv, Fintype.sum_option]
    linarith [abs_nonneg (T.pr a none - T'.pr a none)]
  linarith

/-- `Pr[none]` moves by at most the `ℓ¹` distance. -/
private lemma awk_none_ge (T T' : OTrial ι σ O) (a : ι → σ) :
    T'.pr a none - awk_tv T T' a ≤ T.pr a none := by
  have h1 : T'.pr a none - T.pr a none ≤ |T.pr a none - T'.pr a none| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  have h2 : 0 ≤ ∑ y, |T.pr a (some y) - T'.pr a (some y)| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [awk_tv, Fintype.sum_option]
  linarith

/-- **Outcome laws of nearby unit vectors are close in `ℓ¹`.** -/
private theorem awk_sum_abs_qProb_sub_le {H : Type} [Fintype H] [DecidableEq H] (rd : H → O)
    {ψ φ : H → ℂ} (hψ : qNorm ψ = 1) (hφ : qNorm φ = 1) :
    ∑ o, |qProb rd ψ o - qProb rd φ o| ≤ 2 * qNorm (ψ - φ) := by
  have hsq : ∀ χ : H → ℂ, ∑ o, qNorm (qRestrict rd o χ) ^ 2 = qNorm χ ^ 2 := fun χ => by
    simp only [qNorm_sq, ← qProb_eq_qNormSq_qRestrict, sum_qProb]
  have hCS : ∀ χ : H → ℂ, qNorm χ = 1 →
      ∑ o, qNorm (qRestrict rd o (ψ - φ)) * qNorm (qRestrict rd o χ) ≤ qNorm (ψ - φ) := by
    intro χ hχ
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun o => qNorm (qRestrict rd o (ψ - φ))) (fun o => qNorm (qRestrict rd o χ))
    rw [hsq, hsq, hχ, one_pow, mul_one] at h
    nlinarith [qNorm_nonneg (ψ - φ)]
  have hpt : ∀ o, |qProb rd ψ o - qProb rd φ o|
      ≤ qNorm (qRestrict rd o (ψ - φ)) * qNorm (qRestrict rd o ψ)
        + qNorm (qRestrict rd o (ψ - φ)) * qNorm (qRestrict rd o φ) := fun o => by
    rw [qProb_eq_qNormSq_qRestrict, qProb_eq_qNormSq_qRestrict, ← qNorm_sq, ← qNorm_sq]
    have h1 := qNorm_le_add_sub (qRestrict rd o ψ) (qRestrict rd o φ)
    have h2 := qNorm_le_add_sub (qRestrict rd o φ) (qRestrict rd o ψ)
    rw [← qRestrict_sub] at h1 h2
    have h2' : qNorm (qRestrict rd o (φ - ψ)) = qNorm (qRestrict rd o (ψ - φ)) := by
      rw [qRestrict_sub, qRestrict_sub, qNorm_sub_comm]
    rw [h2'] at h2
    have hA := qNorm_nonneg (qRestrict rd o ψ)
    have hB := qNorm_nonneg (qRestrict rd o φ)
    rw [abs_le]
    constructor <;> nlinarith
  calc ∑ o, |qProb rd ψ o - qProb rd φ o|
      ≤ ∑ o, (qNorm (qRestrict rd o (ψ - φ)) * qNorm (qRestrict rd o ψ)
        + qNorm (qRestrict rd o (ψ - φ)) * qNorm (qRestrict rd o φ)) :=
        Finset.sum_le_sum fun o _ => hpt o
    _ ≤ qNorm (ψ - φ) + qNorm (ψ - φ) := by
        rw [Finset.sum_add_distrib]
        exact add_le_add (hCS ψ hψ) (hCS φ hφ)
    _ = 2 * qNorm (ψ - φ) := by ring

end Laws

/-! ## Part 6. The compiled walk, frozen -/

/-- **The walk setup with its routines and analytic data replaced** (same clock, same start
state). -/
private abbrev awk_frozen (S : WalkSetup ι σ V) (P : QRoutine ι σ V)
    (A B : QRoutine ι σ (V × Option V)) (M : QRoutine ι σ V) (r : V → ℂ) (D : Matrix V V ℂ) (δ : ℝ)
    (hT : 4 ≤ (S.T : ℝ) ^ 2 * δ) : WalkSetup ι σ V :=
  { S with prepV := P, updA := A, updB := B, markV := M, r := r, D := D, δ := δ, hT := hT }

/-- The setup with every routine one query long: it counts routine applications. -/
private noncomputable def awk_unit (S : WalkSetup ι σ V) : WalkSetup ι σ V :=
  awk_frozen S QRoutine.query QRoutine.query QRoutine.query QRoutine.query S.r S.D S.δ S.hT

/-- Query registers blank, every block's parking register blank. -/
private def awk_Gg (Lc T : ℕ) (kk : Fin Lc → ℕ) : Set (QBasis ι σ (Wg ι V Lc T kk)) :=
  {p | p.1 = none ∧ p.2.1 = none ∧ ∀ i, (p.2.2.1 i).2.1 = none}

/-- Query registers blank, on the vertex space. -/
private def awk_QB : Set (QBasis ι σ V) := {p | p.1 = none ∧ p.2.1 = none}

/-- The lifted marker inherits the closeness of the marker. -/
private lemma awk_markG_close {M₁ M₂ : QRoutine ι σ V} {a : ι → σ} {e : ℝ}
    (h : awk_RClose M₁ M₂ a awk_QB e) (Lc T : ℕ) (kk : Fin Lc → ℕ) :
    awk_RClose (M₁.liftReg (∀ j, Blk ι V Lc T kk j)) (M₂.liftReg (∀ j, Blk ι V Lc T kk j)) a
      (awk_Gg Lc T kk) e :=
  (h.liftReg _ (fun bl => ∀ i, (bl i).2.1 = none)).congr_set (by
    ext p; simp [awk_Gg, awk_QB, and_assoc])

/-- The lifted preparation has the error of the preparation on the start state. -/
private lemma awk_prepG_close {P₁ P₂ : QRoutine ι σ V} {a : ι → σ} (init : QBasis ι σ V → ℂ)
    (Lc T : ℕ) (kk : Fin Lc → ℕ) :
    qNorm ((P₁.liftReg (∀ j, Blk ι V Lc T kk j)).run a *ᵥ embedReg (blankAll ι V Lc T kk) init
      - (P₂.liftReg (∀ j, Blk ι V Lc T kk j)).run a *ᵥ embedReg (blankAll ι V Lc T kk) init)
      = qNorm (P₁.run a *ᵥ init - P₂.run a *ᵥ init) := by
  rw [QRoutine.liftReg_run_embed, QRoutine.liftReg_run_embed, ← awk_embedReg_sub, qNorm,
    qNormSq_embedReg, qNorm]

/-- The lifted frozen preparation lands in the global support. -/
private lemma awk_prepG_supp {P₂ : QRoutine ι σ V} {a : ι → σ} {init : QBasis ι σ V → ℂ}
    (h : SuppIn awk_QB (P₂.run a *ᵥ init)) (Lc T : ℕ) (kk : Fin Lc → ℕ) :
    SuppIn (awk_Gg Lc T kk)
      ((P₂.liftReg (∀ j, Blk ι V Lc T kk j)).run a *ᵥ embedReg (blankAll ι V Lc T kk) init) := by
  rw [QRoutine.liftReg_run_embed]
  intro p hp
  rw [embedReg_apply] at hp
  split_ifs at hp with h1
  · obtain ⟨hk, ht⟩ := h _ hp
    refine ⟨hk, ht, fun i => ?_⟩
    rw [h1]
    rfl
  · exact absurd rfl hp

/-- The walk routine: four update applications. -/
private lemma awk_walkR_close {S S' : WalkSetup ι σ V} {a : ι → σ} {e : ℝ}
    (hA : awk_RClose S.updA S'.updA a {q | QbSys q = true} e)
    (hB : awk_RClose S.updB S'.updB a {q | QbSys q = true} e) :
    awk_RClose S.walkR S'.walkR a {q | QbSys q = true} (4 * e) := by
  have hbl : Preserves (blankRefl (ι := ι) (σ := σ) (V := V)) {q | QbSys q = true} :=
    LevelData.preserves_qRefl (by rw [flagProj]; exact awk_preserves_diagonal _ _)
  exact ((hA.inv.conjFixed _ hbl).comp (hB.inv.conjFixed _ hbl)).of_eq (by ring)

/-- The level support, read through `blkEquiv`, is the global support. -/
private lemma awk_Gg_blk {Lc T : ℕ} {kk : Fin Lc → ℕ} (j : Fin Lc) :
    {p | (blkEquiv (ι := ι) (σ := σ) (V := V) (T := T) (kk := kk) j p).1
        ∈ awk_Gc (awk_Gs (Fin (kk j * (T - 1) + 1)) {q | QbSys q = true})
      ∧ (fun g : (∀ i : {i // i ≠ j}, Blk ι V Lc T kk i) => ∀ i, (g i).2.1 = none)
        (blkEquiv j p).2} = awk_Gg Lc T kk := by
  ext p
  simp only [Set.mem_ofPred_eq, awk_Gg, awk_Gc, awk_Gs, blkEquiv_fst, blkEquiv_snd, QbSys,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hpk, hk, ht⟩, hothers⟩
    refine ⟨hk, ht, fun i => ?_⟩
    by_cases hi : i = j
    · subst hi; exact hpk
    · exact hothers ⟨i, hi⟩
  · rintro ⟨hk, ht, hall⟩
    exact ⟨⟨hall j, hk, ht⟩, fun i => hall i.1⟩

/-- **The reflection routines**: `2·ε` per update application. -/
private theorem awk_reflG_close (S : WalkSetup ι σ V) (P : QRoutine ι σ V)
    (A B : QRoutine ι σ (V × Option V)) (M : QRoutine ι σ V) (r : V → ℂ) (D : Matrix V V ℂ)
    (δ : ℝ) (hT : 4 ≤ (S.T : ℝ) ^ 2 * δ) {x : ι → σ} {ε : ℝ}
    (hA : awk_RClose S.updA A x {q | QbSys q = true} (2 * ε))
    (hB : awk_RClose S.updB B x {q | QbSys q = true} (2 * ε)) (Lc n : ℕ) :
    awk_RClose (S.reflG Lc n) ((awk_frozen S P A B M r D δ hT).reflG Lc n) x
      (awk_Gg Lc S.T (WalkGlobal.kkG Lc)) (2 * ε * ((awk_unit S).reflG Lc n).len) := by
  have hW := awk_walkR_close (S := S) (S' := awk_frozen S P A B M r D δ hT) hA hB
  unfold WalkSetup.reflG
  split_ifs with hn
  · have hL := awk_RClose.lvlRoutine hA hW S.T (WalkGlobal.kkG Lc ⟨n - 1, hn.2⟩) S.hT0
    have hK := hL.kronLift (oracleCompat_blkEquiv (ι := ι) (σ := σ) (V := V) (T := S.T)
      (kk := WalkGlobal.kkG Lc) ⟨n - 1, hn.2⟩) (fun g => ∀ i, (g i).2.1 = none)
    refine (hK.congr_set (awk_Gg_blk _)).of_eq ?_
    rw [WalkSetup.blockRefl, QRoutine.kronLift_len, WalkSetup.lvl, lvlRoutine_len,
      WalkSetup.walkR_len]
    simp only [awk_unit, QRoutine.query_len]
    push_cast
    ring
  · simp only [QRoutine.identity_len, Nat.cast_zero, mul_zero]
    exact awk_RClose.self _ (preserves_one _)

/-- `110` passes of at most `passLen 1 1 …` routine applications are within `walkUses`. -/
private lemma awk_passLen_unit_le (S : WalkSetup ι σ V) (K : ℕ) :
    110 * passLen 1 1 (fun l => ((awk_unit S).reflG (K + 1) l).len) (K + 1)
      ≤ walkUses S.T K := by
  have hle := (awk_unit S).walkSearch_q_le K
  rw [(awk_unit S).walkSearch_q K] at hle
  have hρ : (awk_unit S).ρ ≤ 2 + 8 * S.T := by
    change 2 * 1 + 2 * ((S.T - 1) * (2 * 1 + 2 * 1)) ≤ 2 + 8 * S.T
    omega
  have h1 : 2 * 3 ^ (K + 2) * (2 * 1 + 21 * (awk_unit S).ρ)
      ≤ 2 * 3 ^ (K + 2) * (2 + 21 * (2 + 8 * S.T)) :=
    Nat.mul_le_mul_left _ (by omega)
  change 110 * passLen 1 1 (fun l => ((awk_unit S).reflG (K + 1) l).len) (K + 1)
    ≤ 110 * (1 + 1 + 2 * 3 ^ (K + 2) * (2 * 1 + 21 * (awk_unit S).ρ)) at hle
  rw [walkUses]
  omega

/-- The outcome law of a pass is read from the final state of `passR`. -/
private lemma awk_passTrial_pr {W : Type} [Fintype W] [DecidableEq W] (prep mark : QRoutine ι σ W)
    (init : QBasis ι σ W → ℂ) (hinit : IsQState init) (refl : ℕ → QRoutine ι σ W)
    (clean : ℕ → QBasis ι σ W → Bool) (vtx : QBasis ι σ W → V) (K : ℕ) (a : ι → σ)
    (o : Option V) :
    (passTrial prep init hinit mark refl clean vtx K).pr a o
      = qProb (slotReadout ι σ W (K + 2) V) ((passR prep mark refl clean vtx K).run a
          *ᵥ embedReg (emptySlots (K + 2) V) (embedCtrl false init)) o := by
  have hq : (passTrial prep init hinit mark refl clean vtx K).q
      = (passR prep mark refl clean vtx K).len := (passR_len prep mark refl clean vtx K).symm
  have hstate : (passTrial prep init hinit mark refl clean vtx K).alg.state a
      (passTrial prep init hinit mark refl clean vtx K).q
      = (passR prep mark refl clean vtx K).run a
        *ᵥ embedReg (emptySlots (K + 2) V) (embedCtrl false init) := by
    rw [hq]
    exact QRoutine.toAlg_state_len _ _ _ _ a
  change qProb _ ((passTrial prep init hinit mark refl clean vtx K).alg.state a _) o = _
  rw [hstate]
  rfl

set_option synthInstance.maxSize 6400 in
/-- **The core comparison**: the actual and frozen compiled walks have outcome laws within
`walkErr` in `ℓ¹`. -/
private theorem awk_tv_walkSearch (S : WalkSetup ι σ V) (x : ι → σ) {ε : ℝ} (hε : 0 ≤ ε)
    (P : QRoutine ι σ V) (A B : QRoutine ι σ (V × Option V)) (M : QRoutine ι σ V)
    (r : V → ℂ) (D : Matrix V V ℂ) (δ : ℝ) (hT : 4 ≤ (S.T : ℝ) ^ 2 * δ)
    (hP : qNorm (S.prepV.run x *ᵥ S.initV - P.run x *ᵥ S.initV) ≤ ε)
    (hPb : SuppIn awk_QB (P.run x *ᵥ S.initV))
    (hA : awk_RClose S.updA A x {q | QbSys q = true} (2 * ε))
    (hB : awk_RClose S.updB B x {q | QbSys q = true} (2 * ε))
    (hM : awk_RClose S.markV M x awk_QB (2 * ε)) (K : ℕ) :
    awk_tv (S.walkSearch K) ((awk_frozen S P A B M r D δ hT).walkSearch K) x
      ≤ walkErr S.T K ε := by
  set ψ₀ := embedReg (emptySlots (K + 2) V) (embedCtrl false (S.initG (K + 1))) with hψ₀
  have hψ₀n : qNorm ψ₀ = 1 := by
    rw [hψ₀, qNorm, qNormSq_embedReg, qNormSq_embedCtrl, S.initG_unit (K + 1), Real.sqrt_one]
  -- the actual and frozen pass routines
  let T₁ := passTrial (S.prepG (K + 1)) (S.initG (K + 1)) (S.initG_unit (K + 1))
    (S.markG (K + 1)) (S.reflG (K + 1)) cleanG vtxG K
  let T₂ := passTrial ((awk_frozen S P A B M r D δ hT).prepG (K + 1)) (S.initG (K + 1))
    (S.initG_unit (K + 1)) ((awk_frozen S P A B M r D δ hT).markG (K + 1))
    ((awk_frozen S P A B M r D δ hT).reflG (K + 1)) cleanG vtxG K
  let ψ₁ := (passR (S.prepG (K + 1)) (S.markG (K + 1)) (S.reflG (K + 1)) cleanG vtxG K).run x
    *ᵥ ψ₀
  let ψ₂ := (passR ((awk_frozen S P A B M r D δ hT).prepG (K + 1))
    ((awk_frozen S P A B M r D δ hT).markG (K + 1))
    ((awk_frozen S P A B M r D δ hT).reflG (K + 1)) cleanG vtxG K).run x *ᵥ ψ₀
  -- the `110` passes
  have h1 : awk_tv (S.walkSearch K) ((awk_frozen S P A B M r D δ hT).walkSearch K) x
      ≤ (110 : ℕ) * awk_tv T₁ T₂ x := awk_tv_firstOf_replicate T₁ T₂ x 110
  -- one pass: outcome laws from the final states
  have h2 : awk_tv T₁ T₂ x ≤ 2 * qNorm (ψ₁ - ψ₂) := by
    unfold awk_tv
    simp only [T₁, T₂, awk_passTrial_pr]
    exact awk_sum_abs_qProb_sub_le _
      (by rw [qNorm_mulVec (QRoutine.run_mem_unitaryGroup _ x), hψ₀n])
      (by rw [qNorm_mulVec (QRoutine.run_mem_unitaryGroup _ x), hψ₀n])
  -- one pass: the hybrid argument
  have h3 : qNorm (ψ₁ - ψ₂) ≤ awk_passErr (2 * ε) (2 * ε)
      (fun l => 2 * ε * ((awk_unit S).reflG (K + 1) l).len) (K + 1) :=
    awk_pass_close (a := x) (G := awk_Gg (K + 1) S.T (WalkGlobal.kkG (K + 1)))
      (clean := cleanG) (vtx := vtxG)
      (prep := S.prepG (K + 1)) (prep' := (awk_frozen S P A B M r D δ hT).prepG (K + 1))
      (mark := S.markG (K + 1)) (mark' := (awk_frozen S P A B M r D δ hT).markG (K + 1))
      (refl := S.reflG (K + 1)) (refl' := (awk_frozen S P A B M r D δ hT).reflG (K + 1))
      (S.initG_unit (K + 1))
      ((awk_prepG_close (P₁ := S.prepV) (P₂ := P) (a := x) S.initV (K + 1) S.T _).le.trans
        (by linarith))
      (awk_prepG_supp hPb _ _ _) (awk_markG_close hM _ _ _)
      (awk_reflG_close S P A B M r D δ hT hA hB (K + 1)) (N := K + 2) (K + 1)
      (Nat.lt_succ_self _)
  rw [awk_passErr_unit] at h3
  have h4 : (110 : ℝ) * passLen 1 1 (fun l => ((awk_unit S).reflG (K + 1) l).len) (K + 1)
      ≤ walkUses S.T K := by exact_mod_cast awk_passLen_unit_le S K
  rw [walkErr]
  push_cast at h1
  nlinarith

/-! ## Part 7. The frozen setup satisfies the exact contract -/

/-- **Unit vectors are carried to each other by a unitary.** -/
private theorem awk_exists_unitary_mulVec {H : Type} [Fintype H] [DecidableEq H] {u v : H → ℂ}
    (hu : IsQState u) (hv : IsQState v) :
    ∃ U ∈ Matrix.unitaryGroup H ℂ, U *ᵥ u = v := by
  set z := qInner u v with hz
  set ω : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ) with hω
  have hωn : ‖ω‖ = 1 := by
    rw [hω]
    split_ifs with h0
    · simp
    · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr h0)]
  have hωs : ω * star ω = 1 := by
    rw [show star ω = (starRingEnd ℂ) ω from rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      hωn]
    norm_num
  have hωs' : star ω * ω = 1 := by rw [mul_comm]; exact hωs
  have hv' : IsQState (star ω • v) := by
    rw [IsQState, qNormSq_smul, hv, mul_one, Complex.normSq_eq_norm_sq, norm_star, hωn]
    norm_num
  have ht : qInner u (star ω • v) = ((‖z‖ : ℝ) : ℂ) := by
    rw [qInner_smul_right, ← hz, hω]
    split_ifs with h0
    · rw [h0]; simp
    · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
      rw [star_div₀, show star z = (starRingEnd ℂ) z from rfl, Complex.star_def,
        Complex.conj_ofReal, div_mul_eq_mul_div, mul_comm ((starRingEnd ℂ) z),
        Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      field_simp
  refine ⟨ω • bisectRefl u (star ω • v) ‖z‖, ?_, ?_⟩
  · have hB := bisectRefl_mem_unitaryGroup hu hv' (norm_nonneg z) ht
    rw [Matrix.mem_unitaryGroup_iff'] at hB ⊢
    rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, hB, smul_smul, hωs', one_smul]
  · rw [Matrix.smul_mulVec, bisectRefl_mulVec hu (norm_nonneg z) ht, smul_smul, hωs,
      one_smul]

section Frame

variable {H : Type} [Fintype H] [DecidableEq H]

/-- `1 + E (K − 1) Eᴴ` is unitary for an isometry `E` and a unitary `K`, and is supported on
the support of `E`. -/
private lemma awk_frame_unitary {n : Type} [Fintype n] [DecidableEq n] (E : Matrix H n ℂ)
    (hE : Eᴴ * E = 1) {K : Matrix n n ℂ} (hK : K ∈ Matrix.unitaryGroup n ℂ) :
    (1 + E * (K - 1) * Eᴴ) ∈ Matrix.unitaryGroup H ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have hKK : Kᴴ * K = 1 := conjTranspose_mul_self_of_unitary hK
  have e1 : (1 + E * (K - 1) * Eᴴ)ᴴ = 1 + E * (Kᴴ - 1) * Eᴴ := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, Matrix.mul_assoc]
  rw [e1]
  have hAB : E * (Kᴴ - 1) * Eᴴ * (E * (K - 1) * Eᴴ) = E * ((Kᴴ - 1) * (K - 1)) * Eᴴ := by
    calc E * (Kᴴ - 1) * Eᴴ * (E * (K - 1) * Eᴴ)
        = E * (Kᴴ - 1) * (Eᴴ * E) * (K - 1) * Eᴴ := by simp only [Matrix.mul_assoc]
      _ = E * ((Kᴴ - 1) * (K - 1)) * Eᴴ := by
        rw [hE, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have e3 : (K - 1) + (Kᴴ - 1) + (Kᴴ - 1) * (K - 1) = Kᴴ * K - 1 := by noncomm_ring
  have e4 : E * (K - 1) * Eᴴ + E * (Kᴴ - 1) * Eᴴ + E * ((Kᴴ - 1) * (K - 1)) * Eᴴ
      = E * (K - 1 + (Kᴴ - 1) + (Kᴴ - 1) * (K - 1)) * Eᴴ := by
    simp only [Matrix.mul_add, Matrix.add_mul]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, hAB, ← add_assoc, add_assoc 1, add_assoc 1]
  rw [e4, e3, hKK, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]

/-- `E C Eᴴ` is supported on `S × S` when the columns of `E` are supported on `S`. -/
private lemma awk_frame_supp {n : Type} [Fintype n] [DecidableEq n] (S : Set H) (E : Matrix H n ℂ)
    (hS : ∀ p i, E p i ≠ 0 → p ∈ S) (C : Matrix n n ℂ) :
    ∀ p q, (E * C * Eᴴ) p q ≠ 0 → p ∈ S ∧ q ∈ S := by
  intro p q hpq
  constructor
  · by_contra hp
    apply hpq
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.mul_apply]
    have : ∑ i, E p i * C i j = 0 := Finset.sum_eq_zero fun i _ => by
      by_cases h : E p i = 0
      · rw [h, zero_mul]
      · exact absurd (hS p i h) hp
    rw [this, zero_mul]
  · by_contra hq
    apply hpq
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.conjTranspose_apply]
    by_cases h : E q j = 0
    · rw [h, star_zero, mul_zero]
    · exact absurd (hS q j h) hq

/-- The frame matrix of a family of columns. -/
private def awk_frame {n : Type} (x : n → H → ℂ) : Matrix H n ℂ := Matrix.of fun p i => x i p

/-- The frame of an orthonormal family is an isometry. -/
private lemma awk_frame_orth {n : Type} [Fintype n] [DecidableEq n] (x : n → H → ℂ)
    (hx : ∀ i j, qInner (x i) (x j) = if i = j then 1 else 0) :
    (awk_frame x)ᴴ * awk_frame x = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply, ← hx i j, qInner_def]
  rfl

/-- The action of `E C Eᴴ` on a vector, for the frame `E` of a family. -/
private lemma awk_frame_mulVec {n : Type} [Fintype n] [DecidableEq n] (x : n → H → ℂ)
    (C : Matrix n n ℂ) (φ : H → ℂ) :
    (awk_frame x * C * (awk_frame x)ᴴ) *ᵥ φ = ∑ j, (∑ i, C j i * qInner (x i) φ) • x j := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  funext p
  simp only [Matrix.mulVec, dotProduct, awk_frame, Matrix.of_apply, Matrix.conjTranspose_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, qInner_def]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

end Frame

/-- **One block**: for unit vectors `a`, `b` supported on `S`, a unitary `1 + X` with `X`
supported on `S × S`, carrying `a` to `b`, with `‖X φ‖ ≤ 2‖a − b‖‖φ‖`. (Take
`X = (b − a)a* + (e' − e)e*` with `e = (b − z a)/s`, `e' = ω(z̄ b − a)/s`, `z = ⟨a, b⟩`,
`s = √(1 − |z|²)`, `ω = z/|z|`; then `{a, e}`, `{b, e'}` are orthonormal bases of `span{a, b}`
and `‖e' − e‖² = 2 − 2|z| ≤ ‖a − b‖²`; if `s = 0`, `X = (b − a)a*`.) -/
private theorem awk_exists_blockRot {H : Type} [Fintype H] [DecidableEq H] (S : Set H) {a b : H → ℂ}
    (ha : IsQState a) (hb : IsQState b) (hsa : SuppIn S a) (hsb : SuppIn S b) :
    ∃ X : Matrix H H ℂ, (1 + X) ∈ Matrix.unitaryGroup H ℂ ∧ X *ᵥ a = b - a
      ∧ (∀ p q, X p q ≠ 0 → p ∈ S ∧ q ∈ S)
      ∧ ∀ φ, qNorm (X *ᵥ φ) ≤ 2 * qNorm (a - b) * qNorm φ := by
  set z := qInner a b with hz
  have hna : qNorm a = 1 := qNorm_eq_one ha
  have haa : qInner a a = 1 := by rw [qInner_self, ha]; rfl
  have hr1 : ‖z‖ ≤ 1 := by
    have := norm_qInner_le a b
    rwa [hna, qNorm_eq_one hb, mul_one] at this
  have hzz : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [show star z = (starRingEnd ℂ) z from rfl, mul_comm, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  have hd2 : qNorm (a - b) ^ 2 = 2 - 2 * z.re := by
    rw [qNorm_sq, show a - b = a + (-1 : ℂ) • b by rw [neg_one_smul, sub_eq_add_neg],
      qNormSq_add, qNormSq_smul, qInner_smul_right, ha, hb, ← hz]
    simp only [Complex.normSq_neg, Complex.normSq_one, neg_mul, one_mul, Complex.neg_re]
    ring
  have hzre : z.re ≤ ‖z‖ := Complex.re_le_norm z
  have hd0 : 0 ≤ qNorm (a - b) := qNorm_nonneg _
  have hCS : ∀ ψ φ : H → ℂ, qNorm ψ = 1 → ‖qInner ψ φ‖ ≤ qNorm φ := fun ψ φ hψ => by
    have := norm_qInner_le ψ φ
    rwa [hψ, one_mul] at this
  set w := b - z • a with hw
  have hwa : qInner a w = 0 := by
    rw [hw, qInner_sub_right, qInner_smul_right, ← hz, haa, mul_one, sub_self]
  have hw2 : qNormSq w = 1 - ‖z‖ ^ 2 := by
    have h1 : qInner w w = qInner b b - star z * z := by
      rw [hw, qInner_sub_left, qInner_sub_right, qInner_sub_right, qInner_smul_left,
        qInner_smul_left, qInner_smul_right, qInner_smul_right, haa, ← hz, ← qInner_conj a b,
        ← hz]
      ring
    rw [qInner_self, qInner_self, hb, hzz] at h1
    exact_mod_cast h1
  have hsw : SuppIn S w := hsb.sub (hsa.smul z)
  by_cases hs : ‖z‖ = 1
  · -- `b = z a`: a phase on `a`
    have hw0 : w = 0 := by
      rw [← qNormSq_eq_zero_iff, hw2, hs]
      norm_num
    have hbz : b = z • a := by rw [hw, sub_eq_zero] at hw0; exact hw0
    have hz1 : star z * z = 1 := by rw [hzz, hs]; norm_num
    set K : Matrix Unit Unit ℂ := Matrix.of fun _ _ => z with hKdef
    have hK : K ∈ Matrix.unitaryGroup Unit ℂ := by
      rw [Matrix.mem_unitaryGroup_iff']
      ext i j
      simp only [hKdef, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply,
        Finset.univ_unique, Finset.sum_singleton, Matrix.one_apply_eq]
      exact hz1
    have hK1 : ∀ i j : Unit, (K - 1) i j = z - 1 := fun i j => by
      rw [Matrix.sub_apply, Subsingleton.elim i j, Matrix.one_apply_eq]
      rfl
    have hE := awk_frame_orth (fun _ : Unit => a) fun i j => by
      rw [Subsingleton.elim i j]; simpa using haa
    refine ⟨awk_frame (fun _ : Unit => a) * (K - 1) * (awk_frame (fun _ : Unit => a))ᴴ,
      awk_frame_unitary _ hE hK, ?_, awk_frame_supp S _ (fun p _ h => hsa p h) _,
      fun φ => ?_⟩
    · rw [awk_frame_mulVec]
      simp only [Finset.univ_unique, Finset.sum_singleton, hK1, haa, mul_one, hbz, sub_smul,
        one_smul]
    · rw [awk_frame_mulVec]
      simp only [Finset.univ_unique, Finset.sum_singleton, hK1]
      rw [qNorm_smul, norm_mul, qNorm_eq_one ha, mul_one]
      have hza : ‖z - 1‖ = qNorm (a - b) := by
        rw [hbz, ← one_smul ℂ a, smul_smul, mul_one, ← sub_smul, qNorm_smul, qNorm_eq_one ha,
          mul_one, ← norm_neg, neg_sub]
      rw [hza]
      have := hCS a φ hna
      nlinarith [qNorm_nonneg φ, norm_nonneg (qInner a φ)]
  · -- the generic case: a rotation in `span {a, b}`
    have hr : ‖z‖ < 1 := lt_of_le_of_ne hr1 hs
    set s : ℝ := Real.sqrt (1 - ‖z‖ ^ 2) with hsdef
    have hs0 : 0 < s := Real.sqrt_pos.mpr (by nlinarith [norm_nonneg z])
    have hss : s ^ 2 = 1 - ‖z‖ ^ 2 := Real.sq_sqrt (by nlinarith [norm_nonneg z])
    set e : H → ℂ := ((s⁻¹ : ℝ) : ℂ) • w with he
    have hse : ((s : ℝ) : ℂ) • e = w := by
      rw [he, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hs0.ne', Complex.ofReal_one,
        one_smul]
    have hae : qInner a e = 0 := by rw [he, qInner_smul_right, hwa, mul_zero]
    have hea : qInner e a = 0 := by rw [← qInner_conj, hae, star_zero]
    have hee : qInner e e = 1 := by
      rw [he, qInner_smul_left, qInner_smul_right, qInner_self, hw2, ← hss]
      rw [Complex.star_def, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
        ← Complex.ofReal_mul]
      congr 1
      field_simp
    have hne : qNorm e = 1 := by
      rw [qNorm, show qNormSq e = 1 by exact_mod_cast (qInner_self e).symm.trans hee,
        Real.sqrt_one]
    -- the phase of `z`
    set ω : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ) with hω
    have hωn : ‖ω‖ = 1 := by
      rw [hω]
      split_ifs with h0
      · simp
      · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr h0)]
    have hωω : star ω * ω = 1 := by
      rw [show star ω = (starRingEnd ℂ) ω from rfl, mul_comm, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, hωn]
      norm_num
    have hωz : ω * star z = ((‖z‖ : ℝ) : ℂ) := by
      rw [hω]
      split_ifs with h0
      · rw [h0]; simp
      · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
        rw [div_mul_eq_mul_div, show z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) by
          rw [mul_comm]; exact hzz]
        push_cast
        field_simp
    have hss' : (s : ℂ) * s = 1 - ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← sq, hss]; push_cast; ring
    have hb' : b = z • a + (s : ℂ) • e := by rw [hse, hw, add_sub_cancel]
    set x : Fin 2 → H → ℂ := ![a, e] with hx
    have hxo : ∀ i j, qInner (x i) (x j) = if i = j then 1 else 0 := by
      intro i j
      have hqe : qNormSq e = 1 := by exact_mod_cast (qInner_self e).symm.trans hee
      have hqa : qNormSq a = 1 := ha
      fin_cases i <;> fin_cases j <;> simp [hx, hae, hea, hqa, hqe]
    set K : Matrix (Fin 2) (Fin 2) ℂ := !![z, -(ω * s); (s : ℂ), ω * star z] with hKdef
    have hK : K ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff']
      ext i j
      have hzz' : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := hzz
      have hωω' : (starRingEnd ℂ) ω * ω = 1 := hωω
      fin_cases i <;> fin_cases j <;> simp [hKdef, Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination hzz' + hss'
      · ring
      · ring
      · linear_combination ((s : ℂ) * s + (starRingEnd ℂ) z * z) * hωω' + hzz' + hss'
    have hEs : ∀ p i, awk_frame x p i ≠ 0 → p ∈ S := by
      intro p i hpi
      fin_cases i
      · exact hsa p hpi
      · exact (hsw.smul _) p hpi
    set f : H → ℂ := (-(ω * s)) • a + (ω * star z - 1) • e with hf
    have hXφ : ∀ φ, (awk_frame x * (K - 1) * (awk_frame x)ᴴ) *ᵥ φ
        = qInner a φ • (b - a) + qInner e φ • f := by
      intro φ
      rw [awk_frame_mulVec, hb', hf]
      simp only [Fin.sum_univ_two, hx, hKdef, Matrix.sub_apply, Matrix.one_apply,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue]
      simp only [zero_ne_one, one_ne_zero, sub_zero, ite_true, ite_false]
      module
    have hqa : qNormSq a = 1 := ha
    have hqe : qNormSq e = 1 := by exact_mod_cast (qInner_self e).symm.trans hee
    have hqf : qNormSq f = s ^ 2 + (1 - ‖z‖) ^ 2 := by
      rw [hf, qNormSq_add, qNormSq_smul, qNormSq_smul, qInner_smul_left, qInner_smul_right,
        hae, mul_zero, mul_zero, Complex.zero_re, mul_zero, add_zero, hωz, hqa, hqe, mul_one,
        mul_one, Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_eq_norm_sq ω, hωn,
        Complex.normSq_ofReal, show ((‖z‖ : ℝ) : ℂ) - 1 = ((‖z‖ - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.normSq_ofReal]
      ring
    have hfd : qNorm f ≤ qNorm (a - b) := by
      have h1 : qNorm f ^ 2 ≤ qNorm (a - b) ^ 2 := by
        rw [qNorm_sq, hqf, hd2, hss]
        nlinarith
      nlinarith [qNorm_nonneg f]
    refine ⟨awk_frame x * (K - 1) * (awk_frame x)ᴴ,
      awk_frame_unitary _ (awk_frame_orth x hxo) hK, ?_, awk_frame_supp S _ hEs _,
      fun φ => ?_⟩
    · rw [hXφ, haa, hea, one_smul, zero_smul, add_zero]
    · rw [hXφ]
      refine (qNorm_add_le _ _).trans ?_
      rw [qNorm_smul, qNorm_smul, qNorm_sub_comm b a]
      have h1 := hCS a φ hna
      have h2 := hCS e φ hne
      have h3 := mul_le_mul h1 le_rfl hd0 (qNorm_nonneg φ)
      have h4 := mul_le_mul h2 hfd (qNorm_nonneg f) (qNorm_nonneg φ)
      linarith

/-- Pythagoras for vectors with disjoint supports (one direction). -/
private lemma awk_qNormSq_sum_le {H : Type} [Fintype H] [DecidableEq H] (S : V → Set H)
    (hS : ∀ u v, u ≠ v → Disjoint (S u) (S v)) (g : V → H → ℂ)
    (hg : ∀ u, SuppIn (S u) (g u)) : qNormSq (∑ u, g u) ≤ ∑ u, qNormSq (g u) := by
  classical
  simp only [qNormSq_def]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [Finset.sum_apply]
  by_cases h : ∃ u, q ∈ S u
  · obtain ⟨u, hu⟩ := h
    have h0 : ∀ v, v ≠ u → g v q = 0 := fun v hv => by
      by_contra hne
      exact Set.disjoint_left.mp (hS v u hv) (hg v q hne) hu
    rw [Finset.sum_eq_single u (fun v _ hv => h0 v hv) (by simp)]
    exact Finset.single_le_sum (f := fun v => Complex.normSq (g v q))
      (fun v _ => Complex.normSq_nonneg _) (Finset.mem_univ u)
  · simp only [not_exists] at h
    have h0 : ∀ v, g v q = 0 := fun v => by
      by_contra hne
      exact h v (hg v q hne)
    simp only [h0, Finset.sum_const_zero, map_zero, le_refl]

/-- Restrictions to disjoint blocks have total mass at most the mass. -/
private lemma awk_sum_qNormSq_restrict_le {H : Type} [Fintype H] [DecidableEq H] (S : V → Set H)
    (hS : ∀ u v, u ≠ v → Disjoint (S u) (S v)) [∀ u, DecidablePred (· ∈ S u)]
    (φ : H → ℂ) :
    ∑ u, qNormSq (fun q => if q ∈ S u then φ q else 0) ≤ qNormSq φ := by
  simp only [qNormSq_def]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun q _ => ?_
  by_cases h : ∃ u, q ∈ S u
  · obtain ⟨u, hu⟩ := h
    have hv : ∀ v, v ≠ u → q ∉ S v := fun v hv hv' => Set.disjoint_left.mp (hS v u hv) hv' hu
    rw [Finset.sum_eq_single u (fun v _ hv' => by simp [hv v hv']) (by simp)]
    simp [hu]
  · simp only [not_exists] at h
    simp only [h, ite_false, map_zero, Finset.sum_const_zero]
    exact Complex.normSq_nonneg _

/-- **Disjoint blocks combine**: `1 + ∑ X u` is unitary, acts as `1 + X u` on vectors of block
`u`, and is within `2ε` of the identity. -/
private theorem awk_blocks_combine {H : Type} [Fintype H] [DecidableEq H] (S : V → Set H)
    (hS : ∀ u v, u ≠ v → Disjoint (S u) (S v)) (X : V → Matrix H H ℂ)
    (hU : ∀ u, (1 + X u) ∈ Matrix.unitaryGroup H ℂ)
    (hX : ∀ u p q, X u p q ≠ 0 → p ∈ S u ∧ q ∈ S u) {ε : ℝ} (hε : 0 ≤ ε)
    (hn : ∀ u φ, qNorm (X u *ᵥ φ) ≤ 2 * ε * qNorm φ) :
    (1 + ∑ u, X u) ∈ Matrix.unitaryGroup H ℂ
      ∧ (∀ u φ, SuppIn (S u) φ → (1 + ∑ v, X v) *ᵥ φ = φ + X u *ᵥ φ)
      ∧ ∀ φ, qNorm ((1 + ∑ u, X u) *ᵥ φ - φ) ≤ 2 * ε * qNorm φ := by
  classical
  have hdis : ∀ u v, u ≠ v → ∀ r, r ∈ S u → r ∉ S v := fun u v huv r hu hv =>
    Set.disjoint_left.mp (hS u v huv) hu hv
  have hcross : ∀ u v, u ≠ v → star (X u) * X v = 0 := by
    intro u v huv
    ext p q
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [Matrix.star_apply]
    by_cases h1 : X u r p = 0
    · rw [h1, star_zero, zero_mul]
    · by_cases h2 : X v r q = 0
      · rw [h2, mul_zero]
      · exact absurd (hX v r q h2).1 (hdis u v huv r (hX u r p h1).1)
  have hself : ∀ u, star (X u) + X u + star (X u) * X u = 0 := by
    intro u
    have h1 := Matrix.mem_unitaryGroup_iff'.mp (hU u)
    have e : star (1 + X u) * (1 + X u) = 1 + (star (X u) + X u + star (X u) * X u) := by
      rw [star_add, star_one]
      noncomm_ring
    rw [e] at h1
    exact (add_eq_left.mp h1)
  have hW : star (1 + ∑ u, X u) * (1 + ∑ u, X u) = 1 := by
    have hdouble : (∑ u, star (X u)) * (∑ v, X v) = ∑ u, star (X u) * X u := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      exact Finset.sum_eq_single u (fun v _ hv => hcross u v (Ne.symm hv)) (by simp)
    have e : star (1 + ∑ u, X u) * (1 + ∑ u, X u)
        = 1 + ∑ u, (star (X u) + X u + star (X u) * X u) := by
      rw [star_add, star_one, star_sum, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
        Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hdouble, Finset.sum_add_distrib,
        Finset.sum_add_distrib]
      abel
    rw [e, Finset.sum_eq_zero fun u _ => hself u, add_zero]
  have hact : ∀ u φ, SuppIn (S u) φ → ∀ v, v ≠ u → X v *ᵥ φ = 0 := by
    intro u φ hφ v hvu
    funext p
    rw [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases h1 : X v p q = 0
    · rw [h1, zero_mul]
    · by_cases h2 : φ q = 0
      · rw [h2, mul_zero]
      · exact absurd (hφ q h2) (hdis v u hvu q (hX v p q h1).2)
  refine ⟨Matrix.mem_unitaryGroup_iff'.mpr hW, fun u φ hφ => ?_, fun φ => ?_⟩
  · rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec,
      Finset.sum_eq_single u (fun v _ hv => hact u φ hφ v hv) (by simp)]
  · set φr : V → H → ℂ := fun u q => if q ∈ S u then φ q else 0 with hφr
    have hX' : ∀ u, X u *ᵥ φ = X u *ᵥ φr u := fun u => by
      funext p
      rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : q ∈ S u
      · simp [hφr, hq]
      · have : X u p q = 0 := by
          by_contra hne
          exact hq (hX u p q hne).2
        rw [this, zero_mul, zero_mul]
    have hsupp : ∀ u, SuppIn (S u) (X u *ᵥ φr u) := fun u p hp => by
      rw [Matrix.mulVec, dotProduct] at hp
      obtain ⟨q, _, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
      exact (hX u p q (left_ne_zero_of_mul hq)).1
    have hW1 : (1 + ∑ u, X u) *ᵥ φ - φ = ∑ u, X u *ᵥ φr u := by
      rw [Matrix.add_mulVec, Matrix.one_mulVec, add_sub_cancel_left, Matrix.sum_mulVec]
      exact Finset.sum_congr rfl fun u _ => hX' u
    rw [hW1]
    refine qNorm_le_of_qNormSq_le (mul_nonneg (by linarith) (qNorm_nonneg _)) ?_
    have h1 := awk_qNormSq_sum_le S hS _ hsupp
    have h2 : ∀ u, qNormSq (X u *ᵥ φr u) ≤ (2 * ε) ^ 2 * qNormSq (φr u) := fun u => by
      rw [← qNorm_sq, ← qNorm_sq, ← mul_pow]
      exact pow_le_pow_left₀ (qNorm_nonneg _) (hn u _) 2
    have h3 := awk_sum_qNormSq_restrict_le S hS φ
    calc qNormSq (∑ u, X u *ᵥ φr u) ≤ ∑ u, qNormSq (X u *ᵥ φr u) := h1
      _ ≤ ∑ u, (2 * ε) ^ 2 * qNormSq (φr u) := Finset.sum_le_sum fun u _ => h2 u
      _ = (2 * ε) ^ 2 * ∑ u, qNormSq (φr u) := by rw [Finset.mul_sum]
      _ ≤ (2 * ε) ^ 2 * qNormSq φ := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      _ = (2 * ε * qNorm φ) ^ 2 := by rw [mul_pow (2 * ε) (qNorm φ), qNorm_sq]

/-- **A block-diagonal unitary close to the identity** carrying unit vectors `a u` to nearby
unit vectors `b u`, both in the block `B u` and in the flag `f`, and commuting with the flag. -/
private theorem awk_exists_nearUnitary {H : Type} [Fintype H] [DecidableEq H] (B : V → Set H)
    (hB : ∀ u v, u ≠ v → Disjoint (B u) (B v)) (f : H → Bool) (a b : V → H → ℂ)
    (ha : ∀ u, IsQState (a u)) (hb : ∀ u, IsQState (b u))
    (hsa : ∀ u, SuppIn (B u ∩ {q | f q = true}) (a u))
    (hsb : ∀ u, SuppIn (B u ∩ {q | f q = true}) (b u)) {ε : ℝ} (hε : 0 ≤ ε)
    (hab : ∀ u, qNorm (a u - b u) ≤ ε) :
    ∃ W ∈ Matrix.unitaryGroup H ℂ, (∀ u, W *ᵥ a u = b u) ∧ W * flagProj f = flagProj f * W
      ∧ ∀ φ, qNorm (W *ᵥ φ - φ) ≤ 2 * ε * qNorm φ := by
  choose X hXU hXa hXs hXn using fun u =>
    awk_exists_blockRot (B u ∩ {q | f q = true}) (ha u) (hb u) (hsa u) (hsb u)
  have hS : ∀ u v, u ≠ v → Disjoint (B u ∩ {q | f q = true}) (B v ∩ {q | f q = true}) :=
    fun u v huv => (hB u v huv).mono Set.inter_subset_left Set.inter_subset_left
  obtain ⟨hWU, hWact, hWn⟩ := awk_blocks_combine _ hS X hXU hXs hε fun u φ =>
    (hXn u φ).trans (mul_le_mul_of_nonneg_right (by linarith [hab u]) (qNorm_nonneg φ))
  refine ⟨1 + ∑ u, X u, hWU, fun u => ?_, ?_, hWn⟩
  · rw [hWact u (a u) (hsa u), hXa u, add_sub_cancel]
  · have h1 : ∀ u, X u * flagProj f = X u := fun u => by
      ext p q
      rw [flagProj, Matrix.mul_diagonal]
      by_cases hq : f q = true
      · simp [hq]
      · have : X u p q = 0 := by
          by_contra hne
          exact hq (hXs u p q hne).2.2
        simp [this]
    have h2 : ∀ u, flagProj f * X u = X u := fun u => by
      ext p q
      rw [flagProj, Matrix.diagonal_mul]
      by_cases hp : f p = true
      · simp [hp]
      · have : X u p q = 0 := by
          by_contra hne
          exact hp (hXs u p q hne).1.2
        simp [this]
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Finset.sum_mul,
      Finset.mul_sum]
    simp only [h1, h2]

/-- The ideal setup state is a unit vector. -/
private lemma awk_isQState_idealPrep (Q : WalkChain V) :
    IsQState (idealPrep (ι := ι) (σ := σ) Q) := by
  rw [IsQState, qNormSq_def]
  simp only [idealPrep, sqrtPiV, Fintype.sum_prod_type, Fintype.sum_option]
  simp [WalkChain.r, Complex.normSq_ofReal, Real.mul_self_sqrt (Q.π_nonneg _), Q.π_sum]

/-- The ideal row is a unit vector. -/
private lemma awk_isQState_idealRowA (Q : WalkChain V) (u : V) :
    IsQState (idealRowA (ι := ι) (σ := σ) Q u) := by
  rw [IsQState, qNormSq_def]
  simp only [idealRowA, Fintype.sum_prod_type, Fintype.sum_option]
  simp only [and_self, true_and, Finset.sum_const_zero, add_zero, map_zero, reduceCtorEq,
    false_and, ite_false, ite_self, zero_add]
  rw [Finset.sum_eq_single u (fun b _ hb => by simp [hb]) (by simp)]
  simp [Complex.normSq_ofReal, Real.mul_self_sqrt (Q.P_nonneg _ _), Q.P_row]

/-- The ideal row of the other side is a unit vector. -/
private lemma awk_isQState_idealRowB (Q : WalkChain V) (v : V) :
    IsQState (idealRowB (ι := ι) (σ := σ) Q v) := by
  rw [IsQState, qNormSq_def]
  simp only [idealRowB, Fintype.sum_prod_type, Fintype.sum_option]
  simp only [and_self, true_and, Finset.sum_const_zero, add_zero, map_zero, reduceCtorEq,
    false_and, ite_false, Option.some.injEq, zero_add]
  have hx : ∀ w : V, ∑ y : V, Complex.normSq (if y = v then ((Real.sqrt (Q.P v w) : ℝ) : ℂ)
      else 0) = Q.P v w := fun w => by
    rw [Finset.sum_eq_single v (fun b _ hb => by simp [hb]) (by simp)]
    simp [Complex.normSq_ofReal, Real.mul_self_sqrt (Q.P_nonneg _ _)]
  simp only [hx, Q.P_row]

/-- **The ideal rows have Gram matrix `D`.** -/
private lemma awk_qInner_idealRow (Q : WalkChain V) (u v : V) :
    qInner (idealRowA (ι := ι) (σ := σ) Q u) (idealRowB Q v) = Q.disc u v := by
  rw [qInner_def]
  simp only [idealRowA, idealRowB, Fintype.sum_prod_type, Fintype.sum_option]
  simp only [WalkChain.disc, Real.sqrt_mul (Q.P_nonneg _ _), Complex.ofReal_mul]
  simp only [reduceCtorEq, false_and, and_false, ite_false, mul_zero,
    Finset.sum_const_zero, zero_add, add_zero, and_self, true_and, Option.some.injEq]
  rw [Finset.sum_eq_single u (fun b _ hb => by simp [hb]) (by simp)]
  rw [Finset.sum_eq_single v (fun b _ hb => by simp [hb]) (by simp)]
  simp [Complex.conj_ofReal]

/-- The marker of the frozen setup. -/
private def awk_markR (Marked : V → Prop) [DecidablePred Marked] : QRoutine ι σ V :=
  signMarker fun p => decide (Marked p.2.2)

/-- The frozen marker is the phase flip of `Marked`. -/
private lemma awk_markR_run (Marked : V → Prop) [DecidablePred Marked] (a : ι → σ)
    (φ : QBasis ι σ V → ℂ) :
    (awk_markR Marked).run a *ᵥ φ = phaseFlip (fun p : QBasis ι σ V => p.2.2) Marked φ := by
  rw [awk_markR, signMarker_run]
  funext p
  simp only [phaseFlip, Pi.sub_apply, goodPart_apply, badPart_apply, decide_eq_true_eq]

/-- The ideal setup state has blank query registers. -/
private lemma awk_idealPrep_supp (Q : WalkChain V) :
    SuppIn awk_QB (idealPrep (ι := ι) (σ := σ) Q) := by
  intro p hp
  by_contra hq
  apply hp
  simp only [awk_QB, Set.mem_ofPred_eq] at hq
  simp [idealPrep, sqrtPiV, hq]

/-- The ideal row of `u` is in block `u`, query registers blank. -/
private lemma awk_idealRowA_supp (Q : WalkChain V) (u : V) :
    SuppIn ({q | q.2.2.1 = u} ∩ {q | QbSys q = true}) (idealRowA (ι := ι) (σ := σ) Q u) := by
  intro p hp
  by_contra hq
  apply hp
  simp only [idealRowA]
  split_ifs with h
  · exact absurd ⟨h.2.2, by simp [QbSys, h.1, h.2.1]⟩ hq
  · rfl

/-- The ideal row of the other side of `v` is in block `v`, query registers blank. -/
private lemma awk_idealRowB_supp (Q : WalkChain V) (v : V) :
    SuppIn ({q | q.2.2.2 = some v} ∩ {q | QbSys q = true}) (idealRowB (ι := ι) (σ := σ) Q v) := by
  intro p hp
  by_contra hq
  apply hp
  simp only [idealRowB]
  split_ifs with h
  · exact absurd ⟨h.2.2, by simp [QbSys, h.1, h.2.1]⟩ hq
  · rfl

/-- A frozen update `W·U` with `W` close to the identity and commuting with the query-blank
flag is close to `U`. -/
private lemma awk_upd_close {U : QRoutine ι σ (V × Option V)} {a : ι → σ}
    {WA : Matrix (QBasis ι σ (V × Option V)) (QBasis ι σ (V × Option V)) ℂ}
    (hWA : WA ∈ Matrix.unitaryGroup _ ℂ) (hc : WA * flagProj QbSys = flagProj QbSys * WA)
    (hUc : U.run a * flagProj QbSys = flagProj QbSys * U.run a) {ε : ℝ} (hε : 0 ≤ ε)
    (hn : ∀ φ, qNorm (WA *ᵥ φ - φ) ≤ 2 * ε * qNorm φ) :
    awk_RClose U (U.comp (QRoutine.ofUnitary WA hWA)) a {q | QbSys q = true} (2 * ε) := by
  unfold awk_RClose awk_Close
  rw [QRoutine.comp_run, QRoutine.ofUnitary_run]
  refine ⟨by linarith, awk_preserves_of_comm (by
    rw [Matrix.mul_assoc, hUc, ← Matrix.mul_assoc, hc, Matrix.mul_assoc]), fun φ _ => ?_⟩
  rw [← Matrix.mulVec_mulVec, qNorm_sub_comm, ← qNorm_mulVec (U.run_mem_unitaryGroup a) φ]
  exact hn _

/-- The exact marker is close to the actual check on query-blank vectors. -/
private lemma awk_mark_close {Mk : QRoutine ι σ V} {a : ι → σ} {Marked : V → Prop}
    [DecidablePred Marked] {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ φ : QBasis ι σ V → ℂ, SuppIn {p | p.1 = none ∧ p.2.1 = none} φ →
      qNorm (Mk.run a *ᵥ φ - phaseFlip (fun p : QBasis ι σ V => p.2.2) Marked φ)
        ≤ ε * qNorm φ) :
    awk_RClose Mk (awk_markR Marked) a awk_QB (2 * ε) := by
  refine ⟨by linarith, ?_, fun φ hφ => ?_⟩
  · exact awk_preserves_diagonal _ _
  · rw [awk_markR_run]
    exact (h φ hφ).trans (mul_le_mul_of_nonneg_right (by linarith) (qNorm_nonneg φ))

namespace ApproxWalkOK

variable {S : WalkSetup ι σ V} {x : ι → σ} {Q : WalkChain V} {Marked : V → Prop}
  [DecidablePred Marked] {c c₀ : ℂ} {δ ε : ℝ}

/-- The precision is nonnegative. -/
private lemma awk_ε_nonneg (h : ApproxWalkOK S x Q Marked c c₀ δ ε) : 0 ≤ ε :=
  (qNorm_nonneg _).trans h.prep_close

/-- **The frozen ideal setup satisfies `WalkOK`.** -/
private theorem awk_frozen_walkOK (h : ApproxWalkOK S x Q Marked c c₀ δ ε)
    {UP : Matrix (QBasis ι σ V) (QBasis ι σ V) ℂ} (hUP : UP ∈ Matrix.unitaryGroup _ ℂ)
    (hUPi : UP *ᵥ S.initV = c₀ • idealPrep Q)
    {WA WB : Matrix (QBasis ι σ (V × Option V)) (QBasis ι σ (V × Option V)) ℂ}
    (hWA : WA ∈ Matrix.unitaryGroup _ ℂ) (hWB : WB ∈ Matrix.unitaryGroup _ ℂ)
    (hWAr : ∀ u, WA *ᵥ S.rowA x u = c • idealRowA Q u)
    (hWBr : ∀ v, WB *ᵥ S.rowB x v = c • idealRowB Q v)
    (hWAc : WA * flagProj QbSys = flagProj QbSys * WA)
    (hWBc : WB * flagProj QbSys = flagProj QbSys * WB) :
    WalkOK (awk_frozen S (QRoutine.ofUnitary UP hUP) (S.updA.comp (QRoutine.ofUnitary WA hWA))
      (S.updB.comp (QRoutine.ofUnitary WB hWB)) (awk_markR Marked) (c₀ • Q.r) Q.disc δ h.hT)
      x Marked := by
  have hc : star c * c = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      h.c_norm]
    norm_num
  have hc₀ : Complex.normSq c₀ = 1 := by rw [Complex.normSq_eq_norm_sq, h.c₀_norm]; norm_num
  have hrowA : ∀ u, (S.updA.comp (QRoutine.ofUnitary WA hWA)).run x *ᵥ qBasis (vertE u)
      = c • idealRowA Q u := fun u => by
    rw [QRoutine.comp_run, QRoutine.ofUnitary_run, ← Matrix.mulVec_mulVec]
    exact hWAr u
  have hrowB : ∀ v, (S.updB.comp (QRoutine.ofUnitary WB hWB)).run x *ᵥ qBasis (vertE v)
      = c • idealRowB Q v := fun v => by
    rw [QRoutine.comp_run, QRoutine.ofUnitary_run, ← Matrix.mulVec_mulVec]
    exact hWBr v
  refine
    { prep_run := ?_, gram := ?_, herm := ?_, r_unit := ?_, D_r := ?_, δ_pos := h.δ_pos,
      δ_le := h.δ_le, gap_D := ?_, a_supp := ?_, b_supp := ?_, updA_comm := ?_,
      updB_comm := ?_, mark_flip := fun φ => awk_markR_run Marked x φ }
  · change UP *ᵥ S.initV = sqrtPiV (c₀ • Q.r)
    rw [hUPi]
    funext p
    simp only [idealPrep, sqrtPiV, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  · intro u v
    change qInner ((S.updA.comp (QRoutine.ofUnitary WA hWA)).run x *ᵥ qBasis (vertE u))
      ((S.updB.comp (QRoutine.ofUnitary WB hWB)).run x *ᵥ qBasis (vertE v)) = Q.disc u v
    rw [hrowA, hrowB, qInner_smul_left, qInner_smul_right, awk_qInner_idealRow, ← mul_assoc,
      hc, one_mul]
  · change Q.discᴴ = Q.disc
    ext u v
    simp [Matrix.conjTranspose_apply, WalkChain.disc, mul_comm]
  · change IsQState (c₀ • Q.r)
    rw [IsQState, qNormSq_smul, hc₀, one_mul, qNormSq_def]
    simp [WalkChain.r, Complex.normSq_ofReal, Real.mul_self_sqrt (Q.π_nonneg _), Q.π_sum]
  · change Q.disc *ᵥ (c₀ • Q.r) = c₀ • Q.r
    rw [Matrix.mulVec_smul]
    congr 1
    funext u
    have hf := congrArg (fun t : ℝ => (t : ℂ)) (Q.fix u)
    simp only [Complex.ofReal_sum, Complex.ofReal_mul] at hf
    simpa [Matrix.mulVec, dotProduct, WalkChain.disc, WalkChain.r] using hf
  · intro y hy
    change qInner (c₀ • Q.r) y = 0 at hy
    rw [qInner_smul_left] at hy
    have hne : star c₀ ≠ 0 := by
      intro h0
      have h0' : c₀ = 0 := by simpa using h0
      rw [h0', map_zero] at hc₀
      exact zero_ne_one hc₀
    exact h.gap y ((mul_eq_zero.mp hy).resolve_left hne)
  · intro u
    change SuppIn _ ((S.updA.comp (QRoutine.ofUnitary WA hWA)).run x *ᵥ qBasis (vertE u))
    rw [hrowA]
    exact ((awk_idealRowA_supp Q u).mono Set.inter_subset_right).smul c
  · intro v
    change SuppIn _ ((S.updB.comp (QRoutine.ofUnitary WB hWB)).run x *ᵥ qBasis (vertE v))
    rw [hrowB]
    exact ((awk_idealRowB_supp Q v).mono Set.inter_subset_right).smul c
  · change (S.updA.comp (QRoutine.ofUnitary WA hWA)).run x * flagProj QbSys
      = flagProj QbSys * (S.updA.comp (QRoutine.ofUnitary WA hWA)).run x
    rw [QRoutine.comp_run, QRoutine.ofUnitary_run, Matrix.mul_assoc, h.updA_comm,
      ← Matrix.mul_assoc, hWAc, Matrix.mul_assoc]
  · change (S.updB.comp (QRoutine.ofUnitary WB hWB)).run x * flagProj QbSys
      = flagProj QbSys * (S.updB.comp (QRoutine.ofUnitary WB hWB)).run x
    rw [QRoutine.comp_run, QRoutine.ofUnitary_run, Matrix.mul_assoc, h.updB_comm,
      ← Matrix.mul_assoc, hWBc, Matrix.mul_assoc]

/-- The frozen stationary vector `c₀√π` has the marked mass of `π`. -/
private lemma awk_frozen_markedMass (h : ApproxWalkOK S x Q Marked c c₀ δ ε) (S' : WalkSetup ι σ V)
    (hr : S'.r = c₀ • Q.r) : S'.markedMass Marked = ∑ v, if Marked v then Q.π v else 0 := by
  have hc₀ : Complex.normSq c₀ = 1 := by rw [Complex.normSq_eq_norm_sq, h.c₀_norm]; norm_num
  rw [WalkSetup.markedMass, hr]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs
  · simp [WalkChain.r, Complex.normSq_mul, hc₀, Complex.normSq_ofReal,
      Real.mul_self_sqrt (Q.π_nonneg _)]
  · rfl

/-- **Everything the comparison needs**, from the contract: a frozen setup satisfying
`WalkOK`, with the same marked mass, and within `walkErr` of `S` in `ℓ¹`. -/
private theorem awk_exists_frozen (h : ApproxWalkOK S x Q Marked c c₀ δ ε) (K : ℕ) :
    ∃ S' : WalkSetup ι σ V, WalkOK S' x Marked
      ∧ S'.markedMass Marked = (∑ v, if Marked v then Q.π v else 0)
      ∧ awk_tv (S.walkSearch K) (S'.walkSearch K) x ≤ walkErr S.T K ε := by
  have hε := h.awk_ε_nonneg
  have hunit : IsQState (c₀ • idealPrep (ι := ι) (σ := σ) Q) := by
    rw [IsQState, qNormSq_smul, awk_isQState_idealPrep, mul_one, Complex.normSq_eq_norm_sq,
      h.c₀_norm, one_pow]
  have hrow : ∀ (U : QRoutine ι σ (V × Option V)) u,
      IsQState (U.run x *ᵥ qBasis (vertE (ι := ι) (σ := σ) u)) := fun U u => by
    rw [IsQState, qNormSq_mulVec (U.run_mem_unitaryGroup x)]
    exact isQState_qBasis _
  obtain ⟨UP, hUP, hUPi⟩ := awk_exists_unitary_mulVec S.hinit hunit
  obtain ⟨WA, hWA, hWAr, hWAc, hWAn⟩ := awk_exists_nearUnitary
    (fun u => {q : QBasis ι σ (V × Option V) | q.2.2.1 = u})
    (fun u v huv => Set.disjoint_left.mpr fun q hu hv => huv (hu.symm.trans hv)) QbSys
    (S.rowA x) (fun u => c • idealRowA Q u) (hrow S.updA)
    (fun u => by
      rw [IsQState, qNormSq_smul, awk_isQState_idealRowA, mul_one, Complex.normSq_eq_norm_sq,
        h.c_norm, one_pow])
    (fun u q hq => ⟨h.a_block u q hq, h.a_supp u q hq⟩)
    (fun u => (awk_idealRowA_supp Q u).smul c) hε h.rowA_close
  obtain ⟨WB, hWB, hWBr, hWBc, hWBn⟩ := awk_exists_nearUnitary
    (fun v => {q : QBasis ι σ (V × Option V) | q.2.2.2 = some v})
    (fun u v huv => Set.disjoint_left.mpr fun q hu hv =>
      huv (Option.some.inj (hu.symm.trans hv))) QbSys
    (S.rowB x) (fun v => c • idealRowB Q v) (hrow S.updB)
    (fun v => by
      rw [IsQState, qNormSq_smul, awk_isQState_idealRowB, mul_one, Complex.normSq_eq_norm_sq,
        h.c_norm, one_pow])
    (fun u q hq => ⟨h.b_block u q hq, h.b_supp u q hq⟩)
    (fun v => (awk_idealRowB_supp Q v).smul c) hε h.rowB_close
  refine ⟨_, h.awk_frozen_walkOK hUP hUPi hWA hWB hWAr hWBr hWAc hWBc,
    h.awk_frozen_markedMass _ rfl,
    awk_tv_walkSearch S x hε _ _ _ _ _ _ _ h.hT ?_ ?_
      (awk_upd_close hWA hWAc h.updA_comm hε hWAn)
      (awk_upd_close hWB hWBc h.updB_comm hε hWBn) (awk_mark_close hε h.mark_close) K⟩
  · rw [QRoutine.ofUnitary_run, hUPi]
    exact h.prep_close
  · rw [QRoutine.ofUnitary_run, hUPi]
    exact (awk_idealPrep_supp Q).smul c₀

/-- **A marked configuration is found** with probability at least `2/3 − walkErr`, if the marked
configurations have stationary mass at least `η` and `⌈1/η⌉ ≤ 9^K`. -/
theorem two_thirds_sub_le (h : ApproxWalkOK S x Q Marked c c₀ δ ε) {η : ℝ} (hη : 0 < η)
    (hm : η ≤ ∑ v, if Marked v then Q.π v else 0) {K : ℕ} (hK : ⌈1 / η⌉₊ ≤ 9 ^ K) :
    2 / 3 - walkErr S.T K ε ≤ (S.walkSearch K).good Marked x := by
  obtain ⟨S', hok, hmass, htv⟩ := h.awk_exists_frozen K
  have hgood := hok.two_thirds_le_walkSearch K hη (by rw [hmass]; exact hm) hK
  have := awk_good_ge Marked (S.walkSearch K) (S'.walkSearch K) x
  linarith

/-- **An unmarked configuration is returned** with probability at most `walkErr`. -/
theorem bad_le (h : ApproxWalkOK S x Q Marked c c₀ δ ε) (K : ℕ) :
    (S.walkSearch K).bad Marked x ≤ walkErr S.T K ε := by
  obtain ⟨S', hok, -, htv⟩ := h.awk_exists_frozen K
  have hbad : (S'.walkSearch K).bad Marked x = 0 :=
    Finset.sum_eq_zero fun v _ => by
      split_ifs with hv
      · rfl
      · exact hok.walkSearch_pr_unmarked K hv
  have := awk_bad_le Marked (S.walkSearch K) (S'.walkSearch K) x
  linarith

/-- **With no marked configuration, `none` is returned** with probability at least
`1 − walkErr`. -/
theorem one_sub_le_none (h : ApproxWalkOK S x Q Marked c c₀ δ ε) (hM : ∀ v, ¬ Marked v)
    (K : ℕ) : 1 - walkErr S.T K ε ≤ (S.walkSearch K).pr x none := by
  obtain ⟨S', hok, -, htv⟩ := h.awk_exists_frozen K
  have hnone := hok.walkSearch_pr_none_of_empty K hM
  have := awk_none_ge (S.walkSearch K) (S'.walkSearch K) x
  linarith

end ApproxWalkOK

end QuantumQueryComplexity
