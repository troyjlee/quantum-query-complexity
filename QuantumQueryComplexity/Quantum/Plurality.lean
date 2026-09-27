import QuantumQueryComplexity.Quantum.Amplify
import QuantumQueryComplexity.Quantum.LowerBound.Main
set_option synthInstance.maxSize 1600

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Plurality amplification, and the general-output `1/3` lower bound

Milestone H.  For a **Boolean** output the sharp `1/3` lower bound
`(1/36)·ADV±ₚ(f) ≤ Q_{1/3}(f)` needs no amplification
(`LowerBound/MainBool.lean`); for a general finite output type the lower
bound was known only at the characterization's own error,
`(7/32)·ADV±ₚ(f) ≤ Q_{1/16}(f)`.  This file closes the gap by **plurality
amplification**: run a `1/3`-error algorithm `43` times independently and
announce the most frequent answer.

The analysis is an exponential-moment (Markov) bound, not a Chernoff bound
and not a binomial-tail library.  If `W` is the number of wrong runs, the
product structure of the independent-run compiler (`ProductRun.lean`,
exact product statistics) gives

    E[2^W] = ∏ᵢ (1 + Pr[run i wrong]) ≤ (4/3)^43,

so `Pr[W ≥ 22] ≤ (4/3)^43 / 2^22 = 2^64 / 3^43 < 1/16`; and with at most
`21` wrong runs the correct answer has a strict majority, hence is the
plurality.  Thus

    Q_{1/16}(f) ≤ 43·Q_{1/3}(f)      (finite outputs),

and with the `1/16` lower bound, `(7/1376)·ADV±ₚ(f) ≤ Q_{1/3}(f)`.

Contents: the `k`-fold product realization over an arbitrary finite output
type (`Realizes.foldRec`, the Boolean `Realizes.fold` generalized); the
exponential-moment tail `sum_prod_tail_le`; the plurality readout
`plurality` and its majority lemma; `amplify_plurality` at general `k` and
`ε`; and the `43`-run endpoints.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X]
variable {O : Type} [Fintype O] [DecidableEq O]

/-! ## The `k`-fold product realization over any finite output type -/

/-- Prepending a coordinate to a record. -/
def consEquiv (O : Type) (k : ℕ) : O × (Fin k → O) ≃ (Fin (k + 1) → O) where
  toFun p := Fin.cons p.1 p.2
  invFun y := (y 0, fun j => y j.succ)
  left_inv := by
    rintro ⟨b, t⟩
    refine Prod.ext (by simp) (funext fun j => ?_)
    simp
  right_inv := by
    intro y
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp

/-- The trivial realization: no runs, the constant distribution `1` on the
empty record. -/
lemma realizes_zero_rec (read : X → ι → σ) :
    Realizes read 0 (fun (_ : X) (_ : Fin 0 → O) => (1 : ℝ)) := by
  classical
  refine ⟨Unit, inferInstance, inferInstance,
    constAlg ι σ (fun j : Fin 0 => j.elim0), ?_⟩
  intro x o
  have ho : o = fun j : Fin 0 => j.elim0 := funext fun j => j.elim0
  subst ho
  simp [QAlg.prob, constAlg]

/-- **The `k`-fold product realization over any finite output type**: costs
add, distributions multiply. -/
theorem Realizes.foldRec {read : X → ι → σ} :
    ∀ (k : ℕ) (q : Fin k → ℕ) (P : Fin k → X → O → ℝ),
    (∀ j, Realizes read (q j) (P j)) →
    Realizes read (∑ j, q j)
      (fun x (y : Fin k → O) => ∏ j, P j x (y j)) := by
  intro k
  induction k with
  | zero =>
      intro q P _
      rw [show (∑ j : Fin 0, q j) = 0 from by simp]
      exact (realizes_zero_rec read).congr fun x y => by simp
  | succ k ih =>
      intro q P h
      have hfold := ih (fun j => q j.succ) (fun j => P j.succ)
        (fun j => h j.succ)
      have hpair := (h 0).pair hfold
      have hmapped := hpair.map_equiv (consEquiv O k)
      rw [Fin.sum_univ_succ]
      refine hmapped.congr fun x y => ?_
      rw [show (consEquiv O k).symm y = (y 0, fun j => y j.succ) from rfl]
      rw [Fin.prod_univ_succ]

/-! The exponential-moment tail `sum_prod_tail_le` (with `wrongCount`) lives in `Tail.lean`. -/

/-! ## The plurality readout -/

/-- How often `o` occurs in the record `y`. -/
def voteCount {k : ℕ} (y : Fin k → O) (o : O) : ℕ :=
  (Finset.univ.filter (fun j => y j = o)).card

/-- **The plurality readout**: the most frequent value of the record (the
earliest among ties). -/
def plurality {k : ℕ} (y : Fin (k + 1) → O) : O :=
  (((List.finRange (k + 1)).map y).argmax (voteCount y)).getD (y 0)

/-- A strict majority is the plurality. -/
lemma plurality_eq_of_majority {k : ℕ} {y : Fin (k + 1) → O} {o : O}
    (h : k + 1 < 2 * voteCount y o) : plurality y = o := by
  set l := (List.finRange (k + 1)).map y with hl
  have hne : l ≠ [] :=
    List.ne_nil_of_mem (List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩)
  obtain ⟨m, hm⟩ : ∃ m, l.argmax (voteCount y) = some m := by
    rcases hmx : l.argmax (voteCount y) with _ | m
    · exact absurd (List.argmax_eq_none.mp hmx) hne
    · exact ⟨m, rfl⟩
  have hm' : m ∈ l.argmax (voteCount y) := by
    rw [hm]
    rfl
  have ho : o ∈ l := by
    have hpos : 0 < voteCount y o := by omega
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    exact List.mem_map.mpr ⟨j, List.mem_finRange j, (Finset.mem_filter.mp hj).2⟩
  have hle : voteCount y o ≤ voteCount y m := List.le_of_mem_argmax ho hm'
  have hmo : m = o := by
    by_contra hmo
    have hinter : (Finset.univ.filter (fun j => y j = m))
        ∩ (Finset.univ.filter (fun j => y j = o)) = ∅ := by
      ext j
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        exact absurd (h1.symm.trans h2) hmo
      · intro hj
        simp at hj
    have hcard := Finset.card_union_add_card_inter
      (Finset.univ.filter (fun j => y j = m)) (Finset.univ.filter (fun j => y j = o))
    rw [hinter, Finset.card_empty, add_zero] at hcard
    have hle' : ((Finset.univ.filter (fun j => y j = m))
        ∪ (Finset.univ.filter (fun j => y j = o))).card ≤ k + 1 := by
      refine le_trans (Finset.card_le_univ _) ?_
      rw [Fintype.card_fin]
    have hsum : voteCount y m + voteCount y o ≤ k + 1 := by
      rw [voteCount, voteCount, ← hcard]
      exact hle'
    omega
  rw [plurality, hm, Option.getD_some, hmo]

/-- A wrong plurality has at least `⌈(k+1)/2⌉` wrong runs. -/
lemma le_wrongCount_of_plurality_ne {k : ℕ} {y : Fin (k + 1) → O} {o : O}
    (h : plurality y ≠ o) :
    (k + 2) / 2 ≤ wrongCount y (fun _ => o) := by
  have hmaj : ¬ (k + 1 < 2 * voteCount y o) :=
    fun hc => h (plurality_eq_of_majority hc)
  have hsplit : voteCount y o + wrongCount y (fun _ => o) = k + 1 := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun j : Fin (k + 1) => y j = o)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this
  omega

/-! ## Plurality amplification -/

/-- **Plurality amplification.**  `k + 1` independent runs of an algorithm
with error `ε` for a finite-output function, read out by plurality, compute
the same function with error `(1 + ε)^{k+1} / 2^{⌈(k+1)/2⌉}`, at `k + 1`
times the cost. -/
theorem amplify_plurality {read : X → ι → σ} {f : X → O} {q : ℕ} {ε : ℝ}
    (hex : ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : QAlg ι σ O W), ComputesWithErrorOn A q read f ε) (k : ℕ) :
    ∃ (W' : Type) (_ : Fintype W') (_ : DecidableEq W')
      (A' : QAlg ι σ O W'),
      ComputesWithErrorOn A' ((k + 1) * q) read f
        ((1 + ε) ^ (k + 1) / 2 ^ ((k + 2) / 2)) := by
  classical
  obtain ⟨W, hW, hW', A, hA⟩ := hex
  have hbase : Realizes read q (fun x o => A.prob (read x) q o) :=
    ⟨W, hW, hW', A, fun _ _ => rfl⟩
  have hfold := Realizes.foldRec (k + 1) (fun _ => q)
    (fun _ x o => A.prob (read x) q o) (fun _ => hbase)
  have hcost : (∑ _j : Fin (k + 1), q) = (k + 1) * q := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hcost] at hfold
  have hplur := hfold.map (plurality (k := k))
  obtain ⟨W', hW1, hW2, A', hA'⟩ := hplur
  refine ⟨W', hW1, hW2, A', ?_⟩
  intro x
  rw [hA' x (f x)]
  -- the total mass is one
  have htotal : (∑ y : Fin (k + 1) → O, ∏ _j : Fin (k + 1),
      A.prob (read x) q (y _j)) = 1 := by
    rw [← Fintype.prod_sum (fun (_ : Fin (k + 1)) o => A.prob (read x) q o)]
    simp [A.sum_prob]
  have hsplitsum := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun y : Fin (k + 1) → O => plurality y = f x)
    (fun y => ∏ j, A.prob (read x) q (y j))
  rw [htotal] at hsplitsum
  -- the wrong values carry probability at most `ε`
  have hwrongprob : (∑ o ∈ Finset.univ.filter (fun o => o ≠ f x),
      A.prob (read x) q o) ≤ ε := by
    have hsum := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun o : O => o = f x) (fun o => A.prob (read x) q o)
    rw [A.sum_prob, Finset.filter_eq', if_pos (Finset.mem_univ _),
      Finset.sum_singleton] at hsum
    have := hA x
    have hfilter : (Finset.univ.filter (fun o : O => ¬ o = f x))
        = Finset.univ.filter (fun o => o ≠ f x) := rfl
    rw [hfilter] at hsum
    linarith
  -- the wrong-plurality mass is small
  have hwrongmass : (∑ y ∈ Finset.univ.filter
        (fun y : Fin (k + 1) → O => ¬(plurality y = f x)),
      ∏ j, A.prob (read x) q (y j))
      ≤ (1 + ε) ^ (k + 1) / 2 ^ ((k + 2) / 2) := by
    have hsub : Finset.univ.filter
        (fun y : Fin (k + 1) → O => ¬(plurality y = f x))
        ⊆ Finset.univ.filter (fun y : Fin (k + 1) → O =>
          (k + 2) / 2 ≤ wrongCount y (fun _ => f x)) := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact le_wrongCount_of_plurality_ne hy
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun y _ _ => Finset.prod_nonneg fun j _ => A.prob_nonneg _ _ _) ?_
    rw [le_div_iff₀ (by positivity)]
    exact sum_prod_tail_le (fun _ o => A.prob (read x) q o) (fun _ => f x)
      (fun _ o => A.prob_nonneg _ _ _) (fun _ => le_of_eq (A.sum_prob _ _))
      (fun _ => hwrongprob)
  linarith [hsplitsum, hwrongmass]

/-! ## The `43`-run endpoints -/

/-- **`43` runs at error `1/3` give error below `1/16`**:
`(4/3)^43 / 2^22 = 2^64 / 3^43 < 1/16`. -/
theorem fortythree_mem_queryCounts_sixteenth {read : X → ι → σ} {f : X → O}
    {q : ℕ} (hq : q ∈ QueryCounts read f (1 / 3)) :
    43 * q ∈ QueryCounts read f (1 / 16) := by
  obtain ⟨W', hW1, hW2, A', hA'⟩ := amplify_plurality hq 42
  exact ⟨W', hW1, hW2, A', hA'.mono (by norm_num)⟩

variable [Nonempty O] [DecidableEq X]

/-- **`Q_{1/16}(f) ≤ 43·Q_{1/3}(f)`** for finite outputs. -/
theorem qQueryOn_sixteenth_le_fortythree_mul_third {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y) :
    qQueryOn read f (1 / 16) ≤ 43 * qQueryOn read f (1 / 3) :=
  Nat.sInf_le (fortythree_mem_queryCounts_sixteenth
    (Nat.sInf_mem (queryCounts_nonempty hdet (by norm_num))))

/-- **The general-output `1/3` lower bound**:
`(7/1376)·ADV±ₚ(f) ≤ Q_{1/3}(f)` for any finite nonempty output type, on
any promise.  `7/1376 = (7/32)/43`. -/
theorem mul_advPMOn_le_qQueryOn_third_finiteOutput {read : X → ι → σ} {f : X → O}
    (hdet : ∀ x y, read x = read y → f x = f y) :
    (7 / 1376 : ℝ) * advPMOn read f ≤ (qQueryOn read f (1 / 3) : ℝ) := by
  have h16 := mul_advPMOn_le_qQueryOn_of_error_sixteenth hdet
  have h43 : ((qQueryOn read f (1 / 16) : ℕ) : ℝ)
      ≤ 43 * ((qQueryOn read f (1 / 3) : ℕ) : ℝ) := by
    exact_mod_cast qQueryOn_sixteenth_le_fortythree_mul_third hdet
  linarith

/-- The total-function form: `(7/1376)·ADV±(f) ≤ Q_{1/3}(f)`. -/
theorem mul_advPM_le_qQuery_third_finiteOutput (f : (ι → σ) → O) :
    (7 / 1376 : ℝ) * advPM f ≤ (qQuery f (1 / 3) : ℝ) := by
  have h := mul_advPMOn_le_qQueryOn_third_finiteOutput
    (read := (id : (ι → σ) → ι → σ)) (f := f)
    (fun x y hxy => by rw [show x = y from hxy])
  exact h

end QuantumQueryComplexity
