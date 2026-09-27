import QuantumQueryComplexity.Promise.ComposeShared
import QuantumQueryComplexity.Scan.PerCoord
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# The weighted maximum on a promise domain

The node of a divide-and-conquer recursion is a maximum: its value is the
largest of `h` shifted child values (`LDS/Child.lean`'s
Corollary 35).  The children live on a descriptor fiber, so their solutions are
`DualPairOn`s, and each slot must be read through *its own* value map — slot
`ℓ` projects its child's joint output and adds its own constant offset.

`HasDualOn.maxMapFam` is that combinator:

    max_p m_p (g_p x)   at cost   16 √(∑_p c_p²).

It is `Scan/PerCoord.lean`'s per-coordinate maximum (the outer solution, a
*total* dual on the small cube of child values) fed to
`Promise/ComposeShared.lean` (the inner promise solutions).

Neither the value type `V` nor the order `A` has to be finite, even though the
scan needs a finite alphabet: the promise domain `X` is finite, so the inner
functions take finitely many values, and passing to the image is an output
recoding — `ofKer`, free.  This matters because the values flowing through a
recursion are transcripts and lengths, not letters.

**Projection is legal here.**  A child's dual solution is for its *joint*
output (descriptor chain plus value; see `Adaptive.lean`), and `ofKer`
may never project that joint. The value maps `m_p`
of this theorem are applied *inside the outer function*, which is exactly the
sanctioned place: the outer solution never sees the promise, only the cube of
child values.
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ : Type} [DecidableEq σ]
variable {X : Type} [Fintype X] [DecidableEq X]

/-- **The weighted maximum with per-coordinate value maps, on a promise.**
Subproblem `p` costs `c p`; their maximum, read through the value maps `m p`,
costs `16 √(∑ c²)`. -/
theorem HasDualOn.maxMapFam {P V A : Type} [Fintype P] [DecidableEq P]
    [Nonempty P] [DecidableEq V] [DecidableEq A] [LinearOrder A]
    {read : X → ι → σ} {g : P → X → V} {c : P → ℝ} (hc : ∀ p, 0 < c p)
    (m : P → V → A) (hg : ∀ p, HasDualOn read (g p) (c p)) :
    HasDualOn read (fun x => maxFun fun p => m p (g p x)) (16 * costNorm c) := by
  classical
  -- the values actually taken, on both sides: a finite alphabet for the scan
  set SV : Finset V := Finset.image (fun q : P × X => g q.1 q.2) Finset.univ with hSV
  have hmemV : ∀ (p : P) (x : X), g p x ∈ SV := fun p x =>
    Finset.mem_image_of_mem _ (Finset.mem_univ (p, x))
  set SA : Finset A :=
    Finset.image (fun q : P × P × X => m q.1 (g q.2.1 q.2.2)) Finset.univ with hSA
  have hmemA : ∀ (p : P) (v : V), v ∈ SV → m p v ∈ SA := by
    intro p v hv
    obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨(p, q), Finset.mem_univ _, by rw [← hq]⟩
  set m' : P → {v // v ∈ SV} → {a // a ∈ SA} :=
    fun p v => ⟨m p v.val, hmemA p v.val v.2⟩ with hm'
  set g' : P → X → {v // v ∈ SV} := fun p x => ⟨g p x, hmemV p x⟩ with hg'def
  -- the outer solution: a total dual on the cube of child values
  obtain ⟨Q, hQ⟩ := exists_maxMapFam_dual_isWeightedCostLe (ι := P)
    (σ := {v // v ∈ SV}) (A := {a // a ∈ SA}) m' c hc
  have hginner : ∀ p, HasDualOn read (g' p) (c p) := fun p =>
    (hg p).ofKer fun x y => by simp [hg'def, Subtype.ext_iff]
  have hcomp := hasDualOn_sharedFunOn (P := P) (V := {v // v ∈ SV})
    (O := {a // a ∈ SA}) (h := fun z => maxFun fun p => m' p (z p)) (g := g')
    Q hQ hginner
  -- and back to the original order, an output recoding
  have hcoe : ∀ x : X,
      ((sharedFunOn (fun z => maxFun fun p => m' p (z p)) g' x : {a // a ∈ SA}) : A)
        = maxFun fun p => m p (g p x) := by
    intro x
    simp only [sharedFunOn]
    exact (maxFun_strictMono (φ := fun a : {a // a ∈ SA} => (a : A))
      (fun _ _ h => h) fun p => m' p (g' p x)).symm
  refine hcomp.ofKer fun x y => ?_
  rw [← hcoe x, ← hcoe y]
  exact ⟨fun h => by rw [h], fun h => Subtype.ext h⟩

/-- `costNorm` of a constant weight. -/
lemma costNorm_const {P : Type} [Fintype P] {c₀ : ℝ} (hc₀ : 0 ≤ c₀) :
    costNorm (fun _ : P => c₀) = c₀ * Real.sqrt (Fintype.card P) := by
  simp only [costNorm]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_mul_self hc₀]
  ring

/-- **The maximum of equally expensive subproblems, on a promise**: `h`
subproblems of cost `c₀` give their maximum at cost `16 √h · c₀`.  This is the
`h`-ary node step of the recursion, before the value maps are inserted. -/
theorem HasDualOn.maxConst {P A : Type} [Fintype P] [DecidableEq P] [Nonempty P]
    [DecidableEq A] [LinearOrder A] {read : X → ι → σ} {g : P → X → A} {c₀ : ℝ}
    (hc₀ : 0 < c₀) (hg : ∀ p, HasDualOn read (g p) c₀) :
    HasDualOn read (fun x => maxFun fun p => g p x)
      (16 * (c₀ * Real.sqrt (Fintype.card P))) := by
  have h := HasDualOn.maxMapFam (P := P) (V := A) (A := A) (c := fun _ => c₀)
    (fun _ => hc₀) (fun _ a => a) hg
  rwa [costNorm_const hc₀.le] at h

/-- The same, with value maps: `h` subproblems of cost `c₀`, each read through
its own map, at cost `16 √h · c₀`.  This is the shape `LDS/Recur.lean` uses —
slot `ℓ` maps its child's joint output to `offset ℓ + value`. -/
theorem HasDualOn.maxMapConst {P V A : Type} [Fintype P] [DecidableEq P]
    [Nonempty P] [DecidableEq V] [DecidableEq A] [LinearOrder A]
    {read : X → ι → σ} {g : P → X → V} {c₀ : ℝ} (hc₀ : 0 < c₀) (m : P → V → A)
    (hg : ∀ p, HasDualOn read (g p) c₀) :
    HasDualOn read (fun x => maxFun fun p => m p (g p x))
      (16 * (c₀ * Real.sqrt (Fintype.card P))) := by
  have h := HasDualOn.maxMapFam (P := P) (V := V) (A := A) (c := fun _ => c₀)
    (fun _ => hc₀) m hg
  rwa [costNorm_const hc₀.le] at h

end QuantumQueryComplexity
