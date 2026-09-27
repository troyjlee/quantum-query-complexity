import QuantumQueryComplexity.Quantum.UniformAlphabet
import QuantumQueryComplexity.Quantum.FiniteHilbert
import QuantumQueryComplexity.Quantum.Routine
import QuantumQueryComplexity.Quantum.StateConversion
import QuantumQueryComplexity.Promise.Defs
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Milestone D: the coherent target states

The second component, and the one that fixes the scaling for everything
after it.  Existing `Witness.lean` is untouched.

The output register must not be indexed by `O` — `O` is an arbitrary
decidable type with no `Fintype` — but it need not be: only the **image** of
`f` is ever occupied, and `Set.range f` is finite whenever `X` is, whatever
`O` is.  So the workspace is `Option ↥(Set.range f)`: one "common"
coordinate beside one coordinate per attained output.  (`X = ∅` is handled
separately by the caller; `[Nonempty O]` is what keeps the readout total.)

The target states are

    t_{x±} = (|common⟩ ± |f x⟩) / √2

and the identity that drives the whole construction is

    ⟪t_{y−}, t_{x+}⟫ = ½·[f y ≠ f x].

**The `½` is load-bearing.**  It is what forces the witness scaling to be

    φ_x = t_{x+} + α·V_x,        w_y = t_{y−} − (2α)⁻¹·U_y,

since then `(2α)⁻¹·α = ½` cancels the `½` above against
`⟪U_y, V_x⟫ = [f y ≠ f x]`, giving **exact** orthogonality `⟪w_y, φ_x⟫ = 0`.
Dropping the `½` — scaling by `α⁻¹` instead — would destroy that
cancellation, and the resulting norm bound `1 + 2α⁻²c` is in any case four
times looser than the correct `1 + c/(2α²)`.

These states are literally the alphabet gadget of `UniformAlphabet.lean`
applied to the alphabet `Set.range f` and rescaled by `(√2)⁻¹`: the `½` in
the overlap is exactly that rescaling squared.  So the `(1, ±e)`
factorization does double duty — packets on `σ`, targets on `range f` — and
the two `½`s that cancel have a common origin.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {X O : Type} [Fintype X] [DecidableEq O] {f : X → O}

/-- The attained output of `x`, as an element of the finite workspace. -/
def rangeElem (f : X → O) (x : X) : ↥(Set.range f) := ⟨f x, ⟨x, rfl⟩⟩

@[simp] lemma rangeElem_val (f : X → O) (x : X) :
    ((rangeElem f x : ↥(Set.range f)) : O) = f x := rfl

lemma rangeElem_eq_iff (f : X → O) (x y : X) :
    rangeElem f x = rangeElem f y ↔ f x = f y := by
  rw [rangeElem, rangeElem, Subtype.ext_iff]

/-- The `+` target state `(|common⟩ + |f x⟩)/√2`. -/
noncomputable def tPlus (f : X → O) (x : X) : Option ↥(Set.range f) → ℝ :=
  (Real.sqrt 2)⁻¹ • uniformLeft (rangeElem f x)

/-- The `−` target state `(|common⟩ − |f x⟩)/√2`. -/
noncomputable def tMinus (f : X → O) (x : X) : Option ↥(Set.range f) → ℝ :=
  (Real.sqrt 2)⁻¹ • uniformRight (rangeElem f x)

lemma inv_sqrt_two_sq : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- The normalization fact in the form the conversion bounds consume. -/
theorem normSq_inv_sqrt_two :
    Complex.normSq ((((Real.sqrt 2)⁻¹ : ℝ)) : ℂ) = 1 / 2 := by
  rw [Complex.normSq_ofReal]
  exact inv_sqrt_two_sq

/-- **The `+` and `−` targets are orthogonal on matching outputs.** -/
theorem tPlus_dotProduct_tMinus (f : X → O) (x y : X) :
    tPlus f x ⬝ᵥ tMinus f y = if f x = f y then 0 else 1 / 2 := by
  rw [tPlus, tMinus, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, inv_sqrt_two_sq, uniform_dotProduct]
  by_cases hxy : f x = f y
  · rw [if_pos ((rangeElem_eq_iff f x y).mpr hxy), if_pos hxy]
    norm_num
  · rw [if_neg (fun h => hxy ((rangeElem_eq_iff f x y).mp h)), if_neg hxy]
    norm_num

/-- **The target states are unit vectors.** -/
theorem tPlus_normSq (f : X → O) (x : X) : tPlus f x ⬝ᵥ tPlus f x = 1 := by
  rw [tPlus, smul_dotProduct, dotProduct_smul, uniformLeft_normSq,
    smul_eq_mul, smul_eq_mul, ← mul_assoc, inv_sqrt_two_sq]
  norm_num

theorem tMinus_normSq (f : X → O) (x : X) : tMinus f x ⬝ᵥ tMinus f x = 1 := by
  rw [tMinus, smul_dotProduct, dotProduct_smul, uniformRight_normSq,
    smul_eq_mul, smul_eq_mul, ← mul_assoc, inv_sqrt_two_sq]
  norm_num

/-- **The driving identity**: `⟪t_{y−}, t_{x+}⟫ = ½·[f y ≠ f x]`.  The `½` is
what forces the `(2α)⁻¹` in the witness scaling. -/
theorem tMinus_dotProduct_tPlus (f : X → O) (x y : X) :
    tMinus f y ⬝ᵥ tPlus f x = if f x = f y then 0 else 1 / 2 := by
  rw [tMinus, tPlus, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, inv_sqrt_two_sq,
    dotProduct_comm (uniformRight (rangeElem f y)) (uniformLeft (rangeElem f x)),
    uniform_dotProduct]
  by_cases hxy : f x = f y
  · rw [if_pos ((rangeElem_eq_iff f x y).mpr hxy), if_pos hxy]
    norm_num
  · rw [if_neg (fun h => hxy ((rangeElem_eq_iff f x y).mp h)), if_neg hxy]
    norm_num

/-- The same identity in the form the orthogonality computation uses: the
overlap is `½` exactly on the pairs the dual constraint has to separate. -/
theorem tMinus_dotProduct_tPlus_of_ne (f : X → O) {x y : X} (h : f x ≠ f y) :
    tMinus f y ⬝ᵥ tPlus f x = 1 / 2 := by
  rw [tMinus_dotProduct_tPlus, if_neg h]

theorem tMinus_dotProduct_tPlus_of_eq (f : X → O) {x y : X} (h : f x = f y) :
    tMinus f y ⬝ᵥ tPlus f x = 0 := by
  rw [tMinus_dotProduct_tPlus, if_pos h]

/-! ## The common and output vectors

The conversion combines the two signed targets through

    common = (t_{x+} + t_{x−})/√2        out(f x) = (t_{x+} − t_{x−})/√2,

which are exactly the constant coordinate and the attained-output
coordinate: the algorithm starts on the input-**independent** `common`
state, and the detector carries it onto the output-labelled unit vector.
Distinct outputs give orthogonal `out` vectors, which is what the final
readout measures — one coherent conversion, never one detector per
output. -/

/-- The common initial vector: the constant coordinate alone. -/
def commonVec {R : Type} : Option R → ℝ
  | none => 1
  | some _ => 0

/-- The output-labelled vector: the coordinate of one attained output. -/
def outVec {R : Type} [DecidableEq R] (r : R) : Option R → ℝ
  | none => 0
  | some s => if s = r then 1 else 0

@[simp] lemma commonVec_none {R : Type} : commonVec (R := R) none = 1 := rfl

@[simp] lemma commonVec_some {R : Type} (r : R) :
    commonVec (some r) = 0 := rfl

@[simp] lemma outVec_none {R : Type} [DecidableEq R] (r : R) :
    outVec r none = 0 := rfl

@[simp] lemma outVec_some {R : Type} [DecidableEq R] (r s : R) :
    outVec r (some s) = if s = r then 1 else 0 := rfl

/-- The common vector is a unit vector. -/
theorem commonVec_dotProduct_commonVec {R : Type} [Fintype R] :
    (commonVec (R := R)) ⬝ᵥ commonVec = 1 := by
  rw [dotProduct, Fintype.sum_option]
  simp

/-- **The output vectors are orthonormal**: the pairing is the equality
indicator. -/
theorem outVec_dotProduct_outVec {R : Type} [Fintype R] [DecidableEq R]
    (r r' : R) : outVec r ⬝ᵥ outVec r' = if r = r' then 1 else 0 := by
  rw [dotProduct, Fintype.sum_option]
  have hterm : ∀ s : R, outVec r (some s) * outVec r' (some s)
      = if s = r then (if r = r' then (1 : ℝ) else 0) else 0 := by
    intro s
    rw [outVec_some, outVec_some]
    by_cases hs : s = r
    · rw [if_pos hs, if_pos hs, one_mul, hs]
    · rw [if_neg hs, if_neg hs, zero_mul]
  rw [Finset.sum_congr rfl fun s _ => hterm s]
  simp

/-- The common and output vectors are orthogonal. -/
theorem commonVec_dotProduct_outVec {R : Type} [Fintype R] [DecidableEq R]
    (r : R) : commonVec ⬝ᵥ outVec r = 0 := by
  rw [dotProduct, Fintype.sum_option]
  simp

theorem outVec_dotProduct_commonVec {R : Type} [Fintype R] [DecidableEq R]
    (r : R) : outVec r ⬝ᵥ commonVec = 0 := by
  rw [dotProduct, Fintype.sum_option]
  simp

/-- **`(t₊ + t₋)/√2` is exactly the common vector** — the `x`-dependence
cancels. -/
theorem smul_tPlus_add_tMinus (f : X → O) (x : X) :
    (Real.sqrt 2)⁻¹ • (tPlus f x + tMinus f x) = commonVec := by
  funext s
  cases s with
  | none =>
    simp only [Pi.smul_apply, Pi.add_apply, tPlus, tMinus, smul_eq_mul,
      uniformLeft_none, uniformRight_none, commonVec_none]
    linear_combination 2 * inv_sqrt_two_sq
  | some r =>
    simp only [Pi.smul_apply, Pi.add_apply, tPlus, tMinus, smul_eq_mul,
      uniformLeft_some, uniformRight_some, commonVec_some]
    by_cases h : r = rangeElem f x
    · rw [if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h]
      ring

/-- **`(t₊ − t₋)/√2` is exactly the output-labelled vector.** -/
theorem smul_tPlus_sub_tMinus (f : X → O) (x : X) :
    (Real.sqrt 2)⁻¹ • (tPlus f x - tMinus f x) = outVec (rangeElem f x) := by
  funext s
  cases s with
  | none =>
    simp only [Pi.smul_apply, Pi.sub_apply, tPlus, tMinus, smul_eq_mul,
      uniformLeft_none, uniformRight_none, outVec_none]
    ring
  | some r =>
    simp only [Pi.smul_apply, Pi.sub_apply, tPlus, tMinus, smul_eq_mul,
      uniformLeft_some, uniformRight_some, outVec_some]
    by_cases h : r = rangeElem f x
    · rw [if_pos h, if_pos h]
      linear_combination 2 * inv_sqrt_two_sq
    · rw [if_neg h, if_neg h]
      ring


/-! ## The tagged query packets

The packet register is one `Option σ` block **per pair `(i, k)`** — every
pair carries its own flag coordinate.  A shared flag would make different
blocks overlap, and the whole point of the construction is that they do not.

    g_{i,k}         = idleFlag_{i,k} + activeBlank_{i,k}
    leftAtom_{i,k,a}  = idleFlag_{i,k} + answer_{i,k,a}      (the oracle image)
    rightAtom_{i,k,a} = idleFlag_{i,k} − answer_{i,k,a}

Inside a block these are exactly `uniformLeft` and `uniformRight`, so the
`[a ≠ b]` factorization is inherited blockwise, and distinct blocks are
orthogonal.  The ambient space is the target register **direct-summed** with
the packet blocks, which makes every target/packet cross term vanish by
construction. -/

section Packets

variable {R ι σ K : Type} [Fintype R] [DecidableEq R] [Fintype ι]
  [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype K] [DecidableEq K]

/-- The ambient index: the target register, direct-summed with one
`Option σ` packet block per `(i, k)`. -/
abbrev UBasis (R ι σ K : Type) : Type :=
  Option R ⊕ ((ι × K) × Option σ)

/-- A target-register vector, embedded. -/
def uTarget (t : Option R → ℝ) : UBasis R ι σ K → ℂ :=
  Sum.elim (fun s => ((t s : ℝ) : ℂ)) fun _ => 0

lemma uTarget_add (t t' : Option R → ℝ) :
    uTarget (ι := ι) (σ := σ) (K := K) (t + t')
      = uTarget t + uTarget t' := by
  funext b
  cases b with
  | inl s => simp [uTarget]
  | inr q => simp [uTarget]

lemma uTarget_sub (t t' : Option R → ℝ) :
    uTarget (ι := ι) (σ := σ) (K := K) (t - t')
      = uTarget t - uTarget t' := by
  funext b
  cases b with
  | inl s => simp [uTarget]
  | inr q => simp [uTarget]

/-- Real scaling of the target vector is complex scaling of its
embedding. -/
lemma uTarget_realSmul (r : ℝ) (t : Option R → ℝ) :
    uTarget (ι := ι) (σ := σ) (K := K) (r • t)
      = ((r : ℝ) : ℂ) • uTarget t := by
  funext b
  cases b with
  | inl s => simp [uTarget]
  | inr q => simp [uTarget]

/-- A real vector placed in the packet block `p`, zero elsewhere.  Every
block carries its own flag coordinate, which is what keeps distinct blocks
orthogonal. -/
def blockVec (p : ι × K) (w : Option σ → ℝ) : UBasis R ι σ K → ℂ :=
  Sum.elim (fun _ => 0) fun q => if q.1 = p then ((w q.2 : ℝ) : ℂ) else 0

/-- **The one computation the packet layer needs**: blocks are orthogonal,
and inside a block the pairing is the real one. -/
theorem qInner_blockVec (p p' : ι × K) (w w' : Option σ → ℝ) :
    qInner (blockVec (R := R) p w) (blockVec p' w')
      = if p = p' then ((w ⬝ᵥ w' : ℝ) : ℂ) else 0 := by
  classical
  rw [qInner_def, Fintype.sum_sum_type]
  have hL : (∑ s : Option R, star (blockVec (R := R) p w (Sum.inl s))
      * blockVec (R := R) p' w' (Sum.inl s)) = 0 := by
    simp [blockVec]
  rw [hL, zero_add, Fintype.sum_prod_type]
  by_cases hb : p = p'
  · subst hb
    rw [if_pos rfl]
    have hterm : ∀ r : ι × K, (∑ s : Option σ,
          star (blockVec (R := R) p w (Sum.inr (r, s)))
            * blockVec (R := R) p w' (Sum.inr (r, s)))
        = if r = p then ((w ⬝ᵥ w' : ℝ) : ℂ) else 0 := by
      intro r
      by_cases hr : r = p
      · rw [if_pos hr]
        have hs : ∀ s : Option σ,
            star (blockVec (R := R) p w (Sum.inr (r, s)))
              * blockVec (R := R) p w' (Sum.inr (r, s))
            = ((w s * w' s : ℝ) : ℂ) := by
          intro s
          simp only [blockVec, Sum.elim_inr, if_pos hr]
          rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
        rw [Finset.sum_congr rfl fun s _ => hs s, ← Complex.ofReal_sum,
          ← dotProduct]
      · rw [if_neg hr]
        refine Finset.sum_eq_zero fun s _ => ?_
        simp only [blockVec, Sum.elim_inr, if_neg hr]
        simp
    rw [Finset.sum_congr rfl fun r _ => hterm r,
      Finset.sum_ite_eq' Finset.univ p (fun _ => ((w ⬝ᵥ w' : ℝ) : ℂ)),
      if_pos (Finset.mem_univ _)]
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s _ => ?_
    simp only [blockVec, Sum.elim_inr]
    by_cases hr : r = p
    · rw [if_pos hr, if_neg (fun h => hb (hr.symm.trans h))]
      simp
    · rw [if_neg hr]
      simp

/-- `idleFlag_{i,k} + answer_{i,k,a}`: the oracle image of the tagged
generator `g_{i,k} = idleFlag_{i,k} + activeBlank_{i,k}`. -/
def leftAtom (i : ι) (k : K) (a : σ) : UBasis R ι σ K → ℂ :=
  blockVec (i, k) (uniformLeft a)

/-- `idleFlag_{i,k} − answer_{i,k,a}`. -/
def rightAtom (i : ι) (k : K) (a : σ) : UBasis R ι σ K → ℂ :=
  blockVec (i, k) (uniformRight a)

/-- **The blockwise factorization**: distinct blocks are orthogonal, and
inside a block the pairing is the inequality indicator. -/
theorem qInner_leftAtom_rightAtom (i : ι) (k : K) (a : σ) (j : ι) (l : K)
    (b : σ) :
    qInner (leftAtom (R := R) i k a) (rightAtom j l b)
      = if (i, k) = (j, l) then (if a = b then 0 else 1) else 0 := by
  rw [leftAtom, rightAtom, qInner_blockVec, uniform_dotProduct]
  by_cases hb : (i, k) = (j, l)
  · rw [if_pos hb, if_pos hb]
    by_cases hab : a = b <;> simp [hab]
  · rw [if_neg hb, if_neg hb]

/-- **Each atom has squared norm `2`** — independently of the alphabet. -/
theorem qInner_leftAtom_self (i : ι) (k : K) (a : σ) :
    qInner (leftAtom (R := R) i k a) (leftAtom i k a) = 2 := by
  rw [leftAtom, qInner_blockVec, if_pos rfl, uniformLeft_normSq]
  norm_num

theorem qInner_rightAtom_self (i : ι) (k : K) (a : σ) :
    qInner (rightAtom (R := R) i k a) (rightAtom i k a) = 2 := by
  rw [rightAtom, qInner_blockVec, if_pos rfl, uniformRight_normSq]
  norm_num

/-- **Targets and packets never interfere**: they sit in complementary
summands. -/
@[simp] theorem qInner_uTarget_blockVec (t : Option R → ℝ) (p : ι × K)
    (w : Option σ → ℝ) :
    qInner (uTarget (ι := ι) (σ := σ) (K := K) t) (blockVec p w) = 0 := by
  rw [qInner_def, Fintype.sum_sum_type]
  simp [uTarget, blockVec]

@[simp] theorem qInner_blockVec_uTarget (p : ι × K) (w : Option σ → ℝ)
    (t : Option R → ℝ) :
    qInner (blockVec (R := R) p w) (uTarget t) = 0 := by
  rw [qInner_def, Fintype.sum_sum_type]
  simp [uTarget, blockVec]

end Packets


/-! ## The packets of a dual solution

`U_x` and `V_x` are the two dual families spent against the tagged atoms —
`u` on the left (oracle images), `v` on the right — *without* swapping the
families.  One bilinear computation (`qInner_sum_blockVec`) serves both the
cross pairing and the norms, exactly as `qInner_blockVec` served the atoms. -/

section Packets2

variable {R ι σ K X : Type} [Fintype R] [DecidableEq R] [Fintype ι]
  [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype K] [DecidableEq K]
  [Fintype X]

/-- **The one bilinear computation of the packet layer.**  Block-diagonal by
construction, so only the diagonal survives. -/
theorem qInner_sum_blockVec (c d : ι × K → ℝ) (w w' : ι × K → Option σ → ℝ) :
    qInner (∑ p : ι × K, ((c p : ℝ) : ℂ) • blockVec (R := R) p (w p))
        (∑ p : ι × K, ((d p : ℝ) : ℂ) • blockVec (R := R) p (w' p))
      = ((∑ p : ι × K, c p * d p * (w p ⬝ᵥ w' p) : ℝ) : ℂ) := by
  classical
  rw [qInner_sum_left]
  have hrow : ∀ p : ι × K,
      qInner (((c p : ℝ) : ℂ) • blockVec (R := R) p (w p))
          (∑ q : ι × K, ((d q : ℝ) : ℂ) • blockVec (R := R) q (w' q))
        = ((c p * d p * (w p ⬝ᵥ w' p) : ℝ) : ℂ) := by
    intro p
    rw [qInner_smul_left, qInner_sum_right]
    have hin : ∀ q : ι × K,
        qInner (blockVec (R := R) p (w p)) (((d q : ℝ) : ℂ) • blockVec q (w' q))
          = if q = p then ((d p * (w p ⬝ᵥ w' p) : ℝ) : ℂ) else 0 := by
      intro q
      rw [qInner_smul_right, qInner_blockVec]
      by_cases hq : p = q
      · rw [if_pos hq, if_pos hq.symm, ← hq]
        push_cast
        ring
      · rw [if_neg hq, if_neg (fun h => hq h.symm)]
        ring
    rw [Finset.sum_congr rfl fun q _ => hin q,
      Finset.sum_ite_eq' Finset.univ p
        (fun _ => ((d p * (w p ⬝ᵥ w' p) : ℝ) : ℂ)),
      if_pos (Finset.mem_univ _), Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun p _ => hrow p, ← Complex.ofReal_sum]

/-- The left packet: the `u`-family against the oracle images. -/
noncomputable def packetU (u : X → ι → K → ℝ) (read : X → ι → σ) (x : X) :
    UBasis R ι σ K → ℂ :=
  ∑ p : ι × K, ((u x p.1 p.2 : ℝ) : ℂ) • blockVec p (uniformLeft (read x p.1))

/-- The right packet: the `v`-family against the flipped atoms. -/
noncomputable def packetV (v : X → ι → K → ℝ) (read : X → ι → σ) (x : X) :
    UBasis R ι σ K → ℂ :=
  ∑ p : ι × K, ((v x p.1 p.2 : ℝ) : ℂ) • blockVec p (uniformRight (read x p.1))

/-- **The cross pairing is the dual constraint's left-hand side**, verbatim
and with the families unswapped. -/
theorem qInner_packetU_packetV (u v : X → ι → K → ℝ) (read : X → ι → σ)
    (y x : X) :
    qInner (packetU (R := R) u read y) (packetV v read x)
      = ((∑ i, if read y i = read x i then 0
            else ∑ k, u y i k * v x i k : ℝ) : ℂ) := by
  classical
  rw [packetU, packetV, qInner_sum_blockVec]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : read y i = read x i
  · rw [if_pos hi]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [uniform_dotProduct, if_pos hi]
    ring
  · rw [if_neg hi]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [uniform_dotProduct, if_neg hi]
    ring

/-- The same, evaluated on a feasible dual solution: the packets realise the
inequality indicator of the **outputs**. -/
theorem qInner_packetU_packetV_of_dualPairOn {O : Type} [DecidableEq O]
    {read : X → ι → σ} {f : X → O} (P : DualPairOn read K f) (y x : X) :
    qInner (packetU (R := R) P.u read y) (packetV P.v read x)
      = if f y = f x then 0 else 1 := by
  rw [qInner_packetU_packetV, P.constraint y x]
  by_cases h : f y = f x <;> simp [h]

/-- **The exact norms**: `‖U_x‖² = 2·∑ u²`, no alphabet anywhere. -/
theorem qInner_packetU_self (u : X → ι → K → ℝ) (read : X → ι → σ) (x : X) :
    qInner (packetU (R := R) u read x) (packetU u read x)
      = ((2 * ∑ p : ι × K, u x p.1 p.2 * u x p.1 p.2 : ℝ) : ℂ) := by
  rw [packetU, qInner_sum_blockVec]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [uniformLeft_normSq]
  ring

theorem qInner_packetV_self (v : X → ι → K → ℝ) (read : X → ι → σ) (x : X) :
    qInner (packetV (R := R) v read x) (packetV v read x)
      = ((2 * ∑ p : ι × K, v x p.1 p.2 * v x p.1 p.2 : ℝ) : ℂ) := by
  rw [packetV, qInner_sum_blockVec]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [uniformRight_normSq]
  ring

/-- Targets never meet packets. -/
@[simp] theorem qInner_uTarget_packetU (t : Option R → ℝ)
    (u : X → ι → K → ℝ) (read : X → ι → σ) (x : X) :
    qInner (uTarget (ι := ι) (σ := σ) (K := K) t) (packetU u read x) = 0 := by
  rw [packetU, qInner_sum_right]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [qInner_smul_right, qInner_uTarget_blockVec, mul_zero]

@[simp] theorem qInner_uTarget_packetV (t : Option R → ℝ)
    (v : X → ι → K → ℝ) (read : X → ι → σ) (x : X) :
    qInner (uTarget (ι := ι) (σ := σ) (K := K) t) (packetV v read x) = 0 := by
  rw [packetV, qInner_sum_right]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [qInner_smul_right, qInner_uTarget_blockVec, mul_zero]

@[simp] theorem qInner_packetU_uTarget (u : X → ι → K → ℝ)
    (read : X → ι → σ) (x : X) (t : Option R → ℝ) :
    qInner (packetU (R := R) u read x) (uTarget t) = 0 := by
  rw [packetU, qInner_sum_left]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [qInner_smul_left, qInner_blockVec_uTarget, mul_zero]

end Packets2


/-! ## Two convenience pairings

`qInner_uTarget_uTarget` transfers every target norm and overlap from the
real computation of the first section without repeating the real-to-complex
step; `qInner_packetV_uTarget` makes the `‖φ‖²` expansion symmetric. -/

section TargetPairings

variable {R ι σ K X : Type} [Fintype R] [DecidableEq R] [Fintype ι]
  [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype K] [DecidableEq K]
  [Fintype X]

@[simp] theorem qInner_uTarget_uTarget (t t' : Option R → ℝ) :
    qInner (uTarget (ι := ι) (σ := σ) (K := K) t) (uTarget t')
      = ((t ⬝ᵥ t' : ℝ) : ℂ) := by
  rw [qInner_def, Fintype.sum_sum_type]
  have hR : (∑ p : (ι × K) × Option σ,
      star (uTarget (R := R) (ι := ι) (σ := σ) (K := K) t
          ((Sum.inr p : UBasis R ι σ K)))
        * uTarget (ι := ι) (σ := σ) (K := K) t' (Sum.inr p)) = 0 := by
    simp [uTarget]
  rw [hR, add_zero]
  have hL : ∀ s : Option R,
      star (uTarget (R := R) (ι := ι) (σ := σ) (K := K) t
          ((Sum.inl s : UBasis R ι σ K)))
        * uTarget (ι := ι) (σ := σ) (K := K) t' (Sum.inl s)
        = ((t s * t' s : ℝ) : ℂ) := by
    intro s
    simp only [uTarget, Sum.elim_inl]
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [Finset.sum_congr rfl fun s _ => hL s, ← Complex.ofReal_sum, ← dotProduct]

@[simp] theorem qInner_packetV_uTarget (v : X → ι → K → ℝ)
    (read : X → ι → σ) (x : X) (t : Option R → ℝ) :
    qInner (packetV (R := R) v read x) (uTarget t) = 0 := by
  rw [packetV, qInner_sum_left]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [qInner_smul_left, qInner_blockVec_uTarget, mul_zero]

end TargetPairings

/-! ## Operational realization

`UBasis` is an abstract Hilbert basis: it cannot be handed to `oracleMat` or
`inputProj`, which live on `QBasis`.  The realization places it inside a
genuine query basis whose workspace is

    UWork R ι K = Option R ⊕ (ι × K)

— the target register, or the name of a packet block — by

    target s            ↦ (none,   none,   Sum.inl s)
    block (i,k), ⊥      ↦ (none,   none,   Sum.inr (i,k))
    block (i,k), some a ↦ (some i, some a, Sum.inr (i,k))

so a block's flag coordinate is *idle* (no index queried) and its answer
coordinates are *active at the block's own index*.  That is exactly what
makes the oracle carry the physical generator

    gen (i,k) = |⊥, ⊥, (i,k)⟩ + |i, ⊥, (i,k)⟩

onto the `leftAtom` packet: the second summand is the active-blank register,
which the transposition oracle fills with `some (a i)`.

The embedding is injective but not surjective; `uRealize` extends by zero,
which is why it preserves `qInner` and `qNormSq` on the nose. -/

section Realization

variable {R ι σ K : Type} [Fintype R] [DecidableEq R] [Fintype ι]
  [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype K] [DecidableEq K]

/-- The workspace of the realized space: the target register, or the name of
a packet block. -/
abbrev UWork (R ι K : Type) : Type := Option R ⊕ (ι × K)

/-- The realized query basis. -/
abbrev UQBasis (R ι σ K : Type) : Type := QBasis ι σ (UWork R ι K)

/-- The realization: place an abstract vector in the query basis, extending
by zero off the embedded coordinates. -/
def uRealize (ψ : UBasis R ι σ K → ℂ) : UQBasis R ι σ K → ℂ := fun q =>
  match q with
  | (none, none, Sum.inl s) => ψ (Sum.inl s)
  | (none, none, Sum.inr p) => ψ (Sum.inr (p, none))
  | (some i, some a, Sum.inr p) =>
      if p.1 = i then ψ (Sum.inr (p, some a)) else 0
  | _ => 0

@[simp] lemma uRealize_target (ψ : UBasis R ι σ K → ℂ) (s : Option R) :
    uRealize ψ ((none, none, Sum.inl s) : UQBasis R ι σ K) = ψ (Sum.inl s) :=
  rfl

@[simp] lemma uRealize_flag (ψ : UBasis R ι σ K → ℂ) (p : ι × K) :
    uRealize ψ ((none, none, Sum.inr p) : UQBasis R ι σ K)
      = ψ (Sum.inr (p, none)) := rfl

@[simp] lemma uRealize_answer (ψ : UBasis R ι σ K → ℂ) (i : ι) (a : σ)
    (p : ι × K) :
    uRealize ψ ((some i, some a, Sum.inr p) : UQBasis R ι σ K)
      = if p.1 = i then ψ (Sum.inr (p, some a)) else 0 := rfl

/-- The embedding itself, as a function.  **Its image is not
oracle-invariant**: the oracle swaps a realized answer coordinate with the
*active-blank* coordinate `(some i, none, Sum.inr (i,k))`, which is
deliberately outside the image.  So there is no general theorem
`oracleMat a *ᵥ uRealize ψ = uRealize (…)` — that statement is false, and
only the generator-specific identities below hold. -/
def uEmb : UBasis R ι σ K → UQBasis R ι σ K
  | Sum.inl s => (none, none, Sum.inl s)
  | Sum.inr (p, none) => (none, none, Sum.inr p)
  | Sum.inr (p, some a) => (some p.1, some a, Sum.inr p)

@[simp] lemma uRealize_uEmb (ψ : UBasis R ι σ K → ℂ) (b : UBasis R ι σ K) :
    uRealize ψ (uEmb b) = ψ b := by
  obtain (s | ⟨p, a⟩) := b
  · rfl
  · cases a
    · rfl
    · change (if p.1 = p.1 then _ else _) = _
      rw [if_pos rfl]

lemma uEmb_injective : Function.Injective (uEmb (R := R) (ι := ι) (σ := σ)
    (K := K)) := by
  rintro (s | ⟨p, a⟩) (s' | ⟨p', a'⟩) h
  · exact congrArg Sum.inl (by simpa [uEmb] using h)
  · cases a' <;> simp [uEmb] at h
  · cases a <;> simp [uEmb] at h
  · cases a <;> cases a' <;> simp [uEmb] at h ⊢ <;> tauto

/-- Off the image the realization vanishes — which is what makes it an
isometry. -/
lemma uRealize_eq_zero_of_forall_ne (ψ : UBasis R ι σ K → ℂ)
    {q : UQBasis R ι σ K} (h : ∀ b, uEmb b ≠ q) : uRealize ψ q = 0 := by
  by_contra hne
  obtain ⟨i, a, w⟩ := q
  cases i with
  | none =>
      cases a with
      | none =>
          cases w with
          | inl s => exact h (Sum.inl s) rfl
          | inr p => exact h (Sum.inr (p, none)) rfl
      | some a => exact hne rfl
  | some i =>
      cases a with
      | none => exact hne rfl
      | some a =>
          cases w with
          | inl s => exact hne rfl
          | inr p =>
              by_cases hp : p.1 = i
              · refine h (Sum.inr (p, some a)) ?_
                rw [uEmb, hp]
              · exact hne (by rw [uRealize_answer, if_neg hp])

/-- **The master isometry.** -/
theorem qInner_uRealize (ψ φ : UBasis R ι σ K → ℂ) :
    qInner (uRealize ψ) (uRealize φ) = qInner ψ φ := by
  classical
  rw [qInner_def, qInner_def]
  have hsub : (∑ q : UQBasis R ι σ K, star (uRealize ψ q) * uRealize φ q)
      = ∑ q ∈ Finset.univ.image (uEmb (R := R) (ι := ι) (σ := σ) (K := K)),
          star (uRealize ψ q) * uRealize φ q := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro q _ hq
    rw [uRealize_eq_zero_of_forall_ne ψ (fun b hb => hq (by
      rw [Finset.mem_image]
      exact ⟨b, Finset.mem_univ b, hb⟩))]
    simp
  rw [hsub, Finset.sum_image fun b _ b' _ hbb => uEmb_injective hbb]
  exact Finset.sum_congr rfl fun b _ => by rw [uRealize_uEmb, uRealize_uEmb]

theorem qNormSq_uRealize (ψ : UBasis R ι σ K → ℂ) :
    qNormSq (uRealize ψ) = qNormSq ψ := by
  have h := qInner_uRealize ψ ψ
  rw [qInner_self, qInner_self] at h
  exact_mod_cast h

@[simp] lemma uRealize_zero :
    uRealize (0 : UBasis R ι σ K → ℂ) = 0 := by
  funext q
  obtain ⟨i, a, w⟩ := q
  cases i <;> cases a <;> cases w <;>
    simp only [uRealize, Pi.zero_apply] <;>
    first
      | rfl
      | (split_ifs <;> simp)

lemma uRealize_add (ψ φ : UBasis R ι σ K → ℂ) :
    uRealize (ψ + φ) = uRealize ψ + uRealize φ := by
  funext q
  obtain ⟨i, a, w⟩ := q
  cases i <;> cases a <;> cases w <;>
    simp only [uRealize, Pi.add_apply] <;>
    first
      | rfl
      | (split_ifs <;> simp)
      | simp

lemma uRealize_sub (ψ φ : UBasis R ι σ K → ℂ) :
    uRealize (ψ - φ) = uRealize ψ - uRealize φ := by
  funext q
  obtain ⟨i, a, w⟩ := q
  cases i <;> cases a <;> cases w <;>
    simp only [uRealize, Pi.sub_apply] <;>
    first
      | rfl
      | (split_ifs <;> simp)
      | simp

lemma uRealize_sum {α : Type*} (s : Finset α) (F : α → (UBasis R ι σ K → ℂ)) :
    uRealize (∑ a ∈ s, F a) = ∑ a ∈ s, uRealize (F a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [uRealize_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, uRealize_add, ih]

lemma uRealize_smul (c : ℂ) (ψ : UBasis R ι σ K → ℂ) :
    uRealize (c • ψ) = c • uRealize ψ := by
  funext q
  obtain ⟨i, a, w⟩ := q
  cases i <;> cases a <;> cases w <;>
    simp only [uRealize, Pi.smul_apply, smul_eq_mul] <;>
    first
      | rfl
      | (split_ifs <;> simp)
      | simp

end Realization


/-! ## The physical generator

    idleFlag p     = |⊥, ⊥, p⟩
    activeBlank p  = |p.1, ⊥, p⟩
    uniformGen p   = idleFlag p + activeBlank p

The oracle fixes the idle summand (no index is queried there) and fills the
active blank with `some (a p.1)`, so it carries the generator exactly onto
the realized `leftAtom` packet.  This is the **generator-specific transport
identity** the construction uses — *arbitrary* `uRealize` transport is false
(the image is not oracle-invariant, and the active-blank coordinate is
precisely the off-image coordinate the oracle uses), though linear
combinations of generator identities of course still hold. -/

section Generator

variable {R ι σ K : Type} [Fintype R] [DecidableEq R] [Fintype ι]
  [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype K] [DecidableEq K]

/-- `|⊥, ⊥, p⟩` — the block's flag, idle. -/
def idleFlag (p : ι × K) : UQBasis R ι σ K → ℂ :=
  qBasis ((none, none, Sum.inr p) : UQBasis R ι σ K)

/-- `|p.1, ⊥, p⟩` — the block's blank answer register, active at its own
index.  **Outside the image of `uRealize`**, by design. -/
def activeBlank (p : ι × K) : UQBasis R ι σ K → ℂ :=
  qBasis ((some p.1, none, Sum.inr p) : UQBasis R ι σ K)

/-- The tagged generator `g_{i,k}`. -/
def uniformGen (p : ι × K) : UQBasis R ι σ K → ℂ := idleFlag p + activeBlank p

/-- The realized `leftAtom` is a two-term basis sum. -/
lemma uRealize_leftAtom (i : ι) (k : K) (c : σ) :
    uRealize (leftAtom (R := R) i k c)
      = qBasis ((none, none, Sum.inr (i, k)) : UQBasis R ι σ K)
        + qBasis ((some i, some c, Sum.inr (i, k)) : UQBasis R ι σ K) := by
  classical
  funext q
  obtain ⟨j, x, w⟩ := q
  cases j with
  | none =>
      cases x with
      | none =>
          cases w with
          | inl s => simp [uRealize, leftAtom, blockVec, qBasis_apply]
          | inr p =>
              by_cases hp : p = (i, k)
              · subst hp
                simp [uRealize, leftAtom, blockVec, qBasis_apply]
              · simp [uRealize, leftAtom, blockVec, qBasis_apply, hp]
      | some x => cases w <;> simp [uRealize, qBasis_apply]
  | some j =>
      cases x with
      | none => cases w <;> simp [uRealize, qBasis_apply]
      | some x =>
          cases w with
          | inl s => simp [uRealize, blockVec, qBasis_apply]
          | inr p =>
              by_cases hp : p = (i, k)
              · subst hp
                by_cases hj : j = i
                · subst hj
                  by_cases hx : x = c
                  · subst hx
                    simp [uRealize, leftAtom, blockVec, qBasis_apply]
                  · simp [uRealize, leftAtom, blockVec, qBasis_apply, hx]
                · simp [uRealize, leftAtom, blockVec, qBasis_apply, hj,
                    Ne.symm hj]
              · simp [uRealize, leftAtom, blockVec, qBasis_apply, hp]

/-- **The generator-specific transport identity.** -/
theorem oracleMat_mulVec_uniformGen (a : ι → σ) (p : ι × K) :
    oracleMat a *ᵥ uniformGen (R := R) p
      = uRealize (leftAtom p.1 p.2 (a p.1)) := by
  rw [uniformGen, Matrix.mulVec_add, idleFlag, activeBlank, oracleMat,
    qPerm_mulVec_qBasis, qPerm_mulVec_qBasis, uRealize_leftAtom,
    oraclePerm_apply, oraclePerm_apply, oracleMap_none, oracleMap_some,
    Equiv.swap_apply_left]

/-- **The scalar pullback the projector proof consumes**: testing a realized
vector against a generator, through the oracle, is testing it against the
`leftAtom` packet. -/
theorem qInner_uniformGen_oracle_uRealize (a : ι → σ) (p : ι × K)
    (ψ : UBasis R ι σ K → ℂ) :
    qInner (uniformGen p) (oracleMat a *ᵥ uRealize ψ)
      = qInner (leftAtom p.1 p.2 (a p.1)) ψ := by
  rw [← QRoutine.oracleMat_conjTranspose a, ← qInner_mulVec_left,
    oracleMat_mulVec_uniformGen, qInner_uRealize]

/-- **The per-generator cancellation.**  `inputProj` asks orthogonality
against *each* generator separately, so the aggregate `⟪U, V⟫` identity is
not enough: this is the statement that on the *same* input the letters agree
in every block, so every term of `V_x` is killed. -/
theorem qInner_leftAtom_packetV_same {X : Type}
    (v : X → ι → K → ℝ) (read : X → ι → σ) (x : X) (i : ι) (k : K) :
    qInner (leftAtom (R := R) i k (read x i)) (packetV v read x) = 0 := by
  classical
  rw [packetV, qInner_sum_right]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [qInner_smul_right, leftAtom, qInner_blockVec]
  by_cases hq : (i, k) = q
  · rw [if_pos hq, ← hq, uniform_dotProduct, if_pos rfl]
    simp
  · rw [if_neg hq, mul_zero]

end Generator


/-! ## The realized states, and their contracts

Named realized states, with their pairings and norms transported through the
isometry immediately — after this section nothing downstream needs to know
how the realization is built. -/

section Realized

variable {R ι σ K X : Type} [Fintype R] [DecidableEq R] [Fintype ι]
  [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype K] [DecidableEq K]
  [Fintype X]

/-- A realized target state. -/
noncomputable def realizedTarget (t : Option R → ℝ) : UQBasis R ι σ K → ℂ :=
  uRealize (uTarget (ι := ι) (σ := σ) (K := K) t)

/-- The realized `u`-packet. -/
noncomputable def realizedPacketU (u : X → ι → K → ℝ) (read : X → ι → σ)
    (x : X) : UQBasis R ι σ K → ℂ :=
  uRealize (packetU (R := R) u read x)

/-- The realized `v`-packet. -/
noncomputable def realizedPacketV (v : X → ι → K → ℝ) (read : X → ι → σ)
    (x : X) : UQBasis R ι σ K → ℂ :=
  uRealize (packetV (R := R) v read x)

/-! ### Transported pairings and norms -/

@[simp] theorem qInner_realizedTarget (t t' : Option R → ℝ) :
    qInner (realizedTarget (ι := ι) (σ := σ) (K := K) t) (realizedTarget t')
      = ((t ⬝ᵥ t' : ℝ) : ℂ) := by
  rw [realizedTarget, realizedTarget, qInner_uRealize, qInner_uTarget_uTarget]

@[simp] theorem qInner_realizedTarget_realizedPacketU (t : Option R → ℝ)
    (u : X → ι → K → ℝ) (read : X → ι → σ) (x : X) :
    qInner (realizedTarget (ι := ι) (σ := σ) (K := K) t)
      (realizedPacketU u read x) = 0 := by
  rw [realizedTarget, realizedPacketU, qInner_uRealize, qInner_uTarget_packetU]

@[simp] theorem qInner_realizedTarget_realizedPacketV (t : Option R → ℝ)
    (v : X → ι → K → ℝ) (read : X → ι → σ) (x : X) :
    qInner (realizedTarget (ι := ι) (σ := σ) (K := K) t)
      (realizedPacketV v read x) = 0 := by
  rw [realizedTarget, realizedPacketV, qInner_uRealize, qInner_uTarget_packetV]

@[simp] theorem qInner_realizedPacketU_realizedTarget (u : X → ι → K → ℝ)
    (read : X → ι → σ) (x : X) (t : Option R → ℝ) :
    qInner (realizedPacketU (R := R) u read x) (realizedTarget t) = 0 := by
  rw [realizedPacketU, realizedTarget, qInner_uRealize, qInner_packetU_uTarget]

@[simp] theorem qInner_realizedPacketV_realizedTarget (v : X → ι → K → ℝ)
    (read : X → ι → σ) (x : X) (t : Option R → ℝ) :
    qInner (realizedPacketV (R := R) v read x) (realizedTarget t) = 0 := by
  rw [realizedPacketV, realizedTarget, qInner_uRealize, qInner_packetV_uTarget]

theorem qInner_realizedPacketU_realizedPacketV
    {O : Type} [DecidableEq O] {read : X → ι → σ} {f : X → O}
    (P : DualPairOn read K f) (y x : X) :
    qInner (realizedPacketU (R := R) P.u read y) (realizedPacketV P.v read x)
      = if f y = f x then 0 else 1 := by
  rw [realizedPacketU, realizedPacketV, qInner_uRealize,
    qInner_packetU_packetV_of_dualPairOn]

theorem qInner_realizedPacketU_self (u : X → ι → K → ℝ) (read : X → ι → σ)
    (x : X) :
    qInner (realizedPacketU (R := R) u read x) (realizedPacketU u read x)
      = ((2 * ∑ p : ι × K, u x p.1 p.2 * u x p.1 p.2 : ℝ) : ℂ) := by
  rw [realizedPacketU, qInner_uRealize, qInner_packetU_self]

theorem qInner_realizedPacketV_self (v : X → ι → K → ℝ) (read : X → ι → σ)
    (x : X) :
    qInner (realizedPacketV (R := R) v read x) (realizedPacketV v read x)
      = ((2 * ∑ p : ι × K, v x p.1 p.2 * v x p.1 p.2 : ℝ) : ℂ) := by
  rw [realizedPacketV, qInner_uRealize, qInner_packetV_self]

/-! ### The operational form of the `u`-packet -/

/-- **The `u`-packet is the oracle applied to a combination of generators.**
This is what puts it inside the killed space of `inputProj`. -/
theorem realizedPacketU_eq_sum_oracleGen (u : X → ι → K → ℝ)
    (read : X → ι → σ) (x : X) :
    realizedPacketU (R := R) u read x
      = oracleMat (read x)
        *ᵥ ∑ p : ι × K, ((u x p.1 p.2 : ℝ) : ℂ) • uniformGen (R := R) p := by
  classical
  rw [realizedPacketU, packetU, uRealize_sum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [uRealize_smul, Matrix.mulVec_smul, oracleMat_mulVec_uniformGen]
  rfl

/-! ### The projector contracts -/

/-- **The `u`-packet is killed.** -/
theorem inputProj_mulVec_realizedPacketU (u : X → ι → K → ℝ)
    (read : X → ι → σ) (x : X) :
    inputProj (uniformGen (R := R) (ι := ι) (σ := σ) (K := K)) (read x)
        *ᵥ realizedPacketU u read x = 0 := by
  classical
  rw [realizedPacketU_eq_sum_oracleGen, Matrix.mulVec_sum, Matrix.mulVec_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul,
    inputProj_mulVec_oracle_generator, smul_zero]

/-- **The `v`-packet is fixed.** -/
theorem inputProj_mulVec_realizedPacketV (v : X → ι → K → ℝ)
    (read : X → ι → σ) (x : X) :
    inputProj (uniformGen (R := R) (ι := ι) (σ := σ) (K := K)) (read x)
        *ᵥ realizedPacketV v read x = realizedPacketV v read x := by
  refine inputProj_mulVec_of_forall_qInner_eq_zero _ _ fun p => ?_
  rw [realizedPacketV, qInner_uniformGen_oracle_uRealize,
    qInner_leftAtom_packetV_same]

/-- **Targets are fixed.** -/
theorem inputProj_mulVec_realizedTarget (t : Option R → ℝ) (a : ι → σ) :
    inputProj (uniformGen (R := R) (ι := ι) (σ := σ) (K := K)) a
        *ᵥ realizedTarget t = realizedTarget t := by
  refine inputProj_mulVec_of_forall_qInner_eq_zero _ _ fun p => ?_
  rw [realizedTarget, qInner_uniformGen_oracle_uRealize, leftAtom,
    qInner_blockVec_uTarget]


/-! ### Real-valued norm corollaries -/

theorem qNormSq_realizedTarget (t : Option R → ℝ) :
    qNormSq (realizedTarget (ι := ι) (σ := σ) (K := K) t) = t ⬝ᵥ t := by
  have h := qInner_realizedTarget (ι := ι) (σ := σ) (K := K) t t
  rw [qInner_self] at h
  exact_mod_cast h

theorem qNormSq_realizedPacketU (u : X → ι → K → ℝ) (read : X → ι → σ)
    (x : X) :
    qNormSq (realizedPacketU (R := R) u read x)
      = 2 * ∑ p : ι × K, u x p.1 p.2 * u x p.1 p.2 := by
  have h := qInner_realizedPacketU_self (R := R) u read x
  rw [qInner_self] at h
  exact_mod_cast h

theorem qNormSq_realizedPacketV (v : X → ι → K → ℝ) (read : X → ι → σ)
    (x : X) :
    qNormSq (realizedPacketV (R := R) v read x)
      = 2 * ∑ p : ι × K, v x p.1 p.2 * v x p.1 p.2 := by
  have h := qInner_realizedPacketV_self (R := R) v read x
  rw [qInner_self] at h
  exact_mod_cast h

end Realized

/-! ## The scaled witnesses

    φ_x = t_{x+} + α·V_x
    w_x = t_{x−} − (2α)⁻¹·U_x
    ψ_x = 2α·t_{x−} − U_x  ( = 2α·w_x when α ≠ 0)

`α : ℝ`, deliberately: a complex scaling would drag conjugation into the
cancellation.  `⟪ψ_y, φ_x⟫ = 0` holds for **every** `α`: the target term
contributes `2α · ½·[f y ≠ f x] = α·[f y ≠ f x]`, and the packet term
contributes `α · ⟪U_y, V_x⟫ = α·[f y ≠ f x]`, with opposite signs.

One **global** projector `L = spanProj (uniformPhi P α)` indexed by all
promise inputs — not one per output. -/

section Scaled

variable {ι σ K X O : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [DecidableEq σ] [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq O]
  {read : X → ι → σ} {f : X → O}

/-- The realized `+` target. -/
noncomputable def realizedTPlus (f : X → O) (x : X) :
    UQBasis ↥(Set.range f) ι σ K → ℂ :=
  realizedTarget (ι := ι) (σ := σ) (K := K) (tPlus f x)

/-- The realized `−` target. -/
noncomputable def realizedTMinus (f : X → O) (x : X) :
    UQBasis ↥(Set.range f) ι σ K → ℂ :=
  realizedTarget (ι := ι) (σ := σ) (K := K) (tMinus f x)

/-- `φ_x = t_{x+} + α·V_x`. -/
noncomputable def uniformPhi (P : DualPairOn read K f) (α : ℝ) (x : X) :
    UQBasis ↥(Set.range f) ι σ K → ℂ :=
  realizedTPlus (K := K) f x + ((α : ℝ) : ℂ) • realizedPacketV P.v read x

/-- `w_x = t_{x−} − (2α)⁻¹·U_x`. -/
noncomputable def uniformW (P : DualPairOn read K f) (α : ℝ) (x : X) :
    UQBasis ↥(Set.range f) ι σ K → ℂ :=
  realizedTMinus (K := K) f x
    - (((2 * α)⁻¹ : ℝ) : ℂ) • realizedPacketU P.u read x

/-- `ψ_x = 2α·t_{x−} − U_x`. -/
noncomputable def uniformPsi (P : DualPairOn read K f) (α : ℝ) (x : X) :
    UQBasis ↥(Set.range f) ι σ K → ℂ :=
  ((2 * α : ℝ) : ℂ) • realizedTMinus (K := K) f x - realizedPacketU P.u read x

/-- **The exact orthogonality**, for every `α`. -/
theorem qInner_uniformPsi_uniformPhi (P : DualPairOn read K f) (α : ℝ)
    (y x : X) :
    qInner (uniformPsi (K := K) P α y) (uniformPhi P α x) = 0 := by
  classical
  rw [uniformPsi, uniformPhi, qInner_sub_left, qInner_smul_left,
    qInner_add_right, qInner_add_right, qInner_smul_right, qInner_smul_right,
    realizedTMinus, realizedTPlus, qInner_realizedTarget,
    qInner_realizedTarget_realizedPacketV,
    qInner_realizedPacketU_realizedTarget,
    qInner_realizedPacketU_realizedPacketV P y x, tMinus_dotProduct_tPlus]
  by_cases hxy : f x = f y
  · rw [if_pos hxy, if_pos hxy.symm]
    simp only [Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  · rw [if_neg hxy, if_neg (fun h => hxy h.symm)]
    simp only [Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring

/-- `ψ = 2α·w` once `α ≠ 0`. -/
theorem uniformPsi_eq_twoAlpha_smul_uniformW (P : DualPairOn read K f)
    {α : ℝ} (hα : α ≠ 0) (x : X) :
    uniformPsi (K := K) P α x = ((2 * α : ℝ) : ℂ) • uniformW P α x := by
  have h2 : (2 * α : ℝ) ≠ 0 := by
    simp [hα]
  rw [uniformW, uniformPsi, smul_sub, smul_smul, ← Complex.ofReal_mul,
    mul_inv_cancel₀ h2]
  norm_num

/-- Hence `⟪w_y, φ_x⟫ = 0` for `α ≠ 0`. -/
theorem qInner_uniformW_uniformPhi (P : DualPairOn read K f) {α : ℝ}
    (hα : α ≠ 0) (y x : X) :
    qInner (uniformW (K := K) P α y) (uniformPhi P α x) = 0 := by
  have h2 : ((2 * α : ℝ) : ℂ) ≠ 0 := by
    simp [hα]
  have h := qInner_uniformPsi_uniformPhi (K := K) P α y x
  rw [uniformPsi_eq_twoAlpha_smul_uniformW P hα, qInner_smul_left] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd (by simpa using h') h2
  · exact h'

/-- The reversed pairing, by conjugation. -/
theorem qInner_uniformPhi_uniformW (P : DualPairOn read K f) {α : ℝ}
    (hα : α ≠ 0) (y x : X) :
    qInner (uniformPhi (K := K) P α y) (uniformW P α x) = 0 := by
  have h := qInner_uniformW_uniformPhi (K := K) P hα x y
  rw [← qInner_conj, h, star_zero]

/-- **The global projector**, indexed by all promise inputs. -/
noncomputable def uniformL (P : DualPairOn read K f) (α : ℝ) :
    Matrix (UQBasis ↥(Set.range f) ι σ K) (UQBasis ↥(Set.range f) ι σ K) ℂ :=
  spanProj (uniformPhi (K := K) P α)

theorem isQProjector_uniformL (P : DualPairOn read K f) (α : ℝ) :
    IsQProjector (uniformL (K := K) P α) :=
  isQProjector_spanProj _

theorem uniformL_mulVec_uniformPhi (P : DualPairOn read K f) (α : ℝ) (x : X) :
    uniformL (K := K) P α *ᵥ uniformPhi P α x = uniformPhi P α x :=
  spanProj_mulVec_self _ x

theorem uniformL_mulVec_uniformW (P : DualPairOn read K f) {α : ℝ}
    (hα : α ≠ 0) (x : X) :
    uniformL (K := K) P α *ᵥ uniformW P α x = 0 := by
  refine subProj_mulVec_of_mem_orthogonal _ ?_
  exact (mem_rawSpan_orthogonal_iff _ _).mpr fun y =>
    qInner_uniformPhi_uniformW P hα y x

/-! ### The exact norms

Orthogonality of target and packet makes both a Pythagorean sum. -/

private lemma qNormSq_add_real_smul_of_orthogonal {H : Type} [Fintype H]
    [DecidableEq H] (A B : H → ℂ) (r : ℝ) (h1 : qInner A B = 0)
    (h2 : qInner B A = 0) :
    qNormSq (A + ((r : ℝ) : ℂ) • B) = qNormSq A + r ^ 2 * qNormSq B := by
  have h : qInner (A + ((r : ℝ) : ℂ) • B) (A + ((r : ℝ) : ℂ) • B)
      = qInner A A + ((r ^ 2 : ℝ) : ℂ) * qInner B B := by
    rw [qInner_add_left, qInner_add_right, qInner_add_right, qInner_smul_left,
      qInner_smul_right, qInner_smul_left, qInner_smul_right, h1, h2]
    simp only [Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  rw [qInner_self, qInner_self, qInner_self] at h
  exact_mod_cast h

/-- `‖φ_x‖² = 1 + 2α²·(the `v`-mass)` — no hypothesis on `α`. -/
theorem qNormSq_uniformPhi (P : DualPairOn read K f) (α : ℝ) (x : X) :
    qNormSq (uniformPhi (K := K) P α x)
      = 1 + 2 * α ^ 2 * ∑ p : ι × K, P.v x p.1 p.2 * P.v x p.1 p.2 := by
  rw [uniformPhi, realizedTPlus, qNormSq_add_real_smul_of_orthogonal _ _ _
      (qInner_realizedTarget_realizedPacketV _ _ _ _)
      (qInner_realizedPacketV_realizedTarget _ _ _ _),
    qNormSq_realizedTarget, tPlus_normSq, qNormSq_realizedPacketV]
  ring

theorem qNormSq_uniformPhi_le (P : DualPairOn read K f) {c : ℝ}
    (hP : P.IsCostLe c) (α : ℝ) (x : X) :
    qNormSq (uniformPhi (K := K) P α x) ≤ 1 + 2 * α ^ 2 * c := by
  rw [qNormSq_uniformPhi]
  have hmass : (∑ p : ι × K, P.v x p.1 p.2 * P.v x p.1 p.2) ≤ c := by
    simpa only [Fintype.sum_prod_type] using hP.2 x
  nlinarith [sq_nonneg α]

/-- `‖w_x‖² = 1 + (2α)⁻²·2·(the `u`-mass)` — valid for **every** `α`
(at `α = 0` the inverse is `0`, so this reads `‖w‖² = 1`). -/
theorem qNormSq_uniformW (P : DualPairOn read K f) (α : ℝ) (x : X) :
    qNormSq (uniformW (K := K) P α x)
      = 1 + ((2 * α)⁻¹) ^ 2
        * (2 * ∑ p : ι × K, P.u x p.1 p.2 * P.u x p.1 p.2) := by
  rw [uniformW, realizedTMinus, sub_eq_add_neg, ← neg_smul,
    ← Complex.ofReal_neg,
    qNormSq_add_real_smul_of_orthogonal _ _ _
      (qInner_realizedTarget_realizedPacketU _ _ _ _)
      (qInner_realizedPacketU_realizedTarget _ _ _ _),
    qNormSq_realizedTarget, tMinus_normSq, qNormSq_realizedPacketU, neg_sq]

/-- The displayed form, for `α ≠ 0`. -/
theorem qNormSq_uniformW_of_ne_zero (P : DualPairOn read K f) {α : ℝ}
    (hα : α ≠ 0) (x : X) :
    qNormSq (uniformW (K := K) P α x)
      = 1 + (∑ p : ι × K, P.u x p.1 p.2 * P.u x p.1 p.2) / (2 * α ^ 2) := by
  rw [qNormSq_uniformW]
  have h2 : (2 * α) ^ 2 = 4 * α ^ 2 := by ring
  have hne : (α : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hα
  field_simp [h2]

theorem qNormSq_uniformW_le (P : DualPairOn read K f) {c : ℝ}
    (hP : P.IsCostLe c) {α : ℝ} (hα : α ≠ 0) (x : X) :
    qNormSq (uniformW (K := K) P α x) ≤ 1 + c / (2 * α ^ 2) := by
  rw [qNormSq_uniformW_of_ne_zero P hα]
  have hmass : (∑ p : ι × K, P.u x p.1 p.2 * P.u x p.1 p.2) ≤ c := by
    simpa only [Fintype.sum_prod_type] using hP.1 x
  have hpos : (0 : ℝ) < 2 * α ^ 2 := by positivity
  gcongr

/-! ### The input-projector contracts -/

theorem inputProj_mulVec_uniformPhi (P : DualPairOn read K f) (α : ℝ) (x : X) :
    inputProj (uniformGen (R := ↥(Set.range f)) (ι := ι) (σ := σ) (K := K))
        (read x) *ᵥ uniformPhi P α x = uniformPhi P α x := by
  rw [uniformPhi, Matrix.mulVec_add, Matrix.mulVec_smul, realizedTPlus,
    inputProj_mulVec_realizedTarget, inputProj_mulVec_realizedPacketV]

theorem inputProj_mulVec_uniformW (P : DualPairOn read K f) (α : ℝ) (x : X) :
    inputProj (uniformGen (R := ↥(Set.range f)) (ι := ι) (σ := σ) (K := K))
        (read x) *ᵥ uniformW P α x = realizedTMinus f x := by
  rw [uniformW, Matrix.mulVec_sub, Matrix.mulVec_smul, realizedTMinus,
    inputProj_mulVec_realizedTarget, inputProj_mulVec_realizedPacketU,
    smul_zero, sub_zero]

/-- **`φ` is a positive witness.** -/
theorem isPosWitness_uniformPhi (P : DualPairOn read K f) (α : ℝ) (x : X) :
    IsPosWitness (uniformGen (R := ↥(Set.range f)) (ι := ι) (σ := σ) (K := K))
      (uniformL P α) (read x) (uniformPhi P α x) :=
  ⟨inputProj_mulVec_uniformPhi P α x, uniformL_mulVec_uniformPhi P α x⟩

/-! ### Realized-target wrappers -/

@[simp] theorem qNormSq_realizedTPlus (f : X → O) (x : X) :
    qNormSq (realizedTPlus (ι := ι) (σ := σ) (K := K) f x) = 1 := by
  rw [realizedTPlus, qNormSq_realizedTarget, tPlus_normSq]

@[simp] theorem qNormSq_realizedTMinus (f : X → O) (x : X) :
    qNormSq (realizedTMinus (ι := ι) (σ := σ) (K := K) f x) = 1 := by
  rw [realizedTMinus, qNormSq_realizedTarget, tMinus_normSq]

/-- `t₊ ⟂ t₋` on matching outputs — in particular for the same input. -/
theorem qInner_realizedTPlus_realizedTMinus (f : X → O) (x y : X) :
    qInner (realizedTPlus (ι := ι) (σ := σ) (K := K) f x) (realizedTMinus f y)
      = if f x = f y then 0 else ((1 / 2 : ℝ) : ℂ) := by
  rw [realizedTPlus, realizedTMinus, qInner_realizedTarget,
    tPlus_dotProduct_tMinus]
  by_cases hxy : f x = f y <;> simp [hxy]

theorem qInner_realizedTMinus_realizedTPlus (f : X → O) (x y : X) :
    qInner (realizedTMinus (ι := ι) (σ := σ) (K := K) f x) (realizedTPlus f y)
      = if f y = f x then 0 else ((1 / 2 : ℝ) : ℂ) := by
  rw [realizedTMinus, realizedTPlus, qInner_realizedTarget,
    tMinus_dotProduct_tPlus]
  by_cases hxy : f y = f x <;> simp [hxy]

@[simp] theorem qInner_realizedTPlus_realizedTMinus_self (f : X → O) (x : X) :
    qInner (realizedTPlus (ι := ι) (σ := σ) (K := K) f x) (realizedTMinus f x)
      = 0 := by
  rw [qInner_realizedTPlus_realizedTMinus, if_pos rfl]

@[simp] theorem qInner_realizedTMinus_realizedTPlus_self (f : X → O) (x : X) :
    qInner (realizedTMinus (ι := ι) (σ := σ) (K := K) f x) (realizedTPlus f x)
      = 0 := by
  rw [qInner_realizedTMinus_realizedTPlus, if_pos rfl]

/-- The target overlap the readout reads: `⟪t_{x+}, φ_x⟫ = 1`. -/
theorem qInner_realizedTPlus_uniformPhi (P : DualPairOn read K f) (α : ℝ)
    (x : X) :
    qInner (realizedTPlus (K := K) f x) (uniformPhi P α x) = 1 := by
  rw [uniformPhi, qInner_add_right, qInner_smul_right, realizedTPlus,
    qInner_realizedTarget, qInner_realizedTarget_realizedPacketV,
    tPlus_normSq]
  norm_num

/-! ### The common and output states, realized

The conversion's initial state is input-independent; its target is labelled
by the output alone.  Both are unit vectors, and distinct outputs give
orthogonal targets — the coherent readout geometry, with no cardinality of
`O` anywhere. -/

/-- The realized common initial state. -/
noncomputable def realizedCommon (f : X → O) :
    UQBasis ↥(Set.range f) ι σ K → ℂ :=
  realizedTarget (ι := ι) (σ := σ) (K := K)
    (commonVec (R := ↥(Set.range f)))

/-- The realized output-labelled target state. -/
noncomputable def realizedOut (f : X → O) (x : X) :
    UQBasis ↥(Set.range f) ι σ K → ℂ :=
  realizedTarget (ι := ι) (σ := σ) (K := K) (outVec (rangeElem f x))

/-- `common = (t₊ + t₋)/√2`, realized — for **every** `x`. -/
theorem realizedCommon_eq_smul (f : X → O) (x : X) :
    realizedCommon (ι := ι) (σ := σ) (K := K) f
      = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
          (realizedTPlus (K := K) f x + realizedTMinus (K := K) f x) := by
  have h : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
      (realizedTPlus (K := K) f x + realizedTMinus (K := K) f x)
      = realizedCommon (ι := ι) (σ := σ) (K := K) f := by
    rw [realizedTPlus, realizedTMinus, realizedTarget, realizedTarget,
      ← uRealize_add, ← uTarget_add, ← uRealize_smul, ← uTarget_realSmul,
      smul_tPlus_add_tMinus f x, realizedCommon, realizedTarget]
  exact h.symm

/-- `out(f x) = (t₊ − t₋)/√2`, realized. -/
theorem realizedOut_eq_smul (f : X → O) (x : X) :
    realizedOut (ι := ι) (σ := σ) (K := K) f x
      = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
          (realizedTPlus (K := K) f x - realizedTMinus (K := K) f x) := by
  have h : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
      (realizedTPlus (K := K) f x - realizedTMinus (K := K) f x)
      = realizedOut (ι := ι) (σ := σ) (K := K) f x := by
    rw [realizedTPlus, realizedTMinus, realizedTarget, realizedTarget,
      ← uRealize_sub, ← uTarget_sub, ← uRealize_smul, ← uTarget_realSmul,
      smul_tPlus_sub_tMinus f x, realizedOut, realizedTarget]
  exact h.symm

@[simp] theorem qNormSq_realizedCommon (f : X → O) :
    qNormSq (realizedCommon (ι := ι) (σ := σ) (K := K) f) = 1 := by
  rw [realizedCommon, qNormSq_realizedTarget, commonVec_dotProduct_commonVec]

@[simp] theorem qNormSq_realizedOut (f : X → O) (x : X) :
    qNormSq (realizedOut (ι := ι) (σ := σ) (K := K) f x) = 1 := by
  rw [realizedOut, qNormSq_realizedTarget, outVec_dotProduct_outVec,
    if_pos rfl]

/-- **The output states are labelled by the output**: the overlap is the
equality indicator, which is what the final readout measures. -/
theorem qInner_realizedOut_realizedOut (f : X → O) (x y : X) :
    qInner (realizedOut (ι := ι) (σ := σ) (K := K) f x) (realizedOut f y)
      = if f x = f y then 1 else 0 := by
  rw [realizedOut, realizedOut, qInner_realizedTarget,
    outVec_dotProduct_outVec]
  by_cases h : f x = f y
  · rw [if_pos ((rangeElem_eq_iff f x y).mpr h), if_pos h]
    norm_num
  · rw [if_neg (fun hc => h ((rangeElem_eq_iff f x y).mp hc)), if_neg h]
    norm_num

@[simp] theorem qInner_realizedCommon_realizedOut (f : X → O) (x : X) :
    qInner (realizedCommon (ι := ι) (σ := σ) (K := K) f)
      (realizedOut f x) = 0 := by
  rw [realizedCommon, realizedOut, qInner_realizedTarget,
    commonVec_dotProduct_outVec, Complex.ofReal_zero]

@[simp] theorem qInner_realizedOut_realizedCommon (f : X → O) (x : X) :
    qInner (realizedOut (ι := ι) (σ := σ) (K := K) f x)
      (realizedCommon f) = 0 := by
  rw [realizedCommon, realizedOut, qInner_realizedTarget,
    outVec_dotProduct_commonVec, Complex.ofReal_zero]

/-- **The output state is supported on its own label**: off the target
coordinate `(⊥, ⊥, inl (some (f x)))` the realized output state vanishes.
This is exactly what the final readout consumes. -/
theorem realizedOut_apply_of_ne (f : X → O) (x : X)
    {q : UQBasis ↥(Set.range f) ι σ K}
    (hq : q.2.2 ≠ Sum.inl (some (rangeElem f x))) :
    realizedOut (ι := ι) (σ := σ) (K := K) f x q = 0 := by
  obtain ⟨i, a, w⟩ := q
  rw [realizedOut, realizedTarget]
  cases i with
  | none =>
    cases a with
    | none =>
      cases w with
      | inl s =>
        rw [uRealize_target]
        have hs : s ≠ some (rangeElem f x) := fun h => hq (by rw [h])
        cases s with
        | none => simp [uTarget]
        | some t =>
          have ht : t ≠ rangeElem f x := fun h => hs (by rw [h])
          simp [uTarget, ht]
      | inr p => rfl
    | some a => cases w <;> rfl
  | some i =>
    cases a with
    | none => cases w <;> rfl
    | some a =>
      cases w with
      | inl s => rfl
      | inr p => simp [uRealize_answer, uTarget]

end Scaled

end QuantumQueryComplexity
