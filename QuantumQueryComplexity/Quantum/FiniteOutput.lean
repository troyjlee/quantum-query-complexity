import QuantumQueryComplexity.Quantum.Amplify
import QuantumQueryComplexity.Quantum.Postcomp
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log

set_option synthInstance.maxSize 1600

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Finite outputs by bit encoding

A finite output type `O` with `m` values is encoded in
`B = ⌈log₂ m⌉ = Nat.clog 2 m` Boolean bits through `Fintype.equivFin`; each
bit of `f` is a post-composition of `f`, so on the adversary side it costs
nothing (`advPMOn_comp_le`).  Given a `1/16`-algorithm for each bit, the
assembly is:

* amplify each bit to error `(1/4)ᵗ` with `2t` majority rounds (`amplify`;
  the exponent arithmetic is `2^{2t}·(1/16)^t = (1/4)^t`);
* join the `B` amplified bits into the tuple (`exists_tuple_computes`),
  error `B·(1/4)ᵗ`, cost `∑ᵢ 2t·qᵢ`;
* decode by post-composing the readout with the inverse encoding
  (`ComputesWithErrorOn.postcomp` from `Quantum/Postcomp.lean` — the fibre sum
  only grows the correct outcome's probability).

`exists_decode_computes` is the generic assembly; the final theorem against
`advPMOn` lives in `Quantum/Characterization.lean`, which supplies the
per-bit algorithms from the promise-Boolean characterization.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {X : Type} [Fintype X]

/-! ## The bit encoding -/

variable (O : Type) [Fintype O] [DecidableEq O]

/-- The number of encoding bits: `⌈log₂ |O|⌉`. -/
def encBits : ℕ := Nat.clog 2 (Fintype.card O)

variable {O}

/-- Bit `i` of the encoded value. -/
noncomputable def encBit (o : O) (i : Fin (encBits O)) : Bool :=
  Nat.testBit ((Fintype.equivFin O) o).val i.val

/-- The encoding is injective: values are below `2^B`, so the first `B` bits
determine them. -/
lemma encBit_injective {o o' : O}
    (h : ∀ i : Fin (encBits O), encBit o i = encBit o' i) : o = o' := by
  have hlt : ∀ p : O, ((Fintype.equivFin O) p).val < 2 ^ encBits O := by
    intro p
    calc ((Fintype.equivFin O) p).val < Fintype.card O :=
        ((Fintype.equivFin O) p).isLt
      _ ≤ 2 ^ encBits O := Nat.le_pow_clog (by norm_num) _
  have hval : ((Fintype.equivFin O) o).val = ((Fintype.equivFin O) o').val := by
    refine Nat.eq_of_testBit_eq fun i => ?_
    by_cases hi : i < encBits O
    · exact h ⟨i, hi⟩
    · rw [Nat.testBit_eq_false_of_lt, Nat.testBit_eq_false_of_lt]
      · exact lt_of_lt_of_le (hlt o')
          (Nat.pow_le_pow_right (by norm_num) (le_of_not_gt hi))
      · exact lt_of_lt_of_le (hlt o)
          (Nat.pow_le_pow_right (by norm_num) (le_of_not_gt hi))
  exact (Fintype.equivFin O).injective (Fin.ext hval)

/-- The decoder: the (unique) value with the given bits, if any. -/
noncomputable def encDecode [Nonempty O] (y : Fin (encBits O) → Bool) : O :=
  if h : ∃ o : O, (fun i => encBit o i) = y then h.choose
  else Classical.arbitrary O

lemma encDecode_encBit [Nonempty O] (o : O) :
    encDecode (fun i => encBit o i) = o := by
  rw [encDecode, dif_pos ⟨o, rfl⟩]
  have hspec := (⟨o, rfl⟩ : ∃ o' : O,
    (fun i => encBit o' i) = fun i => encBit o i).choose_spec
  exact encBit_injective fun i => congrFun hspec i

/-! ## The assembly -/

/-- The exponent arithmetic of the amplification: `2t` rounds at error
`1/16` give error `(1/4)ᵗ`. -/
private lemma amp_error_eq (t : ℕ) :
    (2 : ℝ) ^ (2 * t) * (1 / 16 : ℝ) ^ ((2 * t + 1) / 2) = (1 / 4) ^ t := by
  have hexp : (2 * t + 1) / 2 = t := by omega
  rw [hexp, pow_mul]
  rw [show ((2 : ℝ) ^ 2) = 4 from by norm_num, ← mul_pow]
  norm_num

/-- **The finite-output assembly**: given a `1/16`-algorithm for each
encoding bit of `f`, there is an algorithm for `f` itself with error
`B·(1/4)ᵗ` at cost `∑ᵢ 2t·qᵢ`. -/
theorem exists_decode_computes {O : Type} [Fintype O] [DecidableEq O]
    [Nonempty O] {read : X → ι → σ} {f : X → O}
    {qb : Fin (encBits O) → ℕ} (t : ℕ)
    (halg : ∀ i, ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : QAlg ι σ Bool W),
      ComputesWithErrorOn A (qb i) read (fun x => encBit (f x) i) (1 / 16)) :
    ∃ (W' : Type) (_ : Fintype W') (_ : DecidableEq W')
      (A' : QAlg ι σ O W'),
      ComputesWithErrorOn A' (∑ i, 2 * t * qb i) read f
        ((encBits O : ℝ) * (1 / 4) ^ t) := by
  classical
  -- amplify each bit
  have hamp : ∀ i, ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : QAlg ι σ Bool W),
      ComputesWithErrorOn A (2 * t * qb i) read
        (fun x => encBit (f x) i) ((1 / 4 : ℝ) ^ t) := by
    intro i
    have h := amplify (by norm_num) (by norm_num) (halg i) (2 * t)
    rw [amp_error_eq] at h
    rw [show 2 * t * qb i = (2 * t) * qb i from rfl]
    exact h
  -- join the bits
  have htuple := exists_tuple_computes
    (ε := fun _ => ((1 / 4 : ℝ) ^ t)) (fun _ => by positivity) hamp
  -- the tuple error sums to `B·(1/4)ᵗ`
  rw [show (∑ _i : Fin (encBits O), ((1 / 4 : ℝ) ^ t))
      = (encBits O : ℝ) * (1 / 4) ^ t from by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
    at htuple
  -- decode
  obtain ⟨W', hW1, hW2, A', hA'⟩ := htuple
  have hdec := hA'.exists_postcomp (encDecode (O := O))
  refine hdec.imp fun W'' h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun A'' hA'' => ?_
  intro x
  have hx := hA'' x
  have hbeta : (fun x => encDecode fun i => encBit (f x) i) x = f x := by
    show encDecode (fun i => encBit (f x) i) = f x
    exact encDecode_encBit (f x)
  rwa [hbeta] at hx

end QuantumQueryComplexity
