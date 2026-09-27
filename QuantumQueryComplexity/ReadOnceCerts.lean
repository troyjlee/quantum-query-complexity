import QuantumQueryComplexity.HasDual
import QuantumQueryComplexity.ReadOnce
import QuantumQueryComplexity.Tree
set_option linter.style.header false
set_option linter.unusedDecidableInType false

/-!
# Read-once certificates, bundled

The read-once development (`ReadOnce.lean`) certifies `ADV±(f) = √n` for a
formula with `n` leaves through the two-sided `Cert` structure, whose dual
half is a `DualPair Unit f`.  This file exposes that dual half in `HasDual`
form — what the operational extraction
(`Quantum/ReadOnceApplications.lean`) consumes — and closes the one gap in
the classical development: the balanced AND-OR tree (`Tree.lean`) carries
its exact adversary value through `HasAdvValue.compose`, which composes
*values*, not certificates; here the tree is rebuilt as a read-once formula
(`hasROCert_andOrTree`), so its dual certificate is preserved verbatim too.

The file lives downstream of both `ReadOnce.lean` and `HasDual.lean`
because neither imports the other.  No quantum import appears anywhere in
this hierarchy.
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## From two-sided certificates to bundled duals -/

/-- The dual half of a two-sided certificate, in `HasDual` form. -/
theorem Cert.hasDual {f : (ι → Bool) → Bool} {c : ℝ} (C : Cert f c) :
    HasDual f c :=
  ⟨Unit, inferInstance, C.P, C.cost⟩

/-- A read-once formula with `n` leaves has a bundled dual of cost `√n`. -/
theorem HasROCert.hasDual {f : (ι → Bool) → Bool} {n : ℕ}
    (h : HasROCert f n) : HasDual f (Real.sqrt (n : ℝ)) :=
  h.2.elim fun C => C.hasDual

/-! ## The gates -/

/-- The `n`-bit `OR` gate is a read-once formula with `n` leaves. -/
theorem hasROCert_orN [Nonempty ι] :
    HasROCert (orN : (ι → Bool) → Bool) (Fintype.card ι) :=
  ⟨Fintype.card_pos, ⟨certOrN⟩⟩

/-- The `n`-bit `AND` gate is a read-once formula with `n` leaves. -/
theorem hasROCert_andN [Nonempty ι] :
    HasROCert (andN : (ι → Bool) → Bool) (Fintype.card ι) :=
  ⟨Fintype.card_pos, ⟨certAndN⟩⟩

/-- The `OR` gate's dual, bundled. -/
theorem hasDual_orN [Nonempty ι] :
    HasDual (orN : (ι → Bool) → Bool)
      (Real.sqrt (Fintype.card ι : ℝ)) :=
  certOrN.hasDual

/-- The `AND` gate's dual, bundled. -/
theorem hasDual_andN [Nonempty ι] :
    HasDual (andN : (ι → Bool) → Bool)
      (Real.sqrt (Fintype.card ι : ℝ)) :=
  certAndN.hasDual

/-! ## The balanced AND-OR tree is read-once -/

/-- On two bits, the `OR` gate is `or2`. -/
lemma orN_fin2 : (orN : (Fin 2 → Bool) → Bool) = or2 := by
  funext x
  revert x
  decide

/-- On two bits, the `AND` gate is `and2`. -/
lemma andN_fin2 : (andN : (Fin 2 → Bool) → Bool) = and2 := by
  funext x
  revert x
  decide

/-- **The balanced AND-OR tree of depth `d+1` is a read-once formula with
`2^(d+1)` leaves** — the certificate composed level by level, preserving
the dual witness that `Tree.lean` only tracks as a value. -/
theorem hasROCert_andOrTree (d : ℕ) :
    HasROCert (andOrTree d) (2 ^ (d + 1)) := by
  induction d with
  | zero =>
      have h := hasROCert_andN (ι := Fin 2)
      rw [andN_fin2, show Fintype.card (Fin 2) = 2 ^ (0 + 1) by simp] at h
      exact h
  | succ d ih =>
      have hsum : ((2 : ℕ) ^ (d + 1 + 1)) = ∑ _i : Fin 2, 2 ^ (d + 1) := by
        simp [Finset.sum_const]
        ring
      rw [show andOrTree (d + 1)
          = composeFun (if d % 2 = 0 then or2 else and2) (andOrTree d)
          from rfl, hsum]
      by_cases hd : d % 2 = 0
      · rw [if_pos hd, ← orN_fin2]
        exact HasROCert.orNode fun _ => ih
      · rw [if_neg hd, ← andN_fin2]
        exact HasROCert.andNode fun _ => ih

/-- The tree's dual, bundled, with the cost written over the number of
input bits. -/
theorem hasDual_andOrTree (d : ℕ) :
    HasDual (andOrTree d)
      (Real.sqrt (Fintype.card (iterIdx (Fin 2) d) : ℝ)) := by
  have h := (hasROCert_andOrTree d).hasDual
  rwa [show ((2 ^ (d + 1) : ℕ) : ℝ)
      = (Fintype.card (iterIdx (Fin 2) d) : ℝ) by
    rw [card_iterIdx_fin2]] at h

end QuantumQueryComplexity
