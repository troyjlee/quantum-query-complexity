import QuantumQueryComplexity.ReadOnceCerts
import QuantumQueryComplexity.Quantum.UniformHasDual
import QuantumQueryComplexity.Quantum.OneHotTransport
import QuantumQueryComplexity.Promise.Post
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Read-once formulas, OR, AND, and the balanced tree: the operational
quantum-query endpoints

The `Θ(√n)` bounded-error quantum query complexity of every read-once
`AND`/`OR` formula with `n` leaves, as named theorems in both oracle
models — with the gates `OR`, `AND` and the balanced AND-OR tree as
instances:

* **native** (transposition oracle): `Q_{1/3}(f) ≤ min{|ι|, 8192·(1 + √n)}`
  and `√n/36 ≤ Q_{1/3}(f)` — the pure-power sandwich
  `√n/36 ≤ Q ≤ min{|ι|, 16384·√n}`;
* **one-hot** (the canonical one-hot XOR oracle model): the same at a
  direct factor two — `16384`, `√n/72`, `32768` — with the **exact**
  read-all cap in both models.

The upper route preserves the read-once dual certificate:
`HasROCert.hasDual` (`ReadOnceCerts.lean`) `→ HasDual.hasDualOn →
qQueryOn_third_le_of_hasDualOn_uniform`.  The lower route is exact — the
read-once theorem pins `ADV±(f) = √n` on the nose
(`HasROCert.hasAdvValue`) — through the sharp Boolean `1/36` bound
(`mul_advPMOn_le_qQueryOn_of_error_third`) at `read = id`, so no
hypotheses beyond the certificate itself are needed: the sandwich holds
for **every** read-once formula, unconditionally.

This file sits outside the `QuantumQueryComplexity.Quantum` aggregate: it is an
application layer importing both the classical read-once development and
the quantum model, built by CI as an explicit cross-stream target.
-/

namespace QuantumQueryComplexity

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The read-all caps, once for every total Boolean function -/

/-- **Reading every position**: the exact cap `Q_{1/3}(f) ≤ |ι|` for any
total Boolean function. -/
theorem boolFun_qQuery_le_card (f : (ι → Bool) → Bool) :
    qQuery f (1 / 3) ≤ Fintype.card ι :=
  qQueryOn_le_card (read := (id : (ι → Bool) → ι → Bool)) (f := f)
    (fun x y h => by rw [show x = y from h]) (by norm_num : (0 : ℝ) ≤ 1 / 3)

/-- **Reading every position, one-hot**: the exact cap `|ι|` — direct, not
through simulation (which would weaken it to `2·|ι|`). -/
theorem boolFun_oneHotQQuery_le_card (f : (ι → Bool) → Bool) :
    oneHotQQuery f (1 / 3) ≤ Fintype.card ι :=
  oneHotQQuery_le_card f (by norm_num : (0 : ℝ) ≤ 1 / 3)

/-! ## The native model, for every read-once formula -/

/-- **The certificate-preserving compiler bound**:
`Q_{1/3}(f) ≤ 8192·(1 + √n)` for a read-once formula with `n` leaves. -/
theorem HasROCert.qQuery_upper {f : (ι → Bool) → Bool} {n : ℕ}
    (h : HasROCert f n) :
    (qQuery f (1 / 3) : ℝ)
      ≤ uniformExtractionConstant * (1 + Real.sqrt (n : ℝ)) :=
  qQueryOn_third_le_of_hasDualOn_uniform h.hasDual.hasDualOn
    (Real.sqrt_nonneg _)

/-- **The unabsorbed minimum form**:
`Q_{1/3}(f) ≤ min{|ι|, 8192·(1 + √n)}`. -/
theorem HasROCert.qQuery_le_min {f : (ι → Bool) → Bool} {n : ℕ}
    (h : HasROCert f n) :
    (qQuery f (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (uniformExtractionConstant * (1 + Real.sqrt (n : ℝ))) :=
  le_min (by exact_mod_cast boolFun_qQuery_le_card f) h.qQuery_upper

/-- **The operational lower bound**: `√n/36 ≤ Q_{1/3}(f)` — the read-once
theorem's exact `ADV±(f) = √n` through the sharp Boolean `1/36`
extraction, unconditionally. -/
theorem HasROCert.qQuery_lower {f : (ι → Bool) → Bool} {n : ℕ}
    (h : HasROCert f n) :
    Real.sqrt (n : ℝ) / 36 ≤ (qQuery f (1 / 3) : ℝ) := by
  have hadv : advPM f = Real.sqrt (n : ℝ) := h.hasAdvValue.1
  have hpar := mul_advPMOn_le_qQueryOn_of_error_third
    (read := (id : (ι → Bool) → ι → Bool)) (f := f)
    (fun x y hxy => by rw [show x = y from hxy])
  have hid : advPMOn (id : (ι → Bool) → ι → Bool) f = advPM f := rfl
  rw [hid, hadv] at hpar
  calc Real.sqrt (n : ℝ) / 36
      = (1 / 36 : ℝ) * Real.sqrt (n : ℝ) := by ring
    _ ≤ _ := hpar

/-- A read-once formula has at least one leaf, so `√n ≥ 1`. -/
private lemma one_le_ro_sqrt {n : ℕ} (hn : 0 < n) :
    (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt h1

/-- **The native `Θ(√n)` sandwich, for every read-once formula**:

    √n/36 ≤ Q_{1/3}(f) ≤ min{|ι|, 16384·√n},

with `16384 = 2·8192`, unconditionally. -/
theorem HasROCert.qQuery_sandwich {f : (ι → Bool) → Bool} {n : ℕ}
    (h : HasROCert f n) :
    Real.sqrt (n : ℝ) / 36 ≤ (qQuery f (1 / 3) : ℝ)
      ∧ (qQuery f (1 / 3) : ℝ)
        ≤ min (Fintype.card ι : ℝ) (16384 * Real.sqrt (n : ℝ)) := by
  refine ⟨h.qQuery_lower, le_min
    (by exact_mod_cast boolFun_qQuery_le_card f)
    (le_trans h.qQuery_upper ?_)⟩
  have hx := one_le_ro_sqrt h.1
  have hC : uniformExtractionConstant = (8192 : ℝ) := by
    norm_num [uniformExtractionConstant]
  rw [hC]
  nlinarith

/-! ## The one-hot model, for every read-once formula -/

/-- **The compiler bound in the one-hot model**, at a direct factor two:
`Q^{1-hot}_{1/3}(f) ≤ 16384·(1 + √n)`. -/
theorem HasROCert.oneHotQQuery_upper {f : (ι → Bool) → Bool} {n : ℕ}
    (h : HasROCert f n) :
    (oneHotQQuery f (1 / 3) : ℝ)
      ≤ 16384 * (1 + Real.sqrt (n : ℝ)) := by
  have h2 := oneHotQQueryOn_le_two_mul_of_qQueryOn_le (id_det f)
    (by norm_num) h.qQuery_upper
  rw [show (16384 : ℝ) = 2 * uniformExtractionConstant by
    norm_num [uniformExtractionConstant], mul_assoc]
  exact h2

/-- **The unabsorbed minimum form, one-hot**:
`Q^{1-hot}_{1/3}(f) ≤ min{|ι|, 16384·(1 + √n)}`. -/
theorem HasROCert.oneHotQQuery_le_min {f : (ι → Bool) → Bool} {n : ℕ}
    (h : HasROCert f n) :
    (oneHotQQuery f (1 / 3) : ℝ)
      ≤ min (Fintype.card ι : ℝ)
          (16384 * (1 + Real.sqrt (n : ℝ))) :=
  le_min (by exact_mod_cast boolFun_oneHotQQuery_le_card f)
    h.oneHotQQuery_upper

/-- **The one-hot lower bound**: `√n/72 ≤ Q^{1-hot}_{1/3}(f)`,
`72 = 2·36`. -/
theorem HasROCert.oneHotQQuery_lower {f : (ι → Bool) → Bool} {n : ℕ}
    (h : HasROCert f n) :
    Real.sqrt (n : ℝ) / 72 ≤ (oneHotQQuery f (1 / 3) : ℝ) := by
  have h2 := half_le_oneHotQQueryOn_of_le_qQueryOn (id_det f)
    (by norm_num) h.qQuery_lower
  calc Real.sqrt (n : ℝ) / 72
      = (Real.sqrt (n : ℝ) / 36) / 2 := by ring
    _ ≤ _ := h2

/-- **The one-hot `Θ(√n)` sandwich, for every read-once formula**:

    √n/72 ≤ Q^{1-hot}_{1/3}(f) ≤ min{|ι|, 32768·√n},

with `32768 = 2·16384`, unconditionally. -/
theorem HasROCert.oneHotQQuery_sandwich {f : (ι → Bool) → Bool} {n : ℕ}
    (h : HasROCert f n) :
    Real.sqrt (n : ℝ) / 72 ≤ (oneHotQQuery f (1 / 3) : ℝ)
      ∧ (oneHotQQuery f (1 / 3) : ℝ)
        ≤ min (Fintype.card ι : ℝ) (32768 * Real.sqrt (n : ℝ)) := by
  refine ⟨h.oneHotQQuery_lower, le_min
    (by exact_mod_cast boolFun_oneHotQQuery_le_card f)
    (le_trans h.oneHotQQuery_upper ?_)⟩
  have hx := one_le_ro_sqrt h.1
  nlinarith

/-! ## The gates -/

/-- **`OR`, native**: `√n/36 ≤ Q_{1/3}(OR) ≤ min{n, 16384·√n}`. -/
theorem orN_qQuery_sandwich [Nonempty ι] :
    Real.sqrt (Fintype.card ι : ℝ) / 36
        ≤ (qQuery (orN : (ι → Bool) → Bool) (1 / 3) : ℝ)
      ∧ (qQuery (orN : (ι → Bool) → Bool) (1 / 3) : ℝ)
        ≤ min (Fintype.card ι : ℝ)
            (16384 * Real.sqrt (Fintype.card ι : ℝ)) :=
  hasROCert_orN.qQuery_sandwich

/-- **`OR`, one-hot**: `√n/72 ≤ Q^{1-hot}_{1/3}(OR) ≤ min{n, 32768·√n}`. -/
theorem orN_oneHotQQuery_sandwich [Nonempty ι] :
    Real.sqrt (Fintype.card ι : ℝ) / 72
        ≤ (oneHotQQuery (orN : (ι → Bool) → Bool) (1 / 3) : ℝ)
      ∧ (oneHotQQuery (orN : (ι → Bool) → Bool) (1 / 3) : ℝ)
        ≤ min (Fintype.card ι : ℝ)
            (32768 * Real.sqrt (Fintype.card ι : ℝ)) :=
  hasROCert_orN.oneHotQQuery_sandwich

/-- **`AND`, native**: `√n/36 ≤ Q_{1/3}(AND) ≤ min{n, 16384·√n}`. -/
theorem andN_qQuery_sandwich [Nonempty ι] :
    Real.sqrt (Fintype.card ι : ℝ) / 36
        ≤ (qQuery (andN : (ι → Bool) → Bool) (1 / 3) : ℝ)
      ∧ (qQuery (andN : (ι → Bool) → Bool) (1 / 3) : ℝ)
        ≤ min (Fintype.card ι : ℝ)
            (16384 * Real.sqrt (Fintype.card ι : ℝ)) :=
  hasROCert_andN.qQuery_sandwich

/-- **`AND`, one-hot**: `√n/72 ≤ Q^{1-hot}_{1/3}(AND) ≤ min{n, 32768·√n}`. -/
theorem andN_oneHotQQuery_sandwich [Nonempty ι] :
    Real.sqrt (Fintype.card ι : ℝ) / 72
        ≤ (oneHotQQuery (andN : (ι → Bool) → Bool) (1 / 3) : ℝ)
      ∧ (oneHotQQuery (andN : (ι → Bool) → Bool) (1 / 3) : ℝ)
        ≤ min (Fintype.card ι : ℝ)
            (32768 * Real.sqrt (Fintype.card ι : ℝ)) :=
  hasROCert_andN.oneHotQQuery_sandwich

/-! ## The balanced AND-OR tree -/

private lemma tree_pow_cast (d : ℕ) :
    ((2 ^ (d + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (d + 1) := by
  push_cast
  ring

private lemma tree_card_cast (d : ℕ) :
    ((Fintype.card (iterIdx (Fin 2) d) : ℕ) : ℝ) = (2 : ℝ) ^ (d + 1) := by
  rw [card_iterIdx_fin2]
  push_cast
  ring

/-- **The balanced AND-OR tree on `n = 2^(d+1)` bits, native**:
`√n/36 ≤ Q_{1/3} ≤ min{n, 16384·√n}` — every input bit is a leaf, so the
cap and the leaf count coincide. -/
theorem andOrTree_qQuery_sandwich (d : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (d + 1)) / 36
        ≤ (qQuery (andOrTree d) (1 / 3) : ℝ)
      ∧ (qQuery (andOrTree d) (1 / 3) : ℝ)
        ≤ min ((2 : ℝ) ^ (d + 1))
            (16384 * Real.sqrt ((2 : ℝ) ^ (d + 1))) := by
  have h := (hasROCert_andOrTree d).qQuery_sandwich
  rwa [tree_pow_cast, tree_card_cast] at h

/-- **The balanced AND-OR tree, one-hot**:
`√n/72 ≤ Q^{1-hot}_{1/3} ≤ min{n, 32768·√n}`. -/
theorem andOrTree_oneHotQQuery_sandwich (d : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (d + 1)) / 72
        ≤ (oneHotQQuery (andOrTree d) (1 / 3) : ℝ)
      ∧ (oneHotQQuery (andOrTree d) (1 / 3) : ℝ)
        ≤ min ((2 : ℝ) ^ (d + 1))
            (32768 * Real.sqrt ((2 : ℝ) ^ (d + 1))) := by
  have h := (hasROCert_andOrTree d).oneHotQQuery_sandwich
  rwa [tree_pow_cast, tree_card_cast] at h

end QuantumQueryComplexity
