# Quantum query verification

## Standalone release 0.1.0 — 27 September 2026

The dedicated repository's [CI run](https://github.com/troyjlee/quantum-query-complexity/actions/runs/36309258539)
passed at [`bd6b593be115d6162cef6b6539fc6fa34c340346`](https://github.com/troyjlee/quantum-query-complexity/tree/bd6b593be115d6162cef6b6539fc6fa34c340346),
the commit tagged `v0.1.0`. This was a Linux build of the standalone package
using Lean/Mathlib **4.35.0-rc2** and `LEAN_NUM_THREADS=1`.

| Check | Result |
| --- | --- |
| Library, examples, regression checks, and Palomar modules | Passed, 3,088 build jobs including cached dependencies |
| Separate downstream Lake project | Passed, 2,864 build jobs including cached dependencies |
| Six direct axiom audits (`--trust=0`) | All passed; only `propext`, `Classical.choice`, and `Quot.sound` encountered |
| Comparator statement and axiom checks | All seven selected Palomar theorems accepted |
| Lean, NanoDa, and con-ron proof replay | All accepted; con-ron checked 40,765 exported declarations |

The audit counts match the historical table below except that the adversary
audit now checks **222** declarations, reflecting the strengthened
characterization proof. All six module counts and theorem-pin counts are
unchanged. The downstream check builds an independent Lake project with a
dependency on this library and proves examples using the public algorithm
and adversary APIs.

On macOS ARM64, both new usage-example modules were also checked directly
with Lean. The TCS consumer's usage file was checked against the actual Git
dependency after moving its former local quantum build artifacts out of the
import path. A byte-for-byte comparison confirmed that extraction preserved
all 251 production Lean files, including the root, and both Palomar modules.

These are repository verification results. They do not constitute a Palomar
service review or registration.

## Source-snapshot history

The historical records below describe the source snapshot in
[`tcs-formalizations`](https://github.com/troyjlee/tcs-formalizations/tree/6cb3955276c61ef96bd1011fd8321ce17db699a0).
[Source provenance](../../PROVENANCE.md) describes the extraction into this
standalone repository.

Local verification completed on **27 September 2026** with Lean and Mathlib
**4.35.0-rc2**. The Mathlib revision in `lake-manifest.json` is
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

The full shared build passed with `LEAN_NUM_THREADS=1 lake build`
(`4607 jobs`). This includes all three libraries, their check targets, and
the existing Sunflower and TSPGap Palomar modules. The quantum checks cover
the library and quantum/classical import boundaries, prediction-tree
composition, the polynomial method, amplitude amplification and estimation,
robust search, quantum walks, and tree search.

All six axiom audit drivers were then run directly with
`LEAN_NUM_THREADS=1 lake env lean --trust=0`, rather than relying on cached
driver builds. Each passed:

| Audit driver | Modules | Declarations | Theorem pins |
| --- | ---: | ---: | ---: |
| [Adversary](../../QuantumQueryComplexity/Test/AdversaryAxioms.lean) | 8 | 221 | 7 |
| [Polynomial](../../QuantumQueryComplexity/Test/PolynomialAxioms.lean) | 5 | 122 | 4 |
| [Amplitude](../../QuantumQueryComplexity/Test/AmplitudeAxioms.lean) | 18 | 628 | 33 |
| [Robust search](../../QuantumQueryComplexity/Test/RobustSearchAxioms.lean) | 11 | 425 | 18 |
| [Quantum walk](../../QuantumQueryComplexity/Test/QuantumWalkAxioms.lean) | 24 | 1096 | 54 |
| [Tree search](../../QuantumQueryComplexity/Test/TreeSearchAxioms.lean) | 7 | 251 | 21 |

Every audit reported exactly `propext`, `Classical.choice`, and `Quot.sound`
as its encountered axioms. The drivers check every declaration in their
listed modules, follow axiom dependencies transitively, and require the
named pins to exist in those modules. Their existing negative controls
also passed. The module lists overlap, so the row counts are not counts of
distinct declarations across the whole library.

The port from Lean/Mathlib 4.33 preserved the production definitions and
theorem statements. Five production files needed compatibility changes:

- [Duality/Gram](../../QuantumQueryComplexity/Duality/Gram.lean) explicitly
  imports the real star-ordered-ring instance.
- [Composition/SchurPSD](../../QuantumQueryComplexity/Composition/SchurPSD.lean)
  explicitly imports matrix order for `PosSemidef.hadamard`.
- [Duality/Compact](../../QuantumQueryComplexity/Duality/Compact.lean)
  explicitly imports the relocated positive-semidefinite eigenvalue lemmas.
- [Quantum/Tail](../../QuantumQueryComplexity/Quantum/Tail.lean) uses
  `Finset.prod_le_prod₀` and `Finset.prod_le_one₀` for nonnegative real factors.
- [RobustSearch/Recursion](../../QuantumQueryComplexity/Quantum/RobustSearch/Recursion.lean)
  removes two redundant tactics after `congr 1`, which now closes the goal.

The two import-boundary tests were adapted to the shared repository. A
source review confirmed that all 251 production modules are reachable from
the library root, no test modules are imported by that root, and no
production admissions or trailing whitespace were introduced. Lake targets,
local documentation links, and the citation/archive metadata were checked.

The table above records the library migration's local Lean validation.
Subsequently, the total Boolean characterization upper constants were
strengthened to `2^14` for value queries and `2^15` for XOR queries. Strong
duality and uniform extraction now establish the additive bound
`Q_{1/16} ≤ 8192(1 + ADV±)` before absorbing the constant term for nonconstant
functions. The stronger library theorems, statement tests, regression checks,
and Palomar modules passed a combined build (`3083 jobs`). A fresh adversary
audit with `--trust=0` passed: 222 declarations in 8 modules, 7 pins, and only
`propext`, `Classical.choice`, and `Quot.sound`.

The [Palomar foundations package](../../Palomar/QuantumQuery/README.md) has a
separate validation record for its independent statements and proof replay.
Neither local record constitutes a Palomar service review or registration.
See the [guide](README.md#build-and-verification) for the library commands.
