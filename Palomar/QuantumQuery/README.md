# Quantum query foundations: Palomar package

This package selects seven results from `QuantumQueryComplexity`: adversary
strong duality, exact composition, two bounded-error query characterizations,
uniform extraction from a supplied dual, and two probability-polynomial
theorems. The [paper correspondence](../../docs/quantum-query/PAPER_CORRESPONDENCE.md)
gives versioned references, theorem numbers, combined proof sources, and
scope differences for these claims and the rest of the library.

| File | Purpose |
| --- | --- |
| [Challenge.lean](Challenge.lean) | Independent mathematical statement using only Mathlib |
| [Solution.lean](Solution.lean) | The same definitions and statements, with proved library bridges |
| [comparator.json](comparator.json) | Exactly seven declarations; three permitted standard axioms |
| [formalization.yaml](formalization.yaml) | Sources, per-theorem alignment, fidelity, authorship, automation, review |

## Mathematical claims

All names below have prefix `PalomarQuantumQuery`.

| Declaration | Claim |
| --- | --- |
| `strong_duality` | The all-pairs real dual and real symmetric primal have the same value for total Boolean functions |
| `composition` | Exact multiplicative adversary composition for total Boolean functions on disjoint blocks |
| `value_characterization` | `ADV±/36 ≤ Q ≤ 2^14 ADV±`, error `1/3` |
| `xor_characterization` | `ADV±/72 ≤ Qˣ ≤ 2^15 ADV±`, error `1/3` |
| `uniform_dual_upper_bound` | A supplied promise dual of cost `c ≥ 0` gives `Q ≤ 8192(1+c)`, error `1/3` |
| `value_probability_polynomial` | Every output probability after `q` value queries has a real polynomial representation of total degree at most `2q` on Boolean inputs |
| `xor_probability_polynomial` | The same degree bound directly for XOR queries |

The characterization upper bounds use strong duality and uniform extraction
with dual costs arbitrarily close to `ADV±`. This gives
`Q ≤ 8192(1 + ADV±)` without requiring an optimal dual certificate.
For nonconstant Boolean functions, `ADV± ≥ 1` absorbs the additive term,
giving `2^14 ADV±`; constant functions need zero queries. The proved
two-query simulation gives the XOR upper constant `2^15`.

The value oracle swaps the blank answer with the input letter; XOR acts on
ordinary Boolean answers and fixes blank. Both have an idle query sector.
The comparison to a model with those sectors removed is not separately
formalized. The uniform upper bound has no alphabet/output-cardinality
factor, but requires a supplied dual; it is not the full finite-output
adversary characterization. Polynomial representations are not asserted to
be multilinear. All complexity bounds count queries, not gates or runtime.

The challenge specifies the initial unit vector, all input-independent
unitaries, oracle action, state evolution, final measurement, and minimization
over finite workspaces. The solution proves that these notions agree with
the library's model. Its seven proofs depend only on `propext`,
`Classical.choice`, and `Quot.sound`; the Challenge's seven `sorry` placeholders
are intentional comparison inputs, not proof-library admissions.

## Reproduction

From the repository root, with the pinned Lean/Mathlib **4.35.0-rc2**:

```sh
LEAN_NUM_THREADS=1 lake build QuantumQueryComplexity QuantumQueryComplexityChecks \
  Palomar.QuantumQuery.Challenge Palomar.QuantumQuery.Solution
LEAN_NUM_THREADS=1 lake env lean --trust=0 QuantumQueryComplexity/Test/AdversaryAxioms.lean
LEAN_NUM_THREADS=1 python3 scripts/check-palomar.py QuantumQuery --no-sandbox
```

The final command runs local Comparator, Lean's kernel, NanoDa, and con-ron.
On Linux with working bubblewrap, omit `--no-sandbox`. On macOS that option
is necessary; this checks a trusted local checkout and does not reproduce
the isolation of Palomar's service. Default `lake build` includes the pair,
and CI checks this foundations package.
The [library verification record](../../docs/quantum-query/VERIFICATION.md)
also covers the standalone downstream-project check and six library axiom audits.

## Historical standalone verification — 27 September 2026

The standalone [CI run](https://github.com/troyjlee/quantum-query-complexity/actions/runs/36309258539)
passed at release `v0.1.0`, commit
`bd6b593be115d6162cef6b6539fc6fa34c340346`, on Linux with Lean/Mathlib
**4.35.0-rc2**. The full build passed (3,088 jobs including cached dependencies),
as did the separate downstream Lake project and all six direct axiom audits.
Comparator accepted all seven statements and their axiom dependencies.
Lean, NanoDa, and con-ron accepted the proofs; con-ron checked **40,765**
exported declarations. This checks the dedicated repository independently
of the earlier TCS build recorded below.

## Source-snapshot verification — 27 September 2026

The following earlier checks were run on the quantum sources in
[`tcs-formalizations` at `6cb3955`](https://github.com/troyjlee/tcs-formalizations/tree/6cb3955276c61ef96bd1011fd8321ce17db699a0).

| Check | Result |
| --- | --- |
| Library, regression checks and package build | Passed, 3,083 build jobs including cached dependencies |
| Adversary axiom audit (`--trust=0`) | Passed, 222 declarations in 8 modules, 7 pins; only the three permitted axioms |
| Comparator statement and axiom checks | All seven selected theorems accepted |
| Lean kernel replay | Accepted |
| NanoDa replay | Accepted |
| con-ron replay | Accepted, 40,765 exported declarations |
| Palomar metadata contract | Passed at [PalomarSubmission `a59f25b`](https://github.com/PalomarRegistry/PalomarSubmission/tree/a59f25bd8a66bf6faf3a4f4260d412989c0185ea) |
| Community metadata schema | Passed `formalization.yaml` v0.4 |
| Statement inventory | Challenge, Solution, Comparator and metadata agree on seven names |

The toolchain was Lean **4.35.0-rc2**, commit
`11acb17ec6b07a8f9e9173e6845197929540936b`, on macOS ARM64. Mathlib was pinned
to `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The check used the local
toolchain's bundled Comparator and checkers with the sandbox disabled, as
described above. This is local verification, not a Palomar service result.

The independent Challenge is **182 lines / 9,060 bytes**, below Palomar's
preferred 300-line / 32-KiB bounds. All definitions are specified. Only its
seven theorem proofs contain deliberate placeholders; Solution contains no
admissions. The source correspondence and local documentation links were
reviewed alongside the mechanical checks.

## Submission fields

| Field | Value |
| --- | --- |
| Repository | `troyjlee/quantum-query-complexity` |
| Lean project directory | `.` |
| Comparator configuration | `Palomar/QuantumQuery/comparator.json` |
| Formalization metadata | `Palomar/QuantumQuery/formalization.yaml` |
| Commit | Full 40-character SHA selected in the Palomar submission form and recorded in its submission receipt |

This is one submission supported by five source papers. It does not select
the library's amplitude, robust-search, walk, tree-search, relational, or
application theorems. Those are documented in the correspondence inventory
and can receive separate packages later.

Use `git rev-parse HEAD` to identify the checked-out snapshot and ensure
that commit is pushed before submitting. Palomar's submission receipt
records the exact commit selected for that submission. The `v0.1.0` commit
in the historical verification record identifies the earlier release on
which those checks ran. If the submission's statements, proofs, or metadata
change, rerun the relevant checks and supply the new full commit SHA.
Preparing or checking these files neither starts a Palomar review nor
registers an entry. Recheck the
[current submission guidance](https://palomar-registry.org/how-to-submit)
at submission time.
