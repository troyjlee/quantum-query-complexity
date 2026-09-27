# Quantum query complexity in Lean

[![CI](https://github.com/troyjlee/quantum-query-complexity/actions/workflows/ci.yml/badge.svg)](https://github.com/troyjlee/quantum-query-complexity/actions/workflows/ci.yml)

A Lean library for proving quantum query bounds. It provides finite quantum
query algorithms, adversary duality and composition, conversion of dual
certificates into algorithms, the polynomial method, amplitude amplification
and estimation, robust search, and quantum walks.

The `QuantumQueryComplexity` modules depend only on Lean, Mathlib, and
Mathlib's pinned dependencies.
The [library guide](docs/quantum-query/README.md) gives exact statements and
oracle conventions; the [source correspondence](docs/quantum-query/PAPER_CORRESPONDENCE.md)
maps the results to their papers and records differences in scope and proof.

## Use in another Lean project

Version `0.1.0` uses Lean **4.35.0-rc2** and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Use the same Lean toolchain and,
if your project already requires Mathlib, the same Mathlib revision.

Add this dependency to your `lakefile.toml`:

```toml
[[require]]
name = "QuantumQueryComplexity"
git = "https://github.com/troyjlee/quantum-query-complexity"
rev = "v0.1.0"
```

Then run `lake update` and `lake exe cache get`. A committed
`lake-manifest.json` pins the resolved Git revisions for reproducibility.
Import the modules needed by your proof:

```lean
import QuantumQueryComplexity.Quantum.Algorithm
import QuantumQueryComplexity.Quantum.Complexity
```

`import QuantumQueryComplexity` imports the whole development. More focused
imports reduce the amount of code loaded into a downstream proof.

| Purpose | Import |
| --- | --- |
| Algorithm model, state, probability, correctness | `QuantumQueryComplexity.Quantum.Algorithm` |
| Minimum query counts and bounds from algorithms | `QuantumQueryComplexity.Quantum.Complexity` |
| Classical postprocessing of an algorithm's output | `QuantumQueryComplexity.Quantum.Postcomp` |
| Adversary characterization of query complexity | `QuantumQueryComplexity.Quantum.Characterization` |
| Algorithm bounds from supplied promise duals | `QuantumQueryComplexity.Quantum.UniformHasDual` |
| Amplitude amplification | `QuantumQueryComplexity.Quantum.Amplitude.Amplification` |
| Amplitude estimation | `QuantumQueryComplexity.Quantum.Amplitude.Estimation` |
| Robust search | `QuantumQueryComplexity.Quantum.RobustSearch.Public` |
| Quantum-walk search | `QuantumQueryComplexity.Quantum.Walk.MNRS` |

The compiled [examples](QuantumQueryExamples.lean) show how to
[construct and certify a one-query algorithm](QuantumQueryExamples/Algorithms.lean)
and [turn an adversary estimate into a query lower bound](QuantumQueryExamples/Adversary.lean).
See [contributing](CONTRIBUTING.md) for the build and downstream compatibility checks.

## Scope and compatibility

The native value oracle swaps a blank answer with the queried letter.
Boolean XOR simulations and their constants are explicit. The guide records
the idle and blank sectors, promise conventions, and other model details.
Bounds count oracle queries; gate complexity and running time are separate
questions. This is a theorem-proving library, not an executable quantum simulator.

The library is at an early public release. Pin a release or commit when
depending on it. Future toolchain upgrades and changes to public definitions
or theorem statements will be recorded in [CHANGELOG.md](CHANGELOG.md).

## Build and verify

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build
LEAN_NUM_THREADS=1 python3 scripts/check-downstream.py
```

The default build includes the library, examples, regression checks, and
Palomar statement/proof modules. CI additionally runs six axiom audits and
Comparator with Lean, NanoDa, and con-ron. The
[verification record](docs/quantum-query/VERIFICATION.md) distinguishes local
checks from any registry review.

## Palomar and attribution

The [Palomar foundations package](Palomar/QuantumQuery/README.md) selects seven
claims, with an independent Mathlib-only specification and per-theorem paper
attribution. Preparation and local checking do not register a Palomar entry.

Apache License 2.0. Formalization by Troy Lee, with AI-assisted development
using Claude and Codex. [CITATION.cff](CITATION.cff) provides citation metadata;
the paper correspondence credits the underlying mathematical sources.
