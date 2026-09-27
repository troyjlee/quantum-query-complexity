# Contributing

Use the Lean version in `lean-toolchain` and the dependencies pinned by
`lake-manifest.json`. Start with `lake exe cache get`, then build the affected
modules. `LEAN_NUM_THREADS=1` is useful on machines with limited memory.

## Library boundaries

Keep the existing `QuantumQueryComplexity.*` module hierarchy. The library
root imports production modules; examples, test drivers, and Palomar wrappers
remain separate. The quantum aggregate intentionally imports only five
shared classical foundation modules. Boundary tests enforce both properties.

Give public definitions and theorems docstrings describing their mathematical
meaning, hypotheses, error parameters, and query costs. Record paper
correspondence and material changes of scope in the library documentation.
The project permits only `propext`, `Classical.choice`, and `Quot.sound` as
proof axioms. The deliberate Challenge placeholders are comparison inputs.

## Verification

```sh
LEAN_NUM_THREADS=1 lake build
LEAN_NUM_THREADS=1 python3 scripts/check-downstream.py
```

The downstream check creates a separate temporary Lake project depending on
the current checkout. It uses the project's public algorithm and adversary
APIs; it does not add the library's source directory to `LEAN_PATH`.
Existing pinned dependency checkouts are shared to avoid another Mathlib
download. CI runs this check after the ordinary build.

For changes affecting a result family, run the relevant audit directly:

```sh
LEAN_NUM_THREADS=1 lake env lean --trust=0 QuantumQueryComplexity/Test/AdversaryAxioms.lean
```

The six drivers are `AdversaryAxioms`, `PolynomialAxioms`, `AmplitudeAxioms`,
`RobustSearchAxioms`, `QuantumWalkAxioms`, and `TreeSearchAxioms`.
CI runs all six. Changes to the selected Palomar claims also require:

```sh
LEAN_NUM_THREADS=1 python3 scripts/check-palomar.py --no-sandbox
```

On Linux with working bubblewrap, omit `--no-sandbox`. The unsandboxed command
is intended for a trusted checkout; it does not reproduce registry isolation.

## Releases

Document changes in `CHANGELOG.md`, including public API and Lean/Mathlib
compatibility changes. Before tagging a release, build the library and
examples, check the downstream project, run the axiom audits, and replay the
Palomar proofs. Release tags use `vMAJOR.MINOR.PATCH`; downstream users should
commit their resolved manifests. Do not move a published release tag.
