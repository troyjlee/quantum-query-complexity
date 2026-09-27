# Source provenance

The initial standalone library comes from
[`troyjlee/tcs-formalizations` at `6cb3955276c61ef96bd1011fd8321ce17db699a0`](https://github.com/troyjlee/tcs-formalizations/tree/6cb3955276c61ef96bd1011fd8321ce17db699a0).
That snapshot includes the Lean/Mathlib 4.35.0-rc2 migration and the stronger
total Boolean characterization constants used by the Palomar package.

The extraction preserves the production `QuantumQueryComplexity` Lean files
and their module names. The Palomar Challenge and Solution are also preserved.
Repository-specific documentation, package configuration, and the boundary-test
description are updated for the dedicated repository. New compiled examples
and a downstream dependency check document and test library use.

The source repository's history remains available at the linked snapshot.
This repository begins with the extracted snapshot; the original Apache-2.0
license, authorship, and mathematical references are retained. New development
of the quantum library belongs in this repository. The TCS collection may
consume an explicitly pinned version as a dependency.

The [paper correspondence](docs/quantum-query/PAPER_CORRESPONDENCE.md) is the
source of mathematical attribution and fidelity notes. Extraction into a new
repository does not change which results are adaptations, which claims are
selected for Palomar, or the recorded role of AI assistance.
