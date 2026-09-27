# Quantum query complexity

`QuantumQueryComplexity` formalizes the negative-weight adversary bound, its
duality and composition theory, and a finite quantum query model. It connects
dual certificates to quantum algorithms and proves explicit query bounds for
standard examples.

The [library root](../../QuantumQueryComplexity.lean) imports the full
development. The [quantum aggregate](../../QuantumQueryComplexity/Quantum.lean)
lists the operational modules in dependency order.

The [paper correspondence](PAPER_CORRESPONDENCE.md) maps the main result
families to versioned sources, theorem numbers, and scope differences. The
[Palomar foundations package](../../Palomar/QuantumQuery/README.md) selects
seven claims in adversary theory, query characterization, dual extraction,
and the polynomial method.

## Main statements

Below, `ADV±` denotes `advPM` (or `advPMOn` on a promise). `Q` denotes the
native value-oracle complexity, and `Qˣ` the Boolean XOR-oracle complexity.
Unless an error is displayed, it is `1/3`. The Lean declarations state the
exact hypotheses and constants.

| Declaration or family | Formalized claim | Source files |
| --- | --- | --- |
| `advDual_eq_advPM` | Strong duality for Boolean-output functions | [Duality/Main](../../QuantumQueryComplexity/Duality/Main.lean) |
| `advPM_composeFun_eq` | Exact multiplicative composition for total Boolean functions | [Duality/Main](../../QuantumQueryComplexity/Duality/Main.lean), [Composition/Main](../../QuantumQueryComplexity/Composition/Main.lean) |
| `qQuery_sixteenth_le_one_add_advPM` | For total Boolean functions, `Q_{1/16} ≤ 8192(1 + ADV±)` from near-optimal duals and uniform extraction | [Characterization](../../QuantumQueryComplexity/Quantum/Characterization.lean) |
| `boundedErrorQQuery_characterized_by_advPM` | For total Boolean functions, `ADV±/36 ≤ Q ≤ 2^14 · ADV±` | [Characterization](../../QuantumQueryComplexity/Quantum/Characterization.lean) |
| `xorQQuery_characterized_by_advPM` | For total Boolean functions, `ADV±/72 ≤ Qˣ ≤ 2^15 · ADV±` | [Characterization](../../QuantumQueryComplexity/Quantum/Characterization.lean) |
| `qQueryOn_third_le_of_hasDualOn_uniform` | A promise dual of cost `c ≥ 0` gives `Q ≤ 8192(1+c)`, independently of alphabet and output size | [UniformHasDual](../../QuantumQueryComplexity/Quantum/UniformHasDual.lean) |
| `QAlg.exists_probability_polynomial` | For Boolean inputs, a `T`-query acceptance probability is represented by a real polynomial of total degree at most `2T`; a direct XOR version is also proved | [PolynomialMethod](../../QuantumQueryComplexity/Quantum/PolynomialMethod.lean), [XorPolynomialMethod](../../QuantumQueryComplexity/Quantum/XorPolynomialMethod.lean) |
| `AmpSetup.amplified` | Amplitude amplification with a query budget, success guarantee and preserved conditional output law | [Amplification](../../QuantumQueryComplexity/Quantum/Amplitude/Amplification.lean) |
| `AmpSetup.aeAlg` | Amplitude estimation with explicit error, probability and query bounds | [Estimation](../../QuantumQueryComplexity/Quantum/Amplitude/Estimation.lean) |
| `robustSearch` | Search using supplied bounded-error tests, with cost proportional to `T·⌈√m⌉` and no logarithmic factor | [RobustSearch/Public](../../QuantumQueryComplexity/Quantum/RobustSearch/Public.lean) |
| `WalkSetup.walkSearch` | Quantum-walk search with explicit setup, update, marking, stationary-mass and spectral-gap hypotheses | [Walk/MNRS](../../QuantumQueryComplexity/Quantum/Walk/MNRS.lean) |

The finite-output theorems named
`qQueryOn_characterized_by_advPMOn` and
`qQueryOn_characterized_by_advPMOn_third` in `Characterization.lean` retain
explicit alphabet- and output-cardinality factors in their upper bounds.
The separate uniform extraction theorem above has no such factors, but its
input is a supplied dual certificate. These are distinct exported statements.

The example applications include element distinctness, `k`-distinctness,
longest distinct substring, maximum finding, and read-once AND/OR formulas.
Their `Quantum/*Applications.lean` files give the operational bounds;
the corresponding `Acceptance*.lean` files pin the theorem statements.

## Oracle and algorithm conventions

An algorithm consists of an initial unit vector, input-independent unitary
steps, and a final computational-basis measurement with a classical readout.
All spaces are finite. Query complexity minimizes the number of queries over
all finite workspaces; this is a query bound, not a bound on gate count or the
classical time needed to construct an algorithm.

The native oracle is the transposition value oracle of
[Oracle.lean](../../QuantumQueryComplexity/Quantum/Oracle.lean). A query reads
an entire alphabet symbol. The basis includes an idle query index and a blank
answer sector.

[Simulation.lean](../../QuantumQueryComplexity/Quantum/Simulation.lean) proves
factor-two simulations in both directions for Boolean XOR queries. The XOR
model retains the idle and blank sectors. Equivalence to a basis with those
sectors removed is not separately formalized.
[OneHotSimulation.lean](../../QuantumQueryComplexity/Quantum/OneHotSimulation.lean)
gives a factor-two comparison with a specified one-hot XOR encoding for finite
alphabets; the statement concerns that encoding.

The native adversary bound uses real symmetric matrices with the L2 operator
norm. Promise statements use an observation map `read : X → ι → σ` and state
when the observations must determine the output. The exported lower bounds
discharge the existence of an algorithm before using the natural-number
infimum defining query complexity.

## Source map

| Area | Modules |
| --- | --- |
| Adversary definitions and spectral estimates | `Defs`, `Spectral`, `Basic`, `Dual`, `Promise/Defs` |
| Strong duality and composition | `Duality/`, `Composition/`, `Relational/`, `DualCompose` |
| Reusable dual constructions | `HasDual`, `Weighted*`, `Promise/`, `Scan/`, `Adaptive`, `DecisionTree`, `PredictionTree*`, `TreeSearch/` |
| Quantum states, algorithms and extraction | `Quantum/FiniteHilbert`, `Oracle`, `Algorithm`, `Complexity`, `UniformExtraction`, `UniformHasDual` |
| Lower bounds and oracle simulations | `Quantum/LowerBound/`, `Characterization`, `Simulation`, `OneHot*` |
| Polynomial method | `Polynomial/`, `Quantum/PolynomialMethod`, `XorPolynomialMethod`, `PolynomialLowerBound` |
| Amplification, estimation and search | `Quantum/Amplitude/`, `RobustSearch/`, `Walk/` |
| Examples | `ED/`, `EDLower/`, `KD/`, `LDS/`, `Max/`, `ReadOnce`, `Quantum/*Applications` |

The quantum aggregate reaches only five classical foundation modules; the
complete library combines both layers. Tests enforce this distinction and
check that the library imports only Lean, Mathlib and its dependencies, and
its own modules.

## Use as a dependency

The [repository README](../../README.md#use-in-another-lean-project) gives the
Lake dependency declaration and compatible toolchain. Compiled
[usage examples](../../QuantumQueryExamples.lean) demonstrate the public APIs.

## Build and verification

The standalone package pins Lean and Mathlib to **4.35.0-rc2**. From the repository
root:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build QuantumQueryComplexity QuantumQueryComplexityChecks
```

`QuantumQueryComplexityChecks` compiles the existing boundary, prediction-tree,
polynomial-method, amplitude, robust-search, quantum-walk and tree-search
regressions. The repository's default `lake build` includes both targets.

Run the axiom checks directly, as CI does:

```sh
for audit in Adversary Polynomial Amplitude RobustSearch QuantumWalk TreeSearch; do
  LEAN_NUM_THREADS=1 lake env lean --trust=0 "QuantumQueryComplexity/Test/${audit}Axioms.lean"
done
```

The audit drivers reject dependencies outside `propext`, `Classical.choice`
and `Quot.sound`, including `sorryAx` and `Lean.ofReduceBool`. They check all
declarations in their listed modules and the presence of their named theorem
pins. These are Lean checks; the separate
[Palomar validation record](../../Palomar/QuantumQuery/README.md) records
Comparator comparison and independent proof replay for the seven selected
foundations claims.

The [verification record](VERIFICATION.md) lists the completed local build,
audit counts, and Lean 4.35 compatibility changes.

## Principal references

- Peter Høyer, Troy Lee and Robert Špalek,
  [*Negative weights make adversaries stronger*](https://arxiv.org/abs/quant-ph/0611054).
- Troy Lee, Rajat Mittal, Ben W. Reichardt, Robert Špalek and Mario Szegedy,
  [*Quantum query complexity of state conversion*](https://arxiv.org/abs/1011.3020).
- Ben W. Reichardt,
  [*Reflections for quantum query algorithms*](https://arxiv.org/abs/1005.1601).
- Robert Beals, Harry Buhrman, Richard Cleve, Michele Mosca and Ronald de Wolf,
  [*Quantum Lower Bounds by Polynomials*](https://arxiv.org/abs/quant-ph/9802049).

Module documentation identifies further sources and constructions. The
explicit numerical constants and oracle conventions above describe the Lean
statements; they are not claims about the papers' original constants.

Formalization by Troy Lee, with AI-assisted proof development using Claude
(Anthropic) and Codex (OpenAI). The shared [license](../../LICENSE) and
[citation metadata](../../CITATION.cff) apply.
