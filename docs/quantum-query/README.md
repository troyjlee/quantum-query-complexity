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
| `jNorm_jRun_sub_mul_le`, `theorem_4_1` | The transfer lemma for runs with arbitrary oracles and per-step errors; comparison of computations, `√σ ≤ (t + v)√(maxₑ αₑ + ∑ₑ βₑ)` for a `t`-query XOR algorithm with a `v`-query exact verifier | [Transfer/Lemma](../../QuantumQueryComplexity/Quantum/Transfer/Lemma.lean), [Transfer/Comparison](../../QuantumQueryComplexity/Quantum/Transfer/Comparison.lean) |
| `FinDist.lemma_4_2`, `CondBern.lemma_4_5`, `CondBern.lemma_4_6` | Conditional resampling: resolvent averaging with Hilbert- and infinity-norm contraction, and the common-block and moving-difference estimates for Bernoulli bits conditioned to avoid all-ones patterns | [Records/](../../QuantumQueryComplexity/Quantum/Records/) |
| `FinDist.probOf_condOn_bern_le` | Conditioning a product Bernoulli distribution on a downward-closed event does not increase the probability of any increasing event | [Records/Domination](../../QuantumQueryComplexity/Quantum/Records/Domination.lean) |
| `xorSuccessProbOn_restrictIdx` | An XOR algorithm on one index set runs against an oracle on another, through a partial map with known-zero padding, at the same query count and with the same success | [JointState/Restrict](../../QuantumQueryComplexity/Quantum/JointState/Restrict.lean) |
| `xorQQueryOn_le_of_padRead` | Restricting a problem through a partial map with known-zero padding does not increase its XOR query complexity | [JointState/Restrict](../../QuantumQueryComplexity/Quantum/JointState/Restrict.lean) |
| `Realizes.bind` | Adaptive composition: run an algorithm, then the algorithm its outcome selects, with the exact product outcome law and the query counts adding | [AdaptiveRun](../../QuantumQueryComplexity/Quantum/AdaptiveRun.lean) |
| `FinDist.recProj`, `FinDist.sum_recProj` | Records of a product distribution with full-support marginals: `P_S = ∏_{i∈S} Dᵢ ∏_{i∉S} Eᵢ` (in any order) are orthogonal projections summing to the identity | [Records/Product](../../QuantumQueryComplexity/Quantum/Records/Product.lean) |
| `FinDist.recLe_mul_jointState`, `FinDist.recLe_mul_jointXorState` | Query locality and the record-count bound: after `t` queries the joint state has at most `t` records (Belovs, Proposition 3.2), value and XOR models | [Records/RecordCount](../../QuantumQueryComplexity/Quantum/Records/RecordCount.lean) |
| `QAlg.hasAmpPoly_state_of_records` | The amplitude half of the polynomial method, derived from records of the uniform distribution on the cube | [Records/BooleanDegree](../../QuantumQueryComplexity/Quantum/Records/BooleanDegree.lean) |
| `FinDist.xferOp_mul_jointState` | The exact transfer operator from a product reference distribution to a hidden problem commutes with queries and carries joint states to joint states (Belovs, Fact 3.5 and Proposition 3.6) | [Records/HiddenTransfer](../../QuantumQueryComplexity/Quantum/Records/HiddenTransfer.lean) |
| `FinDist.knowOp_jOracle_sub`, `FinDist.jNorm_knowOp_jointXorState_le` | Knowledge: the query identity `Υ⁺O − OΥ⁺ = OΨ^∂ − Ψ^∂O` and the knowledge bound (Belovs, Lemma 3.21, Corollaries 3.22–3.24); the refined bound of Lemma 6.13 | [Records/Knowledge](../../QuantumQueryComplexity/Quantum/Records/Knowledge.lean) |
| `FinDist.sqrt_avgXorSuccessProb_le_of_knowledge` | The lower-bound framework: anti-concentration of the no-knowledge part plus small knowledge give `√σ ≤ γ + δ` (Belovs, Lemma 3.18) | [Records/Framework](../../QuantumQueryComplexity/Quantum/Records/Framework.lean) |
| `addOracleMat_eq_fourier_phase`, `zqSuccessProbOn_simStdToZq` | Oracles over `Z_q`: the additive oracle is the Fourier conjugate of the phase oracle `ω^{c·xᵢ}`; value-oracle algorithms run in the phase model at two queries per query with exact success | [ZqOracle](../../QuantumQueryComplexity/Quantum/ZqOracle.lean), [ZqSimulation](../../QuantumQueryComplexity/Quantum/ZqSimulation.lean) |
| `FinDist.sqrt_avgZqSuccessProb_le_of_knowledge`, `FinDist.recProj_uniform_mulVec_fourier` | Belovs's setting: the record-count bound, knowledge bound and framework in the phase model over `Z_q`; the uniform records are the Fourier supports | [Records/ZqRecords](../../QuantumQueryComplexity/Quantum/Records/ZqRecords.lean) |
| `FinDist.qNormSq_eq_sum_fourierCoeff`, `FinDist.knowOp_mulVec_apply` | Fourier analysis on `Z_qⁿ`: character orthogonality, Fourier inversion and Parseval; record projections and knowledge operators in the Fourier basis (Belovs, (3.16), (3.20), Proposition 4.5) | [Records/ZqFourier](../../QuantumQueryComplexity/Quantum/Records/ZqFourier.lean) |
| `FinDist.dbProj_dbSupp_eq_mul_compress`, `FinDist.jNorm_dbProj_compress_jRun_le` | Zhandry's compressed oracle: compression relabels the records of product distributions (record set = non-`⊥` positions); progress measures grow by the commutator with the recording oracle, from the transfer lemma | [Records/Compressed](../../QuantumQueryComplexity/Quantum/Records/Compressed.lean) |
| `FinDist.jNorm_dbProj_compress_of_recProj`, `knowledge_ne_progress_example` | Progress measure and knowledge agree on single record states and differ in general (Belovs, Section 3.8) | [Records/CompressedKnowledge](../../QuantumQueryComplexity/Quantum/Records/CompressedKnowledge.lean) |
| `avgZqSuccessProb_search_le`, `le_of_avgZqSuccessProb_search` | Search under the uniform distribution by the compressed oracle: success at most `(√10 t + √2)²/q` (Hamoudi, Proposition 42) | [Records/CompressedSearch](../../QuantumQueryComplexity/Quantum/Records/CompressedSearch.lean) |
| `FinDist.recCount_jointXorState_le` | Record budget of Bernoulli(p) bits: after `t` phase or XOR queries the expected number of records is at most `2t√(p(1−p))` | [Records/BiasedBudget](../../QuantumQueryComplexity/Quantum/Records/BiasedBudget.lean) |

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
| Joint states, conditional resampling and comparison of computations | `Quantum/JointState/`, `Quantum/Records/`, `Quantum/Transfer/` |
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
for audit in Adversary Polynomial Amplitude RobustSearch QuantumWalk TreeSearch TransferRecords GraphCollision; do
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
