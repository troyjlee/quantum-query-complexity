# Quantum query complexity: paper correspondence

This document separates the **seven claims selected for Palomar** from the
other results in the library. Paper references describe mathematical
provenance; they do not imply that every result of a cited paper is formalized.
The sources were checked against the versioned papers below on 27 September
2026. The review was AI-assisted, not independent human peer review.

The submission's [Challenge](../../Palomar/QuantumQuery/Challenge.lean) is a
standalone specification using only Mathlib. Its
[Solution](../../Palomar/QuantumQuery/Solution.lean) proves explicit bridges
to the library, and its [configuration](../../Palomar/QuantumQuery/comparator.json)
selects exactly the declarations listed in the next table. Structured source
records are in [formalization.yaml](../../Palomar/QuantumQuery/formalization.yaml).

## Selected claims

All submission names have prefix `PalomarQuantumQuery`. All library names in
this document have prefix `QuantumQueryComplexity` unless indicated otherwise.
`ADV±` means the real symmetric, L2-operator-norm primal defined in the
Challenge; `Q` and `Qˣ` count value and padded Boolean XOR queries respectively.

| Compared declaration | Library declaration and proof source | Paper correspondence | Exact scope and adaptation |
| --- | --- | --- | --- |
| `strong_duality` | [`advDual_eq_advPM`](../../QuantumQueryComplexity/Duality/Main.lean) | [LMRSS], Theorem 3.4, Boolean-output equality; restated in [BL], Theorem 7 | Total Boolean input and output. Equality of the infimum of all-pairs dual costs and the primal supremum. Real vectors of arbitrary finite dimension; no optimizer-attainment claim is selected. The proof uses compact convex separation. |
| `composition` | [`advPM_composeFun_eq`](../../QuantumQueryComplexity/Duality/Main.lean), with [primal](../../QuantumQueryComplexity/Composition/Main.lean) and [dual](../../QuantumQueryComplexity/DualCompose.lean) constructions | [BL], Theorem 1; lower direction from [HLS], Theorem 13; upper direction uses the composing all-pairs dual | Exact `ADV±(f ∘ g^n) = ADV±(f) ADV±(g)` for total Boolean functions. One identical inner function on disjoint blocks. Empty index types and constant functions are included. Neither arbitrary partial composition nor relational equality is selected. |
| `value_characterization` | [`boundedErrorQQuery_characterized_by_advPM`](../../QuantumQueryComplexity/Quantum/Characterization.lean) | Total Boolean specialization of [Reichardt], Theorem 1.3; lower bound from [HLS], Theorem 2; upper construction follows [LMRSS], Section 4.1 | At error `1/3`, `ADV±/36 ≤ Q ≤ 2^14 ADV±`. Strong duality and uniform extraction first give `Q ≤ 8192(1 + ADV±)`; nonconstant functions have `ADV± ≥ 1`. The native oracle swaps blank with the input value. The constants belong to this formalization. This is a combination of sources, not a transcription of Reichardt's proof. |
| `xor_characterization` | [`xorQQuery_characterized_by_advPM`](../../QuantumQueryComplexity/Quantum/Characterization.lean) and [Simulation](../../QuantumQueryComplexity/Quantum/Simulation.lean) | Same characterization target as the preceding row, transported by the library's two-query simulations | At error `1/3`, `ADV±/72 ≤ Qˣ ≤ 2^15 ADV±`. XOR fixes idle and blank sectors. Removing those sectors to obtain a literal `ι × Bool × W` basis is not a separate theorem here. |
| `uniform_dual_upper_bound` | [`qQueryOn_third_le_of_hasDualOn_uniform`](../../QuantumQueryComplexity/Quantum/UniformHasDual.lean), [UniformExtraction](../../QuantumQueryComplexity/Quantum/UniformExtraction.lean) | Function-evaluation specialization of [LMRSS], Definition 3.1 and Theorem 4.1 | A supplied all-pairs dual of cost `c ≥ 0` gives `Q ≤ 8192(1+c)` at error `1/3`. Finite promise domain and alphabet; any nonempty decidable output type. No alphabet/output-cardinality factor. This is a certificate upper bound, not a full finite-output adversary characterization. |
| `value_probability_polynomial` | [`QAlg.exists_probability_polynomial`](../../QuantumQueryComplexity/Quantum/PolynomialMethod.lean) | [BBCMW], Lemmas 4.1–4.2, especially Lemma 4.2 | For any `q`-query algorithm and readout value, a real polynomial has degree at most `2q` and equals its probability on the Boolean cube. Direct proof for value queries; multilinearity is not asserted. |
| `xor_probability_polynomial` | [`exists_xor_probability_polynomial`](../../QuantumQueryComplexity/Quantum/XorPolynomialMethod.lean) | [BBCMW], Lemma 4.2 | The same degree bound directly for padded XOR queries, without a simulation factor. One readout fiber is a set of final basis outcomes. Multilinearity and the paper's subsequent applications are not selected. |

### Shared conventions and fidelity

- **Matrix program.** The normalized real symmetric primal follows [LMRSS],
  Definition 3.3, and [BL], Definition 6. [HLS], Definition 2 also permits
  complex Hermitian matrices and uses a norm ratio. No separate theorem
  identifying real and complex optimization values is claimed by this package.
- **Dual constraints.** Both vector families have squared-norm cost at most
  `c`; the filtered inner product is one for unequal outputs and zero for
  equal outputs. The equal-output constraints are material. The strong-duality
  claim is restricted to Boolean functions, where [LMRSS] gives equality.
- **Algorithms.** An initial unit vector, a sequence of input-independent
  unitary matrices, query permutations, and final basis measurement with a
  classical readout define the model. Arbitrary finite workspace is quantified
  over. Queries read whole letters. These statements do not bound gate counts,
  running time, or the cost of synthesizing the unitaries.
- **Promises and feasibility.** A promise is an observation map
  `read : X → ι → σ`; injectivity is unnecessary. A feasible dual prevents
  observationally identical inputs from having distinct outputs. Library
  lower bounds prove algorithm existence before using the natural-number
  infimum, whose value on the empty set would otherwise be zero.
- **Degenerate cases.** Total Boolean inputs exist even when there are no
  query coordinates. Constant functions have zero complexity and adversary
  value. The uniform upper bound assumes nonempty output so that an algorithm
  can announce something even for an empty promise; zero cost is allowed.
- **What is not asserted.** General state conversion, continuous-time
  equivalence, arbitrary-error asymptotics, and a uniform general-output
  adversary characterization are not selected. The separate finite-output
  characterization already in the library retains cardinality factors.

## Other library results: provenance, not additional submitted claims

The following inventory covers the main remaining result families and their
supporting constructions. It is not a claim that every internal lemma has a
counterpart with a paper theorem number. Where the proof has been reorganized
or a result is a repository-specific synthesis, that is stated explicitly.

| Result family and Lean declarations | Sources and locations | Relationship and limits |
| --- | --- | --- |
| Promise Boolean dual witnesses, `exists_dualPairOn_of_advPMOn_lt`; `qQueryOn_characterized_by_advPMOn` and `_third` | [LMRSS], Theorems 3.4 and 1.1; [Duality/MainOn](../../QuantumQueryComplexity/Duality/MainOn.lean), [Characterization](../../QuantumQueryComplexity/Quantum/Characterization.lean) | Promise Boolean duality and finite-output bounds with explicit factors. The finite-output upper bounds retain alphabet/output-cardinality factors; do not identify them with the full uniform claim of Theorem 1.1. |
| Weighted functional composition, `advPM_composeFunFam_ge`; relational composition, `relAdvPM_mul_le_relAdvPM_composeRel` | [HLS], Theorem 13; [BL], Theorem 22; [Weighted](../../QuantumQueryComplexity/Weighted.lean), [Relational/Main](../../QuantumQueryComplexity/Relational/Main.lean) | Weighted functional and relational **lower directions**. The full relational equality and its query characterization for efficiently verifiable relations are not claimed. The composed-matrix norm proof uses a spanning/decomposition argument; see [NormCompose](../../QuantumQueryComplexity/Composition/NormCompose.lean), whose comments explain the change from BL Lemma 21. |
| `HasDual`, `HasDualOn`, postprocessing, pullback, composition and adaptive descriptor combinators | [LMRSS], filtered-dual framework; [BL], Theorem 24's tensor construction; [HasDual](../../QuantumQueryComplexity/HasDual.lean), [Promise](../../QuantumQueryComplexity/Promise/HasDual.lean), [Adaptive](../../QuantumQueryComplexity/Adaptive.lean) | Reusable certificate constructions, including generalizations and packaging specific to this library. They are not individually attributed as named theorems of the papers. |
| `LGFlow.hasDual` | [Belovs-LG], Section 3, Theorem 3; [LearningGraph/Dual](../../QuantumQueryComplexity/LearningGraph/Dual.lean) | A learning-graph flow yields an all-pairs real dual of cost `√(C₀ C₁)`. Direct dual construction with loaded assignments and a side bit; it does not reproduce the paper's span-program implementation or its alphabet-dependent conversion verbatim. |
| `hasDualOn_thresholdSearch`, `QueryTree.hasDual_shared` | Filtered-dual framework; [BinarySearch](../../QuantumQueryComplexity/BinarySearch.lean), [DecisionTree](../../QuantumQueryComplexity/DecisionTree.lean) | Threshold search and adaptive query-tree certificate constructions, with explicit threshold/correctness hypotheses and path costs. Supporting library constructions; no claim that these exact interfaces are separate named paper theorems. |
| `hasDual_scan`, `exists_maxMap_dual_isWeightedCostLe` | First-difference and filtered-dual framework above; [Scan/Bounded](../../QuantumQueryComplexity/Scan/Bounded.lean), [Scan/Weighted](../../QuantumQueryComplexity/Scan/Weighted.lean) | Bounded-change and weighted scan constructions. No exact external theorem attribution established for these particular certificate formulas; they are documented as library constructions, without a novelty claim. |
| `PredTree.hasDual_eval_layered` and compositional prediction-tree interfaces | [BT], Theorem 4(i), generalized decision trees; [PredictionTree](../../QuantumQueryComplexity/PredictionTree.lean), [PredictionTreeCompose](../../QuantumQueryComplexity/PredictionTreeCompose.lean) | Adaptation to weighted and layered transcript duals, with `8 Σ_j √(T_j G_j)` cost for positive layer budgets. Label partitions and repeated reads are explicit. The randomized expected-cost statement in Theorem 4(ii) is not claimed by this row. |
| `AncTree.hasWeightedDual_treeSearch_recCost`, `AncTree.optValue_eq`, `AncTree.qQueryOn_third_treeSearch_hom` | Filtered-dual framework; [TreeSearch/Optimal](../../QuantumQueryComplexity/TreeSearch/Optimal.lean), [Quantum/TreeSearch](../../QuantumQueryComplexity/Quantum/TreeSearch.lean) | Shared-subcomputation tree construction with positive cell costs and `C_v = t_v + √(Σ_child C_u²)`. The weight optimization concerns this construction's path/energy product; it is not a query-complexity lower bound or a claim of optimality among all algorithms. No one-to-one published theorem attribution is asserted. |
| `AmpSetup.amplified`, success, budget and conditional-law theorems | [BHMT], Section 2, Theorems 2–3; [Amplification](../../QuantumQueryComplexity/Quantum/Amplitude/Amplification.lean) | Finite compiled algorithm from a preparation and exact marker, with a supplied positive success lower bound. Budget at most `16(S+C)/√p₀`, success at least `2/3`, no invalid returned output, and preserved conditional law. Fixed bounded budget; not the paper's unknown-success expected-time formulation verbatim. |
| `AmpSetup.aeAlg`, `AmpSetup.five_sixths_le_ae_accurate`, `AmpSetup.ae_additive_five_sixths`; approximate counting | [BHMT], Theorems 12–13; [Estimation](../../QuantumQueryComplexity/Quantum/Amplitude/Estimation.lean), [Counting](../../QuantumQueryComplexity/Quantum/Amplitude/Counting.lean) | Finite phase-estimation implementation. Error `8π√(p(1-p))/M + 16π²/M²` with probability at least `5/6`; query budget `S+(M-1)(2S+C)`. Explicit constants differ from the paper. Counting is the marked-fraction specialization, with `2(M-1)` native queries. |
| `searchAlg` and `markedCount_mul_searchAlg_prob_some` | [BHMT], Section 2 and the search specialization; [Search](../../QuantumQueryComplexity/Quantum/Amplitude/Search.lean) | Under a positive marked-count promise, budget at most `16√(n/k)`; returned indices are marked and conditionally uniform. This uses an exact verifier, unlike robust search. |
| `robustSearch`, `robustSearch_solves`, `robustSearchBudget_le`, `robustOr_computes` | [HMW], Sections 1 and 3, recursive bounded-error search algorithm; [RobustSearch/Public](../../QuantumQueryComplexity/Quantum/RobustSearch/Public.lean) | Supplied tests have error at most `1/3` and cost at most `T`; their input accesses may overlap. Budget at most `10206 T ⌈√m⌉`, success at least `2/3`. Two-sided error permits an unmarked output with small probability. Empty candidate sets and zero budgets are handled. |
| `approxSearch`, `two_thirds_le_approxSearch`, `passLen_le` | [MNRS], Section 4, Lemmas 1–2; [ApproxSearch](../../QuantumQueryComplexity/Quantum/Amplitude/ApproxSearch.lean) | Approximate-reflection recursion with explicit support and precision contracts and 110 tolerant passes. The contracts are hypotheses to be instantiated, not free assumptions about every approximate reflection. |
| `WalkSetup.walkSearch`, `WalkOK.two_thirds_le_walkSearch`, `WalkSetup.walkSearch_q_le_real` | [MNRS], Theorem 3 and Sections 3–4; [Walk/MNRS](../../QuantumQueryComplexity/Quantum/Walk/MNRS.lean) | Supplied setup/update/exact-marking routines, input-independent reversible-chain data, certified **absolute** spectral gap `δ`, and marked mass at least `ε`. Budget `110S + 4490640⌈1/√ε⌉(⌈1/√δ⌉U+C)`, with no logarithmic factor. Gap and invariant-subspace contracts must be proved; choose the phase-detector length for the certified gap and the search level so that `⌈1/ε⌉ ≤ 9^K`. The nonreversible extension is not included in this row. |
| `advPM_edFun_le`, `advPM_edFun_ge`, `ed_qQuery_sandwich` | [Ambainis], Theorem 3, for the upper-bound target; [Belovs-LG], Section 4, for learning-graph construction; [Belovs-ED], Theorem 2 and Lemma 3, for the lower bound; [EDApplications](../../QuantumQueryComplexity/Quantum/EDApplications.lean) | Upper route uses learning-graph duals, not a transcription of Ambainis' walk. The lower bound assumes `n ≥ 2` and alphabet size at least `4n²`; explicit adversary constants are `1/128` and `8` times `n^(2/3)`. Query bounds additionally use extraction/lower-bound constants. |
| `hasDual_kdFun`, `kd_qQuery_upper` | [Ambainis], Theorem 3; [Belovs-LG], learning-graph method; [KD/Main](../../QuantumQueryComplexity/KD/Main.lean), [KDApplications](../../QuantumQueryComplexity/Quantum/KDApplications.lean) | Independently obtains the `n^(k/(k+1))` upper-bound target via a learning-graph dual, with a constant depending on `k`. This is not the later improved k-distinctness exponent. |
| `hasDualOn_ldsFun`, `lds_qQuery_le_logb`, `lds_qQuery_sandwich` | [ABBLS], Problem 28, Fact 36, Theorems 38–39; [LDS/Main](../../QuantumQueryComplexity/LDS/Main.lean), [LDSApplications](../../QuantumQueryComplexity/Quantum/LDSApplications.lean); lower route from [Belovs-ED] | Computes the longest distinct substring **length**. The certificate route uses weighted scans in place of the paper's maximum-finding subroutine and yields an explicit `n^(2/3)(1+log₂ n)` bound. Theorem 39's query bound has an additional `log log n` factor. No running-time claim is formalized. Lower bounds retain the large-alphabet condition `|σ| ≥ 4n²`. |
| `max_qQuery_upper`, `max_qQuery_lower`, `max_qQuery_sandwich` | [DH], minimum-finding algorithm, as background for the `√n` target; [MaxApplications](../../QuantumQueryComplexity/Quantum/MaxApplications.lean), scan duals above | A different proof: uniform dual extraction from a weighted scan, with OR-based lower bound. Outputs the maximum **value**, not an index attaining it. Nonempty finite ordered input; the lower bound needs two distinct ordered values. Does not formalize the Dürr–Høyer algorithm or its runtime. |
| `advPM_andOrTree_eq_sqrt_card`, `HasROCert.hasAdvValue`, `HasROCert.qQuery_sandwich` | [HLS], Corollary 15 for the read-once formula lower-bound target, plus composition and [Reichardt] for the query connection; [ReadOnce](../../QuantumQueryComplexity/ReadOnce.lean), [ReadOnceApplications](../../QuantumQueryComplexity/Quantum/ReadOnceApplications.lean) | Exact adversary value `√n` for the encoded read-once AND/OR certificates, with matching query order through the generic characterization. Read-once/disjointness conditions are part of the certificate. |
| Polynomial obstruction and event interfaces | [BBCMW], Lemma 4.2 and Theorem 4.8; [PolynomialLowerBound](../../QuantumQueryComplexity/Quantum/PolynomialLowerBound.lean) | Supplied degree-obstruction predicates yield lower bounds; finite events also have degree-`2q` probability polynomials. General approximate-degree formalism and all of the paper's concrete applications are not asserted. |
| Alphabet relabeling, read-all, one-hot simulations and transport | [Quantum aggregate](../../QuantumQueryComplexity/Quantum.lean), especially [OneHotSimulation](../../QuantumQueryComplexity/Quantum/OneHotSimulation.lean) | Supporting constructions for this library's explicit oracle conventions. One-hot results concern the specified encoding. They are not advertised as independent paper theorems. |

## Versioned bibliography

- **[HLS]** Peter Høyer, Troy Lee and Robert Špalek, *Negative weights make
  adversaries stronger*, [arXiv:quant-ph/0611054v2][HLS] (2007).
- **[LMRSS]** Troy Lee, Rajat Mittal, Ben W. Reichardt, Robert Špalek and
  Mario Szegedy, *Quantum query complexity of state conversion*,
  [arXiv:1011.3020v2][LMRSS] (2011).
- **[Reichardt]** Ben W. Reichardt, *Reflections for quantum query algorithms*,
  [arXiv:1005.1601v1][Reichardt] (2010). The characterization is **Theorem 1.3**
  in this version; Definition 1.1 defines the adversary bounds.
- **[BL]** Aleksandrs Belovs and Troy Lee, *The quantum query complexity of
  composition with a relation*, [arXiv:2004.06439v1][BL] (2020). Theorems 1 and
  7 restate earlier functional results with their original credits.
- **[BBCMW]** Robert Beals, Harry Buhrman, Richard Cleve, Michele Mosca and
  Ronald de Wolf, *Quantum Lower Bounds by Polynomials*,
  [arXiv:quant-ph/9802049v3][BBCMW] (1998).
- **[BHMT]** Gilles Brassard, Peter Høyer, Michele Mosca and Alain Tapp,
  *Quantum Amplitude Amplification and Estimation*,
  [arXiv:quant-ph/0005055v1][BHMT] (2000).
- **[HMW]** Peter Høyer, Michele Mosca and Ronald de Wolf, *Quantum Search
  on Bounded-Error Inputs*, [arXiv:quant-ph/0304052v2][HMW] (2003).
- **[MNRS]** Frédéric Magniez, Ashwin Nayak, Jérémie Roland and Miklos Santha,
  *Search via Quantum Walk*, [arXiv:quant-ph/0608026v4][MNRS] (2011).
- **[Belovs-LG]** Aleksandrs Belovs, *Span Programs for Functions with
  Constant-Sized 1-certificates*, [arXiv:1105.4024v1][Belovs-LG] (2011).
- **[Belovs-ED]** Aleksandrs Belovs, *Adversary Lower Bound for Element
  Distinctness*, [arXiv:1204.5074v1][Belovs-ED] (2012).
- **[Ambainis]** Andris Ambainis, *Quantum walk algorithm for element
  distinctness*, [arXiv:quant-ph/0311001v8][Ambainis] (2005).
- **[BT]** Salman Beigi and Leila Taghavi, *Quantum Speedup Based on Classical
  Decision Trees*, [arXiv:1905.13095v3][BT] (2020).
- **[ABBLS]** Jonathan Allcock, Jinge Bao, Aleksandrs Belovs, Troy Lee and
  Miklos Santha, *On the quantum time complexity of divide and conquer*,
  [arXiv:2311.16401v1][ABBLS] (2023).
- **[DH]** Christoph Dürr and Peter Høyer, *A Quantum Algorithm for Finding
  the Minimum*, [arXiv:quant-ph/9607014v2][DH] (1999).

[HLS]: https://arxiv.org/abs/quant-ph/0611054v2
[LMRSS]: https://arxiv.org/abs/1011.3020v2
[Reichardt]: https://arxiv.org/abs/1005.1601v1
[BL]: https://arxiv.org/abs/2004.06439v1
[BBCMW]: https://arxiv.org/abs/quant-ph/9802049v3
[BHMT]: https://arxiv.org/abs/quant-ph/0005055v1
[HMW]: https://arxiv.org/abs/quant-ph/0304052v2
[MNRS]: https://arxiv.org/abs/quant-ph/0608026v4
[Belovs-LG]: https://arxiv.org/abs/1105.4024v1
[Belovs-ED]: https://arxiv.org/abs/1204.5074v1
[Ambainis]: https://arxiv.org/abs/quant-ph/0311001v8
[BT]: https://arxiv.org/abs/1905.13095v3
[ABBLS]: https://arxiv.org/abs/2311.16401v1
[DH]: https://arxiv.org/abs/quant-ph/9607014v2
