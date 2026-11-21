# Changelog

## Unreleased

- Adds query gadgets, decision trees and derived oracles for the swap oracle (statements for
  review; proofs pending):
  - `Quantum/ReadGadget.lean`: reads-controlled unitaries. For addresses `addr c j : Option ι`
    (`j < k`) chosen by a control value `c` and unitaries `M c s` on a target register, one
    routine fixed before the input makes exactly `2k` queries and acts on the parked sector
    (query registers idle and blank, scratch blank) as `|c⟩|d⟩ ↦ |c⟩ M(c, answers)|d⟩` for every
    input (`exists_readGadget`, `readGadget`, `readCtrlMat`, `readPark`); free lifts of fixed
    unitaries on the control and target registers (`readLift`).
  - `Quantum/DecisionTree.lean`: decision trees `ReadTree ι σ O` reading an input `ι → σ`
    (`eval`, `depth`, `bind`, non-adaptive `reads`). A tree of depth at most `T` is realized
    with exactly `T` queries, its output a point mass (`ReadTree.realizes`). Derived oracles:
    if every letter of `y` is computed from `x` by a tree of depth at most `T > 0`, every
    algorithm querying `y` has a simulation, fixed before the input and the query count, with
    `2Tq` queries to `x` and the same success probability for every relation on outputs
    (`exists_treeSim`, `treeInput`; for outcome laws `Realizes.treeSim`; non-adaptive reads,
    `2kq` queries, `exists_readsSim`).

- Adds elementary facts used by the triangle and four-cycle lower bounds of the problems
  repository, moved there from their private helpers (statements unchanged up to names):
  - events (`JointState/Conditioning.lean`): `FinDist.probOf_congr`, `FinDist.probOf_pos_of_mem`,
    `FinDist.probOf_not` (`ρ(¬s) = 1 − ρ(s)`), `FinDist.probOf_le_of_imp` (monotonicity on the
    support), `FinDist.probOf_le_sum` (the union bound);
  - the product measure (`Records/Domination.lean`): `sum_bernMass_and_eq_mul` (events on
    complementary coordinates are independent), `sum_bernMass_eq_pow_card` (all of `S` present
    with probability `p^|S|`); and `CondBern.mass_of_avoids` (`Records/CondBern.lean`);
  - workspace vectors (`JointState/Basic.lean`): `FinDist.wvec_add`, `FinDist.wvec_sub`,
    `FinDist.wvec_smul`, `FinDist.wvec_sum`, `FinDist.wvec_diagonal_mul`, `FinDist.eq_of_wvec`,
    `FinDist.sum_ite_eq_one`, `jNormSq_smul`, `normSq_finsetSum_le` and `jNormSq_finsetSum_le`
    (Cauchy–Schwarz for finite sums), `jNormSq_add_finsetSum_le`, `sum_comp_le_sum_of_injective`;
    `FinDist.sum_ite_mul_wvec` (`Records/CondBern.lean`); `FinDist.jNormSq_condDiff_mul_le` (the
    conditional difference is a contraction, `Records/CondExp.lean`);
  - the new module `Records/ReadPhase.lean`: `FinDist.wvec_readPhase_mul` and
    `FinDist.wvecAt_readPhase_mul` (the input phase multiplies workspace vectors by `(−1)^{x_e}`).
  The names differ from the downstream private ones, so files that still keep their copies under
  `open QuantumQueryComplexity` remain unambiguous.

- Adds arc-system duals (`LearningGraph/ArcSystem.lean`): a dual adversary solution for a Boolean
  function on a promise built from arcs, each with a queried index, input-dependent states in a
  finite type and amplitude vectors with finitely many components (`ArcSystem`). A feasible arc
  system (`ArcSystem.Feasible`: the cross sum of every positive and every negative input is `1`)
  whose inputs all have cost `∑_e ∑_c amp² ≤ b` gives `HasDualOn read f b`
  (`ArcSystem.hasDualOn`); `ArcSystem.cost_le_sum_stages` bounds the cost stage by stage. The
  learning-graph theorem is re-derived as a special case (`LGFlow.toArcSystem`,
  `LGFlow.hasDual_of_arcSystem`, same statement as `LGFlow.hasDual`). Intended for the
  k-distinctness dual of Belovs (FOCS 2012, Section 6), whose states hide values and whose
  negative-input amplitudes depend on the input, which a learning-graph flow does not allow.
- Adds `Quantum/DualAlgorithm.lean`: `exists_alg_of_hasDualOn` (an algorithm with error `1/16` and
  exactly `⌊8192 (1 + c)⌋` queries from a promise dual of cost `c ≥ 0`) and `exists_alg_amplify`
  (error `2^{-s}` with `4 s q` queries, any nonempty output type), moved unchanged in statement from
  the minimum-cut upper bound of the problems repository. A downstream file that keeps its own
  copies under `open QuantumQueryComplexity` should delete them to avoid ambiguous names.

- Adds additive oracles over a finite abelian group and their query model
  (`Quantum/AddOracle.lean`, `Quantum/AddSimulation.lean`):
  - for `[AddCommGroup G] [Fintype G]` and `a : ι → G`, the oracle `|i, c⟩ ↦ |i, c + aᵢ⟩`
    (`addOracleMat`); `addOracleMap`, `addOraclePerm`, `addOracleMat` and
    `addOracleMat_mem_unitaryGroup` are generalized from `ZMod q` (existing in-tree uses still
    compile) and move from `ZqOracle.lean`, and `addOracleMat_mulVec_apply` moves from
    `ZqSimulation.lean`; a caller that names the modulus explicitly replaces `(q := q)` with
    `(G := ZMod q)`;
  - the additive query model: `addState`, `AddComputesWithErrorOn`, `addSuccessProbOn`,
    `AddSolvesWithErrorOn`, `AddQueryCounts`, `addQQueryOn`;
  - the two models simulate each other at two queries per query with the same output
    distribution, for every function and relation: `simAddAlg` (native simulates additive,
    `prob_simAddAlg`, `AddComputesWithErrorOn.simAddAlg`, `AddSolvesWithErrorOn.simAddAlg`) and
    `simTransAddAlg` (additive simulates native); `qQueryOn ≤ 2·addQQueryOn` and
    `addQQueryOn ≤ 2·qQueryOn` (`qQueryOn_le_two_mul_addQQueryOn`,
    `addQQueryOn_le_two_mul_qQueryOn`);
  - instances include XOR of `m`-bit strings (`G = Fin m → ZMod 2`) and the adjacency-array oracle
    of Apers and Lee, *Quantum complexity of minimum cut* (`G = ZMod n × (Fin m → ZMod 2)`).

- Adds subroutines for the graph collision algorithm of Cornelissen, Gilani, Kintali, Le Gall,
  Patro and Zhou, all general and part of the quantum aggregate:
  - adaptive programs with fixed budgets (`Quantum/Program.lean`): finite trees of realizable
    calls, each chosen from the earlier outcomes; given the transcript, a continuation has its own
    law (`Prog.law_call`); the budget is the largest path cost, and one algorithm realizes the law
    with exactly that many queries (`Prog.realizes`); a global cutoff with a timeout value loses
    at most the probability of overrunning (`Prog.law_cutoff_ge`); the errors of a call and of its
    continuations add (`Prog.bad_call_le`);
  - the median trick for order-convex targets (`Quantum/Amplitude/Median.lean`): `2j + 1` runs
    miss with probability at most `(2/3)^j/3`, and an outcome returned surely stays sure
    (`Realizes.median_pointMass`, of which `Realizes.median` is a corollary);
  - counting and sampling the marked labels of a known set of `a` labels
    (`Quantum/Amplitude/LabelSearch.lean`, Lemma 2.4): an estimate `r̂` with `r̂ = 0 ↔ r = 0`,
    `r/2 ≤ r̂ ≤ 2r` and `|r̂ − r| ≤ √r/2` except with probability `ε`, and `r̂ = 0` surely when
    `r = 0`, in at most `3000(√a + 1)(1 + ln(1/ε))` queries (`exists_count`,
    `labelCountBudget_le`); batches of `s` labels with a fixed budget, independent and uniform
    over the marked labels given success whatever `r̂`, failing with probability at most `ε` when
    `0 < r̂ ≤ 2r`, in at most `80(s + 1 + ln(1/ε))√(a/r̂)` queries when `0 < r̂ ≤ a`
    (`exists_sample`, `sampleBudget_le`);
  - copied input bits cost one query each in the value-oracle model (`Quantum/IndexCopy.lean`,
    `Realizes.reindex`, for any `φ : κ → ι`);
  - combining one-sided promise tests with unequal costs (`Quantum/PromiseOr.lean`, Lemma 2.5):
    the OR of `m` promise tests with error `1/3` and budgets `q_i`, each promising nothing outside
    its own promise, is a promise test with error `ε` (`exists_promiseOr`) using at most
    `10⁵ √(∑_i (q_i + 1)²) (1 + log₂ m) (3 + log₂(1 + ∑_i q_i))² (1 + log₂(1/ε))` queries
    (`promiseOrBudget_le`);
  - approximate preparations inside larger routines (`Quantum/RoutineClose.lean`): errors add and
    phases multiply under composition, and lifting along an oracle-compatible split and
    query-free unitaries keep the error and the phase;
  - clean coherent preparation of the uniform marked state (`Quantum/Amplitude/CoherentPrep.lean`,
    Lemma 2.4, last clause): from an estimate `r̂ > 0` within a factor `2` of `r`, a routine with
    no other workspace prepares the state to within `η` up to an input-dependent phase
    (`exists_coherentPrep`) in at most `200√(a/r̂)(1 + ln(1/η))` queries (`prepBudget_le`), and
    on every input it commutes with the projection onto blank query registers
    (`exists_coherentPrep_blank`); the construction uses Grover iterations and Grover's π/3
    recursion in place of the fixed-point search cited by the paper;
  - walk search with input-dependent chains and approximate routines (`Quantum/Walk/Approx.lean`,
    Lemma 2.6), **conditional on the contract `ApproxWalkOK`**: update rows within `ε` of one
    common phase times the rows of an ideal chain on all configurations, setup within `ε` of a
    phase times `√π`, check within `ε` on every vector with blank query registers, and gap `δ`
    with `4 ≤ T²δ`. Under it, with `walkErr T K ε = 4ε · walkUses T K`, a marked configuration is
    returned with probability at least `2/3 − walkErr` when the marked mass is at least `η` and
    `⌈1/η⌉ ≤ 9^K` (`ApproxWalkOK.two_thirds_sub_le`), an unmarked one with probability at most
    `walkErr` (`ApproxWalkOK.bad_le`), and `none` with probability at least `1 − walkErr` when
    nothing is marked (`ApproxWalkOK.one_sub_le_none`). The compiled walk depends only on its
    routines, `T` and `K`, not on the analytical fields (`WalkSetup.walkSearch_congr`), and every
    reversible chain is an ideal walk chain (`RevChain.exists_walkChain`). No graph collision
    update or check is yet shown to satisfy `ApproxWalkOK`;
  - no existing declaration changes.
- Adds the `GraphCollisionAxioms` audit driver, run in CI: every declaration of the eight modules,
  private helpers included, with all 31 public results pinned.

- Adds weighted counting (`Quantum/LowerBound/WeightedCounting.lean`), a bound on sums of local
  maps used by Cornelissen, Gilani, Kintali, Le Gall, Patro and Zhou (Lemma 6.7) to estimate
  adversary denominators:
  - if the maps `D_j` have pairwise orthogonal ranges (`D_jᴴ D_{j'} = 0`), `D_j` reads only the
    coordinates in `I_j`, and `‖D_j‖ ≤ w_j`, then
    `‖∑_j D_j f‖² ≤ ∑_i (∑_{j : i ∈ I_j} w_j²) ‖f_i‖²` for every vector `f`
    (`weighted_counting`), over any `RCLike` field; the read sets may overlap;
  - the operator form `‖∑_j D_j‖ ≤ c` when every coordinate's total charge is at most `c²`
    (`l2_opNorm_sum_le_weighted_counting`);
  - maps with no common nonzero row have orthogonal ranges
    (`conjTranspose_mul_eq_zero_of_rows`);
  - the module imports only Mathlib and is part of the quantum aggregate.
- Adds the general adversary bound for rectangular matrices (`Quantum/LowerBound/Rect.lean`),
  as used by Cornelissen, Gilani, Kintali, Le Gall, Patro and Zhou (Lemma 2.10):
  - rows are positive inputs and columns negative inputs; the mask `rectDOn` keeps the entries
    whose inputs disagree at a query;
  - the adversary form `‖Γ‖ / c ≤ advPMOn` through the block matrix `[[0, Γ], [Γᵀ, 0]]`
    (`norm_div_le_advPMOn_rect`);
  - the algorithm forms `(1/36)(‖Γ‖ / c) ≤ q` and `(1/36)(‖Γ‖ / c) ≤ Q_{1/3}(f)`
    (`le_of_computes_rect`, `le_boundedErrorQQuery_rect`);
  - the module is imported by the library root, since it uses `Promise.Basic`.
- Adds probability-weighted joint states and oracle adapters (`Quantum/JointState/`):
  - finite distributions with hidden labels, conditioning, mixtures and uniform distributions;
  - joint vectors with Hilbert and workspace infinity norms;
  - joint oracles and joint-state recursions in the value and XOR models;
  - the controlled phase oracle and the Hadamard bridge to the XOR oracle, and query sectors;
  - relational and average success, transported through both oracle simulations;
  - index restriction with known-zero padding (`QAlg.restrictIdx`), and the resulting
    monotonicity of the XOR query complexity under restriction (`xorQQueryOn_le_of_padRead`).
- Adds the records of product distributions (Layer D, `Quantum/Records/`):
  - for a product distribution with full-support marginals the conditional averages commute;
    the record projections `P_S = ∏_{i∈S} Dᵢ ∏_{i∉S} Eᵢ` (`FinDist.recProj`) are orthogonal
    projections summing to the identity;
  - query locality, and the record-count bound: after `t` queries the joint state has at most
    `t` records, in the value and XOR models (`FinDist.recLe_mul_jointState`,
    `FinDist.recLe_mul_jointXorState`);
  - a consistency check with the polynomial method: the amplitude bound
    `QAlg.hasAmpPoly_state` re-derived from records (`QAlg.hasAmpPoly_state_of_records`);
  - the record basis of Bernoulli bits and the record budget: one phase or XOR query raises the
    expected number of records by at most `2√(p(1−p))`.
- Adds Belovs's knowledge framework over product records (Layer D, `Quantum/Records/`):
  - the exact transfer operator from a product reference distribution to a hidden problem with
    types, which commutes with queries and carries joint states to joint states;
  - knowledge systems and operators, the query-gain operator, the query identity, the knowledge
    bound, and the refined query-gain bound;
  - the lower-bound framework `√σ ≤ γ + δ` from anti-concentration and small knowledge
    (`FinDist.sqrt_avgXorSuccessProb_le_of_knowledge`).
- Adds oracles over `Z_q` (`Quantum/ZqOracle.lean`, `Quantum/ZqSimulation.lean`,
  `Quantum/Records/ZqRecords.lean`):
  - the additive and phase oracles over `Z_q`, conjugate by the Fourier transform on the answer
    register, and the phase-oracle query model;
  - the value oracle simulated in the phase model at two phase queries per query, with exact
    success;
  - in the phase model: the record-count bound, the transferred joint state, the knowledge bound
    and the lower-bound framework; the records of the uniform distribution are the Fourier
    supports.
- Adds Fourier analysis on `Z_qⁿ` (`Quantum/Records/ZqFourier.lean`):
  - orthogonality of the characters of `Z_q^κ` and Parseval's identity for character sums;
  - the Fourier coefficients of a vector of the input register (`FinDist.fourierCoeff`), Fourier
    inversion and Parseval's identity;
  - the record projections and knowledge operators of the uniform distribution in the Fourier
    basis: `Π_G` keeps the characters whose support (`zsupp`) lies in `G`, and a vector with at
    most `t` records has no Fourier weight on larger supports.
- Adds Zhandry's compressed oracle (Layer E, `Quantum/Records/Compressed*.lean`):
  - the recording operators `Rᵢ`, which exchange the empty symbol `⊥` with the conditional-mean
    vector of the coordinate and fix the complement, and the compression `C = R ι` into the
    database register `ι → Option σ`;
  - for product distributions with full-support marginals, compression is an isometry that
    relabels the records: the record set of a database string is its set of non-`⊥` positions
    (`FinDist.dbProj_dbSupp_eq_mul_compress`); the initial record is empty and has at most `t`
    entries after `t` queries;
  - the recording oracle `R O R`, indistinguishability of the compressed run, and the growth of
    progress measures `‖Π C Ψₜ‖` from the transfer lemma
    (`FinDist.jNorm_dbProj_compress_jRun_le`);
  - Belovs's comparison of progress and knowledge: agreement on single record states, and the
    `n = q = 2` example where they differ (`knowledge_ne_progress_example`);
  - Search under the uniform distribution (Hamoudi, Proposition 42): average success at most
    `(√10 t + √2)²/q` after `t` phase queries (`avgZqSuccessProb_search_le`), `(2√10 t + √2)²/q`
    after `t` value queries.
  - public helpers used along the way: isometries preserve joint-vector norms
    (`jNormSq_mul_of_isometry`, `jNorm_mul_of_isometry`); `FinDist.marg_nonneg`,
    `FinDist.sum_supp_eq_univ`, `vecMulVec_row`; the phase-model lemmas
    `FinDist.jointZqState_zero`, `FinDist.jointZqState_succ`, `FinDist.wvec_jointZqState`,
    `FinDist.avgZqSuccessProb_eq_jNormSq_goodMask` and `FinDist.marg_uniform_zq`.
- Makes public, or adds, small facts used by applications of the knowledge framework:
  - the phase-model state and joint state are unit vectors (`zqState_isQState`,
    `FinDist.jNormSq_jointZqState`); a sum over the support of the uniform distribution on `Z_qⁿ`
    (`FinDist.sum_supp_uniform_zq`);
  - `recLe t` is Hermitian, and idempotent for full product distributions
    (`FinDist.recLe_isHermitian`, `FinDist.recLe_mul_recLe`); the projection onto all records is
    the identity, so the knowledge operator of all record sets is the transfer operator
    (`FinDist.recIn_univ`, `FinDist.knowOp_univ`);
  - the squared norm of a joint vector is the sum over its columns
    (`jNormSq_eq_sum_qNormSq_col`);
  - `FinDist.isFullProduct_uniform` moves from `Records/BooleanDegree.lean` to
    `Records/Product.lean`.
- Adds adaptive composition (`Quantum/AdaptiveRun.lean`): `Realizes.bind` runs the algorithm
  that an earlier outcome selects, with the exact product law and the query counts adding.
- Adds conditional resampling (`Quantum/Records/`):
  - conditional expectations and differences over finite alphabets, with query locality;
  - resolvent averaging, `FinDist.lemma_4_2`;
  - Bernoulli bits conditioned to avoid all-ones patterns (`CondBern`);
  - the interaction, projection-sum, common-block and moving-difference estimates,
    `CondBern.lemma_4_3`, `lemma_4_4`, `CondBern.lemma_4_5` and `CondBern.lemma_4_6`;
  - domination of increasing events under downward conditioning, through Mathlib's FKG
    inequality.
- Adds the transfer lemma and comparison of computations (`Quantum/Transfer/`):
  - per-query sector accounting;
  - endpoint lemmas for exact verification and strong anti-concentration;
  - an appended nonadaptive verifier whose queried answers stay in ancillary registers;
  - `theorem_4_1` in the XOR and value-oracle models;
  - a BBBV search lower bound as a validation.
- Adds the `TransferRecordsAxioms` audit driver, run in CI.
- No existing declaration changes. Lean and Mathlib remain at 4.35.0-rc2. The new modules
  import Mathlib's `Analysis.Matrix.Order` and `Combinatorics.SetFamily.FourFunctions`.

## 0.1.0

- First public release of the `QuantumQueryComplexity` library.
- Includes the `2^14` value-query and `2^15` XOR-query characterization upper bounds.
- Adds installation documentation, compiled usage examples, and a separate
  downstream-project check.
- Includes the seven-claim Palomar foundations package and paper correspondence.
- Requires Lean and Mathlib 4.35.0-rc2; exact dependencies are in the manifest.
