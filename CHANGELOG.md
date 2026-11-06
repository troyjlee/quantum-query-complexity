# Changelog

## Unreleased

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
