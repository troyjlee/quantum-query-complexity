import QuantumQueryComplexity.Quantum.FiniteHilbert
import QuantumQueryComplexity.Quantum.Measurement
import QuantumQueryComplexity.Quantum.Oracle
import QuantumQueryComplexity.Quantum.Algorithm
import QuantumQueryComplexity.Quantum.Complexity
import QuantumQueryComplexity.Quantum.ReadFactor
import QuantumQueryComplexity.Quantum.ReadAll
import QuantumQueryComplexity.Quantum.Solvable
import QuantumQueryComplexity.Quantum.Routine
import QuantumQueryComplexity.Quantum.RunWith
import QuantumQueryComplexity.Quantum.Blocks
import QuantumQueryComplexity.Quantum.Control
import QuantumQueryComplexity.Quantum.Padding
import QuantumQueryComplexity.Quantum.Mixture
import QuantumQueryComplexity.Quantum.Projector
import QuantumQueryComplexity.Quantum.Reflection
import QuantumQueryComplexity.Quantum.RoutineLift
import QuantumQueryComplexity.Quantum.Clock
import QuantumQueryComplexity.Quantum.ChordGap
import QuantumQueryComplexity.Quantum.ChordWindow
import QuantumQueryComplexity.Quantum.ClockGap
import QuantumQueryComplexity.Quantum.ClockDetector
import QuantumQueryComplexity.Quantum.OperationalGap
import QuantumQueryComplexity.Quantum.InputDetector
import QuantumQueryComplexity.Quantum.StateConversion
import QuantumQueryComplexity.Quantum.Witness
import QuantumQueryComplexity.Quantum.Fidelity
import QuantumQueryComplexity.Quantum.Detection
import QuantumQueryComplexity.Quantum.HadamardTest
import QuantumQueryComplexity.Quantum.UpperBound
import QuantumQueryComplexity.Quantum.XorOracle
import QuantumQueryComplexity.Quantum.Simulation
import QuantumQueryComplexity.Quantum.OneHot
import QuantumQueryComplexity.Quantum.OneHotSimulation
import QuantumQueryComplexity.Quantum.OneHotReadAll
import QuantumQueryComplexity.Quantum.OneHotTransport
import QuantumQueryComplexity.Quantum.Tail
import QuantumQueryComplexity.Quantum.KronLift
import QuantumQueryComplexity.Quantum.Postcomp
import QuantumQueryComplexity.Quantum.PostQuery
import QuantumQueryComplexity.Quantum.Relabel
import QuantumQueryComplexity.Quantum.UniformAlphabet
import QuantumQueryComplexity.Quantum.UniformWitness
import QuantumQueryComplexity.Quantum.UniformConversion
import QuantumQueryComplexity.Quantum.UniformExtraction
import QuantumQueryComplexity.Quantum.AlphabetSimulation
import QuantumQueryComplexity.Quantum.ProductRun
import QuantumQueryComplexity.Quantum.Amplify
import QuantumQueryComplexity.Quantum.FiniteOutput
import QuantumQueryComplexity.Quantum.Plurality
import QuantumQueryComplexity.Quantum.LowerBound.Bridge
import QuantumQueryComplexity.Quantum.LowerBound.Progress
import QuantumQueryComplexity.Quantum.LowerBound.Output
import QuantumQueryComplexity.Quantum.LowerBound.OutputBool
import QuantumQueryComplexity.Quantum.LowerBound.Main
import QuantumQueryComplexity.Quantum.LowerBound.MainBool
import QuantumQueryComplexity.Quantum.AcceptanceA
import QuantumQueryComplexity.Quantum.Relation
import QuantumQueryComplexity.Quantum.Amplitude.Geometry
import QuantumQueryComplexity.Quantum.Amplitude.Marker
import QuantumQueryComplexity.Quantum.Amplitude.Routine
import QuantumQueryComplexity.Quantum.Amplitude.Verifier
import QuantumQueryComplexity.Quantum.Amplitude.TrigSum
import QuantumQueryComplexity.Quantum.Amplitude.Randomized
import QuantumQueryComplexity.Quantum.Amplitude.FirstSuccess
import QuantumQueryComplexity.Quantum.Amplitude.Amplification
import QuantumQueryComplexity.Quantum.Amplitude.Search
import QuantumQueryComplexity.Quantum.Amplitude.Kernel
import QuantumQueryComplexity.Quantum.Amplitude.Fourier
import QuantumQueryComplexity.Quantum.Amplitude.PhaseEstimation
import QuantumQueryComplexity.Quantum.Amplitude.Estimation
import QuantumQueryComplexity.Quantum.Amplitude.Eigen
import QuantumQueryComplexity.Quantum.Amplitude.Counting
import QuantumQueryComplexity.Quantum.SelectRoutine
import QuantumQueryComplexity.Quantum.CoherentMajority
import QuantumQueryComplexity.Quantum.FirstOf
import QuantumQueryComplexity.Quantum.RobustSearch.Defs
import QuantumQueryComplexity.Quantum.RobustSearch.Recursion
import QuantumQueryComplexity.Quantum.RobustSearch.Filter
import QuantumQueryComplexity.Quantum.RobustSearch.Progress
import QuantumQueryComplexity.Quantum.RobustSearch.Main
import QuantumQueryComplexity.Quantum.RobustSearch.Public
import QuantumQueryComplexity.Quantum.Approximation
import QuantumQueryComplexity.Quantum.Amplitude.ApproxReflection
import QuantumQueryComplexity.Quantum.Amplitude.Recursive
import QuantumQueryComplexity.Quantum.Amplitude.Tolerant
import QuantumQueryComplexity.Quantum.Amplitude.CleanControl
import QuantumQueryComplexity.Quantum.Amplitude.ChainRoutine
import QuantumQueryComplexity.Quantum.Amplitude.SearchInv
import QuantumQueryComplexity.Quantum.History
import QuantumQueryComplexity.Quantum.Amplitude.TolerantPass
import QuantumQueryComplexity.Quantum.Amplitude.ApproxSearch
import QuantumQueryComplexity.Quantum.Amplitude.SearchInvUpTo
import QuantumQueryComplexity.Quantum.Amplitude.NoisyRefl
import QuantumQueryComplexity.Quantum.Walk.Gap
import QuantumQueryComplexity.Quantum.Walk.WeightedClock
import QuantumQueryComplexity.Quantum.Walk.ClockWeights
import QuantumQueryComplexity.Quantum.Walk.TwoReflections
import QuantumQueryComplexity.Quantum.Walk.Detect
import QuantumQueryComplexity.Quantum.Walk.Level
import QuantumQueryComplexity.Quantum.Walk.KronSupport
import QuantumQueryComplexity.Quantum.Walk.Global
import QuantumQueryComplexity.Quantum.Walk.GlobalInv
import QuantumQueryComplexity.Quantum.Walk.MNRS
import QuantumQueryComplexity.Quantum.Walk.Chain
set_option linter.style.header false

/-!
# The quantum query model

The operational layer of the project: quantum states, the value oracle, query
algorithms, bounded-error correctness, and query complexity.  This aggregate reaches
nothing of the classical development beyond the five shared foundation
modules (`Test/StreamBoundary.lean` enforces it), so
`lake build QuantumQueryComplexity.Quantum` builds the quantum layer alone.
The files that need both hierarchies live beside it: the library's own
(`Characterization`, `UniformHasDual`, the classic-example `*Applications`
and their `Acceptance*` pins) are imported by the library root
`QuantumQueryComplexity.lean`.
`Characterization.lean` has both the `1/16` and the conventional `1/3`
form; see `docs/quantum-query/README.md`.

Layers, in dependency order:

| file | contents |
| --- | --- |
| `FiniteHilbert` | `qInner`, `qNormSq`, unitaries, `qPerm`, reflections |
| `Measurement` | `qProb`, the outcome decomposition |
| `Oracle` | `QBasis`, the value oracle and its query decomposition |
| `Algorithm` | `QAlg`, state evolution, `ComputesWithErrorOn` |
| `Complexity` | `qQueryOn`, `boundedErrorQQueryOn` |
| `ReadAll` | the exact `|ι|`-query algorithm; `QueryCounts` is nonempty |
| `Solvable` | when `qQueryOn` is meaningful: the `sInf ∅ = 0` hazard, characterized |
| `Routine` | composable routines: sequencing, inversion, padding by two |
| `RunWith` | the run against an arbitrary oracle matrix; `comp_runWith` |
| `Blocks` | workspace extension / controlled operators: `blockFam` |
| `Control` | the controlled query in one physical query; parking; controlled routines |
| `Padding` | padding an algorithm; `QueryCounts` is upward closed |
| `Mixture` | finite mixtures of algorithms over a seed-dependent workspace: `mixAlg_prob`, `exists_mixture` |
| `Projector` | orthogonal projectors and reflections onto finite spans |
| `Reflection` | the input-dependent reflection, in exactly two queries |
| `RoutineLift` | lifting a routine along a workspace extension |
| `Clock` | the uniform clock, operationally: `selectPowers`, `clockAvgProj`, `clockPhaseRefl` |
| `ChordGap` | the chord form `(1-U)ᴴ(1-U)`: Hermitian, commutes with `U` |
| `ChordWindow` | CFC near/far windows; **the effective spectral gap** |
| `ClockGap` | uniform-clock suppression: the average is small on the far window |
| `ClockDetector` | the suppression bridge: `‖D·u + u‖² ≤ 16/(T²Δ²)‖x‖²` |
| `OperationalGap` | the gap theorem, specialized to the two-query routine |
| `InputDetector` | the detector for `inputReflProduct`, at exact cost `4(T-1)` |
| `StateConversion` | witness contracts: what makes the detector answer `+1` exactly |
| `Witness` | the witness states, built from a `DualPairOn`; the contracts discharged |
| `Fidelity` | generic `Re⟪ψ, Uψ⟫` estimates: fixed-vector overlap, far-pair suppression |
| `Detection` | the detector on the witness states: the two acceptance estimates |
| `HadamardTest` | the compiled Hadamard test: `P(true) = (1 + Re⟪u, R_a u⟫)/2` at `R.len` queries |
| `UpperBound` | **the dual-to-algorithm extraction**: `Q_{1/16}(f) ≤ 8192(1 + 4√|σ|·c)` |
| `XorOracle` | the standard Boolean XOR oracle, and its query model (`xorQQueryOn`) |
| `Simulation` | **oracle simulation**: transposition ↔ XOR at two queries per query |
| `OneHot` | **Milestone G**: the canonical one-hot XOR oracle model (`Hot σ`, `oneHotQQueryOn`) |
| `OneHotSimulation` | **Milestone G**: transposition ↔ one-hot XOR, direct, two queries per query |
| `OneHotReadAll` | **Milestone G**: exact `|ι|`-query one-hot read-all, `oneHotQQueryOn ≤ |ι|` |
| `OneHotTransport` | native ↔ one-hot transport of bounds; the exact read-all cap |
| `Tail` | the union-bound and majority-tail counts of the independent-run analysis |
| `KronLift` | lifting an operator along a factorizing equivalence; split states |
| `Postcomp` | classical postprocessing of the readout is free (`qQueryOn_postcomp_le`) |
| `Relabel` | renaming the oracle alphabet is free (`qQueryOn_relabel`) |
| `UniformAlphabet` | **Milestone D**: the `(1, ±e)` factorization of `[a ≠ b]`, squared norms `2` |
| `UniformWitness` | **Milestone D**: coherent target states over `range f`, `⟪t₋, t₊⟫ = ½[·]` |
| `UniformConversion` | **Milestone D**: the conversion distances, `e₊ ⟂ e₋`, the parameters |
| `UniformExtraction` | **Milestone D**: `exists_algorithm_of_dualPairOn_uniform` at `8192(1+c)` |
| `AlphabetSimulation` | **the two-query section lookup**: `qQueryOn_alphabetMap_le` |
| `ProductRun` | **the independent-run compiler**: banks, exact product statistics |
| `Amplify` | the `k`-fold product, majority amplification, and the tuple compiler |
| `FiniteOutput` | bit encoding/decoding, and the finite-output assembly |
| `Plurality` | **Milestone H**: plurality amplification, `Q_{1/16} ≤ 43·Q_{1/3}`, `7/1376` |
| `LowerBound/Bridge` | a real matrix against complex vector families |
| `LowerBound/Progress` | the progress measure and its three theorems |
| `LowerBound/Output` | the output condition |
| `LowerBound/OutputBool` | the **sharp** output condition `2√(ε(1−ε))`, for Boolean outputs |
| `LowerBound/Main` | **Milestone A**: `mul_advPMOn_le_qQueryOn` |
| `LowerBound/MainBool` | the sharp Boolean bound: `(1/36)·advPMOn ≤ Q_{1/3}`, no amplification |
| `AcceptanceA` | the Milestone A statements, pinned (a test, not a dependency) |
| `Relation` | relation-valued correctness: `successProbOn`, `SolvesWithErrorOn` |
| `Amplitude/Geometry` | the division-free two-reflection rotation; `sin²((2j+1)θ)` for all `0 ≤ p ≤ 1` |
| `Amplitude/Marker` | phase-marker contracts (full operator, clean ancilla, `MarksState`); verifier → marker at `2V`; coherent flag at `C` |
| `Amplitude/Routine` | `AmpSetup`, the compiled Grover iterate (`2S+C`), state equation, conditional law (product form) |
| `Amplitude/Verifier` | `AmpSetup.ofVerifier`: a setup from a preparation and a clean coherent verifier (`C = 2V`); logical law, success mass and `Marks` transported, so only `IsCoherentVerifier` is assumed |
| `Amplitude/TrigSum` | the averaged success of a uniformly random iteration count |
| `Amplitude/Randomized` | dilution, one verified trial, the padded uniform mixture; exact law and success `≥ 1/4` |
| `Amplitude/FirstSuccess` | named `pairAlg`, `mapOut`, `orElse` (first success of two optional outputs) |
| `Amplitude/Amplification` | **amplitude amplification**: `AmpSetup.amplified`, budget `≤ 16(S+C)/√p₀`, never an invalid output, `≥ 2/3`, conditional law |
| `Amplitude/Search` | search over `n` indices with `8m ≤ 16√(n/k)` native queries; exact uniformity over marked indices |
| `Amplitude/Kernel` | the phase-estimation kernel, circular distance, the tail bound and the mass `≤ 1/6` beyond `4/M` |
| `Amplitude/Fourier` | the normalized Fourier matrix (forward sign `+`), unitarity, Parseval, `≥ 5/6` within `4/M` |
| `Amplitude/PhaseEstimation` | operational phase estimation, `(M−1)·R.len` queries; outcome law and concentration on eigenvectors |
| `Amplitude/Estimation` | **amplitude estimation**: `S + (M−1)(2S+C)` queries, finite label with decoder `sin²(πy/M)`, error `8π√(p(1−p))/M + 16π²/M²` with probability `≥ 5/6`, additive `η` at `≤ 18π(S+C)/η` |
| `Amplitude/Eigen` | the eigenvectors `sin θ·b ± i cos θ·g` of the Grover iterate, eigenphases `∓θ/π`, orthogonality, decomposition of the prepared state |
| `Amplitude/Counting` | endpoints `p = 0`, `p = 1` (even clock); approximate counting with `2(M−1)` native queries |
| `SelectRoutine` | coherent selection of an indexed family of routines at the common length (`QRoutine.sig`), the padded adapter for algorithms with different workspaces/budgets (`selectPadded`), selection controlled by a spectator bank (`bankCtrl`), `swapRefl` |
| `CoherentMajority` | named `k`-fold repetition (`powRoutine`), exact product law, majority readout; from error `1/3`, `12n` copies give `2^{-n}` |
| `FirstOf` | bundled optional-output trials, first success of a list, union bound |
| `RobustSearch/Defs`, `Recursion` | levels and test banks; one step = amplify the recorded flag once, initialize a fresh bank by the index, test; `q' = 3q + q_filter`, `u' = (3−4p)²·u·τ` exactly |
| `RobustSearch/Filter`, `Progress`, `Main` | the banks of supplied algorithms, the level sequence and its closed-form cost; the scalar progress analysis; twelve trials per scale, first computed flag |
| `RobustSearch/Public` | **robust search** (Høyer–Mosca–de Wolf): `robustSearch`, budget `≤ 10206·T·⌈√m⌉` with no logarithm, relation `SearchOK`, the OR corollary |
| `Approximation` | the norm `qNorm`, measurement as a contraction, telescoping; the clean-ancilla approximate-reflection contract `IsApproxRefl` and its conjugation lemma (same `β`) |
| `Amplitude/ApproxReflection` | one amplification step with an approximate reflection, intrinsic to the actual state: `|√m' − |3−4m|√m| ≤ 2β√m`; a stage of the tolerant protocol |
| `Amplitude/Recursive` | the MNRS operator recursion `A_{j+1} = (A_j R_{j+1} A_j†) S A_j`; growth of the marked mass; some level `≤ K` reaches `1/10` |
| `Amplitude/Tolerant` | unknown overlap with one preparation: continuing unnormalized vectors, mass conservation, **one pass fails with probability `≤ 99/100`** |
| `Amplitude/CleanControl` | the clean-history reflection `cleanRefl c R`: `R` where the flag `c` holds, `−1` elsewhere, at cost `R.len` on both branches; `IsApproxRefl.clean` |
| `Amplitude/ChainRoutine` | supports (`SuppIn`, `Preserves`); the compiled level and stage routines `chainR`, `stageR` on one shared control workspace, exact costs `q_{j+1} = 3q_j + C + r_{j+1}`, and their operator equations |
| `Amplitude/SearchInv` | the caller's contract in terms of supports; it yields every hypothesis of the abstract recursion, hence `pass_fail_le ≤ 99/100` for the compiled operators |
| `History` | finite coherent measurement histories: slots outside the control workspace, free recording of a flagged value with the flag returned clean, supports preserved by lifted routines, first-slot readout |
| `Amplitude/TolerantPass` | one compiled pass `prepare; (check; record; stage)*`: exact cost with a single setup, the state as continuing vector plus recorded branches, `Pr[none] = ‖ν‖²`, unmarked never read |
| `Amplitude/ApproxSearch` | **search with an approximate reflection**: `110` passes; never an unmarked vertex, `≥ 2/3` under a marked-mass promise, `none` surely on the empty set; `passLen ≤ S + C + 2·3^{K+2}(2C + 21ρ)` |
| `Amplitude/SearchInvUpTo` | the contract restricted to the levels a search uses (`K + 1 ≤ L`: reflections `1..L`, flags `0..L−1`), the extension lemma (exact reflection `prepReflR` above `L`), `approxSearch_congr`, and the three search theorems for the caller's own finitely many routines |
| `Amplitude/NoisyRefl` | `noisyRefl s t t'`: three reflections; fixes `s` exactly, error `≤ 4‖t'−t‖` on the orthogonal component and not zero; adjoint, support preservation, commutation with flags |
| `Walk/Gap` | two spectral-free gap lemmas for walks: the Hermitian inequality `⟨z₁,(1−J)z₁⟩ ≥ (1−λ²)⟨z,(1+J)z⟩` (the gap of a product of two reflections from the discriminant), and the averaging bound on an invariant subspace where `‖(U−1)y‖ ≥ γ‖y‖` |
| `Walk/WeightedClock` | the detector `SELECT†(2|α⟩⟨α|−1)SELECT` for an arbitrary unit clock state `α`: cost `2(T−1)·len`, deviation `= 2·SELECT†(α ⊗ ∑|α_c|²U^c ψ)`, exact identity on fixed vectors; with `|α|²` the law of a sum of `k` uniform clocks this is the `k`-clock reflection on one register |
| `Walk/ClockWeights` | the clock state of `k` summed uniform clocks (coefficients of `avgPoly^k`); its weighted average is the `k`-th power of the uniform average |
| `Walk/TwoReflections` | two orthonormal families with Hermitian Gram matrix `D`: the walk `(2Π_B−1)(2Π_A−1)`, the stationary vector, the invariant subspace `K` orthogonal to it, and the gap `4δ‖v‖² ≤ ‖(1−W)v‖²` on `K` |
| `Walk/Detect` | the `k`-clock detector on `K` is a `2^{1−k}`-approximate reflection about `α ⊗ s`; the Householder clock preparation |
| `Walk/Level` | the level routine `upd ; prepare α ; detector ; unprepare ; upd⁻¹` on a clocked system: cost, Hermitian operator, the contract on `|0⟩ ⊗ (vertex combination)`, support preservation |
| `Walk/KronSupport` | supports, flags and the reflection contract transported along a `kronLift`; `QRoutine.kronLift_run` |
| `Walk/Global`, `Walk/GlobalInv` | the global workspace with one ancilla block per level (`blkEquiv`), and **the walk data satisfies `SearchInvUpTo`** |
| `Walk/MNRS` | **quantum-walk search**: `WalkSetup` (routines and chain data), `WalkOK` (their semantics on an input), the input-independent `walkSearch`, never an unmarked vertex, `≥ 2/3` under the stationary-mass promise, `none` surely on the empty set, budget `≤ 110·S + 4490640·⌈1/√ε⌉(⌈1/√δ⌉U + C)` |
| `Walk/Chain` | reversible chains and the discriminant (`disc_herm`, `disc_r`, `r_unit`); complete resampling (gap `1`) and the lazy two-state chain (gap `2p`) |

Two different notions of amplification live here: `Amplify` is classical *majority*
amplification of a Boolean answer (error reduction by repetition); `Amplitude/*` is
*amplitude* amplification of a success probability (quadratic speed-up).
-/
