import QuantumQueryComplexity

set_option linter.style.header false

/-!
# The library boundary test

The standalone library depends only on its own modules and its Lean/Mathlib foundations:

> `import QuantumQueryComplexity` reaches only its own modules, Lean,
> Mathlib and the pinned Mathlib dependencies.

The root imports the quantum aggregate and every library integration file,
so this check covers the whole library. A sanity clause guards against the
check becoming vacuous. The default check target builds this module.
-/

open Lean in
run_cmd do
  let env ← getEnv
  unless env.header.moduleNames.contains `QuantumQueryComplexity.HasDual do
    throwError "the library boundary test is vacuous: `QuantumQueryComplexity.HasDual` \
      is not in the environment."
  let allowedRoots := ["QuantumQueryComplexity", "Init", "Lean", "Std", "Lake",
    "Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets", "ImportGraph",
    "LeanSearchClient", "Plausible", "Cli"]
  for m in env.header.moduleNames do
    unless allowedRoots.any (fun root => m.toString == root || m.toString.startsWith (root ++ ".")) do
      throwError "library boundary violated: the library root `QuantumQueryComplexity` \
        reaches `{m}`, outside Lean, Mathlib, its pinned dependencies, and the library."
