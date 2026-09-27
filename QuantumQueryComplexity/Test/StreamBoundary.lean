import QuantumQueryComplexity.Quantum
set_option linter.style.header false

/-!
# The stream-separation boundary test

The quantum layer's import invariant:

> from `import QuantumQueryComplexity.Quantum`, **no non-shared classical module is
> reachable**.

The check is a *whitelist over the import closure*, not a search for
particular declarations: every `QuantumQueryComplexity.*` module in the closure must be
either `QuantumQueryComplexity.Quantum` / `QuantumQueryComplexity.Quantum.*` or one of the five shared
foundation modules listed in `sharedFoundation`.  A blacklist of sentinel
declarations would not do — importing, say, `QuantumQueryComplexity.HasDual` exposes
classical code while tripping no sentinel.

A secondary canary follows: a handful of classical-cone declarations that
must not be reachable either.  It is redundant against the whitelist but
cheap, and it names the failure in terms a reader recognises.

The whitelist is also checked to be **exactly minimal**: every entry must
really be imported *by `QuantumQueryComplexity.Quantum`*, so a permission left behind by a
dependency the quantum layer no longer has is rejected.  The check is anchored
to `QuantumQueryComplexity.Quantum`'s ancestry (`findRedundantImports`), not to this file's
environment — otherwise a stale module imported directly *here* and then
whitelisted would pass.  It belongs here rather than in `StreamMarkers.lean`,
whose environment is the *combined* classical and quantum one, where a
classical-only module is present regardless.

The default check target builds this module. `StreamMarkers.lean` is its
companion, checking that the whitelist and the canary both still refer to
things that exist, so that neither can go stale.

**Testing this test.**  Importing this module does *not* re-run the checks
below — `run_cmd` fires when the module is elaborated, not when it is
imported.  A negative control must therefore repeat the closure check in the
probe file itself (or temporarily edit this one).  The control of record:
a file importing `QuantumQueryComplexity.Quantum` *and* `QuantumQueryComplexity.HasDual` that
re-runs the loop is rejected with `reaches QuantumQueryComplexity.HasDual`, while the
same file checking only `classicalMarkers` reports nothing — which is why the
module whitelist, not the canary, is what enforces the invariant.
-/

namespace QuantumQueryComplexity.Test

/-- The only classical modules the quantum layer is permitted to reach:
the shared foundation, deliberately kept small. -/
def sharedFoundation : List Lean.Name :=
  [`QuantumQueryComplexity.Defs, `QuantumQueryComplexity.Spectral, `QuantumQueryComplexity.Basic, `QuantumQueryComplexity.Dual,
    `QuantumQueryComplexity.Promise.Defs]

/-- Declarations that exist only in the library's classical cone (outside the shared
foundation) — a secondary canary. -/
def classicalMarkers : List Lean.Name :=
  [`QuantumQueryComplexity.HasDual, `QuantumQueryComplexity.advDual_eq_advPM, `QuantumQueryComplexity.advPM_composeFun_eq,
    `QuantumQueryComplexity.edFun, `QuantumQueryComplexity.kdFun, `QuantumQueryComplexity.ldsFun]

/-- Is `m` a module the quantum layer may reach? -/
def moduleAllowed (m : Lean.Name) : Bool :=
  let s := m.toString
  if s == "QuantumQueryComplexity" then false
  else if s == "QuantumQueryComplexity.Quantum" || s.startsWith "QuantumQueryComplexity.Quantum." then true
  else if s.startsWith "QuantumQueryComplexity." then sharedFoundation.contains m
  else ["Init", "Lean", "Std", "Lake", "Mathlib", "Batteries", "Aesop", "Qq",
    "ProofWidgets", "ImportGraph", "LeanSearchClient", "Plausible", "Cli"].any
      (fun root => s == root || s.startsWith (root ++ "."))

end QuantumQueryComplexity.Test

open Lean in
run_cmd do
  let env ← getEnv
  for m in env.header.moduleNames do
    unless QuantumQueryComplexity.Test.moduleAllowed m do
      throwError "stream separation violated: `QuantumQueryComplexity.Quantum` reaches the \
        classical module `{m}`.  The quantum aggregate may reach only the \
        shared foundation (see `QuantumQueryComplexity.Test.sharedFoundation`); put \
        cross-stream work in an integration file built as an explicit CI \
        target."
  for n in QuantumQueryComplexity.Test.classicalMarkers do
    if env.contains n then
      throwError "stream separation violated: the classical declaration \
        `{n}` is reachable from `QuantumQueryComplexity.Quantum`."
  -- the whitelist must be exactly the closure, not merely contain it.
  -- Anchor this to `QuantumQueryComplexity.Quantum`'s own ancestry rather than to this
  -- file's environment: `findRedundantImports #[m, Q]` contains `m` exactly
  -- when `Q` (transitively) imports `m`, so a module this test happens to
  -- import directly cannot launder a stale permission.
  for m in QuantumQueryComplexity.Test.sharedFoundation do
    unless (env.findRedundantImports #[m, `QuantumQueryComplexity.Quantum]).contains m do
      throwError "stale permission: `{m}` is whitelisted in \
        `QuantumQueryComplexity.Test.sharedFoundation` but `QuantumQueryComplexity.Quantum` does not \
        import it.  Trim the whitelist so it stays exactly minimal."
  -- the literal list itself must be well-formed
  unless QuantumQueryComplexity.Test.sharedFoundation.Nodup do
    throwError "`QuantumQueryComplexity.Test.sharedFoundation` has a duplicate entry."
  for m in QuantumQueryComplexity.Test.sharedFoundation do
    let str := m.toString
    unless str.startsWith "QuantumQueryComplexity."
        && !(str == "QuantumQueryComplexity.Quantum" || str.startsWith "QuantumQueryComplexity.Quantum.") do
      throwError "`{m}` does not name a non-Quantum `QuantumQueryComplexity.*` module, so \
        whitelisting it is meaningless."
