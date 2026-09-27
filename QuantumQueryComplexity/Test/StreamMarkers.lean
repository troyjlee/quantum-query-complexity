import QuantumQueryComplexity
import QuantumQueryComplexity.Test.StreamBoundary
set_option linter.style.header false

/-!
# The boundary test still refers to things that exist

Guards `QuantumQueryComplexity/Test/StreamBoundary.lean` against going stale.  If a
shared-foundation module is renamed, or one of the canary declarations
disappears, the corresponding list entry would no longer refer to anything —
so both lists are checked here against the *classical* cone, where every
entry must exist.  (A renamed *replacement* is not thereby permitted: the
whitelist matches module names, so the new name is rejected by
`StreamBoundary` until it is deliberately added.) The default check target
builds this module.
-/

open Lean in
run_cmd do
  let env ← getEnv
  for m in QuantumQueryComplexity.Test.sharedFoundation do
    unless env.header.moduleNames.contains m do
      throwError "the boundary whitelist is stale: `{m}` is no longer a \
        module.  Update `QuantumQueryComplexity.Test.sharedFoundation`."
  for n in QuantumQueryComplexity.Test.classicalMarkers do
    unless env.contains n do
      throwError "the boundary canary is vacuous: its marker `{n}` no longer \
        exists in the classical cone.  Update \
        `QuantumQueryComplexity.Test.classicalMarkers`."
