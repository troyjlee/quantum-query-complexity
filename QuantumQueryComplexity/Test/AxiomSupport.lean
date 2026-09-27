import Lean

/-!
# Axiom-audit support (test layer)

A small environment-inspection helper turning `#print axioms` into a failing regression
check. It is imported by audit drivers and the test build, never by the
production library root.

* `auditDecl n` collects the axioms `n` depends on **transitively** (`Lean.collectAxioms`)
  and throws on anything other than `propext`, `Classical.choice`, `Quot.sound` —
  `sorryAx` included.
* `auditModules mods pins` audits **every** declaration defined in each listed module
  (selected through `Environment.getModuleIdxFor?`, so Mathlib's declarations are not
  scanned), and throws if a module is missing from the environment, if a module
  contributes no declaration, or if a pinned declaration does not exist.  It reports the
  checked counts and the axioms encountered.

The drivers are run directly, `lake env lean --trust=0 <driver>`, on every CI run: a cached
build of a driver must not stand in for running its checks.
-/

namespace QuantumQueryComplexity.AxiomAudit

open Lean Elab Command

/-- The only axioms a checked declaration may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The axioms of `n` outside the allowed list. -/
def forbiddenAxioms (n : Name) : CoreM (Array Name) := do
  let axs ← collectAxioms n
  return axs.filter fun a => !allowedAxioms.contains a

/-- Audit one declaration: it must exist and use only allowed axioms. -/
def auditDecl (n : Name) : CoreM (Array Name) := do
  let env ← getEnv
  unless env.contains n do
    throwError "axiom audit: the declaration `{n}` does not exist."
  let bad ← forbiddenAxioms n
  unless bad.isEmpty do
    throwError "axiom audit: `{n}` depends on the forbidden axiom(s) {bad.toList}."
  collectAxioms n

/-- The declarations defined in the module `m` of the current environment. -/
def declsOfModule (m : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf? m
    | throwError "axiom audit: the module `{m}` is not in the environment."
  let mut out := #[]
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      out := out.push n
  return out

/-- Audit every declaration of every listed module, and the presence of the pins. -/
def auditModules (mods : List Name) (pins : List Name) : CoreM Unit := do
  let env ← getEnv
  let mut total := 0
  let mut seen : Array Name := #[]
  for m in mods do
    let decls ← declsOfModule m
    if decls.isEmpty then
      throwError "axiom audit: the module `{m}` contributes no declaration; a checker \
        that checks nothing must fail."
    for n in decls do
      let axs ← auditDecl n
      for a in axs do
        unless seen.contains a do seen := seen.push a
    total := total + decls.size
    logInfo m!"axiom audit: {m}: {decls.size} declarations checked"
  for p in pins do
    unless env.contains p do
      throwError "axiom audit: the pinned declaration `{p}` does not exist."
    let some idx := env.getModuleIdxFor? p
      | throwError "axiom audit: the pinned declaration `{p}` has no defining module."
    let pm := env.header.moduleNames[idx.toNat]!
    unless mods.contains pm do
      throwError "axiom audit: the pinned declaration `{p}` lives in `{pm}`, which is not \
        audited."
  logInfo m!"axiom audit: {total} declarations in {mods.length} modules, {pins.length} pins; \
    axioms encountered: {seen.toList}"

/-- `#audit_axioms_of_modules [M₁, …] pins [p₁, …]`. -/
syntax (name := auditModulesCmd)
  "#audit_axioms_of_modules " "[" ident,* "]" " pins " "[" ident,* "]" : command

@[command_elab auditModulesCmd] def elabAuditModules : CommandElab := fun stx => do
  match stx with
  | `(#audit_axioms_of_modules [$ms,*] pins [$ps,*]) =>
      let mods := ms.getElems.toList.map (·.getId)
      let pinNames := ps.getElems.toList.map (·.getId)
      liftCoreM (auditModules mods pinNames)
  | _ => throwUnsupportedSyntax

/-- `#audit_axioms_of_decl n`: audit a single declaration. -/
syntax (name := auditDeclCmd) "#audit_axioms_of_decl " ident : command

@[command_elab auditDeclCmd] def elabAuditDecl : CommandElab := fun stx => do
  match stx with
  | `(#audit_axioms_of_decl $n) => liftCoreM (discard <| auditDecl n.getId)
  | _ => throwUnsupportedSyntax

end QuantumQueryComplexity.AxiomAudit
