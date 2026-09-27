import QuantumQueryComplexity.Test.AxiomSupport
import QuantumQueryComplexity.Test.PolynomialMethod
set_option linter.style.header false

/-!
# Axiom audit: the polynomial method (core)

Run on every CI run, directly:

    lake env lean --trust=0 QuantumQueryComplexity/Test/PolynomialAxioms.lean

Every declaration of the listed modules is checked, transitively, against the allowed
axioms `propext`, `Classical.choice`, `Quot.sound`.  Keep the module list explicit and
extend it when a production module is added.
-/

open QuantumQueryComplexity.AxiomAudit

#audit_axioms_of_modules [
    QuantumQueryComplexity.Polynomial.Boolean,
    QuantumQueryComplexity.Quantum.PolynomialMethod,
    QuantumQueryComplexity.Quantum.XorPolynomialMethod,
    QuantumQueryComplexity.Quantum.PolynomialLowerBound,
    QuantumQueryComplexity.Test.PolynomialMethod]
  pins [
    QuantumQueryComplexity.QAlg.exists_probability_polynomial,
    QuantumQueryComplexity.exists_xor_probability_polynomial,
    QuantumQueryComplexity.PolynomialMethodAcceptance.acceptance_degree_native,
    QuantumQueryComplexity.PolynomialMethodAcceptance.acceptance_degree_xor]

/-! ## The failure paths are exercised -/

/-- error: axiom audit: `sorryAx` depends on the forbidden axiom(s) [sorryAx]. -/
#guard_msgs in
#audit_axioms_of_decl sorryAx

/-- error: axiom audit: the module `QuantumQueryComplexity.NoSuchModule` is not in the environment. -/
#guard_msgs in
#audit_axioms_of_modules [QuantumQueryComplexity.NoSuchModule] pins []

/-- error: axiom audit: the pinned declaration `QuantumQueryComplexity.noSuchTheorem` does not exist. -/
#guard_msgs(error, drop info) in
#audit_axioms_of_modules [QuantumQueryComplexity.Polynomial.Boolean]
  pins [QuantumQueryComplexity.noSuchTheorem]
