import QuantumQueryComplexity.Test.StreamBoundary
import QuantumQueryComplexity.Test.StreamMarkers
import QuantumQueryComplexity.Test.LibraryBoundary
import QuantumQueryComplexity.Test.AxiomSupport
import QuantumQueryComplexity.Test.PredictionTreeCompose
import QuantumQueryComplexity.Test.PolynomialMethod
import QuantumQueryComplexity.Test.AmplitudeAmplification
import QuantumQueryComplexity.Test.AmplitudeEstimation
import QuantumQueryComplexity.Test.RobustSearch
import QuantumQueryComplexity.Test.QuantumWalk
import QuantumQueryComplexity.Test.TreeSearch

/-!
# Quantum query regression checks

The default build checks the library's import boundaries and the existing
polynomial-method, amplitude, robust-search, quantum-walk and tree-search
statement tests. CI also runs the axiom audit drivers directly.
-/
