import QuantumQueryComplexity.Test.AxiomSupport
import QuantumQueryComplexity.Test.AmplitudeAmplification
import QuantumQueryComplexity.Test.AmplitudeEstimation
import QuantumQueryComplexity.Quantum.Amplitude.Eigen

/-!
# Axiom audit: amplitude amplification and estimation

Run on every CI run, directly:

    lake env lean --trust=0 QuantumQueryComplexity/Test/AmplitudeAxioms.lean

Every declaration of the listed modules may depend only on `propext`, `Classical.choice`,
`Quot.sound`, transitively.  Extend the list when a production module is added.
-/

open QuantumQueryComplexity.AxiomAudit

#audit_axioms_of_modules [
    QuantumQueryComplexity.Quantum.Relation,
    QuantumQueryComplexity.Quantum.Amplitude.Geometry,
    QuantumQueryComplexity.Quantum.Amplitude.Marker,
    QuantumQueryComplexity.Quantum.Amplitude.Routine,
    QuantumQueryComplexity.Quantum.Amplitude.Verifier,
    QuantumQueryComplexity.Quantum.Amplitude.TrigSum,
    QuantumQueryComplexity.Quantum.Amplitude.Randomized,
    QuantumQueryComplexity.Quantum.Amplitude.FirstSuccess,
    QuantumQueryComplexity.Quantum.Amplitude.Amplification,
    QuantumQueryComplexity.Quantum.Amplitude.Search,
    QuantumQueryComplexity.Test.AmplitudeAmplification,
    QuantumQueryComplexity.Quantum.Amplitude.Kernel,
    QuantumQueryComplexity.Quantum.Amplitude.Fourier,
    QuantumQueryComplexity.Quantum.Amplitude.PhaseEstimation,
    QuantumQueryComplexity.Quantum.Amplitude.Estimation,
    QuantumQueryComplexity.Quantum.Amplitude.Eigen,
    QuantumQueryComplexity.Quantum.Amplitude.Counting,
    QuantumQueryComplexity.Test.AmplitudeEstimation]
  pins [
    QuantumQueryComplexity.AmpSetup.successProbOn_ampAlg,
    QuantumQueryComplexity.AmpSetup.two_thirds_le_returnProb,
    QuantumQueryComplexity.AmpSetup.amplified_prob_some_of_not_good,
    QuantumQueryComplexity.AmpSetup.succProb_mul_amplified_prob_some,
    QuantumQueryComplexity.AmpSetup.amplifiedBudget_le_real,
    QuantumQueryComplexity.markedCount_mul_searchAlg_prob_some,
    QuantumQueryComplexity.AmplitudeAmplificationAcceptance.acceptance_public,
    QuantumQueryComplexity.AmplitudeAmplificationAcceptance.acceptance_search,
    QuantumQueryComplexity.ofVerifier_marks,
    QuantumQueryComplexity.ofVerifier_origAlg_prob,
    QuantumQueryComplexity.AmplitudeAmplificationAcceptance.acceptance_verifier_public,
    QuantumQueryComplexity.AmplitudeAmplificationAcceptance.acceptance_verifier_lengths,
    QuantumQueryComplexity.AmplitudeAmplificationAcceptance.Fixture.isCoherentVerifier3,
    QuantumQueryComplexity.AmplitudeAmplificationAcceptance.Fixture.setup3_amplified,
    QuantumQueryComplexity.fourierMat_mem_unitaryGroup,
    QuantumQueryComplexity.three_quarters_le_pe_close,
    QuantumQueryComplexity.AmpSetup.aeAlg_prob,
    QuantumQueryComplexity.GroverSplit.iterate_wPlus,
    QuantumQueryComplexity.GroverSplit.sin_two_mul_smul_eq,
    QuantumQueryComplexity.AmpSetup.three_quarters_le_ae_accurate,
    QuantumQueryComplexity.AmpSetup.ae_additive,
    QuantumQueryComplexity.three_quarters_le_count_accurate,
    QuantumQueryComplexity.AmplitudeEstimationAcceptance.acceptance_ae_accuracy,
    QuantumQueryComplexity.AmplitudeEstimationAcceptance.acceptance_count,
    QuantumQueryComplexity.five_sixths_le_good_mass,
    QuantumQueryComplexity.five_sixths_le_pe_close,
    QuantumQueryComplexity.AmpSetup.five_sixths_le_ae_accurate,
    QuantumQueryComplexity.AmpSetup.ae_additive_five_sixths,
    QuantumQueryComplexity.five_sixths_le_count_accurate,
    QuantumQueryComplexity.count_additive_five_sixths,
    QuantumQueryComplexity.AmplitudeEstimationAcceptance.acceptance_ae_additive_five_sixths,
    QuantumQueryComplexity.AmplitudeEstimationAcceptance.acceptance_count_five_sixths,
    QuantumQueryComplexity.AmplitudeEstimationAcceptance.acceptance_verifier_estimation]

/-- error: axiom audit: `sorryAx` depends on the forbidden axiom(s) [sorryAx]. -/
#guard_msgs in
#audit_axioms_of_decl sorryAx
