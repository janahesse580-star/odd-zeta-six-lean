import OddZetaSix.TrustAudit
import OddZetaSix.Statement
import OddZetaSix.SixFunctional
import OddZetaSix.SixIdentity
import OddZetaSix.SixAssembly
import OddZetaSix.SixConfluentHermite
import OddZetaSix.SixGateLocal
import OddZetaSix.SixConfluentGate
import OddZetaSix.SixTaylor
import OddZetaSix.SixSmallPrimes
import OddZetaSix.SixFolded
import OddZetaSix.SixLocalSlots
import OddZetaSix.SixPNTBridge
import OddZetaSix.SixFoldedCertCore
import OddZetaSix.SixPeriodicRate
import OddZetaSix.SixHighWalls
import OddZetaSix.SixArithRate
import OddZetaSix.SixRationalBounds
import OddZetaSix.SixContour
import OddZetaSix.SixHalfGamma
import OddZetaSix.SixPhaseBridge
import OddZetaSix.SixAnalyticCertCore
import OddZetaSix.SixAnalyticRate
import OddZetaSix.SixIrrational

/-!
# Project Axiom & Trust Audit

Fails compilation if any declaration in `OddZetaSix` depends on any axiom
outside `[propext, Classical.choice, Quot.sound]` (including `sorryAx`,
`Lean.ofReduceBool`, or `Lean.trustCompiler`).

Checks the complete unconditional proof of
`exists_irrational_riemannZeta_seven_to_seventeen`:
- Stage 1A + 1B (`SixFunctional`, `SixIdentity`, `SixAssembly`, `SixConfluentGate`);
- Stage 2A + 2B (`SixTaylor`, `SixSmallPrimes`, `SixFolded`, `SixLocalSlots`,
  `SixPNTBridge`, `SixFoldedCertCore`, `SixPeriodicRate`, `SixHighWalls`, `SixArithRate`);
- Stage 3 (`SixRationalBounds`, `SixContour`, `SixHalfGamma`, `SixPhaseBridge`,
  `SixAnalyticCertCore`, `AnalyticData.Shard0..Shard3`, `SixAnalyticRate`, `SixIrrational`).
-/

audit_project_axioms OddZetaSix

-- Locked final target statement (must use Mathlib's `riemannZeta`)
#check OddZetaSix.SixZetaIrrationalityStatement
#check OddZetaSix.sixZetaIrrationalityStatement_iff
#check OddZetaSix.sixZeta_irrational_iff_standard
#print axioms OddZetaSix.sixZeta_irrational_iff_standard

-- Stage 1A: SixFunctional & SixIdentity core theorems
#check OddZetaSix.six_degree_decay_inequality
#check OddZetaSix.sixKernel_degree
#check OddZetaSix.six_entry_degree_bound
#check OddZetaSix.sixKernel_reflection
#check OddZetaSix.matrixEntryKernel_reflection
#check OddZetaSix.sixEntryReal_isBigO_inv_sq
#check OddZetaSix.hasSum_sixEntryReal_fourthDerivative
#check OddZetaSix.sixZetaCoefficient_zero
#check OddZetaSix.sixZetaCoefficient_odd
#check OddZetaSix.six_aggregate_support
#check OddZetaSix.sixFunctional_eq_six
#check OddZetaSix.sixMatrix_det_eval
#check OddZetaSix.sixMatrix_det_totalDegree_le
#check OddZetaSix.sixPrimitivePolynomial_totalDegree_le
#check OddZetaSix.sixPrimitivePolynomial_eval_actual

-- Endgame skeleton & locked interfaces (SixAssembly)
#check OddZetaSix.sixNorm
#check OddZetaSix.SixGateHypothesis
#check OddZetaSix.SixArithRateHypothesis
#check OddZetaSix.SixAnalyticRateHypothesis
#check OddZetaSix.sixZeta_irrational_of_hypotheses

-- Stage 1B: J = 3 confluent p-adic gate & live closure of SixGateHypothesis
#check OddZetaSix.sixGateEvalMatrixModSq_det_ne_zero
#check OddZetaSix.sixGateTailOrder_eq
#check OddZetaSix.sixSingularEntry_eq_collapsed
#check OddZetaSix.sixGateBlock_det_0
#check OddZetaSix.sixGateBlock_det_1
#check OddZetaSix.sixGateBlock_det_2
#check OddZetaSix.sixGateBlock_det_zmod_ne_zero
#check OddZetaSix.sixGateLeftDiag_det
#check OddZetaSix.sixGateRightDiag_det
#check OddZetaSix.sixGate_rational_det_valuation
#check OddZetaSix.sixGate_primitivePolynomial_ne_zero
#check OddZetaSix.sixGate_proved
#check OddZetaSix.sixZeta_irrational_of_arith_and_analytic

-- Stage 2A: Per-prime general arithmetic bounds (SixTaylor, SixSmallPrimes, SixFolded, SixLocalSlots)
#check OddZetaSix.valAtLeast_p_pow_evenBasis_taylor
#check OddZetaSix.padicValRat_p_pow_evenBasis_taylor_shift_ge
#check OddZetaSix.p_pow_taylorCoeff_evenBasis_shift
#check OddZetaSix.p_pow_taylorCoeff_evenBasis_neg
#check OddZetaSix.evenBasis_weighted_allPrimes
#check OddZetaSix.sixPrimitiveScalar_universal_bound_55
#check OddZetaSix.sixPrimitiveScalar_universal_bound
#check OddZetaSix.sixPrimitiveScalar_large_prime_integral
#check OddZetaSix.sixMatrix_cleared_by_lcm_18
#check OddZetaSix.cauchy_binet_det_mul
#check OddZetaSix.doubled_cauchy_binet_formalValAtLeast
#check OddZetaSix.coarse_tail_sum_le_four_mul
#check OddZetaSix.folded_joint_formalValAtLeast
#check OddZetaSix.unfolded_formalValAtLeast
#check OddZetaSix.folded_periodic_coarse_formalValAtLeast
#check OddZetaSix.sixMatrix_eq_evalJet_mul_weight
#check OddZetaSix.sixLocalRegularFactor_coeff_valAtLeast
#check OddZetaSix.sixCoarsePeriodicCost_le_18
#check OddZetaSix.sixRefinedSlotCost_le_coarse
#check OddZetaSix.sixPrimitiveScalar_folded_joint_bound
#check OddZetaSix.sixPrimitiveScalar_unfolded_bound
#check OddZetaSix.sixPrimitiveScalar_periodic_coarse_bound

-- Stage 2B: Vendored PNT bridge, certified periodic & high bands, and live closure of SixArithRateHypothesis
#check OddZetaSix.sixTinyPrimes_rate_eventually_le
#check OddZetaSix.sixArithRate_of_three_bands
#check OddZetaSix.allPeriodicPieces_valid
#check OddZetaSix.sixPeriodicBand_rate_le
#check OddZetaSix.allHighTiles_valid
#check OddZetaSix.sixHighBand_rate_le
#check OddZetaSix.sixArithRate_proved
#check OddZetaSix.sixZeta_irrational_of_analytic

-- Stage 3: Analytic contour, Gamma phase bridge, slim 4-bin certificate, and unconditional endgame
#check OddZetaSix.sixVerticalIntegral_eq_functional
#check OddZetaSix.sixFunctional_det_abs_le_monicMoments
#check OddZetaSix.sixBasisNormalization_log_rate
#check OddZetaSix.sixModulusWeight_uniform_envelope_abs
#check OddZetaSix.sixPhasePotential_tail_line
#check OddZetaSix.sixAnalyticRate_of_four_bin_endpoints
#check OddZetaSix.sixConstUpper_ok
#check OddZetaSix.AnalyticData.shard0_ok
#check OddZetaSix.AnalyticData.shard1_ok
#check OddZetaSix.AnalyticData.shard2_ok
#check OddZetaSix.AnalyticData.shard3_ok
#check OddZetaSix.sixSlimCompact_certified
#check OddZetaSix.sixAnalyticRate_proved
#check OddZetaSix.sixZeta_irrational
#check OddZetaSix.exists_irrational_riemannZeta_seven_to_seventeen

#print axioms OddZetaSix.sixZeta_irrational_of_hypotheses
#print axioms OddZetaSix.sixGateEvalMatrixModSq_det_ne_zero
#print axioms OddZetaSix.sixGateBlock_det_zmod_ne_zero
#print axioms OddZetaSix.sixGate_rational_det_valuation
#print axioms OddZetaSix.sixGate_proved
#print axioms OddZetaSix.sixZeta_irrational_of_arith_and_analytic
#print axioms OddZetaSix.padicValRat_p_pow_evenBasis_taylor_shift_ge
#print axioms OddZetaSix.sixPrimitiveScalar_universal_bound_55
#print axioms OddZetaSix.sixPrimitiveScalar_large_prime_integral
#print axioms OddZetaSix.folded_joint_formalValAtLeast
#print axioms OddZetaSix.folded_periodic_coarse_formalValAtLeast
#print axioms OddZetaSix.sixMatrix_eq_evalJet_mul_weight
#print axioms OddZetaSix.sixPrimitiveScalar_folded_joint_bound
#print axioms OddZetaSix.sixPrimitiveScalar_unfolded_bound
#print axioms OddZetaSix.sixPrimitiveScalar_periodic_coarse_bound
#print axioms OddZetaSix.sixTinyPrimes_rate_eventually_le
#print axioms OddZetaSix.sixArithRate_of_three_bands
#print axioms OddZetaSix.allPeriodicPieces_valid
#print axioms OddZetaSix.sixPeriodicBand_rate_le
#print axioms OddZetaSix.allHighTiles_valid
#print axioms OddZetaSix.sixHighBand_rate_le
#print axioms OddZetaSix.sixArithRate_proved
#print axioms OddZetaSix.sixZeta_irrational_of_analytic
#print axioms OddZetaSix.sixVerticalIntegral_eq_functional
#print axioms OddZetaSix.sixAnalyticRate_of_four_bin_endpoints
#print axioms OddZetaSix.sixAnalyticRate_proved
#print axioms OddZetaSix.sixZeta_irrational
#print axioms OddZetaSix.exists_irrational_riemannZeta_seven_to_seventeen
