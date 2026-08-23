/-
  VerificationAsymmetry/TheoremMap.lean

  Current-journal-paper theorem map, following the publication-facing pattern
  used by the Gray Code project.  Every numbered mathematical object and every
  load-bearing displayed derivation in the current EINT manuscript has a named
  Lean carrier or theorem below.

  Scope rule:
    * `#check` means the object exists in the compiled kernel environment.
    * Cat 2 textbook inputs are checked here and their downstream dependency is
      printed in `CurrentPaperAxiomAudit.lean`.
    * Narrative interpretation and empirical identification are not promoted to
      Lean propositions.
-/

import VerificationAsymmetry
import VerificationAsymmetry.CurrentPaperClaimBindings
import VerificationAsymmetry.AtomicPaperClaimBindings

open VerificationAsymmetry
open VerificationAsymmetry.Economy

/-! ## Definition 1 and Eq. (1): production economy and CES carrier. -/
#check VerificationAsymmetry.Economy
#check VerificationAsymmetry.Economy.IsCES
#check VerificationAsymmetry.Economy.axiom_ces_wage_ratio

/-! ## Remark 2: interpretation of the CES regime.
    The remark's load-bearing CES interface is `IsCES`; its textbook endpoint
    interpretations are explanatory and are not downstream proof obligations. -/

/-! ## Definition 3 and Eq. (2): AI-augmented generation. -/
#check VerificationAsymmetry.Economy.G
#check VerificationAsymmetry.Economy.G_zero
#check VerificationAsymmetry.Economy.G_one
#check VerificationAsymmetry.Economy.G_monotone_of_KAI_ge_LG
#check VerificationAsymmetry.Economy.G_diff
#check VerificationAsymmetry.Economy.G_tendsto_at_one
#check VerificationAsymmetry.Economy.G_rpow_tendsto_at_one
#check VerificationAsymmetry.Economy.G_rpow_endpoint_pos

/-! ## Definition 4 and Eq. (3): arbitrary-path cohort experience. -/
#check VerificationAsymmetry.Economy.cumulativeExperience
#check VerificationAsymmetry.Economy.cumulativeExperience_const
#check VerificationAsymmetry.Economy.eBar
#check VerificationAsymmetry.Economy.eBar_antitone

/-! ## Definition 5 and Assumption 6: verification-residual stock carrier. -/
#check VerificationAsymmetry.Economy.Vinf
#check VerificationAsymmetry.Economy.gHard
#check VerificationAsymmetry.Economy.hPow
#check VerificationAsymmetry.Economy.timeIndexedStock
#check VerificationAsymmetry.Economy.timeIndexedStock_eq_cohort_integral

/-! ## Lemma 7 and Eqs. (4)--(6): steady-state stock. -/
#check VerificationAsymmetry.Economy.steady_state_stock_identity
#check VerificationAsymmetry.Economy.timeIndexedStock_const_eq_Vinf
#check VerificationAsymmetry.Economy.VinfHard_eq_pow_of_eBar_ge_tauStar
#check VerificationAsymmetry.Economy.VinfHard_eq_zero_of_eBar_lt_tauStar
#check VerificationAsymmetry.Economy.prop_smooth_collapse_below
#check VerificationAsymmetry.Economy.prop_smooth_collapse_above

/-! ## Definition 8: V1--V3 diagnostic conditions. -/
#check VerificationAsymmetry.Economy.V2_TacitAccumulation
#check VerificationAsymmetry.Economy.VerificationAsymmetryDiagnostic
#check VerificationAsymmetry.Economy.verificationAsymmetryDiagnostic_of_V2
#check VerificationAsymmetry.Economy.Vinf_zero_at_theta_one_under_V2
#check VerificationAsymmetry.Economy.h_eBar_nonneg_under_V2

/-! ## Theorem 9 and Eqs. (7)--(8): asymmetry inversion. -/
#check VerificationAsymmetry.Economy.wageRatio
#check VerificationAsymmetry.Economy.wageRatio_eq_ces_marginal_product_ratio
#check VerificationAsymmetry.Economy.thm_inversion_wage_ratio_monotone
#check VerificationAsymmetry.Economy.thm_inversion_wage_ratio_strict
#check VerificationAsymmetry.Economy.wageRatioAtCapacity_tendsto_atTop
#check VerificationAsymmetry.Economy.CESCapacityPriceFamily
#check VerificationAsymmetry.Economy.CESCapacityPriceFamily.ratio_eq
#check VerificationAsymmetry.Economy.marginalProductWageRatioAtCapacity_tendsto_atTop
#check VerificationAsymmetry.Economy.Gstar
#check VerificationAsymmetry.Economy.thetaInv
#check VerificationAsymmetry.Economy.inversionCrossingSet
#check VerificationAsymmetry.Economy.thetaInvInf
#check VerificationAsymmetry.Economy.marginalProductCrossingSet
#check VerificationAsymmetry.Economy.thetaInvMarginalProductInf
#check VerificationAsymmetry.Economy.marginalProductCrossingSet_eq_inversionCrossingSet
#check VerificationAsymmetry.Economy.wageRatio_thetaInv_eq_target
#check VerificationAsymmetry.Economy.thetaInv_isLeast_crossingSet
#check VerificationAsymmetry.Economy.thetaInvInf_eq_thetaInv
#check VerificationAsymmetry.Economy.thetaInvMarginalProductInf_eq_thetaInv
#check VerificationAsymmetry.Economy.thm_inversion_threshold_closed_form
#check VerificationAsymmetry.Economy.thm_inversion_threshold_in_unit_interval
#check VerificationAsymmetry.Economy.thm_inversion_threshold_monotone_in_rBar
#check VerificationAsymmetry.Economy.Gstar_strict_in_rBar
#check VerificationAsymmetry.Economy.thm_inversion_threshold_strict_in_rBar
#check VerificationAsymmetry.Economy.thetaInvAtCapacity_antitone
#check VerificationAsymmetry.Economy.thetaInvAtCapacity_strictAnti
#check VerificationAsymmetry.Economy.thetaInvAtCapacity_tendsto_zero
#check VerificationAsymmetry.Economy.thetaInvAtCapacity_tendsto_zero_right
#check VerificationAsymmetry.Economy.thetaInvRatioInfAtCapacity
#check VerificationAsymmetry.Economy.thetaInvRatioInfAtCapacity_eventually_interior
#check VerificationAsymmetry.Economy.thetaInvRatioInfAtCapacity_tendsto_zero_right
#check VerificationAsymmetry.Economy.capacityMarginalProductCrossingSet
#check VerificationAsymmetry.Economy.thetaInvMarginalProductInfAtCapacity
#check VerificationAsymmetry.Economy.capacityMarginalProductCrossingSet_eq_capacityRatioCrossingSet
#check VerificationAsymmetry.Economy.thetaInvMarginalProductInfAtCapacity_eq_closedForm
#check VerificationAsymmetry.Economy.thetaInvMarginalProductInfAtCapacity_eventually_interior
#check VerificationAsymmetry.Economy.thetaInvMarginalProductInfAtCapacity_tendsto_zero_right
#check VerificationAsymmetry.Economy.thetaInvMarginalProductInf_eq_zero_of_target_le_baseline
#check VerificationAsymmetry.Economy.paper_theorem9_wage_ratio_large_capacity_atomic
#check VerificationAsymmetry.Economy.paper_theorem9_eventual_actual_threshold_atomic
#check VerificationAsymmetry.Economy.paper_theorem9_actual_threshold_limit_atomic

/-! ## Theorem 10 and Eqs. (9)--(10): hard collapse and exact step path. -/
#check VerificationAsymmetry.Economy.PaperStepContext
#check VerificationAsymmetry.Economy.thetaStar
#check VerificationAsymmetry.Economy.thetaStar_in_unit_interval
#check VerificationAsymmetry.Economy.eBar_ge_tauStar_iff_theta_le_thetaStar
#check VerificationAsymmetry.Economy.thm_collapse_below_threshold
#check VerificationAsymmetry.Economy.hardStockSlopeBelow
#check VerificationAsymmetry.Economy.hasDerivAt_hard_stock_below
#check VerificationAsymmetry.Economy.hardStockSlopeBelow_neg
#check VerificationAsymmetry.Economy.thm_collapse_jump_magnitude
#check VerificationAsymmetry.Economy.thm_collapse_jump_diff
#check VerificationAsymmetry.Economy.VinfHard_tendsto_left_at_thetaStar
#check VerificationAsymmetry.Economy.VinfHard_tendsto_right_zero_at_thetaStar
#check VerificationAsymmetry.Economy.thm_collapse_above_threshold
#check VerificationAsymmetry.Economy.cStar
#check VerificationAsymmetry.Economy.cStar_mem_open_interval
#check VerificationAsymmetry.Economy.stepExperience
#check VerificationAsymmetry.Economy.stepSubstitutionPath
#check VerificationAsymmetry.Economy.cumulativeExperience_step_eq_stepExperience
#check VerificationAsymmetry.Economy.stepExperience_ge_tauStar_iff
#check VerificationAsymmetry.Economy.gHard_stepExperience_eq_one_iff
#check VerificationAsymmetry.Economy.exactStepStock
#check VerificationAsymmetry.Economy.exactStepStock_eq_cohort_integral
#check VerificationAsymmetry.Economy.timeIndexedStock_step_eq_exactStepStock
#check VerificationAsymmetry.Economy.preStepStockIntegral
#check VerificationAsymmetry.Economy.preStepStockIntegral_eq_linear
#check VerificationAsymmetry.Economy.preStepStockIntegral_zero_after_Ts
#check VerificationAsymmetry.Economy.preStepStockIntegral_eq_transientStock
#check VerificationAsymmetry.Economy.transientStock
#check VerificationAsymmetry.Economy.thm_collapse_transient_linear
#check VerificationAsymmetry.Economy.exactStepStock_zero_after_last_straddle
#check VerificationAsymmetry.Economy.last_straddling_retirement_time

/-! ## Proposition 11 and Eq. (11): smooth-threshold collapse and kink. -/
#check VerificationAsymmetry.Economy.PaperSmoothThresholdContext
#check VerificationAsymmetry.Economy.gSmooth
#check VerificationAsymmetry.Economy.prop_smooth_collapse_below
#check VerificationAsymmetry.Economy.prop_smooth_collapse_above
#check VerificationAsymmetry.Economy.smoothSlopeBelowAtThreshold
#check VerificationAsymmetry.Economy.smoothSlopeAboveAtThreshold
#check VerificationAsymmetry.Economy.hasDerivAt_smooth_stock_below_at_threshold
#check VerificationAsymmetry.Economy.hasDerivAt_smooth_stock_above_at_threshold
#check VerificationAsymmetry.Economy.hasDerivWithinAt_smoothStock_left
#check VerificationAsymmetry.Economy.hasDerivWithinAt_smoothStock_right
#check VerificationAsymmetry.Economy.prop_smooth_collapse_kink

/-! ## Remark 12: smooth versus hard promotion.
    Its mathematical content is consumed by the two smooth stock formulas,
    the actual derivative theorems, and the strict kink theorem above. -/

/-! ## Theorem 13 and Eqs. (12)--(14): apprenticeship residual. -/
#check VerificationAsymmetry.Economy.PaperExternalityIncidenceContext
#check VerificationAsymmetry.Economy.LambdaJ
#check VerificationAsymmetry.Economy.Lambda
#check VerificationAsymmetry.Economy.LambdaJ_pos
#check VerificationAsymmetry.Economy.Lambda_pos
#check VerificationAsymmetry.Economy.intervalIntegral_exp_neg_eq_LambdaJ
#check VerificationAsymmetry.Economy.intervalIntegral_exp_neg_eq_Lambda
#check VerificationAsymmetry.Economy.MPpriv
#check VerificationAsymmetry.Economy.MPsoc
#check VerificationAsymmetry.Economy.externalityResidual
#check VerificationAsymmetry.Economy.thm_externality_residual_identity
#check VerificationAsymmetry.Economy.wedge
#check VerificationAsymmetry.Economy.thm_externality_wedge_identity
#check VerificationAsymmetry.Economy.hardPromotion_externalityResidual_zero_above
#check VerificationAsymmetry.Economy.hardPromotion_wedge_zero_above
#check VerificationAsymmetry.Economy.wedgeGrowthCore
#check VerificationAsymmetry.Economy.wedgeGrowthCoefficient
#check VerificationAsymmetry.Economy.wedgeExplicit
#check VerificationAsymmetry.Economy.hardPaperWedge
#check VerificationAsymmetry.Economy.wedge_eq_hardPaperWedge
#check VerificationAsymmetry.Economy.hardPaperWedge_eq_wedgeExplicit
#check VerificationAsymmetry.Economy.wedge_eq_wedgeExplicit
#check VerificationAsymmetry.Economy.wedgeExplicit_monotone
#check VerificationAsymmetry.Economy.smoothWedgeExponent_neg
#check VerificationAsymmetry.Economy.smoothWedgeExponent_eq_zero
#check VerificationAsymmetry.Economy.smoothWedgeExponent_pos
#check VerificationAsymmetry.Economy.smoothWedgePower_tendsto_atTop
#check VerificationAsymmetry.Economy.smoothWedgePower_eq_one
#check VerificationAsymmetry.Economy.smoothWedgePower_tendsto_zero
#check VerificationAsymmetry.Economy.smoothPaperWedge
#check VerificationAsymmetry.Economy.smoothMarginalProductWedge
#check VerificationAsymmetry.Economy.smoothMarginalProductWedge_eq_smoothPaperWedge
#check VerificationAsymmetry.Economy.smoothWedgeClosedForm
#check VerificationAsymmetry.Economy.smoothPaperWedge_eq_closedForm
#check VerificationAsymmetry.Economy.smoothPaperWedge_tendsto_atTop
#check VerificationAsymmetry.Economy.smoothPaperWedge_tendsto_endpoint
#check VerificationAsymmetry.Economy.smoothPaperWedge_tendsto_zero
#check VerificationAsymmetry.Economy.smoothMarginalProductWedge_tendsto_atTop
#check VerificationAsymmetry.Economy.smoothMarginalProductWedge_tendsto_endpoint
#check VerificationAsymmetry.Economy.smoothMarginalProductWedge_tendsto_zero
#check VerificationAsymmetry.Economy.thm_externality_pigouvian_cobb_douglas_from_axioms
#check VerificationAsymmetry.Economy.internalizedWedge
#check VerificationAsymmetry.Economy.prop_internalization

/-! ## Proposition 14 and Eq. (15): cross-profession aggregation. -/
#check VerificationAsymmetry.Economy.PaperAggregationContext
#check VerificationAsymmetry.Economy.thm_aggregation_cobb_douglas_zero
#check VerificationAsymmetry.Economy.thm_aggregation_least_resilient_collapse
#check VerificationAsymmetry.Economy.cesInner
#check VerificationAsymmetry.Economy.positiveComponentWeight
#check VerificationAsymmetry.Economy.cesInner_tendsto_positiveComponentWeight
#check VerificationAsymmetry.Economy.positiveComponentWeight_mem_unit
#check VerificationAsymmetry.Economy.aggregateCESQ
#check VerificationAsymmetry.Economy.aggregateCESQ_pos
#check VerificationAsymmetry.Economy.aggregateCESQ_tendsto_zero
#check VerificationAsymmetry.Economy.aggregationQ
#check VerificationAsymmetry.Economy.aggregationQ_tendsto_zero
#check VerificationAsymmetry.Economy.aggregateCES
#check VerificationAsymmetry.Economy.prop_aggregation_fixed_sigma_positive
#check VerificationAsymmetry.Economy.prop_aggregation_near_cobb_douglas_limit

/-! ## Strict one-declaration-per-fragment publication bindings. -/
#check VerificationAsymmetry.Economy.paper_definition1_parameters_exact
#check VerificationAsymmetry.Economy.paper_equation1_ces_exact
#check VerificationAsymmetry.Economy.paper_definition3_generation_supply_exact
#check VerificationAsymmetry.Economy.paper_equation2_generation_supply_exact
#check VerificationAsymmetry.Economy.paper_definition4_cohort_dynamics_exact
#check VerificationAsymmetry.Economy.paper_equation3_cumulative_experience_exact
#check VerificationAsymmetry.Economy.paper_assumption6_time_indexed_stock_exact
#check VerificationAsymmetry.Economy.paper_lemma7_steady_state_stock_exact
#check VerificationAsymmetry.Economy.paper_equation4_steady_state_stock_exact
#check VerificationAsymmetry.Economy.paper_equation5_hard_stock_exact
#check VerificationAsymmetry.Economy.paper_equation6_smooth_stock_exact
#check VerificationAsymmetry.Economy.paper_definition8_diagnostic_exact
#check VerificationAsymmetry.Economy.paper_theorem9_inversion_exact
#check VerificationAsymmetry.Economy.paper_equation7_wage_ratio_exact
#check VerificationAsymmetry.Economy.paper_equation8_inversion_threshold_exact
#check VerificationAsymmetry.Economy.paper_theorem10_pipeline_collapse_exact
#check VerificationAsymmetry.Economy.paper_equation9_collapse_threshold_exact
#check VerificationAsymmetry.Economy.paper_equation10_transient_stock_exact
#check VerificationAsymmetry.Economy.paper_proposition11_smooth_collapse_exact
#check VerificationAsymmetry.Economy.paper_equation11_smooth_stock_exact
#check VerificationAsymmetry.Economy.paper_theorem13_externality_exact
#check VerificationAsymmetry.Economy.paper_equation12_social_present_value_exact
#check VerificationAsymmetry.Economy.paper_equation13_apprenticeship_wedge_exact
#check VerificationAsymmetry.Economy.paper_equation14_explicit_wedge_exact
#check VerificationAsymmetry.Economy.paper_proposition14_aggregation_exact
#check VerificationAsymmetry.Economy.paper_equation15_aggregate_output_exact
