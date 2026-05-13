/-
  VerificationAsymmetry/AxiomAudit.lean

  Prints the axiom dependency list for every paper-level theorem.

  Trust policy.  Every paper-level theorem in this project should
  depend ONLY on the Lean kernel:

    * `propext`           — propositional extensionality
    * `Classical.choice`  — classical choice (used by `Real.rpow` and
                            other Mathlib reals)
    * `Quot.sound`        — quotient soundness

  No Cat 2 or Cat 3 atomic axioms are introduced by this project,
  because the paper's structural mathematics is entirely real-analytic
  (CES algebra, linear cohort accounting, finite products / sums,
  1-D Brouwer / intermediate-value theorem) and lives inside Mathlib.

  Inventory by category (live counts: see `lake env lean
  VerificationAsymmetry/Ledger.lean`):

    Cat 1 (Mathlib-derivable theorems): ALL paper-level results.
                                         Project has zero `axiom`s.
    Cat 2 (external textbook axioms):   NONE.
    Cat 3 (paper-novel axioms):         NONE.

  Per-axiom citations live in the corresponding theorem docstring in
  the source file.  Round-history (prior retracted citations + atomic
  refactor steps) lives in `gap_*.attackHistory` fields inside
  `VerificationAsymmetry.Ledger`.

  Per-theorem axiom dependency profile (verified by `#print axioms`
  below): all theorems expected to depend on Lean kernel only.

  Any axiom outside the Lean kernel (`propext`, `Classical.choice`,
  `Quot.sound`) is a RED FLAG — investigate.

  Usage:
    lake exe cache get
    lake env lean VerificationAsymmetry/AxiomAudit.lean
-/

import VerificationAsymmetry

-- Theorem~\ref{thm:decomp}
#print axioms VerificationAsymmetry.thm_decomp_euler_identity
#print axioms VerificationAsymmetry.thm_decomp
#print axioms VerificationAsymmetry.thm_decomp_factor_share
#print axioms VerificationAsymmetry.thm_decomp_cobb_douglas_shares

-- Theorem~\ref{thm:inversion}
#print axioms VerificationAsymmetry.Economy.thm_inversion_threshold_closed_form
#print axioms VerificationAsymmetry.Economy.thm_inversion_threshold_in_unit_interval
#print axioms VerificationAsymmetry.Economy.thm_inversion_wage_ratio_monotone
#print axioms VerificationAsymmetry.Economy.thm_inversion_threshold_monotone_in_rBar

-- Corollary~\ref{cor:bounded-AI}
#print axioms VerificationAsymmetry.Economy.cor_bounded_AI_threshold_at_rBarZero
#print axioms VerificationAsymmetry.Economy.cor_bounded_AI_threshold_at_rBarMax

-- Theorem~\ref{thm:collapse}
#print axioms VerificationAsymmetry.Economy.thm_collapse_below_threshold
#print axioms VerificationAsymmetry.Economy.thm_collapse_above_threshold
#print axioms VerificationAsymmetry.Economy.thm_collapse_jump_magnitude
#print axioms VerificationAsymmetry.Economy.thm_collapse_jump_diff
#print axioms VerificationAsymmetry.Economy.thm_collapse_transient_at_zero
#print axioms VerificationAsymmetry.Economy.thm_collapse_transient_at_Ts
#print axioms VerificationAsymmetry.Economy.thm_collapse_transient_linear
#print axioms VerificationAsymmetry.Economy.thm_collapse_transient_zero_after_Ts
#print axioms VerificationAsymmetry.Economy.thm_collapse_jump_general_h

-- Proposition~\ref{prop:smooth-collapse}
#print axioms VerificationAsymmetry.Economy.prop_smooth_collapse_below
#print axioms VerificationAsymmetry.Economy.prop_smooth_collapse_above

-- Theorem~\ref{thm:credential}
#print axioms VerificationAsymmetry.Economy.thm_credential_cobb_douglas_reduction
#print axioms VerificationAsymmetry.Economy.thm_credential_closed_form
#print axioms VerificationAsymmetry.Economy.thm_credential_leontief_pre_collapse
#print axioms VerificationAsymmetry.Economy.thm_credential_leontief_post_collapse
#print axioms VerificationAsymmetry.Economy.thm_credential_multiplicative_decay
#print axioms VerificationAsymmetry.Economy.thm_credential_premium_negative_at_collapse

-- Proposition~\ref{prop:junior-senior}
#print axioms VerificationAsymmetry.Economy.prop_junior_senior_wage

-- Theorem~\ref{thm:externality}
#print axioms VerificationAsymmetry.Economy.thm_externality_residual_identity
#print axioms VerificationAsymmetry.Economy.thm_externality_residual_nonneg
#print axioms VerificationAsymmetry.Economy.thm_externality_residual_pos
#print axioms VerificationAsymmetry.Economy.thm_externality_wedge_identity
#print axioms VerificationAsymmetry.Economy.thm_externality_pigouvian_cobb_douglas

-- Proposition~\ref{prop:internalization}
#print axioms VerificationAsymmetry.Economy.prop_internalization
#print axioms VerificationAsymmetry.Economy.prop_internalization_full

-- Proposition~\ref{prop:decentralized-theta}
#print axioms VerificationAsymmetry.Economy.prop_decentralized_theta_foc
#print axioms VerificationAsymmetry.Economy.prop_decentralized_theta_wG_strict
#print axioms VerificationAsymmetry.Economy.prop_decentralized_theta_overshoots

-- Theorem~\ref{thm:recursive}
#print axioms VerificationAsymmetry.Economy.thm_recursive_threshold_closed_form
#print axioms VerificationAsymmetry.Economy.thm_recursive_threshold_ratio
#print axioms VerificationAsymmetry.Economy.thm_recursive_threshold_leftward
#print axioms VerificationAsymmetry.Economy.thm_recursive_thetaStar_invariant
#print axioms VerificationAsymmetry.Economy.thm_recursive_VinfHard_invariant
#print axioms VerificationAsymmetry.Economy.thm_recursive_wage_ratio_amplification

-- Proposition~\ref{prop:boundary}
#print axioms VerificationAsymmetry.Economy.prop_boundary_collapse_iff

-- Theorem~\ref{thm:aggregation}
#print axioms VerificationAsymmetry.Economy.thm_aggregation_cobb_douglas_zero
#print axioms VerificationAsymmetry.Economy.thm_aggregation_least_resilient_collapse
#print axioms VerificationAsymmetry.Economy.thm_aggregation_perfect_substitutes_survival
#print axioms VerificationAsymmetry.Economy.thm_aggregation_perfect_substitutes_residual

-- Proposition~\ref{prop:adjustment-margins}
#print axioms VerificationAsymmetry.Economy.prop_adjustment_career_extension_strict
#print axioms VerificationAsymmetry.Economy.prop_adjustment_career_extension_bounded

-- Theorem~\ref{thm:endogenous-ai}
#print axioms VerificationAsymmetry.Economy.brouwer_1d
#print axioms VerificationAsymmetry.Economy.thm_endogenous_ai_existence
#print axioms VerificationAsymmetry.Economy.thm_endogenous_ai_uniqueness
#print axioms VerificationAsymmetry.Economy.thm_endogenous_ai_corner_exogenous
#print axioms VerificationAsymmetry.Economy.thm_endogenous_ai_corner_endogenous_inconsistent
#print axioms VerificationAsymmetry.Economy.thm_endogenous_ai_hysteresis_nonneg
#print axioms VerificationAsymmetry.Economy.thm_endogenous_ai_recovery_at_Tj
#print axioms VerificationAsymmetry.Economy.thm_endogenous_ai_full_recovery_at_T
#print axioms VerificationAsymmetry.Economy.thm_endogenous_ai_recovery_takes_full_career
