/-
  VerificationAsymmetry/AxiomAudit.lean

  Prints the axiom dependency list for every paper-level theorem.

  ## Trust policy

  Every paper-level theorem in this project should depend on:
    * the Lean kernel — `propext`, `Classical.choice`, `Quot.sound`;
    * the Cat 2 axioms declared in `Axioms.lean`, identified below.

  ## Inventory by category (post-audit 2026-05)

  Cat 1 (Mathlib-derivable theorems).  Closed via `Real.rpow_*` and
                                       Mathlib real-analysis.

  Cat 2 (external textbook axioms).  Three atomic axioms:
    * `axiom_euler_crs` — Euler's identity for CRS production.
      Used by: `thm_decomp`.
      Citation: Mas-Colell, Whinston, Green (1995) §5.B.2.
    * `axiom_ces_wage_ratio` — CES marginal-product wage ratio
      admits the closed form `((1-η)/η) λ^ρ (G/V)^{1-ρ}`.
      Used by: identification of the `wageRatio` definition with
      the CES wage ratio (paper Eq.~\eqref{eq:wage-ratio}).
      Citation: Acemoglu (2009) §15.
    * `axiom_cobb_douglas_factor_share` — Cobb-Douglas verification
      factor share `w_V V = (1-η) Y`.
      Used by: `cobb_douglas_steady_state_identity`, which the
      `_from_axioms` versions of the Cobb-Douglas-regime theorems
      consume.
      Citation: Mas-Colell, Whinston, Green (1995) §5.B.2.

  Cat 3 (paper-novel atomic axioms).  ZERO.  Every paper-novel
                                      structural object (`Economy`,
                                      `Vinf`, `eBar`, `gHard`,
                                      `wageRatio`, `Vreq`, …) is
                                      encoded as a Lean *definition*,
                                      not an axiom.

  ## Audit history

  The 2026-05 audit refactored four theorems from substance-in-
  hypothesis form to honest axiom-discharged form:
    * `thm_decomp` (Decomp.lean) — previously took the Euler identity
      as a hypothesis; now derived from `axiom_euler_crs`.
    * `thm_credential_cobb_douglas_reduction`,
      `prop_junior_senior_wage`,
      `thm_externality_pigouvian_cobb_douglas` — previously took
      the composite Cobb-Douglas-factor-share identity as a
      hypothesis; now have `_from_axioms` companion theorems that
      discharge via `axiom_cobb_douglas_factor_share` + the
      definitional unfolding of `Vinf`.
    * `cor_bounded_AI_threshold_at_rBarZero`, `_at_rBarMax` —
      previously took the endpoint identity `Gstar V (rBarZero V) =
      L_G` as a hypothesis; now derived from `Real.rpow_mul` via
      `Gstar_at_rBarZero`, `Gstar_at_rBarMax`.

  ## Trust profile

  Any axiom outside this list — i.e. anything beyond the Lean kernel
  plus the three declared Cat 2 axioms — is a RED FLAG, investigate.

  Per-axiom citations live in the docstrings of `Axioms.lean`.
  Round-history (prior retracted citations, refactor steps) lives
  in `gap_*.attackHistory` fields inside `Ledger.lean`.

  Usage:
    lake exe cache get
    lake env lean VerificationAsymmetry/AxiomAudit.lean
-/

import VerificationAsymmetry

-- Cat 2 axioms (declared in Axioms.lean).
#print axioms VerificationAsymmetry.Economy.axiom_euler_crs
#print axioms VerificationAsymmetry.Economy.axiom_ces_wage_ratio
#print axioms VerificationAsymmetry.Economy.axiom_cobb_douglas_factor_share

-- Derived steady-state identity (definitional unfolding of Vinf).
#print axioms VerificationAsymmetry.Economy.steady_state_stock_identity
#print axioms VerificationAsymmetry.Economy.cobb_douglas_steady_state_identity

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
#print axioms VerificationAsymmetry.Economy.Gstar_at_rBarZero
#print axioms VerificationAsymmetry.Economy.Gstar_at_rBarMax

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
#print axioms VerificationAsymmetry.Economy.thm_credential_cobb_douglas_reduction_from_axioms
#print axioms VerificationAsymmetry.Economy.thm_credential_closed_form
#print axioms VerificationAsymmetry.Economy.thm_credential_leontief_pre_collapse
#print axioms VerificationAsymmetry.Economy.thm_credential_leontief_post_collapse
#print axioms VerificationAsymmetry.Economy.thm_credential_multiplicative_decay
#print axioms VerificationAsymmetry.Economy.thm_credential_premium_negative_at_collapse

-- Proposition~\ref{prop:junior-senior}
#print axioms VerificationAsymmetry.Economy.prop_junior_senior_wage
#print axioms VerificationAsymmetry.Economy.prop_junior_senior_wage_from_axioms

-- Theorem~\ref{thm:externality}
#print axioms VerificationAsymmetry.Economy.thm_externality_residual_identity
#print axioms VerificationAsymmetry.Economy.thm_externality_residual_nonneg
#print axioms VerificationAsymmetry.Economy.thm_externality_residual_pos
#print axioms VerificationAsymmetry.Economy.thm_externality_wedge_identity
#print axioms VerificationAsymmetry.Economy.thm_externality_pigouvian_cobb_douglas
#print axioms VerificationAsymmetry.Economy.thm_externality_pigouvian_cobb_douglas_from_axioms

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
