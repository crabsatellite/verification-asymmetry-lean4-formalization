/-
  VerificationAsymmetry/AxiomAudit.lean

  Prints the axiom dependency list for every paper-level theorem.

  ## Trust policy

  Every paper-level theorem in this project depends on:
    * the Lean kernel — `propext`, `Classical.choice`, `Quot.sound`;
    * the Cat 2 axioms declared in `Axioms.lean`, identified below.

  ## Inventory by category

  Cat 1 (Mathlib-derivable theorems).  Closed via `Real.rpow_*` and
                                       Mathlib real-analysis.

  Cat 2 (external textbook axioms).  Three atomic axioms:
    * `axiom_euler_crs` — Euler's identity for CRS production.
      Consumed by: `thm_decomp`.
      Citations: Euler 1755 (original) / Mas-Colell, Whinston,
      Green 1995 §5.B.2 (modern textbook).
    * `axiom_ces_wage_ratio` — CES marginal-product wage ratio
      admits the closed form `((1-η)/η) λ^ρ (G/V)^{1-ρ}`.
      Consumed by: `wageRatio_eq_ces_marginal_product_ratio`
      (which establishes that the Lean `wageRatio` closed-form def
      IS the CES marginal-product wage ratio for a generic CES `F`)
      — genuinely Lean-load-bearing.
      Citations: Arrow-Chenery-Minhas-Solow 1961 (original CES
      paper) / Acemoglu 2009 Ch. 15 (modern textbook).
    * `axiom_cobb_douglas_factor_share` — Cobb-Douglas verification
      factor share `w_V V = (1-η) Y`.
      Consumed by (via `cobb_douglas_steady_state_identity_from_axiom`
      bridge):
        - `thm_credential_cobb_douglas_reduction_from_axioms`
        - `prop_junior_senior_wage_from_axioms`
        - `thm_externality_pigouvian_cobb_douglas_from_axioms`
      Citations: Cobb-Douglas 1928 (original Cobb-Douglas paper) /
      Mas-Colell, Whinston, Green 1995 §5.B.2 (modern textbook).

  Cat 3 (paper-novel atomic axioms).  ZERO Lean axioms for the
                                      definitional atoms.  The
                                      genuine Cat 3 atomic inputs
                                      tracked as standalone Ledger
                                      `GapEntry` records are the
                                      `Economy` carrier and the four
                                      production-function-shape /
                                      diagnostic-regime
                                      hypothesisPredicates `IsCRS`,
                                      `IsCobbDouglas`, `IsCES`,
                                      `V2_TacitAccumulation`; each
                                      is encoded as a Lean
                                      `structure` (the carrier) or
                                      `Prop` (the predicates), NOT
                                      as an `axiom`.  The paper's
                                      derived closed-form notation
                                      (`Vinf`, `eBar`, `gHard`,
                                      `wageRatio`, `Gstar`, `Vreq`,
                                      ...) is definitional
                                      infrastructure (concrete
                                      `def`s holding by `rfl`), NOT
                                      standalone Cat 3 atomic
                                      inputs.  The Ledger.lean
                                      entries are the canonical
                                      record for both layers.

  Paper claims tracked as Ledger-only entries.  Four open claims
                                      have NO Lean
                                      `axiom`/`def`/`theorem`
                                      declaration.  These four
                                      claims have Lean derivation
                                      deferred for out-of-scope
                                      Mathlib infrastructure: window
                                      invariance
                                      (`gap_window_invariance_OPEN`),
                                      aggregation sequential kinks
                                      (`gap_aggregation_sequential_kinks_OPEN`),
                                      intermediate-regime elasticity
                                      (`gap_aggregation_intermediate_regime_OPEN`),
                                      narrative endogenous-AI-
                                      verification residual bound
                                      (`gap_prop_adjustment_narrative_OPEN`).
                                      One paper-proved limit is partial:
                                      `gap_thm_aggregation_near_cd_limit_PARTIAL`
                                      records the near-Cobb--Douglas
                                      variable-exponent limit pending Lean.
                                      A faithful sound STATEMENT of
                                      each requires Mathlib
                                      infrastructure (MeasureTheory
                                      integrals; continuity / kink
                                      analysis; residual
                                      non-codifiability semantics)
                                      beyond this formalization's
                                      structural scope.  A separate
                                      definitional claim is satisfied
                                      by construction:
                                      `gap_thm_recursive_invariance_DEFINITIONAL`
                                      records that `thetaStar` /
                                      `VinfHard` are defined without
                                      a μ parameter, so the paper's
                                      μ-invariance commitment of
                                      `\label{thm:recursive}` Part 4
                                      is satisfied by the Lean code's
                                      type-signature structure (no
                                      Lean theorem can be written —
                                      no μ-dependence to quantify
                                      over).  Encoding as
                                      `axiom` is unsound
                                      (`False`-injectable); encoding
                                      as `def : Prop` with a
                                      constraining predicate that
                                      equals the conclusion is
                                      vacuous (tautological).  The
                                      honest encoding is the Ledger
                                      `gapDefinitional` `GapEntry` record — a
                                      typed, `#eval`-retrievable
                                      declaration tracking the gap,
                                      its status, its paper source,
                                      and the reason it is not
                                      Lean-derived.  See the
                                      Ledger-only-entry exemption in
                                      the `Ledger.lean` top
                                      docstring.  Nothing is
                                      `#check`ed or `#print axioms`ed
                                      for these here — correctly, as
                                      there is no Lean declaration.
                                      The numerical-calibration
                                      corollary
                                      `cor_quant_predictions_calibration`
                                      is a derived `theorem`
                                      (`rw` + `norm_num`) and IS
                                      `#print axioms`-checked below.

  ## Trust profile

  Any axiom outside this list — i.e. anything beyond the Lean kernel
  and the three declared Cat 2 axioms — is a RED FLAG, investigate.
  No Ledger-only entry is an `axiom`: the closed numerical
  calibration is a derived `theorem`.  Four Ledger-only paper claims
  are `gapOpen`; the μ-free carrier observation is `gapDefinitional`.
  None is an added Lean axiom.

  Per-axiom citations live in the docstrings of `Axioms.lean`; the
  per-entry scope and notes for each closed result or deferred claim
  live in the corresponding `GapEntry` inside `Ledger.lean`.

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
#print axioms VerificationAsymmetry.Economy.cobb_douglas_steady_state_identity_from_axiom

-- Theorem~\ref{thm:decomp}
#print axioms VerificationAsymmetry.thm_decomp

-- Theorem~\ref{thm:inversion}
#print axioms VerificationAsymmetry.Economy.thm_inversion_threshold_closed_form
#print axioms VerificationAsymmetry.Economy.thm_inversion_threshold_in_unit_interval
#print axioms VerificationAsymmetry.Economy.thm_inversion_wage_ratio_monotone
-- Closed form IS the CES marginal-product wage ratio — consumes
-- `axiom_ces_wage_ratio` (Cat 2).
#print axioms VerificationAsymmetry.Economy.wageRatio_eq_ces_marginal_product_ratio
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
#print axioms VerificationAsymmetry.Economy.thm_collapse_value_at_thetaStar_general_h

-- Proposition~\ref{prop:smooth-collapse}
#print axioms VerificationAsymmetry.Economy.prop_smooth_collapse_below
#print axioms VerificationAsymmetry.Economy.prop_smooth_collapse_above

-- Theorem~\ref{thm:credential}
#print axioms VerificationAsymmetry.Economy.thm_credential_cobb_douglas_reduction
#print axioms VerificationAsymmetry.Economy.thm_credential_cobb_douglas_reduction_from_axioms
#print axioms VerificationAsymmetry.Economy.thm_credential_closed_form
#print axioms VerificationAsymmetry.Economy.thetaGrossPeak_in_unit
#print axioms VerificationAsymmetry.Economy.thm_credential_finite_capacity_peak_foc
#print axioms VerificationAsymmetry.Economy.thm_credential_finite_capacity_peak_unique
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
-- (The full-internalization corner ζ = 1 yielding 0 wedge is
-- captured by `internalizedWedge 1 ... = 0 · wedge ... = 0`
-- directly from the def; no separate Lean theorem is provided.)
#print axioms VerificationAsymmetry.Economy.prop_internalization

-- Proposition~\ref{prop:decentralized-theta}
#print axioms VerificationAsymmetry.Economy.prop_decentralized_theta_foc
#print axioms VerificationAsymmetry.Economy.prop_decentralized_theta_wG_strict
#print axioms VerificationAsymmetry.Economy.prop_decentralized_theta_overshoots

-- Theorem~\ref{thm:recursive}
-- (Part 3 μ-invariance of thetaStar and VinfHard is satisfied by
-- construction — the carriers carry no μ argument; no Lean theorem
-- is provided.  See `gap_thm_recursive_invariance_DEFINITIONAL` in
-- Ledger.lean.)
#print axioms VerificationAsymmetry.Economy.thm_recursive_threshold_closed_form
#print axioms VerificationAsymmetry.Economy.thm_recursive_threshold_ratio
#print axioms VerificationAsymmetry.Economy.thm_recursive_threshold_leftward
#print axioms VerificationAsymmetry.Economy.Vreq_ratio_bounds
#print axioms VerificationAsymmetry.Economy.thm_recursive_wage_ratio_amplification
#print axioms VerificationAsymmetry.Economy.thm_recursive_amplification_bounds
#print axioms VerificationAsymmetry.Economy.thm_recursive_log_slope_difference
#print axioms VerificationAsymmetry.Economy.thm_recursive_log_slope_acceleration

-- Proposition~\ref{prop:boundary}
#print axioms VerificationAsymmetry.Economy.prop_boundary_collapse_iff

-- Definition~\ref{def:diagnostic} V2 consequences (Cat 3
-- hypothesisPredicate `V2_TacitAccumulation` Lean-load-bearing
-- consumers).  Both V2 fields are consumed:
--   * `Vinf_zero_at_theta_one_under_V2` consumes `h_zero_at_zero`
--     (under V2, `V_∞(θ=1, g, h) = 0`);
--   * `h_eBar_nonneg_under_V2` consumes `h_monotone`
--     (and `h_zero_at_zero` as a secondary): on `θ ≤ 1`,
--     `0 ≤ h(ē(θ))`.
#print axioms VerificationAsymmetry.Economy.Vinf_zero_at_theta_one_under_V2
#print axioms VerificationAsymmetry.Economy.h_eBar_nonneg_under_V2

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

-- Paper claims tracked as Ledger-only entries.  Four open paper claims
-- have NO Lean `axiom`/`def`/`theorem` declaration:
-- claims (window invariance; aggregation sequential kinks;
-- intermediate-regime elasticity; the narrative endogenous-AI-
-- verification residual bound) with Lean derivation deferred — a
-- faithful sound statement of each requires Mathlib infrastructure
-- beyond this formalization's structural scope.  The paper-proved
-- near-Cobb--Douglas variable-exponent limit is separately tracked as
-- `gap_thm_aggregation_near_cd_limit_PARTIAL`.  One separate
-- definitional claim is satisfied by construction
-- (`gap_thm_recursive_invariance_DEFINITIONAL`) — `thetaStar` / `VinfHard`
-- are defined without a μ parameter, so the paper's μ-invariance
-- commitment is encoded in the type signatures themselves.  It is
-- tracked as `gapDefinitional`; the other four are `gapOpen` — see
-- `Ledger.lean` for the canonical records (and the Ledger-only-
-- entry exemption in its top docstring).  Nothing to `#check` or
-- `#print axioms` here, which is correct: there is no Lean
-- declaration to inspect.
-- Numerical calibration corollary: derived `theorem` (`rw` +
-- `norm_num`), so `#print axioms` it.
#print axioms VerificationAsymmetry.Economy.cor_quant_predictions_calibration
-- Derivable threshold-reduction conjunct split out of the
-- adjustment-margins narrative (real theorem).
#print axioms VerificationAsymmetry.Economy.prop_adjustment_threshold_reduction_floor
