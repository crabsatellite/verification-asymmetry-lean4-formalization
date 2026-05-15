/-
  VerificationAsymmetry/Aggregation.lean

  Theorem~\ref{thm:aggregation} (Welfare Aggregation Across
  Professions) and Proposition~\ref{prop:adjustment-margins}
  (Adjustment Margins).

  Companion to: "Generation--Verification Asymmetry Inversion and
  Apprenticeship Pipeline Collapse Under AI Substitution" (Li, 2026).

  Statement.

    Cross-profession CES aggregator with elasticity σ_a > 0,
    weights ω_i > 0 summing to 1.  Each Y_i depends on θ via
    its profession-specific apprenticeship dynamics.

    Part 2.  Cobb-Douglas aggregation (σ_a → 1): if any Y_i → 0
              with ω_i > 0, then Y_agg → 0.  Aggregate collapses
              as soon as the least resilient profession crosses
              θ*_(1) = min_i θ*_i.

    Part 3.  Perfect-substitutes aggregation (σ_a → ∞):
              Y_agg = Σ ω_i Y_i.  Collapse of one profession leaves
              Y_agg = Σ_{j ≠ i} ω_j Y_j > 0.

  Lean strategy.  Parts 2 and 3 are the substantive mathematical
  content.  Both are statements about real-valued products and sums
  over finite index sets; we formalize the structural mathematics
  (Cobb-Douglas zero-product, perfect-substitutes positive-sum)
  using Finset machinery.

  Part 1 (sequential phase transitions) and Part 4 (intermediate
  regime sigma_a ∈ (1, ∞)) are continuity / kink statements about
  the CES aggregator.  A faithful sound Lean STATEMENT of each
  requires Mathlib continuity / one-sided-limit / calculus
  infrastructure beyond this formalization's structural scope; they
  are tracked as `gapOpen` Ledger `GapEntry` records
  (`gap_aggregation_sequential_kinks_OPEN`,
  `gap_aggregation_intermediate_regime_OPEN` in `Ledger.lean`)
  WITHOUT a corresponding Lean `axiom`/`def`/`theorem` declaration.
  Proposition~\ref{prop:adjustment-margins} (career extension,
  threshold reduction, endogenous AI verification) is mostly
  economic-narrative content; we formalize the career-extension
  monotonicity and the threshold-reduction floor as `theorem`s, and
  track the endogenous-AI-verification residual bound as a
  `gapOpen` Ledger record (`gap_prop_adjustment_narrative_OPEN`)
  WITHOUT a Lean declaration — its faithful statement is a
  substantive empirical claim with a cohort-study resolution path,
  not a Lean derivation.
-/

import VerificationAsymmetry.Basic
import VerificationAsymmetry.Collapse
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace VerificationAsymmetry

namespace Economy

open Finset

variable (E : Economy)

/-! ### Theorem~\ref{thm:aggregation} Part 2: Cobb-Douglas zero-product. -/

/-- **Theorem~\ref{thm:aggregation} Part 2 (Cobb-Douglas zero-product
    rule).** For the Cobb-Douglas aggregator
    `Y_agg = ∏ Y_i^{ω_i}` (limit `σ_a → 1`), if any factor `Y_i`
    is zero with positive weight `ω_i`, then `Y_agg = 0`.

    *Lean formalization.* The Cobb-Douglas aggregate
    `∏ Y_i^{ω_i}` is zero whenever some `Y_i = 0` and `ω_i > 0`,
    because `0^p = 0` for `p > 0` (the `Real.rpow` convention; see
    `Real.zero_rpow` for positive exponents). -/
theorem thm_aggregation_cobb_douglas_zero
    {ι : Type*} (s : Finset ι) (Y w : ι → ℝ)
    (i₀ : ι) (h_i₀_in : i₀ ∈ s)
    (h_Yi₀ : Y i₀ = 0) (h_wi₀ : 0 < w i₀) :
    ∏ i ∈ s, (Y i) ^ (w i) = 0 := by
  -- Find that the i₀ factor is 0 and use prod_eq_zero.
  apply Finset.prod_eq_zero h_i₀_in
  rw [h_Yi₀]
  exact Real.zero_rpow (ne_of_gt h_wi₀)

/-- **Theorem~\ref{thm:aggregation} Part 2 (corollary).** Under the
    Cobb-Douglas aggregator, if the apprenticeship pipeline of any
    profession collapses (`V_∞,i = 0`, hence `Y_i = 0` in the
    Leontief or Cobb-Douglas within-profession regime), the
    aggregate `Y_agg` collapses to zero. -/
theorem thm_aggregation_least_resilient_collapse
    {ι : Type*} (s : Finset ι) (Y w : ι → ℝ)
    (h_w_pos : ∀ i ∈ s, 0 < w i)
    (h_collapse : ∃ i₀ ∈ s, Y i₀ = 0) :
    ∏ i ∈ s, (Y i) ^ (w i) = 0 := by
  obtain ⟨i₀, h_i₀_in, h_Yi₀⟩ := h_collapse
  -- Direct call (this theorem is `Economy`-independent, no dot notation).
  exact thm_aggregation_cobb_douglas_zero s Y w i₀ h_i₀_in h_Yi₀
    (h_w_pos i₀ h_i₀_in)

/-! ### Theorem~\ref{thm:aggregation} Part 3: perfect-substitutes
    survival. -/

/-- **Theorem~\ref{thm:aggregation} Part 3 (perfect-substitutes
    survival).** Under the perfect-substitutes aggregator
    `Y_agg = Σ ω_i Y_i` (limit `σ_a → ∞`), the aggregate output
    is bounded below by `ω_j Y_j` for any single surviving
    profession `j` with `Y_j > 0`. -/
theorem thm_aggregation_perfect_substitutes_survival
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (Y w : ι → ℝ)
    (h_Y_nonneg : ∀ i ∈ s, 0 ≤ Y i)
    (h_w_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (j : ι) (h_j_in : j ∈ s) (h_Yj : 0 < Y j) (h_wj : 0 < w j) :
    0 < ∑ i ∈ s, w i * Y i := by
  -- The j-th term is strictly positive; all others non-negative;
  -- hence the sum is strictly positive.
  have h_j_term_pos : 0 < w j * Y j := mul_pos h_wj h_Yj
  have h_others_nonneg : ∀ i ∈ s, 0 ≤ w i * Y i := by
    intro i hi
    exact mul_nonneg (h_w_nonneg i hi) (h_Y_nonneg i hi)
  -- Split sum at j.
  rw [← Finset.sum_erase_add _ _ h_j_in]
  have h_erase_sum_nonneg : 0 ≤ ∑ i ∈ s.erase j, w i * Y i := by
    apply Finset.sum_nonneg
    intro i hi
    exact h_others_nonneg i (Finset.mem_of_mem_erase hi)
  linarith

/-- **Theorem~\ref{thm:aggregation} Part 3 (corollary).** In the
    perfect-substitutes limit, collapse of profession `i` (with
    `Y_i = 0`) leaves the aggregate at `∑_{j ≠ i} ω_j Y_j`,
    bounded below by any non-collapsed term. -/
theorem thm_aggregation_perfect_substitutes_residual
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (Y w : ι → ℝ)
    (i₀ : ι) (h_i₀_in : i₀ ∈ s) (h_Yi₀ : Y i₀ = 0) :
    ∑ i ∈ s, w i * Y i = ∑ i ∈ s.erase i₀, w i * Y i := by
  rw [← Finset.sum_erase_add _ _ h_i₀_in]
  rw [h_Yi₀]
  ring

/-! ### Theorem~\ref{thm:aggregation} Parts 1 + 4: Ledger-only
    `gapOpen` claims, not Lean-encoded.

  Parts 1 (sequential phase-transition kinks at the order statistics
  `θ*_(k)`) and 4 (intermediate-regime elasticity non-decreasing
  across transitions) are MATHEMATICAL claims about the CES
  aggregator's continuity / kink structure.  A faithful sound Lean
  STATEMENT of each requires Mathlib continuity / one-sided-limit /
  calculus infrastructure (kink detection across order statistics;
  differentiability of the CES aggregator) beyond this
  formalization's structural scope.  No Lean
  `axiom`/`def`/`theorem` declaration is provided: an `axiom` over a
  free `Yagg` / `aggElasticity` functional is unsound
  (`False`-injectable), and a `def : Prop` whose constraining
  predicate equals the asserted conclusion is vacuous (tautological).
  The honest encoding is the Ledger `GapEntry` records
  `gap_aggregation_sequential_kinks_OPEN` and
  `gap_aggregation_intermediate_regime_OPEN` (`Ledger.lean`): typed,
  `#eval`-retrievable records tracking each gap's status, paper
  source, and the reason it is not Lean-derived.  The Cobb-Douglas
  and perfect-substitutes limit cases (Parts 2 + 3 above) are the
  substantive structural content and ARE closed as `theorem`s. -/

/-! ### Proposition~\ref{prop:adjustment-margins}: career extension. -/

/-- **Proposition~\ref{prop:adjustment-margins} (career-extension
    bound).** The extension-adjusted collapse threshold is
    `θ*_ext = 1 - τ*/T` (replacing `T_j` by the full lifetime `T`
    as the maximum possible junior career length).  This exceeds
    `θ* = 1 - τ*/T_j` strictly when `T_j < T`. -/
noncomputable def thetaStarExt : ℝ := 1 - E.tauStar / E.T

/-- **Proposition~\ref{prop:adjustment-margins} (career-extension
    inequality).** `θ* < θ*_ext` strictly. -/
theorem prop_adjustment_career_extension_strict :
    E.thetaStar < E.thetaStarExt := by
  unfold thetaStar thetaStarExt
  -- 1 - τ*/T_j < 1 - τ*/T  ↔  τ*/T < τ*/T_j.
  have hT_pos : 0 < E.T := by linarith [E.Tj_pos, E.Tj_lt_T]
  have hTj_pos : 0 < E.Tj := E.Tj_pos
  have hτ_pos : 0 < E.tauStar := E.tauStar_pos
  have hTj_lt_T : E.Tj < E.T := E.Tj_lt_T
  have hdiv_lt : E.tauStar / E.T < E.tauStar / E.Tj :=
    div_lt_div_of_pos_left hτ_pos hTj_pos hTj_lt_T
  linarith

/-- **Proposition~\ref{prop:adjustment-margins} (career-extension
    cannot eliminate).** `θ*_ext < 1` strictly (extension cannot
    push the threshold to `1` because `τ* > 0` keeps the bound
    bounded away from `1`). -/
theorem prop_adjustment_career_extension_bounded :
    E.thetaStarExt < 1 := by
  unfold thetaStarExt
  have hT_pos : 0 < E.T := by linarith [E.Tj_pos, E.Tj_lt_T]
  have hτ_pos : 0 < E.tauStar := E.tauStar_pos
  have : 0 < E.tauStar / E.T := div_pos hτ_pos hT_pos
  linarith

/-! ### Proposition~\ref{prop:adjustment-margins}: narrative portion
    (threshold reduction + endogenous AI verification).

  The narrative portion of Proposition~\ref{prop:adjustment-margins}
  splits into two clauses with distinct resolution status:

  (i) **Threshold reduction** — for a profession-specific floor
      `τ*_min ∈ (0, τ*)`, the floored collapse threshold
      `1 - τ*_min/T_j` lies STRICTLY ABOVE `θ* = 1 - τ*/T_j`.  This
      is a real algebraic consequence of `0 < τ*_min < τ*`; it is
      proved below as the `theorem
      prop_adjustment_threshold_reduction_floor`.

  (ii) **Endogenous AI verification** — the substitution rate
       `δ(θ)` satisfies `δ(θ) < 1` uniformly because the
       non-codifiable residual (`def:verification`) keeps AI
       verification from fully substituting human verification.
       This is a substantive empirical claim whose resolution path
       is cohort-study evidence on AI substitution rates by career
       stage, not a Lean derivation.  No Lean
       `axiom`/`def`/`theorem` declaration is provided: an `axiom`
       over a free `delta` functional is unsound
       (`False`-injectable), and a `def : Prop` whose constraining
       predicate equals the asserted conclusion is vacuous
       (tautological).  The honest encoding is the Ledger `GapEntry`
       record `gap_prop_adjustment_narrative_OPEN` (`Ledger.lean`):
       a typed, `#eval`-retrievable record tracking the claim's
       status, paper source, and empirical resolution path. -/

/-- **Proposition~\ref{prop:adjustment-margins} clause (i)
    (threshold-reduction floor).** For a profession-specific
    threshold-reduction floor `τ*_min ∈ (0, τ*)`, the floored
    collapse threshold `1 - τ*_min/T_j` lies strictly above
    `θ* = 1 - τ*/T_j`: reducing the promotion threshold to its
    floor shifts the collapse threshold rightward but cannot
    eliminate the collapse.

    This is the derivable conjunct of the
    `\label{prop:adjustment-margins}` narrative — a real `theorem`,
    not an axiom.  The strict inequality follows from
    `tauStarMin < τ*` and `0 < T_j` alone; the paper states the
    floor as `τ*_min ∈ (0, τ*)`, so the lower bound `_h_floor_pos`
    (`0 < τ*_min`) is carried for paper-faithful signature parity
    but is `_`-prefixed to mark it not load-bearing for the
    conclusion. -/
theorem prop_adjustment_threshold_reduction_floor
    (tauStarMin : ℝ) (_h_floor_pos : 0 < tauStarMin)
    (h_floor_lt : tauStarMin < E.tauStar) :
    E.thetaStar < 1 - tauStarMin / E.Tj := by
  unfold thetaStar
  -- 1 - τ*/T_j < 1 - τ*_min/T_j  ↔  τ*_min/T_j < τ*/T_j.
  have hTj_pos : 0 < E.Tj := E.Tj_pos
  have hdiv_lt : tauStarMin / E.Tj < E.tauStar / E.Tj :=
    div_lt_div_of_pos_right h_floor_lt hTj_pos
  linarith

/-! ### Proposition~\ref{prop:adjustment-margins} clause (ii):
    endogenous-AI-verification residual bound — Ledger-only
    `gapOpen`, not Lean-encoded.

  Paper `\label{prop:adjustment-margins}` clause 3 asserts the
  uniform bound `δ(θ) < 1` on the endogenous-AI-verification
  residual substitution-rate function — the non-codifiable
  residual (`\label{def:verification}`) keeps AI verification from
  fully substituting human verification.  This is a substantive
  empirical claim whose resolution path is cohort-study evidence on
  AI substitution rates by career stage, not a Lean derivation.  No
  Lean `axiom`/`def`/`theorem` declaration is provided: an `axiom`
  over a free `delta` functional is unsound (`False`-injectable),
  and a `def : Prop` whose constraining predicate equals the
  asserted conclusion is vacuous (tautological).  The honest
  encoding is the Ledger `GapEntry` record
  `gap_prop_adjustment_narrative_OPEN` (`Ledger.lean`).  The
  derivable threshold-reduction conjunct of the narrative is the
  `theorem prop_adjustment_threshold_reduction_floor` above. -/

end Economy

end VerificationAsymmetry
