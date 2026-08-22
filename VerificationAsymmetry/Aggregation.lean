/-
  VerificationAsymmetry/Aggregation.lean

  Theorem~\ref{thm:aggregation} (Output Aggregation Across
  Professions) and Proposition~\ref{prop:adjustment-margins}
  (Adjustment Margins).

  Companion to: "Verification Asymmetry under AI Substitution:
  Wage-Ratio Inversion and Apprenticeship Thresholds" (Li, 2026).

  Statement.

    Cross-profession CES aggregator with elasticity σ_a > 0,
    weights ω_i > 0 summing to 1.  Each Y_i depends on θ via
    its profession-specific apprenticeship dynamics.

    Part 2.  Exact Cobb-Douglas aggregation (σ_a = 1): if any Y_i = 0
              with ω_i > 0, then Y_agg = 0.  This zero-propagation
              result is specific to the exact Cobb-Douglas endpoint;
              it is not asserted for every finite σ_a > 1.

    Part 3.  Perfect-substitutes endpoint (σ_a = ∞):
              Y_agg = Σ ω_i Y_i.  Collapse of one profession leaves
              Y_agg = Σ_{j ≠ i} ω_j Y_j > 0.

    Part 4.  Near-Cobb-Douglas limit from above: after at least one
              positive-weight component is zero and at least one survives,
              every fixed σ_a > 1 gives positive output, but that residual
              tends to zero as σ_a ↓ 1.

  Lean strategy.  Parts 2 and 3 are the substantive mathematical
  content.  Both are statements about real-valued products and sums
  over finite index sets; we formalize the structural mathematics
  (Cobb-Douglas zero-product, perfect-substitutes positive-sum)
  using Finset machinery.

  The current Proposition 14 variable-exponent finite-sum limit is fully
  Lean-closed below.  Historical longer-model claims about sequential
  profession-specific kinks and an intermediate-regime elasticity remain
  Ledger-only because they are omitted from the current journal paper.
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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace VerificationAsymmetry

namespace Economy

open Finset Filter Set
open scoped Topology BigOperators

variable (E : Economy)

/-! ### Theorem~\ref{thm:aggregation} Part 2: Cobb-Douglas zero-product. -/

/-- **Theorem~\ref{thm:aggregation} Part 2 (Cobb-Douglas zero-product
    rule).** For the Cobb-Douglas aggregator
    `Y_agg = ∏ Y_i^{ω_i}` (the exact `σ_a = 1` case), if any factor `Y_i`
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

/-! ### Current Proposition~\ref{prop:aggregation}: finite-CES positivity and
    the near-Cobb--Douglas limit from above. -/

/-- Inner CES sum in the paper's `q=(sigma-1)/sigma` parametrization. -/
noncomputable def cesInner {ι : Type*} (s : Finset ι)
    (Y w : ι → ℝ) (q : ℝ) : ℝ :=
  ∑ i ∈ s, w i * (Y i) ^ q

/-- Total weight of the strictly positive-output components. -/
noncomputable def positiveComponentWeight {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (Y w : ι → ℝ) : ℝ :=
  ∑ i ∈ s.filter (fun i => Y i ≠ 0), w i

/-- As `q ↓ 0`, each positive component contributes its weight and each zero
    component contributes zero, so the inner sum tends to the surviving weight. -/
theorem cesInner_tendsto_positiveComponentWeight
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (Y w : ι → ℝ) :
    Tendsto (cesInner s Y w) (nhdsWithin 0 (Ioi 0))
      (𝓝 (positiveComponentWeight s Y w)) := by
  have hsum : Tendsto (fun q : ℝ => ∑ i ∈ s, w i * (Y i) ^ q)
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (∑ i ∈ s, if Y i = 0 then 0 else w i)) := by
    apply tendsto_finsetSum
    intro i hi
    by_cases hYi : Y i = 0
    · have hev : (fun q : ℝ => w i * (Y i) ^ q) =ᶠ[nhdsWithin 0 (Ioi 0)]
          (fun _ => 0) := by
        filter_upwards [self_mem_nhdsWithin] with q hq
        rw [hYi, Real.zero_rpow (ne_of_gt hq)]
        ring
      simpa [hYi] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ))
          (nhdsWithin 0 (Ioi 0)) (𝓝 0)).congr' hev.symm)
    · have hy_full : Tendsto (fun q : ℝ => (Y i) ^ q) (𝓝 0) (𝓝 1) := by
        simpa using (Real.continuousAt_const_rpow hYi :
          ContinuousAt (fun q : ℝ => (Y i) ^ q) 0).tendsto
      have hy : Tendsto (fun q : ℝ => (Y i) ^ q)
          (nhdsWithin 0 (Ioi 0)) (𝓝 1) :=
        hy_full.mono_left inf_le_left
      simpa [hYi] using tendsto_const_nhds.mul hy
  simpa [cesInner, positiveComponentWeight, Finset.sum_filter] using hsum

/-- With positive weights summing to one, at least one collapsed component and
    at least one surviving component make the surviving weight lie in `(0,1)`. -/
theorem positiveComponentWeight_mem_unit
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (Y w : ι → ℝ)
    (hw_pos : ∀ i ∈ s, 0 < w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (hzero : ∃ i ∈ s, Y i = 0)
    (hsurvive : ∃ i ∈ s, 0 < Y i) :
    0 < positiveComponentWeight s Y w ∧
      positiveComponentWeight s Y w < 1 := by
  constructor
  · unfold positiveComponentWeight
    apply Finset.sum_pos'
    · intro i hi
      exact (hw_pos i (Finset.mem_filter.mp hi).1).le
    · obtain ⟨j, hjs, hYj⟩ := hsurvive
      exact ⟨j, Finset.mem_filter.2 ⟨hjs, ne_of_gt hYj⟩, hw_pos j hjs⟩
  · obtain ⟨i0, hi0s, hYi0⟩ := hzero
    have hcomp_pos :
        0 < ∑ i ∈ s.filter (fun i => ¬ Y i ≠ 0), w i := by
      apply Finset.sum_pos'
      · intro i hi
        exact (hw_pos i (Finset.mem_filter.mp hi).1).le
      · exact ⟨i0, Finset.mem_filter.2 ⟨hi0s, by simp [hYi0]⟩,
          hw_pos i0 hi0s⟩
    have hdecomp := Finset.sum_filter_add_sum_filter_not s (fun i => Y i ≠ 0) w
    unfold positiveComponentWeight
    rw [hw_sum] at hdecomp
    linarith

/-- CES aggregate in the paper's positive `q` parametrization. -/
noncomputable def aggregateCESQ {ι : Type*} (s : Finset ι)
    (Y w : ι → ℝ) (q : ℝ) : ℝ :=
  (cesInner s Y w q) ^ (1 / q)

/-- Every fixed positive `q` (equivalently every fixed `sigma>1`) preserves
    positive aggregate output when at least one positive-weight component
    survives. -/
theorem aggregateCESQ_pos
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (Y w : ι → ℝ) {q : ℝ}
    (_hq : 0 < q) (hY_nonneg : ∀ i ∈ s, 0 ≤ Y i)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hsurvive : ∃ j ∈ s, 0 < Y j ∧ 0 < w j) :
    0 < aggregateCESQ s Y w q := by
  obtain ⟨j, hjs, hYj, hwj⟩ := hsurvive
  have hinner : 0 < cesInner s Y w q := by
    unfold cesInner
    apply Finset.sum_pos'
    · intro i hi
      exact mul_nonneg (hw_nonneg i hi) (Real.rpow_nonneg (hY_nonneg i hi) q)
    · refine ⟨j, hjs, ?_⟩
      exact mul_pos hwj (Real.rpow_pos_of_pos hYj q)
  unfold aggregateCESQ
  exact Real.rpow_pos_of_pos hinner _

/-- Paper Proposition 14, `q`-form of the near-Cobb--Douglas limit:
    the positive CES residual tends to zero as `q ↓ 0`. -/
theorem aggregateCESQ_tendsto_zero
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (Y w : ι → ℝ)
    (hY_nonneg : ∀ i ∈ s, 0 ≤ Y i)
    (hw_pos : ∀ i ∈ s, 0 < w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (hzero : ∃ i ∈ s, Y i = 0)
    (hsurvive : ∃ i ∈ s, 0 < Y i) :
    Tendsto (aggregateCESQ s Y w) (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  let p := positiveComponentWeight s Y w
  obtain ⟨hp_pos, hp_lt_one⟩ :=
    positiveComponentWeight_mem_unit s Y w hw_pos hw_sum hzero hsurvive
  let c : ℝ := (p + 1) / 2
  have hpc : p < c := by dsimp [c]; linarith
  have hc_one : c < 1 := by dsimp [c]; linarith
  have hc_neg_one : -1 < c := by dsimp [c]; linarith
  have hinner_limit : Tendsto (cesInner s Y w)
      (nhdsWithin 0 (Ioi 0)) (𝓝 p) :=
    cesInner_tendsto_positiveComponentWeight s Y w
  have hinner_lt : ∀ᶠ q in nhdsWithin 0 (Ioi 0), cesInner s Y w q < c :=
    (tendsto_order.1 hinner_limit).2 c hpc
  have hupper : Tendsto (fun q : ℝ => c ^ (1 / q))
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    have h := (tendsto_rpow_atTop_of_base_lt_one c hc_neg_one hc_one).comp
      (tendsto_inv_nhdsGT_zero :
        Tendsto (fun q : ℝ => q⁻¹) (nhdsWithin 0 (Ioi 0)) atTop)
    simpa [one_div] using h
  apply squeeze_zero'
  · filter_upwards with q
    unfold aggregateCESQ
    exact Real.rpow_nonneg (by
      unfold cesInner
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (hw_pos i hi).le
        (Real.rpow_nonneg (hY_nonneg i hi) q)) _
  · filter_upwards [hinner_lt, self_mem_nhdsWithin] with q hqc hq
    unfold aggregateCESQ
    apply Real.rpow_le_rpow
    · unfold cesInner
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (hw_pos i hi).le
        (Real.rpow_nonneg (hY_nonneg i hi) q)
    · exact hqc.le
    · exact (one_div_pos.mpr hq).le
  · exact hupper

/-- Paper exponent `q=(sigma-1)/sigma`. -/
noncomputable def aggregationQ (sigma : ℝ) : ℝ := (sigma - 1) / sigma

theorem aggregationQ_pos {sigma : ℝ} (h : 1 < sigma) :
    0 < aggregationQ sigma := by
  unfold aggregationQ
  exact div_pos (by linarith) (by linarith)

/-- `sigma ↓ 1` maps to `q ↓ 0`. -/
theorem aggregationQ_tendsto_zero :
    Tendsto aggregationQ (nhdsWithin 1 (Ioi 1)) (nhdsWithin 0 (Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hnum : Tendsto (fun sigma : ℝ => sigma - 1) (𝓝 1) (𝓝 0) := by
      have hid : Tendsto (fun sigma : ℝ => sigma) (𝓝 1) (𝓝 1) := tendsto_id
      simpa using hid.sub_const (1 : ℝ)
    have hden : Tendsto (fun sigma : ℝ => sigma) (𝓝 1) (𝓝 1) := tendsto_id
    have hdiv := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
    have hfull : Tendsto aggregationQ (𝓝 1) (𝓝 0) := by
      simpa [aggregationQ] using hdiv
    exact hfull.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    exact aggregationQ_pos hsigma

/-- CES aggregate in the paper's elasticity parameter `sigma`. -/
noncomputable def aggregateCES {ι : Type*} (s : Finset ι)
    (Y w : ι → ℝ) (sigma : ℝ) : ℝ :=
  aggregateCESQ s Y w (aggregationQ sigma)

/-- Paper Proposition 14 Part 2: every fixed `sigma>1` gives positive output. -/
theorem prop_aggregation_fixed_sigma_positive
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (Y w : ι → ℝ) {sigma : ℝ}
    (hsigma : 1 < sigma) (hY_nonneg : ∀ i ∈ s, 0 ≤ Y i)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hsurvive : ∃ j ∈ s, 0 < Y j ∧ 0 < w j) :
    0 < aggregateCES s Y w sigma := by
  unfold aggregateCES
  exact aggregateCESQ_pos s Y w (aggregationQ_pos hsigma)
    hY_nonneg hw_nonneg hsurvive

/-- Paper Proposition 14 Part 3: the positive residual converges to zero as
    `sigma ↓ 1`. -/
theorem prop_aggregation_near_cobb_douglas_limit
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (Y w : ι → ℝ)
    (hY_nonneg : ∀ i ∈ s, 0 ≤ Y i)
    (hw_pos : ∀ i ∈ s, 0 < w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (hzero : ∃ i ∈ s, Y i = 0)
    (hsurvive : ∃ i ∈ s, 0 < Y i) :
    Tendsto (aggregateCES s Y w) (nhdsWithin 1 (Ioi 1)) (𝓝 0) := by
  unfold aggregateCES
  exact (aggregateCESQ_tendsto_zero s Y w hY_nonneg hw_pos hw_sum
    hzero hsurvive).comp aggregationQ_tendsto_zero

/-! ### Theorem~\ref{thm:aggregation} Parts 1 + 4 + 5: Ledger-only
    non-closed claims, not Lean-encoded.

  Parts 1 (sequential phase-transition kinks at the order statistics
  `θ*_(k)`), 4 (the near-Cobb-Douglas variable-exponent finite-sum
  limit), and 5 (intermediate-regime elasticity non-decreasing across
  transitions) are MATHEMATICAL claims about the CES aggregator's
  continuity / limit / kink structure.  A faithful sound Lean
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
  `gap_aggregation_intermediate_regime_OPEN`.  The current paper's
  near-Cobb--Douglas limit is tracked by
  `gap_prop_aggregation_near_cd_limit_CLOSED` (`Ledger.lean`): typed,
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

  (ii) **Endogenous AI verification** — a residual floor may be stated
       only after imposing an explicit `ε > 0` with `δ(θ) ≤ 1-ε`.
       Such a floor does not follow from the verbal verification
       definition alone.  It is a substantive empirical premise whose resolution path
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

  Paper `\label{prop:adjustment-margins}` now treats the endogenous-AI-
  verification floor as conditional on an explicit quantitative
  premise `δ(θ) ≤ 1-ε` for some `ε>0`; it is not implied by
  `\label{def:verification}`.  Establishing such a floor is a substantive
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
