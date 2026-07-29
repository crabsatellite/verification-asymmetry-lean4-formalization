/-
  VerificationAsymmetry/Recursive.lean

  Theorem~\ref{thm:recursive} (Verification-Pressure Reduced Form) and
  Proposition~\ref{prop:boundary} (Technological Reachability Boundary).

  Companion to: "Verification Asymmetry under AI Substitution:
  Wage-Ratio Inversion and Apprenticeship Thresholds" (Li, 2026).

  Statement.

    The paper DECLARES a reduced-form verification-pressure index in
    which AI output receives weight `μ ≥ 1` and human output weight 1:
        V_req(θ) = (1-θ) L_G + μ θ K_AI.

    Part 1.  When `L_G < G*(r̄) < μ K_AI`, the recursive crossing
              is reachable in `(0,1)` and has closed form
        θ_inv^{rec}(r̄) = (G*(r̄) - L_G) / (μ K_AI - L_G),
        while, when the baseline crossing is also reachable,
        θ_inv^{rec}/θ_inv = (K_AI - L_G)/(μ K_AI - L_G),
        which approaches 1/μ as K_AI → ∞.

    Part 2.  Wedge amplification:
        W_E^{rec}(θ) / W_E(θ) = (V_req(θ)/G(θ))^{1-ρ}
                              → μ^{1-ρ} as K_AI → ∞.

    Part 3.  Conditional log-slope acceleration inside the declared
              reduced form:
        ∂θ log r_μ - ∂θ log r_1
          = (1-ρ)(μ-1)L_G K_AI / (V_req G) > 0.

    Part 4.  Pipeline-collapse threshold θ* unchanged by μ
              (cohort dynamics depend on supply side, not
              recursive-verification demand side).

    Part 5.  Pointwise amplification is bounded between 1 and
              μ^{1-ρ}; the upper endpoint is attained at θ = 1.

  Lean strategy.  The algebraic parts are real-arithmetic consequences
  of the DECLARED `V_req` and `wageRatioRec` reduced forms; Lean does
  not derive those forms from the baseline CES technology.  Part 3 is a definitional
  observation (recursion-θ* invariance is by-construction since
  μ does not appear in `Vinf` / `eBar`).
-/

import VerificationAsymmetry.Basic
import VerificationAsymmetry.Collapse
import VerificationAsymmetry.Inversion

namespace VerificationAsymmetry

namespace Economy

variable (E : Economy)

/-! ### Declared verification-pressure index `V_req(θ)`. -/

/-- *Verification-pressure index* in the recursive reduced form:
    `V_req(θ) = (1-θ) L_G + μ θ K_AI`,
    paper Eq.~\eqref{eq:V-req-recursive}. -/
def Vreq (μ θ : ℝ) : ℝ := (1 - θ) * E.LG + μ * θ * E.KAI

@[simp] lemma Vreq_at_theta_zero (μ : ℝ) : E.Vreq μ 0 = E.LG := by
  simp [Vreq]

@[simp] lemma Vreq_at_theta_one (μ : ℝ) : E.Vreq μ 1 = μ * E.KAI := by
  unfold Vreq; ring

/-- `V_req(θ) = G(θ)` when `μ = 1` (recovery of baseline; recursive
    factor `μ = 1` collapses to plain `G`). -/
theorem Vreq_at_mu_one (θ : ℝ) : E.Vreq 1 θ = E.G θ := by
  unfold Vreq G; ring

/-- For `μ ≥ 1` and a feasible substitution share, the declared pressure
    ratio lies in `[1, μ]`.  This is the exact finite-capacity bound used
    by the paper. -/
theorem Vreq_ratio_bounds
    (μ θ : ℝ) (hμ : 1 ≤ μ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    1 ≤ E.Vreq μ θ / E.G θ ∧ E.Vreq μ θ / E.G θ ≤ μ := by
  have hG : 0 < E.G θ := E.G_pos hθ0 hθ1
  have hA : 0 ≤ (μ - 1) * θ * E.KAI :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hμ) hθ0) E.KAI_pos.le
  have hB : 0 ≤ (μ - 1) * (1 - θ) * E.LG :=
    mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hμ) (sub_nonneg.mpr hθ1)) E.LG_pos.le
  have hLower : E.G θ ≤ E.Vreq μ θ := by
    unfold G Vreq
    nlinarith
  have hUpper : E.Vreq μ θ ≤ μ * E.G θ := by
    unfold G Vreq
    nlinarith
  constructor
  · apply (le_div_iff₀ hG).2
    simpa using hLower
  · exact (div_le_iff₀ hG).2 hUpper

/-! ### Recursive inversion threshold. -/

/-- *Recursive inversion threshold* `θ_inv^{rec}(r̄) :=
    (G*(r̄) - L_G) / (μ K_AI - L_G)`,
    paper Eq.~\eqref{eq:theta-inv-recursive}. -/
noncomputable def thetaInvRec (μ V rBar : ℝ) : ℝ :=
  (E.Gstar V rBar - E.LG) / (μ * E.KAI - E.LG)

/-- **Theorem~\ref{thm:recursive} Part 1 (closed-form reachable
    recursive threshold).** If `L_G < G*(r̄) < μ K_AI`, the recursive
    threshold solves `V_req(θ_inv^{rec}) = G*(r̄)`. -/
theorem thm_recursive_threshold_closed_form
    (μ V rBar : ℝ)
    (hLower : E.LG < E.Gstar V rBar)
    (hUpper : E.Gstar V rBar < μ * E.KAI) :
    E.Vreq μ (E.thetaInvRec μ V rBar) = E.Gstar V rBar := by
  unfold Vreq thetaInvRec
  have hne : μ * E.KAI - E.LG ≠ 0 := by
    have : 0 < μ * E.KAI - E.LG := by linarith
    exact ne_of_gt this
  field_simp
  ring

/-- **Theorem~\ref{thm:recursive} Part 1 (reachability).** The paper's
    endpoint conditions place the recursive closed form strictly inside
    the feasible share interval `(0,1)`. -/
theorem thm_recursive_threshold_in_unit
    (μ V rBar : ℝ)
    (hLower : E.LG < E.Gstar V rBar)
    (hUpper : E.Gstar V rBar < μ * E.KAI) :
    0 < E.thetaInvRec μ V rBar ∧ E.thetaInvRec μ V rBar < 1 := by
  unfold thetaInvRec
  have hNumer : 0 < E.Gstar V rBar - E.LG := by linarith
  have hDenom : 0 < μ * E.KAI - E.LG := by linarith
  constructor
  · exact div_pos hNumer hDenom
  · apply (div_lt_iff₀ hDenom).2
    linarith

/-- **Theorem~\ref{thm:recursive} Part 1 (ratio identity).** The
    ratio `θ_inv^{rec} / θ_inv = (K_AI - L_G)/(μ K_AI - L_G)`
    when both crossings are reachable. -/
theorem thm_recursive_threshold_ratio
    (μ V rBar : ℝ)
    (hLower : E.LG < E.Gstar V rBar)
    (hBaselineUpper : E.Gstar V rBar < E.KAI)
    (hRecursiveUpper : E.Gstar V rBar < μ * E.KAI) :
    E.thetaInvRec μ V rBar / E.thetaInv V rBar
      = (E.KAI - E.LG) / (μ * E.KAI - E.LG) := by
  unfold thetaInvRec thetaInv
  -- (G* - L_G)/(μ K_AI - L_G) / ((G* - L_G)/(K_AI - L_G))
  --   = (K_AI - L_G)/(μ K_AI - L_G).
  have hGstar_LG_ne : E.Gstar V rBar - E.LG ≠ 0 := by
    exact ne_of_gt (by linarith)
  have hKAI_LG_ne : E.KAI - E.LG ≠ 0 := by
    exact ne_of_gt (by linarith)
  have hμKAI_LG_ne : μ * E.KAI - E.LG ≠ 0 := by
    exact ne_of_gt (by linarith)
  field_simp

/-- **Theorem~\ref{thm:recursive} Part 1 (μ > 1 ⇒ leftward shift).**
    For `μ > 1`, when both crossings are reachable,
    `θ_inv^{rec} < θ_inv` strictly. -/
theorem thm_recursive_threshold_leftward
    (μ V rBar : ℝ) (hμ : 1 < μ)
    (hGstar_gt_LG : E.LG < E.Gstar V rBar)
    (hBaselineUpper : E.Gstar V rBar < E.KAI) :
    E.thetaInvRec μ V rBar < E.thetaInv V rBar := by
  unfold thetaInvRec thetaInv
  -- (G* - L_G) > 0 (from hGstar_gt_LG).
  -- We need (G* - L_G)/(μ K_AI - L_G) < (G* - L_G)/(K_AI - L_G).
  -- Both denominators positive (μ K_AI - L_G > K_AI - L_G > 0
  -- since μ > 1, K_AI > 0).
  have hKAI_pos : 0 < E.KAI := E.KAI_pos
  have hKAI_gt : E.LG < E.KAI := by linarith
  have hKAI_LG_pos : 0 < E.KAI - E.LG := by linarith
  have hμKAI_pos : E.KAI < μ * E.KAI := by
    have : 0 < E.KAI := hKAI_pos
    nlinarith
  have hμKAI_LG_pos : 0 < μ * E.KAI - E.LG := by linarith
  have hDenom_lt : E.KAI - E.LG < μ * E.KAI - E.LG := by linarith
  have hNumer_pos : 0 < E.Gstar V rBar - E.LG := by linarith
  -- a/x < a/y when 0 < a, 0 < y < x.
  exact div_lt_div_of_pos_left hNumer_pos hKAI_LG_pos hDenom_lt

/-! ### Theorem~\ref{thm:recursive} Part 3: pipeline-collapse invariance.

  Per paper `\label{thm:recursive}` Part 3, the maintained cohort experience
  accumulation rate `1-θ` is invariant in `μ`: recursive verification
  operates on the demand side (`Vreq`), not the supply side (`eBar`,
  `Vinf`).  Hence `ē(θ) = (1-θ) T_j` is independent of `μ`, and so
  is `θ* = 1 - τ*/T_j`.

  This invariance is satisfied by construction in this Lean
  formalization: the carriers `thetaStar`, `eBar`, `VinfHard` are
  all defined without any `μ` argument, so there is no μ-dependent
  quantity to prove invariant in the first place.  This is a
  definitional separation built into the model, not a derived
  robustness result; no Lean theorem is needed.

  See `gap_thm_recursive_invariance_DEFINITIONAL` in `Ledger.lean`
  for the canonical record. -/

/-! ### Theorem~\ref{thm:recursive} Part 2 + 4: wedge amplification. -/

/-- *Declared recursive wage-ratio schedule* (analogous to `wageRatio`):
    `w_V/w_G in the recursive reduced form = ((1-η)/η) λ^ρ
    (V_req(θ)/V)^{1-ρ}`. -/
noncomputable def wageRatioRec (μ V θ : ℝ) : ℝ :=
  ((1 - E.eta) / E.eta) * E.lam ^ E.rho * (E.Vreq μ θ / V) ^ (1 - E.rho)

/-- **Theorem~\ref{thm:recursive} Part 2 + 4 (amplification ratio).**
    The ratio `w_V^{rec}/w_V (baseline) = (V_req/G)^{1-ρ}`. -/
theorem thm_recursive_wage_ratio_amplification
    (μ V θ : ℝ) (hV_pos : 0 < V) (hG_pos : 0 < E.G θ)
    (hVreq_pos : 0 < E.Vreq μ θ) :
    E.wageRatioRec μ V θ / E.wageRatio V θ
      = (E.Vreq μ θ / E.G θ) ^ (1 - E.rho) := by
  unfold wageRatioRec wageRatio
  -- Strategy: cancel the prefactor `((1-η)/η · λ^ρ)`, then simplify
  -- `(V_req/V)^(1-ρ) / (G/V)^(1-ρ) = (V_req/G)^(1-ρ)`.
  have hPrefactor_pos :
      0 < ((1 - E.eta) / E.eta) * E.lam ^ E.rho := by
    apply mul_pos
    · exact div_pos (by linarith [E.eta_lt_one]) E.eta_pos
    · exact Real.rpow_pos_of_pos E.lam_pos _
  have hPrefactor_ne : ((1 - E.eta) / E.eta) * E.lam ^ E.rho ≠ 0 :=
    ne_of_gt hPrefactor_pos
  have hGV_pos : 0 < E.G θ / V := div_pos hG_pos hV_pos
  have hVreqV_pos : 0 < E.Vreq μ θ / V := div_pos hVreq_pos hV_pos
  have hGV_pow_pos :
      0 < (E.G θ / V) ^ (1 - E.rho) := Real.rpow_pos_of_pos hGV_pos _
  have hGV_pow_ne :
      (E.G θ / V) ^ (1 - E.rho) ≠ 0 := ne_of_gt hGV_pow_pos
  have hV_ne : V ≠ 0 := ne_of_gt hV_pos
  have hG_ne : E.G θ ≠ 0 := ne_of_gt hG_pos
  -- Cancel the prefactor: a*b / (a*c) = b/c when a ≠ 0.
  rw [mul_div_mul_left _ _ hPrefactor_ne]
  -- Now: (V_req/V)^(1-ρ) / (G/V)^(1-ρ) = (V_req/G)^(1-ρ).
  rw [← Real.div_rpow hVreqV_pos.le hGV_pos.le]
  -- Now: ((V_req/V) / (G/V))^(1-ρ) = (V_req/G)^(1-ρ).
  -- The inner ratio: (V_req/V) / (G/V) = V_req/V * V/G = V_req/G.
  have hInnerEq : E.Vreq μ θ / V / (E.G θ / V) = E.Vreq μ θ / E.G θ := by
    field_simp
  rw [hInnerEq]

/-- The amplification factor generated by the declared reduced form is
    pointwise bounded by `1` and `μ^(1-ρ)` for feasible `θ` and `μ ≥ 1`. -/
theorem thm_recursive_amplification_bounds
    (μ θ : ℝ) (hμ : 1 ≤ μ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    1 ≤ (E.Vreq μ θ / E.G θ) ^ (1 - E.rho) ∧
      (E.Vreq μ θ / E.G θ) ^ (1 - E.rho) ≤ μ ^ (1 - E.rho) := by
  have hratio := E.Vreq_ratio_bounds μ θ hμ hθ0 hθ1
  have hexp : 0 ≤ 1 - E.rho := by linarith [E.rho_le_one]
  constructor
  · simpa using Real.rpow_le_rpow (show (0 : ℝ) ≤ 1 by norm_num) hratio.1 hexp
  · exact Real.rpow_le_rpow (by linarith [hratio.1]) hratio.2 hexp

/-! ### Theorem~\ref{thm:recursive} Part 3: conditional log-slope
    acceleration. -/

/-- **Theorem~\ref{thm:recursive} Part 3 (log-slope difference,
    algebraic core).** Direct differentiation of the declared schedules gives
    the two log-slope forms on the left.  Their difference simplifies exactly
    to the expression on the right.

    This theorem machine-checks that simplification.  It remains conditional
    on the paper's declared `wageRatioRec` reduced form; it does not derive that
    schedule from a constrained-production problem. -/
theorem thm_recursive_log_slope_difference
    (μ θ : ℝ) (hμ : 1 ≤ μ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - E.rho) * (μ * E.KAI - E.LG) / E.Vreq μ θ
        - (1 - E.rho) * (E.KAI - E.LG) / E.G θ
      = (1 - E.rho) * (μ - 1) * E.LG * E.KAI /
          (E.Vreq μ θ * E.G θ) := by
  have hG_pos : 0 < E.G θ := E.G_pos hθ0 hθ1
  have hratio := E.Vreq_ratio_bounds μ θ hμ hθ0 hθ1
  have hVreq_pos : 0 < E.Vreq μ θ := by
    have hVG : E.G θ ≤ E.Vreq μ θ := by
      simpa using (le_div_iff₀ hG_pos).mp hratio.1
    linarith
  have hG_ne : E.G θ ≠ 0 := ne_of_gt hG_pos
  have hVreq_ne : E.Vreq μ θ ≠ 0 := ne_of_gt hVreq_pos
  field_simp
  unfold Vreq G
  ring

/-- **Theorem~\ref{thm:recursive} Part 3 (strict acceleration).**
    For `μ > 1` and `ρ < 1`, the exact log-slope difference from
    `thm_recursive_log_slope_difference` is strictly positive.  This is an
    additive comparison, not a claim that derivatives have the constant ratio
    `μ^(1-ρ)`. -/
theorem thm_recursive_log_slope_acceleration
    (μ θ : ℝ) (hμ : 1 < μ) (hρ : E.rho < 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    0 < (1 - E.rho) * (μ * E.KAI - E.LG) / E.Vreq μ θ
        - (1 - E.rho) * (E.KAI - E.LG) / E.G θ := by
  rw [E.thm_recursive_log_slope_difference μ θ hμ.le hθ0 hθ1]
  have hG_pos : 0 < E.G θ := E.G_pos hθ0 hθ1
  have hratio := E.Vreq_ratio_bounds μ θ hμ.le hθ0 hθ1
  have hVreq_pos : 0 < E.Vreq μ θ := by
    have hVG : E.G θ ≤ E.Vreq μ θ := by
      simpa using (le_div_iff₀ hG_pos).mp hratio.1
    linarith
  have hnum_pos :
      0 < (1 - E.rho) * (μ - 1) * E.LG * E.KAI := by
    have hρpos : 0 < 1 - E.rho := sub_pos.mpr hρ
    have hμpos : 0 < μ - 1 := sub_pos.mpr hμ
    exact mul_pos (mul_pos (mul_pos hρpos hμpos) E.LG_pos) E.KAI_pos
  exact div_pos hnum_pos (mul_pos hVreq_pos hG_pos)

/-! ### Proposition~\ref{prop:boundary}: technological reachability. -/

/-- **Proposition~\ref{prop:boundary} (reachability condition).**
    A profession with bundling share `ζ_V ∈ [0, 1]` admits SOME
    technologically feasible substitution share above the collapse
    threshold iff `ζ_V < τ*/T_j`, equivalently
    `1 - ζ_V > θ* = 1 - τ*/T_j`.  It does not assert that an
    equilibrium or observed path reaches that share.

    *Formal content:* the equivalence
    `(1 - ζ_V > θ*) ↔ (ζ_V < τ*/T_j)`. -/
theorem prop_boundary_collapse_iff (zetaV : ℝ) :
    (1 - zetaV > E.thetaStar) ↔ (zetaV < E.tauStar / E.Tj) := by
  unfold thetaStar
  constructor
  · intro h
    -- 1 - ζ_V > 1 - τ*/T_j  ↔  ζ_V < τ*/T_j.
    linarith
  · intro h
    linarith

end Economy

end VerificationAsymmetry
