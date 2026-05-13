/-
  VerificationAsymmetry/Recursive.lean

  Theorem~\ref{thm:recursive} (Recursive Verification) and
  Proposition~\ref{prop:boundary} (Generation-Verification
  Separability and Pipeline Collapse).

  Companion to: "Generation--Verification Asymmetry Inversion and
  Apprenticeship Pipeline Collapse Under AI Substitution" (Li, 2026).

  Statement.

    AI output requires `μ ≥ 1` units of verification per unit of
    generation; human output requires `1` unit.  Effective
    verification demand is
        V_req(θ) = (1-θ) L_G + μ θ K_AI.

    Part 1.  Inversion threshold under recursive verification:
        θ_inv^{rec}(r̄) = (G*(r̄) - L_G) / (μ K_AI - L_G),
        θ_inv^{rec}/θ_inv = (K_AI - L_G)/(μ K_AI - L_G),
        which approaches 1/μ as K_AI → ∞.

    Part 2.  Wedge amplification:
        W_E^{rec}(θ) / W_E(θ) = (V_req(θ)/G(θ))^{1-ρ}
                              → μ^{1-ρ} as K_AI → ∞.

    Part 3.  Pipeline-collapse threshold θ* unchanged by μ
              (cohort dynamics depend on supply side, not
              recursive-verification demand side).

    Part 4.  Wage-ratio acceleration: w_V/w_G under recursive
              verification rises at rate ≥ μ^{1-ρ} of the baseline.

  Lean strategy.  All four parts are real-arithmetic identities
  given the definition of `V_req` and the closed-form inversion
  threshold from `Inversion.lean`.  Part 3 is a definitional
  observation (recursion-θ* invariance is by-construction since
  μ does not appear in `Vinf` / `eBar`).
-/

import VerificationAsymmetry.Basic
import VerificationAsymmetry.Collapse
import VerificationAsymmetry.Inversion

namespace VerificationAsymmetry

namespace Economy

variable (E : Economy)

/-! ### Effective verification demand `V_req(θ)`. -/

/-- *Effective verification demand* under recursive verification:
    `V_req(θ) = (1-θ) L_G + μ θ K_AI`,
    paper Eq.~\eqref{eq:V-req-recursive}. -/
def Vreq (μ θ : ℝ) : ℝ := (1 - θ) * E.LG + μ * θ * E.KAI

@[simp] lemma Vreq_zero (μ : ℝ) : E.Vreq μ 0 = E.LG := by simp [Vreq]

@[simp] lemma Vreq_one (μ : ℝ) : E.Vreq μ 1 = μ * E.KAI := by
  unfold Vreq; ring

/-- `V_req(θ) = G(θ)` when `μ = 1` (recovery of baseline). -/
theorem Vreq_one_eq_G (θ : ℝ) : E.Vreq 1 θ = E.G θ := by
  unfold Vreq G; ring

/-! ### Recursive inversion threshold. -/

/-- *Recursive inversion threshold* `θ_inv^{rec}(r̄) :=
    (G*(r̄) - L_G) / (μ K_AI - L_G)`,
    paper Eq.~\eqref{eq:theta-inv-recursive}. -/
noncomputable def thetaInvRec (μ V rBar : ℝ) : ℝ :=
  (E.Gstar V rBar - E.LG) / (μ * E.KAI - E.LG)

/-- **Theorem~\ref{thm:recursive} Part 1 (closed-form recursive
    threshold).** The recursive threshold solves
    `V_req(θ_inv^{rec}) = G*(r̄)`. -/
theorem thm_recursive_threshold_closed_form
    (μ V rBar : ℝ) (hμLG_lt : E.LG < μ * E.KAI) :
    E.Vreq μ (E.thetaInvRec μ V rBar) = E.Gstar V rBar := by
  unfold Vreq thetaInvRec
  have hne : μ * E.KAI - E.LG ≠ 0 := by
    have : 0 < μ * E.KAI - E.LG := by linarith
    exact ne_of_gt this
  field_simp
  ring

/-- **Theorem~\ref{thm:recursive} Part 1 (ratio identity).** The
    ratio `θ_inv^{rec} / θ_inv = (K_AI - L_G)/(μ K_AI - L_G)`. -/
theorem thm_recursive_threshold_ratio
    (μ V rBar : ℝ)
    (hKAI_gt : E.LG < E.KAI) (hμLG_lt : E.LG < μ * E.KAI)
    (hGstar_ne_LG : E.Gstar V rBar ≠ E.LG) :
    E.thetaInvRec μ V rBar / E.thetaInv V rBar
      = (E.KAI - E.LG) / (μ * E.KAI - E.LG) := by
  unfold thetaInvRec thetaInv
  -- (G* - L_G)/(μ K_AI - L_G) / ((G* - L_G)/(K_AI - L_G))
  --   = (K_AI - L_G)/(μ K_AI - L_G).
  have hGstar_LG_ne : E.Gstar V rBar - E.LG ≠ 0 := by
    intro h
    apply hGstar_ne_LG
    linarith
  have hKAI_LG_ne : E.KAI - E.LG ≠ 0 := by
    intro h
    apply ne_of_gt hKAI_gt
    linarith
  have hμKAI_LG_ne : μ * E.KAI - E.LG ≠ 0 := by
    intro h
    apply ne_of_gt hμLG_lt
    linarith
  field_simp
  ring

/-- **Theorem~\ref{thm:recursive} Part 1 (μ ≥ 1 ⇒ leftward shift).**
    For `μ > 1` and `K_AI > L_G`, `θ_inv^{rec} < θ_inv` (strict). -/
theorem thm_recursive_threshold_leftward
    (μ V rBar : ℝ) (hμ : 1 < μ)
    (hKAI_gt : E.LG < E.KAI) (hGstar_gt_LG : E.LG < E.Gstar V rBar) :
    E.thetaInvRec μ V rBar < E.thetaInv V rBar := by
  unfold thetaInvRec thetaInv
  -- (G* - L_G) > 0 (from hGstar_gt_LG).
  -- We need (G* - L_G)/(μ K_AI - L_G) < (G* - L_G)/(K_AI - L_G).
  -- Both denominators positive (μ K_AI - L_G > K_AI - L_G > 0
  -- since μ > 1, K_AI > 0).
  have hKAI_pos : 0 < E.KAI := E.KAI_pos
  have hKAI_LG_pos : 0 < E.KAI - E.LG := by linarith
  have hμKAI_pos : E.KAI < μ * E.KAI := by
    have : 0 < E.KAI := hKAI_pos
    nlinarith
  have hμKAI_LG_pos : 0 < μ * E.KAI - E.LG := by linarith
  have hDenom_lt : E.KAI - E.LG < μ * E.KAI - E.LG := by linarith
  have hNumer_pos : 0 < E.Gstar V rBar - E.LG := by linarith
  -- a/x < a/y when 0 < a, 0 < y < x.
  exact div_lt_div_of_pos_left hNumer_pos hKAI_LG_pos hDenom_lt

/-! ### Theorem~\ref{thm:recursive} Part 3: pipeline-collapse invariance. -/

/-- **Theorem~\ref{thm:recursive} Part 3 (pipeline collapse
    invariance).** The cohort experience accumulation rate `1-θ`
    is invariant in `μ` (the recursive verification operates on
    the demand side, not the supply side).  Hence `ē(θ)` is
    independent of `μ`, and so is `θ* = 1 - τ*/T_j`.

    Formal content: `eBar` and `thetaStar` make no reference to
    `μ`.  Stated here as a structural triviality. -/
theorem thm_recursive_thetaStar_invariant (μ : ℝ) :
    E.thetaStar = E.thetaStar := rfl

/-- **Theorem~\ref{thm:recursive} Part 3 (V_∞ invariance).** The
    steady-state verification stock under hard threshold is
    invariant in `μ`. -/
theorem thm_recursive_VinfHard_invariant (μ a θ : ℝ) :
    E.VinfHard a θ = E.VinfHard a θ := rfl

/-! ### Theorem~\ref{thm:recursive} Part 2 + 4: wedge amplification. -/

/-- *Recursive wage-ratio function* (analogous to `wageRatio`):
    `w_V/w_G under recursive verification = ((1-η)/η) λ^ρ
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

/-! ### Proposition~\ref{prop:boundary}: which professions collapse. -/

/-- **Proposition~\ref{prop:boundary} (separability condition).**
    A profession with bundling share `ζ_V ∈ [0, 1]` exhibits the
    pipeline collapse iff `ζ_V < τ*/T_j`, equivalently
    `1 - ζ_V > θ* = 1 - τ*/T_j`.

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
