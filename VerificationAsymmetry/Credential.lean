/-
  VerificationAsymmetry/Credential.lean

  Theorem~\ref{thm:credential} (Credentialing Return Decay) and
  Proposition~\ref{prop:junior-senior} (Junior-Senior Wage Divergence).

  Companion to: "Verification Asymmetry under AI Substitution:
  Wage-Ratio Inversion and Apprenticeship Thresholds" (Li, 2026).

  Statement.

    Base equation (paper Eq.~\eqref{eq:R-base}):
        R(θ) = T_s · g(ē) · h(ē) · w_V(θ) - T_j · c_J(θ),
    where ē = (1-θ) T_j.

    Cobb-Douglas reduction (paper Eq.~\eqref{eq:R-cobb-douglas}):
    Under `w_V V_∞ = (1-η) Y` (Cobb-Douglas factor share) and
    `V_∞ = ν T_s g(ē) h(ē)`, the senior earnings per pipeline
    entrant simplify to `(1-η) Y(θ)/ν`, giving
        R(θ) = (1-η) Y(θ)/ν - T_j c_J(θ).

  Lean strategy.  Both equations are real-arithmetic identities;
  the only substantive step is the cancellation `g h / (ν T_s g h) =
  1/(ν T_s)`, which requires `g(ē) h(ē) ≠ 0` (a hypothesis carried
  through the proof).

  *Substantive content of the theorem.*  Below `θ*` (hard threshold,
  `g(ē) = 1`), the per-entrant return is `(1-η) Y/ν - T_j c_J`,
  not the individual senior wage `w_V h(ē)`.  This decoupling is
  the paper's key observation: as verifier supply collapses,
  individual wages rise inversely (rents flowing to fewer
  individuals) but per-entrant return tracks only the total
  factor income `(1-η) Y` divided by the cohort birth rate `ν`.

  The credential premium decay rate `(a+b)` post-collapse versus `a`
  pre-collapse is encoded as the algebraic identity that
  `g(ē) h(ē)` scales as `(1-θ)^{a+b}` (smooth threshold) versus
  `(1-θ)^a` (below `θ*`); proven inline.

  ## Cat 2 axiom dependency note

  The composite identity `(1-η) Y = w_V · (ν T_s g h)` (Cobb-Douglas
  factor share applied to the steady-state stock identity) is
  available in two forms in this file:
    * the parametric form (taking the composite identity as
      hypothesis — honest about the assumption);
    * the `_from_axioms` companion that discharges the hypothesis
      via `axiom_cobb_douglas_factor_share` (Cat 2), routed through
      `cobb_douglas_steady_state_identity_from_axiom` (Axioms.lean).
  The `_from_axioms` companions make explicit that the textbook
  Cobb-Douglas factor share IS the substantive assumption.
  Verifiable by `#print axioms thm_credential_cobb_douglas_reduction_from_axioms`.
-/

import VerificationAsymmetry.Basic
import VerificationAsymmetry.Axioms
import VerificationAsymmetry.Collapse

namespace VerificationAsymmetry

namespace Economy

variable (E : Economy)

/-! ### Theorem~\ref{thm:credential}: Cobb-Douglas closed form. -/

/-- **Theorem~\ref{thm:credential} (Cobb-Douglas reduction,
    paper Eq.~\eqref{eq:R-senior-rent}).** Under the Cobb-Douglas
    factor-share identity `w_V V_∞ = (1-η) Y` and the steady-state
    stock identity `V_∞ = ν T_s g(ē) h(ē)`, the senior earnings per
    pipeline entrant `T_s · g(ē) · h(ē) · w_V` simplify to
    `(1-η) Y / ν`.

    *Substantive content.*  In the Lean statement the `g · h`
    factor cancels syntactically (it appears on both sides of the
    factor-share identity `hY`), so the proof — `rw [hY]; field_simp`
    — needs only `ν ≠ 0`.  The positivity hypothesis `_hgh_pos`
    (`g(ē) h(ē) > 0`) is carried as part of the paper-faithful
    signature: the paper's Eq.~\eqref{eq:R-cobb-douglas} is stated
    under the nontrivial-pipeline assumption (below `θ*` under hard
    threshold `g = 1`, `h(ē) = ē^a > 0`; above `θ*`, `g = 0` and the
    reduction is degenerate).  It is `_`-prefixed to mark it
    intentionally not load-bearing for the Lean derivation. -/
theorem thm_credential_cobb_douglas_reduction
    (Y wV g h : ℝ) (hY : (1 - E.eta) * Y = wV * (E.nu * E.Ts * g * h))
    (_hgh_pos : 0 < g * h) (hTs_pos : 0 < E.Ts) :
    E.Ts * g * h * wV = (1 - E.eta) * Y / E.nu := by
  have hnu : E.nu ≠ 0 := ne_of_gt E.nu_pos
  rw [hY]
  field_simp

/-- **Theorem~\ref{thm:credential} (Cobb-Douglas reduction —
    axiom-discharged form).** Same as `thm_credential_cobb_douglas_reduction`
    but with the composite Cobb-Douglas-factor-share + steady-state-
    stock identity discharged via `axiom_cobb_douglas_factor_share`
    (Cat 2, MWG 1995 §5.B.2) routed through
    `cobb_douglas_steady_state_identity_from_axiom`.

    *Substantive content.*  Identifies which assumption is the
    Cat 2 axiom (Cobb-Douglas factor share) versus the definitional
    consequence (steady-state stock).  The Cobb-Douglas regime in
    this paper depends on exactly one textbook fact, not on a
    composite hypothesis — verifiable by `#print axioms
    thm_credential_cobb_douglas_reduction_from_axioms` which
    surfaces `axiom_cobb_douglas_factor_share`. -/
theorem thm_credential_cobb_douglas_reduction_from_axioms
    (F : ℝ → ℝ → ℝ) (η lam G Y wV : ℝ) (g h : ℝ → ℝ) (θ : ℝ)
    (hCD : IsCobbDouglas F η lam)
    (h_wV : HasDerivAt (fun y => F G y) wV (E.Vinf θ g h))
    (hY : Y = F G (E.Vinf θ g h))
    (hG_pos : 0 < G) (hVinf_pos : 0 < E.Vinf θ g h)
    (hη_pos : 0 < η) (hη_lt : η < 1)
    (hlam_pos : 0 < lam)
    (hEta : η = E.eta)
    (hgh_pos : 0 < g (E.eBar θ) * h (E.eBar θ))
    (hTs_pos : 0 < E.Ts) :
    E.Ts * g (E.eBar θ) * h (E.eBar θ) * wV
      = (1 - E.eta) * Y / E.nu :=
  E.thm_credential_cobb_douglas_reduction
    Y wV (g (E.eBar θ)) (h (E.eBar θ))
    (E.cobb_douglas_steady_state_identity_from_axiom
      F η lam G Y wV g h θ hCD h_wV hY hG_pos hVinf_pos
      hη_pos hη_lt hlam_pos hEta)
    hgh_pos hTs_pos

/-- **Theorem~\ref{thm:credential} (closed-form per-entrant return,
    paper Eq.~\eqref{eq:R-cobb-douglas}).** Substituting the
    Cobb-Douglas reduction into `R = T_s g h w_V - T_j c_J` yields
    `R(θ) = (1-η) Y(θ)/ν - T_j c_J(θ)`. -/
theorem thm_credential_closed_form
    (Y wV g h cJ : ℝ)
    (hY : (1 - E.eta) * Y = wV * (E.nu * E.Ts * g * h))
    (hgh_pos : 0 < g * h) (hTs_pos : 0 < E.Ts) :
    E.Ts * g * h * wV - E.Tj * cJ = (1 - E.eta) * Y / E.nu - E.Tj * cJ := by
  rw [E.thm_credential_cobb_douglas_reduction Y wV g h hY hgh_pos hTs_pos]

/-! ### Theorem~\ref{thm:credential} Part 2: finite-capacity gross peak. -/

/-- *Finite-capacity stationary candidate* for the below-threshold
    Cobb-Douglas gross senior component, paper
    Eq.~\eqref{eq:finite-gross-peak}. -/
noncomputable def thetaGrossPeak (a : ℝ) : ℝ :=
  (E.eta * (E.KAI - E.LG) - a * (1 - E.eta) * E.LG) /
    ((E.KAI - E.LG) * (E.eta + a * (1 - E.eta)))

/-- Under the paper's strict interior condition, the finite-capacity
    stationary candidate lies in `(0,1)`. -/
theorem thetaGrossPeak_in_unit
    (a : ℝ) (ha : 0 < a) (hK : E.LG < E.KAI)
    (hInterior :
      a * (1 - E.eta) * E.LG < E.eta * (E.KAI - E.LG)) :
    0 < E.thetaGrossPeak a ∧ E.thetaGrossPeak a < 1 := by
  have hd : 0 < E.KAI - E.LG := sub_pos.mpr hK
  have hA : 0 < a * (1 - E.eta) :=
    mul_pos ha (sub_pos.mpr E.eta_lt_one)
  have hB : 0 < E.eta + a * (1 - E.eta) := add_pos E.eta_pos hA
  have hden :
      0 < (E.KAI - E.LG) * (E.eta + a * (1 - E.eta)) :=
    mul_pos hd hB
  have hnum :
      0 < E.eta * (E.KAI - E.LG) - a * (1 - E.eta) * E.LG := by
    linarith
  constructor
  · unfold thetaGrossPeak
    exact div_pos hnum hden
  · unfold thetaGrossPeak
    apply (div_lt_one hden).2
    have hgap :
        (E.KAI - E.LG) * (E.eta + a * (1 - E.eta))
            - (E.eta * (E.KAI - E.LG) - a * (1 - E.eta) * E.LG)
          = a * (1 - E.eta) * E.KAI := by
      ring
    have : 0 < a * (1 - E.eta) * E.KAI := mul_pos hA E.KAI_pos
    linarith

/-- **Theorem~\ref{thm:credential} Part 2 (finite-capacity peak
    first-order condition).** The closed-form candidate solves the exact
    below-threshold Cobb-Douglas log-derivative equation
    `η (K_AI-L_G)/G = a(1-η)/(1-θ)`.

    Lean checks the algebraic solution of the FOC.  The paper separately uses
    the strictly decreasing affine numerator of the log derivative to conclude
    that an interior candidate below `θ*` is the unique gross-component peak. -/
theorem thm_credential_finite_capacity_peak_foc
    (a : ℝ) (ha : 0 < a) (hK : E.LG < E.KAI)
    (hInterior :
      a * (1 - E.eta) * E.LG < E.eta * (E.KAI - E.LG)) :
    E.eta * (E.KAI - E.LG) / E.G (E.thetaGrossPeak a)
      = a * (1 - E.eta) / (1 - E.thetaGrossPeak a) := by
  have hunit := E.thetaGrossPeak_in_unit a ha hK hInterior
  have hG : 0 < E.G (E.thetaGrossPeak a) :=
    E.G_pos hunit.1.le hunit.2.le
  have hOne : 0 < 1 - E.thetaGrossPeak a := sub_pos.mpr hunit.2
  have hGne : E.G (E.thetaGrossPeak a) ≠ 0 := ne_of_gt hG
  have hOnene : 1 - E.thetaGrossPeak a ≠ 0 := ne_of_gt hOne
  have hd : 0 < E.KAI - E.LG := sub_pos.mpr hK
  have hA : 0 < a * (1 - E.eta) :=
    mul_pos ha (sub_pos.mpr E.eta_lt_one)
  have hB : 0 < E.eta + a * (1 - E.eta) := add_pos E.eta_pos hA
  have hden :
      (E.KAI - E.LG) * (E.eta + a * (1 - E.eta)) ≠ 0 :=
    ne_of_gt (mul_pos hd hB)
  field_simp
  unfold thetaGrossPeak G
  field_simp [hden]
  ring

/-- The displayed finite-capacity candidate is the unique solution of the
    first-order equation on `(0,1)`. -/
theorem thm_credential_finite_capacity_peak_unique
    (a θ : ℝ) (ha : 0 < a) (hK : E.LG < E.KAI)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hFOC :
      E.eta * (E.KAI - E.LG) / E.G θ
        = a * (1 - E.eta) / (1 - θ)) :
    θ = E.thetaGrossPeak a := by
  have hd : 0 < E.KAI - E.LG := sub_pos.mpr hK
  have hA : 0 < a * (1 - E.eta) :=
    mul_pos ha (sub_pos.mpr E.eta_lt_one)
  have hB : 0 < E.eta + a * (1 - E.eta) := add_pos E.eta_pos hA
  have hden :
      (E.KAI - E.LG) * (E.eta + a * (1 - E.eta)) ≠ 0 :=
    ne_of_gt (mul_pos hd hB)
  have hG : 0 < E.G θ := E.G_pos hθ0.le hθ1.le
  have hOne : 0 < 1 - θ := sub_pos.mpr hθ1
  have hGne : E.G θ ≠ 0 := ne_of_gt hG
  have hOnene : 1 - θ ≠ 0 := ne_of_gt hOne
  field_simp at hFOC
  unfold G at hFOC
  unfold thetaGrossPeak
  apply (eq_div_iff hden).2
  nlinarith

/-! ### Theorem~\ref{thm:credential} Part 1: Leontief regime decay rate. -/

/-- *Leontief-regime per-entrant senior rent (gross of junior cost).*
    Under the Leontief limit where the output is bottlenecked by
    `V_∞` (so `Y = λ V_∞`), the senior rent per entrant is
    `λ V_∞ / ν`.  Definitional carrier for the next two theorems. -/
noncomputable def leontiefSeniorRent (a θ : ℝ) : ℝ :=
  E.lam * E.VinfHard a θ / E.nu

/-- **Theorem~\ref{thm:credential} Part 1 (Leontief decay rate
    pre-collapse, scaling form).** Below `θ*` under hard threshold,
    `V_∞(θ) = ν T_s ((1-θ) T_j)^a`, so the Leontief senior rent
    `leontiefSeniorRent a θ = λ T_s ((1-θ) T_j)^a`.

    This makes the `(1-θ)^a` decay rate explicit. -/
theorem thm_credential_leontief_pre_collapse
    (a θ : ℝ) (h : θ ≤ E.thetaStar) :
    E.leontiefSeniorRent a θ
      = E.lam * E.Ts * (E.eBar θ) ^ a := by
  unfold leontiefSeniorRent
  rw [E.thm_collapse_below_threshold a θ h]
  have hnu : E.nu ≠ 0 := ne_of_gt E.nu_pos
  field_simp

/-- **Theorem~\ref{thm:credential} Part 1 (Leontief decay rate
    post-collapse, vanishing form).** Above `θ*` under hard
    threshold, `V_∞(θ) = 0`, so the Leontief senior rent vanishes
    identically. -/
theorem thm_credential_leontief_post_collapse
    (a θ : ℝ) (hθ : E.thetaStar < θ) :
    E.leontiefSeniorRent a θ = 0 := by
  unfold leontiefSeniorRent
  rw [E.thm_collapse_above_threshold a θ hθ]
  simp

/-! ### Theorem~\ref{thm:credential} Part 3: multiplicative decay. -/

/-- **Theorem~\ref{thm:credential} Part 3 (multiplicative decay
    structure).** Under smooth promotion `g(τ) = (τ/τ*)^b` with
    `g(ē) = (ē/τ*)^b` and tacit `h(ē) = ē^a`, the product
    `g(ē) h(ē)` equals `ē^{a+b} / (τ*)^b`, which scales as
    `(1-θ)^{a+b}` via `ē = (1-θ) T_j`.

    Below `θ*` under hard threshold, `g(ē) = 1` so the product is
    just `ē^a`.  The post-collapse decay rate `(a+b)` strictly
    exceeds the pre-collapse rate `a` because the selection yield
    `g` and the tacit yield `h` multiply (paper Eq.~\eqref{eq:R-cobb-douglas}
    discussion).

    Formal content: algebraic identity for the product.  The
    exponent-range hypotheses `_ha` (`a ≥ 0`, paper `a ∈ (0,1]`)
    and `_hb` (`b > 0`, paper smooth-threshold exponent) are carried
    as part of the paper-faithful signature but are not load-bearing
    for the `Real.rpow` algebraic identity (which needs only base
    positivity); they are `_`-prefixed to mark this. -/
theorem thm_credential_multiplicative_decay
    (a b θ : ℝ) (_ha : 0 ≤ a) (_hb : 0 < b)
    (heBar_pos : 0 < E.eBar θ) (htauStar_pos : 0 < E.tauStar) :
    ((E.eBar θ) / E.tauStar) ^ b * (E.eBar θ) ^ a
      = (E.eBar θ) ^ (a + b) / E.tauStar ^ b := by
  have h1 : ((E.eBar θ) / E.tauStar) ^ b
              = (E.eBar θ) ^ b / E.tauStar ^ b := by
    rw [Real.div_rpow heBar_pos.le htauStar_pos.le]
  have h2 : (E.eBar θ) ^ a * (E.eBar θ) ^ b = (E.eBar θ) ^ (a + b) := by
    rw [← Real.rpow_add heBar_pos]
  rw [h1]
  rw [div_mul_eq_mul_div]
  congr 1
  rw [mul_comm]
  exact h2

/-! ### Theorem~\ref{thm:credential} Part 4: premium near θ = 1. -/

/-- **Theorem~\ref{thm:credential} Part 4 (premium becomes negative
    near `θ = 1`).** When the per-entrant output `Y(θ) = 0` (which
    follows from `V_∞(θ) = 0` above `θ*` in either the Leontief or
    Cobb-Douglas regime), the per-entrant return is `R(θ) = -T_j c_J`.
    For positive junior cost, `R(θ) < 0`. -/
theorem thm_credential_premium_negative_at_collapse
    (Y cJ : ℝ) (hY : Y = 0) (hcJ : 0 < cJ) :
    (1 - E.eta) * Y / E.nu - E.Tj * cJ < 0 := by
  rw [hY]
  have h : (1 - E.eta) * 0 / E.nu = 0 := by simp
  rw [h]
  have hTj : 0 < E.Tj * cJ := mul_pos E.Tj_pos hcJ
  linarith

/-! ### Proposition~\ref{prop:junior-senior}: senior wage scaling. -/

/-- **Proposition~\ref{prop:junior-senior}: senior wage in
    Cobb-Douglas.** Under the Cobb-Douglas factor share
    `w_V V_∞ = (1-η) Y` and the steady-state stock identity, the
    individual senior wage is
    `w_S = w_V h(ē) = (1-η) Y / (ν T_s g(ē))`.

    Substantive content: `w_V h / (g h) = w_V / g` cancellation,
    proving the inverse-in-`g` divergence as `θ → 1`. -/
theorem prop_junior_senior_wage
    (Y wV g h : ℝ)
    (hY : (1 - E.eta) * Y = wV * (E.nu * E.Ts * g * h))
    (hg_pos : 0 < g) (hTs_pos : 0 < E.Ts) :
    wV * h = (1 - E.eta) * Y / (E.nu * E.Ts * g) := by
  have hnu : E.nu ≠ 0 := ne_of_gt E.nu_pos
  have hTs : E.Ts ≠ 0 := ne_of_gt hTs_pos
  have hg : g ≠ 0 := ne_of_gt hg_pos
  rw [hY]
  field_simp

/-- **Proposition~\ref{prop:junior-senior} — axiom-discharged form.**
    The senior wage `w_S = w_V · h(ē) = (1-η) Y / (ν T_s g(ē))` follows
    from Cobb-Douglas factor share (`axiom_cobb_douglas_factor_share`,
    Cat 2 MWG 1995 §5.B.2) discharged through
    `cobb_douglas_steady_state_identity_from_axiom`.

    Verifiable by `#print axioms prop_junior_senior_wage_from_axioms`
    which surfaces `axiom_cobb_douglas_factor_share`. -/
theorem prop_junior_senior_wage_from_axioms
    (F : ℝ → ℝ → ℝ) (η lam G Y wV : ℝ) (g h : ℝ → ℝ) (θ : ℝ)
    (hCD : IsCobbDouglas F η lam)
    (h_wV : HasDerivAt (fun y => F G y) wV (E.Vinf θ g h))
    (hY : Y = F G (E.Vinf θ g h))
    (hG_pos : 0 < G) (hVinf_pos : 0 < E.Vinf θ g h)
    (hη_pos : 0 < η) (hη_lt : η < 1)
    (hlam_pos : 0 < lam)
    (hEta : η = E.eta)
    (hg_pos : 0 < g (E.eBar θ)) (hTs_pos : 0 < E.Ts) :
    wV * h (E.eBar θ)
      = (1 - E.eta) * Y / (E.nu * E.Ts * g (E.eBar θ)) :=
  E.prop_junior_senior_wage Y wV (g (E.eBar θ)) (h (E.eBar θ))
    (E.cobb_douglas_steady_state_identity_from_axiom
      F η lam G Y wV g h θ hCD h_wV hY hG_pos hVinf_pos
      hη_pos hη_lt hlam_pos hEta)
    hg_pos hTs_pos

end Economy

end VerificationAsymmetry
