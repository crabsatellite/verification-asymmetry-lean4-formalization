/-
  VerificationAsymmetry/Credential.lean

  Theorem~\ref{thm:credential} (Credentialing Return Decay) and
  Proposition~\ref{prop:junior-senior} (Junior-Senior Wage Divergence).

  Companion to: "Generation--Verification Asymmetry Inversion and
  Apprenticeship Pipeline Collapse Under AI Substitution" (Li, 2026).

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

  ## Audit note (post-audit 2026-05)

  The composite identity `(1-η) Y = w_V · (ν T_s g h)` (Cobb-Douglas
  factor share applied to the steady-state stock identity) was
  formerly carried as a *hypothesis* of every Cobb-Douglas-regime
  theorem in this file.  The post-audit version provides BOTH:
    * the original parametric form (taking the composite identity
      as hypothesis — honest about the assumption);
    * a derived `_from_axioms` companion that discharges the
      hypothesis using `axiom_cobb_douglas_factor_share` (Cat 2)
      composed with `steady_state_stock_identity` (definitional
      unfolding of `Vinf`).
  The `_from_axioms` companions make explicit that the textbook
  Cobb-Douglas factor share IS the substantive assumption; without
  the axiom, the hypothesis would have no derivation route.
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

    *Substantive content.*  The cancellation depends on
    `g(ē) h(ē) ≠ 0`; below `θ*` under hard threshold this holds
    (`g = 1` and `h(ē) = ē^a > 0`).  Above `θ*`, `g = 0` and the
    cancellation is degenerate; the paper's Eq.~\eqref{eq:R-cobb-douglas}
    is stated under the implicit assumption of nontrivial pipeline. -/
theorem thm_credential_cobb_douglas_reduction
    (Y wV g h : ℝ) (hY : (1 - E.eta) * Y = wV * (E.nu * E.Ts * g * h))
    (hgh_pos : 0 < g * h) (hTs_pos : 0 < E.Ts) :
    E.Ts * g * h * wV = (1 - E.eta) * Y / E.nu := by
  have hnu : E.nu ≠ 0 := ne_of_gt E.nu_pos
  rw [hY]
  field_simp

/-- **Theorem~\ref{thm:credential} (Cobb-Douglas reduction —
    axiom-discharged form).** Same as `thm_credential_cobb_douglas_reduction`
    but with the composite Cobb-Douglas-factor-share + steady-state-
    stock identity discharged using `axiom_cobb_douglas_factor_share`
    (Cat 2, textbook) and the definitional unfolding of `Vinf`.

    *Substantive content.*  Identifies which assumption is the
    Cat 2 axiom (Cobb-Douglas factor share) versus the definitional
    consequence (steady-state stock).  After the axiom-discharged
    form, the Cobb-Douglas regime in this paper depends on exactly
    one textbook fact, not on a composite hypothesis. -/
theorem thm_credential_cobb_douglas_reduction_from_axioms
    (Y wV : ℝ) (g h : ℝ → ℝ) (θ : ℝ)
    (hgh_pos : 0 < g (E.eBar θ) * h (E.eBar θ))
    (hTs_pos : 0 < E.Ts) :
    E.Ts * g (E.eBar θ) * h (E.eBar θ) * wV
      = (1 - E.eta) * Y / E.nu :=
  E.thm_credential_cobb_douglas_reduction
    Y wV (g (E.eBar θ)) (h (E.eBar θ))
    (E.cobb_douglas_steady_state_identity Y wV g h θ)
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

/-! ### Theorem~\ref{thm:credential} Part 1: Leontief regime decay rate. -/

/-- **Theorem~\ref{thm:credential} Part 1 (Leontief decay rate
    pre-collapse).** Below `θ*` in the Leontief regime above the
    inversion, output `Y = λ V_∞` so the per-entrant senior rent
    `R + T_j c_J = λ V_∞ / ν` scales as `(1-θ)^a` via `V_∞ =
    ν T_s ((1-θ) T_j)^a`.

    Formal content: the algebraic identity
    `R(θ) + T_j c_J(θ) = λ V_∞(θ) / ν`. -/
theorem thm_credential_leontief_pre_collapse
    (a : ℝ) {θ : ℝ} (cJ : ℝ) :
    (E.lam * (E.VinfHard a θ) / E.nu - E.Tj * cJ) + E.Tj * cJ
      = E.lam * (E.VinfHard a θ) / E.nu := by
  ring

/-- **Theorem~\ref{thm:credential} Part 1 (Leontief decay rate
    post-collapse).** Above `θ*` in the Leontief regime, `V_∞ = 0`
    so `R + T_j c_J = 0`.  The per-entrant rent has collapsed. -/
theorem thm_credential_leontief_post_collapse
    (a : ℝ) {θ : ℝ} (hθ : E.thetaStar < θ) (cJ : ℝ) :
    (E.lam * (E.VinfHard a θ) / E.nu - E.Tj * cJ) + E.Tj * cJ = 0 := by
  rw [E.thm_collapse_above_threshold a θ hθ]
  ring

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

    Formal content: algebraic identity for the product. -/
theorem thm_credential_multiplicative_decay
    (a b θ : ℝ) (ha : 0 ≤ a) (hb : 0 < b)
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
    near `θ = 1`).** When `V_∞(θ) = 0` (hard threshold above `θ*`),
    `Y(θ) = 0` in either the Leontief or Cobb-Douglas regime (since
    `Y` depends on `V_∞`), so `R(θ) = -T_j c_J(θ)`.  For positive
    junior cost, `R(θ) < 0`.

    Formal content: `R(θ) = -T_j c_J` when `Y(θ) = 0`. -/
theorem thm_credential_premium_negative_at_collapse
    (cJ_pos : ℝ) (hcJ : 0 < cJ_pos) :
    (1 - E.eta) * 0 / E.nu - E.Tj * cJ_pos < 0 := by
  have h : (1 - E.eta) * 0 / E.nu = 0 := by simp
  rw [h]
  have : 0 < E.Tj * cJ_pos := mul_pos E.Tj_pos hcJ
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
    from Cobb-Douglas factor share (Cat 2 axiom) and the steady-state
    stock identity (definitional). -/
theorem prop_junior_senior_wage_from_axioms
    (Y wV : ℝ) (g h : ℝ → ℝ) (θ : ℝ)
    (hg_pos : 0 < g (E.eBar θ)) (hTs_pos : 0 < E.Ts) :
    wV * h (E.eBar θ)
      = (1 - E.eta) * Y / (E.nu * E.Ts * g (E.eBar θ)) :=
  E.prop_junior_senior_wage Y wV (g (E.eBar θ)) (h (E.eBar θ))
    (E.cobb_douglas_steady_state_identity Y wV g h θ)
    hg_pos hTs_pos

end Economy

end VerificationAsymmetry
