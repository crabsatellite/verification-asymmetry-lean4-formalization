/-
  VerificationAsymmetry/Externality.lean

  Theorem~\ref{thm:externality} (Apprenticeship Externality) and
  Propositions ~\ref{prop:internalization} (Partial-Internalization
  Identity) and ~\ref{prop:decentralized-theta}
  (Conditional Adoption Ordering).

  Companion to: "Verification Asymmetry under AI Substitution:
  Wage-Ratio Inversion and Apprenticeship Thresholds" (Li, 2026).

  Statement.

    The private present value of a junior at AI substitution rate θ is
        MP_J^P(θ) = (1-θ) w_G(θ) Λ_J(r),
    where Λ_J(r) = (1-e^{-r T_j})/r is the discounted junior horizon.
    The social present value is
        MP_J^S(θ) = MP_J^P(θ) + w_V(θ) g(ē) h(ē) Λ(r),
    where Λ(r) = (e^{-r T_j} - e^{-r T})/r is the discounted senior
    horizon.

    Apprenticeship wedge (paper Eq.~\eqref{eq:wedge}):
        W_E(θ) = (MP_J^S - MP_J^P)/MP_J^P
              = (w_V/w_G) · g(ē) h(ē) Λ(r) / ((1-θ) Λ_J(r)).

    Residual-equalizing transfer (Cobb-Douglas, paper Thm
    Part 3 algebraic simplification):
        s*(θ) = (1-η) Y(θ) Λ(r) / (ν T_s).

  Lean strategy.  Both formulae are real-arithmetic identities once
  the marginal-product definitions are in place.  We formalize:

    (i)   the explicit algebraic identity for the wedge,
    (ii)  the Cobb-Douglas simplification of the residual transfer,
    (iii) the non-negativity of the wedge (Part 2),
    (iv)  the internalization corollary (Proposition~\ref{prop:internalization}),
    (v)   an anti-monotonicity implication used by the conditional
          adoption-ordering proposition.

  The paper's Part 1 wedge-growth claim is an elementary monotonicity
  argument for `G(θ)^{1-ρ} · (1-θ)^{aρ-1}` under displayed parameter
  restrictions, but it is NOT separately represented by a Lean theorem
  here.  The formal companion closes the identities and sign result, not
  the full economic interpretation or a general-equilibrium policy claim.

  ## Cat 2 axiom dependency note

  The composite Cobb-Douglas-factor-share + steady-state-stock
  identity used in Part 3 (residual-transfer formula) is reduced to
  the Cat 2 axiom `axiom_cobb_douglas_factor_share` in the
  `_from_axioms` companion theorems, routed through
  `cobb_douglas_steady_state_identity_from_axiom` (Axioms.lean).
  The parametric form (`thm_externality_pigouvian_cobb_douglas`)
  carries the composite identity as a hypothesis; the `_from_axioms`
  form discharges it via the Cat 2 axiom (verifiable by
  `#print axioms thm_externality_pigouvian_cobb_douglas_from_axioms`).
-/

import VerificationAsymmetry.Basic
import VerificationAsymmetry.Axioms
import VerificationAsymmetry.Collapse
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace VerificationAsymmetry

namespace Economy

open Filter
open scoped Topology

variable (E : Economy)

/-! ### Discounted junior and senior horizons. -/

/-- *Discounted junior horizon*
    `Λ_J(r) := (1 - e^{-r T_j}) / r`, paper Eq.~\eqref{eq:MPS}. -/
noncomputable def LambdaJ (r : ℝ) : ℝ :=
  (1 - Real.exp (-r * E.Tj)) / r

/-- `Λ_J(r) > 0` for `r > 0`. -/
lemma LambdaJ_pos {r : ℝ} (hr : 0 < r) : 0 < E.LambdaJ r := by
  unfold LambdaJ
  apply div_pos _ hr
  have hprod : 0 < r * E.Tj := mul_pos hr E.Tj_pos
  have harg : -r * E.Tj < 0 := by linarith
  have hexp : Real.exp (-r * E.Tj) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr harg
  linarith

/-- *Discounted senior horizon* `Λ(r) := (e^{-r T_j} - e^{-r T}) / r`,
    paper Eq.~\eqref{eq:MPS}.

    For `r > 0` and `T_j < T`, `Λ(r) > 0`. -/
noncomputable def Lambda (r : ℝ) : ℝ :=
  (Real.exp (-r * E.Tj) - Real.exp (-r * E.T)) / r

/-- `Λ(r) > 0` for `r > 0`. -/
lemma Lambda_pos {r : ℝ} (hr : 0 < r) : 0 < E.Lambda r := by
  unfold Lambda
  apply div_pos _ hr
  -- exp(-r T_j) - exp(-r T) > 0 since -r T_j > -r T (T_j < T)
  -- which gives exp(-r T_j) > exp(-r T).
  have h1 : -r * E.T < -r * E.Tj := by
    have : E.Tj < E.T := E.Tj_lt_T
    nlinarith
  have h2 : Real.exp (-r * E.T) < Real.exp (-r * E.Tj) :=
    Real.exp_lt_exp.mpr h1
  linarith

/-! ### Present-value marginal contributions. -/

/-- *Private present value of a junior* at rate `θ`:
    `MP_J^P(θ) = (1-θ) w_G(θ) Λ_J`.

    Economy-independent definition: takes `wG` as an external
    parameter rather than threading through Economy fields, since
    the marginal-product wage is determined by the underlying CES
    production function and the paper's narrative treats it as a
    given by the time MP_J^P enters the externality calculation.
    Downstream call sites use the bare `MPpriv` (no dot-notation). -/
def MPpriv (wG LambdaJ θ : ℝ) : ℝ := (1 - θ) * wG * LambdaJ

/-- *Social present value of a junior* at rate `θ`:
    `MP_J^S(θ) = MP_J^P(θ) + w_V g(ē) h(ē) Λ`. -/
def MPsoc (wG wV gE hE LambdaJ Lambda θ : ℝ) : ℝ :=
  MPpriv wG LambdaJ θ + wV * gE * hE * Lambda

/-- *Externality residual* `s*(θ) := MP_J^S - MP_J^P =
    w_V g(ē) h(ē) Λ`.  Economy-independent definition: takes
    the relevant marginal products and tacit-technology values as
    external parameters, matching the paper's narrative treatment. -/
def externalityResidual (wV gE hE Lambda : ℝ) : ℝ :=
  wV * gE * hE * Lambda

/-! ### Theorem~\ref{thm:externality} — algebraic identities. -/

/-- **Theorem~\ref{thm:externality} (residual identity).** The
    externality residual `MP_J^S - MP_J^P` equals
    `w_V g(ē) h(ē) Λ`. -/
theorem thm_externality_residual_identity
    (wG wV gE hE LambdaJ Lambda θ : ℝ) :
    MPsoc wG wV gE hE LambdaJ Lambda θ - MPpriv wG LambdaJ θ
      = externalityResidual wV gE hE Lambda := by
  unfold MPsoc MPpriv externalityResidual
  ring

/-- **Theorem~\ref{thm:externality} (non-negativity, Part 2).** The
    externality residual is non-negative whenever
    `w_V, g, h, Λ ≥ 0`. -/
theorem thm_externality_residual_nonneg
    (wV gE hE Lambda : ℝ) (hwV : 0 ≤ wV) (hgE : 0 ≤ gE)
    (hhE : 0 ≤ hE) (hLambda : 0 ≤ Lambda) :
    0 ≤ externalityResidual wV gE hE Lambda := by
  unfold externalityResidual
  have h1 : 0 ≤ wV * gE := mul_nonneg hwV hgE
  have h2 : 0 ≤ wV * gE * hE := mul_nonneg h1 hhE
  exact mul_nonneg h2 hLambda

/-- **Theorem~\ref{thm:externality} (Part 2 — strict positivity).**
    Strict positivity of the externality residual whenever
    `g h > 0` and `w_V, Λ > 0`. -/
theorem thm_externality_residual_pos
    (wV gE hE Lambda : ℝ) (hwV : 0 < wV) (hgh : 0 < gE * hE)
    (hLambda : 0 < Lambda) :
    0 < externalityResidual wV gE hE Lambda := by
  unfold externalityResidual
  have : 0 < wV * (gE * hE) := mul_pos hwV hgh
  have h_eq : wV * gE * hE = wV * (gE * hE) := by ring
  rw [h_eq]
  exact mul_pos this hLambda

/-! ### Apprenticeship wedge. -/

/-- *Apprenticeship wedge* `W_E(θ) := (MP_J^S - MP_J^P)/MP_J^P`,
    paper Eq.~\eqref{eq:wedge}. -/
noncomputable def wedge (wG wV gE hE LambdaJ Lambda θ : ℝ) : ℝ :=
  externalityResidual wV gE hE Lambda / MPpriv wG LambdaJ θ

/-- **Theorem~\ref{thm:externality} (wedge identity).** The
    wedge `W_E(θ)` rearranges to
    `(w_V/w_G) · g(ē) h(ē) Λ / ((1-θ) Λ_J)`. -/
theorem thm_externality_wedge_identity
    (wG wV gE hE LambdaJ Lambda θ : ℝ)
    (hwG : 0 < wG) (hLambdaJ : 0 < LambdaJ) (hθ_lt : θ < 1) :
    wedge wG wV gE hE LambdaJ Lambda θ
      = (wV / wG) * (gE * hE * Lambda) /
          ((1 - θ) * LambdaJ) := by
  unfold wedge externalityResidual MPpriv
  have h1mθ : 0 < 1 - θ := by linarith
  have h1mθ_ne : 1 - θ ≠ 0 := ne_of_gt h1mθ
  have hwG_ne : wG ≠ 0 := ne_of_gt hwG
  have hLambdaJ_ne : LambdaJ ≠ 0 := ne_of_gt hLambdaJ
  field_simp

/-! ### Theorem~\ref{thm:externality} Part 1: wedge growth below the
    hard threshold. -/

/-- The theta-dependent core of paper Eq. (14).  The omitted coefficient is
    strictly positive under the theorem's displayed parameter restrictions. -/
noncomputable def wedgeGrowthCore (a theta : ℝ) : ℝ :=
  (E.G theta) ^ (1 - E.rho) * (1 - theta) ^ (a * E.rho - 1)

/-- Positive theta-independent coefficient in paper Eq. (14). -/
noncomputable def wedgeGrowthCoefficient (r a : ℝ) : ℝ :=
  ((1 - E.eta) * E.lam ^ E.rho * E.Lambda r * E.Tj ^ (a * E.rho)) /
    (E.eta * E.LambdaJ r * (E.nu * E.Ts) ^ (1 - E.rho))

/-- Full closed form displayed in paper Eq. (14). -/
noncomputable def wedgeExplicit (r a theta : ℝ) : ℝ :=
  E.wedgeGrowthCoefficient r a * E.wedgeGrowthCore a theta

theorem wedgeGrowthCoefficient_pos {r a : ℝ} (hr : 0 < r) :
    0 < E.wedgeGrowthCoefficient r a := by
  unfold wedgeGrowthCoefficient
  apply div_pos
  · exact mul_pos
      (mul_pos
        (mul_pos (by linarith [E.eta_lt_one])
          (Real.rpow_pos_of_pos E.lam_pos _))
        (E.Lambda_pos hr))
      (Real.rpow_pos_of_pos E.Tj_pos _)
  · exact mul_pos
      (mul_pos E.eta_pos (E.LambdaJ_pos hr))
      (Real.rpow_pos_of_pos (mul_pos E.nu_pos E.Ts_pos) _)

/-- The wedge-growth core is non-decreasing below the hard threshold.  This is
    the complete two-factor monotonicity argument used in the paper: generation
    rises, while a positive base raised to the negative exponent
    `a*rho-1` also rises as `theta` rises. -/
theorem thm_externality_wedge_growth_core_monotone
    {a theta1 theta2 : ℝ}
    (ha_pos : 0 < a) (ha_le : a ≤ 1)
    (hrho_lt : E.rho < 1) (hKAI_ge : E.LG ≤ E.KAI)
    (htheta1_nonneg : 0 ≤ theta1) (htheta12 : theta1 ≤ theta2)
    (htheta2_below : theta2 < E.thetaStar) :
    E.wedgeGrowthCore a theta1 ≤ E.wedgeGrowthCore a theta2 := by
  have hthetaStar_lt : E.thetaStar < 1 := E.thetaStar_in_unit_interval.2
  have htheta2_lt_one : theta2 < 1 := lt_trans htheta2_below hthetaStar_lt
  have htheta2_le_one : theta2 ≤ 1 := htheta2_lt_one.le
  have htheta1_le_one : theta1 ≤ 1 := le_trans htheta12 htheta2_le_one
  have hG1_pos : 0 < E.G theta1 := E.G_pos htheta1_nonneg htheta1_le_one
  have hG2_pos : 0 < E.G theta2 :=
    E.G_pos (le_trans htheta1_nonneg htheta12) htheta2_le_one
  have hG_le : E.G theta1 ≤ E.G theta2 :=
    E.G_monotone_of_KAI_ge_LG hKAI_ge htheta12
  have hpowG :
      (E.G theta1) ^ (1 - E.rho) ≤ (E.G theta2) ^ (1 - E.rho) :=
    Real.rpow_le_rpow hG1_pos.le hG_le (by linarith)
  have hexp_neg : a * E.rho - 1 < 0 := by
    have hmul : a * E.rho < a * 1 := mul_lt_mul_of_pos_left hrho_lt ha_pos
    linarith
  have hbase2_pos : 0 < 1 - theta2 := by linarith
  have hbase1_pos : 0 < 1 - theta1 := by linarith
  have hbase_le : 1 - theta2 ≤ 1 - theta1 := by linarith
  have hpowTheta :
      (1 - theta1) ^ (a * E.rho - 1) ≤
        (1 - theta2) ^ (a * E.rho - 1) :=
    Real.rpow_le_rpow_of_nonpos hbase2_pos hbase_le hexp_neg.le
  unfold wedgeGrowthCore
  exact mul_le_mul hpowG hpowTheta
    (Real.rpow_nonneg hbase1_pos.le _)
    (Real.rpow_nonneg hG2_pos.le _)

/-- Multiplying the core by the positive theta-independent coefficient in
    Eq. (14) preserves monotonicity. -/
theorem thm_externality_wedge_growth_monotone
    {a theta1 theta2 C : ℝ}
    (hC : 0 ≤ C)
    (ha_pos : 0 < a) (ha_le : a ≤ 1)
    (hrho_lt : E.rho < 1) (hKAI_ge : E.LG ≤ E.KAI)
    (htheta1_nonneg : 0 ≤ theta1) (htheta12 : theta1 ≤ theta2)
    (htheta2_below : theta2 < E.thetaStar) :
    C * E.wedgeGrowthCore a theta1 ≤
      C * E.wedgeGrowthCore a theta2 :=
  mul_le_mul_of_nonneg_left
    (E.thm_externality_wedge_growth_core_monotone ha_pos ha_le hrho_lt
      hKAI_ge htheta1_nonneg htheta12 htheta2_below) hC

/-- Paper Eq. (14) is non-decreasing below the hard threshold. -/
theorem wedgeExplicit_monotone
    {r a theta1 theta2 : ℝ}
    (hr : 0 < r) (ha_pos : 0 < a) (ha_le : a ≤ 1)
    (hrho_lt : E.rho < 1) (hKAI_ge : E.LG ≤ E.KAI)
    (htheta1_nonneg : 0 ≤ theta1) (htheta12 : theta1 ≤ theta2)
    (htheta2_below : theta2 < E.thetaStar) :
    E.wedgeExplicit r a theta1 ≤ E.wedgeExplicit r a theta2 := by
  unfold wedgeExplicit
  exact E.thm_externality_wedge_growth_monotone
    (E.wedgeGrowthCoefficient_pos hr).le ha_pos ha_le hrho_lt hKAI_ge
    htheta1_nonneg htheta12 htheta2_below

/-- Exponent governing the smooth-threshold post-collapse wedge. -/
def smoothWedgeExponent (a b : ℝ) : ℝ := (a + b) * E.rho - 1

theorem smoothWedgeExponent_neg
    {a b : ℝ} (hab : 0 < a + b) (h : E.rho < 1 / (a + b)) :
    E.smoothWedgeExponent a b < 0 := by
  unfold smoothWedgeExponent
  have hmul : E.rho * (a + b) < 1 := (lt_div_iff₀ hab).1 h
  nlinarith

theorem smoothWedgeExponent_eq_zero
    {a b : ℝ} (hab : 0 < a + b) (h : E.rho = 1 / (a + b)) :
    E.smoothWedgeExponent a b = 0 := by
  unfold smoothWedgeExponent
  rw [h]
  field_simp
  norm_num

theorem smoothWedgeExponent_pos
    {a b : ℝ} (hab : 0 < a + b) (h : 1 / (a + b) < E.rho) :
    0 < E.smoothWedgeExponent a b := by
  unfold smoothWedgeExponent
  have hmul : 1 < E.rho * (a + b) := (div_lt_iff₀ hab).1 h
  nlinarith

/-- A negative post-collapse exponent diverges as residual human generation
    `x=1-theta` tends to zero from above. -/
theorem smoothWedgePower_tendsto_atTop
    {a b : ℝ} (h : E.smoothWedgeExponent a b < 0) :
    Tendsto (fun x : ℝ => x ^ E.smoothWedgeExponent a b)
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
  tendsto_rpow_neg_nhdsGT_zero h

/-- A zero post-collapse exponent has the finite nonzero limit one. -/
theorem smoothWedgePower_eq_one
    {a b x : ℝ} (h : E.smoothWedgeExponent a b = 0) :
    x ^ E.smoothWedgeExponent a b = 1 := by
  rw [h, Real.rpow_zero]

/-- A positive post-collapse exponent tends to zero. -/
theorem smoothWedgePower_tendsto_zero
    {a b : ℝ} (h : 0 < E.smoothWedgeExponent a b) :
    Tendsto (fun x : ℝ => x ^ E.smoothWedgeExponent a b)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  have hid : Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  exact hid.rpow_const_nhds_zero h

/-! ### Theorem~\ref{thm:externality} Part 3: residual-equalizing transfer. -/

/-- *Residual-equalizing transfer* in Cobb-Douglas:
    `s*(θ) = (1-η) Y(θ) Λ(r) / (ν T_s)`,
    paper Theorem~\ref{thm:externality} Part 3.

    Derivation: `s* = MP_J^S - MP_J^P = w_V g h Λ`.  Under Cobb-
    Douglas factor share `w_V V_∞ = (1-η) Y` and the steady-state
    stock identity `V_∞ = ν T_s g h`, we have
    `w_V g h = (1-η) Y / (ν T_s)`, hence
    `s* = (1-η) Y Λ / (ν T_s)`. -/
noncomputable def pigouvianSubsidy_CD (Y Lambda : ℝ) : ℝ :=
  (1 - E.eta) * Y * Lambda / (E.nu * E.Ts)

/-- **Theorem~\ref{thm:externality} Part 3 (Cobb-Douglas residual-transfer
    formula).** Under the Cobb-Douglas factor-share identity
    `(1-η) Y = w_V · ν T_s · g h`, the displayed residual
    `s* = w_V g h Λ` simplifies to `(1-η) Y Λ / (ν T_s)`.
    The legacy declaration name is retained for API stability; the
    theorem contains no first-best or financing claim. -/
theorem thm_externality_pigouvian_cobb_douglas
    (Y wV gE hE Lambda : ℝ)
    (hY : (1 - E.eta) * Y = wV * (E.nu * E.Ts * gE * hE)) :
    externalityResidual wV gE hE Lambda
      = E.pigouvianSubsidy_CD Y Lambda := by
  unfold externalityResidual pigouvianSubsidy_CD
  have hnu : E.nu ≠ 0 := ne_of_gt E.nu_pos
  have hTs : E.Ts ≠ 0 := ne_of_gt E.Ts_pos
  -- Goal: wV * gE * hE * Λ = (1-η) Y Λ / (ν T_s)
  -- Rewrite using hY: wV * gE * hE = (1-η) Y / (ν T_s)
  have hkey : wV * gE * hE = (1 - E.eta) * Y / (E.nu * E.Ts) := by
    rw [hY]
    field_simp
  rw [hkey]
  ring

/-- **Theorem~\ref{thm:externality} Part 3 — axiom-discharged form.**
    Same as `thm_externality_pigouvian_cobb_douglas` but with the
    composite Cobb-Douglas-factor-share + steady-state-stock identity
    discharged via `axiom_cobb_douglas_factor_share` (Cat 2,
    MWG 1995 §5.B.2) routed through
    `cobb_douglas_steady_state_identity_from_axiom`.

    Verifiable by `#print axioms thm_externality_pigouvian_cobb_douglas_from_axioms`
    which surfaces `axiom_cobb_douglas_factor_share`. -/
theorem thm_externality_pigouvian_cobb_douglas_from_axioms
    (F : ℝ → ℝ → ℝ) (η lam G Y wV Lambda : ℝ) (g h : ℝ → ℝ) (θ : ℝ)
    (hCD : IsCobbDouglas F η lam)
    (h_wV : HasDerivAt (fun y => F G y) wV (E.Vinf θ g h))
    (hY : Y = F G (E.Vinf θ g h))
    (hG_pos : 0 < G) (hVinf_pos : 0 < E.Vinf θ g h)
    (hη_pos : 0 < η) (hη_lt : η < 1)
    (hlam_pos : 0 < lam)
    (hEta : η = E.eta) :
    externalityResidual wV (g (E.eBar θ)) (h (E.eBar θ)) Lambda
      = E.pigouvianSubsidy_CD Y Lambda :=
  E.thm_externality_pigouvian_cobb_douglas
    Y wV (g (E.eBar θ)) (h (E.eBar θ)) Lambda
    (E.cobb_douglas_steady_state_identity_from_axiom
      F η lam G Y wV g h θ hCD h_wV hY hG_pos hVinf_pos
      hη_pos hη_lt hlam_pos hEta)

/-! ### Proposition~\ref{prop:internalization}: within-firm internalization.

  The paper's Proposition~\ref{prop:internalization} establishes
  that internalizing fraction `ζ ∈ [0, 1]` of the future
  verification rent rescales the paper's externality wedge `W_E(θ)`
  by `(1-ζ)`.

  The Lean encoding mirrors this by *defining* the internalized
  wedge as `(1-ζ) · W_E(θ)`; `prop_internalization` is then the
  definitional unfolding identifying the def with the unrolled
  form `(1-ζ) · (residual / MP_priv)`.

  *Substantive content.*  The substantive economic interpretation
  of this proposition lives in the paper narrative around
  `\label{prop:internalization}`: a fully-internalizing firm
  (`ζ = 1`) faces zero effective externality wedge — captured
  directly by the def, `internalizedWedge 1 ... = 0 · wedge ... = 0`
  — and a partially-internalizing firm (`ζ < 1`) retains a strictly
  positive residual wedge.  The Lean rfl is the algebraic identity
  for the def, not the economic content. -/

/-- *Internalized wedge.*  Definitional infrastructure: internalizing
    fraction `ζ ∈ [0, 1]` of the future verification rent rescales
    the effective externality wedge to `(1-ζ) · W_E(θ)` (paper
    Proposition~\ref{prop:internalization}).  The
    full-internalization corner `ζ = 1` yields zero effective wedge:
    `internalizedWedge 1 ... = 0 · wedge ... = 0` directly from the
    def.

    A concrete `def` whose defining equation holds by `rfl` —
    definitional notation built on `wedge`, not a standalone Cat 3
    atom.  Documented under `gap_prop_internalization_CLOSED`
    in `Ledger.lean`. -/
noncomputable def internalizedWedge
    (zeta wG wV gE hE LambdaJ Lambda θ : ℝ) : ℝ :=
  (1 - zeta) * wedge wG wV gE hE LambdaJ Lambda θ

/-- **Proposition~\ref{prop:internalization} (within-firm
    internalization — unfolding identity).** The internalized
    wedge equals `(1 - ζ) · (residual / MP_priv)` — the
    definitional unfolding of `internalizedWedge` against the
    paper's wedge definition `W_E(θ) = residual / MP_priv`.

    Derived definitional-unfolding identity: the paper derives the
    internalized wedge as `(1-ζ) · W_E` in a one-line step, and the
    Lean theorem is the `rfl` identification of the
    `internalizedWedge` def composed with the `wedge` def with the
    unrolled form `(1-ζ) · (residual / MP_priv)`.

    See `gap_prop_internalization_CLOSED` in `Ledger.lean`
    for the canonical record. -/
theorem prop_internalization
    (zeta wG wV gE hE LambdaJ Lambda θ : ℝ) :
    internalizedWedge zeta wG wV gE hE LambdaJ Lambda θ
      = (1 - zeta) *
          (externalityResidual wV gE hE Lambda /
            MPpriv wG LambdaJ θ) := by
  unfold internalizedWedge wedge
  rfl

/-! ### Proposition~\ref{prop:decentralized-theta}: social vs. private. -/

/-- **Proposition~\ref{prop:decentralized-theta} (social vs. private
    FOC).** The social FOC `p_AI + s*(θ_soc) = B(θ_soc)` and the
    private FOC `p_AI = B(θ_eq)` imply
    `B(θ_soc) = B(θ_eq) + s*(θ_soc)`.

    Hence whenever `s*(θ_soc) > 0`, `B(θ_soc) > B(θ_eq)`. -/
theorem prop_decentralized_theta_foc
    (pAI sStar B_soc B_eq : ℝ)
    (hSoc : pAI + sStar = B_soc) (hEq : pAI = B_eq) :
    B_soc = B_eq + sStar := by
  linarith

/-- **Proposition~\ref{prop:decentralized-theta} (strict inequality).**
    Given the two stipulated interior first-order equations, a positive
    residual transfer implies a strictly higher present-value benefit
    `B` at the residual-adjusted solution.  The legacy declaration name
    is retained for API stability. -/
theorem prop_decentralized_theta_wG_strict
    (pAI sStar B_soc B_eq : ℝ) (hSoc : pAI + sStar = B_soc)
    (hEq : pAI = B_eq) (hsStar : 0 < sStar) :
    B_eq < B_soc := by
  have := prop_decentralized_theta_foc pAI sStar B_soc B_eq hSoc hEq
  linarith

/-- **Proposition~\ref{prop:decentralized-theta} (monotonicity of
    `B`).** Given the INDEPENDENT reduced-form premise that the
    present-value benefit schedule `B` is strictly decreasing in `θ`,
    the strict inequality `B(θ_soc) > B(θ_eq)` implies
    `θ_soc < θ_eq`.

    An increasing ratio `w_V/w_G` does not itself establish this premise.

    *Formal content.*  Anti-monotonicity bridge: if `f` is
    strictly anti-monotone and `f(x) > f(y)`, then `x < y`. -/
theorem prop_decentralized_theta_overshoots
    (theta_soc theta_eq : ℝ) (B : ℝ → ℝ)
    (hB_anti : ∀ x y, x < y → B y < B x)
    (h_strict : B theta_eq < B theta_soc) :
    theta_soc < theta_eq := by
  by_contra hcon
  push Not at hcon
  rcases lt_or_eq_of_le hcon with hlt | heq
  · -- theta_eq < theta_soc would give B theta_soc < B theta_eq,
    -- contradicting h_strict.
    have := hB_anti theta_eq theta_soc hlt
    linarith
  · -- theta_eq = theta_soc would give B equal, contradicting
    -- the strict inequality.
    rw [heq] at h_strict
    exact lt_irrefl _ h_strict

end Economy

end VerificationAsymmetry
