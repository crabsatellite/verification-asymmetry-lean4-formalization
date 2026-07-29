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

namespace VerificationAsymmetry

namespace Economy

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
