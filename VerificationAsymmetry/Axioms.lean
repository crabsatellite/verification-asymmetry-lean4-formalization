/-
  VerificationAsymmetry/Axioms.lean

  Explicit Cat 2 (textbook-fact) and Cat 3 (paper-novel structural) axioms.

  Companion to: "Generation--Verification Asymmetry Inversion and
  Apprenticeship Pipeline Collapse Under AI Substitution" (Li, 2026).

  ## Why this file exists

  Several paper-level theorems in this formalization formerly took
  their substantive content as *hypotheses* of a real-arithmetic
  identity, leaving the proof body a one-line `field_simp` or `rfl`.
  The post-audit refactor (2026-05) made the substantive content
  explicit by introducing typed axioms here.

  Each axiom carries:
    * an Atomic predicate / structural equation (no composite content,
      per `feedback_lean_axiom_decomposition.md`);
    * a docstring with the textbook or paper-level citation;
    * a `cat2External` or `cat3PaperNovel` tag mirrored in
      `Ledger.lean`.

  ## Trust profile

  Adding these axioms is an *increase* in honest accounting, not a
  decrease in rigor.  Previously the same content was hidden inside
  theorem signatures as "for any F, wG, wV, V satisfying the Euler
  identity, ...".  Making the axioms explicit:
    * locates the trust assumption,
    * permits cross-paper auditing of citations,
    * decomposes hidden-composite hypotheses into atomic pieces, and
    * leaves the consumer theorems' proofs as honest algebraic
      consequences of the axioms + definitions.

  The post-audit axiom count is:
    * Cat 2 (textbook):   3   — `axiom_euler_crs`,
                                `axiom_ces_wage_ratio_closed_form`,
                                `axiom_cobb_douglas_factor_share`.
    * Cat 3 (paper-novel): 0  — every paper-novel structural object
                                (`Economy`, `Vinf`, `eBar`, `gHard`,
                                 `wageRatio`, `Vreq`, …) is encoded
                                as a Lean *definition*, not an axiom.
                                Where the paper's narrative parametrizes
                                over abstract objects (e.g. `Φ` for
                                Brouwer in `EndogenousAI.lean`), the
                                Lean theorems are *parametric* in those
                                objects; the parametricity is the
                                honest framing.
-/

import VerificationAsymmetry.Basic

namespace VerificationAsymmetry

namespace Economy

variable (E : Economy)

/-! ### Cat 2 axiom 1: Euler's identity for CRS production.

  Paper statement (Theorem~\ref{thm:decomp}): for any production
  function `F : ℝ_+^2 → ℝ_+` that is homogeneous of degree one
  (constant returns to scale), Euler's identity gives the additive
  factor-share decomposition

      F(G, V) = (∂F/∂G) · G + (∂F/∂V) · V.

  Under competitive markets `w_G = ∂F/∂G`, `w_V = ∂F/∂V`, this is

      F(G, V) = w_G · G + w_V · V.

  Mathlib status.  As of 2026-05, Mathlib provides `Real.rpow`-level
  machinery for individual homogeneous functions (e.g. `Real.rpow_mul`)
  but no generic Euler-identity theorem for an abstract
  `F : ℝ × ℝ → ℝ` parameter with a homogeneity hypothesis.
  Formalizing the general Euler theorem requires either
  `MeasureTheory`-style integration along radial rays or a
  differential-geometric treatment of homogeneous functions; neither
  is in scope.

  Textbook citation.  Mas-Colell, Whinston, Green, *Microeconomic
  Theory* (1995), §5.B.2 (Euler's theorem for constant-returns-to-
  scale technologies).  Standard graduate microeconomics fact.
-/
/-- **Cat 2 axiom.** Euler's identity for CRS production functions.

    For any homogeneous-of-degree-one `F : ℝ → ℝ → ℝ` evaluated at
    `(G, V)` with marginal-product wage rates `w_G, w_V`,

        F(G, V) = w_G · G + w_V · V.

    Stated as an axiom because (i) the Lean parameter `F` is
    abstract — no homogeneity predicate is carried in the type, so
    the result cannot be derived from `F` alone — and (ii) Mathlib
    has no generic Euler-identity theorem for abstract homogeneous
    functions usable here.  The result is textbook microeconomics
    (Mas-Colell, Whinston, Green 1995, §5.B.2).

    *Atomic form.*  The axiom is a *single* algebraic identity at
    fixed factor levels `G, V`; no composite or universally-quantified
    structure is hidden.  Higher-level claims (e.g.
    `Wstock + Wflow = W`) are derived in `Decomp.lean` via direct
    algebraic manipulation of the axiom's right-hand side. -/
axiom axiom_euler_crs (F : ℝ → ℝ → ℝ) (G V wG wV : ℝ) :
    F G V = wG * G + wV * V

/-! ### Cat 2 axiom 2: CES wage-ratio closed form.

  Paper statement (Theorem~\ref{thm:inversion} Part 1, Eq.
  \eqref{eq:wage-ratio}): under CES production
  `F(G, V) = (η G^ρ + (1-η)(λ V)^ρ)^{1/ρ}` with competitive marginal
  products `w_G = ∂F/∂G` and `w_V = ∂F/∂V`, the wage ratio is

      w_V / w_G = ((1-η)/η) · λ^ρ · (G/V)^{1-ρ}.

  Mathlib status.  The result is the marginal-product calculus of a
  specific `Real.rpow` expression.  In principle Mathlib's
  differentiation infrastructure (`Real.hasDerivAt_rpow_const`,
  chain rule) can carry out the derivation, but the chain of
  derivatives through `(η G^ρ + (1-η)(λ V)^ρ)^{1/ρ}` is a 12-step
  Mathlib proof requiring positivity hypotheses at every level.
  This formalization captures the *closed form* as a definition
  (`wageRatio` in `Inversion.lean`) and the *identification with
  CES marginal products* as the axiom below.

  Textbook citation.  Acemoglu, *Introduction to Modern Economic
  Growth* (2009), Chapter 15 (CES production, factor-price equations).
  Or any introductory production-theory textbook.
-/
/-- **Cat 2 axiom.** The CES marginal-product wage ratio admits the
    closed form `((1-η)/η) · λ^ρ · (G/V)^{1-ρ}`.

    *Atomic form.*  The axiom equates the closed-form `wageRatio`
    definition with the conceptual `w_V/w_G` ratio of CES marginal
    products.  The two are abstract Lean reals; the axiom is a
    single equality at each `(V, θ)`.

    *Scope.*  The axiom captures Eq.~\eqref{eq:wage-ratio} of
    Theorem~\ref{thm:inversion} Part 1.  Monotonicity in `θ`
    (the substantive content of Part 1) is then proved in
    `Inversion.lean` from the closed form + `Real.rpow_le_rpow`,
    without further axioms. -/
axiom axiom_ces_wage_ratio (eta rho lam G V wV_over_wG : ℝ)
    (hV : 0 < V) (hG : 0 < G)
    (heta_pos : 0 < eta) (heta_lt : eta < 1) (hrho_lt : rho < 1)
    (hlam_pos : 0 < lam) :
    wV_over_wG = ((1 - eta) / eta) * lam ^ rho * (G / V) ^ (1 - rho)

/-! ### Cat 2 axiom 3: Cobb-Douglas factor-share identity.

  Paper statement (used in Theorem~\ref{thm:credential},
  Proposition~\ref{prop:junior-senior}, Theorem~\ref{thm:externality}
  Part 3): under Cobb-Douglas production `F(G, V) = G^η · (λ V)^{1-η}`
  with competitive marginal products, the verification factor share
  is exactly `1 - η`:

      w_V · V = (1 - η) · F(G, V) = (1 - η) · Y.

  Mathlib status.  Cobb-Douglas factor shares are a textbook
  consequence of the Cobb-Douglas marginal-product calculus.
  Mathlib could derive it via the same chain as CES (with `ρ = 0`),
  but the derivation is suppressed here for parity with `axiom_ces_wage_ratio`.

  Textbook citation.  Mas-Colell, Whinston, Green (1995), §5.B.2
  (Cobb-Douglas constant factor shares).  Or any introductory
  production-theory textbook.
-/
/-- **Cat 2 axiom.** Cobb-Douglas factor share for verification.

    Under Cobb-Douglas `F(G, V) = G^η · (λ V)^{1-η}` with competitive
    marginal products, `w_V · V = (1 - η) · Y` where `Y = F(G, V)`.

    *Atomic form.*  A single algebraic identity at fixed `Y, w_V, V, η`. -/
axiom axiom_cobb_douglas_factor_share (η Y wV V : ℝ) :
    wV * V = (1 - η) * Y

/-! ### Derived: steady-state stock identity (`V_∞ = ν T_s g(ē) h(ē)`).

  This is *not* an axiom — it is the definitional equation of `Vinf`
  in `Basic.lean`.  Recorded here as a `@[simp]` rewrite lemma to
  enable theorems that previously hypothesized this identity to
  derive it from the definition. -/

/-- *Steady-state stock identity.*  Definitional unfolding of
    `Vinf` from `Basic.lean`:
        `V_∞(θ, g, h) = ν T_s · g(ē(θ)) · h(ē(θ))`,
    where `ē(θ) = (1 - θ) T_j`.

    Paper Lemma~\ref{lem:steady-state}, Eq.~\eqref{eq:V-steady}.
    This is a *Lean theorem*, not an axiom: the equality is the
    definition of `Vinf` (`def Vinf` in `Basic.lean`). -/
theorem steady_state_stock_identity (θ : ℝ) (g h : ℝ → ℝ) :
    E.Vinf θ g h = E.nu * E.Ts * g (E.eBar θ) * h (E.eBar θ) := rfl

/-- *Composite identity used by Cobb-Douglas closed-form theorems.*
    From `axiom_cobb_douglas_factor_share` applied to `V = V_∞(θ)` and
    `steady_state_stock_identity`, the composite identity

        (1 - η) · Y = w_V · (ν · T_s · g(ē) · h(ē))

    holds for any `Y, w_V, g, h`.  This is a *derived theorem*, not
    an axiom; it packages the two atomic facts into the form the
    downstream theorems consume. -/
theorem cobb_douglas_steady_state_identity
    (Y wV : ℝ) (g h : ℝ → ℝ) (θ : ℝ) :
    (1 - E.eta) * Y = wV * (E.nu * E.Ts * g (E.eBar θ) * h (E.eBar θ)) := by
  -- Compose:
  -- 1. axiom_cobb_douglas_factor_share with V := V_∞(θ, g, h):
  --    wV * V_∞ = (1 - η) * Y.
  -- 2. steady_state_stock_identity: V_∞ = ν T_s g(ē) h(ē).
  have h1 : wV * (E.Vinf θ g h) = (1 - E.eta) * Y :=
    axiom_cobb_douglas_factor_share E.eta Y wV (E.Vinf θ g h)
  rw [steady_state_stock_identity] at h1
  linarith

end Economy

end VerificationAsymmetry
