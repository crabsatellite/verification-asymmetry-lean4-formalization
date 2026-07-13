/-
  VerificationAsymmetry/Axioms.lean

  Explicit Cat 2 (textbook-fact) and Cat 3 (paper-novel structural) axioms.

  Companion to: "Verification Asymmetry under AI Substitution:
  Wage-Ratio Inversion and Apprenticeship Thresholds" (Li, 2026).

  ## Soundness mandate

  The three Cat 2 axioms `axiom_euler_crs`, `axiom_ces_wage_ratio`,
  and `axiom_cobb_douglas_factor_share` require EXPLICIT antecedents
  (production-function shape, marginal-product identification,
  positivity); without antecedents these would be False-injectable.

  This file declares three Cat 3 paper-novel hypothesisPredicate
  predicates (`IsCRS`, `IsCobbDouglas`, `IsCES`) and three Cat 2
  textbook axioms whose hypotheses CONSUME those predicates plus
  Mathlib's `HasDerivAt` marginal-product identifications.  Every
  Cat 2 axiom requires its antecedents EXPLICITLY in the signature;
  no free-variable quantification injects False into the kernel.

  ## Encoding pattern

  Each axiom carries:
    * an atomic predicate / structural equation (no composite,
      multi-step content);
    * EXPLICIT antecedents (production-function shape, marginal-product
      identification, positivity);
    * a docstring with the textbook or paper-level citation.

  ## Trust profile (current)

    * Cat 2 (textbook):    3 — `axiom_euler_crs`,
                               `axiom_ces_wage_ratio`,
                               `axiom_cobb_douglas_factor_share`
                               (each with explicit antecedents).
    * Cat 3 (paper-novel): definitional hypothesisPredicate atoms
                           `IsCRS`, `IsCobbDouglas`, `IsCES`, plus
                           the carrier/structural-equation atoms
                           tracked in `Ledger.lean`.
-/

import VerificationAsymmetry.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace VerificationAsymmetry

namespace Economy

variable (E : Economy)

/-! ### Cat 3 paper-novel hypothesisPredicate atoms.

  These predicates encode paper-stipulative production-function shapes
  (Eq. `\label{eq:ces}` and its Cobb-Douglas / CRS specializations).
  They are Cat 3 paper-novel hypothesisPredicate definitional atoms;
  never closeable.
-/

/-- Paper-novel hypothesis predicate (Cat 3 hypothesisPredicate):
    `F` is homogeneous of degree one — constant returns to scale.

    Paper Theorem `\label{thm:decomp}` uses CRS to invoke Euler's
    identity. -/
def IsCRS (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ t G V : ℝ, 0 < t → F (t * G) (t * V) = t * F G V

/-- Paper-novel hypothesis predicate (Cat 3 hypothesisPredicate):
    `F` is Cobb-Douglas `F(G, V) = G^η · (λ V)^(1-η)` with share
    parameter `η ∈ (0, 1)` and verification-effectiveness `lam > 0`.

    Paper Theorem `\label{thm:credential}` proof uses this form for
    the verification factor share `(1-η)`. -/
def IsCobbDouglas (F : ℝ → ℝ → ℝ) (η lam : ℝ) : Prop :=
  ∀ G V : ℝ, 0 < G → 0 < V →
    F G V = G ^ η * (lam * V) ^ (1 - η)

/-- Paper-novel hypothesis predicate (Cat 3 hypothesisPredicate):
    `F` is CES with parameters `(η, ρ, λ)`,
    `F(G, V) = (η G^ρ + (1-η)(λ V)^ρ)^(1/ρ)`.

    Paper Eq. `\label{eq:ces}`.

    *Scope of meaningfulness.*  The predicate is mathematically
    meaningful only when `ρ ≠ 0`; at `ρ = 0`, Mathlib's
    `Real.rpow x 0 = 1` makes the right-hand side degenerate to
    the constant `1`, so the predicate would assert `F G V = 1`
    for all positive `(G, V)` — degenerate and NOT the
    Cobb-Douglas limit (which is recovered as `ρ → 0` via
    continuous extension, not by direct `ρ = 0` substitution).
    Call sites add `ρ ≠ 0` as an explicit antecedent —
    `axiom_ces_wage_ratio` carries `hrho_ne : rho ≠ 0`.  The
    Cobb-Douglas factor share is handled by the separate
    `IsCobbDouglas` predicate / `axiom_cobb_douglas_factor_share`
    axiom. -/
def IsCES (F : ℝ → ℝ → ℝ) (η rho lam : ℝ) : Prop :=
  ∀ G V : ℝ, 0 < G → 0 < V →
    F G V = (η * G ^ rho + (1 - η) * (lam * V) ^ rho) ^ (1 / rho)

/-! ### Cat 2 axiom 1: Euler's identity for CRS production.

  Paper statement (Theorem~\ref{thm:decomp}): for any production
  function `F : ℝ_+^2 → ℝ_+` that is homogeneous of degree one
  (constant returns to scale), Euler's identity gives the additive
  factor-share decomposition

      F(G, V) = (∂F/∂G) · G + (∂F/∂V) · V.

  Under competitive markets `w_G = ∂F/∂G`, `w_V = ∂F/∂V`, this is

      F(G, V) = w_G · G + w_V · V.

  Mathlib status.  Mathlib provides `Real.rpow`-level machinery for
  individual homogeneous functions (e.g. `Real.rpow_mul`) but no
  generic Euler-identity theorem for an abstract `F : ℝ × ℝ → ℝ`
  parameter with a homogeneity hypothesis.  Formalizing the general
  Euler theorem requires either `MeasureTheory`-style integration
  along radial rays or a differential-geometric treatment of
  homogeneous functions; neither is in scope.

  Citations.  Original source: Euler, L., 1755.  *Institutiones
  Calculi Differentialis* (original homogeneous-function theorem).
  Modern textbook reference: Mas-Colell, A., Whinston, M.D., Green,
  J.R., 1995.  *Microeconomic Theory*, §5.B.2 Theorem M.B.2 (Euler's
  theorem for constant-returns-to-scale technologies).

  ## Soundness antecedents

  The axiom requires:
    * `hCRS : IsCRS F` — the homogeneity-of-degree-one hypothesis;
    * `h_wG : HasDerivAt (fun x => F x V) wG G` — `w_G` is the
      partial derivative of `F` in `G` at `(G, V)`;
    * `h_wV : HasDerivAt (fun y => F G y) wV V` — `w_V` is the
      partial derivative of `F` in `V` at `(G, V)`;
    * `hG_pos : 0 < G`, `hV_pos : 0 < V` — positivity at the
      evaluation point.

  Without these antecedents the axiom would be False-injectable.
-/
/-- **Cat 2 axiom.** Euler's identity for CRS production functions.

    For any homogeneous-of-degree-one `F : ℝ → ℝ → ℝ` evaluated at
    `(G, V)` with marginal-product wage rates `w_G, w_V`,

        F(G, V) = w_G · G + w_V · V.

    Stated as an axiom (Cat 2, Euler 1755 / MWG 1995 §5.B.2 Theorem).
    The antecedents `IsCRS F`, `HasDerivAt`-bound `wG, wV`, and
    positivity `0 < G`, `0 < V` make the axiom sound. -/
axiom axiom_euler_crs
    (F : ℝ → ℝ → ℝ) (G V wG wV : ℝ)
    (hCRS : IsCRS F)
    (h_wG : HasDerivAt (fun x => F x V) wG G)
    (h_wV : HasDerivAt (fun y => F G y) wV V)
    (hG_pos : 0 < G) (hV_pos : 0 < V) :
    F G V = wG * G + wV * V

/-! ### Cat 2 axiom 2: CES marginal-product wage-ratio closed form.

  Paper statement (Theorem~\ref{thm:inversion} Part 1,
  Eq.~\eqref{eq:wage-ratio}): for CES production
  `F(G, V) = (η G^ρ + (1-η)(λ V)^ρ)^{1/ρ}` with competitive marginal
  products `w_G = ∂F/∂G`, `w_V = ∂F/∂V`, the wage ratio admits the
  closed form

      w_V / w_G = ((1-η)/η) · λ^ρ · (G/V)^{1-ρ}.

  This is substantive production-function calculus — the CES
  marginal-product derivation — and is encoded as a genuine Cat 2
  axiom.  The axiom is CONSUMED by
  `wageRatio_eq_ces_marginal_product_ratio` (Inversion.lean), which
  establishes that the Lean `wageRatio` closed-form def IS the CES
  marginal-product wage ratio — making the axiom genuinely
  Lean-load-bearing (verifiable by
  `#print axioms wageRatio_eq_ces_marginal_product_ratio`).

  Mathlib status.  Mathlib provides `Real.rpow` calculus but no
  generic CES marginal-product wage-ratio theorem for an abstract
  `F : ℝ → ℝ → ℝ` parameter with a CES-shape hypothesis; the
  derivation from `HasDerivAt`-bound partial derivatives is suppressed
  here and located in the external textbook reference.

  Citations.  Original source: Arrow, K.J., Chenery, H.B., Minhas,
  B.S., Solow, R.M., 1961.  Capital-Labor Substitution and Economic
  Efficiency.  *Review of Economics and Statistics* 43(3), 225-250
  (original CES production function paper).  Modern textbook
  reference: Acemoglu, D., 2009.  *Introduction to Modern Economic
  Growth*, Chapter 15 (CES production factor-price equations).

  ## Soundness antecedents

  The axiom requires:
    * `hCES : IsCES F η rho lam` — the CES shape hypothesis;
    * `h_wG : HasDerivAt (fun x => F x V) wG G` — marginal-product
      identification of `wG`;
    * `h_wV : HasDerivAt (fun y => F G y) wV V` — marginal-product
      identification of `wV`;
    * `h_wG_pos : 0 < wG` — positivity of the generation wage
      (so the wage ratio `wV / wG` is well-defined);
    * positivity of `G`, `V`, `eta`, `lam`;
    * shape constraints `0 < eta < 1`, `rho < 1`, `rho ≠ 0`.

  Without these antecedents the axiom would be False-injectable
  (counterexample `F := const 0`, `eta = rho = lam = G = V = wG =
  wV = 0` would inject `0 = 0` only vacuously; with a free `wG = 0`
  the ratio `wV / wG` is malformed — the `0 < wG` antecedent rules
  this out).
-/
/-- **Cat 2 axiom.** CES marginal-product wage-ratio closed form.

    For CES production with parameters `(η, ρ, λ)` and competitive
    marginal-product wages `w_G, w_V`,

        w_V / w_G = ((1-η)/η) · λ^ρ · (G/V)^{1-ρ}.

    Stated as an axiom (Cat 2, Arrow-Chenery-Minhas-Solow 1961 /
    Acemoglu 2009 §15).  The antecedents `IsCES F η rho lam`,
    `HasDerivAt`-bound `wG, wV`, positivity `0 < wG`, `0 < G`,
    `0 < V`, `0 < η`, `0 < lam`, and shape constraints `η < 1`,
    `ρ < 1`, `ρ ≠ 0` make the axiom sound. -/
axiom axiom_ces_wage_ratio
    (F : ℝ → ℝ → ℝ) (η rho lam G V wG wV : ℝ)
    (hCES : IsCES F η rho lam)
    (h_wG : HasDerivAt (fun x => F x V) wG G)
    (h_wV : HasDerivAt (fun y => F G y) wV V)
    (h_wG_pos : 0 < wG)
    (hG : 0 < G) (hV : 0 < V)
    (hη_pos : 0 < η) (hη_lt : η < 1)
    (hrho_lt : rho < 1) (hrho_ne : rho ≠ 0)
    (hlam_pos : 0 < lam) :
    wV / wG = ((1 - η) / η) * lam ^ rho * (G / V) ^ (1 - rho)

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

  Citations.  Original source: Cobb, C.W., Douglas, P.H., 1928.  A
  Theory of Production.  *American Economic Review* 18(1), 139-165
  (original Cobb-Douglas production function paper).  Modern textbook
  reference: Mas-Colell, A., Whinston, M.D., Green, J.R., 1995.
  *Microeconomic Theory*, §5.B.2 Theorem M.B.2 (Cobb-Douglas constant
  factor shares).

  ## Soundness antecedents

  The axiom requires:
    * `hCD : IsCobbDouglas F η lam` — the CD shape hypothesis;
    * `h_wV : HasDerivAt (fun y => F G y) wV V` —
      marginal-product identification of `wV`;
    * `hY : Y = F G V` — definitional bridge;
    * positivity of `G`, `V`, `eta`, `lam`;
    * shape constraints `0 < eta < 1`.

  ## Antecedent parity with `axiom_ces_wage_ratio`

  This axiom carries a STRICTLY SMALLER antecedent set than its
  CES sibling `axiom_ces_wage_ratio` — it omits the generation-side
  derivative `h_wG : HasDerivAt (fun x => F x V) wG G`, the
  generation-wage positivity `h_wG_pos : 0 < wG`, and the CES
  substitution-exponent constraints `rho < 1`, `rho ≠ 0`.  This
  asymmetry is JUSTIFIED, not an oversight, by the different
  conclusion shape:

    * `axiom_ces_wage_ratio` concludes a wage RATIO `wV / wG = …`.
      The ratio is only well-defined with `wG ≠ 0`, so `h_wG_pos`
      is load-bearing; and `wG` itself must be marginal-product-
      identified, so `h_wG` is required.  The CES form carries an
      explicit substitution exponent `ρ`, so `rho < 1`, `rho ≠ 0`
      pin the shape.

    * `axiom_cobb_douglas_factor_share` concludes a factor-share
      PRODUCT `wV · V = (1 - η) · Y` — no generation-side wage `wG`
      appears, so neither `h_wG` nor `h_wG_pos` is needed.  The
      Cobb-Douglas form has no substitution exponent (it is the
      `ρ → 0` limit), so no `rho` constraint applies.

  Soundness check.  Under `IsCobbDouglas F η lam`, the function
  `fun y => F G y` agrees with `fun y => G^η (λ y)^{1-η}` on
  `y > 0` (a neighborhood of `V > 0`).  By `HasDerivAt`
  congruence-on-a-neighborhood and uniqueness of the derivative,
  `wV` is FORCED to the Cobb-Douglas marginal product
  `∂/∂y [G^η (λ y)^{1-η}]|_{y=V} = (1-η) · F(G,V) / V = (1-η) Y / V`,
  whence `wV · V = (1-η) Y`.  No counterexample exists with the
  current antecedents: the conclusion is uniquely determined, so
  the smaller antecedent set is sound.
-/
/-- **Cat 2 axiom.** Cobb-Douglas factor share for verification.

    Under Cobb-Douglas `F(G, V) = G^η · (λ V)^{1-η}` with competitive
    marginal products, `w_V · V = (1 - η) · Y` where `Y = F(G, V)`.
    Antecedents make the axiom sound. -/
axiom axiom_cobb_douglas_factor_share
    (F : ℝ → ℝ → ℝ) (η lam G V wV Y : ℝ)
    (hCD : IsCobbDouglas F η lam)
    (h_wV : HasDerivAt (fun y => F G y) wV V)
    (hY : Y = F G V)
    (hG_pos : 0 < G) (hV_pos : 0 < V)
    (hη_pos : 0 < η) (hη_lt : η < 1)
    (hlam_pos : 0 < lam) :
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

/-- *Composite identity used by Cobb-Douglas closed-form theorems
    (parametric / bridge form).*

    Given the Cobb-Douglas factor share `w_V · V_∞ = (1 - η) · Y`
    (the conclusion of `axiom_cobb_douglas_factor_share` under
    appropriate antecedents) together with the definitional
    `steady_state_stock_identity`, we obtain
        `(1 - η) · Y = w_V · (ν · T_s · g(ē) · h(ē))`.

    Parametric form: takes the bridge
    `hCDshare : w_V · V_∞ = (1-η) · Y` as a hypothesis. -/
theorem cobb_douglas_steady_state_identity
    (Y wV : ℝ) (g h : ℝ → ℝ) (θ : ℝ)
    (hCDshare : wV * E.Vinf θ g h = (1 - E.eta) * Y) :
    (1 - E.eta) * Y = wV * (E.nu * E.Ts * g (E.eBar θ) * h (E.eBar θ)) := by
  -- Unfold the steady-state stock identity and rewrite.
  rw [steady_state_stock_identity] at hCDshare
  linarith

/-- *Composite identity used by Cobb-Douglas closed-form theorems
    (axiom-discharged form).*

    The bridge `wV * V_∞ θ g h = (1-η) * Y` is here derived from
    `axiom_cobb_douglas_factor_share` (Cat 2 MWG 1995 §5.B.2)
    together with `steady_state_stock_identity` and the
    definitional bridge `Y = F G (E.Vinf θ g h)`.

    Consumes `axiom_cobb_douglas_factor_share` — verifiable by
    `#print axioms cobb_douglas_steady_state_identity_from_axiom`. -/
theorem cobb_douglas_steady_state_identity_from_axiom
    (F : ℝ → ℝ → ℝ) (η lam G Y wV : ℝ) (g h : ℝ → ℝ) (θ : ℝ)
    (hCD : IsCobbDouglas F η lam)
    (h_wV : HasDerivAt (fun y => F G y) wV (E.Vinf θ g h))
    (hY : Y = F G (E.Vinf θ g h))
    (hG_pos : 0 < G) (hVinf_pos : 0 < E.Vinf θ g h)
    (hη_pos : 0 < η) (hη_lt : η < 1)
    (hlam_pos : 0 < lam)
    (hEta : η = E.eta) :
    (1 - E.eta) * Y
      = wV * (E.nu * E.Ts * g (E.eBar θ) * h (E.eBar θ)) := by
  have h_axiom :=
    axiom_cobb_douglas_factor_share F η lam G (E.Vinf θ g h) wV Y
      hCD h_wV hY hG_pos hVinf_pos hη_pos hη_lt hlam_pos
  -- h_axiom : wV * E.Vinf θ g h = (1 - η) * Y
  rw [hEta] at h_axiom
  exact E.cobb_douglas_steady_state_identity Y wV g h θ h_axiom

end Economy

end VerificationAsymmetry
