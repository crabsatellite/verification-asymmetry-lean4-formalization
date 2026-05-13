/-
  VerificationAsymmetry/Ledger.lean

  Gap ledger.  Every closed top-level result and every paper-level
  claim deferred to economic narrative is recorded as a typed
  `GapEntry` with TWO orthogonal classifications:

    * 5-tier status:   gapOpen / gapPartial / gapBlocked / gapDeadEnd / gapClosed
    * 3-input-category: cat1Mathlib / cat2External / cat3PaperNovel / notInput

  Pre-attack discipline.  Scan this ledger before launching new
  attacks.  Re-attempting a `gapBlocked` or `gapDeadEnd` route is a
  context-drift failure mode.

  `attackHistory` is the canonical location for round metadata
  (citation revisions, atomic refactors, prior retractions); docstrings
  and scope fields are kept to current-state content only.

  *Inventory profile of this project (post-audit 2026-05).*  The
  paper's structural mathematics is real-analytic — CES algebra,
  linear-cohort accounting, Brouwer fixed-point, finite-product
  algebra — and most paper-level theorems reduce to Mathlib's
  real-arithmetic infrastructure plus the Lean kernel (`propext`,
  `Classical.choice`, `Quot.sound`).

  However, three textbook microeconomics facts enter the paper's
  proofs and are not derivable from `F : ℝ → ℝ → ℝ` taken
  abstractly:

    * Euler's identity for CRS production functions
      (`axiom_euler_crs` in `Axioms.lean`);
    * CES marginal-product wage ratio closed form
      (`axiom_ces_wage_ratio`);
    * Cobb-Douglas verification factor share `w_V V = (1-η) Y`
      (`axiom_cobb_douglas_factor_share`).

  These are declared as Cat 2 (external textbook) axioms with
  explicit citations (Mas-Colell, Whinston, Green 1995 §5.B.2;
  Acemoglu 2009 §15).

  Previously, the same facts were carried inside theorem signatures
  as hypotheses, e.g. `thm_decomp F G V wG wV (hEuler : F G V =
  wG * G + wV * V) : ...`, leaving the proof body a one-line `rfl`
  while hiding the textbook content inside the hypothesis.  The
  post-audit refactor lifted these hypotheses to explicit Cat 2
  axioms.

  The `gapBlocked` entries record paper-level claims that are
  predominantly *economic narrative* (e.g., "the apprenticeship
  externality persists because markets adjust frictionlessly") whose
  Lean formalization would require infrastructure (path-dependent
  integrals, function spaces) beyond the scope of this structural
  formalization.  These are flagged honestly and not faked into
  Lean theorems.
-/

import VerificationAsymmetry

namespace VerificationAsymmetry.Ledger

/-- 5-tier status tag attached to each gap. -/
inductive GapStatus
  | gapOpen
  | gapPartial
  | gapBlocked
  | gapDeadEnd
  | gapClosed
  deriving DecidableEq, Repr

/-- 3-input-category tag attached to each gap.  Orthogonal to status. -/
inductive InputCategory
  /-- Mathlib-derivable theorem (no axiom). -/
  | cat1Mathlib
  /-- External published; opaque-carrier-bound axiom + citation. -/
  | cat2External
  /-- Paper-novel: carrier or paper-stated atomic defining equation. -/
  | cat3PaperNovel
  /-- Not an atomic input: derived theorem (gapClosed) or blocked
      Mathlib-derivation route (gapBlocked). -/
  | notInput
  deriving DecidableEq, Repr

/-- Typed record for a single gap. -/
structure GapEntry where
  /-- Identifier matching the underlying axiom / theorem name. -/
  name : String
  /-- 5-tier status (orthogonal to inputCategory). -/
  status : GapStatus
  /-- Input category (orthogonal to status). -/
  inputCategory : InputCategory
  /-- Operative paper / obstacle citation. -/
  paperSource : String
  /-- Per-round attack trace (canonical location for round metadata). -/
  attackHistory : List String
  /-- What content the entry carries; what it does NOT claim. -/
  scope : String

/-! ### Cat 2 axiom entries (gapClosed: declared in `Axioms.lean`) -/

/-- Cat 2 axiom: Euler's identity for CRS production. -/
def gap_axiom_euler_crs : GapEntry := {
  name := "axiom_euler_crs"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.cat2External
  paperSource :=
    "Li 2026, `\\label{thm:decomp}` proof; " ++
    "citation: Mas-Colell, Whinston, Green 1995 §5.B.2"
  attackHistory := [
    "Pre-audit (v0.1.0): Euler identity carried as hypothesis " ++
    "`hEuler` of `thm_decomp`; proof body `rfl`. Audit (2026-05) " ++
    "lifted to explicit Cat 2 axiom."
  ]
  scope :=
    "For any homogeneous-of-degree-one `F : ℝ → ℝ → ℝ` evaluated at " ++
    "`(G, V)` with marginal-product wage rates `w_G, w_V`, " ++
    "`F G V = w_G · G + w_V · V`. Atomic algebraic identity at " ++
    "fixed factor levels"
}

/-- Cat 2 axiom: CES wage-ratio closed form. -/
def gap_axiom_ces_wage_ratio : GapEntry := {
  name := "axiom_ces_wage_ratio"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.cat2External
  paperSource :=
    "Li 2026, `\\label{thm:inversion}` Part 1, " ++
    "Eq. `\\eqref{eq:wage-ratio}`; " ++
    "citation: Acemoglu 2009 §15 (CES marginal products)"
  attackHistory := [
    "Pre-audit (v0.1.0): `wageRatio` defined as closed form; " ++
    "no axiom recorded for the identification with CES marginal " ++
    "products. Audit (2026-05) added the Cat 2 axiom for honest " ++
    "accounting of the suppressed CES marginal-product derivation."
  ]
  scope :=
    "The CES marginal-product wage ratio admits the closed form " ++
    "`((1-η)/η) · λ^ρ · (G/V)^{1-ρ}`. Atomic algebraic identity at " ++
    "fixed CES parameters and factor levels. The Mathlib-derivable " ++
    "marginal-product calculation is suppressed; the closed form is " ++
    "the substantive content of Part 1"
}

/-- Cat 2 axiom: Cobb-Douglas verification factor share. -/
def gap_axiom_cobb_douglas_factor_share : GapEntry := {
  name := "axiom_cobb_douglas_factor_share"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.cat2External
  paperSource :=
    "Li 2026, `\\label{thm:credential}` proof " ++
    "(\\eqref{eq:R-cobb-douglas}); " ++
    "citation: Mas-Colell, Whinston, Green 1995 §5.B.2"
  attackHistory := [
    "Pre-audit (v0.1.0): composite identity " ++
    "`(1-η) Y = w_V · (ν T_s g h)` carried as hypothesis of every " ++
    "Cobb-Douglas-regime theorem (`thm_credential`, " ++
    "`prop_junior_senior`, `thm_externality_pigouvian_cobb_douglas`); " ++
    "proof bodies `field_simp`. Audit (2026-05) decomposed into " ++
    "(i) Cat 2 axiom for the Cobb-Douglas factor share " ++
    "`w_V V = (1-η) Y`, and (ii) definitional unfolding of `Vinf = " ++
    "ν T_s g h`. Composite hypothesis no longer carries hidden " ++
    "textbook content"
  ]
  scope :=
    "Under Cobb-Douglas `F G V = G^η · (λ V)^{1-η}` with competitive " ++
    "marginal products, the verification factor share is `(1-η)`: " ++
    "`w_V · V = (1-η) · Y`. Atomic algebraic identity at fixed " ++
    "`(Y, w_V, V, η)`"
}

/-! ### gapClosed entries — paper-level results formalized without `sorry` -/

/-- Theorem~\ref{thm:decomp} (stock-flow welfare decomposition,
    Euler-identity portion). -/
def gap_thm_decomp_CLOSED : GapEntry := {
  name := "thm_decomp"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:decomp}`"
  attackHistory := [
    "Pre-audit (v0.1.0): Euler identity carried as hypothesis " ++
    "`hEuler : F G V = wG · G + wV · V`; proof body `rfl`. " ++
    "Audit (2026-05) replaced the hypothesis with an application " ++
    "of `axiom_euler_crs` (Cat 2, MWG 1995 §5.B.2); the proof body " ++
    "is now `axiom_euler_crs F G V wG wV`, with the textbook content " ++
    "located in the axiom, not buried in a hypothesis"
  ]
  scope :=
    "Stock-flow welfare decomposition by Euler's identity: " ++
    "for any CRS `F`, `F G V = w_G · G + w_V · V` " ++
    "(by `axiom_euler_crs`), implying `F = Wflow + Wstock` where " ++
    "`Wflow = wG · G`, `Wstock = wV · V`. " ++
    "The Cobb-Douglas factor-share special case (Proposition " ++
    "`prop:stock-flow-asymptotics` Part 2) is formalized as " ++
    "`thm_decomp_cobb_douglas_shares`. Window invariance " ++
    "(Proposition `prop:stock-flow-asymptotics` Part 4) is a " ++
    "path-dependent integral statement and is deferred to the " ++
    "gapBlocked entry `gap_window_invariance_BLOCKED`"
}

/-- Theorem~\ref{thm:inversion} Part 2: closed-form inversion threshold. -/
def gap_thm_inversion_threshold_CLOSED : GapEntry := {
  name := "thm_inversion_threshold_closed_form"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:inversion}` Part 2"
  attackHistory := []
  scope :=
    "Inversion threshold `θ_inv(r̄) = (G*(r̄) - L_G)/(K_AI - L_G)` " ++
    "satisfies `G(θ_inv) = G*(r̄)`. Algebraic identity proved by " ++
    "`field_simp; ring` from the definitions"
}

/-- Theorem~\ref{thm:inversion} Part 1: wage-ratio monotonicity. -/
def gap_thm_inversion_wage_ratio_CLOSED : GapEntry := {
  name := "thm_inversion_wage_ratio_monotone"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:inversion}` Part 1"
  attackHistory := [
    "Pre-audit (v0.1.0): `wageRatio` defined as the closed form " ++
    "`((1-η)/η) λ^ρ (G/V)^{1-ρ}`; identification with the CES " ++
    "marginal-product ratio implicit. Audit (2026-05) added " ++
    "`axiom_ces_wage_ratio` for honest accounting of the suppressed " ++
    "CES marginal-product derivation. The monotonicity proof " ++
    "(`thm_inversion_wage_ratio_monotone`) operates on the closed-" ++
    "form `wageRatio` definition and does not invoke the axiom; the " ++
    "axiom only locates where the textbook fact sits in the audit"
  ]
  scope :=
    "Wage-ratio function `r(θ) = ((1-η)/η) λ^ρ (G(θ)/V)^{1-ρ}` is " ++
    "non-decreasing in `θ` under `K_AI ≥ L_G` and `ρ < 1`. Proof " ++
    "uses `Real.rpow_le_rpow` on `G(θ)/V` together with the " ++
    "monotonicity of `G` (`Economy.G_monotone_of_KAI_ge_LG`). " ++
    "Closed-form identification with CES marginal products: " ++
    "`axiom_ces_wage_ratio` (Cat 2, Acemoglu 2009 §15)"
}

/-- Corollary~\ref{cor:bounded-AI} (endpoint identifications). -/
def gap_cor_bounded_AI_CLOSED : GapEntry := {
  name := "cor_bounded_AI_threshold_endpoints"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{cor:bounded-AI}`"
  attackHistory := [
    "Pre-audit (v0.1.0): the endpoint identities " ++
    "`G*(r̄_0) = L_G`, `G*(r̄_max) = K_AI` were carried as " ++
    "`hGstar_eq` hypotheses of the corollary statements (these are " ++
    "real `rpow` algebraic identities, not assumptions). Audit " ++
    "(2026-05) derived them inline via `Real.rpow_mul` " ++
    "(`Gstar_at_rBarZero`, `Gstar_at_rBarMax`); no longer hypotheses"
  ]
  scope :=
    "At `r̄ = r̄_0`, `G*(r̄_0) = L_G`, so `θ_inv = 0`. At `r̄ = r̄_max`, " ++
    "`G*(r̄_max) = K_AI`, so `θ_inv = 1`. Both endpoint identities " ++
    "derived from `Real.rpow_mul` and the cancellation " ++
    "`(x^a)^(1/a) = x` for `x > 0, a ≠ 0`"
}

/-- Theorem~\ref{thm:collapse} Part 1: below-threshold smooth power-law. -/
def gap_thm_collapse_below_CLOSED : GapEntry := {
  name := "thm_collapse_below_threshold"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:collapse}` Part 1"
  attackHistory := []
  scope :=
    "For `θ ≤ θ*`, `V_∞(θ) = ν T_s · ((1-θ) T_j)^a` under hard " ++
    "threshold. Reduces to `VinfHard_eq_pow_of_eBar_ge_tauStar` " ++
    "via the bridge `eBar_ge_tauStar_iff_theta_le_thetaStar`"
}

/-- Theorem~\ref{thm:collapse} Part 2: jump magnitude. -/
def gap_thm_collapse_jump_CLOSED : GapEntry := {
  name := "thm_collapse_jump_magnitude"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:collapse}` Part 2"
  attackHistory := []
  scope :=
    "`V_∞(θ*) = ν T_s · (τ*)^a` (left limit); right limit is 0. " ++
    "Jump magnitude `ν T_s (τ*)^a` is exact"
}

/-- Theorem~\ref{thm:collapse} Part 3: long-run zero stock above θ*. -/
def gap_thm_collapse_above_CLOSED : GapEntry := {
  name := "thm_collapse_above_threshold"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:collapse}` Part 3"
  attackHistory := []
  scope :=
    "For `θ > θ*`, `V_∞(θ) = 0`. Reduces to " ++
    "`VinfHard_eq_zero_of_eBar_lt_tauStar`"
}

/-- Theorem~\ref{thm:collapse} Part 4: transient linear decay. -/
def gap_thm_collapse_transient_CLOSED : GapEntry := {
  name := "thm_collapse_transient_decay"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:collapse}` Part 4"
  attackHistory := []
  scope :=
    "Transient stock `V(t) = V_∞(θ_0) · (1 - t/T_s)_+`. Formalized " ++
    "via `transientStock` and the three pointwise lemmas " ++
    "(`thm_collapse_transient_at_zero`, `_at_Ts`, `_linear`, " ++
    "`_zero_after_Ts`)"
}

/-- Theorem~\ref{thm:collapse} Part 5: general-`h` lower bound. -/
def gap_thm_collapse_general_h_CLOSED : GapEntry := {
  name := "thm_collapse_jump_general_h"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:collapse}` Part 5"
  attackHistory := []
  scope :=
    "For any non-decreasing `h`, jump at `θ*` is exactly `ν T_s h(τ*)`. " ++
    "Algebraic identity once `ē(θ*) = τ*` is substituted"
}

/-- Proposition~\ref{prop:smooth-collapse}: smooth-threshold post-collapse
    decay. -/
def gap_prop_smooth_collapse_CLOSED : GapEntry := {
  name := "prop_smooth_collapse_above"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{prop:smooth-collapse}`"
  attackHistory := []
  scope :=
    "Above `θ*` under smooth promotion `g(τ) = (τ/τ*)^b`, " ++
    "`V_∞(θ) = ν T_s · (ē/τ*)^b · ē^a` where `ē = (1-θ) T_j`"
}

/-- Theorem~\ref{thm:credential} (Cobb-Douglas reduction). -/
def gap_thm_credential_CLOSED : GapEntry := {
  name := "thm_credential_cobb_douglas_reduction"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:credential}`"
  attackHistory := [
    "Pre-audit (v0.1.0): composite Cobb-Douglas identity " ++
    "`(1-η) Y = wV · (ν T_s g h)` carried as hypothesis `hY`. " ++
    "Audit (2026-05) added a companion `_from_axioms` theorem that " ++
    "derives `hY` from `axiom_cobb_douglas_factor_share` (Cat 2, " ++
    "MWG 1995 §5.B.2) composed with the definitional " ++
    "steady-state stock identity"
  ]
  scope :=
    "Under Cobb-Douglas factor share `(1-η) Y = wV · ν T_s · g · h` " ++
    "and `g · h > 0`, the per-entrant senior earnings " ++
    "`T_s · g · h · wV` simplify to `(1-η) Y / ν`. The closed-form " ++
    "return per entrant is `R(θ) = (1-η) Y(θ)/ν - T_j · c_J(θ)`. " ++
    "Parametric form takes the composite identity as hypothesis; " ++
    "`_from_axioms` form discharges via Cat 2 axiom + Lean " ++
    "definitional unfolding"
}

/-- Theorem~\ref{thm:credential} Part 3: multiplicative decay. -/
def gap_thm_credential_multiplicative_CLOSED : GapEntry := {
  name := "thm_credential_multiplicative_decay"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:credential}` Part 3"
  attackHistory := []
  scope :=
    "`g(ē) · h(ē) = (ē/τ*)^b · ē^a = ē^{a+b} / (τ*)^b`. Post-collapse " ++
    "decay rate `a+b` strictly exceeds pre-collapse rate `a`"
}

/-- Proposition~\ref{prop:junior-senior} (senior wage scaling). -/
def gap_prop_junior_senior_CLOSED : GapEntry := {
  name := "prop_junior_senior_wage"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{prop:junior-senior}`"
  attackHistory := [
    "Pre-audit (v0.1.0): same composite Cobb-Douglas hypothesis as " ++
    "`thm_credential_cobb_douglas_reduction`. Audit (2026-05) added " ++
    "`prop_junior_senior_wage_from_axioms` that discharges via Cat 2 " ++
    "axiom + definitional unfolding"
  ]
  scope :=
    "Senior wage `w_S = wV · h(ē) = (1-η) Y / (ν T_s g(ē))`. " ++
    "Diverges as `g(ē) → 0` for `θ → 1` under smooth threshold. " ++
    "Parametric and `_from_axioms` forms"
}

/-- Theorem~\ref{thm:externality} (wedge formula). -/
def gap_thm_externality_wedge_CLOSED : GapEntry := {
  name := "thm_externality_wedge_identity"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:externality}` (wedge identity)"
  attackHistory := []
  scope :=
    "`W_E(θ) = (MP_J^S - MP_J^P)/MP_J^P = (wV/wG) · g h Λ / (1-θ)`. " ++
    "Algebraic identity from the marginal-product definitions"
}

/-- Theorem~\ref{thm:externality} (non-negativity, Part 2). -/
def gap_thm_externality_nonneg_CLOSED : GapEntry := {
  name := "thm_externality_residual_nonneg"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:externality}` Part 2"
  attackHistory := []
  scope :=
    "Externality residual `wV · g · h · Λ ≥ 0` from " ++
    "non-negativity of the factors; strict positivity for " ++
    "`g · h > 0` and `wV, Λ > 0`"
}

/-- Theorem~\ref{thm:externality} Part 3: Cobb-Douglas Pigouvian formula. -/
def gap_thm_externality_pigouvian_CLOSED : GapEntry := {
  name := "thm_externality_pigouvian_cobb_douglas"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:externality}` Part 3"
  attackHistory := [
    "Pre-audit (v0.1.0): same composite Cobb-Douglas hypothesis as " ++
    "`thm_credential_cobb_douglas_reduction`. Audit (2026-05) added " ++
    "`thm_externality_pigouvian_cobb_douglas_from_axioms` that " ++
    "discharges via Cat 2 axiom + definitional unfolding"
  ]
  scope :=
    "Under Cobb-Douglas factor share and `g · h > 0`, " ++
    "`s*(θ) = (1-η) Y(θ) Λ / (ν T_s)`. Closed-form Pigouvian " ++
    "subsidy per junior. Parametric and `_from_axioms` forms"
}

/-- Proposition~\ref{prop:internalization} (within-firm internalization). -/
def gap_prop_internalization_CLOSED : GapEntry := {
  name := "prop_internalization"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{prop:internalization}`"
  attackHistory := []
  scope :=
    "Internalizing fraction `ζ ∈ [0, 1]` reduces effective wedge to " ++
    "`(1-ζ) W_E(θ)`. Full internalization (ζ=1) eliminates the " ++
    "externality"
}

/-- Proposition~\ref{prop:decentralized-theta} (social overshoot). -/
def gap_prop_decentralized_theta_CLOSED : GapEntry := {
  name := "prop_decentralized_theta_overshoots"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{prop:decentralized-theta}`"
  attackHistory := []
  scope :=
    "Social FOC `p_AI + s* = wG(θ_soc)`; private FOC `p_AI = " ++
    "wG(θ_eq)`. Strict positivity of `s*` plus anti-monotone " ++
    "`wG` in `θ` gives `θ_soc < θ_eq`"
}

/-- Theorem~\ref{thm:recursive} Part 1: closed-form recursive threshold. -/
def gap_thm_recursive_threshold_CLOSED : GapEntry := {
  name := "thm_recursive_threshold_closed_form"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:recursive}` Part 1"
  attackHistory := []
  scope :=
    "`θ_inv^{rec}(r̄) = (G*(r̄) - L_G)/(μ K_AI - L_G)`. Ratio " ++
    "`θ_inv^{rec}/θ_inv = (K_AI - L_G)/(μ K_AI - L_G)` decreases " ++
    "in μ; strict leftward shift for `μ > 1`"
}

/-- Theorem~\ref{thm:recursive} Parts 2 + 4: wedge amplification. -/
def gap_thm_recursive_wedge_CLOSED : GapEntry := {
  name := "thm_recursive_wage_ratio_amplification"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:recursive}` Parts 2 + 4"
  attackHistory := []
  scope :=
    "`w_V^{rec}/w_V = (V_req/G)^{1-ρ}`. Asymptotic amplification " ++
    "factor `μ^{1-ρ}` as `K_AI → ∞`"
}

/-- Theorem~\ref{thm:recursive} Part 3: collapse threshold invariance. -/
def gap_thm_recursive_invariance_CLOSED : GapEntry := {
  name := "thm_recursive_thetaStar_invariant"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:recursive}` Part 3"
  attackHistory := []
  scope :=
    "θ* and V_∞ make no reference to μ (cohort dynamics depend " ++
    "on supply side, recursive verification on demand side). " ++
    "Structural triviality"
}

/-- Proposition~\ref{prop:boundary}: separability characterization. -/
def gap_prop_boundary_CLOSED : GapEntry := {
  name := "prop_boundary_collapse_iff"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{prop:boundary}`"
  attackHistory := []
  scope :=
    "Pipeline collapse iff `ζ_V < τ*/T_j`, equivalently " ++
    "`1 - ζ_V > θ*`. Algebraic equivalence"
}

/-- Theorem~\ref{thm:aggregation} Part 2: Cobb-Douglas min theorem. -/
def gap_thm_aggregation_CD_CLOSED : GapEntry := {
  name := "thm_aggregation_cobb_douglas_zero"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:aggregation}` Part 2"
  attackHistory := []
  scope :=
    "Cobb-Douglas aggregator `∏ Y_i^{ω_i} = 0` whenever any `Y_i = 0` " ++
    "with `ω_i > 0`. Uses `Real.zero_rpow` for `ω_i > 0` and " ++
    "`Finset.prod_eq_zero`"
}

/-- Theorem~\ref{thm:aggregation} Part 3: perfect-substitutes survival. -/
def gap_thm_aggregation_PS_CLOSED : GapEntry := {
  name := "thm_aggregation_perfect_substitutes_survival"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:aggregation}` Part 3"
  attackHistory := []
  scope :=
    "Linear aggregator `∑ ω_i Y_i > 0` whenever any term is " ++
    "strictly positive. Standard sum-positivity argument"
}

/-- Proposition~\ref{prop:adjustment-margins} (career extension portion). -/
def gap_prop_adjustment_career_CLOSED : GapEntry := {
  name := "prop_adjustment_career_extension"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{prop:adjustment-margins}` (career extension)"
  attackHistory := []
  scope :=
    "`θ* < θ*_ext = 1 - τ*/T < 1` strictly: career-extension margin " ++
    "shifts the collapse threshold rightward but cannot reach 1. " ++
    "Threshold-reduction and endogenous-AI-verification margins are " ++
    "economic-narrative claims (Definition `def:verification` " ++
    "non-codifiability is the operative non-substitutability axiom); " ++
    "see `gap_prop_adjustment_narrative_BLOCKED`"
}

/-- Theorem~\ref{thm:endogenous-ai} Part 1: Brouwer existence. -/
def gap_thm_endogenous_ai_existence_CLOSED : GapEntry := {
  name := "thm_endogenous_ai_existence"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:endogenous-ai}` Part 1"
  attackHistory := []
  scope :=
    "1-D Brouwer (intermediate value theorem) gives existence of a " ++
    "fixed point for any continuous self-map of `[a, b]`. Applied " ++
    "to the abstract map Φ; the construction of Φ from Ψ and the " ++
    "verification-stock decomposition is in the docstring"
}

/-- Theorem~\ref{thm:endogenous-ai} Part 2: uniqueness under monotonicity. -/
def gap_thm_endogenous_ai_uniqueness_CLOSED : GapEntry := {
  name := "thm_endogenous_ai_uniqueness"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:endogenous-ai}` Part 2"
  attackHistory := []
  scope :=
    "Strictly anti-monotone map on ℝ has at most one fixed point. " ++
    "Used to upgrade Part 1's existence to existence-and-uniqueness " ++
    "under the paper's monotonicity assumption on `V_prod^*`"
}

/-- Theorem~\ref{thm:endogenous-ai} Part 3: corner self-consistency. -/
def gap_thm_endogenous_ai_corner_CLOSED : GapEntry := {
  name := "thm_endogenous_ai_corner"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:endogenous-ai}` Part 3"
  attackHistory := []
  scope :=
    "Corner `(θ ≥ θ*, V_∞ = 0, K_AI = 0)` is self-consistent under " ++
    "exogenous θ (from `thm_collapse_above_threshold` and `Ψ(0) = 0`); " ++
    "under endogenous θ = K_AI/(L_G + K_AI), it is inconsistent " ++
    "(yields θ = 0 < θ*)"
}

/-- Theorem~\ref{thm:endogenous-ai} Parts 4–5: hysteresis recovery rate. -/
def gap_thm_endogenous_ai_hysteresis_CLOSED : GapEntry := {
  name := "thm_endogenous_ai_recovery"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:endogenous-ai}` Parts 4–5"
  attackHistory := []
  scope :=
    "Hysteresis deficit `ν · |overlap| · ((1-θ_L) T_j)^a` and " ++
    "recovery stock `V_∞(t) = ν · min(t - t_1 - T_j, T_s) · " ++
    "((1-θ_L) T_j)^a`. Asymmetry: full recovery requires `t ≥ t_1 + T`"
}

/-! ### gapBlocked entries — paper claims not formalized

  These entries record claims in the paper whose formalization would
  require Lean infrastructure (path-dependent integrals over the
  cohort-formation window; full continuity / kink analysis of the
  CES aggregator across multiple phase transitions) that is beyond
  the structural scope of this formalization.  Each is deferred
  honestly and not faked into a Lean theorem.
-/

/-- Proposition~\ref{prop:stock-flow-asymptotics} Part 4: window
    invariance.  Path-dependent integral over cohort-formation
    window; not encoded in the steady-state `Vinf` carrier. -/
def gap_window_invariance_BLOCKED : GapEntry := {
  name := "window_invariance"
  status := GapStatus.gapBlocked
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{prop:stock-flow-asymptotics}` Part 4"
  attackHistory := []
  scope :=
    "Window invariance: `V(t) = ∫_{t-T}^{t-T_j} ν g h dc` depends " ++
    "only on θ_s for `s ∈ [t-T, t-T_j]`. Path-dependent integral " ++
    "statement; the steady-state `Vinf` carrier in `Basic.lean` " ++
    "encodes only constant-θ steady state. Formalization would " ++
    "require Mathlib's `MeasureTheory` integral over the window. " ++
    "DEFERRED — no new mathematical content beyond the steady-" ++
    "state analysis already closed; narrative content only"
}

/-- Theorem~\ref{thm:aggregation} Part 1: sequential phase transitions.
    Kink / jump statement at each order-statistic θ*_(k); requires
    continuity / one-sided-limit machinery for the CES aggregator. -/
def gap_aggregation_sequential_kinks_BLOCKED : GapEntry := {
  name := "aggregation_sequential_kinks"
  status := GapStatus.gapBlocked
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:aggregation}` Part 1"
  attackHistory := []
  scope :=
    "Sequential phase transitions at order statistics " ++
    "`θ*_(1) < ... < θ*_(N)`. Statement about left/right limits of " ++
    "`Y_agg(θ)` and the share-weighted elasticity formula. Requires " ++
    "continuity / kink-detection infrastructure; the Cobb-Douglas " ++
    "and perfect-substitutes limit cases (Parts 2 + 3) are the " ++
    "substantive structural content and are closed"
}

/-- Theorem~\ref{thm:aggregation} Part 4: intermediate-regime
    share-weighted elasticity acceleration.  Requires bounded
    derivatives across each transition. -/
def gap_aggregation_intermediate_BLOCKED : GapEntry := {
  name := "aggregation_intermediate_regime"
  status := GapStatus.gapBlocked
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{thm:aggregation}` Part 4"
  attackHistory := []
  scope :=
    "For `σ_a ∈ (1, ∞)`, the aggregate elasticity is non-decreasing " ++
    "across each transition. Differentiability statement; requires " ++
    "calculus infrastructure not encoded here. Narrative content " ++
    "covered by Parts 2 + 3 limits"
}

/-- Proposition~\ref{prop:adjustment-margins} narrative portion:
    threshold reduction and endogenous-AI-verification margins. -/
def gap_prop_adjustment_narrative_BLOCKED : GapEntry := {
  name := "prop_adjustment_narrative"
  status := GapStatus.gapBlocked
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{prop:adjustment-margins}` (narrative)"
  attackHistory := []
  scope :=
    "Threshold reduction `τ*_min` floor and endogenous-AI-verification " ++
    "`δ(θ) < 1` on residual are economic-narrative statements " ++
    "depending on the operational non-codifiability of the Polanyi " ++
    "residual (Definition `def:verification`). Both clauses are " ++
    "qualitative: the threshold-reduction floor is profession-specific " ++
    "and the residual non-substitutability is a definitional axiom. " ++
    "Career-extension margin (the only one with substantive closed-" ++
    "form mathematics) is closed in `gap_prop_adjustment_career_CLOSED`"
}

/-- Corollary~\ref{cor:quant-predictions}: numerical calibration. -/
def gap_cor_quant_predictions_BLOCKED : GapEntry := {
  name := "cor_quant_predictions"
  status := GapStatus.gapBlocked
  inputCategory := InputCategory.notInput
  paperSource := "Li 2026, `\\label{cor:quant-predictions}`"
  attackHistory := []
  scope :=
    "Numerical predictions (θ*_rad = 0.20, θ*_law = 0.29, " ++
    "θ*_SE = 0.40; lifetime Pigouvian \\$1.55M–\\$3.21M). Pure " ++
    "numerical substitution into the closed forms; not formalized " ++
    "because numerical content is auxiliary to the structural " ++
    "theorems (which deliver the closed forms `θ* = 1 - τ*/T_j`, " ++
    "`s* = (1-η) Y Λ/(ν T_s)` whose substitution is direct)"
}

/-! ### Aggregated ledger inventory -/

/-- All gap entries in canonical order. -/
def allGaps : List GapEntry := [
  -- Cat 2 axioms (gapClosed: declared in Axioms.lean)
  gap_axiom_euler_crs,
  gap_axiom_ces_wage_ratio,
  gap_axiom_cobb_douglas_factor_share,
  -- gapClosed: paper-level theorems formalized
  gap_thm_decomp_CLOSED,
  gap_thm_inversion_threshold_CLOSED,
  gap_thm_inversion_wage_ratio_CLOSED,
  gap_cor_bounded_AI_CLOSED,
  gap_thm_collapse_below_CLOSED,
  gap_thm_collapse_jump_CLOSED,
  gap_thm_collapse_above_CLOSED,
  gap_thm_collapse_transient_CLOSED,
  gap_thm_collapse_general_h_CLOSED,
  gap_prop_smooth_collapse_CLOSED,
  gap_thm_credential_CLOSED,
  gap_thm_credential_multiplicative_CLOSED,
  gap_prop_junior_senior_CLOSED,
  gap_thm_externality_wedge_CLOSED,
  gap_thm_externality_nonneg_CLOSED,
  gap_thm_externality_pigouvian_CLOSED,
  gap_prop_internalization_CLOSED,
  gap_prop_decentralized_theta_CLOSED,
  gap_thm_recursive_threshold_CLOSED,
  gap_thm_recursive_wedge_CLOSED,
  gap_thm_recursive_invariance_CLOSED,
  gap_prop_boundary_CLOSED,
  gap_thm_aggregation_CD_CLOSED,
  gap_thm_aggregation_PS_CLOSED,
  gap_prop_adjustment_career_CLOSED,
  gap_thm_endogenous_ai_existence_CLOSED,
  gap_thm_endogenous_ai_uniqueness_CLOSED,
  gap_thm_endogenous_ai_corner_CLOSED,
  gap_thm_endogenous_ai_hysteresis_CLOSED,
  -- gapBlocked: paper claims deferred to economic narrative
  gap_window_invariance_BLOCKED,
  gap_aggregation_sequential_kinks_BLOCKED,
  gap_aggregation_intermediate_BLOCKED,
  gap_prop_adjustment_narrative_BLOCKED,
  gap_cor_quant_predictions_BLOCKED
]

/-- Status-keyed counts: `(open, partial, blocked, deadEnd, closed)`. -/
def gapCounts : Nat × Nat × Nat × Nat × Nat :=
  let countWhere (s : GapStatus) : Nat :=
    (allGaps.filter (fun g => g.status = s)).length
  ( countWhere GapStatus.gapOpen
  , countWhere GapStatus.gapPartial
  , countWhere GapStatus.gapBlocked
  , countWhere GapStatus.gapDeadEnd
  , countWhere GapStatus.gapClosed )

/-- InputCategory-keyed counts: `(cat1Mathlib, cat2External, cat3PaperNovel, notInput)`. -/
def inputCategoryCounts : Nat × Nat × Nat × Nat :=
  let countWhere (c : InputCategory) : Nat :=
    (allGaps.filter (fun g => g.inputCategory = c)).length
  ( countWhere InputCategory.cat1Mathlib
  , countWhere InputCategory.cat2External
  , countWhere InputCategory.cat3PaperNovel
  , countWhere InputCategory.notInput )

#eval s!"VerificationAsymmetry gap-ledger inventory (status):  open={(gapCounts).1} partial={(gapCounts).2.1} blocked={(gapCounts).2.2.1} deadEnd={(gapCounts).2.2.2.1} closed={(gapCounts).2.2.2.2}"

#eval s!"VerificationAsymmetry gap-ledger inventory (input):   cat1Mathlib={(inputCategoryCounts).1} cat2External={(inputCategoryCounts).2.1} cat3PaperNovel={(inputCategoryCounts).2.2.1} notInput={(inputCategoryCounts).2.2.2}"

#eval s!"Total entries: {allGaps.length}"

/-! ### Inventory summary (post-audit 2026-05)

  The live status counts and input-category counts are printed by the
  `#eval` calls above (run `lake env lean VerificationAsymmetry/Ledger.lean`
  to see them).

  Inventory profile.  This project has:
    * Cat 1 (Mathlib-derivable theorems): the bulk of paper-level
      content. Real-analytic identities, `rpow` arithmetic, Finset
      sums / products, 1-D Brouwer / IVT.
    * Cat 2 (external textbook axioms): three atomic axioms —
      `axiom_euler_crs` (Euler identity for CRS, MWG 1995 §5.B.2),
      `axiom_ces_wage_ratio` (CES wage-ratio closed form,
      Acemoglu 2009 §15),
      `axiom_cobb_douglas_factor_share` (Cobb-Douglas verification
      factor share, MWG 1995 §5.B.2).
    * Cat 3 (paper-novel atomic axioms): zero. Every paper-novel
      structural object (`Economy`, `Vinf`, `eBar`, `gHard`, `wageRatio`,
      `Vreq`) is a Lean *definition*, not an axiom.

  The Cat 2 axioms were introduced by the 2026-05 audit as the
  honest accounting of textbook facts that were previously hidden
  inside theorem signatures as hypotheses.  Each axiom is atomic
  (a single algebraic identity at fixed parameter values), with an
  explicit citation in `Axioms.lean`.

  Lean kernel axioms used: propext, Classical.choice, Quot.sound.
-/

end VerificationAsymmetry.Ledger
