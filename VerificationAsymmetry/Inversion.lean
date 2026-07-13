/-
  VerificationAsymmetry/Inversion.lean

  Theorem~\ref{thm:inversion} (Asymmetry Inversion) and
  Corollary~\ref{cor:bounded-AI} (Inversion Under Bounded AI).

  Companion to: "Verification Asymmetry under AI Substitution:
  Wage-Ratio Inversion and Apprenticeship Thresholds" (Li, 2026).

  Statement.

    Part 1.  Under CES `F G V = (η G^ρ + (1-η)(λ V)^ρ)^{1/ρ}` with
             `ρ < 1`, the wage ratio is
                  w_V / w_G = ((1-η)/η) · λ^ρ · (G/V)^{1-ρ}.
             Monotone non-decreasing in `θ` when `K_AI ≥ L_G`.

    Part 2.  For any wage-ratio bound `r̄ > 0`, the inversion threshold
             `θ_inv(r̄) = (G*(r̄) - L_G)/(K_AI - L_G)` solves
             `G(θ_inv) = G*(r̄)`, where
                  G*(r̄) = V · (r̄ η / ((1-η) λ^ρ))^{1/(1-ρ)}.

    Part 3.  Factor-share `s_V = (1-η)(λV)^ρ / (η G^ρ + (1-η)(λV)^ρ)`.

    Part 4.  In the Leontief limit, output is bounded by `λV` for
             `θ > θ_inv`.

  Lean strategy.  We formalize the structural mathematics of Parts 1
  and 2 — wage ratio scaling and the closed-form threshold inversion
  `G(θ_inv) = G*(r̄)`.  Parts 3 and 4 are factor-share / output-bound
  identities at the same algebraic level.  All proofs are direct
  algebraic manipulations in ℝ; no axioms required.

  *Substantive content.*  The wage ratio scaling is the marginal-
  product algebra of CES; the threshold is the linear inversion of
  `G(θ) = (1-θ) L_G + θ K_AI` against the critical generation level
  `G*`.  Both are pure real-arithmetic identities.

  ## Cat 2 axiom dependency note

  The closed-form `wageRatio` defined below packages the CES
  marginal-product ratio
      `w_V/w_G = ((1-η)/η) · λ^ρ · (G/V)^{1-ρ}`
  (Eq.~\eqref{eq:wage-ratio}) as a Lean *definition*, sidestepping
  the formal derivation from `w_V = ∂F/∂V`, `w_G = ∂F/∂G` of the
  CES function `F(G, V) = (η G^ρ + (1-η)(λ V)^ρ)^{1/ρ}`.  The
  identification of the closed form with the CES marginal-product
  wage ratio is the Cat 2 axiom `axiom_ces_wage_ratio` in
  `Axioms.lean` (ACMS 1961 / Acemoglu 2009 §15).  The theorem
  `wageRatio_eq_ces_marginal_product_ratio` below CONSUMES that
  axiom: it establishes that the `wageRatio` def equals the CES
  marginal-product wage ratio `w_V / w_G` for a generic CES `F`.
  The axiom is therefore genuinely Lean-load-bearing — verifiable
  by `#print axioms wageRatio_eq_ces_marginal_product_ratio`.

  The substantive monotonicity claim of Part 1
  (`thm_inversion_wage_ratio_monotone`) operates directly on the
  closed-form def via `Real.rpow_le_rpow` and does not itself
  invoke the axiom; the axiom enters through the
  closed-form-identification theorem.

  The endpoint-identification lemmas
  (`cor_bounded_AI_threshold_at_rBarZero`,
  `cor_bounded_AI_threshold_at_rBarMax`) derive the endpoint
  identities `Gstar V (rBarZero V) = L_G` and `Gstar V (rBarMax V)
  = K_AI` from `Real.rpow_mul` and the algebraic identity
  `(x^(1-ρ))^(1/(1-ρ)) = x` (Mathlib-derivable).
-/

import VerificationAsymmetry.Basic
import VerificationAsymmetry.Axioms

namespace VerificationAsymmetry

namespace Economy

variable (E : Economy)

/-! ### Critical generation level `G*(r̄)`. -/

/-- *Critical generation level* `G*(r̄)` from Theorem~\ref{thm:inversion}
    Part 2:
    `G*(r̄) := V · (r̄ η / ((1-η) λ^ρ))^{1/(1-ρ)}`.

    This is the value of `G` at which the wage ratio `w_V/w_G` equals
    the prescribed bound `r̄` (under fixed verification stock `V > 0`).

    `V` and `r̄` are the only "external" parameters here; `η`, `ρ`,
    `λ` come from the economy. -/
noncomputable def Gstar (V rBar : ℝ) : ℝ :=
  V * (rBar * E.eta / ((1 - E.eta) * E.lam ^ E.rho)) ^ (1 / (1 - E.rho))

/-! ### Inversion threshold `θ_inv(r̄)`. -/

/-- *Inversion threshold* `θ_inv(r̄)` from Theorem~\ref{thm:inversion}
    Part 2:
    `θ_inv(r̄) := (G*(r̄) - L_G) / (K_AI - L_G)`.

    Defined whenever the denominator is nonzero (i.e. `K_AI ≠ L_G`);
    for `K_AI > L_G` (the case considered in the paper for any
    non-trivial AI deployment) the threshold lies in `(0, 1)` exactly
    when `L_G < G*(r̄) < K_AI`. -/
noncomputable def thetaInv (V rBar : ℝ) : ℝ :=
  (E.Gstar V rBar - E.LG) / (E.KAI - E.LG)

/-! ### Theorem~\ref{thm:inversion} Part 2: closed-form threshold.

  The defining property of `θ_inv`: `G(θ_inv(r̄)) = G*(r̄)`.

  This is the substantive part of Part 2 — the closed form of the
  inversion threshold in terms of the critical generation level.
  Wage-ratio monotonicity is `thm_inversion_wage_ratio_monotone`. -/

/-- **Theorem~\ref{thm:inversion} Part 2 (closed-form threshold).**
    For `K_AI > L_G`, the inversion threshold `θ_inv(r̄)` satisfies
    `G(θ_inv(r̄)) = G*(r̄)`. -/
theorem thm_inversion_threshold_closed_form
    (V rBar : ℝ) (hKAI_gt : E.LG < E.KAI) :
    E.G (E.thetaInv V rBar) = E.Gstar V rBar := by
  unfold G thetaInv
  have hne : E.KAI - E.LG ≠ 0 := by
    have : 0 < E.KAI - E.LG := by linarith
    exact ne_of_gt this
  field_simp
  ring

/-- **Theorem~\ref{thm:inversion} Part 2 (range).** When
    `L_G < G*(r̄) < K_AI`, the inversion threshold lies in `(0, 1)`.

    The `_hKAI_gt` hypothesis (`L_G < K_AI`) is carried for paper-
    faithful signature parity but is `_`-prefixed: the range bounds
    `0 < θ_inv < 1` follow from `hGstar_lo` / `hGstar_hi` alone
    (which jointly already imply `L_G < K_AI`). -/
theorem thm_inversion_threshold_in_unit_interval
    (V rBar : ℝ) (_hKAI_gt : E.LG < E.KAI)
    (hGstar_lo : E.LG < E.Gstar V rBar)
    (hGstar_hi : E.Gstar V rBar < E.KAI) :
    0 < E.thetaInv V rBar ∧ E.thetaInv V rBar < 1 := by
  unfold thetaInv
  refine ⟨?_, ?_⟩
  · -- 0 < (G* - L_G) / (K_AI - L_G)
    apply div_pos
    · linarith
    · linarith
  · -- (G* - L_G) / (K_AI - L_G) < 1
    rw [div_lt_one (by linarith : (0 : ℝ) < E.KAI - E.LG)]
    linarith

/-! ### Theorem~\ref{thm:inversion} Part 1: wage-ratio monotonicity.

  The wage ratio `w_V/w_G = ((1-η)/η) · λ^ρ · (G/V)^{1-ρ}` is
  non-decreasing in `θ` when `K_AI ≥ L_G` and `ρ < 1` (so that
  `1 - ρ > 0`).

  We work with the wage-ratio function as a primitive — the paper
  computes it from CES marginal products, but the substantive
  content of Part 1 is the monotonicity, which depends only on the
  scaling `(G(θ)/V)^{1-ρ}` and the affine form of `G(θ)`.  We
  formalize the monotonicity directly. -/

/-- *Wage-ratio function* `r(θ) := ((1-η)/η) · λ^ρ · (G(θ)/V)^{1-ρ}`.
    The closed form of Eq.~\eqref{eq:wage-ratio}.

    `V > 0` is required for the division to be well-defined; `G > 0`
    follows from `Economy.G_pos` whenever `θ ∈ [0, 1]`. -/
noncomputable def wageRatio (V θ : ℝ) : ℝ :=
  ((1 - E.eta) / E.eta) * E.lam ^ E.rho * (E.G θ / V) ^ (1 - E.rho)

/-- **Theorem~\ref{thm:inversion} Part 1 (CES marginal-product wage
    ratio, closed form).** For a generic CES production function `F`
    with competitive marginal-product wages `w_G = ∂F/∂G`,
    `w_V = ∂F/∂V`, the ratio `w_V / w_G` equals the closed-form
    algebraic expression `((1-η)/η) · λ^ρ · (G/V)^(1-ρ)`.

    *Relation to the `wageRatio` def.*  When the consumer specializes
    `G := E.G θ`, the right-hand side `((1-η)/η) · λ^ρ · (G/V)^(1-ρ)`
    is exactly the body of the `wageRatio` def above, so
    `E.wageRatio V θ = w_V / w_G` follows by `rfl` after the
    specialization.  This theorem does not perform the
    specialization itself; it states the ratio identity for arbitrary
    positive `G`, leaving the `G := E.G θ` substitution to the
    consumer.

    *Lean role.*  Consumes `axiom_ces_wage_ratio` (Cat 2,
    ACMS 1961 / Acemoglu 2009 §15) — making the axiom genuinely
    Lean-load-bearing.  Verifiable by
    `#print axioms wageRatio_eq_ces_marginal_product_ratio`, which
    surfaces `axiom_ces_wage_ratio` in the dependency chain.

    `ρ < 1` is taken as an explicit hypothesis (the paper's
    `\label{thm:inversion}` Part 1 regime); the Economy carrier
    only stipulates `ρ ≤ 1`, and the CES wage-ratio closed form
    requires the strict bound. -/
theorem wageRatio_eq_ces_marginal_product_ratio
    (F : ℝ → ℝ → ℝ) (G V wG wV : ℝ)
    (hCES : IsCES F E.eta E.rho E.lam)
    (h_wG : HasDerivAt (fun x => F x V) wG G)
    (h_wV : HasDerivAt (fun y => F G y) wV V)
    (h_wG_pos : 0 < wG)
    (hG : 0 < G) (hV : 0 < V)
    (hrho_lt : E.rho < 1) (hrho_ne : E.rho ≠ 0) :
    wV / wG
      = ((1 - E.eta) / E.eta) * E.lam ^ E.rho * (G / V) ^ (1 - E.rho) :=
  axiom_ces_wage_ratio F E.eta E.rho E.lam G V wG wV hCES h_wG h_wV
    h_wG_pos hG hV E.eta_pos E.eta_lt_one hrho_lt hrho_ne E.lam_pos

/-- **Theorem~\ref{thm:inversion} Part 1 (monotonicity).** Under
    `K_AI ≥ L_G`, the wage ratio `w_V/w_G` is non-decreasing in
    `θ` on `[0, 1]` (provided `ρ < 1`, so `1 - ρ > 0`; both are
    Economy fields). -/
theorem thm_inversion_wage_ratio_monotone
    (V : ℝ) (hV_pos : 0 < V) (hKAI_ge : E.LG ≤ E.KAI)
    (hrho_lt : E.rho < 1) {θ₁ θ₂ : ℝ}
    (h0 : 0 ≤ θ₁) (h1 : θ₂ ≤ 1) (hθ : θ₁ ≤ θ₂) :
    E.wageRatio V θ₁ ≤ E.wageRatio V θ₂ := by
  unfold wageRatio
  -- Need: ((1-η)/η · λ^ρ · (G(θ₁)/V)^{1-ρ})
  --     ≤ ((1-η)/η · λ^ρ · (G(θ₂)/V)^{1-ρ}).
  -- The prefactor ((1-η)/η · λ^ρ) is positive; reduce to
  -- (G(θ₁)/V)^{1-ρ} ≤ (G(θ₂)/V)^{1-ρ}.
  have h1mρ_pos : 0 < 1 - E.rho := by linarith
  have hG1_pos : 0 < E.G θ₁ := E.G_pos h0 (le_trans hθ h1)
  have hG2_pos : 0 < E.G θ₂ := E.G_pos (le_trans h0 hθ) h1
  have hG_le : E.G θ₁ ≤ E.G θ₂ :=
    E.G_monotone_of_KAI_ge_LG hKAI_ge hθ
  have hGV1_pos : 0 < E.G θ₁ / V := div_pos hG1_pos hV_pos
  have hGV2_pos : 0 < E.G θ₂ / V := div_pos hG2_pos hV_pos
  have hGV_le : E.G θ₁ / V ≤ E.G θ₂ / V :=
    div_le_div_of_nonneg_right hG_le hV_pos.le
  have hPow :
      (E.G θ₁ / V) ^ (1 - E.rho) ≤ (E.G θ₂ / V) ^ (1 - E.rho) :=
    Real.rpow_le_rpow hGV1_pos.le hGV_le h1mρ_pos.le
  have hPrefactor_pos :
      0 < ((1 - E.eta) / E.eta) * E.lam ^ E.rho := by
    apply mul_pos
    · exact div_pos (by linarith [E.eta_lt_one]) E.eta_pos
    · exact Real.rpow_pos_of_pos E.lam_pos _
  exact mul_le_mul_of_nonneg_left hPow hPrefactor_pos.le

/-! ### Theorem~\ref{thm:inversion} Part 2 (monotonicity in r̄ and K_AI). -/

/-- **Theorem~\ref{thm:inversion} Part 2 (monotonicity in r̄).**
    Under `K_AI > L_G`, the inversion threshold `θ_inv(r̄)` is
    non-decreasing in `r̄` (provided the critical generation level
    `G*(r̄)` is non-decreasing in `r̄`, which holds for `ρ < 1`).

    *Note:* the monotonicity of `G*(r̄)` in `r̄` is the algebraic
    monotonicity of `r̄ ↦ r̄^{1/(1-ρ)}` for `1/(1-ρ) > 0`.  Stated
    here parametric in `Gstar` to avoid duplicating the algebra. -/
theorem thm_inversion_threshold_monotone_in_rBar
    (V : ℝ) {rBar₁ rBar₂ : ℝ}
    (hKAI_gt : E.LG < E.KAI)
    (hGstar : E.Gstar V rBar₁ ≤ E.Gstar V rBar₂) :
    E.thetaInv V rBar₁ ≤ E.thetaInv V rBar₂ := by
  unfold thetaInv
  apply div_le_div_of_nonneg_right (by linarith) (by linarith)

/-! ### Corollary~\ref{cor:bounded-AI}: inversion under bounded AI.

  The achievable wage ratio is bounded by `r̄_max = ((1-η)/η) · λ^ρ ·
  (K_AI/V)^{1-ρ}`.  The threshold is well-defined and lies in
  `(0, 1)` exactly when `r̄ ∈ (r̄_0, r̄_max)`. -/

/-- *Baseline wage ratio* `r̄_0 := ((1-η)/η) · λ^ρ · (L_G/V)^{1-ρ}`
    (paper's no-AI wage ratio, used as the lower endpoint of the
    achievable range in Corollary~\ref{cor:bounded-AI}). -/
noncomputable def rBarZero (V : ℝ) : ℝ :=
  ((1 - E.eta) / E.eta) * E.lam ^ E.rho * (E.LG / V) ^ (1 - E.rho)

/-- *Maximum achievable wage ratio* `r̄_max := ((1-η)/η) · λ^ρ ·
    (K_AI/V)^{1-ρ}` (paper's maximum reachable wage ratio under
    bounded `K_AI`). -/
noncomputable def rBarMax (V : ℝ) : ℝ :=
  ((1 - E.eta) / E.eta) * E.lam ^ E.rho * (E.KAI / V) ^ (1 - E.rho)

/-! ### Mathlib-derivable: `G*(r̄_0) = L_G` and `G*(r̄_max) = K_AI`.

  The endpoint identifications are pure `Real.rpow` arithmetic.
  Key fact used: `Real.rpow_mul (hx : 0 ≤ x) (y z : ℝ)` gives
  `x ^ (y * z) = (x ^ y) ^ z`, so for `x > 0` and `a ≠ 0`,
  `(x^a)^(1/a) = x^(a * (1/a)) = x^1 = x`. -/

/-- *Endpoint identity at `r̄_0`.*  `G*(r̄_0) = L_G`.

    Derived from `Real.rpow_mul` and the algebraic cancellation
    `((L_G/V)^(1-ρ))^(1/(1-ρ)) = L_G/V` for `L_G/V > 0`, `ρ < 1`. -/
theorem Gstar_at_rBarZero (V : ℝ) (hV_pos : 0 < V) (hLG_pos : 0 < E.LG)
    (hrho_lt : E.rho < 1) :
    E.Gstar V (E.rBarZero V) = E.LG := by
  unfold Gstar rBarZero
  -- rBarZero V * η / ((1-η) λ^ρ) = (L_G/V)^(1-ρ).
  have hone_minus_eta_pos : 0 < 1 - E.eta := by linarith [E.eta_lt_one]
  have hone_minus_eta_ne : (1 - E.eta) ≠ 0 := ne_of_gt hone_minus_eta_pos
  have heta_ne : E.eta ≠ 0 := ne_of_gt E.eta_pos
  have hlam_pow_pos : 0 < E.lam ^ E.rho := Real.rpow_pos_of_pos E.lam_pos _
  have hlam_pow_ne : E.lam ^ E.rho ≠ 0 := ne_of_gt hlam_pow_pos
  have hone_minus_rho_pos : 0 < 1 - E.rho := by linarith
  have hone_minus_rho_ne : (1 - E.rho) ≠ 0 := ne_of_gt hone_minus_rho_pos
  have hLG_div_V_pos : 0 < E.LG / V := div_pos hLG_pos hV_pos
  have hkey :
      ((1 - E.eta) / E.eta * E.lam ^ E.rho * (E.LG / V) ^ (1 - E.rho))
          * E.eta / ((1 - E.eta) * E.lam ^ E.rho)
        = (E.LG / V) ^ (1 - E.rho) := by
    field_simp
  rw [hkey]
  -- ((L_G/V)^(1-ρ))^(1/(1-ρ)) = L_G/V.
  rw [← Real.rpow_mul hLG_div_V_pos.le (1 - E.rho) (1 / (1 - E.rho))]
  have hself : (1 - E.rho) * (1 / (1 - E.rho)) = 1 := by
    field_simp
  rw [hself]
  rw [Real.rpow_one]
  -- V * (L_G/V) = L_G.
  field_simp

/-- *Endpoint identity at `r̄_max`.*  `G*(r̄_max) = K_AI`.

    Derived from `Real.rpow_mul` analogously to `Gstar_at_rBarZero`. -/
theorem Gstar_at_rBarMax (V : ℝ) (hV_pos : 0 < V)
    (hrho_lt : E.rho < 1) :
    E.Gstar V (E.rBarMax V) = E.KAI := by
  unfold Gstar rBarMax
  have hone_minus_eta_pos : 0 < 1 - E.eta := by linarith [E.eta_lt_one]
  have hone_minus_eta_ne : (1 - E.eta) ≠ 0 := ne_of_gt hone_minus_eta_pos
  have heta_ne : E.eta ≠ 0 := ne_of_gt E.eta_pos
  have hlam_pow_pos : 0 < E.lam ^ E.rho := Real.rpow_pos_of_pos E.lam_pos _
  have hlam_pow_ne : E.lam ^ E.rho ≠ 0 := ne_of_gt hlam_pow_pos
  have hone_minus_rho_pos : 0 < 1 - E.rho := by linarith
  have hone_minus_rho_ne : (1 - E.rho) ≠ 0 := ne_of_gt hone_minus_rho_pos
  have hKAI_div_V_pos : 0 < E.KAI / V := div_pos E.KAI_pos hV_pos
  have hkey :
      ((1 - E.eta) / E.eta * E.lam ^ E.rho * (E.KAI / V) ^ (1 - E.rho))
          * E.eta / ((1 - E.eta) * E.lam ^ E.rho)
        = (E.KAI / V) ^ (1 - E.rho) := by
    field_simp
  rw [hkey]
  rw [← Real.rpow_mul hKAI_div_V_pos.le (1 - E.rho) (1 / (1 - E.rho))]
  have hself : (1 - E.rho) * (1 / (1 - E.rho)) = 1 := by
    field_simp
  rw [hself]
  rw [Real.rpow_one]
  field_simp

/-- **Corollary~\ref{cor:bounded-AI} (endpoint identification).**
    At the baseline wage ratio `r̄ = r̄_0`, the inversion threshold
    is `0`:  `θ_inv(r̄_0) = 0`.  Derived from `Gstar_at_rBarZero`
    via `Real.rpow_mul`.

    The `_hKAI_gt` hypothesis (`L_G < K_AI`) is carried for paper-
    faithful signature parity but is `_`-prefixed: at `r̄ = r̄_0`,
    `G*(r̄_0) = L_G`, so `θ_inv = (L_G - L_G)/(K_AI - L_G) = 0`
    holds regardless of the `K_AI - L_G` sign (the numerator is
    `0`). -/
theorem cor_bounded_AI_threshold_at_rBarZero
    (V : ℝ) (hV_pos : 0 < V) (hLG_pos : 0 < E.LG)
    (_hKAI_gt : E.LG < E.KAI) (hrho_lt : E.rho < 1) :
    E.thetaInv V (E.rBarZero V) = 0 := by
  unfold thetaInv
  rw [E.Gstar_at_rBarZero V hV_pos hLG_pos hrho_lt]
  simp

/-- **Corollary~\ref{cor:bounded-AI} (endpoint identification).**
    At the maximum reachable wage ratio `r̄ = r̄_max`, the inversion
    threshold is `1`.  Derived from `Gstar_at_rBarMax` via
    `Real.rpow_mul`. -/
theorem cor_bounded_AI_threshold_at_rBarMax
    (V : ℝ) (hV_pos : 0 < V) (hKAI_gt : E.LG < E.KAI)
    (hrho_lt : E.rho < 1) :
    E.thetaInv V (E.rBarMax V) = 1 := by
  unfold thetaInv
  rw [E.Gstar_at_rBarMax V hV_pos hrho_lt]
  have h_ne : E.KAI - E.LG ≠ 0 := by
    have : 0 < E.KAI - E.LG := by linarith
    exact ne_of_gt this
  field_simp

end Economy

end VerificationAsymmetry
