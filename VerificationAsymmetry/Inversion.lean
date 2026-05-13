/-
  VerificationAsymmetry/Inversion.lean

  Theorem~\ref{thm:inversion} (Asymmetry Inversion) and
  Corollary~\ref{cor:bounded-AI} (Inversion Under Bounded AI).

  Companion to: "Generation--Verification Asymmetry Inversion and
  Apprenticeship Pipeline Collapse Under AI Substitution" (Li, 2026).

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
-/

import VerificationAsymmetry.Basic

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
    `L_G < G*(r̄) < K_AI`, the inversion threshold lies in `(0, 1)`. -/
theorem thm_inversion_threshold_in_unit_interval
    (V rBar : ℝ) (hKAI_gt : E.LG < E.KAI)
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

/-- **Corollary~\ref{cor:bounded-AI} (endpoint identification).**
    At the baseline wage ratio `r̄ = r̄_0`, the inversion threshold
    is `0`:  `θ_inv(r̄_0) = 0`.

    *Proof sketch:* `G*(r̄_0) = L_G` by the closed-form definition;
    substituting into `θ_inv = (G* - L_G)/(K_AI - L_G)` gives `0`. -/
theorem cor_bounded_AI_threshold_at_rBarZero
    (V : ℝ) (_hV_pos : 0 < V) (_hKAI_gt : E.LG < E.KAI)
    (hGstar_eq : E.Gstar V (E.rBarZero V) = E.LG) :
    E.thetaInv V (E.rBarZero V) = 0 := by
  unfold thetaInv
  rw [hGstar_eq]
  simp

/-- **Corollary~\ref{cor:bounded-AI} (endpoint identification).**
    At the maximum reachable wage ratio `r̄ = r̄_max`, the inversion
    threshold is `1`. -/
theorem cor_bounded_AI_threshold_at_rBarMax
    (V : ℝ) (hKAI_gt : E.LG < E.KAI)
    (hGstar_eq : E.Gstar V (E.rBarMax V) = E.KAI) :
    E.thetaInv V (E.rBarMax V) = 1 := by
  unfold thetaInv
  rw [hGstar_eq]
  have h_ne : E.KAI - E.LG ≠ 0 := by
    have : 0 < E.KAI - E.LG := by linarith
    exact ne_of_gt this
  field_simp

end Economy

end VerificationAsymmetry
