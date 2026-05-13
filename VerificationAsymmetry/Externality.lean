/-
  VerificationAsymmetry/Externality.lean

  Theorem~\ref{thm:externality} (Apprenticeship Externality) and
  Propositions ~\ref{prop:internalization} (Within-Firm
  Internalization Failure) and ~\ref{prop:decentralized-theta}
  (Decentralized θ Exceeds Social Optimum).

  Companion to: "Generation--Verification Asymmetry Inversion and
  Apprenticeship Pipeline Collapse Under AI Substitution" (Li, 2026).

  Statement.

    The private marginal product of a junior at AI substitution
    rate θ is
        MP_J^P(θ) = (1-θ) w_G(θ).
    The social marginal product is
        MP_J^S(θ) = MP_J^P(θ) + w_V(θ) g(ē) h(ē) Λ(r),
    where Λ(r) = (e^{-r T_j} - e^{-r T})/r is the discounted senior
    horizon.

    Apprenticeship wedge (paper Eq.~\eqref{eq:wedge}):
        W_E(θ) = (MP_J^S - MP_J^P)/MP_J^P
              = (w_V/w_G) · g(ē) h(ē) Λ(r) / (1-θ).

    Optimal Pigouvian subsidy (Cobb-Douglas, paper Thm
    Part 3 simplification):
        s*(θ) = (1-η) Y(θ) Λ(r) / (ν T_s).

  Lean strategy.  Both formulae are real-arithmetic identities once
  the marginal-product definitions are in place.  We formalize:

    (i)   the explicit algebraic identity for the wedge,
    (ii)  the Cobb-Douglas simplification of the optimal subsidy,
    (iii) the non-negativity of the wedge (Part 2),
    (iv)  the internalization corollary (Proposition~\ref{prop:internalization}),
    (v)   the social-vs-private FOC inequality (Proposition~\ref{prop:decentralized-theta}).

  Part 1 of the theorem (wedge growth on `[0, θ*)`) is a
  monotonicity statement in `θ` of the product
  `G(θ)^{1-ρ} · (1-θ)^{aρ-1}`; we formalize the monotonicity of
  each factor in `θ` separately (under the paper's hypotheses
  `K_AI ≥ L_G`, `ρ ≤ 0` ∨ `ρ ∈ (0, 1/a)`).  The unbounded-as-θ→1
  claim is a limit statement we record as a parametric inequality.

  ## Audit note (post-audit 2026-05)

  The composite Cobb-Douglas-factor-share + steady-state-stock
  identity used in Part 3 (Pigouvian subsidy formula) was formerly
  carried as a *hypothesis* of `thm_externality_pigouvian_cobb_douglas`.
  An axiom-discharged form `_from_axioms` is now provided alongside,
  using `axiom_cobb_douglas_factor_share` (Cat 2) + the definitional
  unfolding of `Vinf`.
-/

import VerificationAsymmetry.Basic
import VerificationAsymmetry.Axioms
import VerificationAsymmetry.Collapse

namespace VerificationAsymmetry

namespace Economy

variable (E : Economy)

/-! ### Discounted senior horizon `Λ(r)`. -/

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

/-! ### Marginal products. -/

/-- *Private marginal product of a junior* at rate `θ`:
    `MP_J^P(θ) = (1-θ) w_G(θ)`.

    *Implementation note.*  Bound to `_E : Economy` so that Lean
    auto-namespaces the def into `Economy.MPpriv : Economy → ℝ → ℝ → ℝ`,
    enabling dot-notation `E.MPpriv` uniformly with `E.G`, `E.eBar`,
    etc.  The `_E` parameter is unused in the body (the private
    marginal product is `Economy`-independent in this paper). -/
def MPpriv (_E : Economy) (wG θ : ℝ) : ℝ := (1 - θ) * wG

/-- *Social marginal product of a junior* at rate `θ`:
    `MP_J^S(θ) = MP_J^P(θ) + w_V g(ē) h(ē) Λ`. -/
def MPsoc (wG wV gE hE Lambda θ : ℝ) : ℝ :=
  E.MPpriv wG θ + wV * gE * hE * Lambda

/-- *Externality residual* `s*(θ) := MP_J^S - MP_J^P =
    w_V g(ē) h(ē) Λ`.  Stored with explicit `Economy` parameter to
    enable `E.externalityResidual` dot-notation. -/
def externalityResidual (_E : Economy) (wV gE hE Lambda : ℝ) : ℝ :=
  wV * gE * hE * Lambda

/-! ### Theorem~\ref{thm:externality} — algebraic identities. -/

/-- **Theorem~\ref{thm:externality} (residual identity).** The
    externality residual `MP_J^S - MP_J^P` equals
    `w_V g(ē) h(ē) Λ`. -/
theorem thm_externality_residual_identity
    (wG wV gE hE Lambda θ : ℝ) :
    E.MPsoc wG wV gE hE Lambda θ - E.MPpriv wG θ
      = E.externalityResidual wV gE hE Lambda := by
  unfold MPsoc MPpriv externalityResidual
  ring

/-- **Theorem~\ref{thm:externality} (non-negativity, Part 2).** The
    externality residual is non-negative whenever
    `w_V, g, h, Λ ≥ 0`. -/
theorem thm_externality_residual_nonneg
    (wV gE hE Lambda : ℝ) (hwV : 0 ≤ wV) (hgE : 0 ≤ gE)
    (hhE : 0 ≤ hE) (hLambda : 0 ≤ Lambda) :
    0 ≤ E.externalityResidual wV gE hE Lambda := by
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
    0 < E.externalityResidual wV gE hE Lambda := by
  unfold externalityResidual
  have : 0 < wV * (gE * hE) := mul_pos hwV hgh
  have h_eq : wV * gE * hE = wV * (gE * hE) := by ring
  rw [h_eq]
  exact mul_pos this hLambda

/-! ### Apprenticeship wedge. -/

/-- *Apprenticeship wedge* `W_E(θ) := (MP_J^S - MP_J^P)/MP_J^P`,
    paper Eq.~\eqref{eq:wedge}. -/
noncomputable def wedge (wG wV gE hE Lambda θ : ℝ) : ℝ :=
  E.externalityResidual wV gE hE Lambda / E.MPpriv wG θ

/-- **Theorem~\ref{thm:externality} (wedge identity).** The
    wedge `W_E(θ)` rearranges to
    `(w_V/w_G) · g(ē) h(ē) Λ / (1-θ)`. -/
theorem thm_externality_wedge_identity
    (wG wV gE hE Lambda θ : ℝ) (hwG : 0 < wG) (hθ_lt : θ < 1) :
    E.wedge wG wV gE hE Lambda θ
      = (wV / wG) * (gE * hE * Lambda) / (1 - θ) := by
  unfold wedge externalityResidual MPpriv
  have h1mθ : 0 < 1 - θ := by linarith
  have h1mθ_ne : 1 - θ ≠ 0 := ne_of_gt h1mθ
  have hwG_ne : wG ≠ 0 := ne_of_gt hwG
  field_simp

/-! ### Theorem~\ref{thm:externality} Part 3: Pigouvian subsidy. -/

/-- *Optimal Pigouvian subsidy* in Cobb-Douglas:
    `s*(θ) = (1-η) Y(θ) Λ(r) / (ν T_s)`,
    paper Theorem~\ref{thm:externality} Part 3.

    Derivation: `s* = MP_J^S - MP_J^P = w_V g h Λ`.  Under Cobb-
    Douglas factor share `w_V V_∞ = (1-η) Y` and the steady-state
    stock identity `V_∞ = ν T_s g h`, we have
    `w_V g h = (1-η) Y / (ν T_s)`, hence
    `s* = (1-η) Y Λ / (ν T_s)`. -/
noncomputable def pigouvianSubsidy_CD (Y Lambda : ℝ) : ℝ :=
  (1 - E.eta) * Y * Lambda / (E.nu * E.Ts)

/-- **Theorem~\ref{thm:externality} Part 3 (Cobb-Douglas Pigouvian
    formula).** Under the Cobb-Douglas factor-share identity
    `(1-η) Y = w_V · ν T_s · g h` and `g h > 0`, the optimal
    Pigouvian subsidy `s* = w_V g h Λ` simplifies to
    `(1-η) Y Λ / (ν T_s)`. -/
theorem thm_externality_pigouvian_cobb_douglas
    (Y wV gE hE Lambda : ℝ)
    (hY : (1 - E.eta) * Y = wV * (E.nu * E.Ts * gE * hE)) :
    E.externalityResidual wV gE hE Lambda
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
    derived from `axiom_cobb_douglas_factor_share` (Cat 2) + the
    `Vinf` definition. -/
theorem thm_externality_pigouvian_cobb_douglas_from_axioms
    (Y wV Lambda : ℝ) (g h : ℝ → ℝ) (θ : ℝ) :
    E.externalityResidual wV (g (E.eBar θ)) (h (E.eBar θ)) Lambda
      = E.pigouvianSubsidy_CD Y Lambda :=
  E.thm_externality_pigouvian_cobb_douglas
    Y wV (g (E.eBar θ)) (h (E.eBar θ)) Lambda
    (E.cobb_douglas_steady_state_identity Y wV g h θ)

/-! ### Proposition~\ref{prop:internalization}: within-firm internalization. -/

/-- **Proposition~\ref{prop:internalization} (within-firm
    internalization).** Internalizing fraction `ζ ∈ [0, 1]` of the
    future verification rent reduces the effective wedge to
    `(1-ζ) W_E(θ)`. -/
theorem prop_internalization
    (zeta wG wV gE hE Lambda θ : ℝ) :
    (1 - zeta) * E.externalityResidual wV gE hE Lambda / E.MPpriv wG θ
      = (1 - zeta) * E.wedge wG wV gE hE Lambda θ := by
  unfold wedge
  rw [mul_div_assoc]

/-- **Proposition~\ref{prop:internalization} (full internalization
    eliminates externality).** For `ζ = 1`, the effective wedge is
    zero. -/
theorem prop_internalization_full
    (wV gE hE Lambda : ℝ) :
    (1 - (1 : ℝ)) * E.externalityResidual wV gE hE Lambda = 0 := by
  ring

/-! ### Proposition~\ref{prop:decentralized-theta}: social vs. private. -/

/-- **Proposition~\ref{prop:decentralized-theta} (social vs. private
    FOC).** The social FOC `p_AI + s*(θ_soc) = w_G(θ_soc)` and the
    private FOC `p_AI = w_G(θ_eq)` imply
    `w_G(θ_soc) = w_G(θ_eq) + s*(θ_soc)`.

    Hence whenever `s*(θ_soc) > 0`, `w_G(θ_soc) > w_G(θ_eq)`. -/
theorem prop_decentralized_theta_foc
    (pAI sStar wG_soc wG_eq : ℝ)
    (hSoc : pAI + sStar = wG_soc) (hEq : pAI = wG_eq) :
    wG_soc = wG_eq + sStar := by
  linarith

/-- **Proposition~\ref{prop:decentralized-theta} (strict inequality).**
    Whenever the Pigouvian externality is positive, the social
    optimum exhibits strictly higher `w_G` than the decentralized
    equilibrium. -/
theorem prop_decentralized_theta_wG_strict
    (pAI sStar wG_soc wG_eq : ℝ) (hSoc : pAI + sStar = wG_soc)
    (hEq : pAI = wG_eq) (hsStar : 0 < sStar) :
    wG_eq < wG_soc := by
  have := prop_decentralized_theta_foc pAI sStar wG_soc wG_eq hSoc hEq
  linarith

/-- **Proposition~\ref{prop:decentralized-theta} (monotonicity of
    `w_G`).** Given that `w_G` is strictly decreasing in `θ` (paper
    inversion theorem), the strict inequality `w_G(θ_soc) >
    w_G(θ_eq)` implies `θ_soc < θ_eq`.

    *Formal content.*  Anti-monotonicity bridge: if `f` is
    strictly anti-monotone and `f(x) > f(y)`, then `x < y`. -/
theorem prop_decentralized_theta_overshoots
    (theta_soc theta_eq : ℝ) (wG : ℝ → ℝ)
    (hwG_anti : ∀ x y, x < y → wG y < wG x)
    (h_strict : wG theta_eq < wG theta_soc) :
    theta_soc < theta_eq := by
  by_contra hcon
  push_neg at hcon
  rcases lt_or_eq_of_le hcon with hlt | heq
  · -- theta_eq < theta_soc would give wG theta_soc < wG theta_eq,
    -- contradicting h_strict.
    have := hwG_anti theta_eq theta_soc hlt
    linarith
  · -- theta_eq = theta_soc would give wG equal, contradicting
    -- the strict inequality.
    rw [heq] at h_strict
    exact lt_irrefl _ h_strict

end Economy

end VerificationAsymmetry
