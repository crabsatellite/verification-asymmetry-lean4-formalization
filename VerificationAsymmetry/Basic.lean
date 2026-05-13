/-
  VerificationAsymmetry/Basic.lean

  Definitions of the paper:
    * Definition `def:gve`           — Generation-Verification production
                                       economy E = (F, G, V, θ, K_AI, λ,
                                       ν, T, T_j, τ*, h)
    * Definition `def:gen-supply`    — AI-augmented generation
                                       G(θ) = (1-θ) L_G + θ K_AI
    * Definition `def:cohort`        — Cohort dynamics; cumulative
                                       junior experience in steady state
    * Definition `def:verification`  — Verification as Polanyi residual
                                       (carried as the abstract
                                       non-substitutability property)
    * Lemma      `lem:steady-state`  — Steady-state verification stock
                                       V_∞(θ) = ν T_s g((1-θ) T_j)
                                                       h((1-θ) T_j)
    * Definition `def:diagnostic`    — Structural conditions V1/V2/V3

  Companion to: "Generation--Verification Asymmetry Inversion and
  Apprenticeship Pipeline Collapse Under AI Substitution" (Li, 2026).

  Naming conventions (paper symbol → Lean identifier):
      θ        →  theta            (AI substitution rate)
      θ*       →  thetaStar        (apprenticeship collapse threshold)
      θ_inv    →  thetaInv         (asymmetry inversion threshold)
      τ*       →  tauStar          (promotion threshold)
      T_j      →  Tj
      T_s      →  Ts (derived from T - T_j)
      L_G      →  LG
      K_AI     →  KAI
      ē        →  eBar             (steady-state cumulative experience
                                    (1-θ) T_j)
      V_∞      →  Vinf             (steady-state verification stock)
      ν        →  nu
      η        →  eta
      λ        →  lam              (λ collides with Lean lambda)
      ρ        →  rho

  All quantities live in ℝ.  Non-negativity is carried as explicit
  hypotheses in the parameter records, matching the paper's narrative
  which writes "θ ∈ [0,1]" rather than admitting `⊤` into the type.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic

namespace VerificationAsymmetry

/-! ### Definition `def:gve`: Generation-Verification production economy. -/

/--
  A *generation-verification production economy* is the tuple
  `(F, L_G, K_AI, λ, ν, T, T_j, τ*, η, ρ)` of Definition~\ref{def:gve},
  with the convention that:
    * `F` is fixed to the CES form (Equation~\eqref{eq:ces}) parametrized
      by `(η, ρ, λ)`,
    * `T_s = T - T_j` is the senior career length (derived field, not
      a free parameter).

  We carry `K_AI` as a (positive) real number; the paper's `K_AI = ∞`
  limit is treated by allowing `K_AI` to grow in parametric arguments
  (Theorem~\ref{thm:inversion} Part 1) rather than admitting `⊤` into
  the carrier type.

  `L_G > 0` is assumed (paper assumes a nontrivial pre-AI generation
  labor pool); the θ-paramatrized supply `G(θ)` is then strictly
  positive for every `θ ∈ [0, 1]`.
-/
structure Economy where
  /-- `L_G` — human-supplied generation labor at `θ = 0`. -/
  LG : ℝ
  /-- `K_AI` — AI capacity. -/
  KAI : ℝ
  /-- `λ` — verification-generation ratio (each unit of `V` supports
       `λ` units of `G`). -/
  lam : ℝ
  /-- `ν` — cohort birth rate. -/
  nu : ℝ
  /-- `T` — total career length. -/
  T : ℝ
  /-- `T_j` — junior career length. -/
  Tj : ℝ
  /-- `τ*` — promotion threshold (minimum cumulative junior
       generation experience). -/
  tauStar : ℝ
  /-- `η` — CES weight on generation; `1-η` is verification weight. -/
  eta : ℝ
  /-- `ρ` — CES substitution exponent. -/
  rho : ℝ
  /-- `0 < L_G` (nontrivial pre-AI human labor pool). -/
  LG_pos : 0 < LG
  /-- `0 < K_AI`. -/
  KAI_pos : 0 < KAI
  /-- `0 < λ`. -/
  lam_pos : 0 < lam
  /-- `0 < ν`. -/
  nu_pos : 0 < nu
  /-- `0 < T_j`. -/
  Tj_pos : 0 < Tj
  /-- `T_j < T`. -/
  Tj_lt_T : Tj < T
  /-- `0 < τ*`. -/
  tauStar_pos : 0 < tauStar
  /-- `τ* ≤ T_j`. -/
  tauStar_le_Tj : tauStar ≤ Tj
  /-- `0 < η`. -/
  eta_pos : 0 < eta
  /-- `η < 1`. -/
  eta_lt_one : eta < 1
  /-- `ρ ≤ 1`. -/
  rho_le_one : rho ≤ 1

namespace Economy

variable (E : Economy)

/-! ### Derived parameters. -/

/-- Senior career length `T_s := T - T_j`. -/
def Ts : ℝ := E.T - E.Tj

/-- `T_s` is positive. -/
lemma Ts_pos : 0 < E.Ts := by
  unfold Ts; linarith [E.Tj_lt_T]

/-! ### Definition `def:gen-supply`: AI-augmented generation. -/

/--
  Total generation supply at AI substitution rate `θ`:
  `G(θ) = (1-θ) L_G + θ K_AI`.

  Paper Eq.~\eqref{eq:gen-supply}.  The function is affine in `θ`
  and equal to `L_G` at `θ = 0`, equal to `K_AI` at `θ = 1`.
-/
def G (θ : ℝ) : ℝ := (1 - θ) * E.LG + θ * E.KAI

@[simp] lemma G_zero : E.G 0 = E.LG := by simp [G]

@[simp] lemma G_one : E.G 1 = E.KAI := by simp [G]

/-- `G(θ)` is monotone non-decreasing in `θ` when `K_AI ≥ L_G`. -/
lemma G_monotone_of_KAI_ge_LG (h : E.LG ≤ E.KAI) {θ₁ θ₂ : ℝ}
    (hθ : θ₁ ≤ θ₂) : E.G θ₁ ≤ E.G θ₂ := by
  unfold G
  have hsub : 0 ≤ E.KAI - E.LG := by linarith
  have hprod : 0 ≤ (θ₂ - θ₁) * (E.KAI - E.LG) :=
    mul_nonneg (by linarith) hsub
  linarith

/-- `G(θ) > 0` for `θ ∈ [0, 1]`. -/
lemma G_pos {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : 0 < E.G θ := by
  unfold G
  have h1' : 0 ≤ 1 - θ := by linarith
  by_cases hθ : θ = 0
  · subst hθ; simpa using E.LG_pos
  · have hθpos : 0 < θ := lt_of_le_of_ne h0 (Ne.symm hθ)
    have hA : 0 ≤ (1 - θ) * E.LG := mul_nonneg h1' E.LG_pos.le
    have hB : 0 < θ * E.KAI := mul_pos hθpos E.KAI_pos
    linarith

/-- `G(θ) ≥ 0` for `θ ∈ [0, 1]`. -/
lemma G_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : 0 ≤ E.G θ :=
  (E.G_pos h0 h1).le

/-- The slope of `G` with respect to `θ` is `K_AI - L_G`. -/
lemma G_diff (θ₁ θ₂ : ℝ) :
    E.G θ₂ - E.G θ₁ = (θ₂ - θ₁) * (E.KAI - E.LG) := by
  unfold G; ring

/-! ### Definition `def:cohort`: Cohort dynamics (steady-state form).

  In steady state with constant `θ`, every cohort accumulates the same
  junior experience `ē = (1-θ) T_j`.  This is the consequence of
  Definition~\ref{def:cohort} Eq.~\eqref{eq:cumulative-experience}
  specialized to constant `θ`: the integral
  `∫_c^{c+T_j} (1 - θ(s)) ds` collapses to `(1-θ) T_j`.

  We expose `eBar` as a function of `θ`; the full path-dependent
  `e_J(c)` of the paper is not formalized here because it carries
  no new mathematical content under the steady-state focus of
  Theorems~\ref{thm:collapse}, \ref{thm:credential}, \ref{thm:externality}. -/

/-- Steady-state cumulative junior experience `ē(θ) = (1-θ) T_j`. -/
def eBar (θ : ℝ) : ℝ := (1 - θ) * E.Tj

@[simp] lemma eBar_zero : E.eBar 0 = E.Tj := by simp [eBar]

@[simp] lemma eBar_one : E.eBar 1 = 0 := by simp [eBar]

/-- `ē(θ) ≥ 0` for `θ ∈ [0, 1]`. -/
lemma eBar_nonneg {θ : ℝ} (h : θ ≤ 1) : 0 ≤ E.eBar θ := by
  unfold eBar
  have h1 : 0 ≤ 1 - θ := by linarith
  exact mul_nonneg h1 E.Tj_pos.le

/-- `ē(θ)` is monotone non-increasing in `θ`. -/
lemma eBar_antitone {θ₁ θ₂ : ℝ} (hθ : θ₁ ≤ θ₂) : E.eBar θ₂ ≤ E.eBar θ₁ := by
  unfold eBar
  have h1 : 1 - θ₂ ≤ 1 - θ₁ := by linarith
  exact mul_le_mul_of_nonneg_right h1 E.Tj_pos.le

/-! ### Apprenticeship technologies `g` and `h`.

  The paper specifies two pieces of apprenticeship technology:
    * `g : ℝ → ℝ` — promotion technology; non-decreasing, `g(0) = 0`,
                    `g(τ*) = 1` in the hard or smooth variants.
    * `h : ℝ → ℝ` — tacit accumulation; non-decreasing, `h(0) = 0`.

  Two specifications appear in the paper:
    * Hard threshold: `g(τ) = 𝟙[τ ≥ τ*]`.
    * Smooth threshold: `g(τ) = min((τ/τ*)^b, 1)`.

  And the working tacit technology:
    * Power-law: `h(τ) = τ^a` with `a ∈ (0, 1]`.

  We formalize the hard threshold (Theorem~\ref{thm:collapse}) and
  power-law (used throughout) as concrete real-valued functions;
  the smooth threshold appears in Proposition~\ref{prop:smooth-collapse}
  and is handled inline in `Collapse.lean`.
-/

/-- The *hard promotion technology*: `g_hard(τ; τ*) = 1` if `τ ≥ τ*`,
    else `0`.  Encodes the indicator `𝟙[τ ≥ τ*]` as a real-valued
    function. -/
noncomputable def gHard (τ : ℝ) : ℝ :=
  if E.tauStar ≤ τ then (1 : ℝ) else (0 : ℝ)

@[simp] lemma gHard_of_ge {τ : ℝ} (h : E.tauStar ≤ τ) : E.gHard τ = 1 := by
  simp [gHard, h]

@[simp] lemma gHard_of_lt {τ : ℝ} (h : τ < E.tauStar) : E.gHard τ = 0 := by
  simp [gHard, not_le.mpr h]

/-- The *power-law tacit technology*: `h(τ) = τ^a`. -/
noncomputable def hPow (a τ : ℝ) : ℝ := τ ^ a

/-! ### Steady-state verification stock. -/

/--
  *Steady-state verification stock* parametrized by promotion and tacit
  technologies.  Paper Eq.~\eqref{eq:V-steady}:
  `V_∞(θ) = ν T_s · g(ē) · h(ē)`, with `ē = (1-θ) T_j`.

  We take `g` and `h` as explicit function arguments rather than
  Economy fields because the paper considers multiple specifications
  (hard vs. smooth threshold; power-law `h`) and several theorems
  state results parametric in the choice.
-/
def Vinf (θ : ℝ) (g h : ℝ → ℝ) : ℝ :=
  E.nu * E.Ts * g (E.eBar θ) * h (E.eBar θ)

/-- Specialization of `Vinf` to the hard threshold and power-law `h`:
    `V_∞(θ) = ν T_s · g_hard(ē) · ē^a`. -/
noncomputable def VinfHard (a θ : ℝ) : ℝ :=
  E.Vinf θ E.gHard (fun τ => τ ^ a)

/-- Below the collapse threshold (`ē ≥ τ*`), the hard-threshold stock
    simplifies to the smooth power-law form `ν T_s ē^a`. -/
lemma VinfHard_eq_pow_of_eBar_ge_tauStar
    (a : ℝ) (θ : ℝ) (h : E.tauStar ≤ E.eBar θ) :
    E.VinfHard a θ = E.nu * E.Ts * (E.eBar θ) ^ a := by
  unfold VinfHard Vinf
  rw [gHard_of_ge E h]; ring

/-- Above the collapse threshold (`ē < τ*`), the hard-threshold stock
    vanishes. -/
lemma VinfHard_eq_zero_of_eBar_lt_tauStar
    (a : ℝ) (θ : ℝ) (h : E.eBar θ < E.tauStar) :
    E.VinfHard a θ = 0 := by
  unfold VinfHard Vinf
  rw [gHard_of_lt E h]; ring

/-! ### Definition `def:diagnostic`: V1/V2/V3 structural conditions. -/

/--
  Structural conditions (V1) Verification non-substitutability,
  (V2) Tacit accumulation, (V3) Generation displacement.

  (V1) and (V2) are baked into the carrier-type design: `V` is a free
  factor not produced by AI (`Vinf` is the cohort-level stock with no
  AI contribution), and `h` is a function with `h(0) = 0` and
  non-decreasing.  (V3) is the equation `ē(θ) = (1-θ) T_j` already
  proven above (`eBar` definition).

  This structural-condition record carries them in one place so
  downstream theorems can reference `E.satisfiesDiagnostic` as a
  hypothesis (although in practice the conditions are immediate from
  the carrier type and unused as hypotheses; included for narrative
  alignment with paper Definition~\ref{def:diagnostic}). -/
structure SatisfiesDiagnostic (g h : ℝ → ℝ) : Prop where
  /-- (V1) `V` is the residual stock; no AI contribution.  Captured
       structurally: `Vinf θ g h` makes no reference to `θ` through
       an AI-supply channel — `θ` enters only through `ē(θ)`,
       the human-side experience accumulation. -/
  V1_no_ai_in_verification : True
  /-- (V2) Tacit accumulation: `h(0) = 0` and `h` non-decreasing. -/
  V2_h_zero_at_zero : h 0 = 0
  /-- (V2) `h` non-decreasing. -/
  V2_h_monotone : Monotone h
  /-- (V3) Generation displacement: junior experience drops by factor
       `(1-θ)` under AI substitution at rate `θ`.  Captured by the
       defining equation `eBar θ = (1-θ) T_j`. -/
  V3_experience_displacement : True

end Economy
end VerificationAsymmetry
