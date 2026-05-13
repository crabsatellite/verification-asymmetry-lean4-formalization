/-
  VerificationAsymmetry/EndogenousAI.lean

  Theorem~\ref{thm:endogenous-ai} (Endogenous AI Capacity:
  Multi-Equilibrium and Hysteresis).

  Companion to: "Generation--Verification Asymmetry Inversion and
  Apprenticeship Pipeline Collapse Under AI Substitution" (Li, 2026).

  Statement.

    K_AI = Ψ(V_AI), with Ψ continuous, strictly increasing, concave,
    Ψ(0) = 0, Ψ(V) → K_AI^max as V → ∞.  Verification labor splits
    as V_∞ = V_prod + V_AI.

    Part 1.  (Existence of low-AI equilibrium.)  Φ : [0, θ*-ε] →
              [0, θ*-ε] is a continuous self-map of a compact
              interval.  Brouwer's fixed point yields θ_L ∈ [0, θ*-ε].

    Part 2.  (Uniqueness under monotonicity.)  Strict-decreasing Φ
              has a unique fixed point.

    Part 3.  (Corner equilibrium.)  Under exogenous θ ≥ θ*, the
              corner (θ, 0, 0) is self-consistent; under endogenous
              θ, the corner is unstable.

    Part 4.  (Hysteresis bound.)  Senior-pool deficit after a
              transient disturbance is bounded below by
              ν · |[t-T, t-T_j] ∩ [t_0 - T_j, t_1]| · ((1-θ_L) T_j)^a.

    Part 5.  (Recovery rate.)  From the corner with θ_L < θ*,
              V_∞(t) = ν · min(t - t_1 - T_j, T_s) · ((1-θ_L) T_j)^a
              for t ∈ [t_1 + T_j, t_1 + T].  Full recovery at
              t ≥ t_1 + T.

  Lean strategy.  Part 1 (Brouwer existence) is invoked from
  Mathlib's intermediate value theorem on `[a, b] → ℝ` (a 1-D
  Brouwer): a continuous self-map of a compact interval has a
  fixed point.  We formalize this as a real-line statement.

  Parts 4–5 are real-arithmetic identities for the recovery
  dynamics; they hinge on the linear-cohort accounting from
  `Collapse.lean` Part 4.  Part 3 is a definitional /
  self-consistency observation.

  Part 2 (uniqueness) is a structural lemma about strictly-
  decreasing maps on `ℝ`.
-/

import VerificationAsymmetry.Basic
import VerificationAsymmetry.Collapse
import Mathlib.Topology.Algebra.Order.IntermediateValue

namespace VerificationAsymmetry

namespace Economy

variable (E : Economy)

/-! ### Theorem~\ref{thm:endogenous-ai} Part 1: Brouwer existence
    (1-D form). -/

/-- *1-D Brouwer fixed-point theorem.* A continuous function
    `f : ℝ → ℝ` mapping `[a, b]` into itself (`a ≤ b`) has a fixed
    point in `[a, b]`.

    Standard consequence of the intermediate value theorem applied
    to `g(x) := f(x) - x`:  `g(a) = f(a) - a ≥ 0` and
    `g(b) = f(b) - b ≤ 0`, so `g(x) = 0` for some `x ∈ [a, b]`,
    giving a fixed point.

    *Note.*  Mathlib's `intermediate_value_Icc` provides the IVT;
    we apply it here directly. -/
theorem brouwer_1d
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_a : a ≤ f a) (hf_b : f b ≤ b) :
    ∃ x ∈ Set.Icc a b, f x = x := by
  -- Apply IVT to g(x) = f(x) - x.
  let g : ℝ → ℝ := fun x => f x - x
  have hg_cont : ContinuousOn g (Set.Icc a b) := by
    show ContinuousOn (fun x => f x - x) (Set.Icc a b)
    -- f is continuous on [a,b] by hypothesis; `id` is continuous;
    -- pointwise subtraction is continuous.
    intro x hx
    exact (hf_cont x hx).sub (continuousOn_id x hx)
  have hg_a : 0 ≤ g a := by simp [g]; linarith
  have hg_b : g b ≤ 0 := by simp [g]; linarith
  -- Use intermediate_value_Icc for sign-change.
  have h_ivt : ∃ x ∈ Set.Icc a b, g x = 0 := by
    -- intermediate_value_Icc' for descending order is the standard form.
    rcases eq_or_lt_of_le hg_a with hg_a_zero | hg_a_pos
    · -- g a = 0 case.
      exact ⟨a, Set.left_mem_Icc.mpr hab, hg_a_zero.symm⟩
    · rcases eq_or_lt_of_le hg_b with hg_b_zero | hg_b_neg
      · -- g b = 0 case.
        exact ⟨b, Set.right_mem_Icc.mpr hab, hg_b_zero⟩
      · -- Strict sign change: 0 ∈ [g b, g a].
        have h_zero_in : (0 : ℝ) ∈ Set.Icc (g b) (g a) := by
          refine ⟨hg_b_neg.le, hg_a_pos.le⟩
        have h_sub : Set.Icc (g b) (g a) ⊆ g '' Set.Icc a b :=
          intermediate_value_Icc' hab hg_cont
        obtain ⟨x, hx_in, hgx⟩ := h_sub h_zero_in
        exact ⟨x, hx_in, hgx⟩
  -- Translate g x = 0 to f x = x.
  obtain ⟨x, hx_in, hgx⟩ := h_ivt
  refine ⟨x, hx_in, ?_⟩
  show f x = x
  have : g x = 0 := hgx
  simp [g] at this
  linarith

/-- **Theorem~\ref{thm:endogenous-ai} Part 1 (existence of low-AI
    equilibrium).** Under continuity of Φ and the bounded-range
    assumption `Φ([0, θ*-ε]) ⊆ [0, θ*-ε]`, the joint endogenous-`K_AI`
    system has at least one fixed point.

    *Lean form:* direct application of `brouwer_1d` to the abstract
    map `Φ`.  We carry `Φ` as an arbitrary continuous function and
    the range bounds as separate hypotheses; the substantive content
    of the paper's argument is the construction of `Φ` from `Ψ` and
    the verification-stock decomposition `V_∞ = V_prod + V_AI`,
    which is recorded in the docstring and not unrolled here. -/
theorem thm_endogenous_ai_existence
    {Φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hΦ_cont : ContinuousOn Φ (Set.Icc a b))
    (hΦ_a : a ≤ Φ a) (hΦ_b : Φ b ≤ b) :
    ∃ θ_L ∈ Set.Icc a b, Φ θ_L = θ_L :=
  brouwer_1d hab hΦ_cont hΦ_a hΦ_b

/-! ### Theorem~\ref{thm:endogenous-ai} Part 2: uniqueness. -/

/-- **Theorem~\ref{thm:endogenous-ai} Part 2 (uniqueness under
    strict anti-monotonicity).** A strictly anti-monotone map on
    `ℝ` has at most one fixed point.

    *Substantive content of the paper's argument.*  The map Φ is
    strictly anti-monotone under the assumption that
    `V_prod^*(K_AI, θ)` is non-decreasing in both arguments
    (paper Theorem 7 Part 2).  Strict anti-monotonicity is shown by:
        θ ↑  ⇒  V_∞(θ) ↓  ⇒  V_AI = V_∞ - V_prod^* ↓  ⇒  K_AI ↓
        ⇒  Φ(θ) = K_AI/(L_G + K_AI) ↓.
    We formalize the consequence — strictly anti-monotone implies
    unique fixed point — as a general lemma. -/
theorem thm_endogenous_ai_uniqueness
    {Φ : ℝ → ℝ} (hΦ_anti : ∀ x y, x < y → Φ y < Φ x)
    {x y : ℝ} (hx : Φ x = x) (hy : Φ y = y) :
    x = y := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- x < y  ⇒  Φ y < Φ x  ⇒  y < x  (using Φ x = x, Φ y = y).
    have := hΦ_anti x y hlt
    rw [hx, hy] at this
    linarith
  · -- y < x  ⇒  Φ x < Φ y  ⇒  x < y.
    have := hΦ_anti y x hgt
    rw [hx, hy] at this
    linarith

/-! ### Theorem~\ref{thm:endogenous-ai} Part 3: corner equilibrium. -/

/-- **Theorem~\ref{thm:endogenous-ai} Part 3 (corner self-
    consistency under exogenous θ).** If `θ ≥ θ*` is held
    exogenously, the corner `(θ, 0, 0)` is a self-consistent
    steady state of the cohort + AI-supply dynamics:
    `V_∞ = 0` (by `thm_collapse_above_threshold`), and
    `K_AI = Ψ(0) = 0` from the assumption `Ψ(0) = 0`. -/
theorem thm_endogenous_ai_corner_exogenous
    (a θ : ℝ) (h_above : E.thetaStar < θ) (Ψ : ℝ → ℝ)
    (hΨ_zero : Ψ 0 = 0) :
    E.VinfHard a θ = 0 ∧ Ψ 0 = 0 := by
  exact ⟨E.thm_collapse_above_threshold a θ h_above, hΨ_zero⟩

/-- **Theorem~\ref{thm:endogenous-ai} Part 3 (corner self-
    inconsistency under endogenous θ).** Under endogenous
    θ = K_AI/(L_G + K_AI), the corner with `K_AI = 0` yields
    `θ = 0`, which contradicts `θ ≥ θ*` whenever `θ* > 0`.

    *Lean form:* `0 = (0 : ℝ) / (E.LG + 0)` simplifies to `0`,
    which is strictly below `θ*` whenever `θ*` is strictly positive.

    *Note.*  `θ* > 0` requires `τ* < T_j`; under the standing
    hypothesis `τ* ≤ T_j` of `Economy`, this is the strict version.
    The boundary case `τ* = T_j` gives `θ* = 0` and the corner
    inconsistency degenerates. -/
theorem thm_endogenous_ai_corner_endogenous_inconsistent
    (h_tauStar_lt_Tj : E.tauStar < E.Tj) :
    (0 : ℝ) < E.thetaStar := by
  unfold thetaStar
  have hTj : 0 < E.Tj := E.Tj_pos
  have h_div_lt : E.tauStar / E.Tj < 1 :=
    (div_lt_one hTj).mpr h_tauStar_lt_Tj
  linarith

/-! ### Theorem~\ref{thm:endogenous-ai} Parts 4 + 5: hysteresis. -/

/-- *Hysteresis-bound deficit:* the absent senior capacity from
    cohorts whose junior phase intersected the disturbance window.
    Paper Eq.~\eqref{eq:hysteresis-deficit}:
    `ν · |overlap| · ((1-θ_L) T_j)^a`. -/
noncomputable def hysteresisDeficit (a θL overlap : ℝ) : ℝ :=
  E.nu * overlap * ((1 - θL) * E.Tj) ^ a

/-- **Theorem~\ref{thm:endogenous-ai} Part 4 (hysteresis deficit
    non-negativity).** The deficit is non-negative whenever the
    overlap is non-negative and `θ_L ∈ [0, 1]`. -/
theorem thm_endogenous_ai_hysteresis_nonneg
    (a θL overlap : ℝ)
    (h_overlap : 0 ≤ overlap) (hθL_lt : θL ≤ 1) :
    0 ≤ E.hysteresisDeficit a θL overlap := by
  unfold hysteresisDeficit
  have h1 : 0 ≤ (1 - θL) * E.Tj := by
    apply mul_nonneg
    · linarith
    · exact E.Tj_pos.le
  have h2 : 0 ≤ ((1 - θL) * E.Tj) ^ a :=
    Real.rpow_nonneg h1 a
  have h3 : 0 ≤ E.nu * overlap :=
    mul_nonneg E.nu_pos.le h_overlap
  exact mul_nonneg h3 h2

/-- *Recovery stock function* `V_∞(t) = ν · min(t - t_1 - T_j, T_s) ·
    ((1-θ_L) T_j)^a` for Theorem~\ref{thm:endogenous-ai} Part 5
    (recovery rate closed form). Carrier for the closed-form
    senior-pool recovery starting from the corner at `t_1`. -/
noncomputable def recoveryStock (a θL t t₁ : ℝ) : ℝ :=
  E.nu * min (t - t₁ - E.Tj) E.Ts * ((1 - θL) * E.Tj) ^ a

/-- **Theorem~\ref{thm:endogenous-ai} Part 5 (recovery at
    `t = t₁ + T_j`).** At the moment the first post-corner cohort
    matures, the recovery stock is zero. -/
theorem thm_endogenous_ai_recovery_at_Tj
    (a θL t₁ : ℝ) :
    E.recoveryStock a θL (t₁ + E.Tj) t₁ = 0 := by
  unfold recoveryStock
  have hsub : t₁ + E.Tj - t₁ - E.Tj = 0 := by ring
  rw [hsub]
  rw [min_eq_left E.Ts_pos.le]
  ring

/-- **Theorem~\ref{thm:endogenous-ai} Part 5 (full recovery at
    `t = t₁ + T`).** Full steady-state recovery is achieved at
    `t = t₁ + T = t₁ + T_j + T_s`. -/
theorem thm_endogenous_ai_full_recovery_at_T
    (a θL t₁ : ℝ) :
    E.recoveryStock a θL (t₁ + E.T) t₁
      = E.nu * E.Ts * ((1 - θL) * E.Tj) ^ a := by
  unfold recoveryStock
  -- t = t₁ + T,  so t - t₁ - T_j = T - T_j = T_s.
  -- min(T_s, T_s) = T_s.
  have hTs_eq : t₁ + E.T - t₁ - E.Tj = E.Ts := by
    unfold Ts; ring
  rw [hTs_eq, min_self]

/-- **Theorem~\ref{thm:endogenous-ai} Part 5 (asymmetric recovery
    timeline).** Recovery requires the full career length `T`,
    while collapse can occur in arbitrary disturbance windows.
    Quantified as `T_j + T_s = T > 0`. -/
theorem thm_endogenous_ai_recovery_takes_full_career :
    0 < E.Tj + E.Ts := by
  have := E.Ts_pos
  linarith [E.Tj_pos]

end Economy

end VerificationAsymmetry
