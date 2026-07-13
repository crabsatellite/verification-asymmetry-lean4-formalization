/-
  VerificationAsymmetry/EndogenousAI.lean

  Theorem~\ref{thm:endogenous-ai} (Fixed Point and Recovery Accounting).

  Companion to: "Verification Asymmetry under AI Substitution:
  Wage-Ratio Inversion and Apprenticeship Thresholds" (Li, 2026).

  Statement.

    K_AI = Ψ(V_AI), with Ψ continuous, strictly increasing, concave,
    Ψ(0) = 0, Ψ(V) → K_AI^max as V → ∞.  Verification labor splits
    as V_∞ = V_prod + V_AI.

    Part 1.  (Conditional fixed-point existence.)  Φ : [0, θ*-ε] →
              [0, θ*-ε] is a continuous self-map of a compact
              interval.  Brouwer's fixed point yields θ_L ∈ [0, θ*-ε].

    Part 2.  (Conditional uniqueness.)  Strict-decreasing Φ
              has a unique fixed point.

    Part 3.  (Corner accounting.)  Under exogenous θ ≥ θ*, the
              verification stock is zero.  The special map
              θ_endo(K_AI)=K_AI/(L_G+K_AI) sends K_AI=0 to θ=0,
              which is incompatible with an additionally imposed θ≥θ*>0.

    Part 4.  (Worst-case deficit form.)  A declared maximum-loss
              senior-pool deficit after a transient disturbance is
              ν · |[t-T, t-T_j] ∩ [t_0 - T_j, t_1]| · ((1-θ_L) T_j)^a.

    Part 5.  (Recovery rate.)  From the corner with θ_L < θ*,
              V_∞(t) = ν · min(t - t_1 - T_j, T_s) · ((1-θ_L) T_j)^a
              for t ∈ [t_1 + T_j, t_1 + T].  Full recovery at
              t ≥ t_1 + T.

  Lean strategy.  Part 1 (Brouwer existence) is invoked from
  Mathlib's intermediate value theorem on `[a, b] → ℝ` (a 1-D
  Brouwer): a continuous self-map of a compact interval has a
  fixed point.  We formalize this as a real-line statement.

  Parts 4–5 verify real-arithmetic properties of DECLARED deficit and
  recovery functions.  They do not derive those functions from the full
  path-dependent cohort integral.  The ledger therefore marks the paper's
  complete recovery claim `gapPartial`.  Part 3 is a conditional
  self-consistency observation, not a proof of global instability.

  Part 2 (uniqueness) is a structural lemma about strictly-
  decreasing maps on `ℝ`.
-/

import VerificationAsymmetry.Basic
import VerificationAsymmetry.Collapse
import Mathlib.Topology.Order.IntermediateValue

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
    equilibrium — abstract Brouwer wrapper).** Under continuity of
    an abstract self-map `Φ : [a, b] → ℝ` with `Φ([a, b]) ⊆ [a, b]`
    (encoded as `a ≤ Φ a ∧ Φ b ≤ b`), Φ has at least one fixed
    point in `[a, b]`.

    *Scope.* This Lean theorem is the *abstract* 1-D Brouwer
    wrapper, applied to an arbitrary continuous Φ.  The paper's
    full Part 1 additionally constructs Φ from Ψ and the
    verification-stock decomposition `V_∞ = V_prod + V_AI` and
    proves its continuity from the primitives; that construction is
    *not* formalized in this Lean theorem — only the abstract
    fixed-point existence applied at the Φ level.  See Ledger entry
    `gap_thm_endogenous_ai_existence_PARTIAL.scope` for the explicit
    scope. -/
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
    exogenously, the verification stock vanishes: `V_∞(θ) = 0`.
    Combined with the assumption `Ψ(0) = 0` (paper-stipulated
    Ψ-shape), the corner `(θ, 0, 0)` is a self-consistent steady
    state of the cohort + AI-supply dynamics.

    *Substantive content of the Lean theorem:* the vanishing of
    `V_∞` above `θ*` is the substantive part; `Ψ(0) = 0` is the
    paper's stipulation on the Ψ shape, recorded in the hypothesis
    and not re-derived as a conclusion. -/
theorem thm_endogenous_ai_corner_exogenous
    (a θ : ℝ) (h_above : E.thetaStar < θ) :
    E.VinfHard a θ = 0 :=
  E.thm_collapse_above_threshold a θ h_above

/-- *Endogenous θ map under capacity-share rule.* The paper's
    endogenous θ in Theorem~\ref{thm:endogenous-ai} Part 3 is
    `θ_endo(K_AI) := K_AI / (L_G + K_AI)`. -/
noncomputable def thetaEndo (KAI : ℝ) : ℝ := KAI / (E.LG + KAI)

/-- *Endogenous θ at `K_AI = 0`.*  `θ_endo(0) = 0`. -/
lemma thetaEndo_zero : E.thetaEndo 0 = 0 := by
  unfold thetaEndo
  simp

/-- **Theorem~\ref{thm:endogenous-ai} Part 3 (corner self-
    inconsistency witness under endogenous θ).** Under endogenous
    θ = K_AI/(L_G + K_AI), the corner with `K_AI = 0` yields
    `θ_endo(0) = 0`.  When `τ* < T_j` (so `θ* > 0`), the
    endogenous output `θ_endo(0) = 0` lies STRICTLY BELOW the
    corner requirement `θ ≥ θ* > 0`, witnessing the inconsistency:
    the K_AI=0 corner is NOT a fixed point of the endogenous map
    (any θ ≥ θ* would need K_AI > 0, but K_AI = 0 yields θ = 0).

    *Formal content:* the strict inequality `θ_endo(0) < θ*` is
    the inconsistency witness: the corner needs `θ ≥ θ*` but the
    endogenous map at `K_AI = 0` returns `0 < θ*`. -/
theorem thm_endogenous_ai_corner_endogenous_inconsistent
    (h_tauStar_lt_Tj : E.tauStar < E.Tj) :
    E.thetaEndo 0 < E.thetaStar := by
  rw [E.thetaEndo_zero]
  unfold thetaStar
  have hTj : 0 < E.Tj := E.Tj_pos
  have h_div_lt : E.tauStar / E.Tj < 1 :=
    (div_lt_one hTj).mpr h_tauStar_lt_Tj
  linarith

/-! ### Theorem~\ref{thm:endogenous-ai} Parts 4 + 5: recovery accounting. -/

/-- *Declared worst-case deficit:* the maximum absent senior capacity from
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
    timeline).** Recovery to the steady-state stock requires the
    FULL career length `T = T_j + T_s` to elapse beyond the corner
    exit `t_1`.  For any earlier `t < t_1 + T`, the recovery stock
    is strictly below the steady-state value (the linear ramp
    `ν · (t - t_1 - T_j) · ē^a` has not yet hit its `ν T_s ē^a`
    ceiling).

    Formal content: for `t_1 + T_j ≤ t < t_1 + T`, the recovery
    stock `recoveryStock a θL t t₁` is `< ν · T_s · ((1-θL) T_j)^a`. -/
theorem thm_endogenous_ai_recovery_takes_full_career
    (a θL t t₁ : ℝ)
    (h_after_juniors : t₁ + E.Tj ≤ t) (h_before_full : t < t₁ + E.T)
    (h_eBar_pos : 0 < ((1 - θL) * E.Tj) ^ a) :
    E.recoveryStock a θL t t₁
      < E.nu * E.Ts * ((1 - θL) * E.Tj) ^ a := by
  unfold recoveryStock
  have hTs_pos : 0 < E.Ts := E.Ts_pos
  -- t - t₁ - T_j < T - T_j = T_s
  have h_lt : t - t₁ - E.Tj < E.Ts := by
    unfold Ts; linarith
  -- t - t₁ - T_j ≥ 0
  have h_ge : 0 ≤ t - t₁ - E.Tj := by linarith
  -- min(t - t₁ - T_j, T_s) = t - t₁ - T_j  (since t - t₁ - T_j ≤ T_s).
  have h_min : min (t - t₁ - E.Tj) E.Ts = t - t₁ - E.Tj :=
    min_eq_left h_lt.le
  rw [h_min]
  -- Goal: ν * (t - t₁ - T_j) * ē^a < ν * T_s * ē^a.
  have hnu : 0 < E.nu := E.nu_pos
  have h_left  : 0 ≤ E.nu * (t - t₁ - E.Tj) :=
    mul_nonneg hnu.le h_ge
  have h_mul_lt : E.nu * (t - t₁ - E.Tj) < E.nu * E.Ts := by
    have := h_lt
    nlinarith
  nlinarith [h_eBar_pos]

end Economy

end VerificationAsymmetry
