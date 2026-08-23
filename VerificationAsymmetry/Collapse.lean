/-
  VerificationAsymmetry/Collapse.lean

  Theorem~\ref{thm:collapse} (Apprenticeship Pipeline Collapse) and
  Proposition~\ref{prop:smooth-collapse} (Smooth-Threshold Collapse).

  Companion to: "Verification Asymmetry under AI Substitution:
  Wage-Ratio Inversion and Apprenticeship Thresholds" (Li, 2026).

  Statement.

    Apprenticeship collapse threshold:  θ* := 1 - τ*/T_j.

    Part 1.  For θ < θ* in steady state: V_∞(θ) = ν T_s ((1-θ) T_j)^a.
    Part 2.  Jump discontinuity at θ*:
              V_∞(θ*⁻) - V_∞(θ*⁺) = ν T_s (τ*)^a.
    Part 3.  Long-run zero stock above θ*: V_∞(θ) = 0.
    Part 4.  Pre-shock-senior component:
              V_pre(t) = V_∞(θ₀) · (1 - t/T_s)_+.
              The complete straddling-cohort path and the proved zero-stock
              bound after the last straddling cohort retires are encoded in
              `CohortPath.lean`.
    Part 5.  Threshold value for arbitrary h; a left-limit statement
              additionally needs the paper's one-sided-continuity premise.

  Lean strategy.  The encoded algebraic subclaims are real-arithmetic identities once
  one has the `Vinf` carrier of `Basic.lean`.  The threshold equation
  `θ* = 1 - τ*/T_j` is the defining equation; we formalize it as
  a derived field.  Parts 1–3, 5 are direct algebraic consequences
  of `VinfHard_eq_pow_of_eBar_ge_tauStar` and
  `VinfHard_eq_zero_of_eBar_lt_tauStar` from `Basic.lean`.  Part 4
  (transient decay) is only a real-valued algebraic identity for the
  retiring PRE-SHOCK senior component.  The ledger marks the complete
  paper transient `gapPartial`.
-/

import VerificationAsymmetry.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace VerificationAsymmetry

namespace Economy

variable (E : Economy)

open Filter

/-! ### Apprenticeship collapse threshold `θ*`. -/

/-- *Apprenticeship collapse threshold* `θ* := 1 - τ* / T_j`.

    Paper Eq.~\eqref{eq:thetastar}. -/
noncomputable def thetaStar : ℝ := 1 - E.tauStar / E.Tj

/-- `θ*` lies in `[0, 1)` whenever `0 < τ* ≤ T_j`. -/
lemma thetaStar_in_unit_interval :
    0 ≤ E.thetaStar ∧ E.thetaStar < 1 := by
  unfold thetaStar
  refine ⟨?_, ?_⟩
  · -- 0 ≤ 1 - τ*/T_j  ↔  τ*/T_j ≤ 1
    have h : E.tauStar / E.Tj ≤ 1 := by
      rw [div_le_one E.Tj_pos]
      exact E.tauStar_le_Tj
    linarith
  · -- 1 - τ*/T_j < 1  ↔  0 < τ*/T_j
    have h : 0 < E.tauStar / E.Tj :=
      div_pos E.tauStar_pos E.Tj_pos
    linarith

/-! ### Key bridge: `θ ≤ θ*` ↔ `ē(θ) ≥ τ*`. -/

/-- *Threshold reformulation.* The condition `θ ≤ θ*` for the
    apprenticeship pipeline (equivalently `ē(θ) ≥ τ*`) is the
    algebraic consequence of `θ* = 1 - τ*/T_j` and
    `ē(θ) = (1-θ) T_j`.

    This bridge is heavily used in the proofs below. -/
lemma eBar_ge_tauStar_iff_theta_le_thetaStar (θ : ℝ) :
    E.tauStar ≤ E.eBar θ ↔ θ ≤ E.thetaStar := by
  unfold eBar thetaStar
  constructor
  · intro h
    -- τ* ≤ (1 - θ) T_j  →  τ*/T_j ≤ 1 - θ  →  θ ≤ 1 - τ*/T_j.
    have hTj : 0 < E.Tj := E.Tj_pos
    have h' : E.tauStar / E.Tj ≤ 1 - θ :=
      (div_le_iff₀ hTj).mpr (by linarith)
    linarith
  · intro h
    -- θ ≤ 1 - τ*/T_j  →  τ*/T_j ≤ 1 - θ  →  τ* ≤ (1 - θ) T_j.
    have hTj : 0 < E.Tj := E.Tj_pos
    have h' : E.tauStar / E.Tj ≤ 1 - θ := by linarith
    exact (div_le_iff₀ hTj).mp h'

/-- *Strict variant of the threshold reformulation.* `θ > θ*` iff
    `ē(θ) < τ*`. -/
lemma eBar_lt_tauStar_iff_theta_gt_thetaStar (θ : ℝ) :
    E.eBar θ < E.tauStar ↔ E.thetaStar < θ := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have := (E.eBar_ge_tauStar_iff_theta_le_thetaStar θ).mpr hcon
    linarith
  · intro h
    by_contra hcon
    push Not at hcon
    have := (E.eBar_ge_tauStar_iff_theta_le_thetaStar θ).mp hcon
    linarith

@[simp] lemma eBar_thetaStar : E.eBar E.thetaStar = E.tauStar := by
  unfold eBar thetaStar
  have hTj_ne : E.Tj ≠ 0 := ne_of_gt E.Tj_pos
  field_simp
  ring

/-! ### Theorem~\ref{thm:collapse} Part 1: smooth power-law below θ*. -/

/-- **Theorem~\ref{thm:collapse} Part 1 (below collapse).** For
    `θ ≤ θ*`, the steady-state verification stock under the hard
    promotion threshold and power-law tacit technology is
    `V_∞(θ) = ν T_s · ((1-θ) T_j)^a`. -/
theorem thm_collapse_below_threshold
    (a θ : ℝ) (h : θ ≤ E.thetaStar) :
    E.VinfHard a θ = E.nu * E.Ts * (E.eBar θ) ^ a := by
  have h' : E.tauStar ≤ E.eBar θ :=
    (E.eBar_ge_tauStar_iff_theta_le_thetaStar θ).mpr h
  exact E.VinfHard_eq_pow_of_eBar_ge_tauStar a θ h'

/-- The derivative displayed in Theorem 10 Part 1. -/
noncomputable def hardStockSlopeBelow (a theta : ℝ) : ℝ :=
  -a * E.nu * E.Ts * E.Tj * (E.eBar theta) ^ (a - 1)

/-- **Theorem~\ref{thm:collapse} Part 1 (displayed derivative).**
    At every point strictly below the hard threshold, the displayed power-law
    stock has derivative
    `-a * nu * T_s * T_j * ((1-theta)T_j)^(a-1)`. -/
theorem hasDerivAt_hard_stock_below
    (a theta : ℝ) (htheta : theta < E.thetaStar) :
    HasDerivAt
      (fun x => E.nu * E.Ts * (E.eBar x) ^ a)
      (E.hardStockSlopeBelow a theta) theta := by
  have htheta_one : theta < 1 := lt_trans htheta E.thetaStar_in_unit_interval.2
  have heBar_pos : 0 < E.eBar theta := by
    unfold eBar
    exact mul_pos (by linarith) E.Tj_pos
  have hlinear : HasDerivAt (fun x : ℝ => 1 - x) (-1) theta := by
    simpa using (hasDerivAt_const theta (1 : ℝ)).sub (hasDerivAt_id theta)
  have heBar : HasDerivAt (fun x => E.eBar x) (-E.Tj) theta := by
    simpa [eBar] using hlinear.mul_const E.Tj
  have hpow := heBar.rpow_const (p := a) (Or.inl (ne_of_gt heBar_pos))
  have hscaled := hpow.const_mul (E.nu * E.Ts)
  convert hscaled using 1
  unfold hardStockSlopeBelow
  ring

/-- Under the paper's `a>0` premise, the below-threshold derivative is strictly
    negative, not merely non-positive. -/
theorem hardStockSlopeBelow_neg
    {a theta : ℝ} (ha : 0 < a) (htheta : theta < E.thetaStar) :
    E.hardStockSlopeBelow a theta < 0 := by
  have htheta_one : theta < 1 := lt_trans htheta E.thetaStar_in_unit_interval.2
  have heBar_pos : 0 < E.eBar theta := by
    unfold eBar
    exact mul_pos (by linarith) E.Tj_pos
  have hpow : 0 < (E.eBar theta) ^ (a - 1) :=
    Real.rpow_pos_of_pos heBar_pos _
  unfold hardStockSlopeBelow
  have hproduct : 0 < a * E.nu * E.Ts * E.Tj * (E.eBar theta) ^ (a - 1) := by
    exact mul_pos (mul_pos (mul_pos (mul_pos ha E.nu_pos) E.Ts_pos) E.Tj_pos) hpow
  nlinarith

/-! ### Theorem~\ref{thm:collapse} Part 3: zero stock above θ*. -/

/-- **Theorem~\ref{thm:collapse} Part 3 (above collapse).** For
    `θ > θ*`, the steady-state stock vanishes:
    `V_∞(θ) = 0`. -/
theorem thm_collapse_above_threshold
    (a θ : ℝ) (h : E.thetaStar < θ) :
    E.VinfHard a θ = 0 := by
  have h' : E.eBar θ < E.tauStar :=
    (E.eBar_lt_tauStar_iff_theta_gt_thetaStar θ).mpr h
  exact E.VinfHard_eq_zero_of_eBar_lt_tauStar a θ h'

/-! ### Theorem~\ref{thm:collapse} Part 2: jump magnitude. -/

/-- **Theorem~\ref{thm:collapse} Part 2 (jump at threshold).** At
    the collapse threshold, the value `V_∞(θ*)` equals
    `ν T_s (τ*)^a` (left limit), while the value just above is
    `0` (right limit), giving a jump of `ν T_s (τ*)^a`. -/
theorem thm_collapse_jump_magnitude (a : ℝ) :
    E.VinfHard a E.thetaStar = E.nu * E.Ts * (E.tauStar) ^ a := by
  -- At θ = θ*, ē(θ*) = (1 - θ*) T_j = (τ*/T_j) · T_j = τ*.
  have hθStar_le : E.thetaStar ≤ E.thetaStar := le_refl _
  have hBelow := E.thm_collapse_below_threshold a E.thetaStar hθStar_le
  -- Need ē(θ*) = τ*.
  have hTj_ne : E.Tj ≠ 0 := ne_of_gt E.Tj_pos
  have heBar_eq : E.eBar E.thetaStar = E.tauStar := by
    unfold eBar thetaStar
    field_simp
    ring
  rw [hBelow, heBar_eq]

/-- **Theorem~\ref{thm:collapse} Part 2 (jump statement, discrete-
    difference form).** For any `θ_above > θ*`, the difference
    `V_∞(θ*) - V_∞(θ_above)` equals `ν T_s (τ*)^a`.

    *Scope.* This is the discrete-difference form of the paper's
    one-sided-limit claim `V_∞(θ*) - lim_{θ ↘ θ*} V_∞(θ) =
    ν T_s (τ*)^a`.  Since `V_∞(θ_above) = 0` uniformly for every
    `θ_above > θ*` (Part 3), the one-sided limit reduces to `0`,
    and the discrete difference equals the limit difference.  The
    continuous right-limit machinery is not invoked because the
    paper claim follows directly from the uniform vanishing of
    `V_∞` above `θ*`. -/
theorem thm_collapse_jump_diff
    (a : ℝ) {θ_above : ℝ} (h : E.thetaStar < θ_above) :
    E.VinfHard a E.thetaStar - E.VinfHard a θ_above
      = E.nu * E.Ts * (E.tauStar) ^ a := by
  rw [E.thm_collapse_above_threshold a θ_above h,
      E.thm_collapse_jump_magnitude a]
  ring

/-- The hard-threshold stock is left-continuous at `thetaStar`, with the exact
    paper value `nu*T_s*(tauStar)^a`. -/
theorem VinfHard_tendsto_left_at_thetaStar (a : ℝ) :
    Tendsto (fun theta => E.VinfHard a theta)
      (nhdsWithin E.thetaStar (Set.Iic E.thetaStar))
      (nhds (E.nu * E.Ts * E.tauStar ^ a)) := by
  have heBar_cont : ContinuousAt (fun theta => E.eBar theta) E.thetaStar := by
    unfold eBar
    fun_prop
  have hpow_cont : ContinuousAt (fun theta => E.eBar theta ^ a) E.thetaStar :=
    heBar_cont.rpow_const (Or.inl (by
      rw [E.eBar_thetaStar]
      exact ne_of_gt E.tauStar_pos))
  have hcont : ContinuousAt
      (fun theta => E.nu * E.Ts * E.eBar theta ^ a) E.thetaStar := by
    fun_prop
  have htend : Tendsto (fun theta => E.nu * E.Ts * E.eBar theta ^ a)
      (nhdsWithin E.thetaStar (Set.Iic E.thetaStar))
      (nhds (E.nu * E.Ts * E.tauStar ^ a)) := by
    convert hcont.tendsto.mono_left inf_le_left using 1
    rw [E.eBar_thetaStar]
  have heq :
      (fun theta => E.VinfHard a theta) =ᶠ[
        nhdsWithin E.thetaStar (Set.Iic E.thetaStar)]
      (fun theta => E.nu * E.Ts * E.eBar theta ^ a) := by
    filter_upwards [self_mem_nhdsWithin] with theta htheta
    exact E.thm_collapse_below_threshold a theta htheta
  exact htend.congr' heq.symm

/-- Immediately to the right of `thetaStar`, the hard-threshold stock has
    right limit zero. -/
theorem VinfHard_tendsto_right_zero_at_thetaStar (a : ℝ) :
    Tendsto (fun theta => E.VinfHard a theta)
      (nhdsWithin E.thetaStar (Set.Ioi E.thetaStar)) (nhds 0) := by
  have heq :
      (fun theta => E.VinfHard a theta) =ᶠ[
        nhdsWithin E.thetaStar (Set.Ioi E.thetaStar)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with theta htheta
    exact E.thm_collapse_above_threshold a theta htheta
  exact tendsto_const_nhds.congr' heq.symm

/-! ### Theorem~\ref{thm:collapse} Part 4: transient decay. -/

/-- *Transient stock function* `V(t)` from paper Eq.~\eqref{eq:transient}:
    `V(t) = V_∞(θ₀) · (1 - t/T_s)_+`.

    Encoded directly as the real-valued positive-part formula.
    The bound `(1 - t/T_s)_+` corresponds to the fraction of the
    senior cohort that has not yet retired at time `t`. -/
noncomputable def transientStock (Vinf_init t : ℝ) : ℝ :=
  Vinf_init * max (0 : ℝ) (1 - t / E.Ts)

/-- **Theorem~\ref{thm:collapse} Part 4 (transient decay at t=0).** At
    `t = 0` (regime change), the transient stock equals the
    pre-change steady-state: `V(0) = V_∞(θ₀)`. -/
theorem thm_collapse_transient_at_zero (Vinf_init : ℝ) :
    E.transientStock Vinf_init 0 = Vinf_init := by
  unfold transientStock
  simp

/-- **Theorem~\ref{thm:collapse} Part 4 (transient decay at t=T_s).** At
    the end of the senior career length, the transient stock
    reaches zero: `V(T_s) = 0`. -/
theorem thm_collapse_transient_at_Ts (Vinf_init : ℝ) :
    E.transientStock Vinf_init E.Ts = 0 := by
  unfold transientStock
  have hTs_pos : 0 < E.Ts := E.Ts_pos
  have h : (1 : ℝ) - E.Ts / E.Ts = 0 := by
    have : E.Ts / E.Ts = 1 := div_self (ne_of_gt hTs_pos)
    linarith
  rw [h, max_self, mul_zero]

/-- **Theorem~\ref{thm:collapse} Part 4 (transient decay is linear
    on `[0, T_s]`).** For `t ∈ [0, T_s]`, the transient stock is
    `V_∞(θ₀) · (1 - t/T_s)`.

    The `_ht_nonneg` hypothesis (`0 ≤ t`) is carried for paper-
    faithful signature parity (the paper states the linear regime
    on `[0, T_s]`) but is `_`-prefixed: the `max`-branch evaluation
    `max 0 (1 - t/T_s) = 1 - t/T_s` follows from `t ≤ T_s` alone
    (which gives `1 - t/T_s ≥ 0`). -/
theorem thm_collapse_transient_linear
    (Vinf_init t : ℝ) (_ht_nonneg : 0 ≤ t) (ht_le_Ts : t ≤ E.Ts) :
    E.transientStock Vinf_init t = Vinf_init * (1 - t / E.Ts) := by
  unfold transientStock
  have hTs_pos : 0 < E.Ts := E.Ts_pos
  have h : 0 ≤ 1 - t / E.Ts := by
    have h1 : t / E.Ts ≤ 1 := (div_le_one hTs_pos).mpr ht_le_Ts
    linarith
  rw [max_eq_right h]

/-- **Theorem~\ref{thm:collapse} Part 4 (decay after T_s).** For
    `t ≥ T_s`, the transient stock is exhausted: `V(t) = 0`. -/
theorem thm_collapse_transient_zero_after_Ts
    (Vinf_init t : ℝ) (ht : E.Ts ≤ t) :
    E.transientStock Vinf_init t = 0 := by
  unfold transientStock
  have hTs_pos : 0 < E.Ts := E.Ts_pos
  have h : 1 - t / E.Ts ≤ 0 := by
    have h1 : 1 ≤ t / E.Ts := (one_le_div hTs_pos).mpr ht
    linarith
  rw [max_eq_left h, mul_zero]

/-! ### Theorem~\ref{thm:collapse} Part 5: lower bound generalization. -/

/-- **Theorem~\ref{thm:collapse} Part 5 (general `h` value at θ*).**
    For any tacit technology `h` (taken as an arbitrary `ℝ → ℝ`
    function) and the hard promotion threshold, the steady-state
    stock at the collapse threshold equals exactly `ν T_s h(τ*)`.

    Combined with the uniform vanishing `V_∞ ≡ 0` above `θ*`
    (`thm_collapse_above_threshold`), the jump magnitude at `θ*`
    equals `ν T_s h(τ*)` for any `h`.  The lower-bound form of
    Part 5 follows when `h(τ*) > 0` (monotone-`h` regime); the
    Lean theorem captures the exact value identity, with the
    sign/positivity of the jump traced from positivity of
    `h(τ*)` separately by the consumer. -/
theorem thm_collapse_value_at_thetaStar_general_h
    (h : ℝ → ℝ) :
    E.Vinf E.thetaStar E.gHard h = E.nu * E.Ts * h E.tauStar := by
  unfold Vinf
  -- At θ = θ*, ē(θ*) = τ*; g_hard(τ*) = 1.
  have hTj_ne : E.Tj ≠ 0 := ne_of_gt E.Tj_pos
  have heBar : E.eBar E.thetaStar = E.tauStar := by
    unfold eBar thetaStar
    field_simp
    ring
  rw [heBar]
  rw [E.gHard_of_ge (le_refl E.tauStar)]
  ring

/-! ### Proposition~\ref{prop:smooth-collapse}: smooth-threshold decay. -/

/-- *Smooth promotion technology* `g_smooth(τ; τ*, b) = (τ/τ*)^b`
    for `τ ≤ τ*`, equal to `1` for `τ ≥ τ*`.

    Encoded inline; the conditional structure matches the paper's
    `min((τ/τ*)^b, 1)` form. -/
noncomputable def gSmooth (b τ : ℝ) : ℝ :=
  if E.tauStar ≤ τ then (1 : ℝ) else (τ / E.tauStar) ^ b

/-- **Proposition~\ref{prop:smooth-collapse} (below θ*).** For
    `θ ≤ θ*` under smooth threshold, the stock matches the hard-
    threshold value `ν T_s ((1-θ) T_j)^a`. -/
theorem prop_smooth_collapse_below
    (a b θ : ℝ) (h : θ ≤ E.thetaStar) :
    E.Vinf θ (E.gSmooth b) (fun τ => τ ^ a)
      = E.nu * E.Ts * (E.eBar θ) ^ a := by
  unfold Vinf gSmooth
  have h' : E.tauStar ≤ E.eBar θ :=
    (E.eBar_ge_tauStar_iff_theta_le_thetaStar θ).mpr h
  simp [h']

/-- **Proposition~\ref{prop:smooth-collapse} (above θ*).** For
    `θ > θ*` under smooth threshold, the stock decays as
    `(1-θ)^{a+b}`:
    `V_∞(θ) = ν T_s · ((1-θ) T_j/τ*)^b · ((1-θ) T_j)^a`. -/
theorem prop_smooth_collapse_above
    (a b θ : ℝ) (h : E.thetaStar < θ) :
    E.Vinf θ (E.gSmooth b) (fun τ => τ ^ a)
      = E.nu * E.Ts * ((E.eBar θ) / E.tauStar) ^ b * (E.eBar θ) ^ a := by
  unfold Vinf gSmooth
  have h' : E.eBar θ < E.tauStar :=
    (E.eBar_lt_tauStar_iff_theta_gt_thetaStar θ).mpr h
  -- The `if` branch evaluates to (eBar θ / τ*)^b since ē < τ*.
  have hbranch : ¬ (E.tauStar ≤ E.eBar θ) := not_le.mpr h'
  simp [hbranch]

/-! ### Proposition~\ref{prop:smooth-collapse}: slope kink at θ*. -/

/-- Left derivative displayed in the paper at the smooth-promotion threshold. -/
noncomputable def smoothSlopeBelowAtThreshold (a : ℝ) : ℝ :=
  -a * E.nu * E.Ts * E.Tj * E.tauStar ^ (a - 1)

/-- Right derivative displayed in the paper at the smooth-promotion threshold. -/
noncomputable def smoothSlopeAboveAtThreshold (a b : ℝ) : ℝ :=
  -(a + b) * E.nu * E.Ts * E.Tj * E.tauStar ^ (a - 1)

/-- The right slope magnitude is strictly larger than the left slope magnitude
    for `a>0`, `b>0`, exactly as stated in Proposition 11. -/
theorem prop_smooth_collapse_kink
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |E.smoothSlopeBelowAtThreshold a| <
      |E.smoothSlopeAboveAtThreshold a b| := by
  have hpow : 0 < E.tauStar ^ (a - 1) :=
    Real.rpow_pos_of_pos E.tauStar_pos _
  have hbase : 0 < E.nu * E.Ts * E.Tj * E.tauStar ^ (a - 1) := by
    exact mul_pos (mul_pos (mul_pos E.nu_pos E.Ts_pos) E.Tj_pos) hpow
  have hbelow :
      E.smoothSlopeBelowAtThreshold a =
        -(a * (E.nu * E.Ts * E.Tj * E.tauStar ^ (a - 1))) := by
    unfold smoothSlopeBelowAtThreshold
    ring
  have habove :
      E.smoothSlopeAboveAtThreshold a b =
        -((a + b) * (E.nu * E.Ts * E.Tj * E.tauStar ^ (a - 1))) := by
    unfold smoothSlopeAboveAtThreshold
    ring
  rw [hbelow, habove, abs_neg, abs_neg,
      abs_of_pos (mul_pos ha hbase),
      abs_of_pos (mul_pos (by linarith) hbase)]
  nlinarith

/-- The below-threshold stock has the paper's displayed left derivative at the
    threshold. -/
theorem hasDerivAt_smooth_stock_below_at_threshold (a : ℝ) :
    HasDerivAt
      (fun theta => E.nu * E.Ts * (E.eBar theta) ^ a)
      (E.smoothSlopeBelowAtThreshold a) E.thetaStar := by
  have hlinear : HasDerivAt (fun theta : ℝ => 1 - theta) (-1) E.thetaStar := by
    simpa using (hasDerivAt_const E.thetaStar (1 : ℝ)).sub
      (hasDerivAt_id E.thetaStar)
  have heBar : HasDerivAt (fun theta => E.eBar theta) (-E.Tj) E.thetaStar := by
    simpa [eBar] using hlinear.mul_const E.Tj
  have hpow := heBar.rpow_const (p := a) (Or.inl (by
    rw [E.eBar_thetaStar]
    exact ne_of_gt E.tauStar_pos))
  rw [E.eBar_thetaStar] at hpow
  have hscaled := hpow.const_mul (E.nu * E.Ts)
  convert hscaled using 1
  unfold smoothSlopeBelowAtThreshold
  ring

/-- The above-threshold smooth stock has the paper's displayed right derivative
    at the threshold. -/
theorem hasDerivAt_smooth_stock_above_at_threshold (a b : ℝ) :
    HasDerivAt
      (fun theta =>
        E.nu * E.Ts * ((E.eBar theta) / E.tauStar) ^ b *
          (E.eBar theta) ^ a)
      (E.smoothSlopeAboveAtThreshold a b) E.thetaStar := by
  have hlinear : HasDerivAt (fun theta : ℝ => 1 - theta) (-1) E.thetaStar := by
    simpa using (hasDerivAt_const E.thetaStar (1 : ℝ)).sub
      (hasDerivAt_id E.thetaStar)
  have heBar : HasDerivAt (fun theta => E.eBar theta) (-E.Tj) E.thetaStar := by
    simpa [eBar] using hlinear.mul_const E.Tj
  have hratio : HasDerivAt (fun theta => E.eBar theta / E.tauStar)
      (-E.Tj / E.tauStar) E.thetaStar := heBar.div_const E.tauStar
  have hratio_value : E.eBar E.thetaStar / E.tauStar = 1 := by
    rw [E.eBar_thetaStar]
    exact div_self (ne_of_gt E.tauStar_pos)
  have hratio_pow := hratio.rpow_const (p := b)
    (Or.inl (by rw [hratio_value]; norm_num))
  have heBar_pow := heBar.rpow_const (p := a)
    (Or.inl (by rw [E.eBar_thetaStar]; exact ne_of_gt E.tauStar_pos))
  rw [hratio_value] at hratio_pow
  rw [E.eBar_thetaStar] at heBar_pow
  have hprod := hratio_pow.mul heBar_pow
  have hscaled := hprod.const_mul (E.nu * E.Ts)
  have htau_ne : E.tauStar ≠ 0 := ne_of_gt E.tauStar_pos
  convert hscaled using 1
  · funext theta
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  · unfold smoothSlopeAboveAtThreshold
    simp [E.eBar_thetaStar, htau_ne]
    rw [Real.rpow_sub_one (ne_of_gt E.tauStar_pos)]
    field_simp

/-- **Exact left-object bridge.**  The displayed below-threshold derivative is
    the left derivative of the paper's original piecewise `Vinf` carrier, not
    merely the derivative of an unconnected branch formula. -/
theorem hasDerivWithinAt_smoothStock_left (a b : ℝ) :
    HasDerivWithinAt
      (fun theta => E.Vinf theta (E.gSmooth b) (fun tau => tau ^ a))
      (E.smoothSlopeBelowAtThreshold a)
      (Set.Iic E.thetaStar) E.thetaStar := by
  refine (E.hasDerivAt_smooth_stock_below_at_threshold a).hasDerivWithinAt.congr
    ?_ ?_
  · intro theta htheta
    exact E.prop_smooth_collapse_below a b theta htheta
  · exact E.prop_smooth_collapse_below a b E.thetaStar le_rfl

/-- **Exact right-object bridge.**  The displayed above-threshold derivative
    is the right derivative of the same original piecewise `Vinf` carrier.
    At the threshold the two branch values agree, so the within-derivative is
    genuinely attached to the paper's single stock object. -/
theorem hasDerivWithinAt_smoothStock_right (a b : ℝ) :
    HasDerivWithinAt
      (fun theta => E.Vinf theta (E.gSmooth b) (fun tau => tau ^ a))
      (E.smoothSlopeAboveAtThreshold a b)
      (Set.Ici E.thetaStar) E.thetaStar := by
  refine (E.hasDerivAt_smooth_stock_above_at_threshold a b).hasDerivWithinAt.congr
    ?_ ?_
  · intro theta htheta
    have hle : E.thetaStar ≤ theta := by
      simpa only [Set.mem_Ici] using htheta
    rcases eq_or_lt_of_le hle with hEq | hthetaStar
    · subst theta
      rw [E.prop_smooth_collapse_below a b E.thetaStar le_rfl]
      simp [E.eBar_thetaStar, div_self (ne_of_gt E.tauStar_pos)]
    · exact E.prop_smooth_collapse_above a b theta hthetaStar
  · rw [E.prop_smooth_collapse_below a b E.thetaStar le_rfl]
    simp [E.eBar_thetaStar, div_self (ne_of_gt E.tauStar_pos)]

/-! ### Corollary~\ref{cor:quant-predictions}: numerical calibration.

  The paper's Corollary~\ref{cor:quant-predictions} reports numerical
  collapse thresholds (radiology `θ* = 0.20`, legal practice
  `θ* = 0.29`, software engineering `θ* = 0.40`) obtained by
  substituting the calibration parameters of
  Tables~\ref{tab:calibration-thresholds}--\ref{tab:calibration-pigouvian}
  into the already-closed closed form `θ* = 1 - τ*/T_j`.

  This is direct numerical substitution into an already-closed
  closed form: given the calibrated `τ*/T_j` ratios, the collapse
  thresholds follow by `rw` + `norm_num`.  Encoded below as a
  derived `theorem`. -/

/-- **Corollary~\ref{cor:quant-predictions} (numerical calibration).**
    Paper `\label{cor:quant-predictions}`: under the calibration
    `τ*/T_j` ratios of Table~\ref{tab:calibration-thresholds}
    (radiology `0.80`, legal practice `0.71`, software engineering
    `0.60`), the closed form `θ* = 1 - τ*/T_j` yields the collapse
    thresholds `θ*_rad = 0.20`, `θ*_law = 0.29`, `θ*_SE = 0.40`.

    Derived `theorem` (`notInput`): direct numerical substitution
    into the already-closed closed form `θ* = 1 - τ*/T_j`, closed by
    `rw` of the calibration hypotheses followed by `norm_num`. -/
theorem cor_quant_predictions_calibration
    (tauStarRad TjRad tauStarLaw TjLaw tauStarSE TjSE : ℝ)
    (h_rad : tauStarRad / TjRad = 0.80)
    (h_law : tauStarLaw / TjLaw = 0.71)
    (h_se : tauStarSE / TjSE = 0.60) :
    (1 - tauStarRad / TjRad = 0.20)
      ∧ (1 - tauStarLaw / TjLaw = 0.29)
      ∧ (1 - tauStarSE / TjSE = 0.40) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h_rad]; norm_num
  · rw [h_law]; norm_num
  · rw [h_se]; norm_num

end Economy

end VerificationAsymmetry
