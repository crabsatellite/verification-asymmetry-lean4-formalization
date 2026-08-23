/-
  VerificationAsymmetry/CohortPath.lean

  Paper-faithful path-dependent cohort layer for Definition 4 and
  Theorem 10 Part 4 of the current journal manuscript.

  This module closes the mathematics that the earlier companion left partial:
    * cumulative experience as an interval integral;
    * the three-branch completed-experience function after a permanent step;
    * the straddling-cohort cutoff c* and its range;
    * promotion iff c <= -c*;
    * the exact cohort-integral stock;
    * zero full stock after the last promoted straddling cohort retires.
-/

import VerificationAsymmetry.Collapse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace VerificationAsymmetry

namespace Economy

open MeasureTheory

variable (E : Economy)

/-- Paper Eq. (3): cumulative junior generation experience along an arbitrary
    substitution path. -/
noncomputable def cumulativeExperience (theta : ℝ → ℝ) (c : ℝ) : ℝ :=
  ∫ s in c..c + E.Tj, (1 - theta s)

/-- Under a constant path, the cohort integral is `(1-theta) T_j`. -/
theorem cumulativeExperience_const (theta c : ℝ) :
    E.cumulativeExperience (fun _ => theta) c = (1 - theta) * E.Tj := by
  simp [cumulativeExperience]
  ring

/-! ### Assumption 6 and Definition 8: general time-indexed stock. -/

/-- Paper Assumption 6: verification is supplied only by active senior cohorts,
    with no direct AI contribution to the stock integral.  The cohort birth
    interval `[t-T,t-T_j]` is the exact paper carrier. -/
noncomputable def timeIndexedStock
    (theta : ℝ → ℝ) (g h : ℝ → ℝ) (t : ℝ) : ℝ :=
  E.nu * ∫ c in t - E.T..t - E.Tj,
    g (E.cumulativeExperience theta c) * h (E.cumulativeExperience theta c)

/-- Named unfolding theorem for the exact Assumption 6 integral. -/
theorem timeIndexedStock_eq_cohort_integral
    (theta : ℝ → ℝ) (g h : ℝ → ℝ) (t : ℝ) :
    E.timeIndexedStock theta g h t =
      E.nu * ∫ c in t - E.T..t - E.Tj,
        g (E.cumulativeExperience theta c) *
          h (E.cumulativeExperience theta c) := rfl

/-- Lemma 7 is the constant-path specialization of the exact Assumption 6
    cohort integral. -/
theorem timeIndexedStock_const_eq_Vinf
    (theta : ℝ) (g h : ℝ → ℝ) (t : ℝ) :
    E.timeIndexedStock (fun _ => theta) g h t = E.Vinf theta g h := by
  unfold timeIndexedStock Vinf
  simp [E.cumulativeExperience_const, Ts, eBar]
  ring

/-- Paper Definition 8 as one explicit predicate.  V1 is the exact
    no-direct-AI stock equation, V2 is the tacit-accumulation predicate, and V3
    is the exact experience-displacement integral. -/
structure VerificationAsymmetryDiagnostic
    (theta : ℝ → ℝ) (g h : ℝ → ℝ) : Prop where
  v1_verification_non_substitutability :
    ∀ t, E.timeIndexedStock theta g h t =
      E.nu * ∫ c in t - E.T..t - E.Tj,
        g (E.cumulativeExperience theta c) *
          h (E.cumulativeExperience theta c)
  v2_tacit_accumulation : V2_TacitAccumulation h
  v3_generation_displacement :
    ∀ c, E.cumulativeExperience theta c =
      ∫ s in c..c + E.Tj, (1 - theta s)

/-- V1 and V3 are earned from the exact carriers; V2 remains the explicit
    empirical/model premise. -/
theorem verificationAsymmetryDiagnostic_of_V2
    (theta : ℝ → ℝ) (g h : ℝ → ℝ) (hV2 : V2_TacitAccumulation h) :
    E.VerificationAsymmetryDiagnostic theta g h := by
  exact {
    v1_verification_non_substitutability := fun t =>
      E.timeIndexedStock_eq_cohort_integral theta g h t
    v2_tacit_accumulation := hV2
    v3_generation_displacement := fun _ => rfl
  }

/-- Permanent substitution step used in Theorem 10 Part 4. -/
noncomputable def stepSubstitutionPath (theta0 theta1 t : ℝ) : ℝ :=
  if t ≤ 0 then theta0 else theta1

/-- Paper Theorem 10 Part 4: the straddling-cohort distance from time zero. -/
noncomputable def cStar (theta0 theta1 : ℝ) : ℝ :=
  E.Tj * (theta1 - E.thetaStar) / (theta1 - theta0)

/-- The displayed `c*` lies strictly inside the junior interval. -/
theorem cStar_mem_open_interval
    {theta0 theta1 : ℝ}
    (h0 : theta0 < E.thetaStar) (h1 : E.thetaStar < theta1) :
    0 < E.cStar theta0 theta1 ∧ E.cStar theta0 theta1 < E.Tj := by
  have hden : 0 < theta1 - theta0 := by linarith
  have hnum : 0 < theta1 - E.thetaStar := by linarith
  unfold cStar
  constructor
  · exact div_pos (mul_pos E.Tj_pos hnum) hden
  · apply (div_lt_iff₀ hden).2
    have hnum_lt : theta1 - E.thetaStar < theta1 - theta0 := by linarith
    exact mul_lt_mul_of_pos_left hnum_lt E.Tj_pos

/-- Completed junior experience after a permanent step at time zero.  This is
    the paper's displayed three-branch function `e_01(c)`. -/
noncomputable def stepExperience (theta0 theta1 c : ℝ) : ℝ :=
  if c ≤ -E.Tj then
    (1 - theta0) * E.Tj
  else if c ≤ 0 then
    (1 - theta0) * (-c) + (1 - theta1) * (c + E.Tj)
  else
    (1 - theta1) * E.Tj

/-- The displayed three-branch `e_01(c)` is exactly the arbitrary-path cohort
    integral specialized to a permanent step; it is not a surrogate path. -/
theorem cumulativeExperience_step_eq_stepExperience
    (theta0 theta1 c : ℝ) :
    E.cumulativeExperience (stepSubstitutionPath theta0 theta1) c =
      E.stepExperience theta0 theta1 c := by
  unfold cumulativeExperience
  by_cases hpre : c ≤ -E.Tj
  · simp only [stepExperience, if_pos hpre]
    have hend : c + E.Tj ≤ 0 := by linarith
    calc
      (∫ s in c..c + E.Tj,
          (1 - stepSubstitutionPath theta0 theta1 s)) =
          ∫ _ in c..c + E.Tj, (1 - theta0) := by
            apply intervalIntegral.integral_congr
            intro s hs
            rw [Set.uIcc_of_le (by linarith [E.Tj_pos])] at hs
            simp [stepSubstitutionPath, show s ≤ 0 by linarith [hs.2]]
      _ = (1 - theta0) * E.Tj := by simp; ring
  · by_cases hzero : c ≤ 0
    · simp only [stepExperience, if_neg hpre, if_pos hzero]
      have hstart : 0 < c + E.Tj := by linarith
      let f : ℝ → ℝ := fun s => 1 - stepSubstitutionPath theta0 theta1 s
      have hleft_int : IntervalIntegrable f volume c 0 := by
        apply (intervalIntegrable_const :
          IntervalIntegrable (fun _ : ℝ => 1 - theta0) volume c 0).congr_ae
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
        simp only [Set.uIoc_of_le hzero] at hs
        simp [f, stepSubstitutionPath, show s ≤ 0 by linarith [hs.2]]
      have hright_int : IntervalIntegrable f volume 0 (c + E.Tj) := by
        apply (intervalIntegrable_const :
          IntervalIntegrable (fun _ : ℝ => 1 - theta1) volume 0 (c + E.Tj)).congr_ae
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
        simp only [Set.uIoc_of_le hstart.le] at hs
        simp [f, stepSubstitutionPath, show ¬ s ≤ 0 by linarith [hs.1]]
      have hleft : (∫ s in c..0, f s) = ∫ _ in c..0, (1 - theta0) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [Set.uIcc_of_le hzero] at hs
        simp [f, stepSubstitutionPath, show s ≤ 0 by linarith [hs.2]]
      have hright : (∫ s in 0..c + E.Tj, f s) =
          ∫ _ in 0..c + E.Tj, (1 - theta1) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with s
        intro hs
        rw [Set.uIoc_of_le hstart.le] at hs
        simp [f, stepSubstitutionPath, show ¬ s ≤ 0 by linarith [hs.1]]
      change (∫ s in c..c + E.Tj, f s) = _
      rw [← intervalIntegral.integral_add_adjacent_intervals hleft_int hright_int,
        hleft, hright]
      simp
      ring
    · have hc_pos : 0 < c := lt_of_not_ge hzero
      simp only [stepExperience, if_neg hpre, if_neg hzero]
      calc
        (∫ s in c..c + E.Tj,
            (1 - stepSubstitutionPath theta0 theta1 s)) =
            ∫ _ in c..c + E.Tj, (1 - theta1) := by
              apply intervalIntegral.integral_congr
              intro s hs
              rw [Set.uIcc_of_le (by linarith [E.Tj_pos])] at hs
              simp [stepSubstitutionPath, show ¬ s ≤ 0 by linarith [hs.1]]
        _ = (1 - theta1) * E.Tj := by simp; ring

@[simp] theorem stepExperience_pre
    (theta0 theta1 c : ℝ) (hc : c ≤ -E.Tj) :
    E.stepExperience theta0 theta1 c = (1 - theta0) * E.Tj := by
  simp [stepExperience, hc]

@[simp] theorem stepExperience_straddle
    (theta0 theta1 c : ℝ) (hpre : ¬ c ≤ -E.Tj) (hc : c ≤ 0) :
    E.stepExperience theta0 theta1 c =
      (1 - theta0) * (-c) + (1 - theta1) * (c + E.Tj) := by
  simp [stepExperience, hpre, hc]

@[simp] theorem stepExperience_post
    (theta0 theta1 c : ℝ) (hc : 0 < c) :
    E.stepExperience theta0 theta1 c = (1 - theta1) * E.Tj := by
  have hpre : ¬ c ≤ -E.Tj := by linarith [E.Tj_pos]
  have hzero : ¬ c ≤ 0 := not_le.mpr hc
  simp [stepExperience, hpre, hzero]

/-- Threshold identity used in the straddling-cohort algebra. -/
lemma tauStar_eq_one_sub_thetaStar_mul_Tj :
    E.tauStar = (1 - E.thetaStar) * E.Tj := by
  unfold thetaStar
  have hTj_ne : E.Tj ≠ 0 := ne_of_gt E.Tj_pos
  field_simp
  ring

/-- Paper Theorem 10 Part 4: a cohort promotes exactly when its birth date is
    at or before the cutoff `-c*`. -/
theorem stepExperience_ge_tauStar_iff
    {theta0 theta1 c : ℝ}
    (h0 : theta0 < E.thetaStar) (h1 : E.thetaStar < theta1) :
    E.tauStar ≤ E.stepExperience theta0 theta1 c ↔
      c ≤ -E.cStar theta0 theta1 := by
  obtain ⟨hcStar_pos, hcStar_lt⟩ := E.cStar_mem_open_interval h0 h1
  have htheta0 : E.tauStar ≤ E.eBar theta0 :=
    (E.eBar_ge_tauStar_iff_theta_le_thetaStar theta0).2 h0.le
  have htheta1 : E.eBar theta1 < E.tauStar :=
    (E.eBar_lt_tauStar_iff_theta_gt_thetaStar theta1).2 h1
  by_cases hpre : c ≤ -E.Tj
  · rw [E.stepExperience_pre theta0 theta1 c hpre]
    have hc_cut : c ≤ -E.cStar theta0 theta1 := by linarith
    simp [eBar] at htheta0
    exact ⟨fun _ => hc_cut, fun _ => htheta0⟩
  · by_cases hzero : c ≤ 0
    · rw [E.stepExperience_straddle theta0 theta1 c hpre hzero]
      have hden : 0 < theta1 - theta0 := by linarith
      have htau := E.tauStar_eq_one_sub_thetaStar_mul_Tj
      have hcut :
          -E.cStar theta0 theta1 =
            (-E.Tj * (theta1 - E.thetaStar)) / (theta1 - theta0) := by
        unfold cStar
        ring
      rw [hcut]
      rw [le_div_iff₀ hden]
      constructor <;> intro h <;> nlinarith
    · have hc_pos : 0 < c := lt_of_not_ge hzero
      rw [E.stepExperience_post theta0 theta1 c hc_pos]
      have hleft_false : ¬ E.tauStar ≤ (1 - theta1) * E.Tj := by
        simp [eBar] at htheta1
        linarith
      have hright_false : ¬ c ≤ -E.cStar theta0 theta1 := by linarith
      exact iff_of_false hleft_false hright_false

/-- The hard-promotion indicator after the step equals one exactly for cohorts
    born at or before `-c*`. -/
theorem gHard_stepExperience_eq_one_iff
    {theta0 theta1 c : ℝ}
    (h0 : theta0 < E.thetaStar) (h1 : E.thetaStar < theta1) :
    E.gHard (E.stepExperience theta0 theta1 c) = 1 ↔
      c ≤ -E.cStar theta0 theta1 := by
  rw [← E.stepExperience_ge_tauStar_iff h0 h1]
  constructor
  · intro hg
    by_contra hlt
    have hlt' : E.stepExperience theta0 theta1 c < E.tauStar := lt_of_not_ge hlt
    rw [E.gHard_of_lt hlt'] at hg
    norm_num at hg
  · intro hge
    exact E.gHard_of_ge hge

/-- Paper Theorem 10 Part 4 exact verification-stock integral after the step. -/
noncomputable def exactStepStock
    (theta0 theta1 : ℝ) (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  E.nu * ∫ c in t - E.T..t - E.Tj,
    if c ≤ -E.cStar theta0 theta1 then
      h (E.stepExperience theta0 theta1 c)
    else 0

/-- The exact stock is the paper's displayed cohort integral.  This theorem is
    intentionally an unfolding theorem so that the notation has a named
    consumer in the paper theorem map. -/
theorem exactStepStock_eq_cohort_integral
    (theta0 theta1 : ℝ) (h : ℝ → ℝ) (t : ℝ) :
    E.exactStepStock theta0 theta1 h t =
      E.nu * ∫ c in t - E.T..t - E.Tj,
        if c ≤ -E.cStar theta0 theta1 then
          h (E.stepExperience theta0 theta1 c)
        else 0 := rfl

/-- The exact-step stock is the general Assumption 6 stock specialized to the
    paper's permanent substitution path and hard promotion rule. -/
theorem timeIndexedStock_step_eq_exactStepStock
    {theta0 theta1 : ℝ} (h : ℝ → ℝ) (t : ℝ)
    (h0 : theta0 < E.thetaStar) (h1 : E.thetaStar < theta1) :
    E.timeIndexedStock (stepSubstitutionPath theta0 theta1) E.gHard h t =
      E.exactStepStock theta0 theta1 h t := by
  unfold timeIndexedStock exactStepStock
  congr 1
  apply intervalIntegral.integral_congr
  intro c _hc
  change E.gHard (E.cumulativeExperience (stepSubstitutionPath theta0 theta1) c) *
      h (E.cumulativeExperience (stepSubstitutionPath theta0 theta1) c) =
    if c ≤ -E.cStar theta0 theta1 then h (E.stepExperience theta0 theta1 c) else 0
  rw [E.cumulativeExperience_step_eq_stepExperience theta0 theta1 c]
  by_cases hcut : c ≤ -E.cStar theta0 theta1
  · have hg : E.gHard (E.stepExperience theta0 theta1 c) = 1 :=
      (E.gHard_stepExperience_eq_one_iff h0 h1).2 hcut
    simp [hcut, hg]
  · have hnot : ¬ E.tauStar ≤ E.stepExperience theta0 theta1 c := by
      rw [E.stepExperience_ge_tauStar_iff h0 h1]
      exact hcut
    have hg : E.gHard (E.stepExperience theta0 theta1 c) = 0 :=
      E.gHard_of_lt (lt_of_not_ge hnot)
    simp [hcut, hg]

/-- Cohort-integral carrier for the component supplied by cohorts that had
    completed junior training before the permanent step. -/
noncomputable def preStepStockIntegral
    (theta0 : ℝ) (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  E.nu * ∫ c in t - E.T..t - E.Tj,
    if c ≤ -E.Tj then h ((1 - theta0) * E.Tj) else 0

/-- On `0 ≤ t ≤ T_s`, the pre-trained component has exactly the interval
    length `T_s-t`; this earns the paper's linear component formula from the
    cohort integral. -/
theorem preStepStockIntegral_eq_linear
    (theta0 : ℝ) (h : ℝ → ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (htTs : t ≤ E.Ts) :
    E.preStepStockIntegral theta0 h t =
      E.nu * h ((1 - theta0) * E.Tj) * (E.Ts - t) := by
  let H : ℝ := h ((1 - theta0) * E.Tj)
  let f : ℝ → ℝ := fun c => if c ≤ -E.Tj then H else 0
  have ha : t - E.T ≤ -E.Tj := by
    unfold Ts at htTs
    linarith
  have hb : -E.Tj ≤ t - E.Tj := by linarith
  have hleft_int : IntervalIntegrable f volume (t - E.T) (-E.Tj) := by
    apply (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => H) volume (t - E.T) (-E.Tj)).congr
    intro c hc
    rw [Set.uIoc_of_le ha] at hc
    simp [f, show c ≤ -E.Tj by linarith [hc.2]]
  have hright_int : IntervalIntegrable f volume (-E.Tj) (t - E.Tj) := by
    apply (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (-E.Tj) (t - E.Tj)).congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with c hc
    rw [Set.uIoc_of_le hb] at hc
    simp [f, show ¬ c ≤ -E.Tj by linarith [hc.1]]
  have hleft : (∫ c in t - E.T..-E.Tj, f c) =
      ∫ _ in t - E.T..-E.Tj, H := by
    apply intervalIntegral.integral_congr
    intro c hc
    rw [Set.uIcc_of_le ha] at hc
    simp [f, show c ≤ -E.Tj by linarith [hc.2]]
  have hright : (∫ c in -E.Tj..t - E.Tj, f c) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards with c
    intro hc
    rw [Set.uIoc_of_le hb] at hc
    simp [f, show ¬ c ≤ -E.Tj by linarith [hc.1]]
  unfold preStepStockIntegral
  change E.nu * (∫ c in t - E.T..t - E.Tj, f c) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft_int hright_int,
    hleft, hright]
  simp [H, Ts]
  ring

/-- After `T_s`, no pre-trained senior remains in the active cohort window. -/
theorem preStepStockIntegral_zero_after_Ts
    (theta0 : ℝ) (h : ℝ → ℝ) {t : ℝ} (ht : E.Ts ≤ t) :
    E.preStepStockIntegral theta0 h t = 0 := by
  unfold preStepStockIntegral
  have horder : t - E.T ≤ t - E.Tj := by linarith [E.Tj_lt_T]
  have hstart : -E.Tj ≤ t - E.T := by
    unfold Ts at ht
    linarith
  have hintegral :
      (∫ c in t - E.T..t - E.Tj,
        if c ≤ -E.Tj then h ((1 - theta0) * E.Tj) else 0) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards with c
    intro hc
    rw [Set.uIoc_of_le horder] at hc
    have hc_gt : -E.Tj < c := by linarith [hc.1]
    simp [not_le.mpr hc_gt]
  rw [hintegral, mul_zero]

/-- The paper's `V_pre(t)=V_infinity(theta0)(1-t/T_s)_+` is exactly
    the pre-trained cohort integral for every `t≥0`. -/
theorem preStepStockIntegral_eq_transientStock
    (theta0 : ℝ) (h : ℝ → ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (htheta0 : theta0 < E.thetaStar) :
    E.preStepStockIntegral theta0 h t =
      E.transientStock (E.Vinf theta0 E.gHard h) t := by
  by_cases htTs : t ≤ E.Ts
  · rw [E.preStepStockIntegral_eq_linear theta0 h ht0 htTs,
      E.thm_collapse_transient_linear (E.Vinf theta0 E.gHard h) t ht0 htTs]
    have hge : E.tauStar ≤ E.eBar theta0 :=
      (E.eBar_ge_tauStar_iff_theta_le_thetaStar theta0).2 htheta0.le
    have hg : E.gHard (E.eBar theta0) = 1 := E.gHard_of_ge hge
    unfold Vinf
    rw [hg]
    unfold eBar
    have hTs_ne : E.Ts ≠ 0 := ne_of_gt E.Ts_pos
    field_simp
  · have ht : E.Ts ≤ t := le_of_not_ge htTs
    rw [E.preStepStockIntegral_zero_after_Ts theta0 h ht,
      E.thm_collapse_transient_zero_after_Ts (E.Vinf theta0 E.gHard h) t ht]

/-- Once `t >= T-c*`, every cohort in the active-senior integration window was
    born after the last promoting cohort (up to the measure-zero endpoint), so
    the complete stock is zero. -/
theorem exactStepStock_zero_after_last_straddle
    (theta0 theta1 : ℝ) (h : ℝ → ℝ) {t : ℝ}
    (ht : E.T - E.cStar theta0 theta1 ≤ t) :
    E.exactStepStock theta0 theta1 h t = 0 := by
  unfold exactStepStock
  have horder : t - E.T ≤ t - E.Tj := by linarith [E.Tj_lt_T]
  have hintegral :
      (∫ c in t - E.T..t - E.Tj,
        if c ≤ -E.cStar theta0 theta1 then
          h (E.stepExperience theta0 theta1 c)
        else 0) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards with c
    intro hc
    rw [Set.uIoc_of_le horder] at hc
    have hc_gt : -E.cStar theta0 theta1 < c := by linarith [hc.1]
    simp [not_le.mpr hc_gt]
  rw [hintegral, mul_zero]

/-- The last promoting straddling cohort is born at `-c*` and retires at
    `T-c*`; this identifies the cutoff used by the zero-stock theorem above. -/
theorem last_straddling_retirement_time (theta0 theta1 : ℝ) :
    -E.cStar theta0 theta1 + E.T = E.T - E.cStar theta0 theta1 := by
  ring

end Economy

end VerificationAsymmetry
