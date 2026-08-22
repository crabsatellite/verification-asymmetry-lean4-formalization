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
    `T-c*`, matching the paper's clearance-time interpretation. -/
theorem last_straddling_retirement_time (theta0 theta1 : ℝ) :
    -E.cStar theta0 theta1 + E.T = E.T - E.cStar theta0 theta1 := by
  ring

end Economy

end VerificationAsymmetry
