/- Atomic current-paper roots for formal-contract schema 2. -/

import VerificationAsymmetry.CurrentPaperClaimBindings

namespace VerificationAsymmetry.Economy

open Filter Set
open scoped Topology

variable (E : Economy)

/-! ## Atomic model-definition fragments -/

theorem paper_definition3_large_capacity_atomic
    (theta : ℝ) (htheta : 0 < theta) :
    Tendsto (fun K => generationAtCapacity E.LG theta K) atTop atTop :=
  generationAtCapacity_tendsto_atTop htheta

theorem paper_definition4_lifecycle_atomic
    (P : E.PaperCohortPrimitives) (c t : ℝ) :
    0 < E.nu ∧ 0 < E.Tj ∧ E.Tj < E.T ∧
      (E.juniorAt c t ↔ c ≤ t ∧ t ≤ c + E.Tj) ∧
      (E.seniorAt c t ↔ c + E.Tj ≤ t ∧ t ≤ c + E.T) ∧
      (∀ time, P.theta time ∈ Icc (0 : ℝ) 1) :=
  ⟨E.nu_pos, E.Tj_pos, E.Tj_lt_T, Iff.rfl, Iff.rfl, P.htheta_range⟩

theorem paper_definition4_promotion_tacit_atomic
    (P : E.PaperCohortPrimitives) :
    (∀ tau, 0 ≤ tau → P.g tau ∈ Icc (0 : ℝ) 1) ∧
      Monotone P.g ∧ P.g 0 = 0 ∧ P.g E.tauStar = 1 ∧
      (∀ tau, 0 ≤ tau → 0 ≤ P.h tau) ∧ Monotone P.h ∧ P.h 0 = 0 :=
  ⟨P.hg_range, P.hg_monotone, P.hg_zero, P.hg_threshold,
    P.hh_nonneg, P.hh_monotone, P.hh_zero⟩

theorem paper_lemma7_hard_specialization_atomic (tau : ℝ) :
    E.gHard tau = if E.tauStar ≤ tau then 1 else 0 := rfl

theorem paper_lemma7_smooth_specialization_atomic
    {b tau : ℝ} (hb : 0 < b) (htau : 0 ≤ tau) :
    E.gSmooth b tau = min ((tau / E.tauStar) ^ b) 1 := by
  unfold gSmooth
  by_cases h : E.tauStar ≤ tau
  · rw [if_pos h]
    have hratio : 1 ≤ tau / E.tauStar :=
      (le_div_iff₀ E.tauStar_pos).2 (by simpa using h)
    have hpow : (1 : ℝ) ≤ (tau / E.tauStar) ^ b := by
      simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hratio hb.le
    rw [min_eq_right hpow]
  · rw [if_neg h]
    have hratio_nonneg : 0 ≤ tau / E.tauStar :=
      div_nonneg htau E.tauStar_pos.le
    have hratio : tau / E.tauStar ≤ 1 :=
      (div_le_one E.tauStar_pos).2 (le_of_not_ge h)
    have hpow : (tau / E.tauStar) ^ b ≤ (1 : ℝ) := by
      simpa using Real.rpow_le_rpow hratio_nonneg hratio hb.le
    rw [min_eq_left hpow]

/-! ## Theorem 9 -/

theorem paper_theorem9_context_atomic
    (F : ℝ → ℝ → ℝ) (V : ℝ) (wG wV : ℝ → ℝ)
    (P : E.CESPricePathOn F (fun _ => V) wG wV (Icc (0 : ℝ) 1)) :
    IsCES F E.eta E.rho E.lam ∧ E.rho < 1 ∧ E.rho ≠ 0 ∧
      0 < V ∧ 0 < E.KAI := by
  exact ⟨P.hCES, P.hrho_lt, P.hrho_ne,
    P.hV_pos 0 ⟨le_rfl, zero_le_one⟩, E.KAI_pos⟩

theorem paper_theorem9_wage_ratio_monotone_atomic
    (F : ℝ → ℝ → ℝ) (V : ℝ) (wG wV : ℝ → ℝ)
    (P : E.CESPricePathOn F (fun _ => V) wG wV (Icc (0 : ℝ) 1))
    (hKAI : E.LG ≤ E.KAI) {theta1 theta2 : ℝ}
    (h0 : 0 ≤ theta1) (h1 : theta2 ≤ 1) (h12 : theta1 ≤ theta2) :
    wV theta1 / wG theta1 ≤ wV theta2 / wG theta2 := by
  rw [CESPricePathOn.ratio_eq E P ⟨h0, h12.trans h1⟩,
    CESPricePathOn.ratio_eq E P ⟨h0.trans h12, h1⟩]
  exact E.thm_inversion_wage_ratio_monotone V
    (P.hV_pos 0 ⟨le_rfl, zero_le_one⟩) hKAI P.hrho_lt h0 h1 h12

theorem paper_theorem9_wage_ratio_strict_atomic
    (F : ℝ → ℝ → ℝ) (V : ℝ) (wG wV : ℝ → ℝ)
    (P : E.CESPricePathOn F (fun _ => V) wG wV (Icc (0 : ℝ) 1))
    (hKAI : E.LG < E.KAI) {theta1 theta2 : ℝ}
    (h0 : 0 ≤ theta1) (h1 : theta2 ≤ 1) (h12 : theta1 < theta2) :
    wV theta1 / wG theta1 < wV theta2 / wG theta2 := by
  rw [CESPricePathOn.ratio_eq E P ⟨h0, h12.le.trans h1⟩,
    CESPricePathOn.ratio_eq E P ⟨h0.trans h12.le, h1⟩]
  exact E.thm_inversion_wage_ratio_strict V
    (P.hV_pos 0 ⟨le_rfl, zero_le_one⟩) hKAI P.hrho_lt h0 h1 h12

theorem paper_theorem9_wage_ratio_large_capacity_atomic
    (V theta : ℝ) (hV : 0 < V) (htheta : 0 < theta)
    (hrho : E.rho < 1) :
    Tendsto
      (fun K => wageRatioAtCapacity E.eta E.rho E.lam E.LG V theta K)
      atTop atTop :=
  wageRatioAtCapacity_tendsto_atTop E.eta_pos E.eta_lt_one E.lam_pos
    hV htheta hrho

theorem paper_theorem9_threshold_objects_atomic
    (wG wV : ℝ → ℝ) (V rBar : ℝ) :
    thetaInvMarginalProductInf wG wV rBar =
        sInf (marginalProductCrossingSet wG wV rBar) ∧
      E.Gstar V rBar =
        V * (rBar * E.eta / ((1 - E.eta) * E.lam ^ E.rho)) ^
          (1 / (1 - E.rho)) := by
  exact ⟨rfl, rfl⟩

theorem paper_theorem9_target_strict_atomic
    (F : ℝ → ℝ → ℝ) (V : ℝ) (wG wV : ℝ → ℝ)
    (P : E.CESPricePathOn F (fun _ => V) wG wV (Icc (0 : ℝ) 1))
    {rBar1 rBar2 : ℝ} (hr1 : 0 < rBar1) (hr12 : rBar1 < rBar2)
    (hlo : E.LG < E.Gstar V rBar1) (hhi : E.Gstar V rBar2 < E.KAI) :
    thetaInvMarginalProductInf wG wV rBar1 <
      thetaInvMarginalProductInf wG wV rBar2 := by
  have hV := P.hV_pos 0 ⟨le_rfl, zero_le_one⟩
  have hG12 := E.Gstar_strict_in_rBar V hV hr1 hr12 P.hrho_lt
  have hwage : ∀ theta ∈ Icc (0 : ℝ) 1,
      wV theta / wG theta = E.wageRatio V theta := fun theta htheta =>
    CESPricePathOn.ratio_eq E P htheta
  rw [E.thetaInvMarginalProductInf_eq_thetaInv V rBar1 wG wV hV hr1
      (hlo.trans (hG12.trans hhi)) P.hrho_lt hlo (hG12.trans hhi) hwage,
    E.thetaInvMarginalProductInf_eq_thetaInv V rBar2 wG wV hV
      (hr1.trans hr12) ((hlo.trans hG12).trans hhi) P.hrho_lt
      (hlo.trans hG12) hhi hwage]
  exact E.thm_inversion_threshold_strict_in_rBar V hV hr1 hr12
    (hlo.trans (hG12.trans hhi)) P.hrho_lt

theorem paper_theorem9_capacity_strict_atomic
    {Gcrit K1 K2 : ℝ} (hcrit : E.LG < Gcrit)
    (hK1 : Gcrit < K1) (hK12 : K1 < K2) :
    thetaInvAtCapacity E.LG Gcrit K2 < thetaInvAtCapacity E.LG Gcrit K1 :=
  thetaInvAtCapacity_strictAnti hcrit hK1 hK12

theorem paper_theorem9_eventual_actual_threshold_atomic
    (V rBar : ℝ) (hV : 0 < V) (hrBar : 0 < rBar)
    (hrho : E.rho < 1) (hbaseline : E.LG < E.Gstar V rBar) :
    ∀ᶠ K : ℝ in atTop,
      thetaInvRatioInfAtCapacity E.eta E.rho E.lam E.LG V rBar K =
          thetaInvAtCapacity E.LG (E.Gstar V rBar) K ∧
        thetaInvRatioInfAtCapacity E.eta E.rho E.lam E.LG V rBar K ∈
          Ioo (0 : ℝ) 1 :=
  E.thetaInvRatioInfAtCapacity_eventually_interior V rBar hV hrBar hrho
    hbaseline

theorem paper_theorem9_actual_threshold_limit_atomic
    (V rBar : ℝ) (hV : 0 < V) (hrBar : 0 < rBar)
    (hrho : E.rho < 1) (hbaseline : E.LG < E.Gstar V rBar) :
    Tendsto
      (fun K => thetaInvRatioInfAtCapacity E.eta E.rho E.lam E.LG V rBar K)
      atTop (nhdsWithin 0 (Ioi 0)) :=
  E.thetaInvRatioInfAtCapacity_tendsto_zero_right V rBar hV hrBar hrho
    hbaseline

theorem paper_theorem9_baseline_zero_atomic
    (wG wV : ℝ → ℝ) (rBar : ℝ) (hbaseline : rBar ≤ wV 0 / wG 0) :
    thetaInvMarginalProductInf wG wV rBar = 0 :=
  thetaInvMarginalProductInf_eq_zero_of_target_le_baseline wG wV rBar
    hbaseline

/-! ## Theorem 10 -/

theorem paper_theorem10_context_atomic {a : ℝ} (ha : 0 < a) :
    0 < a ∧
      (∀ tau, E.gHard tau = if E.tauStar ≤ tau then 1 else 0) ∧
      (fun tau : ℝ => tau ^ a) = (fun tau : ℝ => tau ^ a) := by
  exact ⟨ha, fun _ => rfl, rfl⟩

theorem paper_theorem10_step_context_atomic
    {theta0 theta1 : ℝ} (h0 : 0 ≤ theta0)
    (h0star : theta0 < E.thetaStar) (hstar1 : E.thetaStar < theta1)
    (h1 : theta1 ≤ 1) :
    theta0 ∈ Ico (0 : ℝ) E.thetaStar ∧ theta1 ∈ Ioc E.thetaStar 1 :=
  ⟨⟨h0, h0star⟩, hstar1, h1⟩

theorem paper_theorem10_stock_below_atomic
    {a theta : ℝ} (ha : 0 < a) (h0 : 0 ≤ theta)
    (htheta : theta < E.thetaStar) :
    E.VinfHard a theta = E.nu * E.Ts * ((1 - theta) * E.Tj) ^ a ∧
      HasDerivAt (fun x => E.VinfHard a x)
        (E.hardStockSlopeBelow a theta) theta ∧
      E.hardStockSlopeBelow a theta < 0 := by
  refine ⟨?_, E.hasDerivAt_VinfHard_below htheta,
    E.hardStockSlopeBelow_neg ha htheta⟩
  rw [E.thm_collapse_below_threshold a theta htheta.le]
  rfl

theorem paper_theorem10_jump_atomic (a : ℝ) :
    E.VinfHard a E.thetaStar = E.nu * E.Ts * E.tauStar ^ a ∧
      Tendsto (fun theta => E.VinfHard a theta)
        (nhdsWithin E.thetaStar (Iic E.thetaStar))
        (𝓝 (E.nu * E.Ts * E.tauStar ^ a)) ∧
      Tendsto (fun theta => E.VinfHard a theta)
        (nhdsWithin E.thetaStar (Ioi E.thetaStar)) (𝓝 0) :=
  ⟨E.thm_collapse_jump_magnitude a,
    E.VinfHard_tendsto_left_at_thetaStar a,
    E.VinfHard_tendsto_right_zero_at_thetaStar a⟩

theorem paper_theorem10_zero_above_atomic
    {a theta : ℝ} (htheta : E.thetaStar < theta) (htheta1 : theta ≤ 1) :
    E.VinfHard a theta = 0 := by
  exact E.thm_collapse_above_threshold a theta htheta

theorem paper_theorem10_step_cutoff_atomic
    {theta0 theta1 : ℝ} (h0 : 0 ≤ theta0)
    (h0star : theta0 < E.thetaStar) (hstar1 : E.thetaStar < theta1)
    (h1 : theta1 ≤ 1) :
    0 < E.cStar theta0 theta1 ∧ E.cStar theta0 theta1 < E.Tj :=
  E.cStar_mem_open_interval h0star hstar1

theorem paper_theorem10_step_experience_atomic
    (theta0 theta1 c : ℝ) :
    E.cumulativeExperience (stepSubstitutionPath theta0 theta1) c =
        E.stepExperience theta0 theta1 c ∧
      E.stepExperience theta0 theta1 c =
        if c ≤ -E.Tj then (1 - theta0) * E.Tj
        else if c ≤ 0 then
          (1 - theta0) * (-c) + (1 - theta1) * (c + E.Tj)
        else (1 - theta1) * E.Tj := by
  exact ⟨E.cumulativeExperience_step_eq_stepExperience theta0 theta1 c, rfl⟩

theorem paper_theorem10_step_promotion_atomic
    {theta0 theta1 c : ℝ} (h0 : theta0 < E.thetaStar)
    (h1 : E.thetaStar < theta1) :
    E.tauStar ≤ E.stepExperience theta0 theta1 c ↔
      c ≤ -E.cStar theta0 theta1 :=
  E.stepExperience_ge_tauStar_iff h0 h1

theorem paper_theorem10_step_stock_atomic
    {a theta0 theta1 t : ℝ} (h0 : 0 ≤ theta0)
    (h0star : theta0 < E.thetaStar) (hstar1 : E.thetaStar < theta1)
    (h1 : theta1 ≤ 1) (ht : 0 ≤ t) :
    E.timeIndexedStock (stepSubstitutionPath theta0 theta1) E.gHard
      (fun tau => tau ^ a) t =
      E.nu * (∫ cohort in t - E.T..t - E.Tj,
        if cohort ≤ -E.cStar theta0 theta1 then
          (E.stepExperience theta0 theta1 cohort) ^ a else 0) := by
  calc
    _ = E.exactStepStock theta0 theta1 (fun tau => tau ^ a) t :=
      E.timeIndexedStock_step_eq_exactStepStock (fun tau => tau ^ a) t
        h0star hstar1
    _ = _ := E.exactStepStock_eq_cohort_integral theta0 theta1
      (fun tau => tau ^ a) t

theorem paper_theorem10_step_clear_atomic
    {a theta0 theta1 t : ℝ} (ht : E.T - E.cStar theta0 theta1 ≤ t) :
    E.exactStepStock theta0 theta1 (fun tau => tau ^ a) t = 0 :=
  E.exactStepStock_zero_after_last_straddle theta0 theta1
    (fun tau => tau ^ a) ht

/-! ## Proposition 11 -/

theorem paper_proposition11_context_atomic
    {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) :
    0 < a ∧ a ≤ 1 ∧ 0 < b ∧
      ∀ tau : ℝ, 0 ≤ tau → tau ≤ E.tauStar →
        E.gSmooth b tau = (tau / E.tauStar) ^ b := by
  refine ⟨ha, ha1, hb, ?_⟩
  intro tau htau htauStar
  unfold gSmooth
  by_cases h : E.tauStar ≤ tau
  · have heq : tau = E.tauStar := le_antisymm htauStar h
    subst tau
    simp [E.tauStar_pos.ne']
  · simp [h]

theorem paper_proposition11_continuity_atomic (a b : ℝ) :
    ContinuousAt
      (fun theta => E.Vinf theta (E.gSmooth b) (fun tau => tau ^ a))
      E.thetaStar :=
  E.continuousAt_smoothStock_threshold a b

theorem paper_proposition11_endpoint_atomic
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a < a + b ∧
      Tendsto (fun theta => E.Vinf theta (E.gSmooth b) (fun tau => tau ^ a))
        (nhdsWithin 1 (Iio 1)) (𝓝 0) :=
  ⟨by linarith, E.smoothStock_tendsto_zero (by linarith)⟩

theorem paper_proposition11_kink_atomic
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |E.smoothSlopeBelowAtThreshold a| <
      |E.smoothSlopeAboveAtThreshold a b| :=
  E.prop_smooth_collapse_kink ha hb

theorem paper_proposition11_continuity_kink_atomic
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContinuousAt
        (fun theta => E.Vinf theta (E.gSmooth b) (fun tau => tau ^ a))
        E.thetaStar ∧
      |E.smoothSlopeBelowAtThreshold a| <
        |E.smoothSlopeAboveAtThreshold a b| :=
  ⟨E.continuousAt_smoothStock_threshold a b,
    E.prop_smooth_collapse_kink ha hb⟩

/-! ## Theorem 13 -/

structure PaperExternalityIncidenceContext
    (F : ℝ → ℝ → ℝ) (g h : ℝ → ℝ) (theta V r wG wV : ℝ)
    (stationaryThetaAndPrices employerCapturesJuniorGeneration
      employerCapturesNoLaterVerificationRent entrantIsPriceTaking : Prop) : Prop where
  theta_range : theta ∈ Icc (0 : ℝ) 1
  steady_stock : V = E.Vinf theta g h
  discount_pos : 0 < r
  generation_price : HasDerivAt (fun x => F x V) wG (E.G theta)
  verification_price : HasDerivAt (fun y => F (E.G theta) y) wV V
  h_stationary : stationaryThetaAndPrices
  h_capture_generation : employerCapturesJuniorGeneration
  h_no_capture_verification : employerCapturesNoLaterVerificationRent
  h_price_taking : entrantIsPriceTaking

theorem paper_theorem13_context_atomic
    (F : ℝ → ℝ → ℝ) (g h : ℝ → ℝ) (theta V r wG wV : ℝ)
    {stationaryThetaAndPrices employerCapturesJuniorGeneration
      employerCapturesNoLaterVerificationRent entrantIsPriceTaking : Prop}
    (P : E.PaperExternalityIncidenceContext F g h theta V r wG wV
      stationaryThetaAndPrices employerCapturesJuniorGeneration
      employerCapturesNoLaterVerificationRent entrantIsPriceTaking) :
    theta ∈ Icc (0 : ℝ) 1 ∧ V = E.Vinf theta g h ∧ 0 < r ∧
      HasDerivAt (fun x => F x V) wG (E.G theta) ∧
      HasDerivAt (fun y => F (E.G theta) y) wV V ∧
      stationaryThetaAndPrices ∧ employerCapturesJuniorGeneration ∧
      employerCapturesNoLaterVerificationRent ∧ entrantIsPriceTaking :=
  ⟨P.theta_range, P.steady_stock, P.discount_pos, P.generation_price,
    P.verification_price, P.h_stationary, P.h_capture_generation,
    P.h_no_capture_verification, P.h_price_taking⟩

theorem paper_theorem13_discount_horizons_atomic {r : ℝ} (hr : 0 < r) :
    (∫ s in (0 : ℝ)..E.Tj, Real.exp (-r * s)) = E.LambdaJ r ∧
      (∫ s in E.Tj..E.T, Real.exp (-r * s)) = E.Lambda r :=
  ⟨E.intervalIntegral_exp_neg_eq_LambdaJ hr,
    E.intervalIntegral_exp_neg_eq_Lambda hr⟩

theorem paper_theorem13_private_value_atomic
    (wG LambdaJ theta : ℝ) :
    MPpriv wG LambdaJ theta = (1 - theta) * wG * LambdaJ := rfl

theorem paper_theorem13_hard_monotone_atomic
    (F : ℝ → ℝ → ℝ) (wG wV : ℝ → ℝ) (r a : ℝ)
    (P : E.CESPricePathOn F (fun x => E.VinfHard a x) wG wV
      (Ico (0 : ℝ) E.thetaStar))
    (hr : 0 < r) (ha : 0 < a) (ha1 : a ≤ 1)
    (hKAI : E.LG ≤ E.KAI) {theta1 theta2 : ℝ}
    (h1 : theta1 ∈ Ico (0 : ℝ) E.thetaStar)
    (h2 : theta2 ∈ Ico (0 : ℝ) E.thetaStar) (h12 : theta1 ≤ theta2) :
    wedge (wG theta1) (wV theta1) (E.gHard (E.eBar theta1))
        (E.eBar theta1 ^ a) (E.LambdaJ r) (E.Lambda r) theta1 ≤
      wedge (wG theta2) (wV theta2) (E.gHard (E.eBar theta2))
        (E.eBar theta2 ^ a) (E.LambdaJ r) (E.Lambda r) theta2 := by
  rw [E.paper_equation14_explicit_wedge_exact F wG wV r a theta1 P hr
      ha ha1 h1,
    E.paper_equation14_explicit_wedge_exact F wG wV r a theta2 P hr
      ha ha1 h2]
  exact E.wedgeExplicit_monotone hr ha ha1 P.hrho_lt hKAI h1.1 h12 h2.2

theorem paper_theorem13_smooth_trichotomy_atomic
    (F : ℝ → ℝ → ℝ) (wG wV : ℝ → ℝ) (r a b : ℝ)
    (P : E.CESPricePathOn F
      (fun theta => E.Vinf theta (E.gSmooth b) (fun tau => tau ^ a))
      wG wV (Ioo E.thetaStar 1)) (hr : 0 < r) :
    (E.smoothWedgeExponent a b < 0 →
      Tendsto (fun theta => E.smoothMarginalProductWedge wG wV r a b theta)
        (nhdsWithin 1 (Iio 1)) atTop) ∧
    (E.smoothWedgeExponent a b = 0 →
      Tendsto (fun theta => E.smoothMarginalProductWedge wG wV r a b theta)
        (nhdsWithin 1 (Iio 1))
        (𝓝 (E.smoothWedgeEndpointCoefficient r a b))) ∧
    (0 < E.smoothWedgeExponent a b →
      Tendsto (fun theta => E.smoothMarginalProductWedge wG wV r a b theta)
        (nhdsWithin 1 (Iio 1)) (𝓝 0)) := by
  have hwage : ∀ theta ∈ Ioo E.thetaStar 1,
      wV theta / wG theta = E.wageRatio
        (E.Vinf theta (E.gSmooth b) (fun tau => tau ^ a)) theta :=
    fun theta htheta => CESPricePathOn.ratio_eq E P htheta
  exact ⟨E.smoothMarginalProductWedge_tendsto_atTop hr P.hwG_pos hwage,
    E.smoothMarginalProductWedge_tendsto_endpoint hr P.hwG_pos hwage,
    E.smoothMarginalProductWedge_tendsto_zero hr P.hwG_pos hwage⟩

theorem paper_theorem13_hard_boundary_atomic
    (wV h : ℝ) (r theta : ℝ) (htheta : E.thetaStar < theta)
    (htheta1 : theta ≤ 1) :
    E.gHard (E.eBar E.thetaStar) = 1 ∧
      externalityResidual wV (E.gHard (E.eBar theta)) h (E.Lambda r) = 0 := by
  exact ⟨E.gHard_of_ge (by simp),
    E.hardPromotion_externalityResidual_zero_above wV h (E.Lambda r)
      theta htheta⟩

theorem paper_theorem13_partial_capture_atomic
    (zeta wG wV gE hE LambdaJ Lambda theta : ℝ) :
    internalizedWedge zeta wG wV gE hE LambdaJ Lambda theta =
      (1 - zeta) *
        (externalityResidual wV gE hE Lambda /
          MPpriv wG LambdaJ theta) :=
  prop_internalization zeta wG wV gE hE LambdaJ Lambda theta

theorem paper_theorem13_residual_transfer_atomic
    (wG wV gE hE LambdaJ Lambda theta : ℝ) :
    MPsoc wG wV gE hE LambdaJ Lambda theta -
        MPpriv wG LambdaJ theta =
      externalityResidual wV gE hE Lambda := by
  exact thm_externality_residual_identity wG wV gE hE LambdaJ Lambda theta

theorem paper_theorem13_cobb_douglas_transfer_atomic
    (F : ℝ → ℝ → ℝ) (g h : ℝ → ℝ)
    (theta G Y wV r : ℝ) (htheta : theta ∈ Icc (0 : ℝ) 1)
    (hCD : IsCobbDouglas F E.eta E.lam)
    (h_wV : HasDerivAt (fun y => F G y) wV (E.Vinf theta g h))
    (hY : Y = F G (E.Vinf theta g h))
    (hG : 0 < G) (hV : 0 < E.Vinf theta g h) :
    externalityResidual wV (g (E.eBar theta)) (h (E.eBar theta))
        (E.Lambda r) =
      (1 - E.eta) * Y * E.Lambda r / (E.nu * E.Ts) := by
  simpa [pigouvianSubsidy_CD] using
    E.thm_externality_pigouvian_cobb_douglas_from_axioms F E.eta E.lam
      G Y wV (E.Lambda r) g h theta hCD h_wV hY hG hV E.eta_pos
      E.eta_lt_one E.lam_pos rfl

theorem paper_theorem13_zero_boundary_atomic
    (a wV h r theta : ℝ) (htheta : E.thetaStar < theta)
    (htheta1 : theta ≤ 1) :
    E.VinfHard a theta = 0 ∧
      externalityResidual wV (E.gHard (E.eBar theta)) h (E.Lambda r) = 0 :=
  ⟨E.thm_collapse_above_threshold a theta htheta,
    E.hardPromotion_externalityResidual_zero_above wV h (E.Lambda r)
      theta htheta⟩

/-! ## Proposition 14 -/

theorem paper_proposition14_context_atomic
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (Y w : ι → ℝ)
    (hY : ∀ i ∈ s, 0 ≤ Y i) (hw : ∀ i ∈ s, 0 < w i)
    (hsum : ∑ i ∈ s, w i = 1)
    (hzero : ∃ i ∈ s, Y i = 0) (hpositive : ∃ i ∈ s, 0 < Y i) :
    (∀ i ∈ s, 0 ≤ Y i) ∧ (∀ i ∈ s, 0 < w i) ∧
      (∑ i ∈ s, w i = 1) ∧ (∃ i ∈ s, Y i = 0) ∧
      (∃ i ∈ s, 0 < Y i) :=
  ⟨hY, hw, hsum, hzero, hpositive⟩

theorem paper_proposition14_cobb_douglas_zero_atomic
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (Y w : ι → ℝ)
    (hzero : ∃ i ∈ s, Y i = 0) (hw : ∀ i ∈ s, 0 < w i) :
    (∏ i ∈ s, Y i ^ w i) = 0 := by
  obtain ⟨i, hi, hYi⟩ := hzero
  exact thm_aggregation_cobb_douglas_zero s Y w i hi hYi (hw i hi)

theorem paper_proposition14_fixed_sigma_atomic
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (Y w : ι → ℝ)
    {sigma : ℝ} (hsigma : 1 < sigma)
    (hY : ∀ i ∈ s, 0 ≤ Y i) (hw : ∀ i ∈ s, 0 < w i)
    (hpositive : ∃ i ∈ s, 0 < Y i) :
    0 < aggregateCES s Y w sigma := by
  apply prop_aggregation_fixed_sigma_positive s Y w hsigma hY
    (fun i hi => (hw i hi).le)
  obtain ⟨i, hi, hYi⟩ := hpositive
  exact ⟨i, hi, hYi, hw i hi⟩

theorem paper_proposition14_limit_atomic
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (Y w : ι → ℝ)
    (hY : ∀ i ∈ s, 0 ≤ Y i) (hw : ∀ i ∈ s, 0 < w i)
    (hsum : ∑ i ∈ s, w i = 1)
    (hzero : ∃ i ∈ s, Y i = 0) (hpositive : ∃ i ∈ s, 0 < Y i) :
    Tendsto (aggregateCES s Y w) (nhdsWithin 1 (Ioi 1)) (𝓝 0) :=
  prop_aggregation_near_cobb_douglas_limit s Y w hY hw hsum hzero hpositive

end VerificationAsymmetry.Economy
