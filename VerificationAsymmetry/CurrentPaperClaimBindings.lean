/-
  Strict one-declaration-per-claim bindings for the current journal paper.

  Unlike TheoremMap.lean, this file does not merely #check that a nearby symbol
  exists.  Every declaration below has a paper-facing type.  The shared formal
  contract pins each full declaration signature and its exact project-axiom
  dependency set to one TeX fragment.
-/

import VerificationAsymmetry

namespace VerificationAsymmetry.Economy

open Filter Finset Set
open scoped Topology BigOperators Interval

variable (E : Economy)

/-! ## Model objects and Equations (1)--(6). -/

theorem paper_definition1_parameters_exact :
    0 < E.LG ∧ 0 < E.KAI ∧ 0 < E.lam ∧ 0 < E.nu ∧
      0 < E.Tj ∧ E.Tj < E.T ∧ 0 < E.tauStar ∧
      E.tauStar < E.Tj ∧ 0 < E.eta ∧ E.eta < 1 ∧ E.rho ≤ 1 :=
  ⟨E.LG_pos, E.KAI_pos, E.lam_pos, E.nu_pos, E.Tj_pos, E.Tj_lt_T,
    E.tauStar_pos, E.tauStar_lt_Tj, E.eta_pos, E.eta_lt_one, E.rho_le_one⟩

theorem paper_equation1_ces_exact
    (F : ℝ → ℝ → ℝ) (hCES : IsCES F E.eta E.rho E.lam)
    {G V : ℝ} (hG : 0 < G) (hV : 0 < V) :
    F G V =
      (E.eta * G ^ E.rho + (1 - E.eta) * (E.lam * V) ^ E.rho) ^
        (1 / E.rho) :=
  hCES G V hG hV

theorem paper_definition3_generation_supply_exact (theta : ℝ) :
    E.G theta = (1 - theta) * E.LG + theta * E.KAI := rfl

theorem paper_equation2_generation_supply_exact (theta : ℝ) :
    E.G theta = (1 - theta) * E.LG + theta * E.KAI := rfl

theorem paper_definition4_cohort_dynamics_exact
    (theta : ℝ → ℝ) (c : ℝ) :
    E.cumulativeExperience theta c =
      ∫ s in c..c + E.Tj, (1 - theta s) := rfl

theorem paper_equation3_cumulative_experience_exact
    (theta : ℝ → ℝ) (c : ℝ) :
    E.cumulativeExperience theta c =
      ∫ s in c..c + E.Tj, (1 - theta s) := rfl

theorem paper_assumption6_time_indexed_stock_exact
    (theta : ℝ → ℝ) (g h : ℝ → ℝ) (t : ℝ) :
    E.timeIndexedStock theta g h t =
      E.nu * ∫ c in t - E.T..t - E.Tj,
        g (E.cumulativeExperience theta c) *
          h (E.cumulativeExperience theta c) :=
  E.timeIndexedStock_eq_cohort_integral theta g h t

theorem paper_lemma7_steady_state_stock_exact
    (theta : ℝ) (g h : ℝ → ℝ) (t : ℝ) :
    E.timeIndexedStock (fun _ => theta) g h t =
      E.nu * E.Ts * g ((1 - theta) * E.Tj) * h ((1 - theta) * E.Tj) := by
  rw [E.timeIndexedStock_const_eq_Vinf]
  rfl

theorem paper_equation4_steady_state_stock_exact
    (theta : ℝ) (g h : ℝ → ℝ) :
    E.Vinf theta g h =
      E.nu * E.Ts * g ((1 - theta) * E.Tj) * h ((1 - theta) * E.Tj) := rfl

theorem paper_equation5_hard_stock_exact (a theta : ℝ) :
    E.VinfHard a theta =
      if theta ≤ E.thetaStar then
        E.nu * E.Ts * ((1 - theta) * E.Tj) ^ a
      else 0 := by
  by_cases htheta : theta ≤ E.thetaStar
  · rw [if_pos htheta, E.thm_collapse_below_threshold a theta htheta]
    rfl
  · have hthetaStar : E.thetaStar < theta := lt_of_not_ge htheta
    rw [if_neg htheta, E.thm_collapse_above_threshold a theta hthetaStar]

theorem paper_equation6_smooth_stock_exact (a b theta : ℝ) :
    E.Vinf theta (E.gSmooth b) (fun tau => tau ^ a) =
      if theta ≤ E.thetaStar then
        E.nu * E.Ts * ((1 - theta) * E.Tj) ^ a
      else
        E.nu * E.Ts * (((1 - theta) * E.Tj) / E.tauStar) ^ b *
          ((1 - theta) * E.Tj) ^ a := by
  by_cases htheta : theta ≤ E.thetaStar
  · rw [if_pos htheta, E.prop_smooth_collapse_below a b theta htheta]
    rfl
  · have hthetaStar : E.thetaStar < theta := lt_of_not_ge htheta
    rw [if_neg htheta, E.prop_smooth_collapse_above a b theta hthetaStar]
    rfl

theorem paper_definition8_diagnostic_exact
    (theta g h : ℝ → ℝ) :
    E.VerificationAsymmetryDiagnostic theta g h ↔ V2_TacitAccumulation h := by
  constructor
  · exact fun hdiag => hdiag.v2_tacit_accumulation
  · exact E.verificationAsymmetryDiagnostic_of_V2 theta g h

/-! ## CES price paths: the paper's marginal-product premises as a typed bundle. -/

structure CESPricePathOn
    (F : ℝ → ℝ → ℝ) (Vstock wG wV : ℝ → ℝ) (domain : Set ℝ) : Prop where
  hCES : IsCES F E.eta E.rho E.lam
  hrho_lt : E.rho < 1
  hrho_ne : E.rho ≠ 0
  hG_pos : ∀ theta ∈ domain, 0 < E.G theta
  hV_pos : ∀ theta ∈ domain, 0 < Vstock theta
  hwG_pos : ∀ theta ∈ domain, 0 < wG theta
  h_wG : ∀ theta ∈ domain,
    HasDerivAt (fun x => F x (Vstock theta)) (wG theta) (E.G theta)
  h_wV : ∀ theta ∈ domain,
    HasDerivAt (fun y => F (E.G theta) y) (wV theta) (Vstock theta)

theorem CESPricePathOn.ratio_eq
    {F : ℝ → ℝ → ℝ} {Vstock wG wV : ℝ → ℝ} {domain : Set ℝ}
    (P : E.CESPricePathOn F Vstock wG wV domain)
    {theta : ℝ} (htheta : theta ∈ domain) :
    wV theta / wG theta = E.wageRatio (Vstock theta) theta := by
  simpa [wageRatio] using
    E.wageRatio_eq_ces_marginal_product_ratio F (E.G theta) (Vstock theta)
      (wG theta) (wV theta) P.hCES (P.h_wG theta htheta)
      (P.h_wV theta htheta) (P.hwG_pos theta htheta)
      (P.hG_pos theta htheta) (P.hV_pos theta htheta)
      P.hrho_lt P.hrho_ne

/-! ## Theorem 9 and Equations (7)--(8). -/

theorem paper_equation7_wage_ratio_exact
    (F : ℝ → ℝ → ℝ) (V : ℝ) (wG wV : ℝ → ℝ)
    (P : E.CESPricePathOn F (fun _ => V) wG wV (Icc (0 : ℝ) 1))
    {theta : ℝ} (htheta : theta ∈ Icc (0 : ℝ) 1) :
    wV theta / wG theta =
      ((1 - E.eta) / E.eta) * E.lam ^ E.rho *
        (E.G theta / V) ^ (1 - E.rho) := by
  simpa [wageRatio] using CESPricePathOn.ratio_eq E P htheta

theorem paper_equation8_inversion_threshold_exact
    (F : ℝ → ℝ → ℝ) (V rBar : ℝ) (wG wV : ℝ → ℝ)
    (P : E.CESPricePathOn F (fun _ => V) wG wV (Icc (0 : ℝ) 1))
    (hrBar_pos : 0 < rBar) (hKAI_gt : E.LG < E.KAI)
    (hGstar_lo : E.LG < E.Gstar V rBar)
    (hGstar_hi : E.Gstar V rBar < E.KAI) :
    thetaInvMarginalProductInf wG wV rBar =
      (E.Gstar V rBar - E.LG) / (E.KAI - E.LG) := by
  have hwage : ∀ theta ∈ Icc (0 : ℝ) 1,
      wV theta / wG theta = E.wageRatio V theta := by
    intro theta htheta
    exact CESPricePathOn.ratio_eq E P htheta
  exact E.thetaInvMarginalProductInf_eq_thetaInv V rBar wG wV
    (P.hV_pos 0 ⟨le_rfl, zero_le_one⟩) hrBar_pos hKAI_gt P.hrho_lt
    hGstar_lo hGstar_hi hwage

theorem paper_theorem9_inversion_exact
    (F : ℝ → ℝ → ℝ) (V rBar : ℝ) (wG wV : ℝ → ℝ)
    (P : E.CESPricePathOn F (fun _ => V) wG wV (Icc (0 : ℝ) 1))
    (hrBar_pos : 0 < rBar) (hKAI_gt : E.LG < E.KAI)
    (hGstar_lo : E.LG < E.Gstar V rBar)
    (hGstar_hi : E.Gstar V rBar < E.KAI) :
    (∀ theta ∈ Icc (0 : ℝ) 1,
      wV theta / wG theta = E.wageRatio V theta) ∧
    (∀ ⦃theta1 theta2 : ℝ⦄, 0 ≤ theta1 → theta2 ≤ 1 → theta1 ≤ theta2 →
      wV theta1 / wG theta1 ≤ wV theta2 / wG theta2) ∧
    thetaInvMarginalProductInf wG wV rBar = E.thetaInv V rBar ∧
    (0 < E.thetaInv V rBar ∧ E.thetaInv V rBar < 1) ∧
    (∀ {rBar1 rBar2 : ℝ}, 0 < rBar1 → rBar1 < rBar2 →
      E.thetaInv V rBar1 < E.thetaInv V rBar2) ∧
    (∀ theta : ℝ, 0 < theta →
      Tendsto
        (fun K => wageRatioAtCapacity E.eta E.rho E.lam E.LG V theta K)
        atTop atTop) ∧
    Tendsto (fun K => thetaInvAtCapacity E.LG (E.Gstar V rBar) K)
      atTop (𝓝 0) := by
  have hwage : ∀ theta ∈ Icc (0 : ℝ) 1,
      wV theta / wG theta = E.wageRatio V theta := by
    intro theta htheta
    exact CESPricePathOn.ratio_eq E P htheta
  have hV_pos : 0 < V := P.hV_pos 0 ⟨le_rfl, zero_le_one⟩
  refine ⟨hwage, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro theta1 theta2 htheta1 htheta2 htheta12
    rw [hwage theta1 ⟨htheta1, le_trans htheta12 htheta2⟩,
      hwage theta2 ⟨le_trans htheta1 htheta12, htheta2⟩]
    exact E.thm_inversion_wage_ratio_monotone V hV_pos hKAI_gt.le
      P.hrho_lt htheta1 htheta2 htheta12
  · exact E.thetaInvMarginalProductInf_eq_thetaInv V rBar wG wV hV_pos
      hrBar_pos hKAI_gt P.hrho_lt hGstar_lo hGstar_hi hwage
  · exact E.thm_inversion_threshold_in_unit_interval V rBar hKAI_gt
      hGstar_lo hGstar_hi
  · intro rBar1 rBar2 hrBar1 hrBar12
    exact E.thm_inversion_threshold_strict_in_rBar V hV_pos hrBar1 hrBar12
      hKAI_gt P.hrho_lt
  · intro theta htheta
    exact wageRatioAtCapacity_tendsto_atTop E.eta_pos E.eta_lt_one
      E.lam_pos hV_pos htheta P.hrho_lt
  · exact thetaInvAtCapacity_tendsto_zero E.LG (E.Gstar V rBar)

/-! ## Theorem 10 and Equations (9)--(10). -/

theorem paper_equation9_collapse_threshold_exact :
    E.thetaStar = 1 - E.tauStar / E.Tj := rfl

theorem paper_equation10_transient_stock_exact
    (a theta0 t : ℝ) (ht0 : 0 ≤ t) (htheta0 : theta0 < E.thetaStar) :
    E.preStepStockIntegral theta0 (fun tau => tau ^ a) t =
      E.Vinf theta0 E.gHard (fun tau => tau ^ a) *
        max 0 (1 - t / E.Ts) := by
  rw [E.preStepStockIntegral_eq_transientStock theta0 (fun tau => tau ^ a)
    ht0 htheta0]
  rfl

theorem paper_theorem10_pipeline_collapse_exact
    {a thetaBelow thetaAbove theta0 theta1 c t tclear : ℝ}
    (ha : 0 < a) (_hthetaBelow0 : 0 ≤ thetaBelow)
    (hthetaBelow : thetaBelow < E.thetaStar)
    (hthetaAbove : E.thetaStar < thetaAbove)
    (hstep0 : theta0 < E.thetaStar) (hstep1 : E.thetaStar < theta1)
    (htclear : E.T - E.cStar theta0 theta1 ≤ tclear) :
    E.thetaStar = 1 - E.tauStar / E.Tj ∧
    E.VinfHard a thetaBelow =
      E.nu * E.Ts * ((1 - thetaBelow) * E.Tj) ^ a ∧
    HasDerivAt
      (fun theta => E.nu * E.Ts * E.eBar theta ^ a)
      (E.hardStockSlopeBelow a thetaBelow) thetaBelow ∧
    E.hardStockSlopeBelow a thetaBelow < 0 ∧
    E.VinfHard a E.thetaStar = E.nu * E.Ts * E.tauStar ^ a ∧
    Tendsto (fun theta => E.VinfHard a theta)
      (nhdsWithin E.thetaStar (Iic E.thetaStar))
      (𝓝 (E.nu * E.Ts * E.tauStar ^ a)) ∧
    Tendsto (fun theta => E.VinfHard a theta)
      (nhdsWithin E.thetaStar (Ioi E.thetaStar)) (𝓝 0) ∧
    E.VinfHard a thetaAbove = 0 ∧
    E.cumulativeExperience (stepSubstitutionPath theta0 theta1) c =
      E.stepExperience theta0 theta1 c ∧
    (E.tauStar ≤ E.stepExperience theta0 theta1 c ↔
      c ≤ -E.cStar theta0 theta1) ∧
    E.timeIndexedStock (stepSubstitutionPath theta0 theta1) E.gHard
      (fun tau => tau ^ a) t =
        E.exactStepStock theta0 theta1 (fun tau => tau ^ a) t ∧
    E.exactStepStock theta0 theta1 (fun tau => tau ^ a) tclear = 0 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [E.thm_collapse_below_threshold a thetaBelow hthetaBelow.le]
    rfl
  · exact E.hasDerivAt_hard_stock_below a thetaBelow hthetaBelow
  · exact E.hardStockSlopeBelow_neg ha hthetaBelow
  · exact E.thm_collapse_jump_magnitude a
  · exact E.VinfHard_tendsto_left_at_thetaStar a
  · exact E.VinfHard_tendsto_right_zero_at_thetaStar a
  · exact E.thm_collapse_above_threshold a thetaAbove hthetaAbove
  · exact E.cumulativeExperience_step_eq_stepExperience theta0 theta1 c
  · exact E.stepExperience_ge_tauStar_iff hstep0 hstep1
  · exact E.timeIndexedStock_step_eq_exactStepStock (fun tau => tau ^ a) t
      hstep0 hstep1
  · exact E.exactStepStock_zero_after_last_straddle theta0 theta1
      (fun tau => tau ^ a) htclear

/-! ## Proposition 11 and Equation (11). -/

theorem smoothStockAbove_eq_paperClosedForm
    {a b theta : ℝ} (hthetaStar : E.thetaStar < theta)
    (htheta1 : theta < 1) :
    E.Vinf theta (E.gSmooth b) (fun tau => tau ^ a) =
      E.nu * E.Ts * E.Tj ^ (a + b) * E.tauStar ^ (-b) *
        (1 - theta) ^ (a + b) := by
  have hx : 0 < 1 - theta := by linarith
  have he : 0 < E.eBar theta := by
    unfold eBar
    exact mul_pos hx E.Tj_pos
  rw [E.prop_smooth_collapse_above a b theta hthetaStar]
  rw [Real.div_rpow he.le E.tauStar_pos.le]
  rw [show
    E.nu * E.Ts * (E.eBar theta ^ b / E.tauStar ^ b) * E.eBar theta ^ a =
      E.nu * E.Ts * (E.eBar theta ^ b * E.eBar theta ^ a) /
        E.tauStar ^ b by field_simp]
  rw [← Real.rpow_add he]
  have hab : b + a = a + b := by ring
  rw [hab]
  unfold eBar
  rw [Real.mul_rpow hx.le E.Tj_pos.le]
  rw [Real.rpow_neg E.tauStar_pos.le]
  field_simp

theorem paper_equation11_smooth_stock_exact
    {a b theta : ℝ} (hthetaStar : E.thetaStar < theta)
    (htheta1 : theta < 1) :
    E.Vinf theta (E.gSmooth b) (fun tau => tau ^ a) =
      E.nu * E.Ts * E.Tj ^ (a + b) * E.tauStar ^ (-b) *
        (1 - theta) ^ (a + b) :=
  E.smoothStockAbove_eq_paperClosedForm hthetaStar htheta1

theorem paper_proposition11_smooth_collapse_exact
    {a b theta : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hthetaStar : E.thetaStar < theta) (htheta1 : theta < 1) :
    E.Vinf theta (E.gSmooth b) (fun tau => tau ^ a) =
      E.nu * E.Ts * E.Tj ^ (a + b) * E.tauStar ^ (-b) *
        (1 - theta) ^ (a + b) ∧
    HasDerivWithinAt
      (fun x => E.Vinf x (E.gSmooth b) (fun tau => tau ^ a))
      (E.smoothSlopeBelowAtThreshold a) (Iic E.thetaStar) E.thetaStar ∧
    HasDerivWithinAt
      (fun x => E.Vinf x (E.gSmooth b) (fun tau => tau ^ a))
      (E.smoothSlopeAboveAtThreshold a b) (Ici E.thetaStar) E.thetaStar ∧
    |E.smoothSlopeBelowAtThreshold a| <
      |E.smoothSlopeAboveAtThreshold a b| := by
  exact ⟨E.smoothStockAbove_eq_paperClosedForm hthetaStar htheta1,
    E.hasDerivWithinAt_smoothStock_left a b,
    E.hasDerivWithinAt_smoothStock_right a b,
    E.prop_smooth_collapse_kink ha hb⟩

/-! ## Theorem 13 and Equations (12)--(14). -/

theorem paper_equation12_social_present_value_exact
    (wG wV gE hE LambdaJ Lambda theta : ℝ) :
    MPsoc wG wV gE hE LambdaJ Lambda theta =
      MPpriv wG LambdaJ theta + wV * gE * hE * Lambda := rfl

theorem paper_equation13_apprenticeship_wedge_exact
    (wG wV gE hE LambdaJ Lambda theta : ℝ)
    (hwG : 0 < wG) (hLambdaJ : 0 < LambdaJ) (htheta1 : theta < 1) :
    wedge wG wV gE hE LambdaJ Lambda theta =
      (wV / wG) * (gE * hE * Lambda) / ((1 - theta) * LambdaJ) :=
  thm_externality_wedge_identity wG wV gE hE LambdaJ Lambda theta
    hwG hLambdaJ htheta1

theorem paper_equation14_explicit_wedge_exact
    (F : ℝ → ℝ → ℝ) (wG wV : ℝ → ℝ)
    (r a theta : ℝ)
    (P : E.CESPricePathOn F (fun x => E.VinfHard a x) wG wV
      (Ico (0 : ℝ) E.thetaStar))
    (hr : 0 < r) (htheta : theta ∈ Ico (0 : ℝ) E.thetaStar) :
    wedge (wG theta) (wV theta) (E.gHard (E.eBar theta))
        (E.eBar theta ^ a) (E.LambdaJ r) (E.Lambda r) theta =
      E.wedgeExplicit r a theta := by
  have hwage := CESPricePathOn.ratio_eq E P htheta
  exact E.wedge_eq_wedgeExplicit hr htheta.1 htheta.2
    (P.hwG_pos theta htheta) hwage

theorem paper_theorem13_externality_exact
    (Fces Fcd : ℝ → ℝ → ℝ)
    (wGHard wVHard wGSmooth wVSmooth : ℝ → ℝ)
    (r a b thetaHard thetaAbove wVBoundary hBoundary : ℝ)
    (Phard : E.CESPricePathOn Fces (fun x => E.VinfHard a x)
      wGHard wVHard (Ico (0 : ℝ) E.thetaStar))
    (Psmooth : E.CESPricePathOn Fces
      (fun x => E.Vinf x (E.gSmooth b) (fun tau => tau ^ a))
      wGSmooth wVSmooth (Ioo E.thetaStar 1))
    (hr : 0 < r) (hthetaHard : thetaHard ∈ Ico (0 : ℝ) E.thetaStar)
    (hthetaAbove : E.thetaStar < thetaAbove)
    (g h : ℝ → ℝ) (thetaCD G Y wVCD : ℝ)
    (hCD : IsCobbDouglas Fcd E.eta E.lam)
    (h_wVCD : HasDerivAt (fun y => Fcd G y) wVCD (E.Vinf thetaCD g h))
    (hY : Y = Fcd G (E.Vinf thetaCD g h))
    (hG_pos : 0 < G) (hVCD_pos : 0 < E.Vinf thetaCD g h) :
    (∫ s in (0 : ℝ)..E.Tj, Real.exp (-r * s)) = E.LambdaJ r ∧
    (∫ s in E.Tj..E.T, Real.exp (-r * s)) = E.Lambda r ∧
    wedge (wGHard thetaHard) (wVHard thetaHard)
        (E.gHard (E.eBar thetaHard)) (E.eBar thetaHard ^ a)
        (E.LambdaJ r) (E.Lambda r) thetaHard =
      E.wedgeExplicit r a thetaHard ∧
    ((E.smoothWedgeExponent a b < 0 →
        Tendsto
          (fun theta => E.smoothMarginalProductWedge
            wGSmooth wVSmooth r a b theta)
          (nhdsWithin 1 (Iio 1)) atTop) ∧
      (E.smoothWedgeExponent a b = 0 →
        Tendsto
          (fun theta => E.smoothMarginalProductWedge
            wGSmooth wVSmooth r a b theta)
          (nhdsWithin 1 (Iio 1))
          (𝓝 (E.smoothWedgeEndpointCoefficient r a b))) ∧
      (0 < E.smoothWedgeExponent a b →
        Tendsto
          (fun theta => E.smoothMarginalProductWedge
            wGSmooth wVSmooth r a b theta)
          (nhdsWithin 1 (Iio 1)) (𝓝 0))) ∧
    externalityResidual wVBoundary (E.gHard (E.eBar thetaAbove))
      hBoundary (E.Lambda r) = 0 ∧
    externalityResidual wVCD (g (E.eBar thetaCD)) (h (E.eBar thetaCD))
        (E.Lambda r) = E.pigouvianSubsidy_CD Y (E.Lambda r) := by
  have hwageHard := CESPricePathOn.ratio_eq E Phard hthetaHard
  have hwageSmooth : ∀ theta ∈ Ioo E.thetaStar 1,
      wVSmooth theta / wGSmooth theta =
        E.wageRatio
          (E.Vinf theta (E.gSmooth b) (fun tau => tau ^ a)) theta := by
    intro theta htheta
    exact CESPricePathOn.ratio_eq E Psmooth htheta
  refine ⟨E.intervalIntegral_exp_neg_eq_LambdaJ hr,
    E.intervalIntegral_exp_neg_eq_Lambda hr, ?_, ?_, ?_, ?_⟩
  · exact E.wedge_eq_wedgeExplicit hr hthetaHard.1 hthetaHard.2
      (Phard.hwG_pos thetaHard hthetaHard) hwageHard
  · exact ⟨E.smoothMarginalProductWedge_tendsto_atTop hr
        Psmooth.hwG_pos hwageSmooth,
      E.smoothMarginalProductWedge_tendsto_endpoint hr
        Psmooth.hwG_pos hwageSmooth,
      E.smoothMarginalProductWedge_tendsto_zero hr
        Psmooth.hwG_pos hwageSmooth⟩
  · exact E.hardPromotion_externalityResidual_zero_above
      wVBoundary hBoundary (E.Lambda r) thetaAbove hthetaAbove
  · exact E.thm_externality_pigouvian_cobb_douglas_from_axioms
      Fcd E.eta E.lam G Y wVCD (E.Lambda r) g h thetaCD hCD h_wVCD hY
      hG_pos hVCD_pos E.eta_pos E.eta_lt_one E.lam_pos rfl

/-! ## Proposition 14 and Equation (15): finite profession set. -/

theorem paper_equation15_aggregate_output_exact
    {ι : Type*} (s : Finset ι) (Y w : ι → ℝ) (sigma : ℝ) :
    aggregateCES s Y w sigma =
      (∑ i ∈ s, w i * Y i ^ ((sigma - 1) / sigma)) ^
        (1 / ((sigma - 1) / sigma)) := rfl

theorem paper_proposition14_aggregation_exact
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (Y w : ι → ℝ) {sigma : ℝ}
    (hsigma : 1 < sigma)
    (hY_nonneg : ∀ i ∈ s, 0 ≤ Y i)
    (hw_pos : ∀ i ∈ s, 0 < w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (hzero : ∃ i ∈ s, Y i = 0)
    (hsurvive : ∃ i ∈ s, 0 < Y i) :
    (∏ i ∈ s, Y i ^ w i) = 0 ∧
    0 < aggregateCES s Y w sigma ∧
    Tendsto (aggregateCES s Y w) (nhdsWithin 1 (Ioi 1)) (𝓝 0) := by
  obtain ⟨i0, hi0, hYi0⟩ := hzero
  have hfixed : 0 < aggregateCES s Y w sigma := by
    apply prop_aggregation_fixed_sigma_positive s Y w hsigma hY_nonneg
      (fun i hi => (hw_pos i hi).le)
    obtain ⟨j, hj, hYj⟩ := hsurvive
    exact ⟨j, hj, hYj, hw_pos j hj⟩
  exact ⟨thm_aggregation_cobb_douglas_zero s Y w i0 hi0 hYi0
      (hw_pos i0 hi0), hfixed,
    prop_aggregation_near_cobb_douglas_limit s Y w hY_nonneg hw_pos
      hw_sum ⟨i0, hi0, hYi0⟩ hsurvive⟩

end VerificationAsymmetry.Economy
