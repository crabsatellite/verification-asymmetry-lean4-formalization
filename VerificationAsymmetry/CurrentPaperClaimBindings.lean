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

structure PaperProductionEnvironment where
  F : ℝ → ℝ → ℝ
  G : ℝ
  V : ℝ
  theta : ℝ
  hCRS : IsCRS F
  hF_nonneg : ∀ G V : ℝ, 0 ≤ G → 0 ≤ V → 0 ≤ F G V
  htheta : theta ∈ Icc (0 : ℝ) 1
  hG_nonneg : 0 ≤ G
  hV_nonneg : 0 ≤ V
  hMarginalG_pos : ∀ G V : ℝ, 0 < G → 0 < V →
    ∃ d : ℝ, HasDerivAt (fun x => F x V) d G ∧ 0 < d
  hMarginalV_pos : ∀ G V : ℝ, 0 < G → 0 < V →
    ∃ d : ℝ, HasDerivAt (fun y => F G y) d V ∧ 0 < d

theorem paper_definition1_parameters_exact
    (P : PaperProductionEnvironment) :
    IsCRS P.F ∧
    (∀ G V : ℝ, 0 ≤ G → 0 ≤ V → 0 ≤ P.F G V) ∧
    P.theta ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ P.G ∧ 0 ≤ P.V ∧
    (∀ G V : ℝ, 0 < G → 0 < V →
      ∃ d : ℝ, HasDerivAt (fun x => P.F x V) d G ∧ 0 < d) ∧
    (∀ G V : ℝ, 0 < G → 0 < V →
      ∃ d : ℝ, HasDerivAt (fun y => P.F G y) d V ∧ 0 < d) ∧
    0 < E.LG ∧ 0 < E.KAI ∧ 0 < E.lam ∧ 0 < E.nu ∧
      0 < E.Tj ∧ E.Tj < E.T ∧ 0 < E.tauStar ∧
      E.tauStar < E.Tj ∧ 0 < E.eta ∧ E.eta < 1 ∧ E.rho ≤ 1 :=
  ⟨P.hCRS, P.hF_nonneg, P.htheta, P.hG_nonneg, P.hV_nonneg,
    P.hMarginalG_pos, P.hMarginalV_pos,
    E.LG_pos, E.KAI_pos, E.lam_pos, E.nu_pos, E.Tj_pos, E.Tj_lt_T,
    E.tauStar_pos, E.tauStar_lt_Tj, E.eta_pos, E.eta_lt_one, E.rho_le_one⟩

theorem paper_equation1_ces_exact
    (F : ℝ → ℝ → ℝ) (hCES : IsCES F E.eta E.rho E.lam)
    (_hrho_ne : E.rho ≠ 0) {G V : ℝ} (hG : 0 < G) (hV : 0 < V) :
    F G V =
      (E.eta * G ^ E.rho + (1 - E.eta) * (E.lam * V) ^ E.rho) ^
        (1 / E.rho) :=
  hCES G V hG hV

theorem paper_definition3_generation_supply_exact
    (theta : ℝ) (_htheta : theta ∈ Icc (0 : ℝ) 1) :
    E.G theta = (1 - theta) * E.LG + theta * E.KAI ∧
    (0 < theta → Tendsto (fun K => generationAtCapacity E.LG theta K)
      atTop atTop) := by
  exact ⟨rfl, generationAtCapacity_tendsto_atTop⟩

theorem paper_equation2_generation_supply_exact
    (theta : ℝ) (_htheta : theta ∈ Icc (0 : ℝ) 1) :
    E.G theta = (1 - theta) * E.LG + theta * E.KAI := rfl

structure PaperCohortPrimitives where
  theta : ℝ → ℝ
  g : ℝ → ℝ
  h : ℝ → ℝ
  htheta_range : ∀ t : ℝ, theta t ∈ Icc (0 : ℝ) 1
  hg_range : ∀ tau : ℝ, 0 ≤ tau → g tau ∈ Icc (0 : ℝ) 1
  hg_monotone : Monotone g
  hg_zero : g 0 = 0
  hg_threshold : g E.tauStar = 1
  hh_nonneg : ∀ tau : ℝ, 0 ≤ tau → 0 ≤ h tau
  hh_monotone : Monotone h
  hh_zero : h 0 = 0

def juniorAt (c t : ℝ) : Prop := c ≤ t ∧ t ≤ c + E.Tj

def seniorAt (c t : ℝ) : Prop := c + E.Tj ≤ t ∧ t ≤ c + E.T

noncomputable def cohortPromotionProbability
    (P : E.PaperCohortPrimitives) (c : ℝ) : ℝ :=
  P.g (E.cumulativeExperience P.theta c)

noncomputable def cohortVerificationCapacity
    (P : E.PaperCohortPrimitives) (c : ℝ) : ℝ :=
  P.h (E.cumulativeExperience P.theta c)

theorem paper_definition4_cohort_dynamics_exact
    (P : E.PaperCohortPrimitives) (c t : ℝ) :
    0 < E.nu ∧ 0 < E.Tj ∧ E.Tj < E.T ∧
    (E.juniorAt c t ↔ c ≤ t ∧ t ≤ c + E.Tj) ∧
    (E.seniorAt c t ↔ c + E.Tj ≤ t ∧ t ≤ c + E.T) ∧
    E.cumulativeExperience P.theta c =
      ∫ s in c..c + E.Tj, (1 - P.theta s) ∧
    E.cohortPromotionProbability P c =
      P.g (E.cumulativeExperience P.theta c) ∧
    E.cohortVerificationCapacity P c =
      P.h (E.cumulativeExperience P.theta c) ∧
    (∀ t : ℝ, P.theta t ∈ Icc (0 : ℝ) 1) ∧
    (∀ tau : ℝ, 0 ≤ tau → P.g tau ∈ Icc (0 : ℝ) 1) ∧
    Monotone P.g ∧ P.g 0 = 0 ∧ P.g E.tauStar = 1 ∧
    (∀ tau : ℝ, 0 ≤ tau → 0 ≤ P.h tau) ∧
    Monotone P.h ∧ P.h 0 = 0 :=
  ⟨E.nu_pos, E.Tj_pos, E.Tj_lt_T, Iff.rfl, Iff.rfl, rfl, rfl, rfl,
    P.htheta_range, P.hg_range, P.hg_monotone, P.hg_zero, P.hg_threshold, P.hh_nonneg,
    P.hh_monotone, P.hh_zero⟩

theorem paper_equation3_cumulative_experience_exact
    (theta : ℝ → ℝ) (c : ℝ)
    (_htheta : ∀ t, theta t ∈ Icc (0 : ℝ) 1) :
    E.cumulativeExperience theta c =
      ∫ s in c..c + E.Tj, (1 - theta s) := rfl

theorem paper_assumption6_time_indexed_stock_exact
    (P : E.PaperCohortPrimitives) (t : ℝ) :
    E.timeIndexedStock P.theta P.g P.h t =
      E.nu * ∫ c in t - E.T..t - E.Tj,
        P.g (E.cumulativeExperience P.theta c) *
          P.h (E.cumulativeExperience P.theta c) :=
  E.timeIndexedStock_eq_cohort_integral P.theta P.g P.h t

theorem paper_lemma7_steady_state_stock_exact
    (theta : ℝ) (g h : ℝ → ℝ) (t : ℝ) :
    E.timeIndexedStock (fun _ => theta) g h t =
      E.nu * E.Ts * g ((1 - theta) * E.Tj) * h ((1 - theta) * E.Tj) := by
  rw [E.timeIndexedStock_const_eq_Vinf]
  rfl

theorem paper_equation4_steady_state_stock_exact
    (theta : ℝ) (P : E.PaperCohortPrimitives)
    (_htheta : theta ∈ Icc (0 : ℝ) 1) :
    E.Vinf theta P.g P.h =
      E.nu * E.Ts * P.g ((1 - theta) * E.Tj) *
        P.h ((1 - theta) * E.Tj) := rfl

theorem paper_equation5_hard_stock_exact
    (a theta : ℝ) (_ha : 0 < a) (_ha_le : a ≤ 1)
    (_htheta : theta ∈ Icc (0 : ℝ) 1) :
    E.VinfHard a theta =
      if theta ≤ E.thetaStar then
        E.nu * E.Ts * ((1 - theta) * E.Tj) ^ a
      else 0 := by
  by_cases htheta : theta ≤ E.thetaStar
  · rw [if_pos htheta, E.thm_collapse_below_threshold a theta htheta]
    rfl
  · have hthetaStar : E.thetaStar < theta := lt_of_not_ge htheta
    rw [if_neg htheta, E.thm_collapse_above_threshold a theta hthetaStar]

theorem paper_equation6_smooth_stock_exact
    (a b theta : ℝ) (_ha : 0 < a) (_ha_le : a ≤ 1) (_hb : 0 < b)
    (_htheta : theta ∈ Icc (0 : ℝ) 1) :
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
    E.VerificationAsymmetryDiagnostic theta g h ↔
      (∀ t, E.timeIndexedStock theta g h t =
        E.nu * ∫ c in t - E.T..t - E.Tj,
          g (E.cumulativeExperience theta c) *
            h (E.cumulativeExperience theta c)) ∧
      V2_TacitAccumulation h ∧
      (∀ c, E.cumulativeExperience theta c =
        ∫ s in c..c + E.Tj, (1 - theta s)) := by
  constructor
  · intro hdiag
    exact ⟨hdiag.v1_verification_non_substitutability,
      hdiag.v2_tacit_accumulation, hdiag.v3_generation_displacement⟩
  · rintro ⟨hV1, hV2, hV3⟩
    exact {
      v1_verification_non_substitutability := hV1
      v2_tacit_accumulation := hV2
      v3_generation_displacement := hV3
    }

/-! ## CES price paths: the paper's marginal-product premises as a typed bundle. -/

structure CESPricePathOn
    (F : ℝ → ℝ → ℝ) (Vstock wG wV : ℝ → ℝ) (domain : Set ℝ) : Prop where
  hCES : IsCES F E.eta E.rho E.lam
  hrho_lt : E.rho < 1
  hrho_ne : E.rho ≠ 0
  hG_pos : ∀ theta ∈ domain, 0 < E.G theta
  hV_pos : ∀ theta ∈ domain, 0 < Vstock theta
  hwG_pos : ∀ theta ∈ domain, 0 < wG theta
  hwV_pos : ∀ theta ∈ domain, 0 < wV theta
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
        (E.Gstar V rBar - E.LG) / (E.KAI - E.LG) ∧
      thetaInvMarginalProductInf wG wV rBar ∈ Ioo (0 : ℝ) 1 := by
  have hwage : ∀ theta ∈ Icc (0 : ℝ) 1,
      wV theta / wG theta = E.wageRatio V theta := by
    intro theta htheta
    exact CESPricePathOn.ratio_eq E P htheta
  have hactual := E.thetaInvMarginalProductInf_eq_thetaInv V rBar wG wV
    (P.hV_pos 0 ⟨le_rfl, zero_le_one⟩) hrBar_pos hKAI_gt P.hrho_lt
    hGstar_lo hGstar_hi hwage
  have hrange := E.thm_inversion_threshold_in_unit_interval V rBar hKAI_gt
    hGstar_lo hGstar_hi
  constructor
  · exact hactual
  · rw [hactual]
    exact hrange

theorem paper_theorem9_inversion_exact
    (F : ℝ → ℝ → ℝ) (V : ℝ) (wG wV : ℝ → ℝ → ℝ)
    (P : E.CESCapacityPriceFamily F V wG wV) :
    (∀ theta ∈ Icc (0 : ℝ) 1,
      wV E.KAI theta / wG E.KAI theta = E.wageRatio V theta) ∧
    (E.LG ≤ E.KAI →
      ∀ ⦃theta1 theta2 : ℝ⦄, 0 ≤ theta1 → theta2 ≤ 1 → theta1 ≤ theta2 →
        wV E.KAI theta1 / wG E.KAI theta1 ≤
          wV E.KAI theta2 / wG E.KAI theta2) ∧
    (E.LG < E.KAI →
      ∀ ⦃theta1 theta2 : ℝ⦄, 0 ≤ theta1 → theta2 ≤ 1 → theta1 < theta2 →
        wV E.KAI theta1 / wG E.KAI theta1 <
          wV E.KAI theta2 / wG E.KAI theta2) ∧
    (∀ rBar : ℝ, 0 < rBar → E.LG < E.Gstar V rBar →
      E.Gstar V rBar < E.KAI →
        thetaInvMarginalProductInf (wG E.KAI) (wV E.KAI) rBar =
            (E.Gstar V rBar - E.LG) / (E.KAI - E.LG) ∧
          thetaInvMarginalProductInf (wG E.KAI) (wV E.KAI) rBar ∈
            Ioo (0 : ℝ) 1) ∧
    (∀ {rBar1 rBar2 : ℝ}, 0 < rBar1 → rBar1 < rBar2 →
      E.LG < E.Gstar V rBar1 → E.Gstar V rBar2 < E.KAI →
        thetaInvMarginalProductInf (wG E.KAI) (wV E.KAI) rBar1 <
          thetaInvMarginalProductInf (wG E.KAI) (wV E.KAI) rBar2) ∧
    (∀ {rBar K1 K2 : ℝ}, 0 < rBar →
      E.LG < E.Gstar V rBar → E.Gstar V rBar < K1 → K1 < K2 →
      thetaInvAtCapacity E.LG (E.Gstar V rBar) K2 <
        thetaInvAtCapacity E.LG (E.Gstar V rBar) K1) ∧
    (∀ theta ∈ Ioc (0 : ℝ) 1,
      Tendsto (fun K => wV K theta / wG K theta) atTop atTop) ∧
    (∀ rBar : ℝ, 0 < rBar → E.LG < E.Gstar V rBar →
      ∀ᶠ K : ℝ in atTop,
        thetaInvMarginalProductInfAtCapacity wG wV rBar K =
            thetaInvAtCapacity E.LG (E.Gstar V rBar) K ∧
          thetaInvMarginalProductInfAtCapacity wG wV rBar K ∈
            Ioo (0 : ℝ) 1) ∧
    (∀ rBar : ℝ, 0 < rBar → E.LG < E.Gstar V rBar →
      Tendsto
        (fun K => thetaInvMarginalProductInfAtCapacity wG wV rBar K)
        atTop (nhdsWithin 0 (Ioi 0))) ∧
    (∀ rBar : ℝ, rBar ≤ wV E.KAI 0 / wG E.KAI 0 →
      thetaInvMarginalProductInf (wG E.KAI) (wV E.KAI) rBar = 0) := by
  have hwage : ∀ theta ∈ Icc (0 : ℝ) 1,
      wV E.KAI theta / wG E.KAI theta = E.wageRatio V theta := by
    intro theta htheta
    simpa [wageRatioAtCapacity, generationAtCapacity, wageRatio, G] using
      P.ratio_eq E E.KAI_pos htheta
  refine ⟨hwage, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hKAI_ge theta1 theta2 htheta1 htheta2 htheta12
    rw [hwage theta1 ⟨htheta1, le_trans htheta12 htheta2⟩,
      hwage theta2 ⟨le_trans htheta1 htheta12, htheta2⟩]
    exact E.thm_inversion_wage_ratio_monotone V P.hV_pos hKAI_ge
      P.hrho_lt htheta1 htheta2 htheta12
  · intro hKAI_gt theta1 theta2 htheta1 htheta2 htheta12
    rw [hwage theta1 ⟨htheta1, le_trans htheta12.le htheta2⟩,
      hwage theta2 ⟨le_trans htheta1 htheta12.le, htheta2⟩]
    exact E.thm_inversion_wage_ratio_strict V P.hV_pos hKAI_gt P.hrho_lt
      htheta1 htheta2 htheta12
  · intro rBar hrBar hGstar_lo hGstar_hi
    have hactual := E.thetaInvMarginalProductInf_eq_thetaInv V rBar
      (wG E.KAI) (wV E.KAI) P.hV_pos hrBar
      (lt_trans hGstar_lo hGstar_hi) P.hrho_lt hGstar_lo hGstar_hi hwage
    have hrange := E.thm_inversion_threshold_in_unit_interval V rBar
      (lt_trans hGstar_lo hGstar_hi) hGstar_lo hGstar_hi
    exact ⟨hactual, by rw [hactual]; exact hrange⟩
  · intro rBar1 rBar2 hrBar1 hrBar12 hGstar1_lo hGstar2_hi
    have hGstar12 := E.Gstar_strict_in_rBar V P.hV_pos hrBar1 hrBar12 P.hrho_lt
    have hGstar1_hi : E.Gstar V rBar1 < E.KAI :=
      lt_trans hGstar12 hGstar2_hi
    have hGstar2_lo : E.LG < E.Gstar V rBar2 :=
      lt_trans hGstar1_lo hGstar12
    rw [E.thetaInvMarginalProductInf_eq_thetaInv V rBar1
        (wG E.KAI) (wV E.KAI) P.hV_pos
        hrBar1 (lt_trans hGstar1_lo hGstar1_hi) P.hrho_lt hGstar1_lo
        hGstar1_hi hwage,
      E.thetaInvMarginalProductInf_eq_thetaInv V rBar2
        (wG E.KAI) (wV E.KAI) P.hV_pos
        (lt_trans hrBar1 hrBar12) (lt_trans hGstar2_lo hGstar2_hi) P.hrho_lt
        hGstar2_lo hGstar2_hi hwage]
    exact E.thm_inversion_threshold_strict_in_rBar V P.hV_pos hrBar1 hrBar12
      (lt_trans hGstar1_lo hGstar1_hi) P.hrho_lt
  · intro rBar K1 K2 _hrBar hcrit hK1 hK12
    exact thetaInvAtCapacity_strictAnti hcrit hK1 hK12
  · intro theta htheta
    exact E.marginalProductWageRatioAtCapacity_tendsto_atTop P htheta.1 htheta.2
  · intro rBar hrBar hbaseline
    exact E.thetaInvMarginalProductInfAtCapacity_eventually_interior P rBar
      hrBar hbaseline
  · intro rBar hrBar hbaseline
    exact E.thetaInvMarginalProductInfAtCapacity_tendsto_zero_right P rBar
      hrBar hbaseline
  · intro rBar hbaseline
    exact thetaInvMarginalProductInf_eq_zero_of_target_le_baseline
      (wG E.KAI) (wV E.KAI) rBar hbaseline

/-! ## Theorem 10 and Equations (9)--(10). -/

structure PaperStepContext (theta0 theta1 : ℝ) : Prop where
  theta0_range : theta0 ∈ Ico (0 : ℝ) E.thetaStar
  theta1_range : theta1 ∈ Ioc E.thetaStar 1

theorem paper_equation9_collapse_threshold_exact :
    E.thetaStar = 1 - E.tauStar / E.Tj := rfl

theorem paper_equation10_transient_stock_exact
    (a theta0 theta1 t : ℝ) (_ha : 0 < a)
    (P : E.PaperStepContext theta0 theta1) (ht0 : 0 ≤ t) :
    E.preStepStockIntegral theta0 (fun tau => tau ^ a) t =
      E.Vinf theta0 E.gHard (fun tau => tau ^ a) *
        max 0 (1 - t / E.Ts) := by
  rw [E.preStepStockIntegral_eq_transientStock theta0 (fun tau => tau ^ a)
    ht0 P.theta0_range.2]
  rfl

theorem hasDerivAt_VinfHard_below
    {a theta : ℝ} (htheta : theta < E.thetaStar) :
    HasDerivAt (fun x => E.VinfHard a x)
      (E.hardStockSlopeBelow a theta) theta := by
  have heventually :
      (fun x => E.VinfHard a x) =ᶠ[𝓝 theta]
        (fun x => E.nu * E.Ts * E.eBar x ^ a) := by
    filter_upwards [Iio_mem_nhds htheta] with x hx
    exact E.thm_collapse_below_threshold a x hx.le
  exact (E.hasDerivAt_hard_stock_below a theta htheta).congr_of_eventuallyEq
    heventually

theorem paper_theorem10_pipeline_collapse_exact
    {a thetaBelow thetaAbove theta0 theta1 c t tclear : ℝ}
    (ha : 0 < a) (_hthetaBelow0 : 0 ≤ thetaBelow)
    (hthetaBelow : thetaBelow < E.thetaStar)
    (hthetaAbove : E.thetaStar < thetaAbove) (_hthetaAbove1 : thetaAbove ≤ 1)
    (_hstep0_nonneg : 0 ≤ theta0) (hstep0 : theta0 < E.thetaStar)
    (hstep1 : E.thetaStar < theta1) (_hstep1_le : theta1 ≤ 1)
    (_ht_nonneg : 0 ≤ t)
    (htclear : E.T - E.cStar theta0 theta1 ≤ tclear) :
    E.thetaStar = 1 - E.tauStar / E.Tj ∧
    (0 < E.cStar theta0 theta1 ∧ E.cStar theta0 theta1 < E.Tj) ∧
    E.VinfHard a thetaBelow =
      E.nu * E.Ts * ((1 - thetaBelow) * E.Tj) ^ a ∧
    HasDerivAt
      (fun theta => E.VinfHard a theta)
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
      E.nu * (∫ cohort in t - E.T..t - E.Tj,
        if cohort ≤ -E.cStar theta0 theta1 then
          (E.stepExperience theta0 theta1 cohort) ^ a
        else 0) ∧
    E.exactStepStock theta0 theta1 (fun tau => tau ^ a) tclear = 0 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact E.cStar_mem_open_interval hstep0 hstep1
  · rw [E.thm_collapse_below_threshold a thetaBelow hthetaBelow.le]
    rfl
  · exact E.hasDerivAt_VinfHard_below hthetaBelow
  · exact E.hardStockSlopeBelow_neg ha hthetaBelow
  · exact E.thm_collapse_jump_magnitude a
  · exact E.VinfHard_tendsto_left_at_thetaStar a
  · exact E.VinfHard_tendsto_right_zero_at_thetaStar a
  · exact E.thm_collapse_above_threshold a thetaAbove hthetaAbove
  · exact E.cumulativeExperience_step_eq_stepExperience theta0 theta1 c
  · exact E.stepExperience_ge_tauStar_iff hstep0 hstep1
  · calc
      E.timeIndexedStock (stepSubstitutionPath theta0 theta1) E.gHard
          (fun tau => tau ^ a) t =
        E.exactStepStock theta0 theta1 (fun tau => tau ^ a) t :=
          E.timeIndexedStock_step_eq_exactStepStock (fun tau => tau ^ a) t
            hstep0 hstep1
      _ = E.nu * (∫ cohort in t - E.T..t - E.Tj,
          if cohort ≤ -E.cStar theta0 theta1 then
            (E.stepExperience theta0 theta1 cohort) ^ a else 0) :=
          E.exactStepStock_eq_cohort_integral theta0 theta1
            (fun tau => tau ^ a) t
  · exact E.exactStepStock_zero_after_last_straddle theta0 theta1
      (fun tau => tau ^ a) htclear

/-! ## Proposition 11 and Equation (11). -/

structure PaperSmoothThresholdContext (a b : ℝ) : Prop where
  ha_pos : 0 < a
  ha_le_one : a ≤ 1
  hb_pos : 0 < b

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
    {a b theta : ℝ} (_P : PaperSmoothThresholdContext a b)
    (hthetaStar : E.thetaStar < theta)
    (htheta1 : theta < 1) :
    E.Vinf theta (E.gSmooth b) (fun tau => tau ^ a) =
      E.nu * E.Ts * E.Tj ^ (a + b) * E.tauStar ^ (-b) *
        (1 - theta) ^ (a + b) :=
  E.smoothStockAbove_eq_paperClosedForm hthetaStar htheta1

theorem continuousAt_smoothStock_threshold (a b : ℝ) :
    ContinuousAt
      (fun x => E.Vinf x (E.gSmooth b) (fun tau => tau ^ a))
      E.thetaStar := by
  have hleft := (E.hasDerivWithinAt_smoothStock_left a b).continuousWithinAt
  have hright := (E.hasDerivWithinAt_smoothStock_right a b).continuousWithinAt
  have hunion := hleft.union hright
  have hcover : Iic E.thetaStar ∪ Ici E.thetaStar = (Set.univ : Set ℝ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_univ, iff_true]
    exact le_total x E.thetaStar
  rw [hcover] at hunion
  exact (continuousWithinAt_univ _ _).1 hunion

theorem smoothStock_tendsto_zero
    {a b : ℝ} (hab : 0 < a + b) :
    Tendsto
      (fun theta => E.Vinf theta (E.gSmooth b) (fun tau => tau ^ a))
      (nhdsWithin 1 (Iio 1)) (𝓝 0) := by
  have hid : Tendsto (fun x : ℝ => x)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := tendsto_id.mono_left inf_le_left
  have hpow : Tendsto (fun x : ℝ => x ^ (a + b))
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := hid.rpow_const_nhds_zero hab
  have htheta := hpow.comp one_sub_tendsto_nhdsGT_zero
  let C : ℝ := E.nu * E.Ts * E.Tj ^ (a + b) * E.tauStar ^ (-b)
  have hclosed : Tendsto (fun theta => C * (1 - theta) ^ (a + b))
      (nhdsWithin 1 (Iio 1)) (𝓝 0) := by
    simpa using Tendsto.const_mul C htheta
  have hstarAt : ∀ᶠ theta : ℝ in 𝓝 1, E.thetaStar < theta :=
    Ioi_mem_nhds E.thetaStar_in_unit_interval.2
  have hstar : ∀ᶠ theta in nhdsWithin 1 (Iio 1), E.thetaStar < theta :=
    hstarAt.filter_mono inf_le_left
  have heq :
      (fun theta => E.Vinf theta (E.gSmooth b) (fun tau => tau ^ a)) =ᶠ[
        nhdsWithin 1 (Iio 1)]
      (fun theta => C * (1 - theta) ^ (a + b)) := by
    filter_upwards [self_mem_nhdsWithin, hstar] with theta htheta1 hthetaStar
    simpa [C] using E.smoothStockAbove_eq_paperClosedForm hthetaStar htheta1
  exact hclosed.congr' heq.symm

theorem paper_proposition11_smooth_collapse_exact
    {a b theta : ℝ} (ha : 0 < a) (_ha_le : a ≤ 1) (hb : 0 < b)
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
    ContinuousAt
      (fun x => E.Vinf x (E.gSmooth b) (fun tau => tau ^ a))
      E.thetaStar ∧
    Tendsto
      (fun x => E.Vinf x (E.gSmooth b) (fun tau => tau ^ a))
      (nhdsWithin 1 (Iio 1)) (𝓝 0) ∧
    |E.smoothSlopeBelowAtThreshold a| <
      |E.smoothSlopeAboveAtThreshold a b| := by
  exact ⟨E.smoothStockAbove_eq_paperClosedForm hthetaStar htheta1,
    E.hasDerivWithinAt_smoothStock_left a b,
    E.hasDerivWithinAt_smoothStock_right a b,
    E.continuousAt_smoothStock_threshold a b,
    E.smoothStock_tendsto_zero (by linarith),
    E.prop_smooth_collapse_kink ha hb⟩

/-! ## Theorem 13 and Equations (12)--(14). -/

structure PaperExternalityIncidenceContext
    (F : ℝ → ℝ → ℝ) (g h : ℝ → ℝ) (theta V r wG wV : ℝ)
    (stationaryThetaAndPrices employerCapturesJuniorGeneration
      employerCapturesNoLaterVerificationRent entrantIsPriceTaking : Prop) : Prop where
  theta_range : theta ∈ Icc (0 : ℝ) 1
  steady_stock : V = E.Vinf theta g h
  discount_pos : 0 < r
  generation_price_pos : 0 < wG
  verification_price_pos : 0 < wV
  generation_price : HasDerivAt (fun x => F x V) wG (E.G theta)
  verification_price : HasDerivAt (fun y => F (E.G theta) y) wV V
  h_stationary : stationaryThetaAndPrices
  h_capture_generation : employerCapturesJuniorGeneration
  h_no_capture_verification : employerCapturesNoLaterVerificationRent
  h_price_taking : entrantIsPriceTaking

theorem paper_equation12_social_present_value_exact
    (F : ℝ → ℝ → ℝ) (g h : ℝ → ℝ) (theta V r wG wV : ℝ)
    {stationaryThetaAndPrices employerCapturesJuniorGeneration
      employerCapturesNoLaterVerificationRent entrantIsPriceTaking : Prop}
    (_P : E.PaperExternalityIncidenceContext F g h theta V r wG wV
      stationaryThetaAndPrices employerCapturesJuniorGeneration
      employerCapturesNoLaterVerificationRent entrantIsPriceTaking) :
    MPsoc wG wV (g (E.eBar theta)) (h (E.eBar theta))
        (E.LambdaJ r) (E.Lambda r) theta =
      MPpriv wG (E.LambdaJ r) theta +
        wV * g (E.eBar theta) * h (E.eBar theta) * E.Lambda r := rfl

theorem paper_equation13_apprenticeship_wedge_exact
    (F : ℝ → ℝ → ℝ) (g h : ℝ → ℝ) (theta V r wG wV : ℝ)
    {stationaryThetaAndPrices employerCapturesJuniorGeneration
      employerCapturesNoLaterVerificationRent entrantIsPriceTaking : Prop}
    (P : E.PaperExternalityIncidenceContext F g h theta V r wG wV
      stationaryThetaAndPrices employerCapturesJuniorGeneration
      employerCapturesNoLaterVerificationRent entrantIsPriceTaking)
    (htheta1 : theta < 1) :
    wedge wG wV (g (E.eBar theta)) (h (E.eBar theta))
        (E.LambdaJ r) (E.Lambda r) theta =
      (wV / wG) *
        (g (E.eBar theta) * h (E.eBar theta) * E.Lambda r) /
          ((1 - theta) * E.LambdaJ r) :=
  thm_externality_wedge_identity wG wV (g (E.eBar theta))
    (h (E.eBar theta)) (E.LambdaJ r) (E.Lambda r) theta
    P.generation_price_pos (E.LambdaJ_pos P.discount_pos) htheta1

theorem paper_equation14_explicit_wedge_exact
    (F : ℝ → ℝ → ℝ) (wG wV : ℝ → ℝ)
    (r a theta : ℝ)
    (P : E.CESPricePathOn F (fun x => E.VinfHard a x) wG wV
      (Ico (0 : ℝ) E.thetaStar))
    (hr : 0 < r) (_ha : 0 < a) (_ha_le : a ≤ 1)
    (htheta : theta ∈ Ico (0 : ℝ) E.thetaStar) :
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
    (ha_pos : 0 < a) (ha_le : a ≤ 1) (_hb_pos : 0 < b)
    (hKAI_ge : E.LG ≤ E.KAI)
    (hthetaAbove : E.thetaStar < thetaAbove) (_hthetaAbove1 : thetaAbove ≤ 1)
    (g h : ℝ → ℝ) (thetaCD G Y wVCD : ℝ)
    (_hthetaCD : thetaCD ∈ Icc (0 : ℝ) 1)
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
    (∀ ⦃theta1 theta2 : ℝ⦄,
      theta1 ∈ Ico (0 : ℝ) E.thetaStar →
      theta2 ∈ Ico (0 : ℝ) E.thetaStar → theta1 ≤ theta2 →
      wedge (wGHard theta1) (wVHard theta1)
          (E.gHard (E.eBar theta1)) (E.eBar theta1 ^ a)
          (E.LambdaJ r) (E.Lambda r) theta1 ≤
        wedge (wGHard theta2) (wVHard theta2)
          (E.gHard (E.eBar theta2)) (E.eBar theta2 ^ a)
          (E.LambdaJ r) (E.Lambda r) theta2) ∧
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
    E.gHard (E.eBar E.thetaStar) = 1 ∧
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
    E.intervalIntegral_exp_neg_eq_Lambda hr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact E.wedge_eq_wedgeExplicit hr hthetaHard.1 hthetaHard.2
      (Phard.hwG_pos thetaHard hthetaHard) hwageHard
  · intro theta1 theta2 htheta1 htheta2 htheta12
    rw [E.paper_equation14_explicit_wedge_exact Fces wGHard wVHard r a
      theta1 Phard hr ha_pos ha_le htheta1,
      E.paper_equation14_explicit_wedge_exact Fces wGHard wVHard r a
        theta2 Phard hr ha_pos ha_le htheta2]
    exact E.wedgeExplicit_monotone hr ha_pos ha_le Phard.hrho_lt hKAI_ge
      htheta1.1 htheta12 htheta2.2
  · exact ⟨E.smoothMarginalProductWedge_tendsto_atTop hr
        Psmooth.hwG_pos hwageSmooth,
      E.smoothMarginalProductWedge_tendsto_endpoint hr
        Psmooth.hwG_pos hwageSmooth,
      E.smoothMarginalProductWedge_tendsto_zero hr
        Psmooth.hwG_pos hwageSmooth⟩
  · exact E.gHard_of_ge (by simp)
  · exact E.hardPromotion_externalityResidual_zero_above
      wVBoundary hBoundary (E.Lambda r) thetaAbove hthetaAbove
  · exact E.thm_externality_pigouvian_cobb_douglas_from_axioms
      Fcd E.eta E.lam G Y wVCD (E.Lambda r) g h thetaCD hCD h_wVCD hY
      hG_pos hVCD_pos E.eta_pos E.eta_lt_one E.lam_pos rfl

/-! ## Proposition 14 and Equation (15): finite profession set. -/

structure PaperAggregationContext
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (Y w : ι → ℝ) : Prop where
  output_nonneg : ∀ i ∈ s, 0 ≤ Y i
  weight_pos : ∀ i ∈ s, 0 < w i
  weight_sum : ∑ i ∈ s, w i = 1
  has_zero : ∃ i ∈ s, Y i = 0
  has_positive : ∃ i ∈ s, 0 < Y i

theorem paper_equation15_aggregate_output_exact
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (Y w : ι → ℝ)
    (_P : PaperAggregationContext s Y w) (sigma : ℝ)
    (hsigma : 1 < sigma) :
    aggregateCES s Y w sigma =
      (∑ i ∈ s, w i * Y i ^ ((sigma - 1) / sigma)) ^
        (1 / ((sigma - 1) / sigma)) ∧
      0 < (sigma - 1) / sigma := by
  exact ⟨rfl, aggregationQ_pos hsigma⟩

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
