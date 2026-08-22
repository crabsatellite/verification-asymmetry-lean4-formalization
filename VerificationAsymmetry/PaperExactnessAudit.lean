/-
  VerificationAsymmetry/PaperExactnessAudit.lean

  Kernel-checked exact-object consumers for the current journal manuscript.
  The shared paper-infrastructure formal contract pins this file byte-for-byte
  to the numbered TeX objects and equations.  These declarations deliberately
  consume the manuscript's original infimum, piecewise stock, marginal-product
  wedge, discounted-integral, and endpoint-limit carriers; a disconnected
  closed-form surrogate cannot satisfy these types.
-/

import VerificationAsymmetry

namespace VerificationAsymmetry.Economy

open Filter Set
open scoped Topology Interval

variable (E : Economy)

/-- Theorem 9 consumes the paper's infimum-defined crossing threshold. -/
theorem paper_inversion_infimum_exact
    (V rBar : ℝ) (wG wV : ℝ → ℝ)
    (hV_pos : 0 < V) (hrBar_pos : 0 < rBar)
    (hKAI_gt : E.LG < E.KAI) (hrho_lt : E.rho < 1)
    (hGstar_lo : E.LG < E.Gstar V rBar)
    (hGstar_hi : E.Gstar V rBar < E.KAI)
    (hwage : ∀ theta ∈ Icc (0 : ℝ) 1,
      wV theta / wG theta = E.wageRatio V theta) :
    thetaInvMarginalProductInf wG wV rBar = E.thetaInv V rBar :=
  E.thetaInvMarginalProductInf_eq_thetaInv V rBar wG wV hV_pos hrBar_pos
    hKAI_gt hrho_lt hGstar_lo hGstar_hi hwage

/-- Proposition 11 differentiates the same piecewise stock on both sides. -/
theorem paper_smooth_stock_one_sided_derivatives_exact (a b : ℝ) :
    HasDerivWithinAt
        (fun theta => E.Vinf theta (E.gSmooth b) (fun tau => tau ^ a))
        (E.smoothSlopeBelowAtThreshold a) (Iic E.thetaStar) E.thetaStar ∧
      HasDerivWithinAt
        (fun theta => E.Vinf theta (E.gSmooth b) (fun tau => tau ^ a))
        (E.smoothSlopeAboveAtThreshold a b) (Ici E.thetaStar) E.thetaStar :=
  ⟨E.hasDerivWithinAt_smoothStock_left a b,
    E.hasDerivWithinAt_smoothStock_right a b⟩

/-- The paper's strict kink compares those derivatives of the common carrier. -/
theorem paper_smooth_stock_kink_exact
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasDerivWithinAt
        (fun theta => E.Vinf theta (E.gSmooth b) (fun tau => tau ^ a))
        (E.smoothSlopeBelowAtThreshold a) (Iic E.thetaStar) E.thetaStar ∧
      HasDerivWithinAt
        (fun theta => E.Vinf theta (E.gSmooth b) (fun tau => tau ^ a))
        (E.smoothSlopeAboveAtThreshold a b) (Ici E.thetaStar) E.thetaStar ∧
      |E.smoothSlopeBelowAtThreshold a| <
        |E.smoothSlopeAboveAtThreshold a b| :=
  ⟨E.hasDerivWithinAt_smoothStock_left a b,
    E.hasDerivWithinAt_smoothStock_right a b,
    E.prop_smooth_collapse_kink ha hb⟩

/-- The displayed discounted horizons are the original interval integrals. -/
theorem paper_discounted_horizons_exact {r : ℝ} (hr : 0 < r) :
    (∫ s in (0 : ℝ)..E.Tj, Real.exp (-r * s)) = E.LambdaJ r ∧
      (∫ s in E.Tj..E.T, Real.exp (-r * s)) = E.Lambda r :=
  ⟨E.intervalIntegral_exp_neg_eq_LambdaJ hr,
    E.intervalIntegral_exp_neg_eq_Lambda hr⟩

/-- Equation (14) is derived from the actual normalized marginal-product
    wedge, after supplying exactly the CES wage-ratio interface. -/
theorem paper_hard_wedge_exact
    {r a theta wG wV : ℝ}
    (hr : 0 < r) (htheta0 : 0 ≤ theta)
    (hthetaStar : theta < E.thetaStar) (hwG : 0 < wG)
    (hwage : wV / wG = E.wageRatio (E.VinfHard a theta) theta) :
    wedge wG wV (E.gHard (E.eBar theta)) ((E.eBar theta) ^ a)
        (E.LambdaJ r) (E.Lambda r) theta = E.wedgeExplicit r a theta :=
  E.wedge_eq_wedgeExplicit hr htheta0 hthetaStar hwG hwage

/-- The smooth closed form is attached to the paper's original stock,
    promotion, wage-ratio, and horizon objects. -/
theorem paper_smooth_wedge_closed_form_exact
    {wG wV : ℝ → ℝ} {r a b theta : ℝ}
    (hr : 0 < r) (htheta0 : 0 ≤ theta)
    (hthetaStar : E.thetaStar < theta) (htheta1 : theta < 1)
    (hwG : 0 < wG theta)
    (hwage : wV theta / wG theta =
      E.wageRatio (E.Vinf theta (E.gSmooth b) (fun tau => tau ^ a)) theta) :
    E.smoothMarginalProductWedge wG wV r a b theta =
      E.smoothWedgeClosedForm r a b theta := by
  rw [E.smoothMarginalProductWedge_eq_smoothPaperWedge hr htheta1 hwG hwage]
  exact E.smoothPaperWedge_eq_closedForm hr htheta0 hthetaStar htheta1

/-- The endpoint trichotomy is stated for the actual smooth paper wedge. -/
theorem paper_smooth_wedge_endpoint_trichotomy_exact
    {wG wV : ℝ → ℝ} {r a b : ℝ} (hr : 0 < r)
    (hwG : ∀ theta ∈ Ioo E.thetaStar 1, 0 < wG theta)
    (hwage : ∀ theta ∈ Ioo E.thetaStar 1,
      wV theta / wG theta =
        E.wageRatio (E.Vinf theta (E.gSmooth b) (fun tau => tau ^ a)) theta) :
    (E.smoothWedgeExponent a b < 0 →
        Tendsto (fun theta => E.smoothMarginalProductWedge wG wV r a b theta)
          (nhdsWithin 1 (Iio 1)) atTop) ∧
      (E.smoothWedgeExponent a b = 0 →
        Tendsto (fun theta => E.smoothMarginalProductWedge wG wV r a b theta)
          (nhdsWithin 1 (Iio 1))
          (𝓝 (E.smoothWedgeEndpointCoefficient r a b))) ∧
      (0 < E.smoothWedgeExponent a b →
        Tendsto (fun theta => E.smoothMarginalProductWedge wG wV r a b theta)
          (nhdsWithin 1 (Iio 1)) (𝓝 0)) :=
  ⟨E.smoothMarginalProductWedge_tendsto_atTop hr hwG hwage,
    E.smoothMarginalProductWedge_tendsto_endpoint hr hwG hwage,
    E.smoothMarginalProductWedge_tendsto_zero hr hwG hwage⟩

end VerificationAsymmetry.Economy
