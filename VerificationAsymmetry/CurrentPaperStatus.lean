/- Current journal-paper submission coverage status. -/

import VerificationAsymmetry.Ledger
import VerificationAsymmetry.TheoremMap

namespace VerificationAsymmetry.Ledger

/-- Ledger entries consumed by the current paper.  Historical results omitted
    from the current submission manuscript deliberately do not enter this list. -/
def currentPaperEntries : List GapEntry := [
  gap_axiom_ces_wage_ratio,
  gap_axiom_cobb_douglas_factor_share,
  gap_Economy_carrier,
  gap_IsCobbDouglas_predicate,
  gap_IsCES_predicate,
  gap_V2_TacitAccumulation_predicate,
  gap_verification_asymmetry_diagnostic_DEFINITIONAL,
  gap_thm_inversion_threshold_CLOSED,
  gap_thm_inversion_threshold_monotone_CLOSED,
  gap_thm_inversion_wage_ratio_CLOSED,
  gap_wageRatio_eq_ces_marginal_product_ratio_CLOSED,
  gap_thm_collapse_below_CLOSED,
  gap_thm_collapse_jump_CLOSED,
  gap_thm_collapse_jump_diff_CLOSED,
  gap_thm_collapse_above_CLOSED,
  gap_thm_collapse_transient_CLOSED,
  gap_thm_collapse_general_h_CLOSED,
  gap_prop_smooth_collapse_CLOSED,
  gap_thm_externality_wedge_CLOSED,
  gap_thm_externality_nonneg_CLOSED,
  gap_thm_externality_pigouvian_CLOSED,
  gap_thm_externality_residual_identity_CLOSED,
  gap_prop_internalization_CLOSED,
  gap_thm_aggregation_CD_CLOSED,
  gap_prop_aggregation_near_cd_limit_CLOSED
]

def isDerivedUnfinished (g : GapEntry) : Bool :=
  g.inputCategory == InputCategory.notInput &&
    (g.status == GapStatus.gapOpen ||
     g.status == GapStatus.gapPartial ||
     g.status == GapStatus.gapBlocked ||
     g.status == GapStatus.gapDeadEnd)

def currentPaperDerivedUnfinished : List GapEntry :=
  currentPaperEntries.filter isDerivedUnfinished

theorem currentPaper_no_unfinished_derived :
    currentPaperDerivedUnfinished.length = 0 := by decide

#eval s!"current-paper theorem coverage: entries={currentPaperEntries.length} " ++
  s!"unfinishedDerived={currentPaperDerivedUnfinished.length}"

end VerificationAsymmetry.Ledger
