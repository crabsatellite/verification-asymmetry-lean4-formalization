/-
  Compatibility audit for the current manuscript.

  The authoritative one-declaration-per-claim types now live in
  CurrentPaperClaimBindings.lean.  This file intentionally declares no
  provider-premise wrappers of its own; it checks the strict roots and prints
  the load-bearing project axioms at those exact endpoints.
-/

import VerificationAsymmetry.CurrentPaperClaimBindings

#check VerificationAsymmetry.Economy.paper_definition1_parameters_exact
#check VerificationAsymmetry.Economy.paper_theorem9_inversion_exact
#check VerificationAsymmetry.Economy.paper_theorem10_pipeline_collapse_exact
#check VerificationAsymmetry.Economy.paper_proposition11_smooth_collapse_exact
#check VerificationAsymmetry.Economy.paper_theorem13_externality_exact
#check VerificationAsymmetry.Economy.paper_proposition14_aggregation_exact

#print axioms VerificationAsymmetry.Economy.paper_theorem9_inversion_exact
#print axioms VerificationAsymmetry.Economy.paper_theorem10_pipeline_collapse_exact
#print axioms VerificationAsymmetry.Economy.paper_proposition11_smooth_collapse_exact
#print axioms VerificationAsymmetry.Economy.paper_theorem13_externality_exact
#print axioms VerificationAsymmetry.Economy.paper_proposition14_aggregation_exact
