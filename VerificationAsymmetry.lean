/-
  VerificationAsymmetry.lean

  Root module. Machine-checked formalization of the structural
  mathematics of:

    Li, Alex Chengyu. *Generation--Verification Asymmetry Inversion
                       and Apprenticeship Pipeline Collapse Under
                       AI Substitution.* 2026.

  Submodules:
    VerificationAsymmetry/Basic.lean         Defs (production economy,
                                             CES, generation supply,
                                             cohort dynamics,
                                             apprenticeship technology,
                                             steady-state stock)
    VerificationAsymmetry/Decomp.lean        Theorem~\ref{thm:decomp}
                                             (stock-flow welfare
                                             decomposition by Euler)
    VerificationAsymmetry/Inversion.lean     Theorem~\ref{thm:inversion}
                                             (CES wage ratio scaling +
                                             closed-form threshold)
    VerificationAsymmetry/Collapse.lean      Theorem~\ref{thm:collapse}
                                             (hard-threshold phase
                                             transition at thetastar +
                                             linear transient decay)
    VerificationAsymmetry/Credential.lean    Theorem~\ref{thm:credential}
                                             (Cobb-Douglas factor-share
                                             closed form + multiplicative
                                             decay structure)
    VerificationAsymmetry/Externality.lean   Theorem~\ref{thm:externality}
                                             (Pigouvian wedge + optimal
                                             subsidy formula)
    VerificationAsymmetry/Recursive.lean     Theorem~\ref{thm:recursive}
                                             (mu-amplification of the
                                             inversion threshold +
                                             collapse invariance)
    VerificationAsymmetry/Aggregation.lean   Theorem~\ref{thm:aggregation}
                                             (Cobb-Douglas aggregation
                                             min-theorem; perfect-
                                             substitutes survival)
    VerificationAsymmetry/EndogenousAI.lean  Theorem~\ref{thm:endogenous-ai}
                                             (Brouwer fixed point;
                                             hysteresis recovery bound)

  Soundness audit:
    VerificationAsymmetry/AxiomAudit.lean — prints axiom dependencies
    of every paper-level theorem.  Expected: standard Lean kernel
    (`propext`, `Classical.choice`, `Quot.sound`) for all closed
    arithmetic theorems.  No Cat 2 axioms are introduced because all
    paper-level mathematical content reduces to real-arithmetic
    identities derivable inside Mathlib.

  Gap ledger:
    VerificationAsymmetry/Ledger.lean — typed record of every closed
    top-level result and every paper claim deferred to economic
    narrative.  Two orthogonal classifications per entry:
      * 5-tier status: gapOpen / gapPartial / gapBlocked / gapDeadEnd /
        gapClosed
      * 3-input-category: cat1Mathlib / cat2External / cat3PaperNovel /
        notInput

  Companion paper.  This formalization is parallel to (and separate
  from) the Karpowicz/Einstein-Test companion at
  `../companion-einstein-test/lean4/`, which formalizes a different
  paper (`einstein_test.tex`).
-/

import VerificationAsymmetry.Basic
import VerificationAsymmetry.Decomp
import VerificationAsymmetry.Inversion
import VerificationAsymmetry.Collapse
import VerificationAsymmetry.Credential
import VerificationAsymmetry.Externality
import VerificationAsymmetry.Recursive
import VerificationAsymmetry.Aggregation
import VerificationAsymmetry.EndogenousAI
