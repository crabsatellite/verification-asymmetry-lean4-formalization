/-
  VerificationAsymmetry/Ledger.lean

  Gap ledger.  Every closed top-level result and every paper-level
  claim deferred to economic narrative is recorded as a typed
  `GapEntry` with TWO orthogonal classifications plus a Cat 3
  sub-type refinement:

    * 7-tier status:    gapOpen / gapPartial / gapBlocked / gapDeadEnd /
                        gapClosed / gapClosedConditional / gapDefinitional
    * 4-input-category: cat1Mathlib / cat2External / cat3PaperNovel /
                        notInput  (Cat 0 = Lean kernel layer is not
                        tracked here)
    * Cat 3 sub-type:   carrier / hypothesisPredicate /
                        structuralEquation / workingAssumption /
                        conditionalHypothesis / phenomenologicalConjecture /
                        notCat3

  Pre-attack discipline.  Scan this ledger before launching new
  attacks.  Re-attempting a `gapBlocked` or `gapDeadEnd` route is a
  context-drift failure mode.

  `attackHistory` is the canonical location for round metadata
  (citation revisions, atomic refactors, prior retractions); docstrings
  and scope fields are kept to current-state content only.

  *Inventory profile.*  The paper's structural mathematics is
  real-analytic — CES algebra, linear-cohort accounting, 1-D IVT
  (the paper's "Brouwer-fixed-point" application reduces to
  intermediate-value theorem on the real line), finite-product
  algebra.  Most paper-level theorems reduce to Mathlib real-
  arithmetic plus the Lean kernel.

  Three textbook microeconomics facts enter the proofs and are
  not derivable from an abstract `F : ℝ → ℝ → ℝ` parameter alone:

    * `axiom_euler_crs` — Euler's identity for CRS production,
      Euler 1755 (original) / Mas-Colell-Whinston-Green 1995 §5.B.2
      (modern textbook) (Cat 2);
    * `axiom_ces_wage_ratio` — CES marginal-product wage ratio
      closed form, Arrow-Chenery-Minhas-Solow 1961 (original CES
      paper) / Acemoglu 2009 Ch. 15 (modern textbook) (Cat 2);
    * `axiom_cobb_douglas_factor_share` — Cobb-Douglas verification
      factor share `w_V V = (1-η) Y`, Cobb-Douglas 1928 (original) /
      Mas-Colell-Whinston-Green 1995 §5.B.2 (modern textbook) (Cat 2).

  Each axiom takes explicit antecedents — production-function-shape
  predicate (`IsCRS` / `IsCES` / `IsCobbDouglas`), `HasDerivAt`-bound
  marginal-product identification, positivity — to close the
  soundness gap caught by audit (recorded in attackHistory).  Without
  antecedents, all three axioms were False-injectable (counterexamples
  documented in the relevant axiom docstrings in `Axioms.lean`).

  Cat 3 paper-novel atomic-input atoms tracked in this ledger as
  standalone `GapEntry` records.  The genuine Cat 3 paper-novel
  atomic inputs of this formalization — the primitives the
  derivations build ON — are:
    * Carrier (`gapDefinitional`): the `Economy` primitive
      structure.
    * Hypothesis predicates (`gapDefinitional`): `IsCRS`,
      `IsCobbDouglas`, `IsCES`, `V2_TacitAccumulation`.
  These five are the standalone Cat 3 atoms.  In addition, one
  `cat3PaperNovel` `phenomenologicalConjecture` entry is tracked —
  the endogenous-AI-verification residual bound `δ(θ) < 1` of the
  adjustment-margins narrative — a genuine Cat 3 paper-novel claim
  under the `phenomenologicalConjecture` sub-type (a substantive
  empirical claim about the Polanyi verification residual with a
  cohort-study resolution path), `gapOpen` and Ledger-only.

  The concrete closed-form `def`s `eBar` (`\label{def:cohort}`),
  `Vinf` (`\label{lem:steady-state}`), `thetaStar`
  (`\label{eq:thetastar}`), and the further derived closed-form
  `def`s (`wageRatio`, `Gstar`, `thetaInv`, `Lambda`, `Vreq`, ...)
  are NOT standalone Cat 3 atoms — a concrete `def` whose defining
  equation holds by `rfl` is definitional notation, not a
  paper-novel atom (Cat 3 ratio guard).  `eBar` / `Vinf` /
  `thetaStar` are the paper's foundational closed-form `def`s
  directly on the Economy primitives; the rest are derived
  closed-form notation built on top.  All are definitional
  infrastructure documented under their parent theorem entries'
  `scope` and the "Definitional infrastructure" section below;
  none has a standalone Ledger `GapEntry`.

  The `gapOpen` deferred-paper-claim entries record paper-level
  claims whose faithful sound statement requires additional Mathlib
  infrastructure (path-dependent / measure-theoretic integrals,
  continuity / calculus across kinks) beyond this formalization's
  structural scope.  Each is tracked as a Ledger `GapEntry` record
  WITHOUT a corresponding Lean `axiom`/`def`/`theorem` declaration
  (see the "Ledger-only-entry exemption" section below).  Three are
  paper-proven mathematical results whose Lean derivation is
  deferred (window invariance, aggregation sequential kinks,
  aggregation intermediate regime) — these are un-formalized
  DERIVED results, not atomic inputs, so they are tagged `notInput`
  / `notCat3`; one is the `cat3PaperNovel` `phenomenologicalConjecture`
  noted above (the endogenous-AI-verification residual bound — a
  substantive empirical claim with an empirical resolution path).
  None is `gapBlocked` (Mathlib infra absence ALONE is NOT
  BLOCKED).

  ## §15.1.D encoding-exemption invocation (definitional atoms)

  Per spec §15.1.D, when keeping legacy `_OPEN`/`_DEFINITIONAL`
  encoding for definitional atoms would touch many downstream proof
  sites, an EXEMPTION pattern is acceptable: let the Ledger entry's
  `status := GapStatus.gapDefinitional` + `cat3SubType` field serve
  as the canonical record, with the exemption documented in the
  project's `Ledger.lean` top docstring.  (Spec §15.1.D explicitly
  mandates that this exemption be documented here in the top
  docstring.)  This project invokes the encoding exemption.

  The `gapDefinitional` Cat 3 paper-novel atoms — the `Economy`
  carrier and the hypothesisPredicates `IsCRS`, `IsCobbDouglas`,
  `IsCES`, `V2_TacitAccumulation` — are encoded as Lean `structure`
  or `Prop`, NOT as `axiom gap_X_DEFINITIONAL`.  Each such atom has
  a Ledger entry with `status := GapStatus.gapDefinitional` +
  `inputCategory := cat3PaperNovel` + `cat3SubType := <subtype>`;
  the Ledger entry is the canonical record.

  One further `gapOpen` Ledger-only entry — the by-construction
  μ-invariance commitment of `\label{thm:recursive}` Part 3
  (`gap_thm_recursive_invariance_OPEN`) — has NO Lean declaration:
  it records the ABSENCE of a μ parameter in the `thetaStar` /
  `VinfHard` carrier signatures.  This is a meta-observation about
  the formalization's shape, not a paper-stated structural equation
  that any derivation consumes as an atomic input, so it is tagged
  `inputCategory := notInput` + `cat3SubType := notCat3`.  The R10
  audit reclassified the status from `gapDefinitional` to `gapOpen`:
  spec §1.1 binds `gapDefinitional` to Cat 3 paper-novel atoms with
  sub-types {carrier, predicate, structuralEq}, and a `notInput
  notCat3` meta-observation falls outside that scope.  `gapOpen` is
  the consistent classification — the paper claim is satisfied by
  the Lean code's type-signature structure, but no Lean derivation
  is provided.

  The concrete closed-form `def`s `eBar` (`\label{def:cohort}`),
  `Vinf` (`\label{lem:steady-state}`), `thetaStar`
  (`\label{eq:thetastar}`), and the further derived closed-form
  `def`s (`wageRatio`, `Gstar`, `thetaInv`, `Lambda`, `Vreq`,
  `hPow`, `gSmooth`, `transientStock`, `MPpriv`, `MPsoc`,
  `externalityResidual`, `wedge`, `internalizedWedge`,
  `pigouvianSubsidy_CD`, `wageRatioRec`, `thetaInvRec`, `thetaEndo`,
  `hysteresisDeficit`, `recoveryStock`, `thetaStarExt`,
  `leontiefSeniorRent`, `rBarZero`, `rBarMax`) are NOT standalone
  Cat 3 atoms (Cat 3 ratio guard) — a concrete `def X :=
  <closed-form>` whose defining equation holds by `rfl` is
  definitional NOTATION, not a paper-novel ATOM.  `eBar` / `Vinf` /
  `thetaStar` are the paper's foundational closed-form `def`s
  directly on the Economy primitives (Section 2 model setup); the
  rest are derived closed-form notation built on top.  All are
  documented under the `scope` of the parent theorem entries that
  consume them; see the "Definitional infrastructure" section
  below.  None has a standalone Ledger `GapEntry`.

  ## Ledger-only-entry exemption (paper claims tracked without Lean declarations)

  Five paper claims are tracked as `gapOpen` Ledger `GapEntry`
  records WITHOUT a corresponding Lean `axiom`/`def`/`theorem`
  declaration.  They split into two semantically distinct groups:

  Group A — four claims with distinct deferred-resolution paths
  (each requiring a faithful sound statement beyond this
  formalization's structural scope):
  window invariance (`gap_window_invariance_OPEN`), sequential
  aggregation kinks (`gap_aggregation_sequential_kinks_OPEN`),
  intermediate-regime elasticity
  (`gap_aggregation_intermediate_regime_OPEN`) — three paper-proven
  mathematical claims whose Lean derivation requires out-of-scope
  Mathlib infrastructure (measure theory / continuity / kink
  analysis) — and the narrative endogenous-AI-verification residual
  bound (`gap_prop_adjustment_narrative_OPEN`) — a substantive
  phenomenological conjecture whose resolution path is empirical
  (cohort-study evidence per `\label{sec:predictions}`), NOT
  Mathlib derivation.

  Group B — one claim satisfied by construction: the μ-invariance
  commitment of `\label{thm:recursive}` Part 3
  (`gap_thm_recursive_invariance_OPEN`).  `thetaStar` / `VinfHard`
  are defined without a μ parameter; the paper claim is satisfied
  by the Lean code's type-signature structure, but no Lean theorem
  is or can be written (there is no μ-dependence to quantify over).

  Rationale.  A faithful sound STATEMENT of each requires Mathlib
  infrastructure (`MeasureTheory` integrals for window invariance;
  continuity / one-sided-limit / kink analysis for the aggregation
  claims) beyond this formalization's structural scope.  Encoding as
  `axiom` is unsound — the claim universally quantifies over a free
  abstract functional, which an `axiom` form leaves
  `False`-injectable.  Encoding as `def : Prop` with a constraining
  hypothesisPredicate that EQUALS the asserted conclusion is vacuous
  — the resulting proposition reduces to `∀ f, P f → P f`, a
  tautology provable by `fun _ h => h`.  The honest encoding is
  the Ledger `GapEntry` itself: it is a typed, `#eval`-retrievable
  declaration that tracks the gap, its status, its paper source, and
  the reason it is not Lean-derived.  This is consistent with spec
  §15's intent (the gap is labeled and tracked) even though it is
  not retrievable by `#print axioms` — nothing asserts or consumes
  it, which is correct, since asserting it would be unsound.  (The
  `axiom` → `def : Prop` → Ledger-only encoding history is recorded
  in each entry's `attackHistory`.)

  This exemption is parallel in spirit to the §15.1.D
  encoding-exemption (the Ledger entry is the canonical record),
  but stronger: §15.1.D keeps a Lean declaration (`structure` /
  `def` / `Prop`) for a definitional atom; here NO Lean declaration
  exists for a genuinely-open paper claim that cannot be faithfully
  stated within scope.

  ## InputCategory tagging convention

  A derived paper theorem (`gapClosed`) whose proof composes Mathlib
  lemmas, Cat 2 axioms, and Cat 3 definitional atoms is tagged
  `notInput`.  The Mathlib lemmas it invokes (e.g.
  `Real.rpow_le_rpow`, `Real.rpow_mul`, `Finset.prod_eq_zero`,
  `intermediate_value_Icc'`, `norm_num`) are NOT separately
  enumerated as atomic `cat1Mathlib` entries in this project, since
  this formalization's atomic input layer is dominated by Cat 2 +
  Cat 3.  This project therefore has ZERO `cat1Mathlib` entries:
  every Mathlib invocation is internal to a `notInput` derived
  theorem's proof.  The numerical-calibration corollary
  `cor_quant_predictions_calibration` and the threshold-reduction
  conjunct `prop_adjustment_threshold_reduction_floor` are derived
  `theorem`s, tagged `notInput gapClosed`. -/

import VerificationAsymmetry

namespace VerificationAsymmetry.Ledger

/-- 7-tier status tag attached to each gap.

    `gapClosedConditional` is used when Phase 4 catches a defect
    breaking a typed-bridge chain: the downstream closure is
    preserved as conditional on a named `Hyp_*` broken-link
    hypothesis (recorded in the entry's `conditionalOn` field)
    pending repair or independent derivation.

    `gapDefinitional` is used for Cat 3 paper-novel atoms that are
    paper-stipulative starting commitments (definitional content,
    never to close).  Covers the three definitional sub-types:
    `carrier`, `hypothesisPredicate`, `structuralEquation`.
    Distinguished from `gapOpen` (no attack or inconclusive
    attempts): `gapDefinitional` says "by design axiomatic, no Lean
    derivation expected". -/
inductive GapStatus
  | gapOpen
  | gapPartial
  | gapBlocked
  | gapDeadEnd
  | gapClosed
  | gapClosedConditional
  | gapDefinitional
  deriving DecidableEq, Repr

/-- 4-input-category tag attached to each gap.  Orthogonal to status.
    (Cat 0 = Lean kernel axioms — `propext` / `Classical.choice` /
    `Quot.sound` — is the always-present system layer and is not
    tracked here.) -/
inductive InputCategory
  /-- Mathlib-derivable theorem (no axiom).  Project has zero such. -/
  | cat1Mathlib
  /-- External published; opaque-carrier-bound axiom + citation. -/
  | cat2External
  /-- Paper-novel: carrier, hypothesis predicate, structural defining
      equation, working assumption, or conditional hypothesis.
      Refine via the `cat3SubType` field. -/
  | cat3PaperNovel
  /-- Not an atomic input: derived theorem (gapClosed) or genuine
      no-acceptance-possible route (gapBlocked / gapDeadEnd). -/
  | notInput
  deriving DecidableEq, Repr

/-- Cat 3 paper-novel sub-types.  Orthogonal to status and
    input-category; only meaningful when `inputCategory = cat3PaperNovel`. -/
inductive Cat3SubType
  /-- Paper-introduced primitive type or typed-primitive value
      (e.g., paper 5-tuple carriers).  Definitional atom; 永不 close. -/
  | carrier
  /-- Paper-introduced scope/regime predicate (e.g., `Conditions_C1_C2_C3`,
      `IsBlackwellOrdered`).  Definitional atom; 永不 close. -/
  | hypothesisPredicate
  /-- Paper-stated definitional equation on its primitives (e.g., paper
      Def 2.6 `V_dyn(v|H,ω) = max{r(w) : w ∈ R(v|H,ω)}`).  Definitional
      atom; 永不 close — these constitute the paper's commitments to
      how its primitives behave. -/
  | structuralEquation
  /-- Higher-level claim temporarily axiomatized while derivation is
      developed.  必须 close before paper submission. -/
  | workingAssumption
  /-- Paper's conclusion conditional on an external open problem (RH,
      BSD, Hodge, P≠NP).  Listed here for completeness; these should
      NEVER be a Cat 3 axiom but theorem-signature antecedents
      `theorem T (hRH : RiemannHypothesis) : ...`.  Project has
      none. -/
  | conditionalHypothesis
  /-- Framework paper's PUBLISHED substantive claim about a
      phenomenon, awaiting EXTERNAL VALIDATION (empirical study,
      cohort data, philosophical-foundations debate).  Never
      Lean-closeable; resolution path = battery / cohort study /
      interpretive debate, not derivation. -/
  | phenomenologicalConjecture
  /-- This entry is not Cat 3 paper-novel. -/
  | notCat3
  deriving DecidableEq, Repr

/-- Typed record for a single gap. -/
structure GapEntry where
  /-- Identifier matching the underlying axiom / theorem name. -/
  name : String
  /-- 7-tier status. -/
  status : GapStatus
  /-- Input category (orthogonal to status). -/
  inputCategory : InputCategory
  /-- Cat 3 sub-type (orthogonal; `notCat3` unless `inputCategory =
      cat3PaperNovel`). -/
  cat3SubType : Cat3SubType
  /-- Operative paper / obstacle citation. -/
  paperSource : String
  /-- Per-round attack trace (canonical location for round metadata).
      For Cat 3 entries, MUST include ≥2 reductionism check outcomes
      (Cat 1? Cat 2?). -/
  attackHistory : List String
  /-- What content the entry carries; what it does NOT claim. -/
  scope : String
  /-- Names of `Hyp_*` broken-link predicates this entry's proof
      depends on.  Invariant: non-empty iff `status =
      gapClosedConditional`. -/
  conditionalOn : List String := []
  /-- Optional auxiliary notes (downstream-consumer list, or other
      metadata that doesn't fit `scope` or `attackHistory`). -/
  notes : String := ""

/-! ### Cat 2 axiom entries (gapOpen: accepted on external authority,
    declared in `Axioms.lean`).

  Opaque Cat 2 axioms with external-authority citation are `gapOpen`
  (Mathlib derivation possible but not undertaken; the paper's claim
  follows from external published authority).  Each axiom carries
  explicit antecedents threaded through the consumer-theorem
  signatures. -/

/-- Cat 2 axiom: Euler's identity for CRS production. -/
def gap_axiom_euler_crs : GapEntry := {
  name := "axiom_euler_crs"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat2External
  cat3SubType := Cat3SubType.notCat3
  paperSource :=
    "Li 2026, `\\label{thm:decomp}` proof; " ++
    "original source: Euler, L., 1755.  *Institutiones Calculi " ++
    "Differentialis* (original homogeneous-function theorem); " ++
    "modern textbook reference: Mas-Colell, A., Whinston, M.D., " ++
    "Green, J.R., 1995.  *Microeconomic Theory*, §5.B.2 Theorem " ++
    "M.B.2 (Euler's theorem for CRS technologies)"
  attackHistory := [
    "Pre-audit (v0.1.0): Euler identity carried as hypothesis " ++
    "`hEuler` of `thm_decomp`; proof body `rfl`.",
    "Audit (2026-05-14) Phase 4: SOUNDNESS DEFECT — " ++
    "axiom universally quantified over (F, G, V, wG, wV) with no " ++
    "antecedents, False-injectable (counterexample `F := const 1, " ++
    "G = V = wG = wV = 0` ⊢ `1 = 0`). Patched: axiom now requires " ++
    "`IsCRS F`, `HasDerivAt`-bound `wG, wV`, positivity of `G, V`.",
    "Phase 4 consumer verification (R2 2026-05-14): " ++
    "`#print axioms thm_decomp` confirms `axiom_euler_crs` IS in " ++
    "the dependency chain — genuine Lean-proof-load-bearing axiom."
  ]
  scope :=
    "For any homogeneous-of-degree-one (`IsCRS`) `F : ℝ → ℝ → ℝ` " ++
    "evaluated at `(G, V)` with `wG = ∂F/∂G`, `wV = ∂F/∂V` " ++
    "(`HasDerivAt`-bound), and `0 < G, 0 < V`: " ++
    "`F G V = wG · G + wV · V`. Atomic single-equation identity."
  notes :=
    "Lean-proof-load-bearing: consumed by `thm_decomp` (Decomp.lean), " ++
    "verifiable by `#print axioms thm_decomp`."
}

/-- Cat 2 axiom: CES wage-ratio closed form. -/
def gap_axiom_ces_wage_ratio : GapEntry := {
  name := "axiom_ces_wage_ratio"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat2External
  cat3SubType := Cat3SubType.notCat3
  paperSource :=
    "Li 2026, `\\label{thm:inversion}` Part 1, " ++
    "Eq. `\\eqref{eq:wage-ratio}`; " ++
    "original source: Arrow, K.J., Chenery, H.B., Minhas, B.S., " ++
    "Solow, R.M., 1961.  Capital-Labor Substitution and Economic " ++
    "Efficiency.  *Review of Economics and Statistics* 43(3), " ++
    "225-250 (original CES paper introducing the production " ++
    "function); modern textbook reference: Acemoglu, D., 2009.  " ++
    "*Introduction to Modern Economic Growth*, Chapter 15 (CES " ++
    "production factor-price equations)"
  attackHistory := [
    "Pre-audit (v0.1.0): `wageRatio` defined as closed form; " ++
    "no axiom recorded for the identification with CES marginal " ++
    "products.",
    "Audit (2026-05-14) Phase 4: SOUNDNESS DEFECT — " ++
    "axiom universally quantified over `(eta, rho, lam, G, V, " ++
    "wV_over_wG)` with no CES-shape antecedent and no marginal-" ++
    "product identification; False-injectable. Patched: axiom now " ++
    "requires `IsCES F eta rho lam`, `HasDerivAt`-bound `wG, wV`, " ++
    "positivity of `wG, G, V, eta, lam`, shape constraints " ++
    "`0 < eta < 1`, `rho < 1`, `rho ≠ 0`.",
    "Phase 4 paper-source verification: VERIFIED — " ++
    "Lean statement matches paper Eq.~`\\eqref{eq:wage-ratio}` " ++
    "exactly under the stated antecedents.",
    "R2 (2026-05-14) Phase 4: invoked the spec §1.6 boundary " ++
    "clause, treating the axiom as a paper-narrative reference " ++
    "(not Lean-proof-load-bearing), and at some point the `axiom " ++
    "axiom_ces_wage_ratio` declaration was removed from Axioms.lean " ++
    "while the Ledger entry + AxiomAudit `#print axioms` line were " ++
    "left dangling.",
    "R3 audit: §1.6 boundary clause MIS-INVOCATION corrected.  " ++
    "The §1.6 boundary clause is for paper-narrative-load-bearing " ++
    "classical-philosophy / statistical-convention citations " ++
    "(Honneth, Brandom, Hegel, Fisher 2002, Hu-Bentler 1999, " ++
    "Cohen 1988).  The CES marginal-product wage ratio is " ++
    "SUBSTANTIVE production-function calculus, NOT such a citation " ++
    "— it does not qualify.  R3 RESTORED the `axiom " ++
    "axiom_ces_wage_ratio` declaration in Axioms.lean (with " ++
    "explicit `IsCES` / `HasDerivAt` / positivity / shape " ++
    "antecedents) AND added the consuming theorem " ++
    "`wageRatio_eq_ces_marginal_product_ratio` (Inversion.lean) " ++
    "that establishes the Lean `wageRatio` closed-form def IS the " ++
    "CES marginal-product wage ratio `w_V / w_G` for a generic " ++
    "CES `F` — making the axiom genuinely Lean-load-bearing.  " ++
    "Verifiable by `#print axioms " ++
    "wageRatio_eq_ces_marginal_product_ratio`, which surfaces " ++
    "`axiom_ces_wage_ratio` in the dependency chain."
  ]
  scope :=
    "Under CES production with explicit shape (`IsCES`) and " ++
    "competitive marginal products (`HasDerivAt`-bound), " ++
    "`wV / wG = ((1-η)/η) · λ^ρ · (G/V)^(1-ρ)`. Atomic single-" ++
    "equation closed form."
  notes :=
    "Lean-proof-load-bearing: consumed by " ++
    "`wageRatio_eq_ces_marginal_product_ratio` (Inversion.lean), " ++
    "which identifies the closed-form `wageRatio` def with the " ++
    "CES marginal-product wage ratio for a generic CES `F`.  " ++
    "Verifiable by `#print axioms " ++
    "wageRatio_eq_ces_marginal_product_ratio`."
}

/-- Cat 2 axiom: Cobb-Douglas verification factor share. -/
def gap_axiom_cobb_douglas_factor_share : GapEntry := {
  name := "axiom_cobb_douglas_factor_share"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat2External
  cat3SubType := Cat3SubType.notCat3
  paperSource :=
    "Li 2026, `\\label{thm:credential}` proof " ++
    "(`\\eqref{eq:R-cobb-douglas}`); " ++
    "original source: Cobb, C.W., Douglas, P.H., 1928.  A Theory of " ++
    "Production.  *American Economic Review* 18(1), 139-165 " ++
    "(original Cobb-Douglas production function paper); " ++
    "modern textbook reference: Mas-Colell, A., Whinston, M.D., " ++
    "Green, J.R., 1995.  *Microeconomic Theory*, §5.B.2 Theorem " ++
    "M.B.2 (Cobb-Douglas constant factor shares)"
  attackHistory := [
    "Pre-audit (v0.1.0): composite identity " ++
    "`(1-η) Y = w_V · (ν T_s g h)` carried as hypothesis of every " ++
    "Cobb-Douglas-regime theorem; proof bodies `field_simp`.",
    "Audit (2026-05-14) Phase 4: SOUNDNESS DEFECT — " ++
    "axiom `∀ η Y wV V, wV * V = (1-η) * Y` universally " ++
    "quantified over `(η, Y, wV, V)` with NO Cobb-Douglas shape " ++
    "antecedent; False-injectable (counterexample `η = 0, Y = 0, " ++
    "wV = 1, V = 1` ⊢ `1 = 0`). Patched: axiom now requires " ++
    "`IsCobbDouglas F η lam`, `HasDerivAt`-bound `wV`, bridge " ++
    "`Y = F G V`, positivity of `G, V, η, lam`, shape " ++
    "`0 < η < 1`.",
    "Phase 4 consumer verification (R2 2026-05-14): added " ++
    "`cobb_douglas_steady_state_identity_from_axiom` bridge in " ++
    "Axioms.lean that genuinely consumes this axiom; updated " ++
    "downstream `_from_axioms` theorems to thread the axiom's " ++
    "antecedents through.  `#print axioms` on " ++
    "`thm_credential_cobb_douglas_reduction_from_axioms`, " ++
    "`prop_junior_senior_wage_from_axioms`, and " ++
    "`thm_externality_pigouvian_cobb_douglas_from_axioms` confirms " ++
    "this axiom IS in their dependency chains — genuine Lean-proof-" ++
    "load-bearing."
  ]
  scope :=
    "Under Cobb-Douglas `F(G, V) = G^η · (λ V)^(1-η)` " ++
    "(`IsCobbDouglas`) with `wV = ∂F/∂V` (`HasDerivAt`-bound), " ++
    "`Y = F G V` definitional bridge, `0 < G, V, η, lam`, " ++
    "`η < 1`: `wV · V = (1 - η) · Y`. Atomic single-equation " ++
    "factor-share identity.  Bridge theorems composing this axiom " ++
    "with `steady_state_stock_identity`: " ++
    "`cobb_douglas_steady_state_identity` (parametric form, takes " ++
    "the factor-share bridge as a hypothesis) and " ++
    "`cobb_douglas_steady_state_identity_from_axiom` (axiom-" ++
    "discharged form, derives the bridge from this axiom) — both " ++
    "in Axioms.lean, both derived `notInput` bridge theorems " ++
    "tracked under this entry's scope."
  notes :=
    "Lean-proof-load-bearing: consumed (via " ++
    "`cobb_douglas_steady_state_identity_from_axiom` bridge) by " ++
    "`thm_credential_cobb_douglas_reduction_from_axioms`, " ++
    "`prop_junior_senior_wage_from_axioms`, and " ++
    "`thm_externality_pigouvian_cobb_douglas_from_axioms`.  " ++
    "Verifiable by `#print axioms` on each."
}

/-! ### gapClosed entries — paper-level results formalized without `sorry` -/

/-- Theorem~\ref{thm:decomp} (stock-flow welfare decomposition,
    Euler-identity portion). -/
def gap_thm_decomp_CLOSED : GapEntry := {
  name := "thm_decomp"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:decomp}`"
  attackHistory := [
    "Pre-audit (v0.1.0): Euler identity carried as hypothesis " ++
    "`hEuler : F G V = wG · G + wV · V`; proof body `rfl`. " ++
    "Audit (2026-05) replaced the hypothesis with an application " ++
    "of `axiom_euler_crs` (Cat 2, Euler 1755 / MWG 1995 §5.B.2); " ++
    "the proof body is now " ++
    "`axiom_euler_crs F G V wG wV hCRS h_wG h_wV hG_pos hV_pos`.",
    "Phase 4 paper-source verification: VERIFIED — " ++
    "Lean statement matches paper `\\label{thm:decomp}` Eq. " ++
    "`\\eqref{eq:decomp}`. R1 audit threaded the new explicit " ++
    "axiom antecedents (`IsCRS`, `HasDerivAt`-bound `wG, wV`, " ++
    "positivity of `G, V`) into the theorem signature.",
    "R2 (2026-05-14) Phase 4 consumer verification: " ++
    "`#print axioms thm_decomp` confirms `axiom_euler_crs` IS in " ++
    "the dependency chain — genuine Cat 2 consumption."
  ]
  scope :=
    "Derived theorem (`notInput`) composing Cat 2 axiom + Cat 3 " ++
    "hypothesisPredicate.  Stock-flow welfare decomposition by " ++
    "Euler's identity: for any CRS `F` with `HasDerivAt`-bound " ++
    "marginal-product wages `w_G, w_V`, " ++
    "`F G V = w_G · G + w_V · V` (by `axiom_euler_crs`), implying " ++
    "`F = Wflow + Wstock` where `Wflow = wG · G`, `Wstock = wV · V`."
  notes :=
    "Cat 2 dependency: `axiom_euler_crs` (Euler 1755 / MWG 1995 " ++
    "§5.B.2 Theorem). Cat 3 hypothesisPredicate dependency: `IsCRS`. " ++
    "Verifiable by `#print axioms thm_decomp`."
}

/-- Theorem~\ref{thm:inversion} Part 2: closed-form inversion threshold
    (bundle covering closed-form + range theorems). -/
def gap_thm_inversion_threshold_CLOSED : GapEntry := {
  name := "thm_inversion_threshold (Part 2 bundle)"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:inversion}` Part 2"
  attackHistory := [
    "Phase 4 paper-verification: " ++
    "VERIFIED — Lean statement `G(θ_inv) = G*(r̄)` matches paper " ++
    "Eq. `\\eqref{eq:theta-inv}`. Proof closure via `field_simp; " ++
    "ring` (Mathlib algebraic manipulation)."
  ]
  scope :=
    "Bundle entry covering two theorems: " ++
    "`thm_inversion_threshold_closed_form` (the closed-form claim " ++
    "`G(θ_inv(r̄)) = G*(r̄)`) and `thm_inversion_threshold_in_unit_interval` " ++
    "(the range claim `0 < θ_inv(r̄) < 1` under `L_G < G* < K_AI`).  " ++
    "Both closed by `field_simp; ring` / `div_pos` / `div_lt_one` " ++
    "from definitions of `G` and `thetaInv`.  Companion: " ++
    "`thm_inversion_threshold_monotone_in_rBar` (the Parts 2 " ++
    "monotonicity claim) lives in `gap_thm_inversion_threshold_monotone_CLOSED`.  " ++
    "Paper Parts 3 (factor share) + 4 (Leontief output bound) are " ++
    "not separately formalized; tracked in scope of the parent " ++
    "`thm:inversion` paper-theorem."
  notes :=
    "Paper `thm:inversion` Parts 3 (CES factor-share decomposition) " ++
    "and 4 (Leontief output bound) are silently omitted from the " ++
    "Lean formalization: Part 3 is the algebraic CES factor-share " ++
    "decomposition which falls under the Cat 2 marginal-product " ++
    "calculus suppressed via `axiom_ces_wage_ratio`; Part 4 is the " ++
    "Leontief asymptotic regime where output is bounded by `λV` " ++
    "for `θ > θ_inv`.  Both are economic-narrative content rather " ++
    "than substantive new algebraic identities."
}

/-- Theorem~\ref{thm:inversion} Part 2 monotonicity in r̄. -/
def gap_thm_inversion_threshold_monotone_CLOSED : GapEntry := {
  name := "thm_inversion_threshold_monotone_in_rBar"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:inversion}` Part 2 " ++
    "(monotonicity in r̄)"
  attackHistory := [
    "Phase 4 paper-verification: VERIFIED — Lean " ++
    "monotonicity of `thetaInv` in `r̄` (parametric in `Gstar` " ++
    "non-decreasingness) matches paper Part 2."
  ]
  scope :=
    "`thetaInv V rBar` is non-decreasing in `rBar` (parametric in " ++
    "the `Gstar`-monotonicity hypothesis).  Algebraic monotonicity " ++
    "of `r̄ ↦ r̄^{1/(1-ρ)}` for `1/(1-ρ) > 0` underlies the " ++
    "`Gstar`-monotonicity hypothesis; this entry covers the lifted " ++
    "monotonicity from `Gstar` to `thetaInv` via division."
  notes :=
    "Parametric bridge — `thm_inversion_threshold_monotone_in_rBar` " ++
    "takes `Gstar` monotonicity in `r̄` (`Gstar V rBar₁ ≤ Gstar V " ++
    "rBar₂`) as a bare hypothesis; the `Gstar`-monotonicity itself " ++
    "is the algebraic monotonicity of `r̄ ↦ r̄^{1/(1-ρ)}` for " ++
    "`1/(1-ρ) > 0` (paper `\\label{thm:inversion}` Part 2, " ++
    "`ρ < 1`).  The Lean encoding chains this dependency " ++
    "conceptually; the bridge theorem proves the lifted " ++
    "`thetaInv` monotonicity (via division by `K_AI - L_G > 0`) " ++
    "GIVEN the `Gstar`-monotonicity, parametrizing over it rather " ++
    "than re-deriving the `r̄^{1/(1-ρ)}` algebra inline."
}

/-- Theorem~\ref{thm:inversion} Part 1: wage-ratio monotonicity. -/
def gap_thm_inversion_wage_ratio_CLOSED : GapEntry := {
  name := "thm_inversion_wage_ratio_monotone"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:inversion}` Part 1, " ++
    "Eq. `\\eqref{eq:wage-ratio}` monotonicity claim"
  attackHistory := [
    "Pre-audit (v0.1.0): `wageRatio` defined as the closed form " ++
    "`((1-η)/η) λ^ρ (G/V)^{1-ρ}`; identification with the CES " ++
    "marginal-product ratio implicit. Audit (2026-05) added " ++
    "`axiom_ces_wage_ratio` for honest accounting of the suppressed " ++
    "CES marginal-product derivation.",
    "Phase 4 paper-verification: " ++
    "VERIFIED — `Real.rpow_le_rpow` chain + `G_monotone_of_KAI_ge_LG` " ++
    "match paper `\\label{thm:inversion}` Part 1 monotonicity claim."
  ]
  scope :=
    "Wage-ratio function `r(θ) = ((1-η)/η) λ^ρ (G(θ)/V)^(1-ρ)` is " ++
    "non-decreasing in `θ` under `K_AI ≥ L_G` and `ρ < 1`. Proof " ++
    "uses `Real.rpow_le_rpow` on `G(θ)/V` together with the " ++
    "monotonicity of `G` (`Economy.G_monotone_of_KAI_ge_LG`)."
  notes :=
    "**Scope precision:** paper abstract / introduction use " ++
    "'monotonically rising'/'monotonically increasing' for the " ++
    "wage ratio; the paper's PROOF body around " ++
    "`\\label{thm:inversion}` Part 1 uses 'non-decreasing' (`G(θ)` " ++
    "is non-decreasing in `θ` assuming `K_AI ≥ L_G`, the relevant " ++
    "case).  Lean follows the proof body (`non-decreasing`).  " ++
    "Strict monotonicity requires `K_AI > L_G` (strict).\n\n" ++
    "**axiom_ces_wage_ratio relationship:** the substantive " ++
    "monotonicity claim is proved here from the closed-form " ++
    "`wageRatio` def via `Real.rpow_le_rpow` (Mathlib) on " ++
    "`(G/V)^(1-ρ)`, and does not itself invoke " ++
    "`axiom_ces_wage_ratio`.  The Cat 2 axiom enters Part 1 " ++
    "through the SEPARATE closed-form-identification theorem " ++
    "`wageRatio_eq_ces_marginal_product_ratio` " ++
    "(`gap_wageRatio_eq_ces_marginal_product_ratio_CLOSED`), which " ++
    "establishes that the `wageRatio` def IS the CES marginal-" ++
    "product wage ratio.  Monotonicity-of-the-closed-form and " ++
    "closed-form-equals-CES-ratio are two distinct sub-results of " ++
    "paper Part 1; the axiom is load-bearing for the latter."
}

/-- Theorem~\ref{thm:inversion} Part 1: the closed-form `wageRatio`
    def IS the CES marginal-product wage ratio. -/
def gap_wageRatio_eq_ces_marginal_product_ratio_CLOSED : GapEntry := {
  name := "wageRatio_eq_ces_marginal_product_ratio"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:inversion}` Part 1, " ++
    "Eq. `\\eqref{eq:wage-ratio}` (closed-form identification with " ++
    "the CES marginal-product wage ratio)"
  attackHistory := [
    "R3 audit: added.  The §1.6 boundary-clause mis-invocation on " ++
    "`axiom_ces_wage_ratio` (R2) left the axiom non-load-bearing " ++
    "and ultimately removed from Axioms.lean.  R3 restored the " ++
    "axiom and added this consuming theorem: it composes " ++
    "`axiom_ces_wage_ratio` (Cat 2) to establish that the Lean " ++
    "closed-form `wageRatio` def equals the CES marginal-product " ++
    "wage ratio `w_V / w_G` for a generic CES `F` with " ++
    "competitive marginal-product wages.  This is the honest " ++
    "Lean encoding of the paper's Eq. `\\eqref{eq:wage-ratio}` " ++
    "closed-form-identification claim.",
    "Phase 4 consumer verification: `#print axioms " ++
    "wageRatio_eq_ces_marginal_product_ratio` confirms " ++
    "`axiom_ces_wage_ratio` IS in the dependency chain — genuine " ++
    "Cat 2 consumption."
  ]
  scope :=
    "Derived theorem (`notInput`) composing the Cat 2 axiom " ++
    "`axiom_ces_wage_ratio`.  For a generic CES production " ++
    "function `F` with competitive marginal-product wages " ++
    "`w_G = ∂F/∂G`, `w_V = ∂F/∂V`, the wage ratio `w_V / w_G` " ++
    "equals the closed form `((1-η)/η) · λ^ρ · (G/V)^(1-ρ)` for " ++
    "arbitrary positive `G`.  Identification with the `wageRatio` " ++
    "def follows by specializing `G := E.G θ`: the RHS is then " ++
    "exactly the body of `E.wageRatio V θ`, so `E.wageRatio V θ = " ++
    "w_V / w_G` holds by `rfl` after the specialization.  This " ++
    "theorem does NOT perform the specialization itself; consumers " ++
    "supply `G := E.G θ` to recover the def-identification.  " ++
    "`ρ < 1` is taken as an explicit hypothesis (the Economy " ++
    "carrier only stipulates `ρ ≤ 1`)."
  notes :=
    "Cat 2 dependency: `axiom_ces_wage_ratio` (ACMS 1961 / " ++
    "Acemoglu 2009 §15).  Verifiable by `#print axioms " ++
    "wageRatio_eq_ces_marginal_product_ratio`."
}

/-- Corollary~\ref{cor:bounded-AI} (endpoint identifications;
    bundle covering four theorems). -/
def gap_cor_bounded_AI_CLOSED : GapEntry := {
  name := "cor_bounded_AI_threshold_endpoints (bundle)"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{cor:bounded-AI}`"
  attackHistory := [
    "Pre-audit (v0.1.0): endpoint identities `G*(r̄_0) = L_G`, " ++
    "`G*(r̄_max) = K_AI` carried as `hGstar_eq` hypotheses. Audit " ++
    "(2026-05) derived them inline via `Real.rpow_mul`.",
    "Phase 4 paper-verification: VERIFIED — Lean " ++
    "endpoint statements match `\\label{cor:bounded-AI}` r̄ → 0 / " ++
    "r̄ → r̄_max identifications.  Closure via `Real.rpow_mul`."
  ]
  scope :=
    "Bundle entry covering four theorems: `Gstar_at_rBarZero`, " ++
    "`Gstar_at_rBarMax`, `cor_bounded_AI_threshold_at_rBarZero`, " ++
    "`cor_bounded_AI_threshold_at_rBarMax`.  At `r̄ = r̄_0`, " ++
    "`G*(r̄_0) = L_G`, so `θ_inv = 0`; at `r̄ = r̄_max`, " ++
    "`G*(r̄_max) = K_AI`, so `θ_inv = 1`. Both endpoint identities " ++
    "derived from `Real.rpow_mul` and the cancellation " ++
    "`(x^a)^(1/a) = x` for `x > 0, a ≠ 0`."
}

/-- Theorem~\ref{thm:collapse} Part 1: below-threshold smooth power-law. -/
def gap_thm_collapse_below_CLOSED : GapEntry := {
  name := "thm_collapse_below_threshold"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:collapse}` Part 1"
  attackHistory := [
    "Phase 4 paper-verification: " ++
    "VERIFIED — Lean statement `V_∞(θ) = ν T_s ((1-θ) T_j)^a` for " ++
    "`θ ≤ θ*` matches paper `\\label{thm:collapse}` Part 1."
  ]
  scope :=
    "For `θ ≤ θ*`, `V_∞(θ) = ν T_s · ((1-θ) T_j)^a` under hard " ++
    "threshold. Reduces to `VinfHard_eq_pow_of_eBar_ge_tauStar` " ++
    "via the bridge `eBar_ge_tauStar_iff_theta_le_thetaStar`."
}

/-- Theorem~\ref{thm:collapse} Part 2: jump magnitude. -/
def gap_thm_collapse_jump_CLOSED : GapEntry := {
  name := "thm_collapse_jump_magnitude"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:collapse}` Part 2"
  attackHistory := [
    "Phase 4 paper-verification: VERIFIED — " ++
    "Lean jump magnitude `ν T_s (τ*)^a` matches paper Part 2."
  ]
  scope :=
    "`V_∞(θ*) = ν T_s · (τ*)^a` (left limit); right limit is 0. " ++
    "Jump magnitude `ν T_s (τ*)^a` is exact.  Companion theorem " ++
    "`thm_collapse_jump_diff` (discrete-difference form) is covered " ++
    "by `gap_thm_collapse_jump_diff_CLOSED`.  Continuous one-sided-" ++
    "limit machinery deferred (not required to state the discrete " ++
    "jump value)."
}

/-- Theorem~\ref{thm:collapse} Part 2 discrete-difference companion. -/
def gap_thm_collapse_jump_diff_CLOSED : GapEntry := {
  name := "thm_collapse_jump_diff"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:collapse}` Part 2 " ++
    "(discrete-difference form)"
  attackHistory := [
    "Phase 4 paper-verification: VERIFIED — " ++
    "for any `θ_above > θ*`, `V_∞(θ*) - V_∞(θ_above) = ν T_s (τ*)^a`."
  ]
  scope :=
    "Discrete-difference form of paper Part 2 jump claim: " ++
    "`V_∞(θ*) - V_∞(θ_above) = ν T_s (τ*)^a` for any `θ_above > θ*`. " ++
    "Reduces to combining `thm_collapse_above_threshold` (uniform " ++
    "vanishing above `θ*`) with `thm_collapse_jump_magnitude` " ++
    "(left-limit value).  Continuous right-limit machinery not " ++
    "required."
}

/-- Theorem~\ref{thm:collapse} Part 3: long-run zero stock above θ*. -/
def gap_thm_collapse_above_CLOSED : GapEntry := {
  name := "thm_collapse_above_threshold"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:collapse}` Part 3"
  attackHistory := [
    "Phase 4 paper-verification: VERIFIED — " ++
    "`V_∞(θ) = 0` for `θ > θ*` matches paper Part 3."
  ]
  scope :=
    "For `θ > θ*`, `V_∞(θ) = 0`. Reduces to " ++
    "`VinfHard_eq_zero_of_eBar_lt_tauStar`."
}

/-- Theorem~\ref{thm:collapse} Part 4: transient linear decay
    (bundle covering four pointwise theorems). -/
def gap_thm_collapse_transient_CLOSED : GapEntry := {
  name := "thm_collapse_transient_decay (bundle)"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:collapse}` Part 4, " ++
    "Eq. `\\eqref{eq:transient}`"
  attackHistory := [
    "Phase 4 paper-verification: VERIFIED — four " ++
    "pointwise lemmas (`_at_zero`, `_at_Ts`, `_linear`, " ++
    "`_zero_after_Ts`) capture the paper's piecewise-linear decay."
  ]
  scope :=
    "Bundle entry covering four pointwise theorems: " ++
    "`thm_collapse_transient_at_zero`, `thm_collapse_transient_at_Ts`, " ++
    "`thm_collapse_transient_linear`, `thm_collapse_transient_zero_after_Ts`. " ++
    "Each is a `gapClosed`-via-`notInput` derived theorem.  Transient " ++
    "stock `V(t) = V_∞(θ_0) · (1 - t/T_s)_+` formalized via " ++
    "`transientStock` def."
}

/-- Theorem~\ref{thm:collapse} Part 5: general-`h` value at θ*. -/
def gap_thm_collapse_general_h_CLOSED : GapEntry := {
  name := "thm_collapse_value_at_thetaStar_general_h"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:collapse}` Part 5"
  attackHistory := [
    "Phase 4 paper-verification: VERIFIED — " ++
    "Lean value `V_∞(θ*) = ν T_s h(τ*)` matches paper Part 5 value-at-θ*.",
    "R2 (2026-05-14) renamed from `thm_collapse_jump_general_h` to " ++
    "`thm_collapse_value_at_thetaStar_general_h` for honesty: the " ++
    "theorem captures the value at `θ*` (not the jump magnitude per " ++
    "se).  The jump magnitude follows by combining with " ++
    "`thm_collapse_above_threshold` (uniform vanishing above `θ*`); " ++
    "for monotone `h` with `h(τ*) > 0`, the jump is strictly positive. " ++
    "Removed unused positivity hypothesis."
  ]
  scope :=
    "For ANY function `h : ℝ → ℝ`, the steady-state stock at " ++
    "`θ*` equals exactly `ν T_s h(τ*)`.  Algebraic identity once " ++
    "`ē(θ*) = τ*` is substituted.  Paper Part 5's lower-bound claim " ++
    "(jump ≥ ν T_s h(τ*) for monotone h with h(τ*) > 0) follows " ++
    "from this value combined with the uniform vanishing above `θ*`."
}

/-- Proposition~\ref{prop:smooth-collapse}: smooth-threshold collapse
    bundle (above + below). -/
def gap_prop_smooth_collapse_CLOSED : GapEntry := {
  name := "prop_smooth_collapse (bundle)"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{prop:smooth-collapse}`"
  attackHistory := [
    "Phase 4 paper-verification: VERIFIED — " ++
    "Lean smooth-threshold statements match paper."
  ]
  scope :=
    "Bundle entry covering two theorems: " ++
    "`prop_smooth_collapse_below` (below `θ*`, matches hard-threshold " ++
    "value `ν T_s ē^a`) and `prop_smooth_collapse_above` (above " ++
    "`θ*`, `V_∞(θ) = ν T_s · (ē/τ*)^b · ē^a` with `(1-θ)^{a+b}` " ++
    "decay rate)."
}

/-- Theorem~\ref{thm:credential} (Cobb-Douglas reduction + closed
    form bundle). -/
def gap_thm_credential_CLOSED : GapEntry := {
  name := "thm_credential (bundle)"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:credential}`, " ++
    "Eq. `\\eqref{eq:R-senior-rent}`"
  attackHistory := [
    "Pre-audit (v0.1.0): composite Cobb-Douglas identity " ++
    "`(1-η) Y = wV · (ν T_s g h)` carried as hypothesis `hY`. " ++
    "Audit (2026-05) added a companion `_from_axioms` theorem that " ++
    "derives `hY` from `axiom_cobb_douglas_factor_share` (Cat 2) " ++
    "composed with the definitional steady-state stock identity.",
    "Phase 4 paper-verification: VERIFIED — Lean " ++
    "reduction `T_s g h wV = (1-η) Y / ν` matches paper " ++
    "Eq. `\\eqref{eq:R-senior-rent}`.",
    "R2 (2026-05-14) Phase 4 phantom-downstream audit: previously " ++
    "the `_from_axioms` companion took `hCDshare` as a free " ++
    "hypothesis and routed through " ++
    "`cobb_douglas_steady_state_identity` (which also took " ++
    "`hCDshare`), so `axiom_cobb_douglas_factor_share` was NOT " ++
    "actually consumed.  Patched: added " ++
    "`cobb_douglas_steady_state_identity_from_axiom` bridge that " ++
    "genuinely derives `hCDshare` from the Cat 2 axiom; updated " ++
    "`_from_axioms` to thread axiom antecedents.  `#print axioms " ++
    "thm_credential_cobb_douglas_reduction_from_axioms` now surfaces " ++
    "`axiom_cobb_douglas_factor_share` in the dependency chain."
  ]
  scope :=
    "Bundle entry covering two theorems plus the axiom-discharged " ++
    "companion: `thm_credential_cobb_douglas_reduction` (parametric " ++
    "form with `hY` hypothesis), " ++
    "`thm_credential_cobb_douglas_reduction_from_axioms` " ++
    "(axiom-discharged form via `axiom_cobb_douglas_factor_share`), " ++
    "and `thm_credential_closed_form` (substitution into the per-" ++
    "entrant return).  Under Cobb-Douglas factor share " ++
    "`(1-η) Y = wV · ν T_s · g · h` and `g · h > 0`, the per-" ++
    "entrant senior earnings `T_s · g · h · wV` simplify to " ++
    "`(1-η) Y / ν`. The closed-form return per entrant is " ++
    "`R(θ) = (1-η) Y(θ)/ν - T_j · c_J(θ)`."
  notes :=
    "Cat 2 dependency (via `_from_axioms` form): " ++
    "`axiom_cobb_douglas_factor_share`. Verifiable by " ++
    "`#print axioms thm_credential_cobb_douglas_reduction_from_axioms`.  " ++
    "Paper `\\label{thm:credential}` Part 2 (Cobb-Douglas regime " ++
    "non-monotonicity of `R(θ)` with peak at `θ† = η/(η + a(1-η))`) " ++
    "is silently omitted from the Lean formalization — the " ++
    "non-monotonicity peak is a differential-calculus statement " ++
    "(first-order condition on a closed form), and the formalization " ++
    "covers the closed-form reduction (Part 1 / `eq:R-senior-rent`) " ++
    "plus the Leontief decay (Part 1+4) and multiplicative decay " ++
    "(Part 3); the Part 2 peak location is not separately tracked.  " ++
    "Disclosed here parallel to the `thm:inversion` Parts 3+4 " ++
    "omission note in `gap_thm_inversion_threshold_CLOSED.notes`."
}

/-- Theorem~\ref{thm:credential} Part 1 (Leontief decay rate
    bundle): pre-collapse + post-collapse + premium negative. -/
def gap_thm_credential_leontief_CLOSED : GapEntry := {
  name := "thm_credential_leontief (Part 1 + Part 4 bundle)"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:credential}` Part 1 + Part 4"
  attackHistory := [
    "Phase 4 paper-verification: VERIFIED — Leontief decay rate " ++
    "`λ T_s ē^a` pre-collapse, vanishing post-collapse, premium " ++
    "negative near `θ = 1`."
  ]
  scope :=
    "Bundle entry covering three theorems: " ++
    "`thm_credential_leontief_pre_collapse` " ++
    "(`leontiefSeniorRent a θ = λ T_s ē^a` for `θ ≤ θ*`), " ++
    "`thm_credential_leontief_post_collapse` " ++
    "(`leontiefSeniorRent a θ = 0` for `θ > θ*`), and " ++
    "`thm_credential_premium_negative_at_collapse` " ++
    "(`R(θ) < 0` when `Y(θ) = 0` and `c_J > 0`).  Captures the " ++
    "paper's Leontief-regime closed forms for the senior rent " ++
    "decay across the threshold."
  notes :=
    "Parametric bridge — `thm_credential_premium_negative_at_collapse` " ++
    "takes `Y = 0` as a bare hypothesis; the vanishing `Y(θ) = 0` " ++
    "near `θ = 1` is itself derived from `V_∞(θ) = 0` above `θ*` " ++
    "(`thm_collapse_above_threshold`) in either the Leontief or " ++
    "Cobb-Douglas regime (paper `\\label{thm:credential}` Part 4). " ++
    "The Lean encoding chains this dependency conceptually; the " ++
    "bridge theorem proves `R(θ) = (1-η)·0/ν - T_j c_J < 0` GIVEN " ++
    "`Y = 0` and `c_J > 0`."
}

/-- Theorem~\ref{thm:credential} Part 3: multiplicative decay. -/
def gap_thm_credential_multiplicative_CLOSED : GapEntry := {
  name := "thm_credential_multiplicative_decay"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:credential}` Part 3"
  attackHistory := [
    "Phase 4 paper-verification: VERIFIED — Lean " ++
    "identity `(ē/τ*)^b · ē^a = ē^(a+b) / τ*^b` is paper's " ++
    "multiplicative-decay claim. Closure via `Real.div_rpow` and " ++
    "`Real.rpow_add`."
  ]
  scope :=
    "`g(ē) · h(ē) = (ē/τ*)^b · ē^a = ē^(a+b) / (τ*)^b`. Post-collapse " ++
    "decay rate `a+b` strictly exceeds pre-collapse rate `a`."
}

/-- Proposition~\ref{prop:junior-senior} (senior wage scaling
    bundle: parametric + `_from_axioms`). -/
def gap_prop_junior_senior_CLOSED : GapEntry := {
  name := "prop_junior_senior_wage (bundle)"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{prop:junior-senior}`, " ++
    "Eq. `\\eqref{eq:senior-junior-ratio}`"
  attackHistory := [
    "Pre-audit (v0.1.0): same composite Cobb-Douglas hypothesis as " ++
    "`thm_credential_cobb_douglas_reduction`. Audit (2026-05) added " ++
    "`prop_junior_senior_wage_from_axioms` that discharges via Cat 2 " ++
    "axiom + definitional unfolding.",
    "Phase 4 paper-verification: VERIFIED — Lean " ++
    "form `wV * h(ē) = (1-η) Y / (ν T_s g(ē))` matches paper " ++
    "`\\label{prop:junior-senior}`.",
    "R2 (2026-05-14) Phase 4 phantom-downstream audit: patched " ++
    "`_from_axioms` form to genuinely consume " ++
    "`axiom_cobb_douglas_factor_share` (via " ++
    "`cobb_douglas_steady_state_identity_from_axiom` bridge); " ++
    "verifiable by `#print axioms prop_junior_senior_wage_from_axioms`."
  ]
  scope :=
    "Bundle entry covering `prop_junior_senior_wage` (parametric " ++
    "form) and `prop_junior_senior_wage_from_axioms` (axiom-" ++
    "discharged form).  Senior wage " ++
    "`w_S = wV · h(ē) = (1-η) Y / (ν T_s g(ē))`. " ++
    "Diverges as `g(ē) → 0` for `θ → 1` under smooth threshold."
  notes :=
    "Cat 2 dependency (via `_from_axioms` form): " ++
    "`axiom_cobb_douglas_factor_share`.  Verifiable by " ++
    "`#print axioms prop_junior_senior_wage_from_axioms`."
}

/-- Theorem~\ref{thm:externality} (wedge formula).  Consumes the
    `wedge` / `externalityResidual` / `MPpriv` definitional
    infrastructure `def`s. -/
def gap_thm_externality_wedge_CLOSED : GapEntry := {
  name := "thm_externality_wedge_identity"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:externality}` " ++
    "(Eq. `\\eqref{eq:wedge}`)"
  attackHistory := [
    "Phase 4 paper-verification: VERIFIED — Lean wedge identity " ++
    "matches paper Eq. `\\eqref{eq:wedge}` (the ratio-form " ++
    "`W_E = (wV/wG)·(gE·hE·Λ)/(1-θ)`).  Closure via `field_simp`.",
    "R3 audit: noted the companion `thm_externality_residual_identity` " ++
    "(`MP_J^S - MP_J^P = externalityResidual`) is by-construction " ++
    "from the defs `MPsoc := MPpriv + externalityResidual` and " ++
    "`externalityResidual := wV·gE·hE·Λ`; reduces to `ring` after " ++
    "unfolding.",
    "R4 audit: the `wedge` / `externalityResidual` / `MPpriv` `def`s " ++
    "this entry consumes are definitional infrastructure (no longer " ++
    "standalone Cat 3 atoms after the R4 Cat 3 ratio guard); they " ++
    "are documented here under `scope`.  The companion " ++
    "`thm_externality_residual_identity` now has its own " ++
    "`gapClosed notInput` entry " ++
    "(`gap_thm_externality_residual_identity_CLOSED`) as a " ++
    "derived `unfold + ring` theorem.",
    "R6 audit: corrected the `paperSource` label from " ++
    "`eq:wedge-explicit` to `eq:wedge`.  The Lean theorem " ++
    "`thm_externality_wedge_identity` proves the `eq:wedge` " ++
    "ratio-form `W_E = (wV/wG)·(gE·hE·Λ)/(1-θ)`, NOT the fully-" ++
    "substituted `eq:wedge-explicit` form; the entry's `scope` " ++
    "already cited `eq:wedge` correctly, so this is a paperSource-" ++
    "field label fix bringing it into agreement."
  ]
  scope :=
    "Covers `thm_externality_wedge_identity` (the substantive wedge " ++
    "form `W_E(θ) = (wV/wG) · g h Λ / (1-θ)` derived by `field_simp` " ++
    "from the def of `wedge`).  Definitional infrastructure `def`s " ++
    "consumed: `wedge wG wV gE hE Lambda θ = externalityResidual " ++
    "wV gE hE Lambda / MPpriv wG θ` (paper Eq. `\\eqref{eq:wedge}`); " ++
    "`externalityResidual wV gE hE Lambda = wV·gE·hE·Lambda` " ++
    "(paper's externality residual `s* = MP_J^S - MP_J^P`); " ++
    "`MPpriv wG θ = (1-θ)·wG` (private marginal product of a " ++
    "junior).  All three are concrete `def`s in Externality.lean " ++
    "whose defining equations hold by `rfl` — definitional " ++
    "notation, not standalone Cat 3 atoms."
}

/-- Theorem~\ref{thm:externality} (non-negativity / strict
    positivity, Part 2 bundle). -/
def gap_thm_externality_nonneg_CLOSED : GapEntry := {
  name := "thm_externality_residual (nonneg + pos bundle)"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:externality}` Part 2"
  attackHistory := [
    "Phase 4 paper-verification: VERIFIED — Lean " ++
    "non-negativity / strict positivity follow from `mul_nonneg` " ++
    "/ `mul_pos` chains."
  ]
  scope :=
    "Bundle entry covering two theorems: " ++
    "`thm_externality_residual_nonneg` (`wV · g · h · Λ ≥ 0` from " ++
    "non-negativity of the factors) and " ++
    "`thm_externality_residual_pos` (strict positivity for " ++
    "`g · h > 0` and `wV, Λ > 0`)."
}

/-- Theorem~\ref{thm:externality} Part 3: Cobb-Douglas Pigouvian
    formula bundle (parametric + `_from_axioms`). -/
def gap_thm_externality_pigouvian_CLOSED : GapEntry := {
  name := "thm_externality_pigouvian_cobb_douglas (bundle)"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:externality}` Part 3 " ++
    "(the formula `s*(θ) = (1-η) Y Λ / (ν T_s)` is derived inside " ++
    "`\\label{thm:externality}` Part 3 and later relabeled " ++
    "`\\label{eq:s-star}` for the Pigouvian-subsidy " ++
    "discussion in `\\label{sec:policy}`)"
  attackHistory := [
    "Pre-audit (v0.1.0): same composite Cobb-Douglas hypothesis as " ++
    "`thm_credential_cobb_douglas_reduction`. Audit (2026-05) added " ++
    "`thm_externality_pigouvian_cobb_douglas_from_axioms` that " ++
    "discharges via Cat 2 axiom + definitional unfolding.",
    "Phase 4 paper-verification: VERIFIED — Lean " ++
    "`s*(θ) = (1-η) Y Λ / (ν T_s)` matches paper Eq. " ++
    "`\\eqref{eq:s-star}`.",
    "R2 (2026-05-14) Phase 4 phantom-downstream audit: patched " ++
    "`_from_axioms` form to genuinely consume " ++
    "`axiom_cobb_douglas_factor_share` (via " ++
    "`cobb_douglas_steady_state_identity_from_axiom` bridge); " ++
    "verifiable by `#print axioms thm_externality_pigouvian_cobb_douglas_from_axioms`."
  ]
  scope :=
    "Bundle entry covering `thm_externality_pigouvian_cobb_douglas` " ++
    "(parametric) and `thm_externality_pigouvian_cobb_douglas_from_axioms` " ++
    "(axiom-discharged via `axiom_cobb_douglas_factor_share`).  Under " ++
    "Cobb-Douglas factor share and `g · h > 0`, " ++
    "`s*(θ) = (1-η) Y(θ) Λ / (ν T_s)`. Closed-form Pigouvian " ++
    "subsidy per junior."
  notes :=
    "Cat 2 dependency (via `_from_axioms` form): " ++
    "`axiom_cobb_douglas_factor_share`.  Verifiable by " ++
    "`#print axioms thm_externality_pigouvian_cobb_douglas_from_axioms`."
}

/-- Proposition~\ref{prop:internalization} (within-firm
    internalization).  Derived definitional-unfolding `theorem`
    (`rfl`); `gapClosed notInput`. -/
def gap_prop_internalization_CLOSED : GapEntry := {
  name := "prop_internalization"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{prop:internalization}`"
  attackHistory := [
    "Pre-audit (v0.1.0): theorem `(1-ζ) · residual / MP_priv = " ++
    "(1-ζ) · wedge` was a `mul_div_assoc` rewrite that does not " ++
    "capture internalization semantics. Audit (2026-05) introduced " ++
    "explicit `internalizedWedge` def and reframed.",
    "Phase 4 paper-verification: VERIFIED — Lean " ++
    "`internalizedWedge` = `(1-ζ) · (residual / MP_priv)` matches " ++
    "paper claim that the effective wedge rescales by `(1-ζ)`.",
    "R3 audit: classified as Cat 3 `gapDefinitional` " ++
    "`structuralEquation`, on the reasoning that the " ++
    "`Vinternalized = (1-ζ) · W_E` identity IS paper-stipulative " ++
    "structural definitional content; removed the redundant " ++
    "`prop_internalization_full`.",
    "R4 audit: reclassified `gapDefinitional structuralEquation " ++
    "cat3PaperNovel` → `gapClosed notInput notCat3`.  Agent J + L " ++
    "noted the paper DERIVES this in a one-line step (internalizing " ++
    "ζ rescales the wedge by `1-ζ`), so the Lean `theorem " ++
    "prop_internalization` is a DERIVED definitional-unfolding " ++
    "identity (`rfl` against the `internalizedWedge` def composed " ++
    "with the `wedge` def), not a Cat 3 paper primitive.  Per spec " ++
    "§0 a trivial-but-honest derived definitional identity is " ++
    "`notInput` / `notCat3` / `gapClosed`.  The `internalizedWedge` " ++
    "def is kept as notational infrastructure (no longer a " ++
    "standalone Cat 3 atom after the R4 Cat 3 ratio guard)."
  ]
  scope :=
    "Derived theorem (`notInput`).  Definitional-unfolding identity " ++
    "`internalizedWedge zeta wG wV gE hE Lambda θ = (1-zeta) · " ++
    "(externalityResidual wV gE hE Lambda / MPpriv wG θ)` — the " ++
    "`rfl` identification of the `internalizedWedge` def " ++
    "(`(1-zeta) · wedge ...`) composed with the `wedge` def " ++
    "(`externalityResidual / MPpriv`).  The full-internalization " ++
    "corner `ζ = 1` (zero effective wedge) is captured directly by " ++
    "the def: `internalizedWedge 1 ... = 0 · wedge ... = 0`.  The " ++
    "`internalizedWedge` def (`(1-zeta) · wedge ...`, paper " ++
    "Proposition~`\\ref{prop:internalization}`) is definitional " ++
    "infrastructure, a concrete `def` in Externality.lean."
  notes :=
    "Substantive economic interpretation lives in paper narrative " ++
    "around `\\label{prop:internalization}`.  The Lean encoding " ++
    "captures the definitional rescaling content; the substantive " ++
    "internalization semantics is paper-side narrative content."
}

/-- Proposition~\ref{prop:decentralized-theta} (social overshoot
    bundle: FOC + wG strict + overshoots). -/
def gap_prop_decentralized_theta_CLOSED : GapEntry := {
  name := "prop_decentralized_theta (bundle)"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{prop:decentralized-theta}`, " ++
    "Eq. `\\eqref{eq:eq-foc}` + `\\eqref{eq:soc-foc}`"
  attackHistory := [
    "Phase 4 paper-verification: VERIFIED — Lean " ++
    "`θ_soc < θ_eq` from anti-monotone `wG` matches paper claim."
  ]
  scope :=
    "Bundle entry covering three theorems: " ++
    "`prop_decentralized_theta_foc` (FOC identity " ++
    "`wG(θ_soc) = wG(θ_eq) + s*`), `prop_decentralized_theta_wG_strict` " ++
    "(strict `wG(θ_eq) < wG(θ_soc)` for `s* > 0`), and " ++
    "`prop_decentralized_theta_overshoots` (anti-monotonicity " ++
    "bridge to `θ_soc < θ_eq`).  Social FOC `p_AI + s* = wG(θ_soc)`; " ++
    "private FOC `p_AI = wG(θ_eq)`. Strict positivity of `s*` plus " ++
    "anti-monotone `wG` in `θ` gives `θ_soc < θ_eq`."
  notes :=
    "Parametric bridge — `prop_decentralized_theta_overshoots` " ++
    "takes `wG` anti-monotonicity as a bare hypothesis " ++
    "(`∀ x y, x < y → wG y < wG x`); the anti-monotonicity itself " ++
    "is derived from the CES inversion structure in " ++
    "`thm_inversion_wage_ratio_monotone` / paper " ++
    "`\\label{thm:inversion}` (wage ratio strictly increasing in " ++
    "`θ`, hence `wG` strictly decreasing as the AI substitution " ++
    "rate rises).  The Lean encoding chains this dependency " ++
    "conceptually; the bridge theorem proves the `θ_soc < θ_eq` " ++
    "overshoot GIVEN anti-monotonicity.  `prop_decentralized_theta_foc` " ++
    "is similarly a parametric bridge: it derives the FOC identity " ++
    "`wG(θ_soc) = wG(θ_eq) + s*` by linear arithmetic from the " ++
    "social FOC `p_AI + s* = wG(θ_soc)` and private FOC " ++
    "`p_AI = wG(θ_eq)` hypotheses (the FOCs themselves are paper-" ++
    "stipulated equilibrium conditions, paper " ++
    "Eq. `\\eqref{eq:eq-foc}` + `\\eqref{eq:soc-foc}`).  The Lean " ++
    "theorems parametrize over any anti-monotone `wG : ℝ → ℝ` " ++
    "rather than re-deriving it from the CES marginal-product " ++
    "structure (which would require Mathlib calculus infrastructure " ++
    "beyond the closed-form `wageRatio` def)."
}

/-- Theorem~\ref{thm:recursive} Part 1: closed-form recursive
    threshold (bundle: closed-form + ratio + leftward). -/
def gap_thm_recursive_threshold_CLOSED : GapEntry := {
  name := "thm_recursive_threshold (Part 1 bundle)"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:recursive}` Part 1, " ++
    "Eq. `\\eqref{eq:theta-inv-recursive}`"
  attackHistory := [
    "Phase 4 paper-verification: VERIFIED — Lean " ++
    "form `(G* - L_G)/(μ K_AI - L_G)` matches paper " ++
    "Eq. `\\eqref{eq:theta-inv-recursive}`."
  ]
  scope :=
    "Bundle entry covering three theorems: " ++
    "`thm_recursive_threshold_closed_form` (the closed form " ++
    "`V_req(θ_inv^{rec}) = G*(r̄)`), `thm_recursive_threshold_ratio` " ++
    "(ratio `θ_inv^{rec}/θ_inv = (K_AI - L_G)/(μ K_AI - L_G)`), and " ++
    "`thm_recursive_threshold_leftward` (strict `θ_inv^{rec} < " ++
    "θ_inv` for `μ > 1`).  Strict leftward shift for `μ > 1`."
}

/-- Theorem~\ref{thm:recursive} Part 2 wedge amplification (Part 4
    asymptotic scaling subsumed by `μ^{1-ρ}` scope claim). -/
def gap_thm_recursive_wedge_CLOSED : GapEntry := {
  name := "thm_recursive_wage_ratio_amplification"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:recursive}` Part 2 wedge " ++
    "amplification ratio, Eq. `\\eqref{eq:wedge-recursive}`"
  attackHistory := [
    "Phase 4 paper-verification: VERIFIED — Lean " ++
    "amplification ratio `(V_req/G)^(1-ρ)` matches paper claim."
  ]
  scope :=
    "`w_V^{rec}/w_V = (V_req/G)^(1-ρ)`. Captures the Part 2 wedge " ++
    "amplification claim.  Paper Part 4 (asymptotic wage-ratio " ++
    "acceleration `μ^{1-ρ}` as `K_AI → ∞`) follows from this " ++
    "Part 2 identity composed with `V_req(θ)/G(θ) → μ` for " ++
    "`K_AI → ∞`; the closed-form Lean identity covers both."
  notes :=
    "Scope clarification: `thm_recursive_wage_ratio_amplification` " ++
    "captures Part 2 closed-form claim (`(V_req/G)^(1-ρ)`) directly; " ++
    "Part 4 asymptotic claim (`μ^{1-ρ}`) is a limit consequence, " ++
    "not separately formalized (would require Mathlib limit " ++
    "infrastructure for `K_AI → ∞`)."
}

/-- Theorem~\ref{thm:recursive} Part 3 (collapse threshold
    μ-invariance) — Ledger-only by-construction structural
    commitment; no Lean declaration. -/
def gap_thm_recursive_invariance_OPEN : GapEntry := {
  name :=
    "thm:recursive Part 3 (μ-invariance) — by-construction; " ++
    "Ledger-only; no Lean declaration"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:recursive}` Part 3"
  attackHistory := [
    "Pre-audit (v0.1.0): theorem `E.thetaStar = E.thetaStar := rfl` " ++
    "was vacuously self-equating.",
    "Audit introduced μ-parametric wrappers and (R2) reformulated as " ++
    "`(fun _ : ℝ => E.thetaStar) μ₁ = (fun _ : ℝ => E.thetaStar) μ₂ " ++
    ":= rfl`, which β-reduces to the same vacuous self-equation.",
    "R3 audit: removed the vacuous theorems entirely.  The paper's " ++
    "Part 3 (μ-invariance of θ* and V_∞) is satisfied by construction " ++
    "in this formalization: `thetaStar = 1 - τ*/T_j` and " ++
    "`VinfHard a θ = ν T_s ((1-θ)T_j)^a` contain no μ.  No Lean " ++
    "theorem is provided; the by-construction structural commitment " ++
    "(absence of μ on the supply side `Vinf`/`eBar`/`thetaStar`) " ++
    "IS the Lean encoding of the paper claim.  Reclassified as " ++
    "`gapDefinitional` Cat 3 `structuralEquation` (the absence of " ++
    "μ-dependence is paper-stipulative structural content, not a " ++
    "derivable consequence).",
    "R6 audit: corrected the `name` field — it formerly read " ++
    "`thm_recursive_invariance (by-construction)`, a phantom " ++
    "declaration name referencing no Lean `def`/`theorem` (R4's " ++
    "removal of the `thetaStarMu`/`VinfHardMu` μ-parametric " ++
    "wrappers left no μ-parametric form to quantify over, so no " ++
    "meaningful Lean theorem can be written: there is no " ++
    "μ-dependence to assert μ-invariance OF).  Set to an honest " ++
    "descriptor; this is a Ledger-only by-construction entry, " ++
    "parallel to the R6 Ledger-only deferred-claim entries but with " ++
    "`gapDefinitional` status (the μ-free carrier signatures are a " ++
    "paper-stipulative structural commitment, not an open gap).",
    "R6 Cat 3 reductionism (≥2 rounds): Round 1 Cat 1? NO — the " ++
    "claim is a paper-stipulative structural commitment about the " ++
    "shape of the formalization's carrier types (`thetaStar`, " ++
    "`VinfHard` take no μ argument), not a Mathlib-derivable " ++
    "mathematical fact; Mathlib has nothing to say about which " ++
    "arguments a paper's bespoke carrier definitions carry.  " ++
    "Round 2 Cat 2? NO — there is no external published theorem " ++
    "asserting μ-independence of the Li 2026 supply-side carriers; " ++
    "the structural design of `\\label{thm:recursive}` Part 3 " ++
    "(recursive verification raising effective DEMAND `Vreq` while " ++
    "the SUPPLY side `Vinf`/`eBar`/`thetaStar` stays μ-free) is " ++
    "paper `\\label{thm:recursive}`-specific.",
    "R8 audit: reclassified `cat3PaperNovel structuralEquation` → " ++
    "`notInput notCat3`, keeping `status := gapDefinitional`.  " ++
    "This entry has NO Lean declaration: it records the ABSENCE of " ++
    "a μ parameter in the `thetaStar` / `VinfHard` carrier " ++
    "signatures — a meta-observation about the formalization's " ++
    "shape, not a paper-stated structural defining equation that " ++
    "any Lean derivation consumes as an atomic input.  A " ++
    "`structuralEquation` Cat 3 atom is a STATED defining axiom on " ++
    "a primitive (e.g. `axiom V_dyn_def`); the μ-freedom here is " ++
    "true by construction of the (separately Ledger-tracked) " ++
    "`thetaStar` / `Vinf` carriers, not a standalone atomic input " ++
    "— hence `notInput` / `notCat3`.",
    "R10 audit: reclassified `status := gapDefinitional` → " ++
    "`gapOpen`.  Multi-agent fresh hostile audit (R5 S, R5 U, R9 X, " ++
    "R10 W) consistently flagged the `gapDefinitional + notInput + " ++
    "notCat3` combination as outside the gapDefinitional scope: " ++
    "the gapDefinitional tier is bound to Cat 3 paper-novel atoms " ++
    "with sub-types {carrier, predicate, structuralEq}, not to " ++
    "`notInput notCat3` meta-observations.  Reclassified to " ++
    "`gapOpen`, which matches the four other Ledger-only entries " ++
    "(window-invariance, sequential-kinks, intermediate-regime, " ++
    "adjustment-narrative).  Semantic refinement: the paper claim " ++
    "is satisfied by construction in the Lean encoding (no μ " ++
    "parameter in the supply-side carriers), so this is `gapOpen` " ++
    "in the formal sense (no Lean derivation provided) while being " ++
    "trivially satisfied by the Lean code's type signatures.  Def " ++
    "identifier renamed `_DEFINITIONAL` → `_OPEN` for status-name " ++
    "consistency."
  ]
  scope :=
    "Paper Theorem 3 Part 3 (μ-invariance of θ* and V_∞) is " ++
    "satisfied by construction in this formalization: " ++
    "`thetaStar = 1 - τ*/T_j` and `VinfHard a θ = ν T_s ((1-θ)T_j)^a` " ++
    "contain no μ.  μ-invariance holds by construction because " ++
    "`thetaStar` / `VinfHard` are defined without a μ parameter; " ++
    "no Lean declaration exists or is needed — there is no " ++
    "μ-dependence to quantify over, so the absence of a μ " ++
    "parameter in the carrier type signatures IS the claim.  Not " ++
    "an atomic input (`notInput` / `notCat3`): it records the " ++
    "ABSENCE of a parameter in the separately-tracked `thetaStar` " ++
    "/ `Vinf` carriers, not a standalone paper-stated structural " ++
    "equation.  Tracked as a `gapOpen` Ledger-only `GapEntry` (no " ++
    "Lean declaration; the paper claim is satisfied by the Lean " ++
    "code's type-signature structure, which is the honest encoding " ++
    "given the absence of a μ-dependence to derive)."
  notes :=
    "Recursive verification operates on the demand side `Vreq`, not " ++
    "the supply side `Vinf`.  The paper's Part 3 claim is structural: " ++
    "the carriers themselves are μ-free.  This is encoded directly " ++
    "in the type signatures of `Vinf : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ` " ++
    "and `VinfHard : ℝ → ℝ → ℝ` (in `Basic.lean`) and `thetaStar : ℝ` " ++
    "(in `Collapse.lean`) — none take a `μ` argument.  No Lean " ++
    "declaration named in this entry; retrievable via `#eval` over " ++
    "`allGaps`, not by `#print axioms`."
}

/-- Proposition~\ref{prop:boundary}: separability characterization. -/
def gap_prop_boundary_CLOSED : GapEntry := {
  name := "prop_boundary_collapse_iff"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{prop:boundary}`"
  attackHistory := [
    "Phase 4 paper-verification: VERIFIED — Lean " ++
    "`1 - ζ_V > θ* ↔ ζ_V < τ*/T_j` matches paper iff."
  ]
  scope :=
    "Pipeline collapse iff `ζ_V < τ*/T_j`, equivalently " ++
    "`1 - ζ_V > θ*`. Algebraic equivalence."
}

/-- Theorem~\ref{thm:aggregation} Part 2: Cobb-Douglas zero-product
    (bundle: base + least-resilient corollary). -/
def gap_thm_aggregation_CD_CLOSED : GapEntry := {
  name := "thm_aggregation_cobb_douglas (Part 2 bundle)"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:aggregation}` Part 2"
  attackHistory := [
    "Phase 4 paper-verification: VERIFIED — Lean " ++
    "`∏ Y_i^(ω_i) = 0` via `Finset.prod_eq_zero` + `Real.zero_rpow` " ++
    "matches paper Cobb-Douglas zero-product rule."
  ]
  scope :=
    "Bundle entry covering two theorems: " ++
    "`thm_aggregation_cobb_douglas_zero` (`∏ Y_i^(ω_i) = 0` whenever " ++
    "any `Y_i = 0` with `ω_i > 0`) and " ++
    "`thm_aggregation_least_resilient_collapse` (existential form: " ++
    "aggregate collapses if ANY profession's Y_i = 0).  Uses " ++
    "`Real.zero_rpow` for `ω_i > 0` and `Finset.prod_eq_zero`."
}

/-- Theorem~\ref{thm:aggregation} Part 3: perfect-substitutes
    (bundle: survival + residual). -/
def gap_thm_aggregation_PS_CLOSED : GapEntry := {
  name := "thm_aggregation_perfect_substitutes (Part 3 bundle)"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:aggregation}` Part 3"
  attackHistory := [
    "Phase 4 paper-verification: VERIFIED — Lean " ++
    "`∑ ω_i Y_i > 0` from one positive term matches paper claim."
  ]
  scope :=
    "Bundle entry covering two theorems: " ++
    "`thm_aggregation_perfect_substitutes_survival` (`∑ ω_i Y_i > 0` " ++
    "whenever any term is strictly positive) and " ++
    "`thm_aggregation_perfect_substitutes_residual` (post-collapse " ++
    "residual identity: `∑_{i ∈ s} ω_i Y_i = ∑_{i ∈ s.erase i₀} " ++
    "ω_i Y_i` when `Y_{i₀} = 0`).  Standard sum-positivity / sum-" ++
    "erase arguments."
}

/-- Proposition~\ref{prop:adjustment-margins} (career extension portion;
    bundle covering strict + bounded theorems). -/
def gap_prop_adjustment_career_CLOSED : GapEntry := {
  name := "prop_adjustment_career_extension (bundle)"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource :=
    "Li 2026, `\\label{prop:adjustment-margins}` (career extension)"
  attackHistory := [
    "Phase 4 paper-verification: VERIFIED — Lean " ++
    "`θ* < θ*_ext = 1 - τ*/T < 1` matches paper."
  ]
  scope :=
    "Bundle entry covering two theorems: " ++
    "`prop_adjustment_career_extension_strict` (`θ* < θ*_ext`) and " ++
    "`prop_adjustment_career_extension_bounded` (`θ*_ext < 1`). " ++
    "`θ* < θ*_ext = 1 - τ*/T < 1` strictly: career-extension margin " ++
    "shifts the collapse threshold rightward but cannot reach 1. " ++
    "The threshold-reduction margin (a separate substantive " ++
    "closed-form claim of the same `prop:adjustment-margins` " ++
    "narrative) is split out and closed as the derived theorem " ++
    "`prop_adjustment_threshold_reduction_floor` (tracked under " ++
    "`gap_prop_adjustment_threshold_reduction_CLOSED`).  The " ++
    "remaining endogenous-AI-verification residual margin — a " ++
    "substantive phenomenological claim about the Polanyi " ++
    "verification residual — is tracked as the Ledger-only " ++
    "`gap_prop_adjustment_narrative_OPEN` " ++
    "(`phenomenologicalConjecture`, resolution path is empirical " ++
    "cohort-study evidence rather than Mathlib derivation)."
}

/-- Theorem~\ref{thm:endogenous-ai} Part 1: Brouwer existence
    (bundle: 1-D Brouwer lemma + theorem).  `gapPartial`: the
    abstract 1-D Brouwer sub-clause is closed; the paper's specific
    Φ construction is not Lean-formalized. -/
def gap_thm_endogenous_ai_existence_PARTIAL : GapEntry := {
  name := "thm_endogenous_ai_existence (bundle)"
  status := GapStatus.gapPartial
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:endogenous-ai}` Part 1, " ++
    "Eq. `\\eqref{eq:Phi}`"
  attackHistory := [
    "Phase 4 paper-verification: VERIFIED — Lean " ++
    "`brouwer_1d` (1-D Brouwer via Mathlib IVT " ++
    "`intermediate_value_Icc'`) is applied to the abstract Φ.",
    "R2 (2026-05-14) Phase 4 scope audit: the Lean theorem applies " ++
    "1-D Brouwer to an ABSTRACT continuous self-map Φ; the paper's " ++
    "full Part 1 additionally constructs Φ from Ψ and the " ++
    "verification-stock decomposition `V_∞ = V_prod + V_AI`.  That " ++
    "construction is NOT formalized in this Lean theorem.",
    "R3 audit: reclassified `gapClosed` → `gapPartial`.  The Lean " ++
    "theorem proves abstract 1-D Brouwer (IVT) for ANY continuous " ++
    "self-map Φ; the paper's Theorem 7 Part 1 requires the SPECIFIC " ++
    "Φ construction from Ψ + the verification-stock decomposition. " ++
    "Since a sub-clause is closed and substantive content remains, " ++
    "the honest tier is `gapPartial`, not `gapClosed`.",
    "R8 audit: renamed the entry `def` identifier from " ++
    "`gap_thm_endogenous_ai_existence_CLOSED` to " ++
    "`gap_thm_endogenous_ai_existence_PARTIAL` — the `_CLOSED` " ++
    "suffix was inconsistent with `status := gapPartial`.  No Lean " ++
    "theorem name changed (the underlying `brouwer_1d` / " ++
    "`thm_endogenous_ai_existence` declarations are unaffected); " ++
    "this is a Ledger-entry-identifier fix only."
  ]
  scope :=
    "Bundle entry covering two theorems: `brouwer_1d` " ++
    "(general 1-D Brouwer / IVT-derived fixed point for any " ++
    "continuous self-map of `[a, b]`) and " ++
    "`thm_endogenous_ai_existence` (applied form: any continuous Φ " ++
    "satisfying `a ≤ Φ a ∧ Φ b ≤ b` has a fixed point).  " ++
    "Sub-clause CLOSED: 1-D Brouwer (IVT) existence for an abstract " ++
    "continuous self-map Φ.  Remaining (OPEN): the paper's specific " ++
    "construction of Φ from Ψ + the verification-stock decomposition " ++
    "`V_∞ = V_prod + V_AI` is documented in the `thm_endogenous_ai_existence` " ++
    "docstring but not Lean-formalized (would require Mathlib " ++
    "calculus + Ψ continuity machinery)."
  notes :=
    "Mathlib dependency: `intermediate_value_Icc'`. Closure is 1-D " ++
    "IVT, not Brouwer fixed-point general form.  `gapPartial`: " ++
    "abstract-Brouwer sub-clause closed; paper's Φ construction " ++
    "remains open."
}

/-- Theorem~\ref{thm:endogenous-ai} Part 2: uniqueness under monotonicity. -/
def gap_thm_endogenous_ai_uniqueness_CLOSED : GapEntry := {
  name := "thm_endogenous_ai_uniqueness"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:endogenous-ai}` Part 2"
  attackHistory := [
    "Phase 4 paper-verification: VERIFIED — Lean " ++
    "strictly-anti-monotone-implies-at-most-one-fixed-point matches " ++
    "paper Part 2."
  ]
  scope :=
    "Strictly anti-monotone map on ℝ has at most one fixed point. " ++
    "Used to upgrade Part 1's existence to existence-and-uniqueness " ++
    "under the paper's monotonicity assumption on `V_prod^*`."
}

/-- Theorem~\ref{thm:endogenous-ai} Part 3: corner self-consistency
    (bundle covering exogenous + endogenous theorems). -/
def gap_thm_endogenous_ai_corner_CLOSED : GapEntry := {
  name := "thm_endogenous_ai_corner (bundle)"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:endogenous-ai}` Part 3"
  attackHistory := [
    "Pre-audit (v0.1.0): theorem " ++
    "`thm_endogenous_ai_corner_endogenous_inconsistent` only proved " ++
    "`0 < thetaStar`, not the inconsistency.  Patched: added " ++
    "explicit `thetaEndo : ℝ → ℝ` def and witnessed the inconsistency " ++
    "as the strict inequality `thetaEndo 0 < thetaStar` " ++
    "(R2 simplification: dropped trivial conjunct).",
    "Phase 4 paper-verification: VERIFIED — Lean " ++
    "matches paper Part 3 corner inconsistency."
  ]
  scope :=
    "Bundle entry covering two theorems: " ++
    "`thm_endogenous_ai_corner_exogenous` (under exogenous θ ≥ θ*, " ++
    "`V_∞ = 0`) and `thm_endogenous_ai_corner_endogenous_inconsistent`.  " ++
    "The latter proves the strict inequality `thetaEndo 0 < thetaStar` " ++
    "(NOT `False` directly): under the endogenous map " ++
    "`θ_endo(K_AI) = K_AI/(L_G + K_AI)`, the corner `K_AI = 0` " ++
    "yields `θ_endo(0) = 0`, which lies STRICTLY BELOW the collapse " ++
    "threshold `θ* > 0` (when `τ* < T_j`).  This strict inequality " ++
    "IS the paper's substantive Part 3 claim: it contradicts the " ++
    "`θ ≥ θ*` corner premise, so the `K_AI = 0` corner is not a " ++
    "fixed point of the endogenous map — the inconsistency is " ++
    "`thetaEndo 0 < thetaStar` set against `thetaEndo 0 ≥ thetaStar`, " ++
    "not a Lean `False` derivation."
}

/-- Theorem~\ref{thm:endogenous-ai} Parts 4–5: hysteresis recovery rate
    (bundle covering four theorems). -/
def gap_thm_endogenous_ai_hysteresis_CLOSED : GapEntry := {
  name := "thm_endogenous_ai_recovery (bundle)"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:endogenous-ai}` Parts 4–5, " ++
    "Eq. `\\eqref{eq:hysteresis-deficit}` + " ++
    "Eq. `\\eqref{eq:multi-cohort-recovery}`"
  attackHistory := [
    "Pre-audit (v0.1.0): `thm_endogenous_ai_recovery_takes_full_career` " ++
    "only proved `0 < T_j + T_s` (trivial).  Patched: " ++
    "strengthened to actual scaling — for `t < t_1 + T`, the recovery " ++
    "stock is strictly below the steady-state ceiling — capturing the " ++
    "paper's claim that recovery requires the FULL career length.",
    "Phase 4 paper-verification: VERIFIED — Lean " ++
    "hysteresis statements match paper Parts 4-5."
  ]
  scope :=
    "Bundle entry covering four theorems: " ++
    "`thm_endogenous_ai_hysteresis_nonneg` (non-negativity of " ++
    "deficit), `thm_endogenous_ai_recovery_at_Tj` (zero at junior " ++
    "horizon), `thm_endogenous_ai_full_recovery_at_T` (full recovery " ++
    "at `t = t_1 + T`), `thm_endogenous_ai_recovery_takes_full_career` " ++
    "(strict below steady-state ceiling for `t < t_1 + T`).  " ++
    "Hysteresis deficit `ν · |overlap| · ((1-θ_L) T_j)^a`; " ++
    "recovery stock `V_∞(t) = ν · min(t - t_1 - T_j, T_s) · " ++
    "((1-θ_L) T_j)^a`. Asymmetry: full recovery requires `t ≥ t_1 + T`."
}

/-! ### gapOpen deferred-paper-claim entries — Ledger-only records.

  These four entries record paper claims whose faithful sound
  statement requires additional Mathlib infrastructure (path-
  dependent / measure-theoretic integrals; one-sided limits across
  kinks; calculus across CES transitions) beyond this
  formalization's structural scope.  Each is tracked WITHOUT a
  corresponding Lean `axiom`/`def`/`theorem` declaration — see the
  "Ledger-only-entry exemption" in the top docstring.  The encoding
  history (the `axiom` → `def : Prop` → Ledger-only encoding ladder)
  is recorded in each entry's `attackHistory`.  Classification:
  three are paper-proven MATHEMATICAL results whose Lean derivation
  is deferred (`gap_window_invariance_OPEN`,
  `gap_aggregation_sequential_kinks_OPEN`,
  `gap_aggregation_intermediate_regime_OPEN`) — un-formalized
  DERIVED results, not atomic inputs, so tagged `notInput` /
  `notCat3`; one is a `cat3PaperNovel` `phenomenologicalConjecture`
  (`gap_prop_adjustment_narrative_OPEN` — non-codifiability of the
  verification residual is a substantive empirical claim with a
  cohort-study resolution path, a genuine Cat 3 paper-novel claim
  under the `phenomenologicalConjecture` sub-type).  None is
  `gapBlocked` (Mathlib infra absence ALONE is NOT BLOCKED).

  The numerical-calibration corollary and the threshold-reduction
  conjunct of the adjustment-margins narrative are NOT in this
  group: they are derived `theorem`s
  (`cor_quant_predictions_calibration` via `rw` + `norm_num`;
  `prop_adjustment_threshold_reduction_floor` via
  `div_lt_div_of_pos_right` + `linarith`), tracked as
  `gapClosed notInput`. -/

/-- Proposition~\ref{prop:stock-flow-asymptotics} Part 4 (window
    invariance) — Ledger-only `gapOpen`; not Lean-encoded.  A
    faithful sound statement requires Mathlib `MeasureTheory`
    integral infrastructure beyond this formalization's scope. -/
def gap_window_invariance_OPEN : GapEntry := {
  name :=
    "prop:stock-flow-asymptotics Part 4 (window invariance) — " ++
    "Ledger-only; not Lean-encoded"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{prop:stock-flow-asymptotics}` Part 4"
  attackHistory := [
    "Pre-audit (v0.1.0): classified `gapBlocked` citing Mathlib " ++
    "`MeasureTheory` absence.  R1 (2026-05-14) reclassified — " ++
    "Mathlib infra absence alone is NOT BLOCKED.",
    "R2 (2026-05-14) Phase 4 internal-consistency audit: " ++
    "reclassified to `gapDefinitional structuralEquation` invoking " ++
    "the §15.1.D encoding-exemption.",
    "R3 audit: reclassified to `cat3PaperNovel workingAssumption " ++
    "gapOpen`.  Window invariance is NOT a paper-stipulative " ++
    "definitional atom — the paper PROVES it (cohort-integral " ++
    "specialization: `V(t) = ∫_{t-T}^{t-T_j} ν g(e_J(c)) h(e_J(c)) " ++
    "dc`, with the integrand depending only on `θ(s)` for `s` in " ++
    "the window).  R3 added a typed `axiom gap_window_invariance_OPEN` " ++
    "(Decomp.lean) with abstract `windowedStock` functional.",
    "R4 audit: converted from `axiom` to `def : Prop` — the R3 " ++
    "axiom form was `False`-injectable (R4 hostile-audit machine-" ++
    "verification: free `windowedStock` quantified with no " ++
    "constraint; `windowedStock := fun _ _ => 0` ⊢ " ++
    "`0 = ν T_s g h > 0` ⊢ `False`).  The R4 `def : Prop` added a " ++
    "constraining hypothesis predicate `IsCohortWindowStock`.",
    "R5 audit: the R4 `def : Prop` was found TAUTOLOGICAL — the " ++
    "constraining predicate `IsCohortWindowStock windowedStock` " ++
    "was defined to be EXACTLY the conclusion the proposition " ++
    "asserts, so `gap_window_invariance_OPEN` reduced to " ++
    "`∀ ws, P ws → P ws`, provable by `fun _ h => h`; the paper's " ++
    "substantive claim was not actually formalized.",
    "R6 audit: removed the Lean declaration entirely — both the " ++
    "`def gap_window_invariance_OPEN : Prop` and the constraining " ++
    "`def IsCohortWindowStock` are deleted from Decomp.lean.  The " ++
    "claim is now tracked as a Ledger-only `gapOpen` `GapEntry`.  " ++
    "Encoding any of {`axiom`, `def : Prop` with a " ++
    "conclusion-equalling constraining predicate} is an anti-" ++
    "pattern; honest tracking via this Ledger `GapEntry` is the " ++
    "correct encoding for a paper claim that requires out-of-scope " ++
    "Mathlib `MeasureTheory` infrastructure to even STATE " ++
    "faithfully.  Cat 3 reductionism (≥2 rounds): Round 1 Cat 1? " ++
    "NO — Mathlib has no named cohort-window-stock functional " ++
    "primitive, and the cohort-integral form cannot be stated " ++
    "without `MeasureTheory` integration that is out of scope.  " ++
    "Round 2 Cat 2? NO — the cohort-integral construction " ++
    "`V(t) = ∫_{t-T}^{t-T_j} ν g(e_J(c)) h(e_J(c)) dc` is paper " ++
    "`\\label{def:cohort}`-specific, bound to the paper's Economy " ++
    "primitives `T`, `Tj`, `nu` and the steady-state stock `Vinf` " ++
    "— not an external published theorem.  Stands as " ++
    "`cat3PaperNovel workingAssumption`.",
    "R8 audit: reclassified `cat3PaperNovel workingAssumption` → " ++
    "`notInput notCat3`.  The window-invariance identity is a " ++
    "paper-PROVEN mathematical result (cohort-integral " ++
    "specialization), not a Cat 3 paper-novel ATOM — it is an " ++
    "un-formalized DERIVED result whose Lean derivation is deferred " ++
    "for want of out-of-scope Mathlib `MeasureTheory` " ++
    "infrastructure.  An atomic Cat 3 input is a primitive type / " ++
    "hypothesisPredicate / structural defining equation the " ++
    "formalization builds ON; this is a higher-level claim built " ++
    "FROM the cohort primitives, hence `notInput` / `notCat3`.  " ++
    "The genuine Cat 3 atomic inputs of this project are the " ++
    "`Economy` carrier and the four hypothesisPredicates."
  ]
  scope :=
    "Paper's window-integral identity " ++
    "`V(t) = ∫_{t-T}^{t-T_j} ν g h dc`, asserting that the " ++
    "verification stock at time `t` depends only on `θ_s` for " ++
    "`s ∈ [t-T, t-T_j]` (in particular it is invariant to the " ++
    "current rate `θ_t`).  Paper-proven mathematical result " ++
    "(cohort-integral specialization); Lean derivation deferred.  " ++
    "NOT an atomic input — a derived result built from the cohort " ++
    "primitives — hence `notInput` / `notCat3`.  NOT Lean-encoded: " ++
    "a faithful sound STATEMENT of the cohort-integral form " ++
    "requires out-of-scope Mathlib `MeasureTheory` integral " ++
    "infrastructure.  No Lean `axiom`/`def`/`theorem` declaration " ++
    "exists — encoding as `axiom` is unsound (`False`-injectable) " ++
    "and as a `def : Prop` with a conclusion-equalling constraining " ++
    "predicate is vacuous (tautological); this Ledger `GapEntry` is " ++
    "the honest encoding, tracked as a `gapOpen` Ledger-only entry."
  notes :=
    "Ledger-only entry (Ledger-only-entry exemption — see Ledger " ++
    "top docstring).  No Lean declaration; not retrievable by " ++
    "`#print axioms` — correct, since nothing asserts or consumes " ++
    "it (asserting it would be unsound).  Retrievable via " ++
    "`#eval` over `allGaps`.\n\n" ++
    "Parts 1-3 of `\\label{prop:stock-flow-asymptotics}` omission " ++
    "note: Parts 1 (Leontief limit `ρ → -∞`), 2 (Cobb-Douglas " ++
    "`ρ → 0`), and 3 (generic CES factor share `s_V`) are " ++
    "factor-share computations the paper derives `direct from the " ++
    "CES form` (paper proof of `\\label{prop:stock-flow-" ++
    "asymptotics}`).  They are NOT separately formalized in the " ++
    "Lean codebase — they fall under the Cat 2 marginal-product / " ++
    "factor-share calculus already suppressed via " ++
    "`axiom_ces_wage_ratio` and `axiom_cobb_douglas_factor_share` " ++
    "(the Cobb-Douglas `Wstock = (1-η)W` factor share of Part 2 IS " ++
    "the conclusion of `axiom_cobb_douglas_factor_share`), and are " ++
    "economic-narrative / limit-case content rather than " ++
    "substantive new algebraic identities.  This omission is " ++
    "recorded here for transparency parity with " ++
    "`gap_thm_inversion_threshold_CLOSED.notes` (which documents " ++
    "the analogous Parts 3-4 omission for `thm:inversion`).  Only " ++
    "Part 4 (window invariance) is tracked as a deferred gap, " ++
    "since it is the only Part requiring out-of-scope (`MeasureTheory`) " ++
    "infrastructure to STATE."
}

/-- Theorem~\ref{thm:aggregation} Part 1 (sequential phase
    transitions) — Ledger-only `gapOpen`; not Lean-encoded.  A
    faithful sound statement of the kink / one-sided-limit structure
    at each order statistic `θ*_(k)` requires Mathlib continuity /
    kink-detection infrastructure beyond this formalization's
    scope. -/
def gap_aggregation_sequential_kinks_OPEN : GapEntry := {
  name :=
    "thm:aggregation Part 1 (sequential phase-transition kinks) — " ++
    "Ledger-only; not Lean-encoded"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:aggregation}` Part 1, " ++
    "Eq. `\\eqref{eq:agg-marginal}`"
  attackHistory := [
    "Pre-audit (v0.1.0): classified `gapBlocked` citing continuity " ++
    "infra absence.  R1 (2026-05-14) reclassified as " ++
    "`workingAssumption` — Mathlib infra absence alone is NOT " ++
    "BLOCKED.",
    "R2 (2026-05-14) Phase 4 post-publication compliance audit: " ++
    "reclassified to `phenomenologicalConjecture`.",
    "R3 audit: reclassified back to `cat3PaperNovel " ++
    "workingAssumption gapOpen`.  `phenomenologicalConjecture` " ++
    "requires an EMPIRICAL / INTERPRETIVE resolution path; the " ++
    "sequential-kink claim is a MATHEMATICAL claim about the CES " ++
    "aggregator's continuity / kink structure at the order " ++
    "statistics `θ*_(k)`, awaiting Mathlib continuity / kink-" ++
    "detection infrastructure — not an empirical claim.  R3 added " ++
    "a typed `axiom gap_aggregation_sequential_kinks_OPEN` " ++
    "(Aggregation.lean) with abstract `Yagg` and order-statistic " ++
    "enumeration.",
    "R4 audit: converted from `axiom` to `def : Prop` — the R3 " ++
    "axiom form was `False`-injectable (R4 hostile-audit machine-" ++
    "verification: free `Yagg` quantified with no constraint; " ++
    "`Yagg := fun _ => 0` ⊢ `0 < 0` ⊢ `False`).  The R4 " ++
    "`def : Prop` added a constraining hypothesis predicate " ++
    "`IsCESAggregateOutput`.",
    "R5 audit: the R4 `def : Prop` was found TAUTOLOGICAL — the " ++
    "constraining predicate `IsCESAggregateOutput Yagg " ++
    "thetaStarOrd N` was defined to be EXACTLY the conclusion the " ++
    "proposition asserts, so `gap_aggregation_sequential_kinks_OPEN` " ++
    "reduced to `∀ Yagg ..., P → P`, provable by `fun _ h => h`; " ++
    "the paper's substantive claim was not actually formalized.",
    "R6 audit: removed the Lean declaration entirely — both the " ++
    "`def gap_aggregation_sequential_kinks_OPEN : Prop` and the " ++
    "constraining `def IsCESAggregateOutput` are deleted from " ++
    "Aggregation.lean.  The claim is now tracked as a Ledger-only " ++
    "`gapOpen` `GapEntry`.  Encoding any of {`axiom`, `def : Prop` " ++
    "with a conclusion-equalling constraining predicate} is an " ++
    "anti-pattern; honest tracking via this Ledger `GapEntry` is " ++
    "the correct encoding for a paper claim that requires out-of-" ++
    "scope Mathlib continuity / kink-detection infrastructure to " ++
    "even STATE faithfully.  Cat 3 reductionism (≥2 rounds): " ++
    "Round 1 Cat 1? NO — Mathlib has no named CES-aggregate-output " ++
    "primitive, and the downward-jump / one-sided-limit structure " ++
    "cannot be stated without continuity infrastructure that is " ++
    "out of scope.  Round 2 Cat 2? NO — the cross-profession CES " ++
    "aggregator of Eq. `\\eqref{eq:Y-agg}` with the hard-promotion " ++
    "downward-jump structure is paper `\\label{thm:aggregation}`-" ++
    "specific, not an external published theorem.  Stands as " ++
    "`cat3PaperNovel workingAssumption`.",
    "R8 audit: reclassified `cat3PaperNovel workingAssumption` → " ++
    "`notInput notCat3`.  The sequential-kink claim is a paper-" ++
    "PROVEN mathematical result about the CES aggregator's kink / " ++
    "one-sided-limit structure, not a Cat 3 paper-novel ATOM — it " ++
    "is an un-formalized DERIVED result whose Lean derivation is " ++
    "deferred for want of out-of-scope Mathlib continuity / kink-" ++
    "detection infrastructure.  An atomic Cat 3 input is a " ++
    "primitive type / hypothesisPredicate / structural defining " ++
    "equation the formalization builds ON; this is a higher-level " ++
    "claim built FROM the profession primitives, hence `notInput` " ++
    "/ `notCat3`."
  ]
  scope :=
    "Sequential phase transitions at order statistics " ++
    "`θ*_(1) < ... < θ*_(N)` — in the hard-promotion case, a " ++
    "downward jump of `Y_agg` at each `θ*_(k)`.  Paper-proven " ++
    "mathematical result (the paper proves the jump structure); " ++
    "Lean derivation deferred.  NOT an atomic input — a derived " ++
    "result built from the profession primitives — hence " ++
    "`notInput` / `notCat3`.  NOT Lean-encoded: a faithful sound " ++
    "STATEMENT of the kink / one-sided-limit structure requires " ++
    "out-of-scope Mathlib continuity / kink-detection " ++
    "infrastructure.  No Lean `axiom`/`def`/`theorem` declaration " ++
    "exists — encoding as `axiom` is unsound (`False`-injectable) " ++
    "and as a `def : Prop` with a conclusion-equalling constraining " ++
    "predicate is vacuous (tautological); this Ledger `GapEntry` is " ++
    "the honest encoding, tracked as a `gapOpen` Ledger-only " ++
    "entry.  The Cobb-Douglas and perfect-substitutes limit cases " ++
    "(Parts 2 + 3) are the substantive structural content and ARE " ++
    "closed."
  notes :=
    "Ledger-only entry (Ledger-only-entry exemption — see Ledger " ++
    "top docstring).  No Lean declaration; not retrievable by " ++
    "`#print axioms` — correct, since nothing asserts or consumes " ++
    "it.  Retrievable via `#eval` over `allGaps`."
}

/-- Theorem~\ref{thm:aggregation} Part 4 (intermediate-regime
    share-weighted elasticity acceleration) — Ledger-only `gapOpen`;
    not Lean-encoded.  A faithful sound statement requires Mathlib
    calculus infrastructure (differentiability of the CES
    aggregator) beyond this formalization's scope. -/
def gap_aggregation_intermediate_regime_OPEN : GapEntry := {
  name :=
    "thm:aggregation Part 4 (intermediate-regime elasticity " ++
    "acceleration) — Ledger-only; not Lean-encoded"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:aggregation}` Part 4, " ++
    "Eq. `\\eqref{eq:agg-decay-precise}`"
  attackHistory := [
    "Pre-audit (v0.1.0): classified `gapBlocked` citing calculus " ++
    "infra absence.  R1 (2026-05-14) reclassified as " ++
    "`workingAssumption` — Mathlib infra absence alone is NOT " ++
    "BLOCKED.",
    "R2 (2026-05-14) Phase 4 post-publication compliance audit: " ++
    "reclassified to `phenomenologicalConjecture`.",
    "R3 audit: reclassified back to `cat3PaperNovel " ++
    "workingAssumption gapOpen`.  `phenomenologicalConjecture` " ++
    "requires an EMPIRICAL / INTERPRETIVE resolution path; the " ++
    "intermediate-regime elasticity-acceleration claim is a " ++
    "MATHEMATICAL claim about the CES aggregator's " ++
    "differentiability / share-weighted elasticity for " ++
    "`σ_a ∈ (1, ∞)`, awaiting Mathlib calculus infrastructure — " ++
    "not an empirical claim.  R3 added a typed `axiom " ++
    "gap_aggregation_intermediate_regime_OPEN` (Aggregation.lean) " ++
    "with abstract `aggElasticity`.",
    "R4 audit: converted from `axiom` to `def : Prop` — the R3 " ++
    "axiom form was `False`-injectable (R4 hostile-audit machine-" ++
    "verification: free `aggElasticity` quantified with no " ++
    "constraint; `aggElasticity := fun x => -x` ⊢ `t ≤ -t - 1` ⊢ " ++
    "`False`).  The R4 `def : Prop` added a constraining " ++
    "hypothesis predicate `IsAggregateElasticity`.",
    "R5 audit: the R4 `def : Prop` was found TAUTOLOGICAL — the " ++
    "constraining predicate `IsAggregateElasticity aggElasticity " ++
    "sigma_a thetaStarOrd` was defined to be EXACTLY the " ++
    "conclusion the proposition asserts, so " ++
    "`gap_aggregation_intermediate_regime_OPEN` reduced to " ++
    "`∀ aggElasticity ..., P → P`, provable by `fun _ h => h`; " ++
    "the paper's substantive claim was not actually formalized.",
    "R6 audit: removed the Lean declaration entirely — both the " ++
    "`def gap_aggregation_intermediate_regime_OPEN : Prop` and the " ++
    "constraining `def IsAggregateElasticity` are deleted from " ++
    "Aggregation.lean.  The claim is now tracked as a Ledger-only " ++
    "`gapOpen` `GapEntry`.  Encoding any of {`axiom`, `def : Prop` " ++
    "with a conclusion-equalling constraining predicate} is an " ++
    "anti-pattern; honest tracking via this Ledger `GapEntry` is " ++
    "the correct encoding for a paper claim that requires out-of-" ++
    "scope Mathlib calculus infrastructure to even STATE " ++
    "faithfully.  Cat 3 reductionism (≥2 rounds): Round 1 Cat 1? " ++
    "NO — Mathlib has no named CES-aggregate-elasticity primitive, " ++
    "and the share-weighted elasticity `-∂ log Y_agg/∂ log(1-θ)` " ++
    "cannot be stated without calculus infrastructure that is out " ++
    "of scope.  Round 2 Cat 2? NO — the share-weighted aggregate " ++
    "output elasticity of Eq. `\\eqref{eq:agg-decay-precise}` for " ++
    "`σ_a ∈ (1, ∞)` is paper `\\label{thm:aggregation}`-specific, " ++
    "not an external published theorem.  Stands as " ++
    "`cat3PaperNovel workingAssumption`.",
    "R8 audit: reclassified `cat3PaperNovel workingAssumption` → " ++
    "`notInput notCat3`.  The intermediate-regime elasticity-" ++
    "acceleration claim is a paper-PROVEN mathematical result " ++
    "about the CES aggregator's share-weighted elasticity, not a " ++
    "Cat 3 paper-novel ATOM — it is an un-formalized DERIVED " ++
    "result whose Lean derivation is deferred for want of out-of-" ++
    "scope Mathlib calculus infrastructure.  An atomic Cat 3 input " ++
    "is a primitive type / hypothesisPredicate / structural " ++
    "defining equation the formalization builds ON; this is a " ++
    "higher-level claim built FROM the profession primitives, " ++
    "hence `notInput` / `notCat3`."
  ]
  scope :=
    "For `σ_a ∈ (1, ∞)`, aggregate elasticity is non-decreasing " ++
    "across each transition `θ*_(k)`.  Paper-proven mathematical " ++
    "result (the paper proves the elasticity acceleration); Lean " ++
    "derivation deferred.  NOT an atomic input — a derived result " ++
    "built from the profession primitives — hence `notInput` / " ++
    "`notCat3`.  NOT Lean-encoded: a faithful sound STATEMENT " ++
    "requires out-of-scope Mathlib calculus infrastructure " ++
    "(differentiability of the CES aggregator; share-weighted-" ++
    "elasticity algebra).  No Lean `axiom`/`def`/`theorem` " ++
    "declaration exists — encoding as `axiom` is unsound " ++
    "(`False`-injectable) and as a `def : Prop` with a conclusion-" ++
    "equalling constraining predicate is vacuous (tautological); " ++
    "this Ledger `GapEntry` is the honest encoding, tracked as a " ++
    "`gapOpen` Ledger-only entry.  Narrative content covered by " ++
    "Parts 2 + 3 limits."
  notes :=
    "Ledger-only entry (Ledger-only-entry exemption — see Ledger " ++
    "top docstring).  No Lean declaration; not retrievable by " ++
    "`#print axioms` — correct, since nothing asserts or consumes " ++
    "it.  Retrievable via `#eval` over `allGaps`."
}

/-- Proposition~\ref{prop:adjustment-margins} narrative portion,
    clause (ii): endogenous-AI-verification residual bound
    `δ(θ) < 1` — Ledger-only `gapOpen` `phenomenologicalConjecture`;
    not Lean-encoded.  A substantive empirical claim with a cohort-
    study resolution path, not a Lean derivation.  The derivable
    threshold-reduction conjunct is split out as the `theorem
    prop_adjustment_threshold_reduction_floor` — see
    `gap_prop_adjustment_threshold_reduction_CLOSED`. -/
def gap_prop_adjustment_narrative_OPEN : GapEntry := {
  name :=
    "prop:adjustment-margins (endogenous-AI-verification residual " ++
    "bound) — Ledger-only; not Lean-encoded"
  status := GapStatus.gapOpen
  inputCategory := InputCategory.cat3PaperNovel
  cat3SubType := Cat3SubType.phenomenologicalConjecture
  paperSource :=
    "Li 2026, `\\label{prop:adjustment-margins}` (narrative " ++
    "endogenous-AI-verification residual margin — paper's " ++
    "enumerate item 3, the substantive non-codifiability conjunct " ++
    "distinct from the closed-form career-extension and " ++
    "threshold-reduction margins)"
  attackHistory := [
    "Pre-audit (v0.1.0): classified `gapBlocked` as economic " ++
    "narrative.  R1 (2026-05-14) reclassified as " ++
    "`workingAssumption`.",
    "R2 (2026-05-14) Phase 4 post-publication compliance audit: " ++
    "`workingAssumption` must close before publication; paper is " ++
    "published.  Reclassified as `phenomenologicalConjecture`: the " ++
    "paper's published claims about the threshold-reduction floor " ++
    "`τ*_min` and the endogenous-AI-verification residual " ++
    "`δ(θ) < 1` are substantive claims about profession-specific " ++
    "tacit-knowledge floors awaiting empirical / interpretive " ++
    "validation.",
    "R3 audit: classification KEPT `phenomenologicalConjecture`.  " ++
    "R3 added a typed `axiom gap_prop_adjustment_narrative_OPEN` " ++
    "(Aggregation.lean) bundling threshold-reduction floor " ++
    "`θ* < 1 - τ*_min/T_j` and endogenous-AI residual `δ(θ) < 1`.",
    "R4 audit: converted from `axiom` to `def : Prop` AND " ++
    "decomposed.  The R3 axiom form was `False`-injectable (R4 " ++
    "hostile-audit machine-verification: free `delta` quantified " ++
    "with no constraint in the conjunct `delta θ < 1`; " ++
    "`delta := fun _ => 2` ⊢ `2 < 1` ⊢ `False`).  DECOMPOSITION: " ++
    "the first conjunct `E.thetaStar < 1 - tauStarMin/E.Tj` is " ++
    "DERIVABLE from `0 < tauStarMin < E.tauStar` and `0 < E.Tj` — " ++
    "it is split out as the real `theorem " ++
    "prop_adjustment_threshold_reduction_floor` (`gapClosed`, see " ++
    "`gap_prop_adjustment_threshold_reduction_CLOSED`).  The " ++
    "genuinely-deferred `delta θ < 1` conjunct was kept as the R4 " ++
    "`def : Prop` with a constraining hypothesis predicate " ++
    "`IsResidualSubstitutability`.",
    "R5 audit: the R4 `def : Prop` was found TAUTOLOGICAL — the " ++
    "constraining predicate `IsResidualSubstitutability delta` " ++
    "(`∀ θ, delta θ < 1`) was defined to be EXACTLY the conclusion " ++
    "the proposition asserts, so `gap_prop_adjustment_narrative_OPEN` " ++
    "reduced to `∀ delta, P delta → P delta`, provable by " ++
    "`fun _ h => h`; the paper's substantive claim was not " ++
    "actually formalized.",
    "R6 audit: removed the Lean declaration entirely — both the " ++
    "`def gap_prop_adjustment_narrative_OPEN : Prop` and the " ++
    "constraining `def IsResidualSubstitutability` are deleted " ++
    "from Aggregation.lean.  The claim is now tracked as a Ledger-" ++
    "only `gapOpen` `phenomenologicalConjecture` `GapEntry`.  " ++
    "Encoding any of {`axiom`, `def : Prop` with a conclusion-" ++
    "equalling constraining predicate} is an anti-pattern; honest " ++
    "tracking via this Ledger `GapEntry` is the correct encoding " ++
    "for a substantive empirical claim whose faithful resolution " ++
    "is a cohort study, not a Lean derivation.  Cat 3 reductionism " ++
    "(≥2 rounds): Round 1 Cat 1? NO — Mathlib has no named " ++
    "residual-substitutability primitive, and the claim is a " ++
    "substantive assertion about real-world AI substitution " ++
    "rates, not a Mathlib-derivable mathematical fact.  Round 2 " ++
    "Cat 2? NO — the endogenous-AI-verification residual " ++
    "substitution-rate `δ(θ)` and its uniform bound `δ(θ) < 1` " ++
    "(grounded in the non-codifiable verification residual of " ++
    "`\\label{def:verification}`) is paper " ++
    "`\\label{prop:adjustment-margins}`-specific, not an external " ++
    "published theorem.  Stands as `cat3PaperNovel " ++
    "phenomenologicalConjecture` — distinct from the three " ++
    "deferred-claim entries reclassified to `notInput notCat3` " ++
    "because its resolution path is empirical (cohort-study " ++
    "evidence) rather than a deferred Mathlib derivation, and a " ++
    "phenomenological conjecture about a real-world phenomenon IS " ++
    "a Cat 3 paper-novel claim per spec §3.4.6.",
    "R8 audit: classification reviewed and KEPT `cat3PaperNovel " ++
    "phenomenologicalConjecture`.  The other three deferred-claim " ++
    "entries (window invariance; sequential kinks; intermediate " ++
    "regime) are paper-proven MATHEMATICAL results with a deferred " ++
    "Mathlib-derivation resolution path, so they were reclassified " ++
    "to `notInput notCat3`.  This entry is different: the `δ(θ) < " ++
    "1` bound is a SUBSTANTIVE EMPIRICAL claim about the Polanyi " ++
    "verification residual (`\\label{def:verification}`), with a " ++
    "cohort-study / Cohen's-κ resolution path (`\\label{rem:" ++
    "residual-proxy}`) — per spec §3.4.6 a phenomenological " ++
    "conjecture is a genuine Cat 3 paper-novel claim, so the " ++
    "`cat3PaperNovel phenomenologicalConjecture` tagging stands."
  ]
  scope :=
    "Endogenous-AI-verification residual bound `δ(θ) < 1` " ++
    "uniformly — the non-codifiable verification residual " ++
    "(`def:verification`) keeps AI verification from fully " ++
    "substituting human verification.  Phenomenological conjecture " ++
    "about the operative non-substitutability predicate of " ++
    "`def:verification`: a substantive empirical claim, not a " ++
    "stipulative definitional atom and not a deferred Mathlib " ++
    "derivation.  NOT Lean-encoded: no Lean " ++
    "`axiom`/`def`/`theorem` declaration exists — encoding as " ++
    "`axiom` is unsound (`False`-injectable) and as a " ++
    "`def : Prop` with a conclusion-equalling constraining " ++
    "predicate is vacuous (tautological); this Ledger " ++
    "`GapEntry` is the honest encoding.  The threshold-reduction " ++
    "conjunct of the narrative is split out as the real `theorem " ++
    "prop_adjustment_threshold_reduction_floor`; the career-" ++
    "extension margin (the only narrative margin with substantive " ++
    "closed-form mathematics) is closed in " ++
    "`gap_prop_adjustment_career_CLOSED`."
  notes :=
    "Ledger-only entry (Ledger-only-entry exemption — see Ledger " ++
    "top docstring).  No Lean declaration; not retrievable by " ++
    "`#print axioms` — correct, since nothing asserts or consumes " ++
    "it.  Retrievable via `#eval` over `allGaps`.  Resolution " ++
    "path: cohort-study evidence on AI substitution rates by " ++
    "career stage.  The paper's five falsifiable predictions " ++
    "(Section `\\label{sec:predictions}`) provide the " ++
    "falsifiability anchor — in particular Prediction 2 (time-to-" ++
    "promotion lengthening, bounded by the extension-margin cap " ++
    "`θ*_ext`) and Prediction 4 (tacit-intensity ordering of " ++
    "collapse) operationalize the non-substitutability claim as " ++
    "testable cross-profession panel hypotheses."
}

/-- Proposition~\ref{prop:adjustment-margins} narrative portion,
    clause (i): threshold-reduction floor.  The derivable conjunct
    split out of the former `gap_prop_adjustment_narrative_OPEN`
    bundle. -/
def gap_prop_adjustment_threshold_reduction_CLOSED : GapEntry := {
  name := "prop_adjustment_threshold_reduction_floor"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource :=
    "Li 2026, `\\label{prop:adjustment-margins}` (narrative, " ++
    "clause (i) threshold-reduction floor)"
  attackHistory := [
    "R4 audit: added.  Agents K + L noted that the first conjunct " ++
    "of the former `gap_prop_adjustment_narrative_OPEN` axiom — " ++
    "`E.thetaStar < 1 - tauStarMin/E.Tj` — is DERIVABLE from the " ++
    "hypotheses `0 < tauStarMin < E.tauStar` and `0 < E.Tj` and " ++
    "should not be axiomatized.  Split out and proved as the real " ++
    "`theorem prop_adjustment_threshold_reduction_floor` " ++
    "(Aggregation.lean): `unfold thetaStar` reduces the goal to " ++
    "`τ*_min/T_j < τ*/T_j`, discharged by `div_lt_div_of_pos_right` " ++
    "+ `linarith`.  Derived `theorem` composing Mathlib arithmetic, " ++
    "so `inputCategory := notInput`, `cat3SubType := notCat3`."
  ]
  scope :=
    "Derived theorem (`notInput`).  For a profession-specific " ++
    "threshold-reduction floor `τ*_min ∈ (0, τ*)`, the floored " ++
    "collapse threshold `1 - τ*_min/T_j` lies strictly above " ++
    "`θ* = 1 - τ*/T_j`: reducing the promotion threshold to its " ++
    "floor shifts the collapse threshold rightward but cannot " ++
    "eliminate the collapse.  Proof: `unfold thetaStar` + " ++
    "`div_lt_div_of_pos_right` + `linarith`."
  notes :=
    "The paper hypothesis `τ*_min ∈ (0, τ*)` is carried in full " ++
    "(`0 < tauStarMin` AND `tauStarMin < E.tauStar`) to match the " ++
    "paper signature; the strict inequality follows from " ++
    "`tauStarMin < E.tauStar` and `0 < E.Tj` alone (the " ++
    "`0 < tauStarMin` clause is part of the paper-faithful " ++
    "hypothesis set but not load-bearing for the conclusion)."
}

/-- Corollary~\ref{cor:quant-predictions}: numerical calibration.
    Derived `theorem` (`rw` + `norm_num`); `gapClosed`. -/
def gap_cor_quant_predictions_CLOSED : GapEntry := {
  name := "cor_quant_predictions_calibration"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{cor:quant-predictions}`"
  attackHistory := [
    "Pre-audit (v0.1.0): classified `gapBlocked` as auxiliary " ++
    "numerical content. R1 (2026-05-14) reclassified to " ++
    "`cat1Mathlib gapOpen` — the numerical predictions are direct " ++
    "`norm_num`-substitution into the already-closed closed forms " ++
    "`θ* = 1 - τ*/T_j` and `s* = (1-η) Y Λ/(ν T_s)`.",
    "R3 audit: reclassified to `cat3PaperNovel workingAssumption " ++
    "gapOpen`; added a typed `axiom gap_cor_quant_predictions_OPEN` " ++
    "(Collapse.lean) faithfully encoding the Corollary's three " ++
    "collapse thresholds (`θ*_rad = 0.20`, `θ*_law = 0.29`, " ++
    "`θ*_SE = 0.40`).",
    "R4 audit: converted from `axiom` to `theorem`.  Agent J " ++
    "machine-verified that the axiom's conclusion follows from its " ++
    "own hypotheses by `rw` + `norm_num` WITHOUT the axiom — the " ++
    "axiom was redundant.  The derived `theorem` was proved " ++
    "`refine ⟨?_, ?_, ?_⟩ <;> (rw [h_...]; norm_num)`.  " ++
    "Reclassified: `status := gapClosed`, `inputCategory := " ++
    "notInput` (derived theorem composing `norm_num` / Mathlib " ++
    "arithmetic), `cat3SubType := notCat3`.  The R4 `theorem` " ++
    "retained the legacy identifier `gap_cor_quant_predictions_OPEN`.",
    "R6 audit: renamed the underlying Collapse.lean `theorem` from " ++
    "`gap_cor_quant_predictions_OPEN` to a status-suffixed " ++
    "identifier — the `_OPEN` suffix was stale (the entry is " ++
    "`gapClosed`, a derived `theorem`, not an open gap).",
    "R8 audit: renamed the underlying Collapse.lean `theorem` to " ++
    "the clean mathematical identifier `cor_quant_predictions_" ++
    "calibration` — a ledger-bookkeeping-style name (`gap_..._" ++
    "CLOSED`) is not an appropriate identifier for a Lean theorem.  " ++
    "The `GapEntry.name` field and the AxiomAudit.lean `#print " ++
    "axioms` reference were updated to match."
  ]
  scope :=
    "Derived theorem (`notInput`).  Numerical predictions " ++
    "(θ*_rad = 0.20, θ*_law = 0.29, θ*_SE = 0.40).  The Lean " ++
    "theorem `cor_quant_predictions_calibration` proves the " ++
    "arithmetic identities `1 - 0.80 = 0.20`, `1 - 0.71 = 0.29`, " ++
    "`1 - 0.60 = 0.40` (under hypotheses `tauStarRad/TjRad = 0.80` " ++
    "etc.) via `rw + norm_num`; it does NOT take an `Economy` " ++
    "instance as parameter and therefore does not directly " ++
    "instantiate `E.thetaStar`.  The paper's claim `θ*_rad = 0.20` " ++
    "follows by composing: (a) the paper's defining identity " ++
    "`thetaStar = 1 - tauStar/Tj` (Lean: `def thetaStar` in " ++
    "Collapse.lean by `rfl`), (b) the calibration substitution " ++
    "`tauStarRad / TjRad = 0.80` (paper Tables 1 + 2), and " ++
    "(c) this theorem's arithmetic identity.  Composing (a)+(b)+(c) " ++
    "into a single `E.thetaStar = 0.20` corollary specialized to a " ++
    "radiology-calibrated `Economy` instance is left for a future " ++
    "calibration-specific Economy specialization; the substantive " ++
    "Lean content of the present theorem is the arithmetic check " ++
    "matching the paper's numerical claim.  Encoded as the " ++
    "`theorem cor_quant_predictions_calibration` in Collapse.lean.  " ++
    "The lifetime Pigouvian \\$1.55M–\\$3.21M magnitudes of the " ++
    "Corollary's clause 4 are illustrative table values, not a " ++
    "separate Lean claim."
}

/-! ### Cat 3 paper-novel atomic entries (gapDefinitional)

  Definitional atoms 永不 close.  The genuine Cat 3 paper-novel
  atomic-input atoms of this formalization are the `Economy`
  carrier and the production-function-shape hypothesisPredicates
  (`IsCRS`, `IsCobbDouglas`, `IsCES`, `V2_TacitAccumulation`) —
  paper-stipulative definitional content, tracked here as
  `gapDefinitional` `cat3PaperNovel` entries with the appropriate
  Cat 3 sub-type.  Per the encoding-exemption documented in the
  top docstring, the Lean encoding is a `structure` (the `Economy`
  carrier) or a `Prop` (the hypothesisPredicates), not `axiom`,
  with the Ledger entry as the canonical record.  The concrete
  closed-form `def`s (`eBar`, `Vinf`, `thetaStar`, `wageRatio`,
  ...) whose defining equations hold by `rfl` are definitional
  infrastructure, NOT standalone Cat 3 atoms and NOT standalone
  Ledger entries — see the "Definitional infrastructure" section
  below. -/

/-- Cat 3 carrier: paper Definition `def:gve`
    Generation-Verification production economy. -/
def gap_Economy_carrier : GapEntry := {
  name := "Economy"
  status := GapStatus.gapDefinitional
  inputCategory := InputCategory.cat3PaperNovel
  cat3SubType := Cat3SubType.carrier
  paperSource := "Li 2026, `\\label{def:gve}` " ++
    "(Generation-Verification production economy)"
  attackHistory := [
    "R1 (2026-05-14) Cat 3 reductionism review: " ++
    "Round 1 Cat 1? NO (paper-novel structure, not Mathlib-defined). " ++
    "Round 2 Cat 2? NO (paper-original packaging, not external).",
    "R4 audit: corrected the `paperSource` tuple description.  The " ++
    "paper `\\label{def:gve}` introduces the economy as the tuple " ++
    "`(F, G, V, θ, K_AI, λ, ν, T, T_j, τ*, h)`; the Lean `Economy` " ++
    "structure is NOT a literal transcription of that tuple.  It " ++
    "carries 9 scalar fields — `LG`, `KAI`, `lam`, `nu`, `T`, `Tj`, " ++
    "`tauStar`, `eta`, `rho` — plus the paper's positivity / range " ++
    "constraints as proof fields; the production function `F` is " ++
    "FIXED to the CES form (paper Eq. `\\eqref{eq:ces}`, parametric " ++
    "in `(η, ρ, λ)`) rather than carried as a field, `G`/`V` are " ++
    "θ-parametrized derived quantities (`def G`, the verification " ++
    "stock `Vinf`), `θ` ranges as a free argument, and `h` is " ++
    "passed as an explicit function argument to `Vinf`.  Prior " ++
    "`paperSource` claimed a \"10-tuple\" — a count matching " ++
    "neither the paper's 11-element tuple nor the Lean structure's " ++
    "9 scalar fields; the bare count is dropped."
  ]
  scope := "Paper's primitive economy structure (`\\label{def:gve}`).  " ++
    "The Lean `Economy` structure carries 9 scalar fields " ++
    "`(L_G, K_AI, λ, ν, T, T_j, τ*, η, ρ)` plus positivity / range " ++
    "constraint proof fields; the CRS production function `F` of " ++
    "the paper tuple is fixed to the CES form (Eq. `\\eqref{eq:ces}`), " ++
    "and `G`, `V`, `θ`, `h` of the paper tuple are realized as " ++
    "derived quantities / free arguments rather than structure " ++
    "fields.  Definitional atom; 永不 close."
}

/-- Cat 3 hypothesisPredicate: paper's CRS shape predicate. -/
def gap_IsCRS_predicate : GapEntry := {
  name := "IsCRS"
  status := GapStatus.gapDefinitional
  inputCategory := InputCategory.cat3PaperNovel
  cat3SubType := Cat3SubType.hypothesisPredicate
  paperSource := "Li 2026, `\\label{thm:decomp}` (CRS hypothesis)"
  attackHistory := [
    "Audit (2026-05-14) introduced this predicate as the Cat 3 " ++
    "hypothesisPredicate antecedent of `axiom_euler_crs` to close " ++
    "soundness gap (previously axiom universally quantified over " ++
    "any `F`).",
    "Phase 0 hostile reductionism: Round 1 Cat 1? NO — Mathlib has " ++
    "no `IsHomogeneousOfDegreeOne` predicate primitive for binary " ++
    "real-valued functions; the closest concept is positively " ++
    "homogeneous on normed vector spaces (`IsPosHom`), but the " ++
    "paper's `F : ℝ → ℝ → ℝ` shape with `0 < t` factor scaling has " ++
    "no direct Mathlib match.  Round 2 Cat 2? Constant-returns-to-" ++
    "scale is from classical microeconomics (Euler 1755 homogeneous-" ++
    "function theorem) — could be encoded as a Cat 2 def. " ++
    "CLASSIFIED Cat 3 paper-novel hypothesisPredicate because: " ++
    "(i) the predicate is the paper's stipulated shape constraint " ++
    "on the production function `F` that anchors the Euler-identity " ++
    "decomposition argument; (ii) typing `IsCRS F` ties `F` to the " ++
    "paper's parameter binding in `axiom_euler_crs`, not to a free-" ++
    "floating Euler 1755 form.  The predicate as a paper-stipulated " ++
    "shape-predicate is the paper-novel content; the underlying " ++
    "Euler-identity argument (which IS Euler 1755) lives in " ++
    "`axiom_euler_crs` as Cat 2."
  ]
  scope := "Predicate `IsCRS F : Prop := ∀ t G V, 0 < t → " ++
    "F (t * G) (t * V) = t * F G V`. Constant-returns-to-scale " ++
    "hypothesis on production function `F : ℝ → ℝ → ℝ`. " ++
    "Definitional atom; 永不 close."
  notes :=
    "The predicate quantifies over all `t G V : ℝ` with `0 < t`; " ++
    "the paper's narrative restricts to `(G, V) ∈ ℝ_+^2`, but the " ++
    "Lean encoding allows arbitrary signs for `(G, V)`.  The " ++
    "downstream consumer `axiom_euler_crs` adds explicit positivity " ++
    "`0 < G, 0 < V` as separate antecedents, so the Lean restriction " ++
    "matches paper at the call site.  Tightening `IsCRS` itself to " ++
    "the positive quadrant would require encoding the positivity " ++
    "into the predicate definition; deferred for simplicity, with " ++
    "the call-site positivity providing equivalent protection."
}

/-- Cat 3 hypothesisPredicate: paper's Cobb-Douglas shape predicate. -/
def gap_IsCobbDouglas_predicate : GapEntry := {
  name := "IsCobbDouglas"
  status := GapStatus.gapDefinitional
  inputCategory := InputCategory.cat3PaperNovel
  cat3SubType := Cat3SubType.hypothesisPredicate
  paperSource := "Li 2026, `\\label{thm:credential}` (CD regime)"
  attackHistory := [
    "Audit (2026-05-14) introduced this predicate as the Cat 3 " ++
    "hypothesisPredicate antecedent of " ++
    "`axiom_cobb_douglas_factor_share` to close soundness gap.",
    "Phase 0 hostile reductionism: Round 1 Cat 1? NO — Mathlib has " ++
    "`Real.rpow` infrastructure but no `IsCobbDouglas` predicate " ++
    "primitive; predicate of shape `F G V = G^η · (λV)^(1-η)` is " ++
    "not a Mathlib-named concept.  Round 2 Cat 2? Cobb-Douglas form " ++
    "is from Cobb-Douglas 1928 (*American Economic Review* 18, " ++
    "139-165); could be encoded as a Cat 2 def referencing that " ++
    "paper.  CLASSIFIED Cat 3 paper-novel hypothesisPredicate " ++
    "because: (i) the predicate is named and used by Li 2026 " ++
    "specifically as the shape antecedent of `axiom_cobb_douglas_" ++
    "factor_share`; (ii) the shape is parametric in `(η, λ)` which " ++
    "are Li 2026's specific parameters threaded through the " ++
    "downstream paper-novel cohort accounting; (iii) typing " ++
    "`IsCobbDouglas F η lam` ties `F` to the paper's parameter " ++
    "binding, not to a free-floating Cobb-Douglas 1928 form.  Re-" ++
    "classification to Cat 2 would require dropping the `(η, λ)` " ++
    "parameters from the predicate, which would lose the paper's " ++
    "binding to the Economy parameters.  The predicate as a paper-" ++
    "stipulated shape-predicate is the paper-novel content."
  ]
  scope := "Predicate `IsCobbDouglas F η lam := ∀ G V, 0 < G → " ++
    "0 < V → F G V = G^η · (lam · V)^(1-η)`. Cobb-Douglas shape " ++
    "hypothesis. Definitional atom; 永不 close."
}

/-- Cat 3 hypothesisPredicate: paper's CES shape predicate
    (Eq. `\eqref{eq:ces}`). -/
def gap_IsCES_predicate : GapEntry := {
  name := "IsCES"
  status := GapStatus.gapDefinitional
  inputCategory := InputCategory.cat3PaperNovel
  cat3SubType := Cat3SubType.hypothesisPredicate
  paperSource := "Li 2026, Eq. `\\eqref{eq:ces}`"
  attackHistory := [
    "Audit (2026-05-14) introduced this predicate as the Cat 3 " ++
    "hypothesisPredicate antecedent of `axiom_ces_wage_ratio` to " ++
    "close soundness gap.",
    "Phase 0 hostile reductionism: Round 1 Cat 1? NO — Mathlib " ++
    "lacks a CES-form predicate primitive (`Real.rpow` exists but " ++
    "no named CES typing).  Round 2 Cat 2? CES form is from Arrow, " ++
    "Chenery, Minhas, Solow 1961 (*Review of Economics and " ++
    "Statistics* 43, 225-250, the original CES production function " ++
    "paper); could be encoded as a Cat 2 def referencing ACMS 1961.  " ++
    "CLASSIFIED Cat 3 paper-novel hypothesisPredicate because: " ++
    "(i) the predicate is named and used by Li 2026 specifically " ++
    "as the shape antecedent of `axiom_ces_wage_ratio`; (ii) the " ++
    "shape is parametric in `(η, ρ, λ)` which are Li 2026's specific " ++
    "parameters bound to the Economy `(eta, rho, lam)` fields; " ++
    "(iii) typing `IsCES F η rho lam` ties `F` to the paper's " ++
    "parameter binding, not to a free-floating ACMS 1961 form.  " ++
    "Re-classification to Cat 2 would require dropping the `(η, ρ, " ++
    "λ)` parameters from the predicate, losing the paper's binding " ++
    "to the Economy parameters.  The predicate as a paper-stipulated " ++
    "shape-predicate is the paper-novel content."
  ]
  scope := "Predicate `IsCES F η rho lam := ∀ G V, 0 < G → 0 < V → " ++
    "F G V = (η · G^ρ + (1-η) · (lam · V)^ρ)^(1/ρ)`. CES shape " ++
    "hypothesis. Definitional atom; 永不 close."
}

/-! ### Definitional infrastructure (NOT standalone Cat 3 atoms)

  Cat 3 ratio guard.  The concrete Lean `def`s — `eBar`, `Vinf`,
  `thetaStar`, `wageRatio`, `Gstar`, `thetaInv`, `Lambda`, `Vreq`,
  `hPow`, `gSmooth`, `transientStock`, `MPpriv`, `MPsoc`,
  `externalityResidual`, `wedge`, `internalizedWedge`,
  `pigouvianSubsidy_CD`, `wageRatioRec`, `thetaInvRec`, `thetaEndo`,
  `hysteresisDeficit`, `recoveryStock`, `thetaStarExt`,
  `leontiefSeniorRent`, `rBarZero`, `rBarMax` — are NOT standalone
  Cat 3 atoms.  A CONCRETE `def X := <closed-form expression>` whose
  defining equation holds by `rfl` is NOT a Cat 3 paper-novel ATOM:
  a `structuralEquation` Cat 3 atom is an OPAQUE primitive carrying
  a STATED defining axiom (e.g. `V_dyn` opaque + `axiom V_dyn_def`);
  a concrete `def` is settled definitional NOTATION, neither a "gap"
  nor an "input atom".  (Per-entry attack history of this
  reclassification lives in the `attackHistory` fields of the
  affected parent theorem entries.)

  These closed-form `def`s are therefore NOT tracked as standalone
  Ledger entries.  Each is definitional infrastructure built FROM
  the genuine Cat 3 atoms (`Economy` carrier; the `IsCRS` /
  `IsCobbDouglas` / `IsCES` / `V2_TacitAccumulation`
  hypothesisPredicates) plus Economy fields, and appears inside
  theorem statements.  Each is documented under the `scope` of the
  parent `gapClosed` theorem entry that consumes it:

    * `eBar` (`\label{def:cohort}`, `ē(θ) = (1-θ) T_j`) — consumed
      throughout `Collapse.lean` / `Credential.lean`; documented
      under `gap_thm_collapse_below_CLOSED` and the collapse-family
      entries.  `eBar` is a concrete `def eBar θ := (1 - θ) * E.Tj`
      whose defining equation holds by `rfl` — by the criterion
      above it is definitional infrastructure, NOT a standalone
      Cat 3 atom and NOT a standalone Ledger entry.
    * `Vinf` (`\label{lem:steady-state}`,
      `V_∞ θ g h = ν T_s g(ē) h(ē)`) — consumed throughout
      `Collapse.lean`; the `rfl` bridge `steady_state_stock_identity`
      (Axioms.lean) is the explicit unfolding-by-`rfl` theorem
      consumed by `cobb_douglas_steady_state_identity` and
      `cobb_douglas_steady_state_identity_from_axiom` (not carrying
      `@[simp]`; downstream call sites `rw` or `unfold` it
      explicitly).  `Vinf` is a concrete
      `def Vinf θ g h := E.nu * E.Ts * g (E.eBar θ) *
      h (E.eBar θ)` whose defining equation holds by `rfl` —
      definitional infrastructure, NOT a standalone Ledger entry.
    * `thetaStar` (`\label{eq:thetastar}`, `θ* = 1 - τ*/T_j`) —
      consumed throughout `Collapse.lean`.  `thetaStar` is a
      concrete `def thetaStar := 1 - E.tauStar / E.Tj` whose
      defining equation holds by `rfl` — definitional
      infrastructure, NOT a standalone Ledger entry.
    * `wageRatio` — `gap_thm_inversion_wage_ratio_CLOSED`,
      `gap_wageRatio_eq_ces_marginal_product_ratio_CLOSED`
    * `Gstar`, `thetaInv` — `gap_thm_inversion_threshold_CLOSED`,
      `gap_thm_inversion_threshold_monotone_CLOSED`
    * `rBarZero`, `rBarMax` — `gap_cor_bounded_AI_CLOSED`
    * `Lambda`, `wedge`, `MPpriv`, `MPsoc`, `externalityResidual` —
      `gap_thm_externality_wedge_CLOSED`,
      `gap_thm_externality_nonneg_CLOSED`
    * `pigouvianSubsidy_CD` — `gap_thm_externality_pigouvian_CLOSED`
    * `internalizedWedge` — `gap_prop_internalization_CLOSED`
    * `Vreq`, `thetaInvRec`, `wageRatioRec` —
      `gap_thm_recursive_threshold_CLOSED`,
      `gap_thm_recursive_wedge_CLOSED`
    * `transientStock`, `gSmooth`, `hPow` —
      `gap_thm_collapse_transient_CLOSED`,
      `gap_prop_smooth_collapse_CLOSED`,
      `gap_thm_collapse_below_CLOSED`
    * `thetaEndo`, `hysteresisDeficit`, `recoveryStock` —
      `gap_thm_endogenous_ai_corner_CLOSED`,
      `gap_thm_endogenous_ai_hysteresis_CLOSED`
    * `thetaStarExt` — `gap_prop_adjustment_career_CLOSED`
    * `leontiefSeniorRent` — `gap_thm_credential_leontief_CLOSED`

  `eBar` / `Vinf` / `thetaStar` are the paper's FOUNDATIONAL
  closed-form `def`s directly on the Economy primitives (introduced
  in the Section 2 model setup), as distinct from the derived
  closed-form notation built on top — but all are concrete `def`s
  holding by `rfl`, hence ALL are definitional infrastructure, none
  is a standalone Cat 3 atom, and none has a standalone Ledger
  `GapEntry`.

  The GENUINE Cat 3 paper-novel atomic-input atoms that ARE tracked
  as standalone `GapEntry` records are exactly: the `Economy`
  carrier and the four hypothesisPredicates `IsCRS` /
  `IsCobbDouglas` / `IsCES` / `V2_TacitAccumulation`.  (One further
  `cat3PaperNovel` standalone entry — `gap_prop_adjustment_narrative_OPEN`,
  a `phenomenologicalConjecture` — is a substantive empirical claim,
  not a definitional atom; it is tracked among the deferred
  paper-claim entries above.) -/

/-- Theorem~\ref{thm:externality} (by-construction externality
    residual identity `MP_J^S - MP_J^P = externalityResidual`).
    Derived theorem (`unfold + ring`); `gapClosed notInput`. -/
def gap_thm_externality_residual_identity_CLOSED : GapEntry := {
  name := "thm_externality_residual_identity"
  status := GapStatus.gapClosed
  inputCategory := InputCategory.notInput
  cat3SubType := Cat3SubType.notCat3
  paperSource := "Li 2026, `\\label{thm:externality}` " ++
    "(residual identity)"
  attackHistory := [
    "R3 audit: added dedicated Ledger entry and classified as " ++
    "Cat 3 `gapDefinitional structuralEquation`, on the reasoning " ++
    "that `MPsoc` is paper-DEFINED as `MPpriv + wV·gE·hE·Λ` so the " ++
    "residual identity was paper-stipulative structural content.",
    "R4 audit: reclassified `gapDefinitional structuralEquation " ++
    "cat3PaperNovel` → `gapClosed notInput notCat3`.  The Lean " ++
    "theorem `thm_externality_residual_identity` " ++
    "(`MP_J^S - MP_J^P = externalityResidual`) is a DERIVED " ++
    "theorem proved by `unfold MPsoc MPpriv externalityResidual; " ++
    "ring` — it composes the concrete `MPsoc` / `MPpriv` / " ++
    "`externalityResidual` `def`s (themselves definitional " ++
    "infrastructure, no longer standalone Cat 3 atoms after the " ++
    "R4 Cat 3 ratio guard) via Mathlib `ring`.  Per spec §0 a " ++
    "derived theorem composing Mathlib lemmas is `notInput` / " ++
    "`notCat3` / `gapClosed`, not a Cat 3 definitional atom.  " ++
    "Parallel to the R4 treatment of `prop_internalization`."
  ]
  scope := "Derived theorem (`notInput`).  Identity " ++
    "`MPsoc wG wV gE hE Lambda θ - MPpriv wG θ = " ++
    "externalityResidual wV gE hE Lambda`.  Proved by `unfold " ++
    "MPsoc MPpriv externalityResidual; ring` — a by-construction " ++
    "consequence of the `MPsoc` def `MPpriv + wV·gE·hE·Λ` and the " ++
    "`externalityResidual` def `wV·gE·hE·Λ`.  The `MPsoc` / " ++
    "`MPpriv` / `externalityResidual` `def`s are definitional " ++
    "infrastructure documented under " ++
    "`gap_thm_externality_wedge_CLOSED` / " ++
    "`gap_thm_externality_nonneg_CLOSED`."
}

/-- Cat 3 hypothesisPredicate: paper's V2 (tacit accumulation)
    diagnostic predicate. -/
def gap_V2_TacitAccumulation_predicate : GapEntry := {
  name := "V2_TacitAccumulation"
  status := GapStatus.gapDefinitional
  inputCategory := InputCategory.cat3PaperNovel
  cat3SubType := Cat3SubType.hypothesisPredicate
  paperSource := "Li 2026, `\\label{def:diagnostic}` (V2 condition)"
  attackHistory := [
    "Cat 3 reductionism: Round 1 Cat 1? NO — Mathlib has " ++
    "`Monotone` and equality-at-zero but no named `V2_TacitAccumulation` " ++
    "predicate.  Round 2 Cat 2? NO — paper's specific V2 condition " ++
    "naming (Li 2026 `def:diagnostic`).",
    "R2 (2026-05-14) added Ledger entry; at that round the " ++
    "predicate had no downstream Lean consumer.  Documented as " ++
    "paper's V2 predicate (h(0) = 0 ∧ Monotone h); V1/V3 are " ++
    "absorbed into the carrier types `Vinf` and `eBar` per " ++
    "def:diagnostic structural reformulation; V2 remains a " ++
    "constraint on the apprenticeship technology `h`.",
    "R14 (2026-05-15) Phase 4 phantom-downstream patch: fresh " ++
    "audit flagged the Cat 3 hypothesisPredicate semantics " ++
    "tension — spec §3.4.2 says hypothesisPredicates are 'used as " ++
    "antecedent in downstream theorems', but the V2 predicate had " ++
    "no Lean consumer (only paper-section anchoring).  Resolution: " ++
    "added the consuming theorem " ++
    "`Vinf_zero_at_theta_one_under_V2` (Basic.lean) — under V2, " ++
    "`V_∞(θ=1, g, h) = 0` because `eBar 1 = 0` and " ++
    "`V2.h_zero_at_zero : h 0 = 0`.  This is paper-meaningful: at " ++
    "full AI substitution junior experience drops to zero, and " ++
    "V2's tacit-accumulation requirement forces accumulated " ++
    "verification capability also to zero.  V2 is now genuinely " ++
    "Lean-load-bearing, verifiable by `#print axioms " ++
    "Vinf_zero_at_theta_one_under_V2`.",
    "R16 (2026-05-15) Phase 4 field-consumption audit: fresh " ++
    "audit observed that R14's consumer used only the " ++
    "`h_zero_at_zero` field; the `h_monotone` field remained " ++
    "declared-but-unconsumed.  Resolution: added a second " ++
    "consuming theorem `h_eBar_nonneg_under_V2` (Basic.lean) " ++
    "that consumes `h_monotone` (and `h_zero_at_zero` as a " ++
    "secondary): for `θ ≤ 1`, `ē(θ) ≥ 0`, so `h_monotone` gives " ++
    "`h(0) ≤ h(ē(θ))`, and `h_zero_at_zero` rewrites `h(0) = 0` " ++
    "to deliver `0 ≤ h(ē(θ))`.  Both V2 fields are now " ++
    "independently Lean-load-bearing, verifiable by " ++
    "`#print axioms` on each consumer."
  ]
  scope := "Predicate `V2_TacitAccumulation h : Prop` with fields " ++
    "`h_zero_at_zero : h 0 = 0` and `h_monotone : Monotone h`.  " ++
    "Encodes paper's `def:diagnostic` V2 condition. Definitional " ++
    "atom; 永不 close.  V1 (non-substitutability) and V3 (experience " ++
    "displacement) are structural properties of the carrier types " ++
    "themselves and not separately encoded.  Both fields are " ++
    "Lean-load-bearing: `h_zero_at_zero` is consumed by " ++
    "`Vinf_zero_at_theta_one_under_V2` (Basic.lean) and " ++
    "`h_monotone` is consumed by `h_eBar_nonneg_under_V2` " ++
    "(Basic.lean), making V2 a genuine paper-load-bearing " ++
    "antecedent rather than a paper-section anchor only."
  notes := "Cat 3 hypothesisPredicate: paper-stipulative regime " ++
    "predicate, definitional atom (永不 close).  Lean-load-bearing " ++
    "in both fields: " ++
    "(i) `Vinf_zero_at_theta_one_under_V2` (Basic.lean) consumes " ++
    "`h_zero_at_zero` — under V2, `V_∞(θ=1, g, h) = 0` follows " ++
    "because `eBar 1 = 0` and `V2.h_zero_at_zero : h 0 = 0` (the " ++
    "structural consequence that makes V2 paper-load-bearing — at " ++
    "full AI substitution junior experience drops to zero and " ++
    "V2's tacit-accumulation requirement forces the accumulated " ++
    "verification capability also to zero); " ++
    "(ii) `h_eBar_nonneg_under_V2` (Basic.lean) consumes " ++
    "`h_monotone` (and `h_zero_at_zero` as a secondary) — for " ++
    "`θ ≤ 1`, `0 ≤ ē(θ)` and V2's monotonicity gives " ++
    "`h(0) ≤ h(ē(θ))`, which combined with `h_zero_at_zero` " ++
    "yields `0 ≤ h(ē(θ))`.  Verifiable by `#print axioms` on " ++
    "each consumer (both are listed in `AxiomAudit.lean`)."
}

/-! ### Aggregated ledger inventory -/

/-- All gap entries in canonical order. -/
def allGaps : List GapEntry := [
  -- Cat 2 axioms (gapOpen: declared in Axioms.lean, accepted on
  -- external authority Euler 1755 / Cobb-Douglas 1928 / ACMS 1961)
  gap_axiom_euler_crs,
  gap_axiom_ces_wage_ratio,
  gap_axiom_cobb_douglas_factor_share,
  -- Cat 3 paper-novel atoms (gapDefinitional): the `Economy`
  -- carrier + the four hypothesisPredicates.  The concrete
  -- closed-form `def`s — `eBar`, `Vinf`, `thetaStar`, `wageRatio`,
  -- `Gstar`, `thetaInv`, `Lambda`, `Vreq`, `hPow`, `gSmooth`,
  -- `transientStock`, `MPpriv`, `MPsoc`, `externalityResidual`,
  -- `wedge`, `internalizedWedge`, `pigouvianSubsidy_CD`,
  -- `wageRatioRec`, `thetaInvRec`, `thetaEndo`, `hysteresisDeficit`,
  -- `recoveryStock`, `thetaStarExt`, `leontiefSeniorRent`,
  -- `rBarZero`, `rBarMax` — are definitional infrastructure (a
  -- concrete `def` holding by `rfl` is settled notation, not a
  -- Cat 3 atom), NOT standalone Ledger entries; each is documented
  -- under its parent theorem's `scope` / the "Definitional
  -- infrastructure" section.
  gap_Economy_carrier,
  gap_IsCRS_predicate,
  gap_IsCobbDouglas_predicate,
  gap_IsCES_predicate,
  gap_V2_TacitAccumulation_predicate,
  -- gapClosed: paper-level theorems formalized
  gap_thm_decomp_CLOSED,
  gap_thm_inversion_threshold_CLOSED,
  gap_thm_inversion_threshold_monotone_CLOSED,
  gap_thm_inversion_wage_ratio_CLOSED,
  gap_wageRatio_eq_ces_marginal_product_ratio_CLOSED,
  gap_cor_bounded_AI_CLOSED,
  gap_thm_collapse_below_CLOSED,
  gap_thm_collapse_jump_CLOSED,
  gap_thm_collapse_jump_diff_CLOSED,
  gap_thm_collapse_above_CLOSED,
  gap_thm_collapse_transient_CLOSED,
  gap_thm_collapse_general_h_CLOSED,
  gap_prop_smooth_collapse_CLOSED,
  gap_thm_credential_CLOSED,
  gap_thm_credential_leontief_CLOSED,
  gap_thm_credential_multiplicative_CLOSED,
  gap_prop_junior_senior_CLOSED,
  gap_thm_externality_wedge_CLOSED,
  gap_thm_externality_nonneg_CLOSED,
  gap_thm_externality_pigouvian_CLOSED,
  gap_thm_externality_residual_identity_CLOSED,
  gap_prop_internalization_CLOSED,
  gap_prop_decentralized_theta_CLOSED,
  gap_thm_recursive_threshold_CLOSED,
  gap_thm_recursive_wedge_CLOSED,
  gap_prop_boundary_CLOSED,
  gap_thm_aggregation_CD_CLOSED,
  gap_thm_aggregation_PS_CLOSED,
  gap_prop_adjustment_career_CLOSED,
  gap_prop_adjustment_threshold_reduction_CLOSED,
  gap_thm_endogenous_ai_existence_PARTIAL,
  gap_thm_endogenous_ai_uniqueness_CLOSED,
  gap_thm_endogenous_ai_corner_CLOSED,
  gap_thm_endogenous_ai_hysteresis_CLOSED,
  -- numerical calibration: derived `theorem` (`rw` + `norm_num`),
  -- `gapClosed notInput`
  gap_cor_quant_predictions_CLOSED,
  -- gapOpen: paper claims tracked as Ledger-only `GapEntry` records
  -- WITHOUT a Lean declaration (Ledger-only-entry exemption, top
  -- docstring).  Group A: four paper-proven mathematical results
  -- whose Lean derivation requires Mathlib infrastructure beyond
  -- this formalization's scope (three tagged `notInput notCat3`,
  -- one tagged `cat3PaperNovel phenomenologicalConjecture` with a
  -- cohort-study resolution path).  Group B: one claim satisfied
  -- by construction (`thetaStar`/`VinfHard` are defined without a
  -- μ parameter; no Lean theorem is or can be written).
  gap_window_invariance_OPEN,
  gap_aggregation_sequential_kinks_OPEN,
  gap_aggregation_intermediate_regime_OPEN,
  gap_prop_adjustment_narrative_OPEN,
  gap_thm_recursive_invariance_OPEN
]

/-- Canonical status-count function.  Returns counts in the
    canonical 7-tier order: `(open, partial, blocked, deadEnd,
    closed, closedConditional, definitional)`. -/
def countByStatus : Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  let cnt (s : GapStatus) : Nat :=
    (allGaps.filter (fun g => g.status = s)).length
  ( cnt GapStatus.gapOpen
  , cnt GapStatus.gapPartial
  , cnt GapStatus.gapBlocked
  , cnt GapStatus.gapDeadEnd
  , cnt GapStatus.gapClosed
  , cnt GapStatus.gapClosedConditional
  , cnt GapStatus.gapDefinitional )

/-- InputCategory-keyed counts: `(cat1Mathlib, cat2External,
    cat3PaperNovel, notInput)`. -/
def inputCategoryCounts : Nat × Nat × Nat × Nat :=
  let cnt (c : InputCategory) : Nat :=
    (allGaps.filter (fun g => g.inputCategory = c)).length
  ( cnt InputCategory.cat1Mathlib
  , cnt InputCategory.cat2External
  , cnt InputCategory.cat3PaperNovel
  , cnt InputCategory.notInput )

/-- Cat3SubType-keyed counts (carrier, hypothesisPredicate,
    structuralEquation, workingAssumption, conditionalHypothesis,
    phenomenologicalConjecture, notCat3). -/
def cat3SubTypeCounts : Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  let cnt (s : Cat3SubType) : Nat :=
    (allGaps.filter (fun g => g.cat3SubType = s)).length
  ( cnt Cat3SubType.carrier
  , cnt Cat3SubType.hypothesisPredicate
  , cnt Cat3SubType.structuralEquation
  , cnt Cat3SubType.workingAssumption
  , cnt Cat3SubType.conditionalHypothesis
  , cnt Cat3SubType.phenomenologicalConjecture
  , cnt Cat3SubType.notCat3 )

/-- Cross-table `(status × inputCategory) → Nat`.  Returns a 7×4
    table flattened to a list of `(GapStatus, InputCategory, Nat)`
    triples. -/
def gapCrossTable : List (GapStatus × InputCategory × Nat) :=
  let statuses : List GapStatus :=
    [ GapStatus.gapOpen, GapStatus.gapPartial, GapStatus.gapBlocked,
      GapStatus.gapDeadEnd, GapStatus.gapClosed,
      GapStatus.gapClosedConditional, GapStatus.gapDefinitional ]
  let cats : List InputCategory :=
    [ InputCategory.cat1Mathlib, InputCategory.cat2External,
      InputCategory.cat3PaperNovel, InputCategory.notInput ]
  statuses.flatMap (fun s =>
    cats.map (fun c =>
      (s, c,
        (allGaps.filter
          (fun g => decide (g.status = s) && decide (g.inputCategory = c))).length)))

/-- Cat 3 ratio guard: `Cat3 / (Cat1 + Cat2 + Cat3)` as a per-mille
    integer (× 1000, rounded down).  The denominator is the count of
    genuine atomic-input entries (Cat 1 + Cat 2 + Cat 3); `notInput`
    derived theorems and `notInput` deferred-derived-result entries
    are excluded since they are not atomic inputs.  The spec flags
    a ratio above 500‰ for a ≥2-round hostile reduction.

    This project's ratio is genuinely high: the atomic-input layer
    is dominated by the paper-novel `Economy` carrier + the four
    production-function-shape hypothesisPredicates +
    one phenomenologicalConjecture, against only the three Cat 2
    textbook axioms and zero Cat 1 atoms (every Mathlib invocation
    is internal to a `notInput` derived theorem).  This is justified
    novelty, not laziness: every `cat3PaperNovel`
    entry has its ≥2-round reductionism check (Cat 1? Cat 2?)
    recorded in its `attackHistory`, all returning CLEAR-NO, and
    each is a real paper primitive (a carrier, a regime predicate,
    or a substantive phenomenological conjecture) — not a
    higher-level claim reachable for an axiom too fast. -/
def cat3RatioPerMille : Nat :=
  let c := inputCategoryCounts
  let cat1 := c.1
  let cat2 := c.2.1
  let cat3 := c.2.2.1
  let denom := cat1 + cat2 + cat3
  if denom = 0 then 0 else cat3 * 1000 / denom

#eval s!"VerificationAsymmetry gap-ledger inventory (status):    open={(countByStatus).1} partial={(countByStatus).2.1} blocked={(countByStatus).2.2.1} deadEnd={(countByStatus).2.2.2.1} closed={(countByStatus).2.2.2.2.1} closedConditional={(countByStatus).2.2.2.2.2.1} definitional={(countByStatus).2.2.2.2.2.2}"

#eval s!"VerificationAsymmetry gap-ledger inventory (input):     cat1Mathlib={(inputCategoryCounts).1} cat2External={(inputCategoryCounts).2.1} cat3PaperNovel={(inputCategoryCounts).2.2.1} notInput={(inputCategoryCounts).2.2.2}"

#eval s!"VerificationAsymmetry gap-ledger inventory (Cat 3 sub): carrier={(cat3SubTypeCounts).1} hypothesisPredicate={(cat3SubTypeCounts).2.1} structuralEquation={(cat3SubTypeCounts).2.2.1} workingAssumption={(cat3SubTypeCounts).2.2.2.1} conditionalHypothesis={(cat3SubTypeCounts).2.2.2.2.1} phenomenologicalConjecture={(cat3SubTypeCounts).2.2.2.2.2.1} notCat3={(cat3SubTypeCounts).2.2.2.2.2.2}"

#eval s!"Cat 3 ratio (Cat3 / (Cat1+Cat2+Cat3)): {cat3RatioPerMille}‰"

#eval s!"Total entries: {allGaps.length}"

/-! ### Inventory summary

  This summary deliberately bakes NO fixed counts or per-entry
  classifications: the `#eval` printouts above — `countByStatus`,
  `inputCategoryCounts`, `cat3SubTypeCounts`, `allGaps.length` — are
  the canonical authority for the live inventory.  The shape of the
  inventory:

  * The bulk of paper-level content is `notInput` derived theorems
    whose proofs compose Mathlib real-analytic identities
    (`Real.rpow_*`, `field_simp`, `ring`), Finset sums/products, and
    1-D IVT, together with the Cat 2 axioms and the Cat 3
    definitional atoms.
  * Cat 2: three external textbook `axiom`s with explicit Cat 3
    hypothesisPredicate antecedents — `axiom_euler_crs`,
    `axiom_ces_wage_ratio`, `axiom_cobb_douglas_factor_share`.  The
    antecedents (`IsCRS`/`IsCobbDouglas`/`IsCES`, `HasDerivAt`,
    positivity) make the axioms sound.  These are the ONLY `axiom`
    declarations in the project.
  * Cat 3 definitional atoms (`gapDefinitional` `cat3PaperNovel`):
    the `Economy` carrier and the hypothesisPredicates `IsCRS`,
    `IsCobbDouglas`, `IsCES`, `V2_TacitAccumulation` — the genuine
    Cat 3 paper-novel atomic inputs, each a standalone Ledger
    `GapEntry`.  One further `gapOpen` Ledger-only entry — the
    by-construction μ-invariance commitment of `\label{thm:recursive}`
    Part 3 (`gap_thm_recursive_invariance_OPEN`) — has no Lean
    declaration and is tagged `notInput` `notCat3` (it records the
    absence of a μ parameter in the `thetaStar` / `VinfHard`
    carriers, a meta-observation, not an atomic input; status
    `gapOpen` rather than `gapDefinitional` per the §1.1 binding of
    `gapDefinitional` to Cat 3 sub-types).  The concrete closed-form `def`s — `eBar`
    (`\label{def:cohort}`), `Vinf` (`\label{lem:steady-state}`),
    `thetaStar` (`\label{eq:thetastar}`), and the further derived
    `def`s (`wageRatio`, `Gstar`, `Lambda`, `wedge`, ...) — are
    definitional infrastructure, NOT standalone Cat 3 atoms and NOT
    standalone Ledger entries; see the "Definitional infrastructure"
    section above.
  * Cat 3 deferred paper claims (`gapOpen`, Ledger-only): three
    paper-proven mathematical results whose Lean derivation is
    deferred — `gap_window_invariance_OPEN`,
    `gap_aggregation_sequential_kinks_OPEN`,
    `gap_aggregation_intermediate_regime_OPEN` — tagged `notInput`
    `notCat3` (un-formalized derived results, not atomic inputs);
    and one `cat3PaperNovel` `phenomenologicalConjecture`
    (`gap_prop_adjustment_narrative_OPEN`).  Each is tracked as a
    Ledger `GapEntry` record WITHOUT a Lean `axiom`/`def`/`theorem`
    declaration (Ledger-only-entry exemption, top docstring).  The
    numerical-calibration corollary `cor_quant_predictions_calibration`
    and the threshold-reduction conjunct
    `prop_adjustment_threshold_reduction_floor` are derived
    `theorem`s (`gapClosed notInput`).

  Lean kernel (Cat 0; not declared here): propext, Classical.choice,
  Quot.sound. -/

end VerificationAsymmetry.Ledger
