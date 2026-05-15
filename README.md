# Generation-Verification Asymmetry — Lean 4 Formalization

Formal verification of the theorems and propositions of

> Li, Alex Chengyu. *Generation--Verification Asymmetry Inversion and
> Apprenticeship Pipeline Collapse Under AI Substitution.* 2026.

**Paper:**
- SSRN abstract id [6718418](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6718418)
- Zenodo DOI: [10.5281/zenodo.20038848](https://doi.org/10.5281/zenodo.20038848)

## Status

The formalization machine-checks the **structural mathematics** of the
paper inside Lean 4 + Mathlib.  Every paper-internal deduction
captured here is a genuine Lean 4 theorem — **zero `sorry`**.  Five
paper claims are tracked as `gapOpen` Ledger-only `GapEntry` records
with no corresponding Lean `axiom`/`def`/`theorem` declaration: four
whose Lean derivation is deferred for out-of-scope Mathlib
infrastructure (window invariance, sequential aggregation kinks,
intermediate-regime elasticity, the endogenous-AI-verification
residual bound of the adjustment-margins narrative), plus one
satisfied by construction (the μ-invariance commitment of
`\label{thm:recursive}` Part 3 — `thetaStar` / `VinfHard` are defined
without a μ parameter, so the paper claim is encoded in the type
signatures themselves).  Earlier encoding attempts for the four
deferred claims (`axiom` with a free abstract functional — unsound,
`False`-injectable; `def : Prop` with a constraining predicate
equalling the conclusion — vacuous tautology) were retracted; the
honest encoding is the Ledger entry itself.  The numerical-calibration corollary and the
threshold-reduction conjunct of the adjustment-margins narrative are
derived `theorem`s.  Only the three Cat 2 textbook axioms remain as
`axiom` declarations; see `Ledger.lean` for current scope.

The trust boundary is explicit.  Each entry in the inventory below
is honest about whether its claim is Lean-proof-load-bearing
(consumed in the `#print axioms` dependency chain of a downstream
theorem) or paper-narrative reference (formalized reference point
without Lean-proof consumption).

* **Cat 1 (Mathlib-derivable atoms).**  This project has **zero**
  standalone `cat1Mathlib` Ledger entries: it does not enumerate
  individual Mathlib lemmas as atomic inputs.  The bulk of
  paper-level content is instead **`notInput` derived theorems**
  whose proofs *compose* Mathlib lemmas internally — `Real.rpow`
  arithmetic, `Finset` sums / products, 1-D IVT (the paper's
  "Brouwer fixed-point" reduces to intermediate-value theorem on
  the real line) — together with the three Cat 2 axioms and the
  Cat 3 definitional atoms, over the standard Lean kernel
  (`propext`, `Classical.choice`, `Quot.sound`).  The live
  `inputCategoryCounts` `#eval` in `Ledger.lean` is authoritative.
* **Cat 2 (external textbook axioms).**  Three atomic axioms with
  explicit Cat 3 hypothesisPredicate antecedents declared in
  [`VerificationAsymmetry/Axioms.lean`](VerificationAsymmetry/Axioms.lean):
  * `axiom_euler_crs` — Euler's identity for CRS production.
    Citations: Euler 1755 (original) / Mas-Colell, Whinston, Green
    1995 §5.B.2 (modern textbook).
    **Lean role**: load-bearing — consumed by `thm_decomp`
    (verifiable by `#print axioms thm_decomp`).
  * `axiom_ces_wage_ratio` — CES marginal-product wage-ratio closed
    form.
    Citations: Arrow-Chenery-Minhas-Solow 1961 (original CES paper)
    / Acemoglu 2009 §15 (modern textbook).
    **Lean role**: load-bearing — consumed by
    `wageRatio_eq_ces_marginal_product_ratio`, which establishes
    that the wage ratio `w_V / w_G` equals the closed-form algebraic
    expression `((1-η)/η)·λ^ρ·(G/V)^(1-ρ)` for arbitrary positive
    `G` (verifiable by `#print axioms wageRatio_eq_ces_marginal_product_ratio`).
    Identification with the `wageRatio` def follows by specializing
    `G := E.G θ`: the RHS is then exactly the body of `E.wageRatio V θ`,
    so `E.wageRatio V θ = w_V / w_G` holds by `rfl` after the
    specialization.  The
    substantive monotonicity claim of Theorem~\ref{thm:inversion}
    Part~1 (`thm_inversion_wage_ratio_monotone`) is proved separately
    from the closed-form def via `Real.rpow_le_rpow`.
  * `axiom_cobb_douglas_factor_share` — Cobb-Douglas verification
    factor share.
    Citations: Cobb-Douglas 1928 (original) / Mas-Colell, Whinston,
    Green 1995 §5.B.2 (modern textbook).
    **Lean role**: load-bearing — consumed (via
    `cobb_douglas_steady_state_identity_from_axiom` bridge) by
    `thm_credential_cobb_douglas_reduction_from_axioms`,
    `prop_junior_senior_wage_from_axioms`, and
    `thm_externality_pigouvian_cobb_douglas_from_axioms` (verifiable
    by `#print axioms` on each).
* **Cat 3 (paper-novel atomic atoms; `gapDefinitional`).**  The
  genuine standalone Cat 3 atoms tracked as Ledger entries are:
  the `Economy` carrier (a Lean `structure`); the production-
  function-shape hypothesisPredicates `IsCRS` / `IsCobbDouglas` /
  `IsCES` (Lean `def ... : Prop`); and the `def:diagnostic` V2
  tacit-accumulation hypothesisPredicate `V2_TacitAccumulation`
  (Lean `structure` over `h : ℝ → ℝ` with fields `h_zero_at_zero`
  and `h_monotone`).  These are paper-stipulative primitives; not
  Lean-closeable.  Encoded as Lean `structure`/`def`/`Prop` per
  spec §15.1.D encoding-exemption; the Ledger entry's `status :=
  gapDefinitional` + `cat3SubType` field is the canonical record.

  The paper's derived closed-form notation (`eBar`, `Vinf`,
  `thetaStar`, `wageRatio`, `Gstar`, `thetaInv`, `Lambda`, `Vreq`,
  `hPow`, `gSmooth`, `transientStock`, `MPpriv`, `MPsoc`,
  `externalityResidual`, `wedge`, `internalizedWedge`,
  `pigouvianSubsidy_CD`, `wageRatioRec`, `thetaInvRec`, `thetaEndo`,
  `hysteresisDeficit`, `recoveryStock`, `thetaStarExt`,
  `leontiefSeniorRent`, `rBarZero`, `rBarMax`) are concrete Lean
  `def`s whose defining equations hold by `rfl` — definitional
  *infrastructure*, NOT standalone Cat 3 atoms.  They are
  inventoried in the "Definitional infrastructure" section of
  `Ledger.lean` without standalone `GapEntry` records.
* **Cat 3 (paper claims tracked as Ledger-only entries; `gapOpen`).**
  Five paper claims are tracked as `gapOpen` Ledger-only `GapEntry`
  records with no corresponding Lean `axiom`/`def`/`theorem`
  declaration.  They split into two semantically distinct groups.

  *Group A* (four claims, distinct resolution paths — each with a
  faithful sound statement beyond this formalization's scope):
  `gap_window_invariance_OPEN`,
  `gap_aggregation_sequential_kinks_OPEN`,
  `gap_aggregation_intermediate_regime_OPEN`, and
  `gap_prop_adjustment_narrative_OPEN`.  The first three are
  paper-proven mathematical results whose Lean derivation requires
  out-of-scope Mathlib infrastructure (measure theory / continuity /
  kink analysis) — they carry `inputCategory := notInput`,
  `cat3SubType := notCat3` (paper-proven derived results pending
  formalization, not atomic inputs).  The fourth (residual
  non-codifiability) is a substantive phenomenological claim about
  the Polanyi verification residual whose resolution path is
  empirical (cohort-study evidence on AI substitution rates by
  career stage) rather than Mathlib derivation — it carries
  `inputCategory := cat3PaperNovel`,
  `cat3SubType := phenomenologicalConjecture`.

  *Group B* (one claim satisfied by construction):
  `gap_thm_recursive_invariance_OPEN` — paper Theorem 3 Part 3's
  μ-invariance commitment is satisfied by the Lean code's
  type-signature structure (`thetaStar` and `VinfHard` are defined
  without a μ parameter, so there is no μ-dependence to derive).
  Carries `inputCategory := notInput`, `cat3SubType := notCat3`;
  R10 reclassified `status := gapDefinitional → gapOpen` per
  spec §1.1, which binds `gapDefinitional` to Cat 3 sub-types
  {carrier, predicate, structuralEq}.

  The numerical-calibration corollary
  `cor_quant_predictions_calibration` is a derived `theorem` (`rw`
  + `norm_num`), and the threshold-reduction conjunct of the
  adjustment-margins narrative is the derived `theorem
  prop_adjustment_threshold_reduction_floor`.

The authoritative current inventory of theorem names and per-theorem
dependencies is the `lake env lean VerificationAsymmetry/AxiomAudit.lean`
output combined with the `#eval` printout at the bottom of
[`VerificationAsymmetry/Ledger.lean`](VerificationAsymmetry/Ledger.lean);
those `#eval`s — `countByStatus`, `inputCategoryCounts`,
`cat3SubTypeCounts`, `allGaps.length` — are the canonical authority
for the live entry counts (this README deliberately bakes no fixed
counts).

## File structure

| File | Paper component |
|------|-----------------|
| [`VerificationAsymmetry/Basic.lean`](VerificationAsymmetry/Basic.lean) | Definitions `def:gve`, `def:gen-supply`, `def:cohort`, `def:verification`, `def:diagnostic`; Lemma `lem:steady-state`; carriers `Economy`, `G`, `eBar`, `gHard`, `Vinf`, `VinfHard` |
| [`VerificationAsymmetry/Axioms.lean`](VerificationAsymmetry/Axioms.lean) | Cat 2 (textbook) atomic axioms: `axiom_euler_crs` (Euler's identity for CRS), `axiom_ces_wage_ratio` (CES wage-ratio closed form), `axiom_cobb_douglas_factor_share` (Cobb-Douglas verification factor share). Each axiom has a docstring with textbook citation |
| [`VerificationAsymmetry/Decomp.lean`](VerificationAsymmetry/Decomp.lean) | Theorem `thm:decomp` (stock-flow welfare decomposition; consumes `axiom_euler_crs` from `Axioms.lean`).  The Cobb-Douglas factor-share consequence used by `thm:credential` / `prop:junior-senior` / `thm:externality` is `cobb_douglas_steady_state_identity_from_axiom`, which lives in `Axioms.lean` as a bridge theorem |
| [`VerificationAsymmetry/Inversion.lean`](VerificationAsymmetry/Inversion.lean) | Theorem `thm:inversion` (wage ratio scaling, closed-form threshold); Corollary `cor:bounded-AI` (endpoint identifications) |
| [`VerificationAsymmetry/Collapse.lean`](VerificationAsymmetry/Collapse.lean) | Theorem `thm:collapse` (phase transition at `θ*`, transient decay, jump magnitude, general-`h` bound); Proposition `prop:smooth-collapse` (smooth-threshold decay rate) |
| [`VerificationAsymmetry/Credential.lean`](VerificationAsymmetry/Credential.lean) | Theorem `thm:credential` (Cobb-Douglas closed form, multiplicative decay); Proposition `prop:junior-senior` (senior wage scaling) |
| [`VerificationAsymmetry/Externality.lean`](VerificationAsymmetry/Externality.lean) | Theorem `thm:externality` (Pigouvian wedge, Cobb-Douglas subsidy formula); Propositions `prop:internalization`, `prop:decentralized-theta` |
| [`VerificationAsymmetry/Recursive.lean`](VerificationAsymmetry/Recursive.lean) | Theorem `thm:recursive` (μ-amplification, leftward shift, collapse invariance); Proposition `prop:boundary` (separability condition) |
| [`VerificationAsymmetry/Aggregation.lean`](VerificationAsymmetry/Aggregation.lean) | Theorem `thm:aggregation` Parts 2-3 (Cobb-Douglas zero-product `thm_aggregation_cobb_douglas_zero` + corollary `thm_aggregation_least_resilient_collapse`; perfect-substitutes survival `thm_aggregation_perfect_substitutes_survival` + post-collapse residual identity `thm_aggregation_perfect_substitutes_residual`); Proposition `prop:adjustment-margins` (career extension: `prop_adjustment_career_extension_strict` and `prop_adjustment_career_extension_bounded`; threshold-reduction floor: `prop_adjustment_threshold_reduction_floor`) |
| [`VerificationAsymmetry/EndogenousAI.lean`](VerificationAsymmetry/EndogenousAI.lean) | Theorem `thm:endogenous-ai` (Brouwer existence, uniqueness, corner self-consistency, hysteresis recovery rate) |
| [`VerificationAsymmetry/AxiomAudit.lean`](VerificationAsymmetry/AxiomAudit.lean) | Trust audit: prints `#print axioms` for every paper-level theorem |
| [`VerificationAsymmetry/Ledger.lean`](VerificationAsymmetry/Ledger.lean) | Typed gap ledger: `GapStatus` × `InputCategory` orthogonal classification, with one `GapEntry` per closed top-level result and per deferred paper claim |

## Building

Requires Lean 4 toolchain `v4.30.0-rc2` (managed via `elan`).

```bash
# Install elan + Lean toolchain if not already
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Get Mathlib cache (MUST run before `lake build` to avoid rebuilding Mathlib)
lake exe cache get

# Build
lake build

# Run axiom audit
lake env lean VerificationAsymmetry/AxiomAudit.lean
```

## Trust verification

For an independent trust check, after `lake build`:

```bash
# Count of `sorry` (expect 0)
grep -rn '\bsorry\b' VerificationAsymmetry/

# Print axiom dependencies of every paper-level theorem
lake env lean VerificationAsymmetry/AxiomAudit.lean

# Print live gap-ledger inventory (status counts, input-category counts)
# — authoritative inventory of closed results and deferred claims
lake env lean VerificationAsymmetry/Ledger.lean
```

## Companion paper

The Karpowicz/Einstein-Test companion paper lives in a parallel
directory at `../companion-einstein-test/lean4/` and formalizes a
*different* paper (`einstein_test.tex`, "What the Karpowicz Theorem
Does Not Prove").  The two formalizations are independent.

This formalization corresponds to the main paper:
`../paper/verification_asymmetry.tex`.

| Resource | Identifier |
|----------|------------|
| SSRN abstract id | [6718418](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6718418) |
| Zenodo DOI | [10.5281/zenodo.20038848](https://doi.org/10.5281/zenodo.20038848) |

## License

MIT License © 2026 Alex Li.
