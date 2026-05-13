# Generation-Verification Asymmetry — Lean 4 Formalization

Formal verification of the theorems and propositions of

> Li, Alex Chengyu. *Generation--Verification Asymmetry Inversion and
> Apprenticeship Pipeline Collapse Under AI Substitution.* 2026.

**Paper:**
- SSRN abstract id [6718418](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6718418)
- Zenodo DOI: [10.5281/zenodo.20038848](https://doi.org/10.5281/zenodo.20038848)

## Status

The formalization machine-checks the **structural mathematics** of the
paper end-to-end inside Lean 4 + Mathlib.  Every paper-internal
deduction is a genuine Lean 4 theorem — **zero `sorry`**.

The trust boundary is explicit:

* **Cat 1 (Mathlib-derivable theorems).** The bulk of paper-level
  content.  Closed via `Real.rpow` arithmetic, `Finset` sums /
  products, 1-D Brouwer (intermediate-value theorem), and the
  standard Lean kernel (`propext`, `Classical.choice`, `Quot.sound`).
* **Cat 2 (external textbook axioms).** Three atomic axioms
  declared in
  [`VerificationAsymmetry/Axioms.lean`](VerificationAsymmetry/Axioms.lean):
  Euler's identity for CRS production (used in Theorem~`thm:decomp`;
  citation Mas-Colell, Whinston, Green 1995 §5.B.2), the CES
  marginal-product wage-ratio closed form (used to identify the
  `wageRatio` definition with the CES marginal products; citation
  Acemoglu 2009 §15), and the Cobb-Douglas verification factor
  share (used in `thm:credential`, `prop:junior-senior`,
  `thm:externality` Part 3; citation Mas-Colell, Whinston, Green
  1995 §5.B.2).
* **Cat 3 (paper-novel atomic axioms).** Zero.  Every paper-novel
  structural object (`Economy`, `Vinf`, `eBar`, `gHard`,
  `wageRatio`, `Vreq`) is a Lean *definition*, not an axiom.

The Cat 2 axioms were introduced by the 2026-05 audit as the honest
accounting of textbook facts that were previously hidden inside
theorem signatures as hypotheses (e.g. `thm_decomp` formerly took
`hEuler : F G V = wG * G + wV * V` as a hypothesis, with proof body
`rfl`).  The audited form lifts the textbook content to explicit,
atomic axioms with citations; the consumer theorems' proofs are now
honest applications of those axioms.

Paper claims deferred to economic narrative or path-dependent
analysis (window invariance, sequential phase-transition kinks at
multiple order statistics, numerical calibration values) are
recorded honestly as `gapBlocked` entries in
[`VerificationAsymmetry/Ledger.lean`](VerificationAsymmetry/Ledger.lean);
they are NOT axiomatized.

The authoritative current inventory of theorem names and per-theorem
dependencies is the `lake env lean VerificationAsymmetry/AxiomAudit.lean`
output combined with the `#eval` printout at the bottom of
[`VerificationAsymmetry/Ledger.lean`](VerificationAsymmetry/Ledger.lean);
see those sources for the live counts.

## File structure

| File | Paper component |
|------|-----------------|
| [`VerificationAsymmetry/Basic.lean`](VerificationAsymmetry/Basic.lean) | Definitions `def:gve`, `def:gen-supply`, `def:cohort`, `def:verification`, `def:diagnostic`; Lemma `lem:steady-state`; carriers `Economy`, `G`, `eBar`, `gHard`, `Vinf`, `VinfHard` |
| [`VerificationAsymmetry/Axioms.lean`](VerificationAsymmetry/Axioms.lean) | Cat 2 (textbook) atomic axioms: `axiom_euler_crs` (Euler's identity for CRS), `axiom_ces_wage_ratio` (CES wage-ratio closed form), `axiom_cobb_douglas_factor_share` (Cobb-Douglas verification factor share). Each axiom has a docstring with textbook citation |
| [`VerificationAsymmetry/Decomp.lean`](VerificationAsymmetry/Decomp.lean) | Theorem `thm:decomp` (stock-flow welfare decomposition, Euler identity); Cobb-Douglas factor-share special case |
| [`VerificationAsymmetry/Inversion.lean`](VerificationAsymmetry/Inversion.lean) | Theorem `thm:inversion` (wage ratio scaling, closed-form threshold); Corollary `cor:bounded-AI` (endpoint identifications) |
| [`VerificationAsymmetry/Collapse.lean`](VerificationAsymmetry/Collapse.lean) | Theorem `thm:collapse` (phase transition at `θ*`, transient decay, jump magnitude, general-`h` bound); Proposition `prop:smooth-collapse` (smooth-threshold decay rate) |
| [`VerificationAsymmetry/Credential.lean`](VerificationAsymmetry/Credential.lean) | Theorem `thm:credential` (Cobb-Douglas closed form, multiplicative decay); Proposition `prop:junior-senior` (senior wage scaling) |
| [`VerificationAsymmetry/Externality.lean`](VerificationAsymmetry/Externality.lean) | Theorem `thm:externality` (Pigouvian wedge, Cobb-Douglas subsidy formula); Propositions `prop:internalization`, `prop:decentralized-theta` |
| [`VerificationAsymmetry/Recursive.lean`](VerificationAsymmetry/Recursive.lean) | Theorem `thm:recursive` (μ-amplification, leftward shift, collapse invariance); Proposition `prop:boundary` (separability condition) |
| [`VerificationAsymmetry/Aggregation.lean`](VerificationAsymmetry/Aggregation.lean) | Theorem `thm:aggregation` Parts 2-3 (Cobb-Douglas zero-product, perfect-substitutes survival); Proposition `prop:adjustment-margins` (career extension) |
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

## Audit history

The formalization has been built to mirror the Einstein-Test companion's
structure (typed gap ledger, Cat 1/2/3 discipline, `attackHistory`
hooks per `GapEntry`).  The attack history of each entry (citation
revisions, atomic refactors, prior retractions) will be preserved in
the `attackHistory` field of the corresponding `GapEntry` in
[`VerificationAsymmetry/Ledger.lean`](VerificationAsymmetry/Ledger.lean);
release-level milestones will be recorded in commit history and git
tags as the formalization is iterated.

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
