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

This project has **zero atomic axioms** (Cat 2 / Cat 3): the paper's
mathematical content is entirely real-analytic, reducing to:

* CES algebra (closed-form wage ratio, inversion threshold);
* Linear-cohort accounting (transient decay, hysteresis bound);
* `Finset` products / sums (aggregation min-theorem);
* 1-D Brouwer fixed point (intermediate value theorem).

All four ingredients live inside Mathlib's core libraries and the
standard Lean kernel (`propext`, `Classical.choice`, `Quot.sound`);
no external textbook axioms are required.

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
