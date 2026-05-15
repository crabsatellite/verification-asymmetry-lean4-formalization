# Generation-Verification Asymmetry — Lean 4 Formalization

Companion machine-checked formalization for

> Li, Alex Chengyu. *Generation--Verification Asymmetry Inversion and
> Apprenticeship Pipeline Collapse Under AI Substitution.* 2026.

**Paper:**
- SSRN abstract id [6718418](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6718418)
- Zenodo DOI: [10.5281/zenodo.20038848](https://doi.org/10.5281/zenodo.20038848)

## Status

This Lean 4 + Mathlib project machine-checks the structural mathematics of the paper.
Every paper-internal deduction captured here is a genuine Lean 4 theorem with
**zero `sorry`**. The trust boundary is explicit: each result is either

- a derived theorem composing Lean kernel primitives, Mathlib lemmas, and the
  external textbook axioms below; or
- an explicit `axiom` declaration with a textbook citation; or
- an honest open entry in a typed gap ledger (no Lean declaration), with a
  documented resolution path.

The live counts of closed / partial / open entries are emitted by `#eval` at the
bottom of [`VerificationAsymmetry/Ledger.lean`](VerificationAsymmetry/Ledger.lean);
this README deliberately bakes no fixed counts.

### Inputs of the formalization

**Cat 1 — Mathlib-derivable atoms.** This project does not enumerate individual
Mathlib lemmas as Ledger entries. Most paper-level content is composed from
Mathlib internally (`Real.rpow`, `Finset` sums/products, the 1-D
intermediate-value theorem used as Brouwer on a real interval) together with the
Cat 2 axioms below and the Cat 3 paper-novel atoms, over the standard Lean
kernel (`propext`, `Classical.choice`, `Quot.sound`).

**Cat 2 — external textbook axioms** (declared in
[`VerificationAsymmetry/Axioms.lean`](VerificationAsymmetry/Axioms.lean)):

- `axiom_euler_crs` — Euler's identity for CRS production. Citations:
  Euler 1755 (original); Mas-Colell, Whinston, Green 1995 §5.B.2 (modern
  textbook). Load-bearing: consumed by `thm_decomp`.
- `axiom_ces_wage_ratio` — CES marginal-product wage-ratio closed form.
  Citations: Arrow-Chenery-Minhas-Solow 1961 (original CES paper);
  Acemoglu 2009 §15 (modern textbook). Load-bearing: consumed by
  `wageRatio_eq_ces_marginal_product_ratio`.
- `axiom_cobb_douglas_factor_share` — Cobb-Douglas verification factor share.
  Citations: Cobb-Douglas 1928 (original); Mas-Colell, Whinston, Green
  1995 §5.B.2 (modern textbook). Load-bearing (via the
  `cobb_douglas_steady_state_identity_from_axiom` bridge): consumed by the
  `_from_axioms` Cobb-Douglas closed-form theorems in `Credential.lean` and
  `Externality.lean`.

Each axiom carries explicit antecedents (production-function shape predicate
`IsCRS` / `IsCobbDouglas` / `IsCES`, `HasDerivAt` for the marginal-product
identification, and positivity constraints) in its Lean signature.

**Cat 3 — paper-novel atomic atoms** (encoded as Lean `structure` /
`def : Prop`, not `axiom`):

- the `Economy` carrier;
- the production-function-shape hypothesis predicates `IsCRS`, `IsCobbDouglas`,
  `IsCES`;
- the V2 tacit-accumulation hypothesis predicate `V2_TacitAccumulation`
  (Lean `structure` with fields `h_zero_at_zero` and `h_monotone`, both
  consumed downstream).

The paper's derived closed-form notation (`eBar`, `Vinf`, `thetaStar`,
`wageRatio`, `Gstar`, `thetaInv`, `Lambda`, `Vreq`, `hPow`, `gSmooth`,
`transientStock`, `MPpriv`, `MPsoc`, `externalityResidual`, `wedge`,
`internalizedWedge`, `pigouvianSubsidy_CD`, `wageRatioRec`, `thetaInvRec`,
`thetaEndo`, `hysteresisDeficit`, `recoveryStock`, `thetaStarExt`,
`leontiefSeniorRent`, `rBarZero`, `rBarMax`) are concrete Lean `def`s whose
defining equations hold by `rfl`. They are definitional infrastructure, not
standalone Cat 3 atoms.

### Open paper claims tracked without a Lean declaration

A small number of paper claims are tracked as `gapOpen` Ledger entries without a
corresponding Lean `axiom` / `def` / `theorem`. They split into two groups:

*Group A* — out-of-scope Mathlib infrastructure or empirical resolution path:

- `gap_window_invariance_OPEN` (measure-theoretic statement, Proposition
  Stock-Flow-Asymptotics Part 4);
- `gap_aggregation_sequential_kinks_OPEN` (continuity / kink analysis,
  Theorem Aggregation Part 1);
- `gap_aggregation_intermediate_regime_OPEN` (calculus on the intermediate
  regime, Theorem Aggregation Part 4);
- `gap_prop_adjustment_narrative_OPEN` (substantive phenomenological claim
  about the Polanyi verification residual; resolution path is empirical
  cohort-study evidence).

*Group B* — satisfied by carrier construction:

- `gap_thm_recursive_invariance_OPEN` — paper Theorem Recursive Part 3's
  μ-invariance commitment is satisfied by the type-signature structure
  (`thetaStar` / `VinfHard` / `eBar` take no μ argument), so there is no
  μ-dependence to derive.

These claims are deferred honestly rather than encoded as unsound `axiom`s or
as vacuous tautologies. The numerical calibration corollary
`cor_quant_predictions_calibration` and the threshold-reduction conjunct
`prop_adjustment_threshold_reduction_floor` of the adjustment-margins
narrative are derived Lean `theorem`s.

The authoritative inventory of theorem names and per-theorem axiom
dependencies is the output of
`lake env lean VerificationAsymmetry/AxiomAudit.lean`, combined with the
`#eval` printouts at the bottom of `Ledger.lean`.

## File structure

| File | Paper component |
|------|-----------------|
| [`VerificationAsymmetry/Basic.lean`](VerificationAsymmetry/Basic.lean) | Definitions `def:gve`, `def:gen-supply`, `def:cohort`, `def:verification`, `def:diagnostic`; Lemma `lem:steady-state`; carriers `Economy`, `G`, `eBar`, `gHard`, `Vinf`, `VinfHard` |
| [`VerificationAsymmetry/Axioms.lean`](VerificationAsymmetry/Axioms.lean) | Cat 2 textbook atomic axioms: `axiom_euler_crs`, `axiom_ces_wage_ratio`, `axiom_cobb_douglas_factor_share`; bridge theorems composing them with `steady_state_stock_identity` |
| [`VerificationAsymmetry/Decomp.lean`](VerificationAsymmetry/Decomp.lean) | Theorem `thm:decomp` (stock-flow welfare decomposition; consumes `axiom_euler_crs`) |
| [`VerificationAsymmetry/Inversion.lean`](VerificationAsymmetry/Inversion.lean) | Theorem `thm:inversion` (wage ratio scaling, closed-form threshold); Corollary `cor:bounded-AI` (endpoint identifications) |
| [`VerificationAsymmetry/Collapse.lean`](VerificationAsymmetry/Collapse.lean) | Theorem `thm:collapse` (phase transition at `θ*`, transient decay, jump magnitude, general-`h` bound); Proposition `prop:smooth-collapse` (smooth-threshold decay rate) |
| [`VerificationAsymmetry/Credential.lean`](VerificationAsymmetry/Credential.lean) | Theorem `thm:credential` (Cobb-Douglas closed form, multiplicative decay); Proposition `prop:junior-senior` (senior wage scaling) |
| [`VerificationAsymmetry/Externality.lean`](VerificationAsymmetry/Externality.lean) | Theorem `thm:externality` (Pigouvian wedge, Cobb-Douglas subsidy formula); Propositions `prop:internalization`, `prop:decentralized-theta` |
| [`VerificationAsymmetry/Recursive.lean`](VerificationAsymmetry/Recursive.lean) | Theorem `thm:recursive` (μ-amplification, leftward shift, collapse invariance); Proposition `prop:boundary` (separability condition) |
| [`VerificationAsymmetry/Aggregation.lean`](VerificationAsymmetry/Aggregation.lean) | Theorem `thm:aggregation` Parts 2-3 (Cobb-Douglas zero-product + least-resilient-collapse corollary; perfect-substitutes survival + post-collapse residual identity); Proposition `prop:adjustment-margins` (career extension theorems + threshold-reduction floor) |
| [`VerificationAsymmetry/EndogenousAI.lean`](VerificationAsymmetry/EndogenousAI.lean) | Theorem `thm:endogenous-ai` (Brouwer existence, uniqueness, corner self-consistency, hysteresis recovery rate) |
| [`VerificationAsymmetry/AxiomAudit.lean`](VerificationAsymmetry/AxiomAudit.lean) | Trust audit: prints `#print axioms` for every paper-level theorem |
| [`VerificationAsymmetry/Ledger.lean`](VerificationAsymmetry/Ledger.lean) | Typed gap ledger: each closed top-level result and each deferred paper claim is one `GapEntry`, with `GapStatus` × `InputCategory` × `Cat3SubType` classification |

## Building

Requires Lean 4 toolchain `v4.30.0-rc2` (managed via `elan`).

```bash
# Install elan + Lean toolchain if not already
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Get Mathlib cache (run before `lake build` to avoid rebuilding Mathlib)
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

# Print live gap-ledger inventory
lake env lean VerificationAsymmetry/Ledger.lean
```

## Companion paper

This formalization corresponds to the main paper at
`../paper/verification_asymmetry.tex`.

| Resource | Identifier |
|----------|------------|
| SSRN abstract id | [6718418](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6718418) |
| Zenodo DOI | [10.5281/zenodo.20038848](https://doi.org/10.5281/zenodo.20038848) |

## License

MIT License © 2026 Alex Li.
