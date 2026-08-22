# Verification Asymmetry — Lean 4 Formalization

Companion machine-checked formalization for

> Li, Alex Chengyu. *Verification Asymmetry under AI Substitution:
> Wage-Ratio Inversion and Apprenticeship Thresholds.* 2026.

The theorem map targets the current 22-page EINT submission manuscript. The
public preprint identifiers near the end of this README refer to an earlier,
longer manuscript version.

## Status

The current 22-page EINT manuscript has a complete publication-facing theorem
map. Every derived mathematical claim in that manuscript has a named Lean
carrier or theorem, and `CurrentPaperStatus.lean` evaluates to
`unfinishedDerived=0`. The project contains zero executable `sorry` or `admit`.

Two external textbook inputs are load-bearing for the current paper:
`axiom_ces_wage_ratio` and `axiom_cobb_douglas_factor_share`. Their signatures
carry the exact production-function, derivative, positivity, and range
antecedents used by the paper. All other current-paper mathematical deductions
are derived in Lean from Mathlib and those explicit inputs.

The repository remains a superset of an older 42-page model. Historical modules
for credentialing, recursive verification, and endogenous adoption retain honest
conditional, partial, or open ledger entries, but those entries are not claims of
the current journal manuscript and are excluded from `currentPaperEntries`.

The trust boundary is explicit: each ledger entry is either

- a derived theorem composing Lean kernel primitives, Mathlib lemmas, and the
  external textbook axioms below; or
- an explicit `axiom` declaration with a textbook citation; or
- an honest open entry in a typed gap ledger (no Lean declaration), with a
  documented resolution path.

The live superset-ledger counts are emitted by `Ledger.lean`. Current-paper
coverage is independently emitted by `CurrentPaperStatus.lean` and enforced by
the manuscript audit.

### Inputs of the formalization

**Cat 1 — Mathlib-derivable atoms.** This project does not enumerate individual
Mathlib lemmas as Ledger entries. Most paper-level content is composed from
Mathlib internally (`Real.rpow`, `Finset` sums/products, the 1-D
intermediate-value theorem used as Brouwer on a real interval) together with the
Cat 2 axioms below and the Cat 3 paper-novel atoms, over the standard Lean
kernel (`propext`, `Classical.choice`, `Quot.sound`).

**Cat 2 — external textbook axioms** (declared in
[`VerificationAsymmetry/Axioms.lean`](VerificationAsymmetry/Axioms.lean)):

- `axiom_euler_crs` — Euler's identity for CRS production. Historical-superset
  input, not consumed by the current 22-page paper. Citations:
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
`wageRatio`, `Gstar`, `thetaInv`, `LambdaJ`, `Lambda`, `Vreq`, `hPow`, `gSmooth`,
`transientStock`, `MPpriv`, `MPsoc`, `externalityResidual`, `wedge`,
`internalizedWedge`, `pigouvianSubsidy_CD`, `wageRatioRec`, `thetaInvRec`,
`thetaEndo`, `hysteresisDeficit`, `recoveryStock`, `thetaStarExt`,
`leontiefSeniorRent`, `rBarZero`, `rBarMax`) are concrete Lean `def`s whose
defining equations hold by `rfl`. They are definitional infrastructure, not
standalone Cat 3 atoms.

### Current-paper closure and historical-superset gaps

The current manuscript's exact post-step cohort path, straddling-cohort cutoff,
full-stock clearing time, smooth-threshold derivative kink, externality-wedge
growth, post-collapse exponent trichotomy, large-capacity limits, fixed-CES
positivity, and near-Cobb--Douglas variable-exponent limit are all Lean-closed.

Historical claims omitted from the journal paper remain in `Ledger.lean` with
their original conditional/partial/open status. They are not converted into
axioms and do not enter `CurrentPaperStatus.currentPaperEntries`.

The authoritative current-paper surfaces are:

- `TheoremMap.lean` — Definition 1 through Proposition 14 and Eqs. (1)--(15);
- `CurrentPaperAxiomAudit.lean` — per-endpoint axiom dependencies;
- `CurrentPaperStatus.lean` — typed current-paper ledger with zero unfinished
  derived entries;
- `Ledger.lean` / `AxiomAudit.lean` — the broader historical project inventory.

## File structure

| File | Paper component |
|------|-----------------|
| [`VerificationAsymmetry/Basic.lean`](VerificationAsymmetry/Basic.lean) | Definitions `def:gve`, `def:gen-supply`, `def:cohort`, `def:verification`, `def:diagnostic`; Lemma `lem:steady-state`; carriers `Economy`, `G`, `eBar`, `gHard`, `Vinf`, `VinfHard` |
| [`VerificationAsymmetry/Axioms.lean`](VerificationAsymmetry/Axioms.lean) | Cat 2 textbook atomic axioms: `axiom_euler_crs`, `axiom_ces_wage_ratio`, `axiom_cobb_douglas_factor_share`; bridge theorems composing them with `steady_state_stock_identity` |
| [`VerificationAsymmetry/Decomp.lean`](VerificationAsymmetry/Decomp.lean) | Theorem `thm:decomp` (stock-flow output decomposition; consumes `axiom_euler_crs`) |
| [`VerificationAsymmetry/Inversion.lean`](VerificationAsymmetry/Inversion.lean) | Theorem `thm:inversion` (wage ratio scaling, closed-form threshold); Corollary `cor:bounded-AI` (endpoint identifications) |
| [`VerificationAsymmetry/Collapse.lean`](VerificationAsymmetry/Collapse.lean) | Steady-state hard/smooth threshold algebra, derivative formulas, and the verified slope kink |
| [`VerificationAsymmetry/CohortPath.lean`](VerificationAsymmetry/CohortPath.lean) | Arbitrary-path experience integral, exact permanent-step cohort path, promotion cutoff, full stock integral, and clearing time |
| [`VerificationAsymmetry/Credential.lean`](VerificationAsymmetry/Credential.lean) | Theorem `thm:credential` (Cobb-Douglas closed form, finite-capacity gross-peak FOC and uniqueness, multiplicative decay); Proposition `prop:junior-senior` (senior wage scaling) |
| [`VerificationAsymmetry/Externality.lean`](VerificationAsymmetry/Externality.lean) | Present-value identities, wedge closed form and monotonicity, smooth exponent limits, Cobb-Douglas residual-transfer simplification, and partial-capture identity |
| [`VerificationAsymmetry/Recursive.lean`](VerificationAsymmetry/Recursive.lean) | Conditional reduced-form μ-amplification, exact log-slope acceleration algebra, and threshold algebra; definitional cohort-side μ-invariance; technological reachability equivalence |
| [`VerificationAsymmetry/Aggregation.lean`](VerificationAsymmetry/Aggregation.lean) | Exact Cobb-Douglas zero propagation, every-fixed-CES positivity, surviving-weight limit, and the full `sigma -> 1+` near-Cobb--Douglas limit |
| [`VerificationAsymmetry/EndogenousAI.lean`](VerificationAsymmetry/EndogenousAI.lean) | Abstract fixed-point/uniqueness lemmas and direct-form recovery arithmetic; the economic construction and cohort derivation remain partial |
| [`VerificationAsymmetry/AxiomAudit.lean`](VerificationAsymmetry/AxiomAudit.lean) | Trust audit: prints `#print axioms` for every paper-level theorem |
| [`VerificationAsymmetry/Ledger.lean`](VerificationAsymmetry/Ledger.lean) | Typed gap ledger: each closed top-level result and each deferred paper claim is one `GapEntry`, with `GapStatus` × `InputCategory` × `Cat3SubType` classification |
| [`VerificationAsymmetry/TheoremMap.lean`](VerificationAsymmetry/TheoremMap.lean) | Publication-facing `#check` map for every numbered current-paper object and derivation |
| [`VerificationAsymmetry/CurrentPaperAxiomAudit.lean`](VerificationAsymmetry/CurrentPaperAxiomAudit.lean) | Current-paper-only `#print axioms` audit; allowed project axioms are exactly CES wage ratio and Cobb-Douglas factor share |
| [`VerificationAsymmetry/CurrentPaperStatus.lean`](VerificationAsymmetry/CurrentPaperStatus.lean) | Current-paper ledger; evaluates to 25 entries and zero unfinished derived mathematics |

## Building

Requires Lean 4 toolchain `v4.30.0-rc2` (managed via `elan`).
The tracked `lake-manifest.json` pins Mathlib revision
`388f44f89d70fbad0e1accb8fd62fc8c97714a85`; release and CI builds must not
re-resolve Mathlib from its moving `main` branch.

```bash
# Install elan + Lean toolchain if not already
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Get Mathlib cache (run before `lake build` to avoid rebuilding Mathlib)
lake exe cache get

# Build
lake build

# Run axiom audit
lake env lean VerificationAsymmetry/CurrentPaperAxiomAudit.lean

# Run current-paper theorem map and status
lake env lean VerificationAsymmetry/TheoremMap.lean
lake env lean VerificationAsymmetry/CurrentPaperStatus.lean
```

## Trust verification

Run the same fail-closed release verifier used by CI:

```bash
python verify_release.py
```

The verifier checks zero executable `sorry`/`admit`, the exact three-name
project axiom declaration boundary, the exact two-name current-paper axiom
dependency boundary, all numbered theorem-map markers, `24/0` current-paper
status, the reviewed historical ledger inventory, required default build
targets, and release-metadata consistency.

## Companion paper

This formalization targets the current 22-page EINT submission manuscript named
above. Its canonical TeX source is maintained with the submission package, not
inside this public code repository. The identifiers below refer to an older
public paper snapshot and must not be treated as identifiers for the current
submission text.

| Resource | Identifier |
|----------|------------|
| Historical SSRN abstract id | [6718418](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6718418) |
| Zenodo concept DOI | [10.5281/zenodo.20038847](https://doi.org/10.5281/zenodo.20038847) |

## Citation

Repository citation metadata is provided in [`CITATION.cff`](CITATION.cff).
Until the Zenodo archive for version 0.4.2 is minted, cite the repository URL with
the exact commit or release tag used. The SSRN and Zenodo identifiers above are
historical paper surfaces and are not software-release identifiers.

## License

Released under the [`MIT License`](LICENSE), © 2026 Alex Chengyu Li.
