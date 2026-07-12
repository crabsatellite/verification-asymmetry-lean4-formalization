# Generation-Verification Asymmetry — Lean 4 Formalization

Companion machine-checked formalization for

> Li, Alex Chengyu. *Generation--Verification Asymmetry and
> Apprenticeship-Pipeline Thresholds Under AI Substitution.* 2026.

The current manuscript is an internal reconstruction and is not represented by
the historical public identifiers listed near the end of this README.

## Status

This Lean 4 + Mathlib project is a **typed algebraic audit**, not a certificate
for the complete paper. Every deduction actually captured as a theorem here is
checked with **zero `sorry`**, but several paper claims are only conditional,
partial, definitional, or open. In particular, the complete path-dependent
cohort dynamics and the economic microfoundation of several reduced forms are
not machine-checked.

The trust boundary is explicit: each ledger entry is either

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

### Non-closed paper claims

The authoritative classification is the live `allGaps` inventory in
`Ledger.lean`. Important limitations include:

- The complete post-step cohort path is **partial**. Lean proves the linear
  decay of the pre-shock senior component, not the complete stock including
  straddling cohorts or its exact clearing time.
- The endogenous-AI fixed-point construction is **partial**. Lean proves an
  abstract one-dimensional fixed-point lemma, but does not derive the paper's
  selected inner map from primitives.
- The disturbance deficit and recovery functions are **partial**: endpoint
  arithmetic is checked for declared functions, while their derivation from
  the cohort integral remains open.
- Recursive pressure and endogenous uniqueness claims are **conditional** on
  explicitly declared reduced-form schedules or composite-map properties.
- The recursive log-slope comparison is machine-checked **conditional** on the
  declared pressure schedule; the constrained-production derivation of that
  schedule remains open.
- The near-Cobb--Douglas limit from above is **partial**: the manuscript proves
  the variable-exponent finite-sum limit, while its Lean formalization remains
  pending.
- Window invariance, sequential aggregation kinks, the intermediate-CES
  regime, and an empirical residual-floor claim remain **open**.
- The μ-invariance of the cohort threshold is **definitional**: the relevant
  carriers have no μ argument. It is not an independently proved robustness
  theorem.

These claims are not converted into axioms merely to make a proof pass.

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
| [`VerificationAsymmetry/Collapse.lean`](VerificationAsymmetry/Collapse.lean) | Steady-state hard-threshold algebra and the pre-shock-senior component of the transient path; the complete transient is partial |
| [`VerificationAsymmetry/Credential.lean`](VerificationAsymmetry/Credential.lean) | Theorem `thm:credential` (Cobb-Douglas closed form, finite-capacity gross-peak FOC and uniqueness, multiplicative decay); Proposition `prop:junior-senior` (senior wage scaling) |
| [`VerificationAsymmetry/Externality.lean`](VerificationAsymmetry/Externality.lean) | Algebraic residual/wedge identities, sign, Cobb-Douglas residual-transfer simplification, and an anti-monotonicity implication; no first-best policy theorem |
| [`VerificationAsymmetry/Recursive.lean`](VerificationAsymmetry/Recursive.lean) | Conditional reduced-form μ-amplification, exact log-slope acceleration algebra, and threshold algebra; definitional cohort-side μ-invariance; technological reachability equivalence |
| [`VerificationAsymmetry/Aggregation.lean`](VerificationAsymmetry/Aggregation.lean) | Exact Cobb-Douglas zero propagation, perfect-substitutes endpoint identities, and selected adjustment bounds; the near-Cobb--Douglas limit is partial and intermediate-CES claims remain open |
| [`VerificationAsymmetry/EndogenousAI.lean`](VerificationAsymmetry/EndogenousAI.lean) | Abstract fixed-point/uniqueness lemmas and direct-form recovery arithmetic; the economic construction and cohort derivation remain partial |
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

This formalization audits selected claims in the current manuscript at
`../paper/verification_asymmetry.tex`. The identifiers below refer to an older
public snapshot and must not be treated as identifiers for the reconstructed text.

| Resource | Identifier |
|----------|------------|
| Historical SSRN abstract id | [6718418](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6718418) |
| Historical Zenodo DOI | [10.5281/zenodo.20038848](https://doi.org/10.5281/zenodo.20038848) |

## License

MIT License © 2026 Alex Li.
