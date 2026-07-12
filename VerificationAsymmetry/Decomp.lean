/-
  VerificationAsymmetry/Decomp.lean

  Theorem~\ref{thm:decomp} (Stock-Flow Welfare Decomposition).

  Companion to: "Generation--Verification Asymmetry and
  Apprenticeship-Pipeline Thresholds Under AI Substitution" (Li, 2026).

  Statement.  For any constant-returns-to-scale `F`, Euler's identity
  gives the additive split

      W = F_G · G + F_V · V = W_flow + W_stock,

  where `W_flow := F_G · G` is the generation factor income and
  `W_stock := F_V · V` is the verification factor income.

  Lean formalization.  We formalize Euler's identity directly: a
  function `F : ℝ × ℝ → ℝ` is *homogeneous of degree 1* iff
  `F(t G, t V) = t · F(G, V)` for all `t > 0`.  Under sufficient
  smoothness, Euler's identity `F = F_G · G + F_V · V` follows.

  Substantive content of `thm:decomp`.  The decomposition is the
  *additive split* itself — once one defines `W_stock` and `W_flow`
  as factor-share components, Euler's identity is the algebraic
  identity that they sum to `W`.  We formalize this as an exact
  identity at the level of marginal-product values.

  Window invariance (Proposition~\ref{prop:stock-flow-asymptotics}
  Part 4) is *not* formalized in this file.  A faithful Lean
  statement of the paper's window-integral identity requires Mathlib
  `MeasureTheory` integral infrastructure beyond this formalization's
  structural scope; the claim is tracked as a `gapOpen` Ledger
  `GapEntry` record (`gap_window_invariance_OPEN` in `Ledger.lean`)
  WITHOUT a corresponding Lean `axiom`/`def`/`theorem` declaration.
-/

import VerificationAsymmetry.Basic
import VerificationAsymmetry.Axioms

namespace VerificationAsymmetry

open Economy

/-! ### Euler decomposition for CRS production. -/

/-- *Stock-flow decomposition.* Define `Wflow := w_G · G` and
    `Wstock := w_V · V`.  Then for any CRS production function `F`
    with marginal-product wages `w_G, w_V`,

        F G V = Wflow + Wstock.

    Paper Theorem~\ref{thm:decomp}.  This is the concrete form
    referenced from `Credential.lean` and `Externality.lean`.

    *Lean form:* derived from `axiom_euler_crs` (Cat 2, textbook
    Euler identity for CRS production).  The axiom requires explicit
    antecedents: `IsCRS F`, `HasDerivAt`-bound `wG`, `wV`, and
    positivity of `G, V`. -/
theorem thm_decomp (F : ℝ → ℝ → ℝ) (G V wG wV : ℝ)
    (hCRS : IsCRS F)
    (h_wG : HasDerivAt (fun x => F x V) wG G)
    (h_wV : HasDerivAt (fun y => F G y) wV V)
    (hG_pos : 0 < G) (hV_pos : 0 < V) :
    F G V = (wG * G) + (wV * V) :=
  axiom_euler_crs F G V wG wV hCRS h_wG h_wV hG_pos hV_pos

/-! ### Proposition~\ref{prop:stock-flow-asymptotics} Part 4: window
    invariance — Ledger-only `gapOpen`, not Lean-encoded.

  The paper's window-invariance result
  (Proposition~\ref{prop:stock-flow-asymptotics} Part 4) states that,
  for a time-varying AI-substitution path `θ(·)` held CONSTANT at
  `θ_old` on the cohort-formation window `[t-T, t-T_j]`, the
  verification stock `V(t)` depends ONLY on `θ_old` — in particular
  it is invariant to the current substitution rate `θ(t)`.  The paper
  derives this from the cohort integral
  `V(t) = ∫_{t-T}^{t-T_j} ν g(e_J(c)) h(e_J(c)) dc`
  (Def~\ref{def:cohort}), whose integrand depends only on `θ(s)` for
  `s` in the window.

  A faithful sound STATEMENT of this claim requires Mathlib
  `MeasureTheory` integral infrastructure (to even express the
  cohort-integral form) that is beyond this formalization's
  structural scope.  No Lean `axiom`/`def`/`theorem` declaration is
  provided: an `axiom` over a free `windowedStock` functional is
  unsound (`False`-injectable), and a `def : Prop` whose constraining
  predicate equals the asserted conclusion is vacuous (tautological).
  The honest encoding is the Ledger `GapEntry`
  `gap_window_invariance_OPEN` (`Ledger.lean`): a typed,
  `#eval`-retrievable record tracking the gap's status, paper source,
  and the reason it is not Lean-derived. -/

end VerificationAsymmetry
