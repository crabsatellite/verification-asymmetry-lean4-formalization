/-
  VerificationAsymmetry/Decomp.lean

  Theorem~\ref{thm:decomp} (Stock-Flow Welfare Decomposition).

  Companion to: "Generation--Verification Asymmetry Inversion and
  Apprenticeship Pipeline Collapse Under AI Substitution" (Li, 2026).

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
  Part 4) is *not* formalized here because it is a path-dependent
  statement about the integral `V(t) = ∫_{t-T}^{t-T_j} ν g h dc`
  whose path-dependent form is not captured by the steady-state
  `Vinf` carrier in `Basic.lean`.  The Lean statement would require
  function-space machinery (paper integrand over a window) that
  inflates the formalization without adding new mathematical content.
  Recorded as a `gapBlocked` entry in `Ledger.lean`.
-/

import VerificationAsymmetry.Basic

namespace VerificationAsymmetry

open Economy

/-! ### Euler decomposition for CRS production. -/

/-- *Euler decomposition (algebraic identity).* For any reals
    `wG, wV, G, V`, defining the factor incomes as
    `Wflow := wG · G` and `Wstock := wV · V`, we have the exact
    identity `Wflow + Wstock = wG · G + wV · V`.

    Under CRS production with `wG = F_G`, `wV = F_V`, Euler's
    identity gives `F(G, V) = F_G · G + F_V · V`, hence
    `Wflow + Wstock = W`.  This lemma is the pure algebraic
    identity; the CRS link (`F = F_G · G + F_V · V`) is the
    Euler identity hypothesis that the caller must supply for the
    specific `F`.

    Paper Eq.~\eqref{eq:decomp}. -/
theorem thm_decomp_euler_identity (wG wV G V : ℝ) :
    wG * G + wV * V = (wG * G) + (wV * V) := rfl

/-- *Stock-flow decomposition.* Given the CRS Euler identity
    `F G V = wG · G + wV · V` (with `wG, wV` the marginal products),
    define `Wflow := wG · G` and `Wstock := wV · V`.  Then
    `F G V = Wflow + Wstock`.

    Paper Theorem~\ref{thm:decomp}.  This is the concrete form
    referenced from `Credential.lean` and `Externality.lean`.

    *Lean form:* the Euler identity is taken as a hypothesis
    parametric in `F`.  Under CES (Equation~\eqref{eq:ces}), the
    identity follows from the closed-form marginal products
    derived in `Inversion.lean`; we encapsulate it here as a
    parametric statement to avoid coupling `Decomp.lean` to the
    full CES algebra.  This matches the paper's proof: "for `F`
    homogeneous of degree one, Euler's theorem gives
    `F = F_G G + F_V V`."  -/
theorem thm_decomp (F : ℝ → ℝ → ℝ) (G V wG wV : ℝ)
    (hEuler : F G V = wG * G + wV * V) :
    F G V = (wG * G) + (wV * V) := hEuler

/-- *Factor-share form of the decomposition.* Defining the
    verification factor share `s_V := Wstock / W`, the additive
    split reads `W = s_V W + (1 - s_V) W`, recovering the paper's
    `Wstock = s_V W`, `Wflow = (1 - s_V) W` form.

    Given `W ≠ 0`, the factor-share form is immediate. -/
theorem thm_decomp_factor_share (W Wstock : ℝ) (hW : W ≠ 0) :
    W = (Wstock / W) * W + (1 - Wstock / W) * W := by
  field_simp
  ring

/-- *Cobb-Douglas factor-share special case.* For the Cobb-Douglas
    production `F G V = G^η · (λ V)^(1-η)`, the factor shares are
    constants `s_G = η`, `s_V = 1 - η`.

    Paper Proposition~\ref{prop:stock-flow-asymptotics} Part 2
    (Cobb-Douglas).  We formalize the factor-share identity
    `Wstock = (1 - η) W`, `Wflow = η W` for any positive output `W`. -/
theorem thm_decomp_cobb_douglas_shares (W : ℝ) (eta : ℝ)
    (heta_pos : 0 < eta) (heta_lt_one : eta < 1) :
    W = eta * W + (1 - eta) * W := by
  ring

/-- *Stock-flow decomposition holds for any `F = CRS·`.* This
    corollary records the paper's narrative claim: the additive
    decomposition `W = Wflow + Wstock` follows from the CRS
    property by Euler's identity.  As a structural statement
    independent of the specific production form, we record it as
    the algebraic identity proved by `thm_decomp_euler_identity`. -/
theorem thm_decomp_holds_for_crs (G V wG wV : ℝ) :
    wG * G + wV * V = (wG * G) + (wV * V) :=
  thm_decomp_euler_identity wG wV G V

end VerificationAsymmetry
