#!/usr/bin/env python3
"""Fail-closed release verification for the public Lean companion.

The script is cross-platform and intentionally checks the publication-facing
surfaces rather than treating a successful library build as sufficient.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path


if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")


ROOT = Path(__file__).resolve().parent
LEAN_ROOT = ROOT / "VerificationAsymmetry"

EXPECTED_DECLARED_AXIOMS = {
    "axiom_ces_wage_ratio",
    "axiom_cobb_douglas_factor_share",
    "axiom_euler_crs",
}
EXPECTED_CURRENT_AXIOMS = {
    "VerificationAsymmetry.Economy.axiom_ces_wage_ratio",
    "VerificationAsymmetry.Economy.axiom_cobb_douglas_factor_share",
}
EXPECTED_LEDGER = (
    "open=7 partial=2 blocked=0 deadEnd=0 closed=30 "
    "closedConditional=6 definitional=7"
)
EXPECTED_STATUS = "current-paper theorem coverage: entries=25 unfinishedDerived=0"
NUMBERED_MARKERS = (
    "Definition 1",
    "Remark 2",
    "Definition 3",
    "Definition 4",
    "Definition 5 and Assumption 6",
    "Lemma 7",
    "Definition 8",
    "Theorem 9",
    "Theorem 10",
    "Proposition 11",
    "Remark 12",
    "Theorem 13",
    "Proposition 14",
)
REQUIRED_MAP_SYMBOLS = (
    "G_tendsto_at_one",
    "G_rpow_tendsto_at_one",
    "G_rpow_endpoint_pos",
    "timeIndexedStock_eq_cohort_integral",
    "timeIndexedStock_const_eq_Vinf",
    "VerificationAsymmetryDiagnostic",
    "verificationAsymmetryDiagnostic_of_V2",
    "thm_inversion_wage_ratio_strict",
    "thetaInvMarginalProductInf_eq_thetaInv",
    "thm_inversion_threshold_strict_in_rBar",
    "thetaInvAtCapacity_strictAnti",
    "CESCapacityPriceFamily.ratio_eq",
    "marginalProductWageRatioAtCapacity_tendsto_atTop",
    "thetaInvMarginalProductInfAtCapacity_eq_closedForm",
    "thetaInvMarginalProductInfAtCapacity_eventually_interior",
    "thetaInvMarginalProductInfAtCapacity_tendsto_zero_right",
    "paper_theorem9_wage_ratio_large_capacity_atomic",
    "paper_theorem9_eventual_actual_threshold_atomic",
    "paper_theorem9_actual_threshold_limit_atomic",
    "PaperStepContext",
    "PaperSmoothThresholdContext",
    "PaperExternalityIncidenceContext",
    "PaperAggregationContext",
    "hasDerivAt_hard_stock_below",
    "hardStockSlopeBelow_neg",
    "VinfHard_tendsto_left_at_thetaStar",
    "VinfHard_tendsto_right_zero_at_thetaStar",
    "hasDerivWithinAt_smoothStock_left",
    "hasDerivWithinAt_smoothStock_right",
    "cumulativeExperience_step_eq_stepExperience",
    "timeIndexedStock_step_eq_exactStepStock",
    "preStepStockIntegral_eq_transientStock",
    "hardPromotion_externalityResidual_zero_above",
    "hardPromotion_wedge_zero_above",
    "intervalIntegral_exp_neg_eq_LambdaJ",
    "intervalIntegral_exp_neg_eq_Lambda",
    "wedge_eq_wedgeExplicit",
    "smoothPaperWedge_eq_closedForm",
    "smoothPaperWedge_tendsto_atTop",
    "smoothPaperWedge_tendsto_endpoint",
    "smoothPaperWedge_tendsto_zero",
    "smoothMarginalProductWedge_tendsto_atTop",
    "smoothMarginalProductWedge_tendsto_endpoint",
    "smoothMarginalProductWedge_tendsto_zero",
    "prop_aggregation_near_cobb_douglas_limit",
    "paper_definition1_parameters_exact",
    "paper_equation1_ces_exact",
    "paper_definition3_generation_supply_exact",
    "paper_equation2_generation_supply_exact",
    "paper_definition4_cohort_dynamics_exact",
    "paper_equation3_cumulative_experience_exact",
    "paper_assumption6_time_indexed_stock_exact",
    "paper_lemma7_steady_state_stock_exact",
    "paper_equation4_steady_state_stock_exact",
    "paper_equation5_hard_stock_exact",
    "paper_equation6_smooth_stock_exact",
    "paper_definition8_diagnostic_exact",
    "paper_theorem9_inversion_exact",
    "paper_equation7_wage_ratio_exact",
    "paper_equation8_inversion_threshold_exact",
    "paper_theorem10_pipeline_collapse_exact",
    "paper_equation9_collapse_threshold_exact",
    "paper_equation10_transient_stock_exact",
    "paper_proposition11_smooth_collapse_exact",
    "paper_equation11_smooth_stock_exact",
    "paper_theorem13_externality_exact",
    "paper_equation12_social_present_value_exact",
    "paper_equation13_apprenticeship_wedge_exact",
    "paper_equation14_explicit_wedge_exact",
    "paper_proposition14_aggregation_exact",
    "paper_equation15_aggregate_output_exact",
)
REQUIRED_DEFAULT_TARGETS = (
    "VerificationAsymmetry",
    "VerificationAsymmetry.Ledger",
    "VerificationAsymmetry.TheoremMap",
    "VerificationAsymmetry.CurrentPaperStatus",
    "VerificationAsymmetry.CurrentPaperAxiomAudit",
    "VerificationAsymmetry.PaperExactnessAudit",
    "VerificationAsymmetry.CurrentPaperClaimBindings",
    "VerificationAsymmetry.AtomicPaperClaimBindings",
    "VerificationAsymmetry.AtomicPaperAxiomAudit",
)
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.30.0-rc2"
EXPECTED_MATHLIB_REV = "388f44f89d70fbad0e1accb8fd62fc8c97714a85"
EXPECTED_PAPER_CONCEPT_DOI = "10.5281/zenodo.20038847"


def strip_lean_comments_and_strings(source: str) -> str:
    """Remove nested Lean comments and strings before proof-escape scanning."""

    out: list[str] = []
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    escaped = False

    while index < len(source):
        pair = source[index:index + 2]
        char = source[index]

        if in_line_comment:
            if char == "\n":
                in_line_comment = False
                out.append("\n")
            index += 1
            continue

        if block_depth:
            if pair == "/-":
                block_depth += 1
                index += 2
            elif pair == "-/":
                block_depth -= 1
                index += 2
            else:
                if char == "\n":
                    out.append("\n")
                index += 1
            continue

        if in_string:
            if char == '"' and not escaped:
                in_string = False
            escaped = char == "\\" and not escaped
            if char != "\\":
                escaped = False
            index += 1
            continue

        if pair == "--":
            in_line_comment = True
            index += 2
        elif pair == "/-":
            block_depth = 1
            index += 2
        elif char == '"':
            in_string = True
            escaped = False
            index += 1
        else:
            out.append(char)
            index += 1

    if block_depth:
        raise SystemExit("unterminated Lean block comment encountered during release scan")
    if in_string:
        raise SystemExit("unterminated Lean string encountered during release scan")
    return "".join(out)


def lean_sources() -> list[Path]:
    return [ROOT / "VerificationAsymmetry.lean", *sorted(LEAN_ROOT.glob("*.lean"))]


def check_source_policy() -> None:
    proof_escapes: list[str] = []
    declared_axioms: set[str] = set()
    for path in lean_sources():
        source = path.read_text(encoding="utf-8")
        executable = strip_lean_comments_and_strings(source)
        if re.search(r"\b(?:sorry|admit)\b", executable):
            proof_escapes.append(str(path.relative_to(ROOT)))
        declared_axioms.update(
            re.findall(r"(?m)^\s*axiom\s+(axiom_[A-Za-z0-9_]+)\b", executable)
        )

    if proof_escapes:
        raise SystemExit("proof escape found in: " + ", ".join(proof_escapes))
    if declared_axioms != EXPECTED_DECLARED_AXIOMS:
        raise SystemExit(
            "project axiom declarations drifted: "
            f"expected={sorted(EXPECTED_DECLARED_AXIOMS)} "
            f"observed={sorted(declared_axioms)}"
        )

    theorem_map = (LEAN_ROOT / "TheoremMap.lean").read_text(encoding="utf-8")
    missing_markers = [marker for marker in NUMBERED_MARKERS if marker not in theorem_map]
    if missing_markers:
        raise SystemExit("theorem map lacks numbered markers: " + ", ".join(missing_markers))
    missing_symbols = [symbol for symbol in REQUIRED_MAP_SYMBOLS if symbol not in theorem_map]
    if missing_symbols:
        raise SystemExit("theorem map lacks required consumers: " + ", ".join(missing_symbols))

    lakefile = (ROOT / "lakefile.toml").read_text(encoding="utf-8")
    missing_targets = [target for target in REQUIRED_DEFAULT_TARGETS if f'"{target}"' not in lakefile]
    if missing_targets:
        raise SystemExit("lakefile default target missing: " + ", ".join(missing_targets))

    lake_version = re.search(r'(?m)^version\s*=\s*"([^"]+)"', lakefile)
    citation = (ROOT / "CITATION.cff").read_text(encoding="utf-8")
    citation_version = re.search(r'(?m)^version:\s*([^\s]+)', citation)
    if not lake_version or not citation_version or lake_version.group(1) != citation_version.group(1):
        raise SystemExit("lakefile.toml and CITATION.cff versions are missing or inconsistent")
    if not (ROOT / "LICENSE").is_file():
        raise SystemExit("LICENSE is missing")

    zenodo_path = ROOT / ".zenodo.json"
    if not zenodo_path.is_file():
        raise SystemExit(".zenodo.json is required for the software archive")
    zenodo = json.loads(zenodo_path.read_text(encoding="utf-8"))
    if zenodo.get("version") != lake_version.group(1):
        raise SystemExit("lakefile.toml and .zenodo.json versions are inconsistent")
    if zenodo.get("upload_type") != "software" or zenodo.get("license") != "mit":
        raise SystemExit(".zenodo.json must declare open MIT software")
    expected_creator = {"name": "Li, Alex Chengyu", "orcid": "0009-0008-4516-8946"}
    if expected_creator not in zenodo.get("creators", []):
        raise SystemExit(".zenodo.json lacks the canonical creator and ORCID")
    paper_relation = {
        "identifier": f"https://doi.org/{EXPECTED_PAPER_CONCEPT_DOI}",
        "relation": "isSupplementTo",
        "resource_type": "publication-workingpaper",
    }
    if paper_relation not in zenodo.get("related_identifiers", []):
        raise SystemExit(".zenodo.json lacks the paper concept-DOI supplement relation")

    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    if toolchain != EXPECTED_TOOLCHAIN:
        raise SystemExit(
            f"Lean toolchain drifted: expected={EXPECTED_TOOLCHAIN} observed={toolchain}"
        )
    manifest_path = ROOT / "lake-manifest.json"
    if not manifest_path.is_file():
        raise SystemExit("tracked lake-manifest.json is required for reproducible releases")
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    packages = manifest.get("packages", [])
    mathlib = next(
        (package for package in packages if isinstance(package, dict) and package.get("name") == "mathlib"),
        None,
    )
    if not isinstance(mathlib, dict) or mathlib.get("rev") != EXPECTED_MATHLIB_REV:
        raise SystemExit(
            "Mathlib revision drifted or is absent from lake-manifest.json: "
            f"expected={EXPECTED_MATHLIB_REV} observed={None if mathlib is None else mathlib.get('rev')}"
        )

    print("source policy: 0 proof escapes, exact 3-name project axiom boundary")
    print("publication map: all numbered markers and required default targets present")
    print(
        f"release metadata: version {lake_version.group(1)}, CITATION.cff, .zenodo.json, and LICENSE present"
    )
    print(f"dependency lock: {EXPECTED_TOOLCHAIN}, Mathlib {EXPECTED_MATHLIB_REV}")


def run(command: list[str]) -> str:
    completed = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        encoding="utf-8",
        errors="replace",
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if completed.returncode:
        print(completed.stdout, file=sys.stderr)
        raise SystemExit(f"command failed ({completed.returncode}): {' '.join(command)}")
    return completed.stdout


def check_kernel_outputs(skip_build: bool) -> None:
    if not skip_build:
        print(run(["lake", "build"]), end="")

    theorem_map = run(["lake", "env", "lean", "VerificationAsymmetry/TheoremMap.lean"])
    missing_outputs = [symbol for symbol in REQUIRED_MAP_SYMBOLS if symbol not in theorem_map]
    if missing_outputs:
        raise SystemExit("compiled theorem-map output lacks consumers: " + ", ".join(missing_outputs))

    run(["lake", "env", "lean", "VerificationAsymmetry/PaperExactnessAudit.lean"])
    run(["lake", "env", "lean", "VerificationAsymmetry/CurrentPaperClaimBindings.lean"])

    status = run(["lake", "env", "lean", "VerificationAsymmetry/CurrentPaperStatus.lean"])
    if EXPECTED_STATUS not in status:
        raise SystemExit("current-paper status drifted")

    axiom_output = run(["lake", "env", "lean", "VerificationAsymmetry/CurrentPaperAxiomAudit.lean"])
    observed_current_axioms = set(
        re.findall(r"VerificationAsymmetry\.Economy\.axiom_[A-Za-z0-9_]+", axiom_output)
    )
    if observed_current_axioms != EXPECTED_CURRENT_AXIOMS:
        raise SystemExit(
            "current-paper axiom boundary drifted: "
            f"expected={sorted(EXPECTED_CURRENT_AXIOMS)} "
            f"observed={sorted(observed_current_axioms)}"
        )

    ledger = run(["lake", "env", "lean", "VerificationAsymmetry/Ledger.lean"])
    if EXPECTED_LEDGER not in ledger:
        raise SystemExit("historical-superset ledger inventory drifted")

    print(f"current-paper status: {EXPECTED_STATUS}")
    print("current-paper project axioms: exact 2-name boundary")
    print(f"historical ledger: {EXPECTED_LEDGER}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--skip-build",
        action="store_true",
        help="Reuse an immediately preceding successful `lake build` (used by CI).",
    )
    parser.add_argument(
        "--source-only",
        action="store_true",
        help="Check source policy and release metadata without running Lean commands.",
    )
    args = parser.parse_args()
    check_source_policy()
    if not args.source_only:
        check_kernel_outputs(args.skip_build)
    print("release verification passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
