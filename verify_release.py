#!/usr/bin/env python3
"""Fail-closed release verification for the public Lean companion.

The script is cross-platform and intentionally checks the publication-facing
surfaces rather than treating a successful library build as sufficient.
"""

from __future__ import annotations

import argparse
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
    "closedConditional=6 definitional=6"
)
EXPECTED_STATUS = "current-paper theorem coverage: entries=24 unfinishedDerived=0"
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
REQUIRED_DEFAULT_TARGETS = (
    "VerificationAsymmetry",
    "VerificationAsymmetry.Ledger",
    "VerificationAsymmetry.TheoremMap",
    "VerificationAsymmetry.CurrentPaperStatus",
    "VerificationAsymmetry.CurrentPaperAxiomAudit",
)


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

    print("source policy: 0 proof escapes, exact 3-name project axiom boundary")
    print("publication map: all numbered markers and required default targets present")
    print(f"release metadata: version {lake_version.group(1)}, CITATION.cff and LICENSE present")


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
    if "prop_aggregation_near_cobb_douglas_limit" not in theorem_map:
        raise SystemExit("theorem-map output lacks the near-Cobb-Douglas endpoint")

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
