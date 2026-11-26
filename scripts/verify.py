#!/usr/bin/env python3
"""Verify completed sources and report, separately, whether the target exists.

This is a local development check, not the Palomar validator. --release exits
nonzero unless the full theorem and the remaining release evidence are present.
It never treats a successful build of supporting lemmas as a completed proof.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument("--lake", default=os.environ.get("TP3_LAKE", "lake"))
parser.add_argument("--release", action="store_true")
args = parser.parse_args()
lake = shutil.which(args.lake) or args.lake
logs = ROOT / "verification"
logs.mkdir(exist_ok=True)

sources = sorted([*ROOT.glob("*.lean"), *(ROOT / "TP3").rglob("*.lean")])
failures = []
for path in sources:
    source = path.read_text()
    if path.is_symlink():
        failures.append(f"Symlinked Lean source: {path.relative_to(ROOT)}")
    if not source.startswith("module\n"):
        failures.append(f"Missing module header: {path.relative_to(ROOT)}")
    if len(source.splitlines()) > 10000:
        failures.append(f"Oversized Lean file: {path.relative_to(ROOT)}")
    if path.name != "Challenge.lean" and re.search(
        r"\b(sorry|admit|native_decide|axiom)\b", source
    ):
        # An indicative source scan; the Lean axiom audit is the authoritative
        # check for the imported proof closures. Ignore comments in this scan.
        clean = re.sub(r"/-.*?-/", "", source, flags=re.S)
        clean = re.sub(r"--[^\n]*", "", clean)
        clean = re.sub(r'"(?:\\.|[^"\\])*"', '""', clean)
        if re.search(r"\b(sorry|admit|native_decide|axiom)\b", clean):
            failures.append(f"Proof-hole/axiom token: {path.relative_to(ROOT)}")

challenge = ROOT / "Challenge.lean"
if len(challenge.read_text().splitlines()) > 1000 or challenge.stat().st_size > 102400:
    failures.append("Challenge exceeds Palomar size limit")

manifest = json.loads((ROOT / "lake-manifest.json").read_text())
for dep in manifest["packages"]:
    if dep.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", dep.get("rev", "")):
        failures.append(f"Dependency is not a pinned Git commit: {dep.get('name')}")
    if not re.fullmatch(r"https://github.com/[^/?#]+/[^/?#]+", dep.get("url", "")):
        failures.append(f"Dependency does not use a plain GitHub HTTPS URL: {dep.get('name')}")

command = [lake, "build", "TP3", "+Challenge:olean", "+Solution:olean", "+AxiomAudit:olean"]
with (logs / "build-and-audit.log").open("w") as output:
    build = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
if build.returncode:
    failures.append("Lean build/axiom audit failed; inspect verification/build-and-audit.log")

# Import only the proof, never Challenge, when probing the target.
probe = subprocess.run(
    [lake, "env", "lean", "--stdin"], cwd=ROOT,
    input="module\nimport Solution\n#check TP3.ramsey_bound\n#print axioms TP3.ramsey_bound\n",
    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
)
(logs / "main-theorem-probe.log").write_text(probe.stdout)
target_present = probe.returncode == 0
release_gaps = []
if not target_present:
    release_gaps.append("The exact main theorem TP3.ramsey_bound is absent from Solution.")
if not (ROOT / "formalization.yaml").is_file():
    release_gaps.append("Final formalization.yaml is absent; only draft metadata exists.")
if not any((ROOT / name).is_file() for name in ("LICENSE", "LICENSE.md", "LICENSE.txt")):
    release_gaps.append("A final root SPDX licence is absent.")
comparison = {}
comparison_file = logs / "comparator-status.json"
if comparison_file.is_file():
    comparison = json.loads(comparison_file.read_text())
comparison_current = bool(comparison.get("exact_comparison_passed"))
for filename, digest in comparison.get("source_sha256", {}).items():
    path = ROOT / filename
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
        comparison_current = False
if not comparison_current:
    release_gaps.append("Current source-bound Comparator/Lean/NanoDa evidence is absent.")
release_gaps.append("Public-commit Palomar preflight and editorial review are separate external gates.")

report = {
    "checked_at_utc": datetime.now(timezone.utc).isoformat(),
    "build_command": command,
    "supporting_development_passed": not failures,
    "main_theorem_present": target_present,
    "main_theorem_proved_and_compared": target_present and comparison_current and not failures,
    "fresh_kernel_replay": "exported_main_proof_accepted" if comparison_current else "not_recorded",
    "comparator_nanoda": "passed" if comparison_current else "not_recorded_for_current_sources",
    "ready_for_registration": False,
    "development_failures": failures,
    "release_gaps": release_gaps,
    "source_sha256": {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sources
    },
}
(logs / "status.json").write_text(json.dumps(report, indent=2) + "\n")
print("Supporting development:", "PASS" if not failures else "FAIL")
print("Main theorem:", "PROVED AND COMPARED" if target_present and comparison_current and not failures
      else ("present; needs exact comparison" if target_present else "NOT PROVED"))
print("Registration:", "NOT READY")
for message in failures:
    print(" -", message)
if args.release:
    for message in release_gaps:
        print(" -", message)
sys.exit(1 if failures else (2 if args.release and release_gaps else 0))
