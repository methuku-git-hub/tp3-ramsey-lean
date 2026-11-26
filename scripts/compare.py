#!/usr/bin/env python3
"""Run actual Comparator and bind its result to the checked source hashes."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument("--lake", default="lake")
parser.add_argument("--no-sandbox", action="store_true")
args = parser.parse_args()
lake = Path(shutil.which(args.lake) or args.lake).resolve()
env = dict(os.environ)
env["PATH"] = str(lake.parent) + os.pathsep + env.get("PATH", "")

def source_manifest():
    files = sorted([*ROOT.glob("*.lean"), *(ROOT / "TP3").glob("*.lean")])
    files += [ROOT / name for name in
              ("comparator.json", "lean-toolchain", "lakefile.toml", "lake-manifest.json")]
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}

before = source_manifest()
command = [str(lake), "comparator", "--config", "comparator.json"]
if args.no_sandbox:
    command.append("--inadvisably-no-sandbox")
logs = ROOT / "verification"
logs.mkdir(exist_ok=True)
with (logs / "comparator-main.log").open("w") as output:
    result = subprocess.run(command, cwd=ROOT, env=env, stdout=output, stderr=subprocess.STDOUT)
log = (logs / "comparator-main.log").read_text()
after = source_manifest()
stable = before == after
lean = "Lean default kernel accepts the solution" in log
nanoda = "nanoda kernel accepts the solution" in log
accepted = result.returncode == 0 and stable and lean and nanoda and "Your solution is okay!" in log
report = {
    "checked_at_utc": datetime.now(timezone.utc).isoformat(),
    "command": command,
    "exit_code": result.returncode,
    "source_stable": stable,
    "exact_comparison_passed": accepted,
    "lean_kernel_accepted": lean,
    "nanoda_accepted": nanoda,
    "sandbox_disabled": args.no_sandbox,
    "log_sha256": hashlib.sha256(log.encode()).hexdigest(),
    "source_sha256": after,
}
(logs / "comparator-status.json").write_text(json.dumps(report, indent=2) + "\n")
print("Comparator, Lean kernel and NanoDa:", "PASS" if accepted else "FAIL")
sys.exit(0 if accepted else 1)
