#!/usr/bin/env python3
"""Public verification gate for the finite arithmetic Kakeya proof supplement."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "verification" / "kakeya_public"
OUT.mkdir(parents=True, exist_ok=True)
MODULES = [
    "OperatorFirst.KakeyaDenominators",
    "OperatorFirst.KakeyaCutCompletion",
    "OperatorFirst.KakeyaForcingBridge",
    "OperatorFirst.KakeyaAuditControls",
    "OperatorFirst.KakeyaCutAssumptionControl",
]
report = {
    "schema": "kakeya-public-verification-v1",
    "status": "RUNNING",
    "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
    "sources": {},
    "checks": {},
    "scope": "finite two-coordinate nonzero-multiple forcing",
}

def run(name, argv, expected_rejection=False):
    p = subprocess.run(argv, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=1200)
    log = OUT / (name + ".log")
    log.write_text(p.stdout)
    report["checks"][name] = {
        "exit_code": p.returncode,
        "expected_rejection": expected_rejection,
        "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest(),
    }
    if expected_rejection:
        if p.returncode == 0:
            raise RuntimeError(name + " was unexpectedly accepted")
        if not re.search(r"unsolved goals|proved that the proposition.*false", p.stdout, re.S):
            raise RuntimeError(name + " did not fail for a mathematical reason")
        if re.search(r"unknown (module|identifier|constant)|unexpected token", p.stdout):
            raise RuntimeError(name + " failed because of infrastructure")
    elif p.returncode != 0:
        raise RuntimeError(name + " failed")
    return p.stdout

try:
    for module in MODULES:
        path = ROOT / (module.replace(".", "/") + ".lean")
        report["sources"][str(path.relative_to(ROOT))] = {
            "bytes": path.stat().st_size,
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        }
    run("build", ["lake", "build", *MODULES])
    for module in MODULES:
        run(module + "_kernel", ["lake", "env", "leanchecker", "-v", module])
    audit = run("declaration_audit",
                ["lake", "env", "lean", "scripts/AuditKakeyaBridges.lean"])
    rows = [json.loads(line.split("AUDIT_JSON ", 1)[1])
            for line in audit.splitlines() if "AUDIT_JSON " in line]
    if len(rows) != 121:
        raise RuntimeError(f"expected 121 audited declarations, found {len(rows)}")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if any(set(row["axioms"]) - allowed or row["kind"] == "axiom" for row in rows):
        raise RuntimeError("unapproved axiom or axiom declaration")
    (OUT / "declarations.json").write_text(json.dumps(rows, indent=2) + "\n")
    negatives = {
        "false_integer_unit":
            "import OperatorFirst.KakeyaAuditControls\n"
            "example : (∃ z : ℤ, 2 * z = 1) := by\n"
            "  have h := OperatorFirst.KakeyaAuditControls.rational_unit_without_integer_unit.2\n"
            "  simp_all\n",
        "false_equal_kernel":
            "import OperatorFirst.KakeyaAuditControls\n"
            "example : LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) = "
            "LinearMap.ker (LinearMap.snd ℚ ℚ ℚ) := by\n"
            "  have h := OperatorFirst.KakeyaAuditControls.same_range_different_kernels.2\n"
            "  simp_all\n",
    }
    for name, source in negatives.items():
        path = OUT / (name + ".lean")
        path.write_text(source)
        run(name, ["lake", "env", "lean", str(path.relative_to(ROOT))], True)
    report["status"] = "PASS"
except Exception as exc:
    report["status"] = "FAIL"
    report["error"] = str(exc)
finally:
    (OUT / "report.json").write_text(json.dumps(report, indent=2) + "\n")
sys.exit(0 if report["status"] == "PASS" else 1)
