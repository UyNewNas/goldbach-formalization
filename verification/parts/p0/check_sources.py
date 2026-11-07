#!/usr/bin/env python3
"""Apply the existing project's source guard to an explicit P0 batch.

This is supplementary to strict elaboration, kernel replay and Lean's
defining-module/transitive-axiom inventory; it does not replace those gates.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[3]
SCANNER = ROOT / "verification/verify_variable_envelope_boxes.py"
spec = importlib.util.spec_from_file_location("chen_existing_source_guard", SCANNER)
assert spec is not None and spec.loader is not None
scanner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(scanner)

if len(sys.argv) < 2:
    raise SystemExit("Supply explicit production/audit module names")

records = []
for module in sys.argv[1:]:
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", module):
        raise SystemExit(f"Invalid module name: {module}")
    path = ROOT / (module.replace(".", "/") + ".lean")
    content = path.read_bytes()
    code = scanner.lean_code(content.decode())
    if re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide|sorryAx)\b", code):
        raise SystemExit(f"Forbidden proof escape in {path.relative_to(ROOT)}")
    if "debug.skipKernelTC" in code:
        raise SystemExit(f"Kernel-check bypass in {path.relative_to(ROOT)}")
    records.append({"module": module, "path": str(path.relative_to(ROOT)),
                    "sha256": hashlib.sha256(content).hexdigest(),
                    "source_guard": "passed"})

print(json.dumps({"scanner": str(SCANNER.relative_to(ROOT)),
                  "scanner_sha256": hashlib.sha256(SCANNER.read_bytes()).hexdigest(),
                  "records": records}, ensure_ascii=False, indent=2))
