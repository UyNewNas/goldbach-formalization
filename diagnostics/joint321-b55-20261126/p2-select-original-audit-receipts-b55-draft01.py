import hashlib
import base64
import gzip
import importlib.util
import traceback
import json
import os
from pathlib import Path
import re
import selectors
import subprocess
import sys
import time

root = Path.cwd()
pin = "b55fa93d39e6a4ddf2abd37b9b8481078e329f70"
# The owner submits only after the b55 original strict321 gate succeeds; all eleven repaired source hashes are fixed.
assert re.fullmatch(r"[0-9a-f]{40}", pin), "NEW_COMMIT has not been finalized"
A = "ImbalancedChen.P2OriginalCompactArchivedTotalCandidate"
B = "ImbalancedChen.P2OriginalCompactCachedEndpointCandidate"
W = "ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint"
ordered_expected = "c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f"
snapshot_path = Path("/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json")
snapshot_expected = "ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27"
native_context_expected = "71451bbb4a755fb5ec8744663121d0630ba5afd3d5774f7d0ec7931d9d387e90"
expected = {
    "verification/part2/run_winner9_private_checks.py": "164bc271d8806ed45ebdd71c8f394c4706d7cfdaf4a121b633d738e094bad7ac",
    "verification/part2/run_winner9_private_audit.py": "571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5",
    "verification/part2/winner9_private_audit_template.lean": "2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b",
    "verification/part2/winner9_external_snapshot.py": "a57b658beef42ebfe75ccb09d84f7f1ee7252c289f267396063c93ae5e0bbedf",
    "verification/part2/inspect_winner9_owner_native.py": "9460e319b2f247b4deb6c4c12ad7b59732bfde939f5dc68e541b4a5714aed90d",
    "ImbalancedChen/P2HistoricLogPointInterpreter.lean": "07798022d2370d12091d123a8f55ab106ee08a02b5dd104ce84d30aed3882552",
    "ImbalancedChen/P2OriginalCompactCachedRun.lean": "61ea2a921d3b754feb82b507a7b632c8570cc6a0b35d3d3ebca0c02936553ce9",
    "ImbalancedChen/P2OriginalCompactArchivedTotalCandidate.lean": "03e45537c9309e79c46fd924383d850935cb2b82a5de7ac4205731f4df048fcd",
    "ImbalancedChen/P2OriginalCompactCachedEndpointCandidate.lean": "3f84c653e57cf48266a4160477c94112acbad086028c75652892fb9ab04aecb6",
    "verification/part2/export_winner9_private_evidence.py": "fc0f97f4941339d9c0cb149055b233bf7a0daa3b8eff3da2998c921885948645",
    "ImbalancedChen/P2OriginalCompactWholeFunctionalEndpoint.lean": "606cb2277c031d440cc379aedd4029a8f386f9925d93ccfcb77cf37557d80185",
    "ImbalancedChen/ActualThirdOriginalP4AOrdinaryFiniteSelector.lean": "bc50bc05f214ff8c9716000558c170fb8a92334ff7bd32465616507107f81547",
    "ImbalancedChen/Certificates/OriginalNodeArraysV1/DataCore.lean": "048eda0f169f5842cf3a969e0c05eb1192222ac920e71153b4cecd5e564990a6",
    "ImbalancedChen/P2OriginalAdaptiveForestSourceIdentity.lean": "e948aa494518fc9fda2aedeee99e4c8b8f9d27be9cd64692036f1ad0e3e06ce6",
    "ImbalancedChen/P2OriginalCompactConcreteLoop.lean": "04d6475a718cb7fd237ca52e7ee0d6555f23783cd39e6f9d92ac63ceca24c2d0",
    "ImbalancedChen/P2OriginalCompactConcreteRun.lean": "18f347ca0c231e7bcceca4e7752908bb311052b01495e839ffcef48aacd0ffd2",
    "ImbalancedChen/P2OriginalCompactQ80ArrayTable.lean": "b07fe6df9a3434301d2af52a6c54b02bd8f6bc6b9dbdd7e957244cf78d337b1d",
    "ImbalancedChen/P2OriginalCompactQ80Encloser.lean": "139686b3a2f5453350faf6495ac30424fbe71aa472ae3eba7d3475e1a0fd5058",
    "ImbalancedChen/P2OriginalPriorityForestLedger.lean": "11e2a50288146a94cbb6351fd6f5b279469c6cce1d6af437569260d54880cc0c",
    "ImbalancedChen/P2OriginalCompactQ80Reachability.lean": "6f78f1f03b58666d7c968bbcebd6d7c72a680ed8340a685c67404ea2a873c5fb",
    "ImbalancedChen/P2OriginalCompactQ80FixedBindings.lean": "ba24af1a733626cafc3d53d5fc5294c021879b7503c639f4ef97b937cbd00cc9"
}

def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()

def json_digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()

def check_source():
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip() == pin
    assert not subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"], text=True).strip()
    actual = {name: digest(root / name) for name in expected}
    assert actual == expected, "Pinned source or original verifier bytes changed"

check_source()
sys.path.insert(0, str(root / "verification/part2"))
from run_winner9_private_audit import LEAN, LEANCHECKER, MATHLIB, PIN, project_nodes, snapshot, verify_compilation
from winner9_external_snapshot import ExternalSnapshot, mark_project_nodes

assert PIN == "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1"
runtime_expected = {
    LEAN: "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",
    LEANCHECKER: "ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a",
}
assert {name: digest(name) for name in runtime_expected} == runtime_expected
assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=MATHLIB, text=True).strip() == PIN
assert digest(snapshot_path) == snapshot_expected
roots = [
    "ImbalancedChen.P2OriginalCompactQ80CompleteSoundness",
    "ImbalancedChen.P2OriginalCompactCachedRun",
    "ImbalancedChen.P2OriginalCompactQ80FixedBindings",
    "ImbalancedChen.P4AOrdinaryRootFirstIntegral",
    "ImbalancedChen.Part4ActualThirdFiniteDensityReserve",
]
full_nodes = project_nodes(root, W)
full = list(full_nodes)
assert len(full) == 324 and len(set(full)) == 324
assert hashlib.sha256(("\n".join(full) + "\n").encode()).hexdigest() == ordered_expected
prereq_nodes = {}
for name in roots:
    prereq_nodes.update(project_nodes(root, name))
assert len(prereq_nodes) == 321
assert set(full) - set(prereq_nodes) == {A, B, W}
assert A not in prereq_nodes and B not in prereq_nodes and W not in prereq_nodes
a_nodes = project_nodes(root, A)
assert len(a_nodes) == 102 and A in a_nodes
assert set(a_nodes) - {A} <= set(prereq_nodes)
assert len(project_nodes(root, B)) == 103
sources_before = {name: digest(node["source"]) for name, node in full_nodes.items()}
lib = root / ".lake/p2-private/lib"
registry = root / ".lake/p2-private/records.json"
external = ExternalSnapshot(snapshot_path, lean=LEAN, mathlib_pin=PIN, project_lib=lib)
native_before = external.binding()
assert native_before["snapshot_sha256"] == snapshot_expected
assert native_before["context_signature"] == native_context_expected
assert native_before["verification_helper_sha256"] == expected["verification/part2/winner9_external_snapshot.py"]
assert Path(external.value["runtime"]["leanchecker"]).resolve() == Path(LEANCHECKER).resolve()
assert external.files[external.value["runtime"]["leanchecker"]]["sha256"] == runtime_expected[LEANCHECKER]
mark_project_nodes(full_nodes, set(external.modules))
toolchain = {
    "lean_version": subprocess.check_output([LEAN, "--version"], text=True).strip(),
    "lean_binary_sha256": runtime_expected[LEAN],
    "mathlib_commit": PIN,
}
common = [sys.executable, "-B", "verification/part2/run_winner9_private_checks.py",
          "--baseline-root", "/workspace/p2-4-compact-proof-20261125/.lake/p24-baseline-8657/attempt-001",
          "--external-snapshot", str(snapshot_path),
          "--memory-mb", "11264", "--workers", "1", "--threads", "1"]
SELECTION_HELPER_BASE64 = 'IyEvdXNyL2Jpbi9lbnYgcHl0aG9uMwoiIiJTY2hlZHVsZSBvcmlnaW5hbCBhdWRpdHMgdXNpbmcgdGhlIGZyb3plbiBleHBvcnRlcidzIGV4YWN0IHNlbGVjdGlvbiBibG9jay4KClRoaXMgaGVscGVyIGRvZXMgbm90IHJlcGxhY2UgdGhlIG9yaWdpbmFsIGF1ZGl0IHJ1bm5lciBvciBmaW5hbCBmdWxsIGV4cG9ydC4KSXQgZXhlY3V0ZXMgdGhlIHVubW9kaWZpZWQgcmVjZWlwdC1zZWxlY3Rpb24gQVNUIGZyb20gdGhlIFNIQS1waW5uZWQgZXhwb3J0ZXIsCmluY2x1ZGluZyBpdHMgb3JpZ2luYWwgdmFsaWRhdGVfcmVjZWlwdCwgYXJ0aWZhY3QgY2FwdHVyZSwgY2FuZGlkYXRlIG9yZGVyIGFuZApkdXBsaWNhdGUtcmVjZWlwdCBoYW5kbGluZy4gSXQgb21pdHMgb25seSBhcmNoaXZlL3Byb3ZlbmFuY2UgcGFja2FnaW5nLCB3aGljaCBpcwpub3QgbmVlZGVkIHRvIGNob29zZSB0aGUgbmV4dCBvcmlnaW5hbCBhdWRpdCBiYXRjaC4KIiIiCmZyb20gX19mdXR1cmVfXyBpbXBvcnQgYW5ub3RhdGlvbnMKCmltcG9ydCBhc3QKZnJvbSBjb2xsZWN0aW9ucyBpbXBvcnQgZGVmYXVsdGRpY3QKaW1wb3J0IGhhc2hsaWIKaW1wb3J0IGltcG9ydGxpYgppbXBvcnQganNvbgpmcm9tIHBhdGhsaWIgaW1wb3J0IFBhdGgKaW1wb3J0IHN5cwoKRVhQT1JURVJfU0hBMjU2ID0gImZjMGY5N2Y0OTQxMzM5ZDljMGNiMTQ5MDU1YjIzM2JmN2EwZGFhM2I4ZWZmM2RhMjk5OGM5MjE4ODU5NDg2NDUiCkFVRElUX1NIQTI1NiA9ICI1NzFiNjEzN2RhNWUxYTFjZjllYzkwMjBlMDNiNGY4ODFiYzRmMGYzZjM2ZWFlMGFhOWQ2MmEzYTVjMDkzOWQ1IgoKCmRlZiBzaGEocGF0aDogUGF0aCkgLT4gc3RyOgogICAgd2l0aCBwYXRoLm9wZW4oInJiIikgYXMgc3RyZWFtOgogICAgICAgIHJldHVybiBoYXNobGliLmZpbGVfZGlnZXN0KHN0cmVhbSwgInNoYTI1NiIpLmhleGRpZ2VzdCgpCgoKZGVmIHNlbGVjdF9jdXJyZW50KHJvb3Q6IFBhdGgsIHRhcmdldHM6IGxpc3Rbc3RyXSkgLT4gZGljdDoKICAgIHJvb3QgPSByb290LnJlc29sdmUoKQogICAgZXhwb3J0ZXJfcGF0aCA9IHJvb3QgLyAidmVyaWZpY2F0aW9uL3BhcnQyL2V4cG9ydF93aW5uZXI5X3ByaXZhdGVfZXZpZGVuY2UucHkiCiAgICBhdWRpdF9wYXRoID0gcm9vdCAvICJ2ZXJpZmljYXRpb24vcGFydDIvcnVuX3dpbm5lcjlfcHJpdmF0ZV9hdWRpdC5weSIKICAgIGFzc2VydCBzaGEoZXhwb3J0ZXJfcGF0aCkgPT0gRVhQT1JURVJfU0hBMjU2CiAgICBhc3NlcnQgc2hhKGF1ZGl0X3BhdGgpID09IEFVRElUX1NIQTI1NgogICAgc3lzLnBhdGguaW5zZXJ0KDAsIHN0cihleHBvcnRlcl9wYXRoLnBhcmVudCkpCiAgICBvcmlnaW5hbCA9IGltcG9ydGxpYi5pbXBvcnRfbW9kdWxlKCJleHBvcnRfd2lubmVyOV9wcml2YXRlX2V2aWRlbmNlIikKICAgIGFzc2VydCBQYXRoKG9yaWdpbmFsLl9fZmlsZV9fKS5yZXNvbHZlKCkgPT0gZXhwb3J0ZXJfcGF0aAogICAgbGl2ZV9waW4gPSBvcmlnaW5hbC5zdWJwcm9jZXNzLmNoZWNrX291dHB1dCgKICAgICAgICBbImdpdCIsICJyZXYtcGFyc2UiLCAiSEVBRCJdLCBjd2Q9b3JpZ2luYWwuTUFUSExJQiwgdGV4dD1UcnVlKS5zdHJpcCgpCiAgICBvcmlnaW5hbC5yZXF1aXJlKGxpdmVfcGluID09IG9yaWdpbmFsLlBJTiwKICAgICAgICAgICAgICAgICAgICAgIkxpdmUgTWF0aGxpYiBjaGVja291dCBkaWZmZXJzIGZyb20gdGhlIGZpeGVkIHBpbiIpCiAgICBzb3VyY2UgPSBleHBvcnRlcl9wYXRoLnJlYWRfdGV4dCgpCiAgICB0cmVlID0gYXN0LnBhcnNlKHNvdXJjZSwgZmlsZW5hbWU9c3RyKGV4cG9ydGVyX3BhdGgpKQogICAgbWFpbnMgPSBbbiBmb3IgbiBpbiB0cmVlLmJvZHkgaWYgaXNpbnN0YW5jZShuLCBhc3QuRnVuY3Rpb25EZWYpIGFuZCBuLm5hbWUgPT0gIm1haW4iXQogICAgYXNzZXJ0IGxlbihtYWlucykgPT0gMQogICAgbG9vcHMgPSBbbiBmb3IgbiBpbiBtYWluc1swXS5ib2R5IGlmIGlzaW5zdGFuY2UobiwgYXN0LkZvcikKICAgICAgICAgICAgIGFuZCBpc2luc3RhbmNlKG4udGFyZ2V0LCBhc3QuTmFtZSkgYW5kIG4udGFyZ2V0LmlkID09ICJ0YXJnZXQiCiAgICAgICAgICAgICBhbmQgaXNpbnN0YW5jZShuLml0ZXIsIGFzdC5OYW1lKSBhbmQgbi5pdGVyLmlkID09ICJ0YXJnZXRzIl0KICAgIGFzc2VydCBsZW4obG9vcHMpID09IDEKICAgIGxvb3AgPSBsb29wc1swXQogICAgb3JpZ2luYWxfYmxvY2sgPSBhc3QuZ2V0X3NvdXJjZV9zZWdtZW50KHNvdXJjZSwgbG9vcCkKICAgIGFzc2VydCBvcmlnaW5hbF9ibG9jayBpcyBub3QgTm9uZQogICAgZHJpdmVyX3BhdGhzID0gWwogICAgICAgIHJvb3QgLyAiZG9jcy92ZXJpZmljYXRpb24vMjAyNjExMjQtcDItcHJpdmF0ZS9kcml2ZXItdjEucHkiLAogICAgICAgIHJvb3QgLyAiZG9jcy92ZXJpZmljYXRpb24vMjAyNjExMjQtcDItcHJpdmF0ZS9hdWRpdC1kcml2ZXItdjIucHkiLAogICAgICAgIHJvb3QgLyAiZG9jcy92ZXJpZmljYXRpb24vMjAyNjExMjUtcDItcmVzdW1lL2F1ZGl0LWRyaXZlci12My5weSIsCiAgICAgICAgYXVkaXRfcGF0aCwKICAgIF0KICAgIGRyaXZlcnMgPSB7c2hhKHApOiBwIGZvciBwIGluIGRyaXZlcl9wYXRocyBpZiBwLmlzX2ZpbGUoKSBhbmQgc2hhKHApIGluIG9yaWdpbmFsLkRSSVZFUl9GSUxFU30KICAgIG9yaWdpbmFsLnJlcXVpcmUoe29yaWdpbmFsLkRSSVZFUl9WMSwgb3JpZ2luYWwuRFJJVkVSX1YyfSA8PSBzZXQoZHJpdmVycyksCiAgICAgICAgICAgICAgICAgICAgICJCb3RoIGV4YWN0IGhpc3RvcmljYWwgYXVkaXQgZHJpdmVyIHZlcnNpb25zIG11c3QgYmUgYXZhaWxhYmxlIikKICAgIHJlZ2lzdHJ5X3BhdGggPSByb290IC8gIi5sYWtlL3AyLXByaXZhdGUvcmVjb3Jkcy5qc29uIgogICAgcmVnaXN0cnlfcmF3ID0gcmVnaXN0cnlfcGF0aC5yZWFkX2J5dGVzKCkKICAgIHJlZ2lzdHJ5X3NoYTI1NiA9IGhhc2hsaWIuc2hhMjU2KHJlZ2lzdHJ5X3JhdykuaGV4ZGlnZXN0KCkKICAgIGV2aWRlbmNlID0gb3JpZ2luYWwuRXZpZGVuY2UoKQogICAgZm9yIGRyaXZlcl9zaGEsIHBhdGggaW4gZHJpdmVycy5pdGVtcygpOgogICAgICAgIG9yaWdpbmFsLnJlcXVpcmUoZXZpZGVuY2UuZnJlZXplKHBhdGgpID09IGRyaXZlcl9zaGEsCiAgICAgICAgICAgICAgICAgICAgICAgICAiSGlzdG9yaWNhbCBhdWRpdCBkcml2ZXIgY2hhbmdlZCBiZWZvcmUgc2VsZWN0aW9uOiAiICsgc3RyKHBhdGgpKQogICAgY29udGV4dCA9IGRpY3QodmFycyhvcmlnaW5hbCkpCiAgICBjb250ZXh0LnVwZGF0ZShyb290PXJvb3QsIGF1ZGl0X3Jvb3Q9cm9vdCAvICIubGFrZS9wMi1wcml2YXRlL2F1ZGl0IiwKICAgICAgICAgICAgICAgICAgIHJlY29yZHM9anNvbi5sb2FkcyhyZWdpc3RyeV9yYXcpLCBldmlkZW5jZT1ldmlkZW5jZSwgZHJpdmVycz1kcml2ZXJzLAogICAgICAgICAgICAgICAgICAgdGFyZ2V0cz1zb3J0ZWQoc2V0KHRhcmdldHMpKSwgY29tbW9uPXNldCgpLCBtb2R1bGVfZmlsZXM9e30sCiAgICAgICAgICAgICAgICAgICBhY2NlcHRlZD17fSwgcmVqZWN0ZWQ9W10sIHVuc2VsZWN0ZWQ9W10sIHdhcm5pbmdzPVtdLAogICAgICAgICAgICAgICAgICAgcHJvamVjdF91bmlvbj17fSwgb3duZWRfbmFtZXM9ZGVmYXVsdGRpY3QobGlzdCkpCiAgICBwcm9ncmFtID0gYXN0Lk1vZHVsZShib2R5PVtsb29wXSwgdHlwZV9pZ25vcmVzPVtdKQogICAgZXhlYyhjb21waWxlKHByb2dyYW0sIHN0cihleHBvcnRlcl9wYXRoKSwgImV4ZWMiKSwgY29udGV4dCwgY29udGV4dCkKICAgIGV2aWRlbmNlLnZlcmlmeV9mcm96ZW4oKQogICAgIyBQcmVzZXJ2ZSB0aGUgZXhhY3QgY2FwdHVyZWQgcmVjZWlwdC9hcnRpZmFjdCBieXRlcyB0aHJvdWdoIHRoaXMgcmVhZC1vbmx5CiAgICAjIHNlbGVjdGlvbi4gVGhlc2UgYXJlIGFkZGl0aW9ucyB0byB0aGUgb3JpZ2luYWwgc2VsZWN0aW9uIGNoZWNrcy4KICAgIGZvciBpdGVtIGluIGV2aWRlbmNlLmZpbGVzLnZhbHVlcygpOgogICAgICAgIG9yaWdpbiA9IFBhdGgoaXRlbVsib3JpZ2luIl0pCiAgICAgICAgaWYgb3JpZ2luLmlzX2Fic29sdXRlKCk6CiAgICAgICAgICAgIG9yaWdpbmFsLnJlcXVpcmUoc2hhKG9yaWdpbikgPT0gaXRlbVsic2hhMjU2Il0sCiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIkNhcHR1cmVkIGV2aWRlbmNlIGNoYW5nZWQgZHVyaW5nIHNlbGVjdGlvbjogIiArIHN0cihvcmlnaW4pKQogICAgb3JpZ2luYWwucmVxdWlyZShzaGEocmVnaXN0cnlfcGF0aCkgPT0gcmVnaXN0cnlfc2hhMjU2LAogICAgICAgICAgICAgICAgICAgICAiQ29tcGlsZSByZWdpc3RyeSBjaGFuZ2VkIGR1cmluZyBzZWxlY3Rpb24iKQogICAgb3JpZ2luYWwucmVxdWlyZShzaGEoZXhwb3J0ZXJfcGF0aCkgPT0gRVhQT1JURVJfU0hBMjU2IGFuZCBzaGEoYXVkaXRfcGF0aCkgPT0gQVVESVRfU0hBMjU2LAogICAgICAgICAgICAgICAgICAgICAiT3JpZ2luYWwgZXZpZGVuY2UgdG9vbHMgY2hhbmdlZCBkdXJpbmcgc2VsZWN0aW9uIikKICAgIGxpdmVfcGluX2FmdGVyID0gb3JpZ2luYWwuc3VicHJvY2Vzcy5jaGVja19vdXRwdXQoCiAgICAgICAgWyJnaXQiLCAicmV2LXBhcnNlIiwgIkhFQUQiXSwgY3dkPW9yaWdpbmFsLk1BVEhMSUIsIHRleHQ9VHJ1ZSkuc3RyaXAoKQogICAgb3JpZ2luYWwucmVxdWlyZShsaXZlX3Bpbl9hZnRlciA9PSBvcmlnaW5hbC5QSU4sCiAgICAgICAgICAgICAgICAgICAgICJMaXZlIE1hdGhsaWIgY2hlY2tvdXQgY2hhbmdlZCBkdXJpbmcgc2VsZWN0aW9uIikKICAgIGR1cGxpY2F0ZXMgPSB7bjogb3duZXJzIGZvciBuLCBvd25lcnMgaW4gY29udGV4dFsib3duZWRfbmFtZXMiXS5pdGVtcygpIGlmIGxlbihvd25lcnMpID4gMX0KICAgIG9yaWdpbmFsLnJlcXVpcmUobm90IGR1cGxpY2F0ZXMsICJEdXBsaWNhdGUgb3duZWQgZGVjbGFyYXRpb24gbmFtZXMgYWNyb3NzIHNlbGVjdGVkIG1vZHVsZXMiKQogICAgYWNjZXB0ZWQgPSBjb250ZXh0WyJhY2NlcHRlZCJdCiAgICB1bnNlbGVjdGVkID0gY29udGV4dFsidW5zZWxlY3RlZCJdCiAgICBvcmlnaW5hbC5yZXF1aXJlKHNldChhY2NlcHRlZCkuaXNkaXNqb2ludCh1bnNlbGVjdGVkKQogICAgICAgICAgICAgICAgICAgICBhbmQgc2V0KGFjY2VwdGVkKSB8IHNldCh1bnNlbGVjdGVkKSA9PSBzZXQodGFyZ2V0cyksCiAgICAgICAgICAgICAgICAgICAgICJTZWxlY3RlZC91bnNlbGVjdGVkIHBhcnRpdGlvbiBkaWZmZXJzIGZyb20gcmVxdWVzdGVkIHNjb3BlIikKICAgIHJldHVybiB7CiAgICAgICAgInNlbGVjdGlvbl9vbmx5IjogVHJ1ZSwKICAgICAgICAiZmluYWxfb3JpZ2luYWxfZXhwb3J0X3N0aWxsX3JlcXVpcmVkIjogVHJ1ZSwKICAgICAgICAib3JpZ2luYWxfZXhwb3J0ZXJfc2hhMjU2IjogRVhQT1JURVJfU0hBMjU2LAogICAgICAgICJvcmlnaW5hbF9hdWRpdF9kcml2ZXJfc2hhMjU2IjogQVVESVRfU0hBMjU2LAogICAgICAgICJ1bmNoYW5nZWRfc2VsZWN0aW9uX2Jsb2NrX3NoYTI1NiI6IGhhc2hsaWIuc2hhMjU2KG9yaWdpbmFsX2Jsb2NrLmVuY29kZSgpKS5oZXhkaWdlc3QoKSwKICAgICAgICAicmVjb3Jkc19zbmFwc2hvdF9zaGEyNTYiOiByZWdpc3RyeV9zaGEyNTYsCiAgICAgICAgImFjY2VwdGVkX21vZHVsZV9jb3VudCI6IGxlbihhY2NlcHRlZCksCiAgICAgICAgIm93bmVkX2RlY2xhcmF0aW9uX2NvdW50Ijogc3VtKHhbImRlY2xhcmF0aW9uX2NvdW50Il0gZm9yIHggaW4gYWNjZXB0ZWQudmFsdWVzKCkpLAogICAgICAgICJ1bmlxdWVfb3duZWRfZGVjbGFyYXRpb25fY291bnQiOiBsZW4oY29udGV4dFsib3duZWRfbmFtZXMiXSksCiAgICAgICAgImR1cGxpY2F0ZV9vd25lZF9kZWNsYXJhdGlvbnMiOiBkdXBsaWNhdGVzLAogICAgICAgICJhY2NlcHRlZF9tb2R1bGVzIjogYWNjZXB0ZWQsCiAgICAgICAgInVuc2VsZWN0ZWRfbW9kdWxlcyI6IHVuc2VsZWN0ZWQsCiAgICAgICAgInJlamVjdGVkX2NhbmRpZGF0ZXMiOiBjb250ZXh0WyJyZWplY3RlZCJdLAogICAgICAgICJ3YXJuaW5ncyI6IGNvbnRleHRbIndhcm5pbmdzIl0sCiAgICAgICAgImZ1bGxfcDJfY29tcGxldGUiOiBGYWxzZSwKICAgIH0K'

# This tail is appended to the unchanged b55 A wrapper's source/runtime/scope setup.
# No A gate, audit runner, final exporter main, or package operation is invoked.
out = Path("/workspace/p24-current-audit-receipt-selection-b55-20261126/attempt-001")
assert not out.exists(), "Preserve every earlier selection attempt"
out.mkdir(parents=True, exist_ok=False)
selection_helper_sha = "0b2798884008c0de0827c8668e828c2bcf236f2e81ec5a2a1eadce9e1769d6be"
selection_block_sha = "6f8d699df12e76a747efe2893ef5a0ff76654357dedacc15bf0ec95f13d52b53"
helper_path = out / "select_original_audit_receipts.py"
helper_raw = base64.b64decode(SELECTION_HELPER_BASE64, validate=True)
assert hashlib.sha256(helper_raw).hexdigest() == selection_helper_sha
helper_path.write_bytes(helper_raw)

def file_info(path):
    path = Path(path)
    return {"path": str(path), "bytes": path.stat().st_size, "sha256": digest(path)}

def write_json(name, value):
    path = out / name
    with path.open("x", encoding="utf-8") as stream:
        stream.write(json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n")
    return file_info(path)

def write_json_gzip(name, value):
    # Preserve the complete serialized JSON; no loose large JSON or registry copy.
    raw = (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode()
    path = out / name
    with path.open("xb") as stream:
        with gzip.GzipFile(filename="", mode="wb", fileobj=stream, compresslevel=9, mtime=0) as compressed:
            compressed.write(raw)
    observed = hashlib.sha256()
    observed_bytes = 0
    with gzip.open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            observed.update(chunk)
            observed_bytes += len(chunk)
    raw_sha = hashlib.sha256(raw).hexdigest()
    assert observed_bytes == len(raw) and observed.hexdigest() == raw_sha
    return {"gzip": file_info(path), "uncompressed_json_bytes": len(raw),
            "uncompressed_json_sha256": raw_sha, "lossless_roundtrip_verified": True}

checks, errors = {}, []
artifacts = {}
before_frozen = None
registry_raw_before = None
records_before = None
pre_rc = None
pre_summary = None
pre_seconds = None
selection = None
selection_started = False

def perform(name, action):
    try:
        action()
        checks[name] = True
    except Exception as error:
        checks[name] = False
        errors.append({"check": name, "type": type(error).__name__, "error": str(error),
                       "traceback": traceback.format_exc()})

def check_runtime_native():
    assert {name: digest(name) for name in runtime_expected} == runtime_expected
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=MATHLIB, text=True).strip() == PIN
    assert digest(snapshot_path) == snapshot_expected
    assert external.verify() == native_before

def get_current_snapshot():
    current = project_nodes(root, W)
    assert list(current) == full
    assert {name: digest(node["source"]) for name, node in current.items()} == sources_before
    mark_project_nodes(current, set(external.modules))
    return snapshot(root, lib, current, toolchain, external)

def check_complete_inputs():
    check_source()
    check_runtime_native()
    assert registry.read_bytes() == registry_raw_before, "Complete compilation registry changed"
    current = get_current_snapshot()
    assert current == before_frozen, "Full324 source/object/tool/native snapshot changed"
    verify_compilation(json.loads(registry_raw_before), prereq_nodes, current)
    assert digest(helper_path) == selection_helper_sha

def parse_original_summary(path):
    summaries = []
    required = {"roots", "successful_closure", "failed_or_blocked", "pending", "complete", "exit_code", "total"}
    with path.open("rb") as stream:
        for line in stream:
            try:
                value = json.loads(line)
            except (ValueError, UnicodeDecodeError):
                continue
            if isinstance(value, dict) and required <= value.keys():
                summaries.append(value)
    assert len(summaries) == 1, "Expected one complete original zero-budget summary"
    return summaries[0]

print("P24_CURRENT_RECEIPT_SELECTION_BEGIN " + json.dumps({
    "source_pin": pin, "scope": 324, "ordered_fingerprint": ordered_expected,
    "prerequisite_scope": 321, "selection_only": True,
    "output_directory": str(out), "audit_started": False, "final_export_started": False,
    "full324_credit": False}), flush=True)

try:
    registry_raw_before = registry.read_bytes()
    records_before = json.loads(registry_raw_before)
    # The unchanged original zero-budget checker writes canonical registry JSON.
    # Refuse first if that write would alter any existing record or byte.
    persisted = {name: (dict(row, exit_code=125, new_strict_compile=False)
                       if row.get("external_check", {}).get("status") == "PENDING_BATCH_POSTCHECK" else row)
                 for name, row in records_before.items()}
    assert (json.dumps(persisted, indent=2, sort_keys=True) + "\n").encode() == registry_raw_before, \
        "Original zero-budget registry persistence would change existing bytes"
    assert lib.is_dir() and (root / ".lake/p2-private/logs").is_dir()
    for name in prereq_nodes:
        assert records_before.get(name, {}).get("object") == str(lib / (name.replace(".", "/") + ".olean")), \
            "Original zero-budget reuse would rebind an object path: " + name
    baseline_lib = Path("/workspace/p2-4-compact-proof-20261125/.lake/p24-baseline-8657/attempt-001/.lake/build/lib/lean")
    assert baseline_lib.is_dir()
    for source in baseline_lib.rglob("*"):
        if source.is_file():
            assert (lib / source.relative_to(baseline_lib)).is_file(), \
                "Original zero-budget driver would copy a missing baseline file: " + str(source)
    check_runtime_native()
    before_frozen = get_current_snapshot()
    assert before_frozen["external_snapshot"] == native_before
    verify_compilation(records_before, prereq_nodes, before_frozen)
    checks["original321_valid_before_zero_gate"] = True
    artifacts["full324_before"] = write_json_gzip("full324-before.json.gz", before_frozen)
    artifacts["scope"] = write_json("scope.json", {
        "source_pin": pin, "full324_topological_order": full,
        "ordered_fingerprint": ordered_expected,
        "symbolic321_topological_order": [name for name in full if name in prereq_nodes],
        "finite_modules": [A, B, W]})
    artifacts["before_binding"] = write_json("before-binding.json", {
        "source_pin": pin, "registry": {"path": str(registry), "bytes": len(registry_raw_before),
            "sha256": hashlib.sha256(registry_raw_before).hexdigest()},
        "source_sha256": sources_before, "pinned_files": expected,
        "runtime": runtime_expected, "native": native_before,
        "selection_helper": file_info(helper_path), "full324_snapshot": artifacts["full324_before"]})

    command = common + ["--time-budget-seconds", "0", *roots]
    log_path = out / "zero321-original.log"
    started = time.monotonic()
    with log_path.open("xb") as log:
        child = subprocess.run(command, cwd=root, stdout=log, stderr=subprocess.STDOUT)
    pre_rc = child.returncode
    pre_seconds = time.monotonic() - started
    artifacts["zero321_log"] = file_info(log_path)
    pre_summary = parse_original_summary(log_path)
    artifacts["zero321_result"] = write_json("zero321-result.json", {
        "command": command, "exit_code": pre_rc, "elapsed_seconds": pre_seconds,
        "original_summary": pre_summary, "log": artifacts["zero321_log"]})
    assert pre_summary["roots"] == roots and pre_summary["total"] == 321
    assert pre_summary["time_budget_seconds"] == 0 and pre_summary["exit_code"] == pre_rc
    assert pre_summary["complete"] == (pre_rc == 0)
    assert pre_summary["successful_closure"] + len(pre_summary["failed_or_blocked"]) + len(pre_summary["pending"]) == 321
    assert pre_rc == 0 and pre_summary["successful_closure"] == pre_summary["reused"] == 321
    assert not pre_summary["failed_or_blocked"] and not pre_summary["pending"]
    checks["original_zero321_all_reuse"] = True
    check_complete_inputs()
    checks["all_protected_inputs_unchanged_after_zero_gate"] = True

    spec = importlib.util.spec_from_file_location("p24_exact_original_receipt_selector", helper_path)
    assert spec is not None and spec.loader is not None
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    assert Path(helper.__file__).resolve() == helper_path.resolve()
    selection_started = True
    selection = helper.select_current(root, full)
    assert selection["selection_only"] is True and selection["final_original_export_still_required"] is True
    assert selection["original_exporter_sha256"] == expected["verification/part2/export_winner9_private_evidence.py"]
    assert selection["original_audit_driver_sha256"] == expected["verification/part2/run_winner9_private_audit.py"]
    assert selection["unchanged_selection_block_sha256"] == selection_block_sha
    assert selection["records_snapshot_sha256"] == hashlib.sha256(registry_raw_before).hexdigest()
    accepted = set(selection["accepted_modules"])
    unselected = set(selection["unselected_modules"])
    assert len(selection["unselected_modules"]) == len(unselected)
    assert accepted.isdisjoint(unselected) and accepted | unselected == set(full)
    assert selection["accepted_module_count"] == len(accepted)
    assert not selection["duplicate_owned_declarations"]
    artifacts["selection"] = write_json_gzip("full324-original-selection.json.gz", selection)
    checks["original_selector_complete_partition"] = True
except Exception as error:
    errors.append({"check": "original_prerequisite_or_selection", "type": type(error).__name__,
                   "error": str(error), "traceback": traceback.format_exc()})
finally:
    if registry_raw_before is not None and before_frozen is not None:
        perform("all_protected_inputs_unchanged_final", check_complete_inputs)
        def capture_after():
            artifacts["full324_after"] = write_json_gzip("full324-after.json.gz", get_current_snapshot())
            assert artifacts["full324_after"]["uncompressed_json_sha256"] == artifacts["full324_before"]["uncompressed_json_sha256"]
        perform("full324_after_snapshot_recorded_equal", capture_after)

passed = checks.get("original_selector_complete_partition") is True and not errors
exit_code = pre_rc if pre_rc is not None and pre_rc != 0 else (0 if passed else 125)
if errors:
    artifacts["errors"] = write_json_gzip("errors.json.gz", errors)
accepted_names = set(selection["accepted_modules"]) if selection is not None else set()
unselected_names = set(selection["unselected_modules"]) if selection is not None else set()
receipt = {
    "source_pin": pin, "purpose": "full324 original receipt selection for scheduling only",
    "selection_only": True, "selection_started": selection_started, "selection_passed": passed,
    "scope": 324, "ordered_fingerprint": ordered_expected,
    "prerequisite_scope": 321, "zero321_exit_code": pre_rc, "zero321_seconds": pre_seconds,
    "zero321_original_summary": pre_summary,
    "accepted_count": len(accepted_names) if selection is not None else None,
    "unselected_count": len(unselected_names) if selection is not None else None,
    "eligible_missing_symbolic_count": len(unselected_names & set(prereq_nodes)) if selection is not None else None,
    "existing_finite_receipt_selection": {name: ("accepted" if name in accepted_names else "unselected") for name in (A, B, W)} if selection is not None else None,
    "registry_sha256_before": hashlib.sha256(registry_raw_before).hexdigest() if registry_raw_before is not None else None,
    "registry_sha256_after": digest(registry),
    "native_context_signature": native_context_expected, "selection_helper_sha256": selection_helper_sha,
    "original_selection_block_sha256": selection_block_sha,
    "checks": checks, "error_count": len(errors), "artifacts": artifacts,
    "audit_started": False, "final_export_started": False, "registry_loose_copy_written": False,
    "A_credit": False, "B_credit": False, "W_credit": False,
    "new_owned_audit_credit": False, "full324_credit": False,
    "final_original_export_still_required": True, "wrapper_exit_code": exit_code,
}
receipt_info = write_json("receipt.json", receipt)
if passed:
    for name in full:
        print("P24_CURRENT_RECEIPT_TARGET " + json.dumps({"module": name,
            "status": "accepted" if name in accepted_names else "unselected",
            "symbolic": name in prereq_nodes}), flush=True)
print("P24_CURRENT_RECEIPT_SELECTION_DONE " + json.dumps({
    "receipt": receipt_info, "source_pin": pin, "selection_passed": passed,
    "scope": 324, "accepted_count": receipt["accepted_count"], "unselected_count": receipt["unselected_count"],
    "eligible_missing_symbolic_count": receipt["eligible_missing_symbolic_count"],
    "zero321_exit_code": pre_rc, "zero321_seconds": pre_seconds,
    "registry_sha256_before": receipt["registry_sha256_before"], "registry_sha256_after": receipt["registry_sha256_after"],
    "selection_artifact": artifacts.get("selection"), "checks": checks, "error_count": len(errors),
    "errors_artifact": artifacts.get("errors"), "wrapper_exit_code": exit_code,
    "audit_started": False, "final_export_started": False, "full324_credit": False}), flush=True)
raise SystemExit(exit_code)
