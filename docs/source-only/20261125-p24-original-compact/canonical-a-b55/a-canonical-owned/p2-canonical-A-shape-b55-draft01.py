import gzip
import io
import hashlib
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

SHAPE_SOURCE = 'import ImbalancedChen.P2OriginalCompactArchivedTotalCandidate\nimport Lean\nimport Lean.Meta.Sym.LitValues\n\nopen Lean Elab Command in\nrun_cmd do\n  let env ← getEnv\n  let moduleName := `ImbalancedChen.P2OriginalCompactArchivedTotalCandidate\n  let some owner := env.getModuleIdx? moduleName\n    | throwError "Missing Q80 diagnostic module"\n  let names := env.const2ModIdx.fold (init := (#[] : Array Name)) fun ns n i =>\n    if i == owner && (env.find? n).isSome then ns.push n else ns\n  let resolve := fun wanted => names.filter fun n => privateToUserName n == wanted\n  let some sourceOwner := env.getModuleIdx?\n      `ImbalancedChen.P2OriginalCompactQ80Encloser\n    | throwError "Missing canonical Q80 source module"\n  let some historicOwner := env.getModuleIdx?\n      `ImbalancedChen.P2HistoricSieveTableSemantics\n    | throwError "Missing canonical HistoricNode module"\n  let sourceOwnedNames := env.const2ModIdx.fold (init := (#[] : Array Name)) fun ns n i =>\n    if i == sourceOwner && (env.find? n).isSome then ns.push n else ns\n  let historicOwnedNames := env.const2ModIdx.fold (init := (#[] : Array Name)) fun ns n i =>\n    if i == historicOwner && (env.find? n).isSome then ns.push n else ns\n  let resolveSource := fun wanted =>\n    sourceOwnedNames.filter fun n => privateToUserName n == wanted\n  let resolveHistoric := fun wanted =>\n    historicOwnedNames.filter fun n => privateToUserName n == wanted\n  let sourceNames := resolveSource\n    `ImbalancedChen.P2OriginalCompactQ80EncloserSourceOnly.sourceState\n  let aliasNames := resolveSource\n    `ImbalancedChen.P2OriginalCompactQ80EncloserSourceOnly.Node\n  let nodeNames := resolveHistoric\n    `ImbalancedChen.P2HistoricSieveTableSemantics.HistoricNode\n  let ctorNames := resolveHistoric\n    `ImbalancedChen.P2HistoricSieveTableSemantics.HistoricNode.mk\n  let entryNames := resolve\n    `ImbalancedChen.P2OriginalCompactArchivedTotalCandidateSourceOnly.cached_fixed_plus_original_compact_eq_archived_candidate\n  unless sourceNames.size == 1 && aliasNames.size == 1 && nodeNames.size == 1 &&\n      ctorNames.size == 1 && entryNames.size == 1 do\n    throwError "Cannot uniquely resolve the exact Q80 source/Node/constructor/public entry"\n  let sourceName := sourceNames[0]!\n  let aliasName := aliasNames[0]!\n  let nodeName := nodeNames[0]!\n  let ctorName := ctorNames[0]!\n  let entryName := entryNames[0]!\n  let some aliasInfo := env.find? aliasName | throwError "Missing Node alias"\n  -- Read the alias body only. No defeq, whnf, or evaluation of a sourceState term.\n  let aliasIsDirect := match aliasInfo with\n    | .defnInfo value => value.value.consumeMData.isConstOf nodeName\n    | _ => false\n  unless aliasIsDirect do\n    throwError "Node is not the expected direct HistoricNode type alias"\n  let some entryInfo := env.find? entryName | throwError "Missing public entry"\n  let entryIsTheorem := match entryInfo with\n    | .thmInfo _ => true\n    | _ => false\n  let entryOK := !isPrivateName entryName && entryIsTheorem &&\n    !entryInfo.isUnsafe && !entryInfo.isPartial && !entryInfo.isAxiom\n  unless entryOK do\n    throwError "The diagnostic entry is not a public safe nonpartial theorem"\n  let blocks := (names.filter fun n =>\n    n.anyS (fun part => "_q80NodeProofBlock".isPrefixOf part)).qsort Name.lt\n\n  -- Only a Nat literal or its canonical OfNat Nat / instOfNatNat wrapper.\n  let asNat? : Expr → Option Nat := fun original =>\n    match original.consumeMData with\n    | .lit (.natVal n) => some n\n    | .app (.app (.app (.const ofNatName _) (.const natName []))\n        (.lit (.natVal n))) (.app (.const instName []) (.lit (.natVal m))) =>\n        if ofNatName == ``OfNat.ofNat && natName == ``Nat &&\n            instName == ``instOfNatNat && n == m then some n else none\n    | _ => none\n  -- Keep the original Sym literal forms, plus exact Int constructors on the\n  -- recognized Nat syntax. negSucc n denotes -(n+1), not -n.\n  let asInt? : Expr → Option Int := fun original =>\n    let e := original.consumeMData\n    match e with\n    | .app (.const ctor []) n =>\n        if ctor == ``Int.ofNat then (asNat? n).map Int.ofNat\n        else if ctor == ``Int.negSucc then (asNat? n).map Int.negSucc\n        else none\n    | _ => Lean.Meta.Sym.getIntValue? e\n\n  let mut allOK := blocks.size == 2048\n  let mut allIndices : Array Nat := #[]\n  let mut totalTypeNodes := 0\n  for name in blocks do\n    let some info := env.find? name | throwError "Missing generated Q80 block"\n    let isTheorem := match info with\n      | .thmInfo _ => true\n      | _ => false\n    let type := info.type.consumeMData\n    let mut facts : Array Expr := #[type]\n    let mut balanced := true\n    for _ in [:6] do\n      let mut next : Array Expr := #[]\n      for original in facts do\n        let term := original.consumeMData\n        if term.isAppOfArity ``And 2 then\n          let args := term.getAppArgs\n          next := next.push args[0]!\n          next := next.push args[1]!\n        else\n          balanced := false\n      facts := next\n    balanced := balanced && facts.size == 64\n    let mut blockOK := isPrivateName name && isTheorem &&\n      !info.isUnsafe && !info.isPartial && !info.isAxiom &&\n      !type.hasFVar && !type.hasMVar && balanced\n    let mut indices : Array Nat := #[]\n    let mut factRecords : Array Json := #[]\n    for originalFact in facts do\n      let fact := originalFact.consumeMData\n      let mut factOK := false\n      let mut index : Option Nat := none\n      let mut grid : Option Nat := none\n      let mut completed : Option Nat := none\n      let mut values : Array (Option Int) := #[]\n      if fact.isAppOfArity ``Eq 3 then\n        let equality := fact.getAppArgs\n        let carrier := equality[0]!.consumeMData\n        let lhs := equality[1]!.consumeMData\n        let rhs := equality[2]!.consumeMData\n        if (carrier.isConstOf aliasName || carrier.isConstOf nodeName) &&\n            lhs.isAppOfArity sourceName 3 && rhs.isAppOfArity ctorName 4 then\n          let sourceArgs := lhs.getAppArgs\n          grid := asNat? sourceArgs[0]!\n          completed := asNat? sourceArgs[1]!\n          index := asNat? sourceArgs[2]!\n          values := rhs.getAppArgs.map asInt?\n          factOK := grid == some 16384 && index.isSome &&\n            completed == index && values.all Option.isSome\n      if let some i := index then indices := indices.push i\n      blockOK := blockOK && factOK\n      -- Decimal strings preserve the exact Q80 integers in JSON consumers.\n      let decimalValues := values.map fun value => value.map toString\n      factRecords := factRecords.push <| Json.mkObj [\n        ("grid", toJson grid), ("completed", toJson completed), ("index", toJson index),\n        ("four_int_normal_form_decimal", toJson decimalValues),\n        ("exact_source_node_equality", toJson factOK)]\n    let first := (indices[0]?).getD 0\n    let expected := (List.range 64).toArray.map fun i => first + i\n    let aligned := decide (32769 ≤ first ∧ first ≤ 163777) &&\n      (first - 32769) % 64 == 0\n    blockOK := blockOK && aligned && indices == expected\n    allOK := allOK && blockOK\n    allIndices := allIndices ++ indices\n    let nodes := info.type.sizeWithoutSharing\n    totalTypeNodes := totalTypeNodes + nodes\n    let record := Json.mkObj [\n      ("name", toJson name.toString), ("private", toJson (isPrivateName name)),\n      ("theorem", toJson isTheorem), ("unsafe", toJson info.isUnsafe),\n      ("partial", toJson info.isPartial), ("axiom", toJson info.isAxiom),\n      ("balanced_and_depth", toJson (6 : Nat)),\n      ("sixty_four_fact_balanced_and", toJson balanced),\n      ("fact_count", toJson facts.size), ("indices", toJson indices), ("facts", toJson factRecords),\n      ("type_expr_nodes_without_sharing", toJson nodes),\n      ("shape_checks_passed", toJson blockOK)]\n    liftIO <| IO.println s!"P24_Q80_BLOCK {record.compress}"\n  allOK := allOK &&\n    allIndices.qsort (· < ·) == (List.range 131072).toArray.map (fun i => 32769 + i)\n  let summary := Json.mkObj [\n    ("module", toJson moduleName.toString), ("diagnostic_only", toJson true),\n    ("public_entry_name", toJson entryName.toString), ("public_entry_checks_passed", toJson entryOK),\n    ("node_alias_directly_equals_historic_node", toJson aliasIsDirect),\n    ("owned_block_count", toJson blocks.size), ("total_fact_count", toJson allIndices.size),\n    ("total_type_expr_nodes_without_sharing", toJson totalTypeNodes),\n    ("indices", toJson allIndices), ("shape_checks_passed", toJson allOK),\n    ("P2_acceptance_credit", toJson false)]\n  liftIO <| IO.println s!"P24_Q80_BLOCK_SUMMARY {summary.compress}"\n  unless allOK do\n    throwError "Q80 block shape diagnostics failed"\n'

# Canonical A shape inspection only. No proof regeneration, independent replay,
# original audit CLI, or canonical audit receipt is created by this wrapper.
from run_winner9_private_audit import parse_audit, require

MINIMUM_FREE_BYTES = 32 * 1024 * 1024
METADATA_ALLOWANCE = 2 * 1024 * 1024
CAPTURE_DRAIN_ALLOWANCE = 4 * 1024 * 1024
CHUNK_BYTES = 65536
out = root / ".lake/p24-canonical-A-block-shape/b55-attempt-001"
assert not out.exists() and not out.is_symlink(), "Preserve previous shape evidence"
assert out.resolve().is_relative_to(root.resolve())
capacity_directory = root / ".lake/p24-owned-capacity/b55-A-attempt-001"
capacity_receipt_path = capacity_directory / "capacity-diagnostic.json"
capacity_receipt_sha256 = "47734ae76baf0a59f4f381e491ff4fc2ed62669a2fd81131af24635bb94d20a9"
shape_source_sha256 = "b54a2c1ae01c1ebfbcb83bb63a9e09f7275ef818eb368e683d615deca1196734"
executed_original_shape_sha256 = "c190906df505fbe101f0aca84f46a7ba3252ad75b7ab6bb07ffa2ae3fb950d48"
shape_core_sha256 = "a8db2e02200ea9d21063fbb8e451feebedcb851be3ae53ff7f58c61a313061d3"

def available_bytes():
    stat = os.statvfs(root)
    return stat.f_bavail * stat.f_frsize


def need_free(extra=0):
    free = available_bytes()
    if free < MINIMUM_FREE_BYTES + extra:
        raise RuntimeError("32 MiB free reserve guard: available=" + str(free) + ", extra=" + str(extra))
    return free


def encoded_json(value):
    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


def write_derived(name, data):
    assert Path(name).name == name
    need_free(len(data) + 65536)
    destination = out / name
    assert not destination.exists(), "Diagnostic artifact already exists: " + name
    with destination.open("xb") as stream:
        stream.write(data)
        stream.flush()
        os.fsync(stream.fileno())
    return {"path": str(destination), "bytes": len(data), "sha256": digest(destination)}


def audit_directory_fingerprint():
    directory = root / ".lake/p2-private/audit" / A
    if not directory.exists():
        return {"exists": False, "files": {}}
    assert directory.is_dir() and not directory.is_symlink()
    result = {}
    for path in sorted(directory.rglob("*")):
        assert not path.is_symlink(), "Original target audit contains a symlink"
        if path.is_file():
            result[str(path.relative_to(directory))] = {"bytes": path.stat().st_size, "sha256": digest(path)}
    return {"exists": True, "files": result}


def stop_only_this_child(process):
    if process.poll() is not None:
        return
    process.terminate()
    try:
        process.wait(timeout=10)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait()


def capture_complete_stdout(command, environment, path):
    raw_hash = hashlib.sha256()
    raw_bytes = 0
    capture_errors = []
    stopped_for_reserve = False
    finished_stream = False
    process = None
    started = time.monotonic()
    # A bounded drain allowance remains in addition to the 32 MiB floor, so a
    # stopped diagnostic child can be drained and this gzip can be finalized.
    need_free(METADATA_ALLOWANCE + CAPTURE_DRAIN_ALLOWANCE)
    with path.open("xb") as physical:
        with gzip.GzipFile(filename="", mode="wb", compresslevel=9, fileobj=physical, mtime=0) as compressed:
            try:
                process = subprocess.Popen(command, cwd=root, env=environment, stdout=subprocess.PIPE,
                                           stderr=subprocess.STDOUT, bufsize=0)
                selector = selectors.DefaultSelector()
                selector.register(process.stdout, selectors.EVENT_READ)
                last_report = time.monotonic()
                try:
                    while selector.get_map():
                        for key, _ in selector.select(timeout=5):
                            chunk = os.read(key.fileobj.fileno(), CHUNK_BYTES)
                            if not chunk:
                                selector.unregister(key.fileobj)
                                finished_stream = True
                                continue
                            if not stopped_for_reserve:
                                try:
                                    need_free(METADATA_ALLOWANCE + CAPTURE_DRAIN_ALLOWANCE + 2 * CHUNK_BYTES)
                                except RuntimeError as error:
                                    stopped_for_reserve = True
                                    capture_errors.append(str(error))
                                    stop_only_this_child(process)
                            compressed.write(chunk)
                            raw_hash.update(chunk)
                            raw_bytes += len(chunk)
                        if time.monotonic() - last_report >= 30:
                            print(json.dumps({"phase": "canonical_A_shape_capture_progress", "raw_stdout_bytes": raw_bytes,
                                              "gzip_bytes_so_far": physical.tell(),
                                              "free_bytes": available_bytes(), "diagnostic_only": True}, sort_keys=True), flush=True)
                            last_report = time.monotonic()
                    returncode = process.wait()
                finally:
                    selector.close()
                    if process.stdout is not None:
                        process.stdout.close()
            except Exception as error:
                capture_errors.append(type(error).__name__ + ": " + str(error))
                if process is not None:
                    stop_only_this_child(process)
                returncode = process.returncode if process is not None else None
            finally:
                if process is not None and process.poll() is None:
                    stop_only_this_child(process)
        physical.flush()
        os.fsync(physical.fileno())
    result = {"command": command, "lean_exit_code": returncode,
              "seconds": round(time.monotonic() - started, 6),
              "stdout_and_stderr_combined": True,
              "stdout_bytes": raw_bytes, "stdout_sha256": raw_hash.hexdigest(),
              "gzip_path": str(path), "gzip_bytes": path.stat().st_size, "gzip_sha256": digest(path),
              "gzip_compresslevel": 9, "gzip_mtime": 0,
              "read_to_eof": finished_stream, "stopped_for_reserve": stopped_for_reserve,
              "errors": capture_errors}
    result["complete_successful_template_stdout"] = (
        returncode == 0 and finished_stream and not stopped_for_reserve and not capture_errors)
    return result


def fingerprint_gzip_payload(path):
    result = hashlib.sha256()
    count = 0
    with gzip.open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(chunk)
            count += len(chunk)
    return {"bytes": count, "sha256": result.hexdigest()}


class CompleteGzipAuditText:
    """Only supply the read_text API used by the unchanged original parser."""

    def __init__(self, path):
        self.path = path

    def read_text(self):
        # Path.read_text() and this wrapper both use the standard TextIOWrapper
        # defaults, including locale encoding and universal-newline handling.
        with gzip.open(self.path, "rb") as binary:
            with io.TextIOWrapper(binary) as text:
                return text.read()



def bound_capacity_input(binding, basename):
    path = Path(binding["path"])
    assert path == capacity_directory / basename
    assert path.is_file() and not path.is_symlink()
    assert path.resolve().is_relative_to(capacity_directory.resolve())
    assert path.stat().st_size == binding["bytes"] and digest(path) == binding["sha256"]
    return path


registry_before = {"bytes": registry.stat().st_size, "sha256": digest(registry)}
records = json.loads(registry.read_text())
full_before = snapshot(root, lib, full_nodes, toolchain, external)
assert full_before["external_snapshot"] == native_before
verify_compilation(records, prereq_nodes, full_before)
verify_compilation(records, a_nodes, full_before)
assert digest(registry) == registry_before["sha256"]
original_audit_before = audit_directory_fingerprint()
assert digest(capacity_receipt_path) == capacity_receipt_sha256
measured = json.loads(capacity_receipt_path.read_text())
assert measured["diagnostic_passed"] is True and measured["wrapper_exit_code"] == 0
assert measured["source_pin"] == pin and measured["target"] == A
assert measured["target_project_scope"] == 102 and measured["full_source_scope"] == 324
assert measured["ordered_fingerprint"] == ordered_expected
assert measured["pinned_file_sha256"] == expected and measured["runtime_sha256"] == runtime_expected
assert measured["native_binding"] == native_before
assert measured["postchecks"] and all(value is True for value in measured["postchecks"].values())
assert not measured["errors"] and measured["registry_before"] == measured["registry_after"]
assert measured["original_runner_main_called"] is False
assert measured["independent_replay_performed"] is False and measured["canonical_audit_credit"] is False
capacity_full_path = bound_capacity_input(measured["full324_before"], "full324-before-snapshot.json")
capacity_full = json.loads(capacity_full_path.read_text())
assert {name: capacity_full["project"][name] for name in a_nodes} == \
    {name: full_before["project"][name] for name in a_nodes}
for key in ("toolchain", "lean_binary_sha256", "leanchecker_sha256", "template_sha256", "driver_sha256", "external_snapshot"):
    assert capacity_full[key] == full_before[key]
capacity_capture = measured["capture"]
assert capacity_capture["complete_successful_template_stdout"] is True
assert capacity_capture["lean_exit_code"] == 0 and capacity_capture["read_to_eof"] is True
assert capacity_capture["stopped_for_reserve"] is False and not capacity_capture["errors"]
capacity_gzip = bound_capacity_input({"path": capacity_capture["gzip_path"],
    "bytes": capacity_capture["gzip_bytes"], "sha256": capacity_capture["gzip_sha256"]}, "audit.stdout.log.gz")
assert capacity_capture["gzip_bytes"] == 10708984
assert capacity_capture["gzip_sha256"] == "92489930738bdb59e07ff98dfb795960c324949fd54550c01c7e739382faa780"
assert fingerprint_gzip_payload(capacity_gzip) == {
    "bytes": capacity_capture["stdout_bytes"], "sha256": capacity_capture["stdout_sha256"]}

assert hashlib.sha256(SHAPE_SOURCE.encode()).hexdigest() == shape_source_sha256
shape_core = SHAPE_SOURCE[SHAPE_SOURCE.index("  unless sourceNames.size == 1"):]
assert len(shape_core.encode()) == 6652
assert hashlib.sha256(shape_core.encode()).hexdigest() == shape_core_sha256
free_before = need_free(12 * 1024 * 1024 + METADATA_ALLOWANCE + CAPTURE_DRAIN_ALLOWANCE)
out.mkdir(parents=True, exist_ok=False)
source_binding = write_derived("InspectBlocks.lean", SHAPE_SOURCE.encode())
before_binding = write_derived("full324-before-snapshot.json", encoded_json(full_before))
audit_binding = write_derived("original-A-audit-directory-before.json", encoded_json(original_audit_before))
environment = dict(os.environ)
environment["LEAN_PATH"] = str(lib) + ":" + environment.get("LEAN_PATH", "")
environment = external.environment(environment)
command = [LEAN, "-t0", "-j1", "-M11264", "-DwarningAsError=true",
    "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000", str((out / "InspectBlocks.lean").relative_to(root))]
initial = {
    "schema": 1, "purpose": "Canonical A exact block-shape inspection, separately from original replay/full-owned audit",
    "source_pin": pin, "target": A, "target_project_scope": 102, "prerequisite_symbolic_scope": 321,
    "full_source_scope": 324, "ordered_fingerprint": ordered_expected,
    "pinned_file_sha256": expected, "runtime_sha256": runtime_expected, "native_binding": native_before,
    "registry_before": registry_before, "full324_before": before_binding,
    "original_A_audit_before": audit_binding, "inspector_source": source_binding,
    "executed_original_inspector_sha256": executed_original_shape_sha256,
    "unchanged_executed_core_bytes": 6652, "unchanged_executed_core_sha256": shape_core_sha256,
    "capacity_receipt": {"path": str(capacity_receipt_path), "bytes": capacity_receipt_path.stat().st_size,
        "sha256": capacity_receipt_sha256},
    "capacity_full_owned_link_is_diagnostic_only": True,
    "command": command, "lean_path": environment.get("LEAN_PATH", ""),
    "minimum_free_reserve_bytes": MINIMUM_FREE_BYTES, "free_bytes_before": free_before,
    "outer_timeout_seconds": 3600, "job_memory_mb": 13107, "cpu_threads": 1,
    "lean_memory_mb": 11264, "lean_threads": 1,
    "original_runner_main_called": False, "independent_replay_performed": False,
    "proof_generator_run": False, "canonical_audit_credit": False, "full324_credit": False,
    "original_audit_files_deleted": False,
}
write_derived("shape-input.json", encoded_json(initial))
print("P24_CANONICAL_A_SHAPE_BEGIN " + json.dumps(initial, sort_keys=True), flush=True)

capture = None
shape_summary = None
shape_join = None
shape_summary_binding = None
shape_join_binding = None
shape_checks_passed = False
full_after = None
errors = []
postchecks = {}
gzip_path = out / "blocks.stdout.log.gz"
try:
    capture = capture_complete_stdout(command, environment, gzip_path)
    assert fingerprint_gzip_payload(gzip_path) == {
        "bytes": capture["stdout_bytes"], "sha256": capture["stdout_sha256"]}
    capture["gzip_roundtrip_verified"] = True
    assert capture["complete_successful_template_stdout"] is True, "Shape child failed or output was incomplete"
    with gzip.open(gzip_path, "rt") as stream:
        inspect_raw = stream.read()
    records_with_prefix = lambda text, prefix: [json.loads(line[len(prefix):])
        for line in text.splitlines() if line.startswith(prefix)]
    target = A
    blocks = records_with_prefix(inspect_raw, "P24_Q80_BLOCK ")
    summaries = records_with_prefix(inspect_raw, "P24_Q80_BLOCK_SUMMARY ")
    require(len(summaries) == 1 and summaries[0].get("module") == target, "Missing block summary")
    require(len(blocks) == 2048 and summaries[0].get("owned_block_count") == 2048 and
            summaries[0].get("shape_checks_passed") is True, "Incorrect block inventory/shape")
    require(summaries[0].get("public_entry_checks_passed") is True and
            summaries[0].get("node_alias_directly_equals_historic_node") is True and
            summaries[0].get("total_fact_count") == 131072,
            "Incorrect public entry/carrier/total fact count")
    require(sorted(summaries[0].get("indices", [])) == list(range(32769, 163841)),
            "Q80 block indices do not cover the exact original first-131072 prefix")
    require(all(block.get("shape_checks_passed") is True and
                block.get("balanced_and_depth") == 6 and block.get("fact_count") == 64
                for block in blocks), "Q80 block depth/fact count differs")
    # Preserve the executed P3 cross-check against complete original-template
    # owned records. Here those records are the already-bound capacity diagnostic;
    # this link does not create a canonical audit/replay receipt.
    parsed = parse_audit(CompleteGzipAuditText(capacity_gzip), A, set(a_nodes))
    assert parsed["declaration_count"] == measured["original_format_sizes"]["declaration_count"]
    assert parsed["axiom_counts"] == measured["original_format_sizes"]["axiom_counts"]
    declarations = parsed["declarations"]
    by_name = {row["name"]:row for row in declarations}
    for block in blocks:
        require(block["name"] in by_name, "Inspected block is absent from original owned audit")
        block["printed_type_utf8_bytes"] = len(by_name[block["name"]]["type"].encode())
        block["axioms"] = by_name[block["name"]]["axioms"]
    shape_summary = summaries[0]
    # The full per-node normal forms and full global index list remain in the
    # lossless stdout gzip. Avoid a second 32+ MB plaintext JSON copy of them.
    shape_join = [{"name": block["name"], "printed_type_utf8_bytes": block["printed_type_utf8_bytes"],
        "axioms": block["axioms"]} for block in blocks]
    summary_raw = encoded_json(shape_summary)
    summary_gzip = gzip.compress(summary_raw, compresslevel=9, mtime=0)
    assert gzip.decompress(summary_gzip) == summary_raw
    shape_summary_binding = write_derived("complete-block-summary.json.gz", summary_gzip)
    join_raw = encoded_json(shape_join)
    join_gzip = gzip.compress(join_raw, compresslevel=9, mtime=0)
    assert gzip.decompress(join_gzip) == join_raw
    shape_join_binding = write_derived("complete-block-owned-link.json.gz", join_gzip)
    shape_checks_passed = True
    del parsed, declarations, by_name, blocks, inspect_raw, summary_raw, join_raw
except Exception as error:
    errors.append({"stage": "shape_capture_parse_or_exact_owned_link", "error": type(error).__name__ + ": " + str(error)})


def postcheck(name, action):
    try:
        action()
        postchecks[name] = True
    except Exception as error:
        postchecks[name] = False
        errors.append({"check": name, "error": type(error).__name__ + ": " + str(error)})


def check_runtime_after():
    assert {name: digest(name) for name in runtime_expected} == runtime_expected
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=MATHLIB, text=True).strip() == PIN
    assert digest(snapshot_path) == snapshot_expected


def check_all_inputs_after():
    global full_after
    current_nodes = project_nodes(root, W)
    assert list(current_nodes) == full
    mark_project_nodes(current_nodes, set(external.modules))
    full_after = snapshot(root, lib, current_nodes, toolchain, external)
    assert full_after == full_before
    assert {"bytes": registry.stat().st_size, "sha256": digest(registry)} == registry_before
    current_records = json.loads(registry.read_text())
    verify_compilation(current_records, prereq_nodes, full_after)
    verify_compilation(current_records, a_nodes, full_after)


def check_original_audits_after():
    assert audit_directory_fingerprint() == original_audit_before


def check_derived_inputs_after():
    assert digest(out / "InspectBlocks.lean") == shape_source_sha256
    assert digest(capacity_receipt_path) == capacity_receipt_sha256
    assert digest(capacity_gzip) == capacity_capture["gzip_sha256"]
    if capture is not None:
        assert digest(gzip_path) == capture["gzip_sha256"]


postcheck("pinned_sources_and_original_tools", check_source)
postcheck("runtime_and_original_native_snapshot_bytes", check_runtime_after)
postcheck("full324_inputs_registry_native_and_321_plus_A102_bindings", check_all_inputs_after)
postcheck("original_canonical_A_audit_files_unchanged", check_original_audits_after)
postcheck("inspector_capacity_reference_and_complete_stdout_unchanged", check_derived_inputs_after)
postcheck("minimum_32MiB_free_reserve", need_free)
if full_after is not None:
    write_derived("full324-after-snapshot.json", encoded_json(full_after))
success = shape_checks_passed and not errors and all(postchecks.values())
exit_code = 0 if success else 125
if capture is not None and isinstance(capture.get("lean_exit_code"), int) and capture["lean_exit_code"] != 0:
    exit_code = capture["lean_exit_code"] if capture["lean_exit_code"] > 0 else 1
result = dict(initial, canonical_A_shape_checks_passed=success,
    shape_capture=capture, complete_block_summary=shape_summary_binding,
    complete_block_owned_link=shape_join_binding,
    total_block_printed_type_utf8_bytes=None if shape_join is None else sum(row["printed_type_utf8_bytes"] for row in shape_join),
    block_count=2048 if shape_checks_passed else None, fact_count=131072 if shape_checks_passed else None,
    postchecks=postchecks, errors=errors, wrapper_exit_code=exit_code,
    registry_after={"bytes": registry.stat().st_size, "sha256": digest(registry)},
    free_bytes_after=available_bytes(), canonical_audit_credit=False,
    independent_replay_performed=False, original_runner_main_called=False, full324_credit=False)
result_binding = write_derived("shape-diagnostic.json", encoded_json(result))
directory_fd = os.open(out, os.O_RDONLY | os.O_DIRECTORY)
try:
    os.fsync(directory_fd)
finally:
    os.close(directory_fd)
print("P24_CANONICAL_A_SHAPE_DONE " + json.dumps({
    "result": result_binding, "canonical_A_shape_checks_passed": success, "exit_code": exit_code,
    "gzip": None if capture is None else {key: capture[key] for key in ("gzip_path", "gzip_bytes", "gzip_sha256")},
    "block_count": result["block_count"], "fact_count": result["fact_count"],
    "canonical_audit_credit": False, "independent_replay_performed": False,
    "full324_credit": False, "errors": errors}, sort_keys=True), flush=True)
raise SystemExit(exit_code)
