set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
mkdir -p /workspace/p24-datacore-owned-diagnostic-20261126
mkdir /workspace/p24-datacore-owned-diagnostic-20261126/attempt-001
cat > /workspace/p24-datacore-owned-diagnostic-20261126/attempt-001/driver.py <<'P24_DATACORE_DRIVER'
import hashlib, json, os, pathlib, signal, subprocess, sys, time
root = pathlib.Path("/workspace/p24-datacore-owned-diagnostic-20261126/attempt-001")
payload = json.loads(r'''{"source":"import Std\n\n/-!\nSOURCEONLY / UNCOMPILED. Data carrier only; no analytic imports or checks.\nProposed module: ImbalancedChen.Certificates.OriginalNodeArraysV1.DataCore\nThe untrusted emitter places 4096 consecutive rows in each depth12 tree.\nLookup follows one branch at each depth; it never traverses a global list.\nThe prefix is represented by its constant original initializer. The emitter\nmust reject input prefix bytes differing from that initializer; this is an\nexternal byte correspondence check, not a formal SHA/decoder theorem.\n-/\n\nnamespace ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly\n\nstructure RawNode where\n  Llo : Int\n  Lhi : Int\n  Hlo : Int\n  Hhi : Int\n  deriving DecidableEq\n\ninductive NodeTree : Nat → Type where\n  | leaf : RawNode → NodeTree 0\n  | fork {depth : Nat} : NodeTree depth → NodeTree depth → NodeTree (depth+1)\n\n/-- High-bit-first, contiguous halves. Legal block offsets are0..4095.\nThe outer reader guards that domain; an unrestricted read outside a leaf's\ndomain has no array-correspondence meaning and certifies no such index. -/\nnoncomputable def NodeTree.read : {depth : Nat} → NodeTree depth → Nat → RawNode :=\n  fun {_depth} tree =>\n    NodeTree.rec (motive := fun _ _ => Nat → RawNode)\n      (fun value _ => value)\n      (fun {depth} _left _right readLeft readRight i =>\n        if i < 2^depth then readLeft i else readRight (i-2^depth))\n      tree\n\nabbrev Block := NodeTree 12\n\ndef rawInitial : RawNode := ⟨0,0,(2 : Int)^112,(2 : Int)^112⟩\n\n/-- A single immutable block function supplies all40 update blocks.\nOnly0..196608 has the specified stored-array meaning. -/\nnoncomputable def assembledRawRead (blocks : Nat → Block) (i : Nat) : RawNode :=\n  if i ≤ 32768 then rawInitial else\n  if i ≤ 196608 then\n    (blocks ((i-32769)/4096)).read ((i-32769)%4096)\n  else rawInitial\n\nend ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly\n","candidate":"import Std\nimport Lean.Elab.Command\n\n/-!\nSOURCEONLY / UNCOMPILED. Data carrier only; no analytic imports or checks.\nProposed module: ImbalancedChen.Certificates.OriginalNodeArraysV1.DataCore\nThe untrusted emitter places 4096 consecutive rows in each depth12 tree.\nLookup follows one branch at each depth; it never traverses a global list.\nThe prefix is represented by its constant original initializer. The emitter\nmust reject input prefix bytes differing from that initializer; this is an\nexternal byte correspondence check, not a formal SHA/decoder theorem.\n-/\n\nnamespace ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly\n\nstructure RawNode where\n  Llo : Int\n  Lhi : Int\n  Hlo : Int\n  Hhi : Int\n  deriving DecidableEq\n\ninductive NodeTree : Nat → Type where\n  | leaf : RawNode → NodeTree 0\n  | fork {depth : Nat} : NodeTree depth → NodeTree depth → NodeTree (depth+1)\n\n/-- High-bit-first, contiguous halves. Legal block offsets are0..4095.\nThe outer reader guards that domain; an unrestricted read outside a leaf's\ndomain has no array-correspondence meaning and certifies no such index. -/\nnoncomputable def NodeTree.read : {depth : Nat} → NodeTree depth → Nat → RawNode :=\n  fun {_depth} tree =>\n    NodeTree.rec (motive := fun _ _ => Nat → RawNode)\n      (fun value _ => value)\n      (fun {depth} _left _right readLeft readRight i =>\n        if i < 2^depth then readLeft i else readRight (i-2^depth))\n      tree\n\nabbrev Block := NodeTree 12\n\ndef rawInitial : RawNode := ⟨0,0,(2 : Int)^112,(2 : Int)^112⟩\n\n/-- A single immutable block function supplies all40 update blocks.\nOnly0..196608 has the specified stored-array meaning. -/\nnoncomputable def assembledRawRead (blocks : Nat → Block) (i : Nat) : RawNode :=\n  if i ≤ 32768 then rawInitial else\n  if i ≤ 196608 then\n    (blocks ((i-32769)/4096)).read ((i-32769)%4096)\n  else rawInitial\n\nend ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly\n","template":"import ImbalancedChen.P2Winner9FiniteMomentKernel\nimport Lean.Util.CollectAxioms\nset_option pp.all true\nset_option pp.proofs true\nset_option pp.deepTerms true\nset_option pp.universes true\nset_option pp.explicit true\nset_option pp.fullNames true\nset_option pp.privateNames true\nset_option pp.maxSteps 1000000\nopen Lean Elab Command in\nrun_cmd do\n  let env ← getEnv\n  liftIO <| IO.println s!\"P0_QUEUE_IMPORTS {(toJson (env.header.moduleNames.map Name.toString)).compress}\"\n  let moduleName := `ImbalancedChen.P2Winner9FiniteMomentKernel\n  let some idx := env.getModuleIdx? moduleName | throwError \"Missing target module\"\n  let names := env.const2ModIdx.fold (init := (#[] : Array Name)) fun ns n i =>\n    if i == idx && (env.find? n).isSome then ns.push n else ns\n  let mut serialized : Array Name := #[]\n  let mut found := false\n  for i in List.range env.header.modules.size do\n    let imported := env.header.modules[i]!\n    if imported.module == moduleName then\n      if found then throwError \"Duplicate module\"\n      found := true\n      let data := env.header.moduleData[i]!\n      if data.isModule || !imported.importAll || !imported.hasData then\n        throwError \"Incomplete imported legacy data\"\n      serialized := data.constNames\n  unless found && names.size > 0 && names.qsort Name.lt == serialized.qsort Name.lt do\n    throwError \"Complete serialized/environment inventory mismatch\"\n  liftIO <| IO.println s!\"P0_QUEUE_INVENTORY {(Json.mkObj [(\"module\", toJson moduleName.toString), (\"serialized\", toJson (serialized.map Name.toString)), (\"environment\", toJson (names.map Name.toString))]).compress}\"\n  for name in names.qsort Name.lt do\n    let some info := env.find? name | throwError \"Missing inventoried declaration\"\n    if info.isUnsafe || info.isPartial || info.isAxiom then throwError \"Unsafe/partial/axiom target\"\n    let axioms ← collectAxioms name\n    for ax in axioms do\n      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do\n        throwError \"Forbidden transitive axiom {ax}\"\n    let type ← liftTermElabM do return (← Meta.ppExpr info.type).pretty\n    if type.contains '⋯' then throwError \"Truncated type\"\n    let record := Json.mkObj [(\"name\", toJson name.toString), (\"module\", toJson moduleName.toString),\n      (\"unsafe\", toJson info.isUnsafe), (\"partial\", toJson info.isPartial), (\"axiom\", toJson info.isAxiom),\n      (\"type\", toJson type), (\"axioms\", toJson (axioms.map Name.toString))]\n    liftIO <| IO.println s!\"P0_QUEUE_DECL {record.compress}\"\n\n","flags_source":"import ImbalancedChen.Certificates.OriginalNodeArraysV1.DataCore\nimport Lean.Util.CollectAxioms\nimport Lean.Elab.Command\nopen Lean Elab Command in\nrun_cmd do\n  let env ← getEnv\n  let moduleName := `ImbalancedChen.Certificates.OriginalNodeArraysV1.DataCore\n  let some idx := env.getModuleIdx? moduleName | throwError \"Missing target module\"\n  let names := env.const2ModIdx.fold (init := (#[] : Array Name)) fun ns n i =>\n    if i == idx && (env.find? n).isSome then ns.push n else ns\n  let mut serialized : Array Name := #[]\n  let mut matches : Nat := 0\n  let mut dataComplete := true\n  for i in List.range env.header.modules.size do\n    let imported := env.header.modules[i]!\n    if imported.module == moduleName then\n      matches := matches + 1\n      let data := env.header.moduleData[i]!\n      dataComplete := dataComplete && !data.isModule && imported.importAll && imported.hasData\n      serialized := serialized ++ data.constNames\n  let inventoryMatches := matches == 1 && dataComplete && names.size > 0 &&\n    names.qsort Name.lt == serialized.qsort Name.lt\n  liftIO <| IO.println s!\"DATACORE_FLAGS_INVENTORY {(Json.mkObj [(\"module\", toJson moduleName.toString), (\"matches\", toJson matches), (\"data_complete\", toJson dataComplete), (\"inventory_matches\", toJson inventoryMatches), (\"serialized\", toJson (serialized.map Name.toString)), (\"environment\", toJson (names.map Name.toString))]).compress}\"\n  let mut bad : Array Name := #[]\n  for name in names.qsort Name.lt do\n    let some info := env.find? name | throwError \"Missing inventoried declaration\"\n    let axioms ← collectAxioms name\n    let forbidden := axioms.filter fun ax => !#[`propext, `Classical.choice, `Quot.sound].contains ax\n    if info.isUnsafe || info.isPartial || info.isAxiom || !forbidden.isEmpty then\n      bad := bad.push name\n    let record := Json.mkObj [(\"name\", toJson name.toString), (\"unsafe\", toJson info.isUnsafe),\n      (\"partial\", toJson info.isPartial), (\"axiom\", toJson info.isAxiom),\n      (\"axioms\", toJson (axioms.map Name.toString)), (\"forbidden_axioms\", toJson (forbidden.map Name.toString))]\n    liftIO <| IO.println s!\"DATACORE_FLAGS_DECL {record.compress}\"\n  liftIO <| IO.println s!\"DATACORE_FLAGS_DONE {(Json.mkObj [(\"owned_count\", toJson names.size), (\"inventory_matches\", toJson inventoryMatches), (\"bad\", toJson (bad.map Name.toString))]).compress}\"\n"}''')
target = "ImbalancedChen.Certificates.OriginalNodeArraysV1.DataCore"
old_target = "ImbalancedChen.P2Winner9FiniteMomentKernel"
pin = "6e616f4e0372555f7a78bcdba3e198d0e277eec8"
def sha(data):
    return hashlib.sha256(data).hexdigest()
def file_info(path):
    data = pathlib.Path(path).read_bytes()
    return {"path": str(path), "bytes": len(data), "sha256": sha(data)}
source = payload["source"].encode("utf-8")
candidate = payload["candidate"].encode("utf-8")
template = payload["template"].encode("utf-8")
assert hashlib.sha1(b"blob " + str(len(source)).encode() + b"\0" + source).hexdigest() == "3c8cb466e40a188e4f48f960fc31885689998828"
assert sha(template) == "2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b"
assert source.startswith(b"import Std\n\n")
assert candidate == source.replace(b"import Std\n\n", b"import Std\nimport Lean.Elab.Command\n\n", 1)
assert candidate.replace(b"import Std\nimport Lean.Elab.Command\n\n", b"import Std\n\n", 1) == source
assert template.count(old_target.encode()) == 2
audit = template.replace(old_target.encode(), target.encode())
relative_source = pathlib.Path("ImbalancedChen/Certificates/OriginalNodeArraysV1/DataCore.lean")
source_path = root / relative_source
source_path.parent.mkdir(parents=True, exist_ok=True)
source_path.write_bytes(candidate)
(root / "DataCore-original.lean").write_bytes(source)
(root / "OriginalAuditTemplate.lean").write_bytes(template)
(root / "Audit.lean").write_bytes(audit)
lib = root / "lib"
obj = lib / relative_source.with_suffix(".olean")
obj.parent.mkdir(parents=True, exist_ok=True)
lean = "/toolchains/bin/lean"
checker = "/toolchains/bin/leanchecker"
version = subprocess.check_output([lean, "--version"], text=True).strip()
assert "4.33.0-rc1" in version and "62eed1db4d67327ec8120be05f1a1b0847d74561" in version
sysroot = subprocess.check_output([lean, "--print-prefix"], text=True).strip()
env = dict(os.environ)
env["LEAN_SYSROOT"] = sysroot
env["LEAN_PATH"] = str(lib) + ":" + str(pathlib.Path(sysroot) / "lib/lean")
env.pop("LEAN_SRC_PATH", None)
flags = ["-t0", "-j1", "-M11264", "-DwarningAsError=true", "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000"]
before = {
    "source": file_info(source_path),
    "original_source": file_info(root / "DataCore-original.lean"),
    "template": file_info(root / "OriginalAuditTemplate.lean"),
    "audit": file_info(root / "Audit.lean"),
    "lean": file_info(lean),
    "checker": file_info(checker),
}
manifest = {
    "purpose": "isolated DataCore original-owned audit import compatibility candidate",
    "production_pin": pin,
    "target": target,
    "source_git_blob": "3c8cb466e40a188e4f48f960fc31885689998828",
    "candidate_change": "insert exactly import Lean.Elab.Command after import Std",
    "source_inverse_bytes_equal": True,
    "template_target_replacements": 2,
    "template_other_bytes_equal": audit.replace(target.encode(), old_target.encode()) == template,
    "canonical_credit": False, "p2_credit": False, "production_changed": False,
    "version": version, "sysroot": sysroot, "lean_path": env["LEAN_PATH"],
    "before": before, "stages": [],
}
(root / "input-manifest.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n")
deadline = time.monotonic() + 840
def run_stage(name, command):
    log_path = root / (name + ".log")
    left = deadline - time.monotonic()
    if left <= 0:
        raise RuntimeError("Diagnostic soft deadline reached before stage")
    started = time.monotonic()
    timed_out = False
    with log_path.open("wb") as log:
        proc = subprocess.Popen(command, cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            rc = proc.wait(timeout=left)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
            rc = 124
    entry = {"stage": name, "command": command, "exit_code": rc, "timed_out": timed_out,
             "elapsed_seconds": time.monotonic() - started, "log": file_info(log_path)}
    manifest["stages"].append(entry)
    (root / "receipt.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n")
    print("DATACORE_STAGE " + json.dumps(entry, ensure_ascii=False), flush=True)
    return rc

compile_rc = run_stage("compile", [lean] + flags + ["-o", str(obj), str(relative_source)])
rc = compile_rc
if compile_rc == 0:
    manifest["object_before_replay"] = file_info(obj)
    replay_rc = run_stage("replay", [checker, "--verbose", target])
    audit_rc = run_stage("audit", [lean] + flags + ["Audit.lean"])
    rc = replay_rc if replay_rc != 0 else audit_rc
    if audit_rc != 0:
        (root / "FlagsOnly.lean").write_text(payload["flags_source"], encoding="utf-8")
        flags_rc = run_stage("flags-only", [lean] + flags + ["FlagsOnly.lean"])
        manifest["flags_only_is_supplemental_diagnostic"] = True
        manifest["flags_only_exit_code"] = flags_rc
    else:
        inventory = []
        declarations = []
        for line in (root / "audit.log").read_text(encoding="utf-8").splitlines():
            if line.startswith("P0_QUEUE_INVENTORY "):
                inventory.append(json.loads(line[len("P0_QUEUE_INVENTORY "):]))
            if line.startswith("P0_QUEUE_DECL "):
                declarations.append(json.loads(line[len("P0_QUEUE_DECL "):]))
        assert len(inventory) == 1, "Expected exactly one original inventory output"
        names = sorted(d["name"] for d in declarations)
        assert sorted(inventory[0]["serialized"]) == sorted(inventory[0]["environment"]) == names
        assert len(names) == len(set(names)) and names
        bad = [d["name"] for d in declarations if d["unsafe"] or d["partial"] or d["axiom"] or set(d["axioms"]) - {"propext", "Classical.choice", "Quot.sound"}]
        assert not bad
        manifest["original_audit_summary"] = {
            "owned_count": len(names), "exact_serialized_environment_decl_inventory": True,
            "all_safe_nonpartial_nonaxiom": True, "allowed_axioms_only": True,
            "declaration_names": names
        }
    manifest["object_after_audit"] = file_info(obj)
    manifest["object_unchanged"] = manifest["object_before_replay"] == manifest["object_after_audit"]
after = {
    "source": file_info(source_path),
    "original_source": file_info(root / "DataCore-original.lean"),
    "template": file_info(root / "OriginalAuditTemplate.lean"),
    "audit": file_info(root / "Audit.lean"),
    "lean": file_info(lean),
    "checker": file_info(checker),
}
manifest["after"] = after
manifest["inputs_and_tools_unchanged"] = before == after
manifest["exit_code"] = rc
manifest["all_three_original_stages_passed"] = len(manifest["stages"]) >= 3 and all(x["exit_code"] == 0 for x in manifest["stages"][:3])
if not manifest["inputs_and_tools_unchanged"] or (compile_rc == 0 and not manifest["object_unchanged"]):
    manifest["exit_code"] = rc if rc != 0 else 125
receipt = root / "receipt.json"
receipt.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n")
print("DATACORE_RECEIPT " + json.dumps({"receipt": file_info(receipt), "manifest": manifest}, ensure_ascii=False), flush=True)
for stage in manifest["stages"]:
    name = stage["stage"]
    data = (root / (name + ".log")).read_bytes()
    if len(data) <= 1200000:
        print("DATACORE_FULL_LOG_BEGIN " + name, flush=True)
        sys.stdout.buffer.write(data)
        sys.stdout.buffer.flush()
        print("\nDATACORE_FULL_LOG_END " + name, flush=True)
    else:
        print("DATACORE_FULL_LOG_RETAINED " + json.dumps(stage["log"]), flush=True)
raise SystemExit(manifest["exit_code"])

P24_DATACORE_DRIVER
python3 -B /workspace/p24-datacore-owned-diagnostic-20261126/attempt-001/driver.py
