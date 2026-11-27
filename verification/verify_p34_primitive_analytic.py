"""Verify the three existing primitive Eisenstein analytic supplier modules."""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import zipfile

sys.dont_write_bytecode = True
import verify_p34_classical_support as shared
from run_p34_primitive_analytic_cloud import (CHECKPOINT, DOCS, PROJECT_SOURCES, REQUIRED,
                                             checkpoint_archive)


ROOT = shared.ROOT
BASE = "3193c2dfda0f05c334b918da3a4724907660311f"
TARGETS = tuple(path[:-5].replace("/", ".") for path in PROJECT_SOURCES)
NAMESPACES = (
    "ImbalancedChen.Part3.RealEisensteinSeedConvergence",
    "ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic",
    "ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic",
)
ENDPOINT_NAMES = tuple(namespace + "." + name for namespace, names in zip(NAMESPACES, (
    ("seed_summable", "primitiveSeed_summable", "seed_tendstoLocallyUniformly"),
    ("primitiveComplexEisenstein_hasDerivAt", "primitiveComplexEisenstein_analyticOnNhd"),
    ("actualPrimitiveFourier_hasDerivAt", "actualPrimitiveFourier_analyticOnNhd"),
)) for name in names)
AUDIT = Path("verification/P34PrimitiveAnalyticAudit.lean")
ENDPOINTS = Path("verification/P34PrimitiveAnalyticEndpoints.lean")
CLOSURE = Path(DOCS) / "PROJECT_SOURCE_CLOSURE.json"
INTAKE = Path(DOCS) / "SOURCE_INTAKE.json"
STRICT_FLAGS = ["-t0", "-j1", "-M12000", "-DwarningAsError=true"]


def classify_declarations(records, modules):
    """Link explicit source declarations to their unique compiler owner and kind."""
    origins = {}
    for item in modules:
        owner = item["module"]
        for decl in item["source_declarations"]:
            name = decl["qualified_name"]
            kind = {"theorem": "theorem", "abbrev": "definition", "def": "definition"}[decl["kind"]]
            pattern = re.escape(name)
            if decl["private"]:
                pattern = r"_private\." + re.escape(owner) + r"\.\d+\." + pattern
            matches = [r["name"] for r in records if r["module"] == owner and r["kind"] == kind
                       and re.fullmatch(pattern, r["name"])]
            if len(matches) != 1 or matches[0] in origins:
                raise ValueError("Missing, duplicated or ambiguous explicit declaration: " + name)
            origins[matches[0]] = "explicit_private" if decl["private"] else "explicit_public"
    return [{**r, "origin": origins.get(r["name"], "generated")} for r in records]


def verify_tool_hashes(observed, pinned):
    different = sorted(name for name in set(observed) | set(pinned)
                       if observed.get(name) != pinned.get(name))
    if different:
        raise ValueError("Tool hashes differ from pins: " + ", ".join(different))


DECL = re.compile(r"(?:@\[[^\n]*?\] )?(private )?(abbrev|def|theorem|lemma) ([\w']+)\b")


def source_declarations(source, namespace):
    """Compare the explicit contracts in these three ordinary, top-level source files."""
    declarations = []
    for chunk in re.split(r"(?m)(?=^\S)", shared.lean_code(source)):
        match = DECL.match(chunk)
        if match is None:
            # All non-declaration commands in this bounded legacy source are one-line.
            lines = [line for line in chunk.splitlines() if line.strip()]
            if lines and (len(lines) != 1 or lines[0].split()[0] not in {
                    "import", "namespace", "noncomputable", "open", "end"}):
                raise ValueError("Unsupported source command: " + lines[0])
            continue
        private, kind, name = match.groups()
        signature, assignment, _ = chunk.partition(":=")
        if not assignment:
            raise ValueError("Missing definition or proof: " + name)
        contract = signature if kind in {"theorem", "lemma"} else chunk
        declarations.append({"name": name, "qualified_name": namespace + "." + name,
                             "kind": kind, "private": private is not None,
                             "contract": " ".join(contract.split())})
    return declarations


def reverse_repairs(current, repairs):
    """Undo the documented proof edits and recover the original source exactly."""
    if not isinstance(repairs, list):
        raise ValueError("Expected an ordered expression repair list")
    seen = set()
    for repair in reversed(repairs):
        required = {"id", "original", "repaired", "reason", "diagnostic_task"}
        if not required <= repair.keys() or not all(isinstance(repair[k], str) and repair[k].strip()
                                                    for k in required):
            raise ValueError("Incomplete expression repair: " + str(repair.get("id")))
        name, before, after = repair["id"], repair["original"], repair["repaired"]
        if name in seen or before == after or current.count(after) != 1:
            raise ValueError("Duplicate or unanchored expression repair: " + name)
        current = current.replace(after, before, 1)
        if current.count(before) != 1:
            raise ValueError("Ambiguous original expression: " + name)
        seen.add(name)
    return current


def checkpoint_prefix(report, sources):
    """Stop at the first changed, unbuilt or explicitly failed supplier."""
    stages = {s["name"]: s["exit_code"] for s in report["stages"]}
    prefix = []
    for item in sources:
        module = item["module"]
        if (module not in report["project_object_bindings"]
                or report["source_sha256"].get(item["path"]) != item["sha256"]):
            break
        stage = module.split(".")[-1] + "-strict"
        if stage in stages:
            if stages[stage] != 0:
                break
        elif module not in report.get("reused_strict_origins", {}):
            break
        prefix.append(module)
    return prefix


def read_archive(path, digest):
    if path.resolve() != path or shared.sha256(path) != digest:
        raise ValueError("Checkpoint archive identity differs")
    with zipfile.ZipFile(path) as archive:
        names = archive.namelist()
        if len(set(names)) != len(names) or any(
                n.startswith("/") or ".." in Path(n).parts or n.endswith("/") for n in names):
            raise ValueError("Invalid checkpoint archive members")
        members = {n: archive.read(n) for n in names}
    manifest = json.loads(members.pop("ARCHIVE_MEMBERS.json"))
    actual = {n: {"bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}
              for n, raw in members.items()}
    if actual != manifest:
        raise ValueError("Checkpoint archive member digest or length differs")
    return members


def verify_bound_prefix(objroot, bindings, external):
    for module, binding in bindings.items():
        if shared.bind_object(module, objroot, external) != binding:
            raise ValueError("Changed checkpoint object: " + module)


def verify_sources(receipt):
    closure = shared.project_closure(ROOT, targets=TARGETS)
    intake = json.loads((ROOT / INTAKE).read_text())
    if closure != json.loads((ROOT / CLOSURE).read_text()) or closure["topological_order"] != list(TARGETS):
        raise ValueError("Committed source closure differs from the exact three-module chain")
    if (intake["baseline_commit"] != BASE or intake["targets"] != list(TARGETS)
            or intake["endpoint_names"] != list(ENDPOINT_NAMES)
            or [m["module"] for m in intake["modules"]] != list(TARGETS)):
        raise ValueError("Unexpected analytic source intake or endpoints")
    spec = json.loads((ROOT / CHECKPOINT).read_text())
    archive = checkpoint_archive(spec)
    paths = [*REQUIRED, *PROJECT_SOURCES, CHECKPOINT, archive]
    if any((ROOT / p).resolve() != ROOT / p for p in paths):
        raise ValueError("Redirected source input")
    hashes = {p: shared.sha256(ROOT / p) for p in paths}
    if hashes[archive] != spec["archive_sha256"]:
        raise ValueError("Checkpoint archive digest differs")
    if any(hashes[p] != value for p, value in shared.CONFIG_SHA256.items()):
        raise ValueError("Pinned configuration changed")
    if (ROOT / AUDIT).read_text() != shared.render_audit(TARGETS):
        raise ValueError("Owner audit differs from the full three-module audit template")
    for path in [*PROJECT_SOURCES, AUDIT, ENDPOINTS]:
        if shared.FORBIDDEN.search(shared.lean_code((ROOT / path).read_text())):
            raise ValueError("Forbidden proof escape in " + str(path))
    explicit_count = 0
    for record, item, namespace in zip(closure["project_sources"], intake["modules"], NAMESPACES, strict=True):
        path = record["path"]
        if (item["namespace"] != namespace or item["path"] != path
                or item["sha256"] != hashes[path] or record["sha256"] != hashes[path]):
            raise ValueError("Source intake identity differs: " + path)
        name = item["module"].split(".")[-1]
        blob = receipt.run(name + "-base-blob", "git", "rev-parse", BASE + ":" + path).strip()
        stage = name + "-base-source"
        receipt.run(stage, "git", "show", BASE + ":" + path)
        # Receipt.run returns translated text. Compare the actual Git blob bytes.
        original_bytes = (receipt.out / (stage + ".log")).read_bytes().split(b"\n", 1)[1]
        original = original_bytes.decode()
        if blob != item["baseline_git_blob"] or hashlib.sha256(original_bytes).hexdigest() != item["baseline_sha256"]:
            raise ValueError("Intake baseline source differs: " + path)
        current = (ROOT / path).read_bytes().decode()
        if reverse_repairs(current, item["expression_repairs"]) != original:
            raise ValueError("Documented repairs do not recover the original Git blob: " + path)
        if bool(item["expression_repairs"]) != (hashes[path] != item["baseline_sha256"]):
            raise ValueError("Recorded repair status differs: " + path)
        contracts = source_declarations(original, namespace)
        if contracts != source_declarations(current, namespace):
            raise ValueError("Explicit declaration names, definitions or statements changed: " + path)
        original_lines = original.splitlines()
        for contract, declaration in zip(contracts, item["source_declarations"], strict=True):
            if {k: v for k, v in contract.items() if k != "contract"} != {
                    k: v for k, v in declaration.items() if k != "baseline_line"}:
                raise ValueError("Explicit source declaration metadata differs: " + path)
            line = declaration["baseline_line"]
            match = DECL.match(original_lines[line - 1]) if 1 <= line <= len(original_lines) else None
            if not match or match.group(3) != declaration["name"]:
                raise ValueError("Explicit baseline declaration location differs: " + declaration["name"])
        explicit_count += len(contracts)
    if explicit_count != intake["source_only_explicit_declaration_count"]:
        raise ValueError("Source declaration count differs from intake")
    return closure, intake, hashes


class Receipt(shared.Receipt):
    def __init__(self, out, head):
        self.out = out
        self.env = dict(os.environ)
        self.external_scope = None
        self.data = {"status": "RUNNING", "started_utc": shared.now(), "baseline_commit": BASE,
                     "expected_head": head, "targets": list(TARGETS), "replay_targets": list(TARGETS),
                     "trust_mode": "NORMAL_IMPORTED_ENVIRONMENT_TRUST",
                     "full_external_kernel_replay_claimed": False,
                     "allowed_transitive_axioms": sorted(shared.ALLOWED), "stages": []}
        self.save()

    def save(self):
        # The shared setup writes its original caller's labels before checking packages.
        # Every intermediate or failed receipt must describe only this analytic closure.
        if self.external_scope is not None:
            self.data["external_scope"] = self.external_scope
        self.data.pop("prior_receipt_tool_sha256", None)
        self.data.pop("matches_prior_receipt_tool_hashes", None)
        super().save()


def checkpoint_evidence(owner, spec):
    archive = checkpoint_archive(spec)
    members = read_archive(owner / archive, spec["archive_sha256"])
    report = json.loads(members["verification/report.json"])
    provenance = json.loads(members["provenance/worktree-provenance.json"])
    head, tree, root = spec["source_commit"], spec["source_tree"], spec["source_root"]
    if (provenance["root"] != root or report["expected_head"] != head
            or any(provenance[k] != head for k in ("source", "initial_head", "final_head"))
            or provenance["tree"] != tree or provenance["final_tree"] != tree
            or provenance["initial_status"] or provenance["final_status"]
            or report["initial_checkout"] != {"root": root, "head": head, "working_tree": ""}
            or (report["status"], provenance["status"], provenance["gate_exit_code"])
               not in {("FAILED", "GATE_FAILED", 1), ("PASSED", "PASSED", 0)}
            or report["initial_project_object_parts"] != 0
            or report["baseline_commit"] != BASE or report["targets"] != list(TARGETS)
            or report["project_import_closure"]["topological_order"] != list(TARGETS)):
        raise ValueError("Checkpoint provenance, checkout or scope differs")
    for label, git_args, expected in (
            ("initial-head", ["rev-parse", "HEAD"], head),
            ("final-head", ["rev-parse", "HEAD"], head),
            ("tree", ["rev-parse", head + "^{tree}"], tree),
            ("final-tree", ["rev-parse", "HEAD^{tree}"], tree),
            ("initial-status", ["status", "--porcelain", "--untracked-files=all"], ""),
            ("final-status", ["status", "--porcelain", "--untracked-files=all"], "")):
        command, output = members["provenance/" + label + ".log"].decode().split("\n", 1)
        if command != "command=" + json.dumps(["git", *git_args]) or output.rstrip("\n") != expected:
            raise ValueError("Checkpoint Git provenance log differs: " + label)
    stages = report["stages"]
    if len({s["name"] for s in stages}) != len(stages) or any(s["exit_code"] != 0 for s in stages[:-1]):
        raise ValueError("Checkpoint stage history is inconsistent")
    for stage in stages:
        raw = members["verification/" + stage["name"] + ".log"]
        if (hashlib.sha256(raw).hexdigest() != stage["log_sha256"]
                or raw.split(b"\n", 1)[0].decode() != "command=" + json.dumps(stage["command"])):
            raise ValueError("Checkpoint stage log or command differs: " + stage["name"])
    if (set(provenance["sparse_paths"]) != set(report["source_sha256"])
            or report["source_sha256"]["verification/run_p34_primitive_analytic_cloud.py"]
               != provenance["launcher_sha256"]):
        raise ValueError("Checkpoint sparse input or launcher binding differs")
    return report, members


def authenticate_prefix(receipt, owner, sources, packages, syslib, snapshots):
    """Recursively establish the original strict command even for a copied prefix."""
    spec = json.loads((owner / CHECKPOINT).read_text())
    report, members = checkpoint_evidence(owner, spec)
    root = Path(spec["source_root"])
    head = spec["source_commit"]
    label = "checkpoint-" + spec["task_id"]
    if root.resolve(strict=True) != root or root == ROOT or root in snapshots:
        raise ValueError("Redirected, overlapping or cyclic checkpoint root")
    receipt.run(label + "-ancestor", "git", "-C", owner, "merge-base", "--is-ancestor", head, "HEAD")
    shared.git_checkout(receipt, root, label, head)
    tree = receipt.run(label + "-tree", "git", "-C", root, "rev-parse", "HEAD^{tree}").strip()
    if tree != spec["source_tree"] or shared.project_closure(root, targets=TARGETS) != report["project_import_closure"]:
        raise ValueError("Checkpoint tree or project source closure changed")
    oldpaths = set(REQUIRED + PROJECT_SOURCES)
    if CHECKPOINT in report["source_sha256"]:
        oldspec = json.loads((root / CHECKPOINT).read_text())
        oldpaths.update((CHECKPOINT, checkpoint_archive(oldspec)))
    if oldpaths != set(report["source_sha256"]):
        raise ValueError("Unexpected checkpoint source inputs")
    recheck_sources(report["source_sha256"], root)
    for field in ("tool_paths", "tool_sha256", "pinned_tool_sha256", "package_checkouts",
                  "configured_package_pins", "sysroot", "system_object_root", "lean_version"):
        if report[field] != receipt.data[field]:
            raise ValueError("Checkpoint environment differs: " + field)
    for path, digest in shared.CONFIG_SHA256.items():
        if report["source_sha256"][path] != digest:
            raise ValueError("Checkpoint configuration differs: " + path)

    oldobj = root / shared.OBJECTS
    if oldobj.resolve(strict=True) != oldobj or report["lean_path"] != os.pathsep.join(
            map(str, [oldobj, *packages.values()])):
        raise ValueError("Unexpected checkpoint project or package search path")
    prefix = checkpoint_prefix(report, sources)
    if report["project_import_closure"]["project_sources"][:len(prefix)] != sources[:len(prefix)]:
        raise ValueError("Checkpoint source or import graph differs within reusable prefix")
    bindings = {m: report["project_object_bindings"][m] for m in prefix}
    external = (*packages.values(), syslib)
    verify_bound_prefix(oldobj, bindings, external)
    # A failed job never ran its final invariants. Rebind even those external
    # inputs first read by the failing successor, keeping its project output excluded.
    old_external = report["direct_external_object_bindings"]
    parsed_external = {p for deps in report["parsed_dependencies"].values() for p in deps
                       if not Path(p).is_relative_to(oldobj)}
    if parsed_external != set(old_external):
        raise ValueError("Incomplete checkpoint external dependency inventory")
    for p, parts in old_external.items():
        path = Path(p)
        if (not path.is_file() or path != path.resolve() or path.suffix != ".olean"
                or not any(path.is_relative_to(allowed_root) for allowed_root in external)
                or shared.external_object_parts(path) != parts):
            raise ValueError("Changed or unowned checkpoint external object: " + p)
    snapshots[root] = {"spec": spec, "source_sha256": report["source_sha256"],
                       "bindings": bindings, "external": old_external}
    stages = {s["name"]: s for s in report["stages"]}
    inherited = [m for m in prefix if m.split(".")[-1] + "-strict" not in stages]
    ancestors = {}
    if inherited:
        if CHECKPOINT not in oldpaths:
            raise ValueError("Missing predecessor checkpoint for inherited strict evidence")
        _, inherited_bindings, ancestors = authenticate_prefix(
            receipt, root, sources[:len(inherited)], packages, syslib, snapshots)
        if inherited != list(inherited_bindings) or any(
                inherited_bindings[m]["parts"] != bindings[m]["parts"] for m in inherited):
            raise ValueError("Inherited checkpoint object or prefix differs")

    indexes = {s["name"]: i for i, s in enumerate(report["stages"])}
    prior_stage = -1
    fresh = set()
    origins = {}
    for module in prefix:
        source = shared.module_file(module, ".lean")
        stage = module.split(".")[-1]
        imports = stages[stage + "-imports"]
        lean = report["tool_paths"]["lean"]
        if (indexes[imports["name"]] <= prior_stage or imports["exit_code"] != 0
                or imports["command"] != [lean, "--deps", str(source)]):
            raise ValueError("Missing successful checkpoint import command: " + module)
        prior_stage = indexes[imports["name"]]
        log = members["verification/" + stage + "-imports.log"].decode().split("\n", 1)[1]
        deps = shared.expected_deps(root / source, log, fresh, oldobj, packages, syslib)
        if deps != report["parsed_dependencies"][module]:
            raise ValueError("Checkpoint parsed dependency binding differs: " + module)
        obj = oldobj / shared.module_file(module, ".olean")
        if module in ancestors:
            origin = ancestors[module]
            if origin != report["reused_strict_origins"][module]:
                raise ValueError("Inherited original strict provenance differs: " + module)
        else:
            compiled = stages[stage + "-strict"]
            if (module in report.get("reused_strict_origins", {}) or indexes[compiled["name"]] <= prior_stage
                    or compiled["exit_code"] != 0 or compiled["command"] !=
                    [lean, *STRICT_FLAGS, "-o", str(obj), str(source)]):
                raise ValueError("Missing exact successful checkpoint strict compile: " + module)
            prior_stage = indexes[compiled["name"]]
            origin = {**spec, "strict_stage": compiled["name"], "strict_log_sha256": compiled["log_sha256"]}
        origins[module] = origin
        fresh.add(obj)
    return oldobj, bindings, origins


def verify(args, receipt):
    data = receipt.data
    data["initial_checkout"] = shared.git_checkout(receipt, ROOT, "initial", args.expected_head)
    receipt.run("base-ancestor", "git", "merge-base", "--is-ancestor", BASE, args.expected_head)
    closure, intake, hashes = verify_sources(receipt)
    data.update(project_import_closure=closure, source_sha256=hashes, endpoint_names=list(ENDPOINT_NAMES))
    if args.source_only:
        recheck_sources(hashes)
        data["final_checkout"] = shared.git_checkout(receipt, ROOT, "final", args.expected_head)
        data.update(status="SOURCE_ONLY_NOT_COMPILED", finished_utc=shared.now())
        receipt.save()
        return

    objroot = ROOT / shared.OBJECTS
    if objroot != objroot.resolve() or (objroot.exists() and any(objroot.iterdir())):
        raise ValueError("Expected a fresh, empty project object root")
    if shared.checkout_object_parts():
        raise ValueError("Checkout already contains project object parts")
    objroot.mkdir(parents=True, exist_ok=True)
    data["initial_project_object_parts"] = 0
    pins = shared.package_pins(json.loads((ROOT / "lake-manifest.json").read_text()))
    data["configured_package_pins"] = pins
    receipt.external_scope = {
        "configured_package_count": len(pins), "direct_project_imports": closure["external_imports"],
        "audit_external_imports": ["Lean.Util.CollectAxioms"], "implicit_import": "Init",
        "external_kernel_replay": False,
    }
    toolchain = args.toolchain_root.resolve(strict=True)
    data["pinned_tool_sha256"] = shared.TOOL_HASHES
    data["tool_sha256"] = {k: shared.sha256(toolchain / "bin" / k) for k in shared.TOOL_HASHES}
    verify_tool_hashes(data["tool_sha256"], shared.TOOL_HASHES)
    tools, tool_hashes, packages, syslib = shared.prepare_environment(receipt, args, objroot)
    verify_tool_hashes(tool_hashes, shared.TOOL_HASHES)
    external = (*packages.values(), syslib)
    fresh = set()
    bindings = data["project_object_bindings"] = {}
    parsed = data["parsed_dependencies"] = {}
    external_objects = data["direct_external_object_bindings"] = {}
    replayed = data["replayed_modules"] = []
    flags = STRICT_FLAGS
    snapshots = {}
    oldobj, reusable, origins = authenticate_prefix(receipt, ROOT, closure["project_sources"],
                                                   packages, syslib, snapshots)
    data["checkpoint"] = json.loads((ROOT / CHECKPOINT).read_text())
    data["checkpoint_external_object_bindings"] = {
        p: parts for snapshot in snapshots.values() for p, parts in snapshot["external"].items()}
    reused = data["reused_strict_origins"] = {}
    strict_targets = data["strict_targets"] = []
    data.update(fresh_compiled_module_count=0, reused_compiled_module_count=0,
                reused_targets=[], attempted_strict_targets=[])
    receipt.save()
    lean = tools["lean"]

    def check_imports(stage, key, path):
        log = receipt.run(stage + "-imports", lean, "--deps", path)
        parsed[key] = shared.expected_deps(ROOT / path, log, fresh, objroot, packages, syslib)
        for dep in parsed[key]:
            if Path(dep) not in fresh and dep not in external_objects:
                external_objects[dep] = shared.external_object_parts(Path(dep))

    for item in closure["project_sources"]:
        module, path = item["module"], item["path"]
        stage = module.split(".")[-1]
        obj = objroot / shared.module_file(module, ".olean")
        if obj != obj.resolve() or any(Path(str(obj) + p).exists() for p in shared.PARTS):
            raise ValueError("Redirected or existing project object target: " + str(obj))
        obj.parent.mkdir(parents=True, exist_ok=True)
        print(("REUSE " if module in reusable else "STRICT ") + module, flush=True)
        check_imports(stage, module, path)
        if module in reusable:
            bindings[module] = shared.copy_checkpoint_object(module, reusable[module], oldobj, objroot, external)
            reused[module] = origins[module]
            data["reused_compiled_module_count"] = len(reused)
            data["reused_targets"].append(module)
        else:
            data["attempted_strict_targets"].append(module)
            receipt.run(stage + "-strict", lean, *flags, "-o", obj, path)
            bindings[module] = shared.bind_object(module, objroot, external)
            strict_targets.append(module)
            data["fresh_compiled_module_count"] = len(strict_targets)
        fresh.add(obj)
        receipt.save()
    for module in TARGETS:
        print("REPLAY " + module, flush=True)
        replay = receipt.run(module.split(".")[-1] + "-replay", tools["leanchecker"], "--verbose", module)
        if "replaying " + module not in replay.splitlines():
            raise ValueError("Missing replay evidence for " + module)
        replayed.append(module)
        receipt.save()
    check_imports("endpoints", str(ENDPOINTS), ENDPOINTS)
    receipt.run("endpoints", lean, *flags, ENDPOINTS)
    check_imports("owner-audit", str(AUDIT), AUDIT)
    log = receipt.run("owner-audit", lean, *flags, AUDIT)
    records, counts = shared.validate_inventory(log, modules=TARGETS)
    records = classify_declarations(records, intake["modules"])

    recheck_sources(hashes)
    if bindings != {m: shared.bind_object(m, objroot, external) for m in TARGETS}:
        raise ValueError("Fresh project object bindings changed")
    expected_parts = {p for binding in bindings.values() for p in binding["parts"]}
    if shared.object_parts(objroot) != expected_parts or set(shared.checkout_object_parts()) != {
            str(shared.OBJECTS / p) for p in expected_parts}:
        raise ValueError("Unexpected project object inventory")
    # Repeat exact namespace ownership checks as well as hashing previously bound parts.
    for key, paths in parsed.items():
        source = (ROOT / shared.module_file(key, ".lean")) if key in TARGETS else ROOT / key
        shared.expected_deps(source, "\n".join(paths), fresh, objroot, packages, syslib)
    if any(shared.external_object_parts(Path(p)) != parts for p, parts in external_objects.items()):
        raise ValueError("Direct external object parts changed")
    if any(p.resolve() != p for p in tools.values()):
        raise ValueError("Tool path redirected")
    verify_tool_hashes({k: shared.sha256(p) for k, p in tools.items()}, shared.TOOL_HASHES)
    if args.toolchain_root.resolve(strict=True) != toolchain or (toolchain / "lib/lean").resolve(strict=True) != syslib:
        raise ValueError("Toolchain installation redirected")
    for name, entry in data["package_checkouts"].items():
        checkout = (args.package_root / name).resolve(strict=True)
        if checkout != Path(entry["root"]) or (checkout / shared.OBJECTS).resolve(strict=True) != packages[name]:
            raise ValueError("Package or object root redirected: " + name)
        shared.git_checkout(receipt, checkout, "final-package-" + name, pins[name])
    for root, snapshot in snapshots.items():
        recheck_sources(snapshot["source_sha256"], root)
        verify_bound_prefix(root / shared.OBJECTS, snapshot["bindings"], external)
        if any(shared.external_object_parts(Path(p)) != parts for p, parts in snapshot["external"].items()):
            raise ValueError("Checkpoint external object changed during verification")
        spec = snapshot["spec"]
        shared.git_checkout(receipt, root, "final-checkpoint-" + spec["task_id"], spec["source_commit"])
    data["final_checkout"] = shared.git_checkout(receipt, ROOT, "final", args.expected_head)
    shared.json_file(receipt.out / "declarations.json", records)
    (receipt.out / "theorem-types.txt").write_text("head_commit=" + args.expected_head + "\n\n" +
        "\n\n".join(r["module"] + " [" + r["origin"] + "]\n" + r["name"] + " :\n" + r["type"]
                   + "\naxioms=" + ",".join(r["axioms"]) for r in records if r["kind"] == "theorem") + "\n")
    data.update(status="PASSED", finished_utc=shared.now(), module_counts=counts,
                declaration_count=len(records), origin_counts=dict(Counter(r["origin"] for r in records)),
                strict_coverage=list(TARGETS),
                strict_compile_sources={m: reused[m]["source_commit"] if m in reused
                                        else args.expected_head for m in TARGETS},
                artifacts_sha256={p: shared.sha256(receipt.out / p)
                                 for p in ("declarations.json", "theorem-types.txt")})
    receipt.save()


def recheck_sources(hashes, root=ROOT):
    for path, digest in hashes.items():
        source = root / path
        if source.resolve() != source or shared.sha256(source) != digest:
            raise ValueError("Source binding changed: " + path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-head", required=True)
    parser.add_argument("--source-only", action="store_true")
    parser.add_argument("--toolchain-root", type=Path)
    parser.add_argument("--package-root", type=Path)
    parser.add_argument("--output-dir", type=Path, default=ROOT / ".lake/p34-primitive-analytic-verification")
    args = parser.parse_args()
    if not re.fullmatch(r"[0-9a-f]{40}", args.expected_head):
        parser.error("--expected-head must be a full lowercase commit ID")
    if not args.source_only and (args.toolchain_root is None or args.package_root is None):
        parser.error("Fresh verification requires --toolchain-root and --package-root")
    out = args.output_dir.absolute()
    if out.resolve() != out or (out.exists() and any(out.iterdir())):
        parser.error("Verification requires a fresh output directory")
    out.mkdir(parents=True, exist_ok=True)
    receipt = Receipt(out, args.expected_head)
    try:
        verify(args, receipt)
    except BaseException as exc:
        receipt.data.update(status="FAILED", finished_utc=shared.now(), error=str(exc))
        receipt.save()
        raise
    print(receipt.data["status"], flush=True)


if __name__ == "__main__":
    main()
