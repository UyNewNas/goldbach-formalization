#!/usr/bin/env python3
"""Dormant four-owner Cell00 typed-pulling continuation; no accepted gate rerun.

The exact reviewed source bytes are copied, never generated. Six accepted
objects retain their original owner receipts and context. Four fresh owners
receive the existing normal/replay/complete-owned gates. Actual reviewed v6
success must be pinned before any filesystem or subprocess action.
"""
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time
import traceback

ROOT = Path('/workspace/p25-q96-20261125')
OUT = ROOT / '.lake/diagnostic/p25-cell00-typed-pulling-attempt001'
RUNNER_REL = 'docs/verification/20261126-p2-5-resumed/cell00-typed-pulling/run_typed_pulling.py'
MANIFEST_REL = 'docs/verification/20261126-p2-5-resumed/cell00-typed-pulling/RUNNER_MANIFEST.json'
SOURCE_SELECTION_REL = 'docs/source-only/20261126-p2-5-cell00-finite-geometry/SOURCE_SELECTION.json'
SOURCE_SELECTION_SHA = 'db7faff1e43f09869edde6600ef452bca1bef24a2668ff19611509cf375d0d92'
V6_RESULT_SHA = None
V6_ARTIFACTS_REVIEWED = False
V6_PUBLICATION = '4653b261828f127ba0b5082eaf1106a3fea09d46'
V6_RESULT = ROOT / '.lake/diagnostic/p25-cell00-four-consumers-attempt006/RESULT.json'
V6_DRIVER = 'docs/verification/20261126-p2-5-resumed/run_cell00_four_consumers_v6.py'
V6_DRIVER_SHA = '064fa8414660f7036b51bf6bf336f1aef168913dca5722cd4050b9d005174f7a'
PREVIOUS_RESULT = ROOT / '.lake/diagnostic/p25-cell00-five-consumers-attempt005/RESULT.json'
PREVIOUS_RESULT_SHA = 'bc26ddfa2b6a06ce4935430f6bedaf2419c7a1033723c98efe499f24116fdf88'
PREVIOUS_PUBLICATION = 'be20f0b050bb787ecb98f9afdd9b6a386706f45a'
LEGACY_OUTER = ROOT / '.lake/p25-unguarded-sources/attempt001/RUN_RESULT.json'
LEGACY_OUTER_SHA = 'cb11eb092d12e3e1f08eb9dccad4ecbe53311f456babe6c0ccabe72b93c3fa65'
LEGACY_PUBLICATION = '448e03d6ce02fd7d3b8d008defcd5ffffc4fc426'
LOCAL_LEGACY_OUTER = 'docs/source-only/20261125-p2-5-decoder/p3-actual/p25-unguarded-sources/attempt001/RUN_RESULT.json'
INPUT_HELPER = 'docs/source-only/20261125-p2-5-decoder/run_unguarded_sources.py'
INPUT_HELPER_SHA = '30350d5baac2abfd9491d01f1d7fc02230ef44fc7e641830af378b8ad1bb4a59'
INPUT_MANIFEST = 'docs/verification/20261125-p2-5-saving16/Q96_EXISTING_INPUTS_AND_SOURCES.json'
INPUT_MANIFEST_SHA = '79404a0f8ed17c2d49fd377363a5169936628ff88e8e7fdd6d5165c8c6a917e0'
PRIVATE_AUDIT_HELPER = 'verification/part2/run_winner9_private_audit.py'
PRIVATE_AUDIT_HELPER_SHA = '571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5'
PRIVATE_CHECK_HELPER = 'verification/part2/run_winner9_private_checks.py'
PRIVATE_CHECK_HELPER_SHA = 'f7816db16309f99b6f3babbe128425c06818b3da1dec556dffffe5e8132a6314'
PRIVATE_RECORDS = ROOT / '.lake/p2-private/records.json'
PAYLOAD = 'ImbalancedChen.P2Saving16Cell00TypedPayload'
SUPPORT = 'ImbalancedChen.P2Saving16Cell00FieldSimp'
INPUT = 'ImbalancedChen.P2OriginalSaving16OriginalInput'
CORE_OWNER = 'ImbalancedChen.P2OriginalSaving16FiniteCore'
JSON_OWNER = 'ImbalancedChen.P2Saving16Cell00OriginalJson'
FINITE_CORE = ROOT / '.lake/diagnostic/p25-finite-core-attempt001'
FINITE_CORE_RECEIPT_SHA = 'b1f2a463ed670e01335244dc35f1e0a3614ced20bbea791a5a5d72e980e95dd9'
PAYLOAD_FLOORS = ROOT / '.lake/diagnostic/p25-payload-floors-attempt001'
PAYLOAD_RESULT_SHA = '090463b93761d31023f39111c32522e1f2bb3cbcec46e606f7fc429d69d4a204'
PAYLOAD_FILES = 'docs/source-only/20261126-p2-5-cell00-decoded/TYPED_PAYLOAD_FILES.json'
PAYLOAD_FILES_SHA = '76aa078eef969fa6c8d8270529f3d68f50b4bb6762626ba14a484423bbdc4321'
AUDIT_TEMPLATE = 'docs/source-only/20261126-p2-5-cell00-decoded/TYPED_PAYLOAD_AUDIT.lean'
AUDIT_TEMPLATE_SHA = 'cd452bddeee765b82187f03893cddb5f7136e3420591f0ea00c9bfe1028f670a'
EXTERNAL_SNAPSHOT_SHA = 'b94ab99b39a831a616d626c55c4b89c0a921d15c95319de19063d375bc982728'
EXPECTED_EXTERNAL_COUNT = 5312
EXPECTED_EXTERNAL_COMPANIONS = 10624
LEAN = Path('/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean')
CHECKER = LEAN.with_name('leanchecker')
MATHLIB_PIN = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
FLAGS = ['-t0', '-j1', '-M11264', '-DwarningAsError=true', '-DmaxRecDepth=1000000', '-DmaxHeartbeats=80000000']
LEGACY_FLAGS = ['-t0', '-j1', '-M11264', '-DwarningAsError=true', '-DmaxRecDepth=50000', '-DmaxHeartbeats=40000000']
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
AXIOMS = ALLOWED_AXIOMS
CACHE_SCHEMA = 2
EXTERNAL_CACHE_SCHEMA = 3
MIN_INITIAL_FREE_BYTES = 1024 * 1024 * 1024
GATE_WORKING_HEADROOM_BYTES = 256 * 1024 * 1024
SOURCES = {}
FRESH_MODULES = ['ImbalancedChen.P2OriginalSaving16FaceDecoderCore', 'ImbalancedChen.P2OriginalSaving16FiniteGeometryCore', 'ImbalancedChen.P2OriginalSaving16PullingFaceInduction', 'ImbalancedChen.P2Saving16Cell00TypedPulling']
KNOWN_OBJECTS = {'ImbalancedChen.P2OriginalSaving16Decoder': 'fd25815778e3bae5518d3fcc6a5461724b64251f91c4c08e61312fbae4987b39', 'ImbalancedChen.P2OriginalSaving16OriginalInput': '72488821ccb01dec90188d2f09b0e3a73c0087b54c6c4bae4410a109b6f82f91', 'ImbalancedChen.P2OriginalSaving16Q96FloorCore': '720df453f67d6650c195b737357d87aafb511b10a87dbf8654ae2fc6d9e712b9', 'ImbalancedChen.P2OriginalSaving19SourceJson': '50b1caec038208d3becd6cbef3a318b1d2966add295c060ad28d8999e1aa64e7', 'ImbalancedChen.P2OriginalSaving16FiniteCore': '83923cb30eed3a39509324af01988e9708005913b304bb63fd2f56dcee82604c', 'ImbalancedChen.P2Saving16Cell00TypedPayload': '1c61948df2571b065f3b27ae2eeeff1202b942e39bb16229f93c9cc40b1e8c75'}
SOURCE_HASHES = {'ImbalancedChen.P2OriginalSaving16Decoder': 'e1b23e3de928a97c411d1c6aa73f2059b204d7b9f297105edcd591916b9aee80', 'ImbalancedChen.P2OriginalSaving16OriginalInput': '792a5adf50263cfc1a0f67fb3d088c7612910388e4d1fa65db45c3c50065aca5', 'ImbalancedChen.P2OriginalSaving16Q96FloorCore': '9a456807e6c3a167fd12c1c6e5db492d6c54fd700a1de122ea492774f697c778', 'ImbalancedChen.P2OriginalSaving19SourceJson': 'd58e22ba7e2d92b6c9f2d139993361ae9b827d25d6869fcf38f3837ba7bc3d02', 'ImbalancedChen.P2OriginalSaving16FiniteCore': '552f7ac2f777173c0f555896d85d98bd17513fc972e520f7a0f4dbc406a96322', 'ImbalancedChen.P2Saving16Cell00TypedPayload': 'e92848bd075bf82fe7325bd46e3ddcde937cba277387d46a3579560c27aa287b', 'ImbalancedChen.P2OriginalSaving16FaceDecoderCore': 'e689722471f796762f430073702978e3e92e5a2553e9aac4957c480337e4d21d', 'ImbalancedChen.P2OriginalSaving16FiniteGeometryCore': 'd710f472c975e11a229c6018eb2b353ebf98119363cfbd35b0f9cdb9444040fe', 'ImbalancedChen.P2OriginalSaving16PullingFaceInduction': 'e12ef58905dada51d9233644443f06967fa46588881a000437d679c9fa026448', 'ImbalancedChen.P2Saving16Cell00TypedPulling': 'b9e929148191385de1eb1dc8016acf919b7f4e551da383d165eb89b12478f22b'}
PROJECT_IMPORTS = {'ImbalancedChen.P2OriginalSaving16Decoder': ['ImbalancedChen.P2OriginalSaving16Q96FloorCore', 'ImbalancedChen.P2OriginalSaving19SourceJson'], 'ImbalancedChen.P2OriginalSaving16OriginalInput': [], 'ImbalancedChen.P2OriginalSaving16Q96FloorCore': [], 'ImbalancedChen.P2OriginalSaving19SourceJson': [], 'ImbalancedChen.P2OriginalSaving16FiniteCore': ['ImbalancedChen.P2OriginalSaving16OriginalInput', 'ImbalancedChen.P2OriginalSaving16Decoder', 'ImbalancedChen.P2OriginalSaving16Q96FloorCore', 'ImbalancedChen.P2OriginalSaving19SourceJson'], 'ImbalancedChen.P2Saving16Cell00TypedPayload': ['ImbalancedChen.P2OriginalSaving16Decoder'], 'ImbalancedChen.P2OriginalSaving16FaceDecoderCore': ['ImbalancedChen.P2OriginalSaving19SourceJson'], 'ImbalancedChen.P2OriginalSaving16FiniteGeometryCore': ['ImbalancedChen.P2OriginalSaving16FiniteCore'], 'ImbalancedChen.P2OriginalSaving16PullingFaceInduction': ['ImbalancedChen.P2OriginalSaving16FiniteGeometryCore'], 'ImbalancedChen.P2Saving16Cell00TypedPulling': ['ImbalancedChen.P2OriginalSaving16FaceDecoderCore', 'ImbalancedChen.P2OriginalSaving16PullingFaceInduction', 'ImbalancedChen.P2Saving16Cell00TypedPayload']}
V6_MODULES = ['ImbalancedChen.P2Saving16Cell00OriginalParse', 'ImbalancedChen.P2Saving16Cell00OriginalFloors', 'ImbalancedChen.P2Saving16Cell00OriginalArithmetic', 'ImbalancedChen.P2Saving16Cell00OriginalSourceFacts']
LEGACY_MODULES = ['ImbalancedChen.P2OriginalSaving16Decoder', 'ImbalancedChen.P2OriginalSaving16OriginalInput', 'ImbalancedChen.P2OriginalSaving16Q96FloorCore', 'ImbalancedChen.P2OriginalSaving19SourceJson']

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def now():
    return datetime.now(timezone.utc).isoformat()

def git(*args, cwd=ROOT):
    return subprocess.check_output(['git', *args], cwd=cwd, timeout=120).decode().strip()

def record_file(path):
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': digest(path)}

def project_closure(module):
    found = set()

    def visit(name):
        if name in found:
            return
        require(name in SOURCES, f'Unspecified project import: {name}')
        found.add(name)
        for imported in SOURCES[name]['project_imports']:
            visit(imported)

    visit(module)
    return found

def read_audit(log, module):
    lines = log.read_text().splitlines()
    records = [json.loads(s.removeprefix('P0_QUEUE_DECL ')) for s in lines if s.startswith('P0_QUEUE_DECL ')]
    inventories = [json.loads(s.removeprefix('P0_QUEUE_INVENTORY ')) for s in lines if s.startswith('P0_QUEUE_INVENTORY ')]
    imports = [json.loads(s.removeprefix('P0_QUEUE_IMPORTS ')) for s in lines if s.startswith('P0_QUEUE_IMPORTS ')]
    names = sorted(r['name'] for r in records)
    require(len(inventories) == len(imports) == 1 and inventories[0]['module'] == module,
            f'Missing/duplicate full inventory: {module}')
    require(names and len(names) == len(set(names)) and
            names == sorted(inventories[0]['serialized']) == sorted(inventories[0]['environment']),
            f'Incomplete serialized/environment/declaration inventory: {module}')
    require(all(r['module'] == module and not any(r[k] for k in ['axiom', 'partial', 'unsafe']) and
                set(r['axioms']) <= ALLOWED_AXIOMS for r in records), f'Forbidden declaration/axiom: {module}')
    actual = {m for m in imports[0] if m.startswith('ImbalancedChen.')}
    require(actual == project_closure(module), f'Actual project closure mismatch: {module}: {sorted(actual)}')
    return records, inventories[0], sorted(actual)

def audited_imports(log):
    rows = [json.loads(line.removeprefix('P0_QUEUE_IMPORTS '))
            for line in Path(log).read_text().splitlines() if line.startswith('P0_QUEUE_IMPORTS ')]
    require(len(rows) == 1 and len(rows[0]) == len(set(rows[0])),
            'Missing or duplicate full imported-module inventory.')
    return rows[0]

def read_private_scope_audit(log, records, required):
    # Same check as the accepted Field-split 3b774024 driver, with explicit scope.
    marker = 'P25_PRIVATE_SCOPED_SIMP_INTERFACE '
    rows = [json.loads(s.removeprefix(marker)) for s in Path(log).read_text().splitlines() if s.startswith(marker)]
    require(len(rows) == 1, 'Missing or duplicate imported private scoped-simp interface audit.')
    row = rows[0]
    matches = row['matches']
    require(row['module'] == SUPPORT and row['scope'] == SCOPE and
            row['required_count'] == row['matched_count'] == len(matches) == len(required) == 296 and
            [r['user_name'] for r in matches] == required and len({r['actual_name'] for r in matches}) == 296,
            'Private scoped-simp interface inventory differs.')
    owned = {r['name'] for r in records}
    for match in matches:
        candidates = [name for name in owned if name.endswith('.' + match['user_name'])]
        require(candidates == [match['actual_name']] and match['actual_name'].startswith('_private.'),
                'Scoped-simp name is not the unique actual private declaration in the full owned audit.')
    return row

def check_disk_space(required_free_bytes, purpose):
    """Read live capacity; no deletion, cache adoption, or storage mutation."""
    require(type(required_free_bytes) is int and required_free_bytes > 0, 'Invalid disk-space requirement.')
    free = shutil.disk_usage(ROOT).free
    require(free >= required_free_bytes,
            f'DISK_SPACE: {purpose}: {free} bytes free; at least {required_free_bytes} required.')
    return {'checked_utc': now(), 'purpose': purpose, 'free_bytes': free,
            'required_free_bytes': required_free_bytes}

def input_snapshot(rows):
    data_path = ROOT / "../goldbach-research"
    data_dir = data_path.resolve()
    result = {
        "cwd": str(ROOT), "directory": str(data_dir),
        "directory_realpath": str(data_dir.resolve()),
        "directory_identity": None, "files": [], "errors": [],
    }
    if data_path.is_symlink():
        result["errors"].append("Input directory is a symlink")
    try:
        directory = data_dir.stat()
        result["directory_identity"] = {
            "device": directory.st_dev, "inode": directory.st_ino,
            "mtime_ns": directory.st_mtime_ns, "ctime_ns": directory.st_ctime_ns,
        }
    except OSError as error:
        result["errors"].append(str(error))
    for row in rows:
        path = ROOT / row["install_path"]
        item = {"install_path": row["install_path"], "realpath": str(path.resolve())}
        try:
            if path.is_symlink():
                result["errors"].append("Input file is a symlink: " + str(path))
            stat = path.stat()
            actual = digest(path)
            item.update({
                "bytes": stat.st_size, "sha256": actual,
                "device": stat.st_dev, "inode": stat.st_ino,
                "mtime_ns": stat.st_mtime_ns, "ctime_ns": stat.st_ctime_ns,
            })
            if stat.st_size != row["bytes"] or actual != row["sha256"]:
                result["errors"].append("Original input differs: " + str(path))
        except OSError as error:
            item["error"] = str(error)
            result["errors"].append(str(error))
        result["files"].append(item)
    if len(result["files"]) != 14 or sum(item.get("bytes", 0) for item in result["files"]) != 93508187:
        result["errors"].append("Expected fourteen original inputs totaling 93508187 bytes")
    result["all_inputs_match_manifest"] = not result["errors"]
    return result

def parse_audit(log: Path, target: str, project: set[str]) -> dict:
    inventories, import_lists, declarations = [], [], []
    for line in log.read_text().splitlines():
        for prefix, output in (("P0_QUEUE_IMPORTS ", import_lists),
                               ("P0_QUEUE_INVENTORY ", inventories),
                               ("P0_QUEUE_DECL ", declarations)):
            if line.startswith(prefix):
                output.append(json.loads(line[len(prefix):]))
                break
    require(len(import_lists) == 1 and isinstance(import_lists[0], list), "Missing/duplicate import inventory")
    actual_project = {name for name in import_lists[0] if name.startswith("ImbalancedChen.")}
    require(actual_project == project, "Loaded project modules differ from the frozen source closure")
    require(len(inventories) == 1 and inventories[0].get("module") == target,
            "Missing/duplicate/wrong target inventory")
    inventory = inventories[0]
    serialized, environment = inventory["serialized"], inventory["environment"]
    require(serialized and len(serialized) == len(set(serialized))
            and sorted(serialized) == sorted(environment), "Serialized/environment inventory mismatch")
    names = [record["name"] for record in declarations]
    require(len(names) == len(set(names)) and sorted(names) == sorted(serialized),
            "Declaration records do not exactly cover the owned inventory")
    for record in declarations:
        require(record.get("module") == target, "Declaration belongs to another module")
        require(all(record.get(flag) is False for flag in ("unsafe", "partial", "axiom")),
                "Unsafe/partial/axiom declaration: " + record["name"])
        require(isinstance(record.get("type"), str) and record["type"] and "⋯" not in record["type"],
                "Missing/truncated declaration type: " + record["name"])
        require(isinstance(record.get("axioms"), list) and set(record["axioms"]) <= AXIOMS,
                "Forbidden transitive axiom: " + record["name"])
    return {"inventory": inventory, "imports": import_lists[0], "declarations": declarations,
            "declaration_count": len(declarations),
            "axiom_counts": dict(sorted(Counter(ax for rec in declarations for ax in rec["axioms"]).items()))}

def json_digest(payload: dict) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()

def closure_signature(record: dict) -> str:
    """Bind the source/object to the recursively frozen dependency environment.

    A parent's .olean bytes can remain identical when an imported definition
    changes. Object hashes alone therefore do not identify the proof context.
    This helper must only be called for actual compilation snapshots or an
    explicitly evidenced historical migration, never to backfill an old probe
    with whatever dependency objects happen to exist now.
    """
    payload = {key: record[key] for key in (
        "module", "source_sha256", "object_sha256", "toolchain", "dependency_signatures")}
    payload["cache_schema"] = record.get("cache_schema", CACHE_SCHEMA)
    if payload["cache_schema"] == EXTERNAL_CACHE_SCHEMA:
        payload["external_snapshot"] = record["external_snapshot"]
    return json_digest(payload)

def require_workflow_ready():
    require(isinstance(V6_RESULT_SHA, str) and re.fullmatch(r'[0-9a-f]{64}', V6_RESULT_SHA)
            and V6_ARTIFACTS_REVIEWED is True,
            'Dormant: actual successful v6 receipt and reviewed artifacts must be pinned first.')


def validate_manifest(manifest):
    require(manifest['schema'] == 'p25-cell00-typed-pulling-runner-manifest-v1'
            and manifest['fresh_owner_order'] == FRESH_MODULES
            and set(manifest['accepted_dependencies']) == set(KNOWN_OBJECTS)
            and len(manifest['accepted_dependencies']) == 6
            and manifest['source_selection_sha256'] == SOURCE_SELECTION_SHA
            and manifest['v6_result_sha256'] == V6_RESULT_SHA
            and manifest['v6_artifacts_reviewed'] is V6_ARTIFACTS_REVIEWED
            and manifest['P2_5_proved'] is False,
            'Runner manifest changes the dormant scope or prerequisite.')
    graph = manifest['source_graph']
    require(set(graph) == set(FRESH_MODULES) | set(KNOWN_OBJECTS) and len(graph) == 10,
            'Exactly four fresh owners and six accepted dependencies are required.')
    for module, spec in graph.items():
        require(spec['source_sha256'] == SOURCE_HASHES[module]
                and spec['project_imports'] == PROJECT_IMPORTS[module],
                'Pinned source/import identity differs: ' + module)
        require(set(spec['project_imports']) <= set(graph), 'Unselected import: ' + module)
    available = set(KNOWN_OBJECTS)
    for module in FRESH_MODULES:
        require(set(graph[module]['project_imports']) <= available,
                'Fresh owner order is not topological: ' + module)
        available.add(module)
    return graph


def validate_v6_result(receipt, previous):
    require(receipt.get('schema') == 'p25-cell00-four-consumers-strict-v6'
            and receipt.get('accepted') is True
            and receipt.get('status') == 'ORIGINAL_CELL00_FOUR_CONSUMERS_ACCEPTED'
            and receipt['publication_commit'] == V6_PUBLICATION
            and receipt['runner']['sha256'] == V6_DRIVER_SHA
            and receipt['module_order'] == V6_MODULES and set(receipt['modules']) == set(V6_MODULES)
            and receipt['complete_external_after_matches_before'] is True
            and receipt['accepted_dependency_gates_rerun'] == receipt['dependency_modules_compiled']
                == receipt['existing_owners_normally_recompiled'] == receipt['decoded_gates_rerun'] == []
            and receipt['private_parse_helpers_audited'] is True
            and receipt['failed_parse_aggregate_relabelled'] is False
            and len(receipt['dependency_objects']) == 41
            and receipt['Q96_proved'] is False and receipt['P2_5_proved'] is False,
            'Actual complete successful v6 acceptance is required.')
    for module in V6_MODULES:
        owner = receipt['modules'][module]
        require(owner['module'] == module and owner['accepted'] is True
                and owner['status'] == 'NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED'
                and owner['source_origin']['commit'] == V6_PUBLICATION
                and set(owner['stages']) == {'normal', 'replay', 'audit'}
                and all(row['status'] == 'PASSED' and row['exit_code'] == 0
                        and row['timed_out'] is False for row in owner['stages'].values()),
                'A v6 owner lacks actual complete acceptance: ' + module)
    decoded = 'ImbalancedChen.P2Saving16Cell00Decoded'
    require(previous['accepted'] is False and previous['status'] == 'MODULE_STAGE_FAILED'
            and previous['publication_commit'] == PREVIOUS_PUBLICATION
            and receipt['previous_parse_failed_owner'] == previous['modules'][V6_MODULES[0]]
            and receipt['reused_decoded_owner_receipt'] == previous['modules'][decoded]
            and receipt['previous_parse_failure']['aggregate_accepted'] is False
            and receipt['previous_parse_failure']['sha256'] == PREVIOUS_RESULT_SHA
            and receipt['reused_decoded_owner_receipt_source']['sha256'] == PREVIOUS_RESULT_SHA
            and receipt['reused_decoded_owner_receipt']['accepted'] is True,
            'The failed005 aggregate and its accepted Decoded owner must remain distinct.')
    for module, expected in KNOWN_OBJECTS.items():
        require(receipt['dependency_objects'][module]['sha256'] == expected
                == previous['dependency_objects'][module]['sha256']
                and receipt['dependency_objects'][module]['source_sha256'] == SOURCE_HASHES[module]
                == previous['dependency_objects'][module]['source_sha256'],
                'A selected accepted dependency changed between v5 and v6: ' + module)


def validate_private_outer(outer):
    require(outer['accepted'] is True and outer['publication_commit'] == LEGACY_PUBLICATION
            and outer['original_input_fresh_data_to_object_bound'] is True
            and outer['inputs_unchanged'] is True and outer['sources_gates_toolchain_unchanged'] is True
            and outer['records_objects_unchanged_during_audit'] is True
            and outer['fresh_compilation'][INPUT] is True
            and INPUT in outer['normal']['exact_START_modules']
            and outer['input_snapshot_after_compile'] == outer['input_snapshot_after_audit']
                == outer['final_input_snapshot']
            and outer['final_input_snapshot']['all_inputs_match_manifest'] is True,
            'The original four-owner receipt lacks its actual fourteen-input binding.')
    require(set(outer['owned_receipts']) == set(LEGACY_MODULES)
            and set(outer['compile_records']) == set(LEGACY_MODULES), 'Legacy owner set differs.')
    for module in LEGACY_MODULES:
        record = outer['compile_records'][module]
        owner = outer['owned_receipts'][module]['receipt']
        require(record['cache_schema'] == CACHE_SCHEMA and record['module'] == module
                and record['exit_code'] == 0 and record['source_sha256'] == SOURCE_HASHES[module]
                and record['object_sha256'] == KNOWN_OBJECTS[module]
                and record['closure_signature'] == closure_signature(record)
                and record['command'][:1 + len(LEGACY_FLAGS)] == [str(LEAN), *LEGACY_FLAGS]
                and record['toolchain']['lean_binary_sha256'] == 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
                and record['toolchain']['mathlib_commit'] == MATHLIB_PIN,
                'Legacy compilation signature/source/object/runtime differs: ' + module)
        deps = PROJECT_IMPORTS[module]
        require(record['deps'] == {dep: KNOWN_OBJECTS[dep] for dep in deps}
                and record['dependency_signatures'] == {
                    dep: outer['compile_records'][dep]['closure_signature'] for dep in deps},
                'Legacy dependency signature graph differs: ' + module)
        require(owner['accepted'] is True and owner['module'] == module
                and owner['source_sha256'] == SOURCE_HASHES[module]
                and owner['object_sha256'] == KNOWN_OBJECTS[module]
                and owner['compile_closure_signature'] == record['closure_signature']
                and outer['compiled_objects'][module]['sha256'] == KNOWN_OBJECTS[module]
                and owner['input_snapshot']['project'][module]['object_sha256'] == KNOWN_OBJECTS[module],
                'Legacy owned receipt does not bind its actual compilation: ' + module)
        for label in ['replay', 'audit']:
            require(owner[label]['exit_code'] == 0 and owner[label]['inputs_unchanged'] is True,
                    'Legacy owner replay/audit failed: ' + module)


def main():
    global SOURCES
    require_workflow_ready()
    require(sys.flags.optimize == 0, 'Do not run with Python -O')
    require(len(sys.argv) == 2 and re.fullmatch(r'[0-9a-f]{40}', sys.argv[1]),
            'Pass one exact already-fetched publication40')
    publication = sys.argv[1]
    require(ROOT.is_dir() and not ROOT.is_symlink() and not OUT.exists() and not OUT.is_symlink(),
            'Missing own worktree or existing/symlinked output; preserve all prior attempts.')
    require(OUT.parent.resolve().is_relative_to(ROOT.resolve()), 'Output parent escapes own worktree.')
    initial_disk = check_disk_space(MIN_INITIAL_FREE_BYTES, 'before fresh typed-pulling output')
    require(digest(V6_RESULT) == V6_RESULT_SHA and digest(PREVIOUS_RESULT) == PREVIOUS_RESULT_SHA,
            'Actual v6 or original failed005 receipt hash differs.')
    workflow = json.loads(V6_RESULT.read_text())
    previous = json.loads(PREVIOUS_RESULT.read_text())
    validate_v6_result(workflow, previous)
    initial_head = git('rev-parse', 'HEAD')
    require(initial_head in {V6_PUBLICATION, publication}
            and not git('status', '--porcelain', '--untracked-files=no'), 'Unexpected/dirty task worktree.')
    require(subprocess.run(['git', 'merge-base', '--is-ancestor', V6_PUBLICATION, publication],
                           cwd=ROOT, check=False).returncode == 0, 'Publication is not a v6 continuation.')
    published_runner = subprocess.check_output(['git', 'show', publication + ':' + RUNNER_REL], cwd=ROOT, timeout=120)
    require(published_runner == Path(__file__).read_bytes(), 'Executing runner differs from publication.')
    manifest_bytes = subprocess.check_output(['git', 'show', publication + ':' + MANIFEST_REL], cwd=ROOT, timeout=120)
    manifest = json.loads(manifest_bytes)
    require(manifest['runner_sha256'] == digest(Path(__file__)), 'Runner manifest/code mismatch.')
    SOURCES = validate_manifest(manifest)
    require(project_closure(FRESH_MODULES[-1]) == set(SOURCES), 'The actual selected closure is not exactly ten modules.')
    OUT.mkdir()
    state = {'schema': 'p25-cell00-typed-pulling-strict-v1', 'status': 'PREFLIGHT', 'accepted': False,
             'publication_commit': publication, 'started_utc': now(), 'runner': record_file(Path(__file__).resolve()),
             'strict_flags': FLAGS, 'stage_wall_limit_seconds': 600, 'module_order': FRESH_MODULES,
             'modules': {}, 'source_graph': SOURCES, 'dependency_objects': {}, 'dependency_receipts': {},
             'dependency_modules_compiled': [], 'accepted_dependency_gates_rerun': [], 'private_records_written': [],
             'source_generation_performed': False, 'storage_cleanup_performed': False,
             'v6_gates_rerun': [], 'legacy_owned_receipts': {}, 'disk_checks': [initial_disk],
             'typed_face_decode_proved': False, 'typed_shape_proved': False, 'typed_ordered_pull_nodup_proved': False,
             'original_archive_transport_proved': False, 'source_cell_membership_proved': False,
             'all96_vertex_inequalities_proved': False, 'geometric_pulling_ownership_proved': False,
             'Literal96_imported': False, 'Q96_proved': False, 'P2_5_proved': False, 'host_correctness_credit': False}
    frozen = {}
    external_entries = []
    expected_external = set()
    providers = []
    target_names = set(FRESH_MODULES)
    appendix_text = ''
    expected_private = []
    def write():
        temp = OUT / 'RESULT.tmp'
        temp.write_text(json.dumps(state, ensure_ascii=False, indent=2) + '\n')
        temp.replace(OUT / 'RESULT.json')

    def bind(path, expected=None):
        path = Path(path)
        actual = digest(path)
        require(expected is None or actual == expected, f'Artifact hash mismatch: {path}')
        require(str(path) not in frozen or frozen[str(path)] == actual, f'Artifact changed during preflight: {path}')
        frozen[str(path)] = actual
        return path

    def artifact(row, expected=None):
        path = bind(row['path'], expected or row['sha256'])
        require(digest(path) == row['sha256'] and path.stat().st_size == row['bytes'], f'Artifact record mismatch: {path}')
        return path

    def check_frozen():
        require(all(digest(path) == h for path, h in frozen.items()), 'Frozen source/object/receipt/log/runtime changed.')

    def external_resolutions():
        require(len(external_entries) == len(expected_external) == EXPECTED_EXTERNAL_COUNT,
                'Complete current external context has not been initialized.')
        for row in external_entries:
            relative = row['module'].replace('.', '/') + '.olean'
            found = [provider / relative for provider in providers if (provider / relative).is_file()]
            require([str(path) for path in found] == [row['object']['path']],
                    'External import provider changed: ' + row['module'])
            companions = [str(found[0]) + suffix for suffix in ['.private', '.server']
                          if Path(str(found[0]) + suffix).is_file()]
            require(companions == [entry['path'] for entry in row['companions']],
                    'External companion inventory changed: ' + row['module'])

    def context_check():
        require(git('rev-parse', 'HEAD') == publication and
                not git('status', '--porcelain', '--untracked-files=no'), 'Selected publication changed during gates.')
        require(git('rev-parse', 'HEAD', cwd=Path(state['runtime']['mathlib_path'])) == MATHLIB_PIN,
                'Mathlib source pin changed during gates.')
        external_resolutions()
        check_frozen()

    def require_external(log, expected_count=EXPECTED_EXTERNAL_COUNT):
        external = {m for m in audited_imports(log) if not m.startswith('ImbalancedChen.')}
        require(external <= expected_external and len(external) == expected_count,
                'Audited external imports are not the selected accepted subset of the complete current snapshot: ' + str(log))
        return external

    def stage_log(row, override=None):
        require(row['exit_code'] == 0 and not row.get('timed_out', False), 'Dependency stage did not pass.')
        path = Path(override) if override is not None else Path(row['log'])
        if not path.is_absolute():
            path = ROOT / path
        bound = bind(path, row['log_sha256'])
        require('log_bytes' not in row or bound.stat().st_size == row['log_bytes'], 'Stage log byte count mismatch.')
        return bound

    def strict_commands(stages, module, source, object_path, audit_source):
        require(stages['replay']['command'] == [str(CHECKER), '--verbose', module], f'Unexpected replay command: {module}')
        for label in ['normal', 'audit']:
            command = stages[label]['command']
            require(command[0] == str(LEAN) and
                    all(flag in command for flag in FLAGS),
                    f'Non-strict accepted stage: {module}/{label}')
        normal = stages['normal']['command']
        require(Path(normal[-1]) == source and Path(normal[normal.index('-o') + 1]) == object_path,
                f'Normal command/source/object binding mismatch: {module}')
        require(Path(stages['audit']['command'][-1]) == audit_source, f'Audit source binding mismatch: {module}')

    def copy_dependency(module, original, expected, provenance, companions=None):
        require(module in SOURCES and module not in target_names, f'Refuse a target/unknown dependency object: {module}')
        if module in KNOWN_OBJECTS:
            require(expected == KNOWN_OBJECTS[module], f'Known accepted object identity mismatch: {module}')
        original = bind(original, expected)
        companions = [] if companions is None else companions
        actual_companions = [str(original) + suffix for suffix in ['.private', '.server']
                             if Path(str(original) + suffix).is_file()]
        require(actual_companions == [row['path'] for row in companions],
                f'Project object companion set differs from accepted inventory: {module}')
        for row in companions:
            artifact(row)
        destination = lib / (module.replace('.', '/') + '.olean')
        if module in state['dependency_objects']:
            previous = state['dependency_objects'][module]
            require(previous['sha256'] == expected and digest(destination) == expected,
                    f'Conflicting accepted object provenance: {module}')
            previous_companions = [(Path(row['path']).suffix, row['sha256']) for row in previous['companions']]
            require(previous_companions == [(Path(row['path']).suffix, row['sha256']) for row in companions],
                    f'Conflicting accepted companion provenance: {module}')
            return
        require(not destination.exists(), f'Unexpected preexisting dependency object: {module}')
        shutil.copyfile(original, destination)
        bind(destination, expected)
        copied_companions = []
        for row in companions:
            target = Path(str(destination) + Path(row['path']).suffix)
            require(not target.exists(), f'Unexpected existing companion: {target}')
            shutil.copyfile(row['path'], target)
            bind(target, row['sha256'])
            copied_companions.append(record_file(target))
        state['dependency_objects'][module] = {
            'path': str(original), 'sha256': expected, 'isolated_path': str(destination),
            'source_sha256': SOURCES[module]['source_sha256'], 'provenance': provenance,
            'companions': copied_companions,
        }

    def modern_owner(container, receipt_path, module):
        owner = container['modules'][module]
        require(owner['accepted'] is True and owner['status'] == 'NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED',
                f'Owner not accepted: {module}')
        require(owner['module'] == module and owner['source_origin']['sha256'] == SOURCES[module]['source_sha256'] and
                owner['source_origin']['commit'] == container['publication_commit'] and
                owner['source_origin']['path'] == SOURCES[module]['path'], f'Accepted source-origin binding mismatch: {module}')
        source = artifact(owner['source_copy'], SOURCES[module]['source_sha256'])
        audit_source = artifact(owner['audit_source'])
        required_audit = audit_template.replace(PAYLOAD, module) + (appendix_text if module == SUPPORT else '')
        require(audit_source.read_text() == required_audit, f'Changed complete-audit template: {module}')
        object_path = artifact(owner['object'])
        for label in ['normal', 'replay', 'audit']:
            require(owner['stages'][label]['status'] == 'PASSED', f'Owner stage not marked passed: {module}/{label}')
            stage_log(owner['stages'][label])
        strict_commands(owner['stages'], module, source, object_path, audit_source)
        records, inventory, imports = read_audit(Path(owner['stages']['audit']['log']), module)
        require(records == owner['owned_declarations'] and len(records) == owner['owned_count'] and
                json.loads(artifact(owner['declarations']).read_text()) == records and
                json.loads(artifact(owner['inventory']).read_text()) == inventory and
                owner['actual_project_closure'] == imports, f'Owner inventory/receipt/log mismatch: {module}')
        require(set(SOURCES[module]['public_names']) <= {r['name'] for r in records}, f'Accepted public declarations missing: {module}')
        if module == PAYLOAD:
            require(sorted(r['name'] for r in records) == expected_payload, 'Payload inventory is not exactly all 544 expected names.')
        require_external(owner['stages']['audit']['log'])
        if module == SUPPORT:
            scope = read_private_scope_audit(owner['stages']['audit']['log'], records, expected_private)
            require(json.loads(artifact(owner['private_scoped_simp_interface']).read_text()) == scope,
                    'FieldSimp stored scoped interface differs from actual full-owned audit marker.')
        copy_dependency(module, object_path, owner['object']['sha256'],
                        'Accepted normal/replay/full-owned owner and complete inventory revalidated',
                        owner.get('object_companions', []))
        state['dependency_receipts'][module] = {
            **record_file(receipt_path), 'owner_accepted': True, 'owner_status': owner['status'],
            'owner_publication': owner['source_origin']['commit'], 'owned_count': len(records),
        }

    def legacy_owner(directory, module, receipt_sha):
        receipt_path = bind(directory / 'RESULT.json', receipt_sha)
        receipt = json.loads(receipt_path.read_text())
        require(receipt['accepted'] is True and receipt['status'] == 'NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED' and
                receipt['module'] == module and receipt['source_sha256'] == SOURCES[module]['source_sha256'] and
                receipt['object_sha256'] == KNOWN_OBJECTS[module], f'Legacy accepted owner mismatch: {module}')
        require(hashlib.sha256(receipt['source'].encode()).hexdigest() == SOURCES[module]['source_sha256'],
                f'Legacy embedded source mismatch: {module}')
        source = bind(directory / 'src' / (module.replace('.', '/') + '.lean'), SOURCES[module]['source_sha256'])
        object_path = bind(directory / 'lib' / (module.replace('.', '/') + '.olean'), KNOWN_OBJECTS[module])
        audit_source = bind(directory / 'audit/Audit.lean')
        require(audit_source.read_text() == audit_template.replace(PAYLOAD, module), f'Legacy audit template differs: {module}')
        stages = {label: receipt[label] for label in ['normal', 'replay', 'audit']}
        for label, stage in stages.items():
            stage_log(stage, directory / (label.upper() + '.log'))
        strict_commands(stages, module, source, object_path, audit_source)
        records, _, _ = read_audit(directory / 'AUDIT.log', module)
        require_external(directory / 'AUDIT.log', 2872 if module == JSON_OWNER else EXPECTED_EXTERNAL_COUNT)
        require(records == receipt['owned_declarations'] and len(records) == receipt['owned_count'],
                f'Legacy owned inventory differs from receipt: {module}')
        require(set(SOURCES[module]['public_names']) <= {r['name'] for r in records}, f'Legacy public declarations missing: {module}')
        copy_dependency(module, object_path, KNOWN_OBJECTS[module], 'Exact accepted legacy owner receipt, logs and full inventory revalidated')
        state['dependency_receipts'][module] = record_file(receipt_path)
        return receipt

    def run_stage(owner, label, command, log):
        require(owner['module'] in target_names and label in {'normal', 'replay', 'audit'},
                'Only the four fresh typed-pulling owners may execute compiler gates.')
        context_check()
        start = time.monotonic()
        row = {'command': command, 'status': 'RUNNING', 'started_utc': now(), 'log': str(log)}
        owner['stages'][label] = row
        write()
        print('P25_TYPED_PULLING_STAGE_START', owner['module'], label, flush=True)
        with log.open('wb') as stream:
            process = subprocess.Popen(command, cwd=ROOT, env=env, stdout=stream,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            timed_out = False
            try:
                code = process.wait(timeout=600)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(process.pid, signal.SIGKILL)
                process.wait(timeout=30)
                code = 124
        row.update(status='PASSED' if code == 0 else 'FAILED', exit_code=code, timed_out=timed_out,
                   seconds=round(time.monotonic() - start, 3), ended_utc=now(),
                   log_sha256=digest(log), log_bytes=log.stat().st_size)
        bind(log, row['log_sha256'])
        state['frozen_inputs'] = dict(frozen)
        write()
        print('P25_TYPED_PULLING_STAGE_RESULT', owner['module'], label,
              json.dumps({k: row[k] for k in ['exit_code', 'timed_out', 'seconds', 'log_bytes', 'log_sha256']}), flush=True)
        if code:
            owner['status'] = label.upper() + '_FAILED'
            state.update(status='MODULE_STAGE_FAILED', failed_module=owner['module'], failed_stage=label)
            write()
            with log.open('rb') as stream:
                stream.seek(max(0, log.stat().st_size - 1800))
                print(stream.read().decode(errors='replace'), flush=True)
            raise RuntimeError(f'{owner["module"]} {label} failed with exit {code}.')
        context_check()

