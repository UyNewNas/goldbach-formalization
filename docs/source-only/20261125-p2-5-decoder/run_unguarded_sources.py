#!/usr/bin/env python3
"""Validate only the four saving16 unguarded source owners in the fixed P3 root.

The caller first publishes and fetches the exact candidate commit. This script
advances only the existing task worktree, installs no sources or dependencies,
and uses the original compile/replay/full-owned gates. The original input owner
must actually compile under this attempt's fourteen-file physical snapshot.
No FiniteArchive guard, String equality, parse or numerical checker is run.
"""
import argparse
import datetime
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path('/workspace/p25-q96-20261125')
PREVIOUS_COMMIT = '0669b915c59927248eff8bb60d6850dfed74e950'
BASELINE = Path('/workspace/p25-q96-baseline-8657')
BASELINE_COMMIT = '8657cfffef159185f73c6a04ae4d31c846c0d0a9'
PACKAGE = 'docs/source-only/20261125-p2-5-decoder'
RUNNER_PATH = PACKAGE + '/run_unguarded_sources.py'
SOURCE_MAP_PATH = PACKAGE + '/SOURCE_CLOSURE.json'
ATTEMPT = '.lake/p25-unguarded-sources/attempt001'
MANIFEST_PATH = 'docs/verification/20261125-p2-5-saving16/Q96_EXISTING_INPUTS_AND_SOURCES.json'
MANIFEST_SHA256 = '79404a0f8ed17c2d49fd377363a5169936628ff88e8e7fdd6d5165c8c6a917e0'
MATHLIB = Path('/mathlib')
MATHLIB_ALIAS = Path('/workspace/compile-deps/mathlib')
MATHLIB_PIN = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
LEAN_COMMIT = '62eed1db4d67327ec8120be05f1a1b0847d74561'
LEAN = Path('/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean')
CHECKER = LEAN.with_name('leanchecker')
LEAN_SHA256 = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
CHECKER_SHA256 = 'ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a'
PROJECT_LIB = ROOT / '.lake/p2-private/lib'
MATHLIB_PATHS = ['/mathlib/.lake/build/lib/lean'] + [
    f'/mathlib/.lake/packages/{p}/.lake/build/lib/lean'
    for p in ['plausible', 'LeanSearchClient', 'importGraph', 'proofwidgets', 'aesop', 'Qq', 'batteries']
]
STRICT_FLAGS = ['-t0', '-j1', '-M11264', '-DwarningAsError=true',
                '-DmaxRecDepth=50000', '-DmaxHeartbeats=40000000']
COMPILE_START_BUDGET_SECONDS = 1000
INPUT_MODULE = 'ImbalancedChen.P2OriginalSaving16OriginalInput'
DECODER_MODULE = 'ImbalancedChen.P2OriginalSaving16Decoder'
MODULES = ['ImbalancedChen.P2OriginalSaving16Q96FloorCore',
           'ImbalancedChen.P2OriginalSaving19SourceJson', INPUT_MODULE, DECODER_MODULE]
NEW_MODULES = [INPUT_MODULE, DECODER_MODULE]
FINITE_PATH = 'ImbalancedChen/P2OriginalSaving16FiniteArchive.lean'
PREVIOUS_FINITE_SHA256 = '72824a189dd65b29f0f340918ff867a1e905959e8e60e683a797226923d7e01d'
MODULE_SHA256 = {
    MODULES[0]: '9a456807e6c3a167fd12c1c6e5db492d6c54fd700a1de122ea492774f697c778',
    MODULES[1]: 'd58e22ba7e2d92b6c9f2d139993361ae9b827d25d6869fcf38f3837ba7bc3d02',
    INPUT_MODULE: '792a5adf50263cfc1a0f67fb3d088c7612910388e4d1fa65db45c3c50065aca5',
    DECODER_MODULE: 'e1b23e3de928a97c411d1c6aa73f2059b204d7b9f297105edcd591916b9aee80',
}
DEPENDENCIES = {
    MODULES[1]: {
        'source_sha256': MODULE_SHA256[MODULES[1]],
        'object_sha256': '50b1caec038208d3becd6cbef3a318b1d2966add295c060ad28d8999e1aa64e7',
        'closure_signature': 'a10f02a0c330018bbe871da38adf5fb2f88b4c7d0a7994bf334ae8e4701e1f20',
        'owned_declarations': 122,
    },
    MODULES[0]: {
        'source_sha256': MODULE_SHA256[MODULES[0]],
        'object_sha256': '720df453f67d6650c195b737357d87aafb511b10a87dbf8654ae2fc6d9e712b9',
        'closure_signature': 'b6b656dea45d9be757d6aed80b3fbb6275b0935824e538056f14066a2d775597',
        'owned_declarations': 1,
    },
}
SOURCE_OVERLAYS = {
    INPUT_MODULE: 'docs/source-only/20261125-p2-5-original-input/postimages/ImbalancedChen/P2OriginalSaving16OriginalInput.lean',
    DECODER_MODULE: PACKAGE + '/after/ImbalancedChen/P2OriginalSaving16Decoder.lean',
}
PINS = {
    SOURCE_MAP_PATH: 'ba7b651154e3829cceff6058c48630b33fadaabad716b1e038add1b54c97edc0',
    PACKAGE + '/DECLARATION_IDENTITY.json': 'bcc7635af4b07cbe47d9376d8dbd0214eda8baa885b4643bde5cd5b1f6437dbd',
    PACKAGE + '/SOURCE_SELECTION.json': '13b5d772e069429767ba6f673e077e17c6dfc41cfd8f20ca4a7effb2c2e50d75',
    MANIFEST_PATH: MANIFEST_SHA256,
    'verification/part2/run_winner9_private_checks.py': 'f7816db16309f99b6f3babbe128425c06818b3da1dec556dffffe5e8132a6314',
    'verification/part2/run_winner9_private_audit.py': '571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5',
    'verification/part2/winner9_private_audit_template.lean': '2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b',
    'verification/part2/inspect_winner9_owner_native.py': '28fbce08aa1adcc379ee592eda3760d2465b27e784cc735497d35b3658c9e464',
    'verification/part2/winner9_external_snapshot.py': 'a57b658beef42ebfe75ccb09d84f7f1ee7252c289f267396063c93ae5e0bbedf',
    FINITE_PATH: '9db41aa0553a3c5020acceffa3f1bc91529f1382f7dc6c6d57ba96c073e6d627',
    PACKAGE + '/after/' + FINITE_PATH: '9db41aa0553a3c5020acceffa3f1bc91529f1382f7dc6c6d57ba96c073e6d627',
}
for _module, _expected in MODULE_SHA256.items():
    PINS[_module.replace('.', '/') + '.lean'] = _expected
for _module, _overlay in SOURCE_OVERLAYS.items():
    PINS[_overlay] = MODULE_SHA256[_module]

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def digest_bytes(value):
    return hashlib.sha256(value).hexdigest()

def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()

def output(args, cwd=None):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()

def utc_now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def saved(path, value):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)

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

def dependency_snapshot():
    records_path = ROOT / ".lake/p2-private/records.json"
    records = json.loads(records_path.read_text())
    result = {}
    for module, expected in DEPENDENCIES.items():
        source = ROOT / (module.replace(".", "/") + ".lean")
        obj = PROJECT_LIB / (module.replace(".", "/") + ".olean")
        receipt_path = ROOT / ".lake/p2-private/audit" / module / "latest.json"
        receipt = json.loads(receipt_path.read_text())
        record = records.get(module, {})
        require(digest(source) == expected["source_sha256"], "Dependency source differs: " + module)
        require(digest(obj) == expected["object_sha256"], "Dependency object differs: " + module)
        require(record.get("exit_code") == 0 and record.get("source_sha256") == expected["source_sha256"]
                and record.get("object_sha256") == expected["object_sha256"]
                and record.get("closure_signature") == expected["closure_signature"]
                and record.get("deps") == {}, "Dependency compile record is not the accepted exact object: " + module)
        require(receipt.get("accepted") is True and receipt.get("module") == module
                and receipt.get("source_sha256") == expected["source_sha256"]
                and receipt.get("object_sha256") == expected["object_sha256"]
                and receipt.get("compile_closure_signature") == expected["closure_signature"],
                "Dependency accepted receipt differs: " + module)
        for phase in ["replay", "audit"]:
            require(receipt.get(phase, {}).get("exit_code") == 0
                    and receipt.get(phase, {}).get("inputs_unchanged") is True,
                    "Dependency " + phase + " did not pass: " + module)
        require(receipt["audit"].get("declaration_count") == expected["owned_declarations"],
                "Dependency full-owned declaration count differs: " + module)
        result[module] = {
            "source": str(source), "source_sha256": digest(source),
            "object": str(obj), "object_sha256": digest(obj),
            "compile_record": record, "receipt_path": str(receipt_path),
            "receipt_sha256": digest(receipt_path), "receipt": receipt,
        }
    return result

def file_identity(path):
    path = Path(path)
    st = path.stat()
    return {'path': str(path), 'realpath': str(path.resolve()), 'bytes': st.st_size,
            'sha256': digest(path), 'device': st.st_dev, 'inode': st.st_ino,
            'mtime_ns': st.st_mtime_ns, 'ctime_ns': st.st_ctime_ns}


def frozen_context(publication):
    files = {}
    for relative, expected in PINS.items():
        item = file_identity(ROOT / relative)
        require(item['sha256'] == expected, 'Pinned source/gate differs: ' + relative)
        files[relative] = item
    require(digest(LEAN) == LEAN_SHA256 and digest(CHECKER) == CHECKER_SHA256,
            'Compiler/checker binary differs')
    require(MATHLIB_ALIAS.resolve() == MATHLIB.resolve(), 'Mathlib alias differs')
    require(output(['git', 'rev-parse', 'HEAD'], MATHLIB) == MATHLIB_PIN, 'Mathlib pin differs')
    require(output(['git', 'rev-parse', 'HEAD'], ROOT) == publication, 'Publication HEAD changed')
    require(not output(['git', 'status', '--porcelain', '--untracked-files=no'], ROOT),
            'Tracked source changed')
    require(output(['git', 'rev-parse', 'HEAD'], BASELINE) == BASELINE_COMMIT,
            'Empty baseline HEAD changed')
    require(not output(['git', 'status', '--porcelain', '--untracked-files=no'], BASELINE),
            'Empty baseline tracked source changed')
    require(not (BASELINE / '.lake/build/lib/lean').exists(), 'Empty baseline gained objects')
    return {'files': files, 'lean': file_identity(LEAN), 'leanchecker': file_identity(CHECKER),
            'mathlib_pin': MATHLIB_PIN, 'mathlib_realpath': str(MATHLIB_ALIAS.resolve()),
            'baseline_commit': BASELINE_COMMIT, 'source_commit': publication}


def object_snapshot():
    result = {}
    for module in MODULES:
        path = PROJECT_LIB / (module.replace('.', '/') + '.olean')
        result[module] = file_identity(path) if path.is_file() else None
    return result


def record_snapshot():
    path = ROOT / '.lake/p2-private/records.json'
    records = json.loads(path.read_text())
    return {module: records.get(module) for module in MODULES}


def run_driver(command, log_path, environment, state, receipt_path, stage):
    started = time.monotonic()
    result = {'command': command, 'started_utc': utc_now(), 'log': str(log_path),
              'exact_START_modules': []}
    state[stage] = result
    saved(receipt_path, state)
    with log_path.open('w') as log:
        proc = subprocess.Popen(command, cwd=ROOT, env=environment, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True)
        require(proc.stdout is not None, 'Missing driver output stream')
        for line in proc.stdout:
            log.write(line)
            log.flush()
            print(line, end='', flush=True)
            if stage == 'normal':
                for module in MODULES:
                    if line.rstrip('\r\n') == 'START ' + module and module not in result['exact_START_modules']:
                        result['exact_START_modules'].append(module)
                        saved(receipt_path, state)
        result['exit_code'] = proc.wait()
    result['seconds'] = round(time.monotonic() - started, 3)
    result['log_sha256'] = digest(log_path)
    saved(receipt_path, state)
    return result


def verify_source_map():
    graph = json.loads((ROOT / SOURCE_MAP_PATH).read_text())['unguarded_two_root_closure']
    require(graph['project_module_count'] == 4 and set(graph['modules']) == set(MODULES),
            'Expected only the four unguarded modules')
    require(set(graph['roots']) == set(NEW_MODULES) and graph['FiniteArchive_imported'] is False,
            'Unexpected roots or guarded owner in the selected closure')
    require(not graph['missing_project_imports'] and not graph['cycles'], 'Invalid fixed source closure')
    for module, row in graph['modules'].items():
        production = ROOT / (module.replace('.', '/') + '.lean')
        require(row['sha256'] == MODULE_SHA256[module] and digest(production) == row['sha256'],
                'Published production source differs: ' + module)
        require(production.read_bytes() == (ROOT / row['path']).read_bytes(),
                'Production and selected source-only postimage differ: ' + module)
        actual_imports = re.findall(r'^import\s+([^\s]+)\s*$', production.read_text(), re.MULTILINE)
        require(actual_imports == row['imports'], 'Selected import list differs: ' + module)
        project_imports = {name for name in actual_imports if name.startswith('ImbalancedChen.')}
        require(project_imports <= set(MODULES), 'Guarded or unrelated project import: ' + module)
    return graph


def fresh_record(module, record, obj, started):
    expected_command = [str(LEAN), *STRICT_FLAGS, '-o',
                        str(PROJECT_LIB / (module.replace('.', '/') + '.olean')),
                        module.replace('.', '/') + '.lean']
    return bool(module in started and record and obj and record.get('exit_code') == 0
                and record.get('new_strict_compile') is True
                and record.get('source_sha256') == MODULE_SHA256[module]
                and record.get('object_sha256') == obj['sha256']
                and record.get('command') == expected_command)


def main():
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument('publication_commit', help='One already-fetched full publication commit')
    options = args.parse_args()
    if not ROOT.is_dir():
        print('P25_UNGUARDED_ERROR fixed existing root is missing', file=sys.stderr)
        return 1
    out = ROOT / ATTEMPT
    if out.exists():
        print('P25_UNGUARDED_ERROR preserve existing attempt: ' + str(out), file=sys.stderr)
        return 1
    out.mkdir(parents=True)
    receipt_path = out / 'RUN_RESULT.json'
    rows = None
    before = None
    context = None
    objects_after_compile = None
    records_after_compile = None
    state = {'schema': 'p25-unguarded-original-input-decoder-bound-validation-v1',
             'status': 'PREPARING', 'accepted': False, 'started_utc': utc_now(),
             'publication_commit': options.publication_commit, 'previous_commit': PREVIOUS_COMMIT,
             'runner_path': str(Path(__file__).resolve()), 'runner_sha256': digest(__file__),
             'modules': MODULES, 'source_map': SOURCE_MAP_PATH, 'strict_flags': STRICT_FLAGS,
             'scope': 'Only the four unguarded source owners: fresh original text embedding, decoder definitions, and their accepted floor/parser prerequisites.',
             'original_input_fresh_data_to_object_bound': False,
             'FiniteArchive_imported': False, 'finite_guards_started': False,
             'String_equality_proved': False, 'parse_success_proved': False,
             'decode_success_proved': False, 'Q96_proved': False, 'P2_5_proved': False,
             'read_window_condition': 'No task subprocess writes the original input directory or files. Before/after physical identities and hashes use the existing task-owned no-out-of-band-write window.',
             'replay_boundary': 'The independent checker reads embedded literals from bound objects; it does not reread JSON. No finite guard or success theorem is claimed.'}
    saved(receipt_path, state)
    try:
        publication = options.publication_commit
        require(len(publication) == 40 and all(c in '0123456789abcdef' for c in publication),
                'Expected one full publication commit')
        require(output(['git', 'rev-parse', 'HEAD'], ROOT) == PREVIOUS_COMMIT,
                'Fixed root must still be at the authorized previous commit')
        require(not output(['git', 'status', '--porcelain', '--untracked-files=no'], ROOT),
                'Tracked root must be clean before any advance')
        require(digest(ROOT / FINITE_PATH) == PREVIOUS_FINITE_SHA256,
                'Previous guarded owner is not the unchanged historical source')
        subprocess.check_call(['git', 'cat-file', '-e', publication + '^{commit}'], cwd=ROOT)
        subprocess.check_call(['git', 'merge-base', '--is-ancestor', PREVIOUS_COMMIT, publication], cwd=ROOT)
        def published(path):
            return subprocess.check_output(['git', 'show', publication + ':' + path], cwd=ROOT)
        require(Path(__file__).read_bytes() == published(RUNNER_PATH),
                'Executing runner differs from the publication')
        for path, expected in PINS.items():
            require(digest_bytes(published(path)) == expected, 'Published source/gate pin differs: ' + path)
        require(digest(LEAN) == LEAN_SHA256 and digest(CHECKER) == CHECKER_SHA256,
                'Pinned Lean/checker binary differs')
        version = output([str(LEAN), '--version'])
        require('4.33.0-rc1' in version and LEAN_COMMIT in version, 'Lean version differs')
        require(output(['git', 'rev-parse', 'HEAD'], MATHLIB) == MATHLIB_PIN, 'Mathlib pin differs')
        require(MATHLIB_ALIAS.resolve() == MATHLIB.resolve(), 'Existing Mathlib alias differs')
        require(all(Path(path).is_dir() for path in MATHLIB_PATHS), 'Approved Mathlib library path is missing')
        require(output(['git', 'rev-parse', 'HEAD'], BASELINE) == BASELINE_COMMIT, 'Empty baseline differs')
        require(not output(['git', 'status', '--porcelain', '--untracked-files=no'], BASELINE),
                'Empty baseline is dirty')
        require(not (BASELINE / '.lake/build/lib/lean').exists(), 'Empty baseline has objects')
        require(digest(ROOT / MANIFEST_PATH) == MANIFEST_SHA256, 'Original input manifest differs')
        rows = json.loads((ROOT / MANIFEST_PATH).read_text())['saving16_inputs']
        before = input_snapshot(rows)
        state['input_snapshot_before_advance'] = before
        saved(receipt_path, state)
        require(before['all_inputs_match_manifest'], 'Original fourteen inputs failed the saved snapshot')
        dependencies = dependency_snapshot()
        state['accepted_dependencies_before'] = dependencies
        toolchain = {'lean_version': version, 'lean_binary_sha256': LEAN_SHA256, 'mathlib_commit': MATHLIB_PIN}
        for module, row in dependencies.items():
            require(row['compile_record'].get('toolchain') == toolchain
                    and row['compile_record'].get('cache_schema') == 2,
                    'Accepted dependency has another compiler context: ' + module)
        records_path = ROOT / '.lake/p2-private/records.json'
        prior_bytes = records_path.read_bytes()
        prior = json.loads(prior_bytes)
        old_input = prior.get(INPUT_MODULE, {})
        require(old_input.get('exit_code') != 0 or old_input.get('source_sha256') != MODULE_SHA256[INPUT_MODULE],
                'OriginalInput has a successful current-source record; inspect its input-bound receipt before reuse')
        backup = out / 'previous-records.json.gz'
        backup.write_bytes(gzip.compress(prior_bytes, mtime=0))
        state['previous_records'] = {'path': str(records_path), 'bytes': len(prior_bytes),
                                     'sha256': digest_bytes(prior_bytes), 'backup': str(backup),
                                     'backup_sha256': digest(backup),
                                     'selected_records': {module: prior.get(module) for module in MODULES}}
        state['status'] = 'ADVANCING_ONLY_FIXED_TASK_WORKTREE'
        saved(receipt_path, state)
        subprocess.check_call(['git', 'checkout', '--detach', publication], cwd=ROOT)
        state['source_tree'] = output(['git', 'rev-parse', 'HEAD^{tree}'], ROOT)
        state['selected_four_module_graph'] = verify_source_map()
        context = frozen_context(publication)
        state['frozen_context_before'] = context
        require(input_snapshot(rows) == before, 'Inputs changed during source advancement')
        require(dependency_snapshot() == dependencies, 'Accepted dependency changed during source advancement')
        for module in NEW_MODULES:
            relative = module.replace('.', '/') + '.lean'
            copy = out / 'sources' / relative
            copy.parent.mkdir(parents=True, exist_ok=True)
            copy.write_bytes((ROOT / relative).read_bytes())
        environment = dict(os.environ)
        environment['LEAN_PATH'] = ':'.join(MATHLIB_PATHS)
        environment['LEAN_SYSROOT'] = str(LEAN.parent.parent)
        environment.pop('LEAN_SRC_PATH', None)
        state['approved_LEAN_PATH'] = environment['LEAN_PATH']
        state['LEAN_SYSROOT'] = environment['LEAN_SYSROOT']
        state['status'] = 'NORMAL_COMPILE_RUNNING'
        command = [sys.executable, 'verification/part2/run_winner9_private_checks.py', *MODULES,
                   '--baseline-root', str(BASELINE), '--workers', '1', '--threads', '1',
                   '--memory-mb', '11264', '--time-budget-seconds', str(COMPILE_START_BUDGET_SECONDS)]
        normal = run_driver(command, out / 'NORMAL_DRIVER.log', environment, state, receipt_path, 'normal')
        after_compile = input_snapshot(rows)
        state['input_snapshot_after_compile'] = after_compile
        state['frozen_context_after_compile'] = frozen_context(publication)
        records_after_compile = record_snapshot()
        objects_after_compile = object_snapshot()
        state['compile_records'] = records_after_compile
        state['compiled_objects'] = objects_after_compile
        state['fresh_compilation'] = {
            module: fresh_record(module, records_after_compile[module], objects_after_compile[module],
                                 normal['exact_START_modules']) for module in NEW_MODULES}
        unchanged = after_compile == before and state['frozen_context_after_compile'] == context
        state['original_input_fresh_data_to_object_bound'] = bool(unchanged and state['fresh_compilation'][INPUT_MODULE])
        saved(receipt_path, state)
        require(unchanged, 'Source/input/gate/compiler context changed during compilation')
        require(dependency_snapshot() == dependencies, 'Accepted prerequisites changed during compilation')
        require(not set(normal['exact_START_modules']) & set(DEPENDENCIES),
                'Accepted prerequisites were unexpectedly recompiled; no reuse credit')
        # Keep normal compilation and full-owned audit separate, as in the parent
        # finite runner. Failed records are rejected by the unchanged audit driver.
        state['status'] = 'INDEPENDENT_REPLAY_AND_FULL_OWNED_AUDIT_RUNNING'
        summary_name = 'p25-unguarded-input-decoder-attempt001-owned.json'
        command = [sys.executable, 'verification/part2/run_winner9_private_audit.py', *MODULES,
                   '--summary-name', summary_name, '--memory-mb', '11264']
        audit = run_driver(command, out / 'AUDIT_DRIVER.log', environment, state, receipt_path, 'audit')
        summary_path = ROOT / '.lake/p2-private/audit' / summary_name
        summary = json.loads(summary_path.read_text()) if summary_path.is_file() else None
        state['audit_summary'] = summary
        state['audit_summary_sha256'] = digest(summary_path) if summary_path.is_file() else None
        state['owned_receipts'] = {}
        for module in MODULES:
            path = ROOT / '.lake/p2-private/audit' / module / 'latest.json'
            if path.is_file():
                content = json.loads(path.read_text())
                state['owned_receipts'][module] = {'path': str(path), 'sha256': digest(path), 'receipt': content}
        final_input = input_snapshot(rows)
        final_context = frozen_context(publication)
        final_records = record_snapshot()
        final_objects = object_snapshot()
        state.update(input_snapshot_after_audit=final_input, frozen_context_after_audit=final_context,
                     records_after_audit=final_records, objects_after_audit=final_objects,
                     records_file_sha256_after=digest(records_path))
        state['inputs_unchanged'] = final_input == before
        state['sources_gates_toolchain_unchanged'] = final_context == context
        state['records_objects_unchanged_during_audit'] = (final_records == records_after_compile
                                                         and final_objects == objects_after_compile)
        require(dependency_snapshot() == dependencies, 'Accepted prerequisites changed during audit')
        exact_summary = bool(summary and summary.get('requested') == 4
                             and set(summary.get('modules', {})) == set(MODULES)
                             and summary.get('all_accepted') is True)
        owned_match = all(
            state['owned_receipts'].get(module, {}).get('receipt', {}).get('accepted') is True
            and state['owned_receipts'][module]['receipt'].get('source_sha256') == MODULE_SHA256[module]
            and final_objects[module] is not None
            and state['owned_receipts'][module]['receipt'].get('object_sha256') == final_objects[module]['sha256']
            for module in MODULES)
        state['accepted'] = bool(normal['exit_code'] == audit['exit_code'] == 0
                                 and state['original_input_fresh_data_to_object_bound']
                                 and state['inputs_unchanged'] and state['sources_gates_toolchain_unchanged']
                                 and state['records_objects_unchanged_during_audit']
                                 and exact_summary and owned_match)
        state['status'] = ('UNGUARDED_SOURCE_OBJECTS_AND_OWNED_AUDITS_ACCEPTED' if state['accepted']
                           else 'UNGUARDED_SOURCE_VALIDATION_INCOMPLETE_OR_FAILED')
    except (OSError, ValueError, RuntimeError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        state['accepted'] = False
        state['status'] = 'ERROR_NOT_ACCEPTED'
        state['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        if rows is not None:
            state['final_input_snapshot'] = input_snapshot(rows)
            if before is not None and state['final_input_snapshot'] != before:
                state['accepted'] = False
                state['status'] = 'FINAL_INPUT_IDENTITY_MISMATCH_NOT_ACCEPTED'
        state['ended_utc'] = utc_now()
        saved(receipt_path, state)
    print('P25_UNGUARDED_RESULT ' + json.dumps({
        'status': state['status'], 'accepted': state['accepted'],
        'publication_commit': state['publication_commit'],
        'normal_exit': state.get('normal', {}).get('exit_code'),
        'audit_exit': state.get('audit', {}).get('exit_code'),
        'original_input_fresh_data_to_object_bound': state['original_input_fresh_data_to_object_bound'],
        'P2_5_proved': False, 'error': state.get('error'),
    }), flush=True)
    print('P25_UNGUARDED_RECEIPT ' + str(receipt_path) + ' ' + digest(receipt_path), flush=True)
    return 0 if state['accepted'] else 1


if __name__ == '__main__':
    sys.exit(main())
