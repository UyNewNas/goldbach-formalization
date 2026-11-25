#!/usr/bin/env python3
"""Prepare a transferable three-gate receipt for the unchanged FastDet owner.

Usage: python3 run_p1_fastdet_cloud.py MATERIALIZED_SOURCE PUBLICATION_SHA SOURCE_SHA

The caller transports the exact published source. This process checks its bytes
against the frozen source hash, but makes no remote checkout or remote Git-object
inspection claim. It creates only a fresh /workspace/p25-fastdet-20261126 root.
It never compiles a project dependency or changes the determinant algorithm.
"""
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
import tarfile
import time
import traceback


ROOT = Path('/workspace/p25-fastdet-20261126')
MODULE = 'ImbalancedChen.P2Winner9FastDetPure'
SOURCE_PATH = 'docs/source-only/20261126-p2-5-cell00-row00-arithmetic/ImbalancedChen/P2Winner9FastDetPure.lean'
SOURCE_SHA = 'd1a0d2ae8af1cf90e05af11b983c5c41ea97a42387eb6c6b9c32ff176e2258ac'
SOURCE_BYTES = 6729
HISTORICAL_OBJECT_SHA = 'abd3a41b786826af3d608a50de7096dda26fe7034970340789063647b88bd64c'
LEAN = Path('/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean')
CHECKER = LEAN.with_name('leanchecker')
TOOLCHAIN_ROOT = LEAN.parent.parent
LEAN_COMMIT = '62eed1db4d67327ec8120be05f1a1b0847d74561'
MATHLIB = Path('/workspace/blue-member-build/.lake/packages/mathlib')
MATHLIB_PIN = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
MANIFEST_SHA = '951d5f6dcfce202878cd5b103157bd0ceba69510955db6e11db4183fd866a911'
PACKAGE_PINS = {
    'plausible': 'b1c4a69a7e247ab7df20460212001673d74f08c0',
    'LeanSearchClient': '0498c7c070c143a3bf7379f4d99a2c63bb9d9715',
    'importGraph': '18a90119a5d316358fde6c86e0ca24e59212e32c',
    'proofwidgets': 'b1436dc749e722c9920036b52cdc43b3451d0b69',
    'aesop': '57d3325be72a842920813bcb40f96a6f7393c185',
    'Qq': 'ee41917ae11d38479fb8fb24745f7ca4bf0a784d',
    'batteries': '41bd267b3f6b7252f6676af46d4ffc6783b64de9',
    'Cli': 'da07ca808b6718cb2aed14dba154e5a08b8f8ecf',
}
DIRECT_IMPORTS = [
    'Mathlib.LinearAlgebra.Matrix.Determinant.Basic',
    'Mathlib.Data.Rat.Defs',
    'Mathlib.Tactic.NormNum',
    'Mathlib.Tactic.Ring',
]
FLAGS = ['-t0', '-j1', '-M11264', '-DwarningAsError=true',
         '-DmaxRecDepth=1000000', '-DmaxHeartbeats=80000000']
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
AUDIT_TEMPLATE_SHA = 'cd452bddeee765b82187f03893cddb5f7136e3420591f0ea00c9bfe1028f670a'
AUDIT_SOURCE = 'import ImbalancedChen.P2Winner9FastDetPure\nimport Lean.Util.CollectAxioms\nset_option pp.all true\nset_option pp.proofs true\nset_option pp.deepTerms true\nset_option pp.universes true\nset_option pp.explicit true\nset_option pp.fullNames true\nset_option pp.privateNames true\nset_option pp.maxSteps 1000000\nopen Lean Elab Command in\nrun_cmd do\n  let env ← getEnv\n  liftIO <| IO.println s!"P0_QUEUE_IMPORTS {(toJson (env.header.moduleNames.map Name.toString)).compress}"\n  let moduleName := `ImbalancedChen.P2Winner9FastDetPure\n  let some idx := env.getModuleIdx? moduleName | throwError "Missing target module"\n  let names := env.const2ModIdx.fold (init := (#[] : Array Name)) fun ns n i =>\n    if i == idx && (env.find? n).isSome then ns.push n else ns\n  let mut serialized : Array Name := #[]\n  let mut found := false\n  for i in List.range env.header.modules.size do\n    let imported := env.header.modules[i]!\n    if imported.module == moduleName then\n      if found then throwError "Duplicate module"\n      found := true\n      let data := env.header.moduleData[i]!\n      if data.isModule || !imported.importAll || !imported.hasData then\n        throwError "Incomplete imported legacy data"\n      serialized := data.constNames\n  unless found && names.size > 0 && names.qsort Name.lt == serialized.qsort Name.lt do\n    throwError "Complete serialized/environment inventory mismatch"\n  liftIO <| IO.println s!"P0_QUEUE_INVENTORY {(Json.mkObj [("module", toJson moduleName.toString), ("serialized", toJson (serialized.map Name.toString)), ("environment", toJson (names.map Name.toString))]).compress}"\n  for name in names.qsort Name.lt do\n    let some info := env.find? name | throwError "Missing inventoried declaration"\n    if info.isUnsafe || info.isPartial || info.isAxiom then throwError "Unsafe/partial/axiom target"\n    let axioms ← collectAxioms name\n    for ax in axioms do\n      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do\n        throwError "Forbidden transitive axiom {ax}"\n    let type ← liftTermElabM do return (← Meta.ppExpr info.type).pretty\n    if type.contains \'⋯\' then throwError "Truncated type"\n    let record := Json.mkObj [("name", toJson name.toString), ("module", toJson moduleName.toString),\n      ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial), ("axiom", toJson info.isAxiom),\n      ("type", toJson type), ("axioms", toJson (axioms.map Name.toString))]\n    liftIO <| IO.println s!"P0_QUEUE_DECL {record.compress}"\n\n'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def now():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def record(path, relative=True):
    path = Path(path)
    name = str(path.relative_to(ROOT)) if relative else str(path)
    return {'path': name, 'bytes': path.stat().st_size, 'sha256': digest(path)}


def save_json(path, value):
    path = Path(path)
    tmp = path.with_name(path.name + '.tmp')
    tmp.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')
    tmp.replace(path)


def checked_output(command, cwd=ROOT):
    env = os.environ.copy()
    env['GIT_OPTIONAL_LOCKS'] = '0'
    return subprocess.check_output(command, cwd=cwd, env=env, timeout=60,
                                   stderr=subprocess.STDOUT).decode().strip()


def git_pin(path, expected):
    actual = checked_output(['git', 'rev-parse', 'HEAD'], cwd=path)
    require(actual == expected, f'Source revision mismatch at {path}: {actual}')
    # Read-only tracked-worktree checks; no refresh, checkout, reset or fetch.
    for args in [['diff', '--no-ext-diff', '--quiet'],
                 ['diff', '--no-ext-diff', '--cached', '--quiet']]:
        env = os.environ.copy()
        env['GIT_OPTIONAL_LOCKS'] = '0'
        result = subprocess.run(['git', *args], cwd=path, env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
        require(result.returncode == 0, f'Tracked source changes at {path}')
    return actual


def parse_audit(log):
    lines = log.read_text().splitlines()
    declarations = [json.loads(x.removeprefix('P0_QUEUE_DECL '))
                    for x in lines if x.startswith('P0_QUEUE_DECL ')]
    inventories = [json.loads(x.removeprefix('P0_QUEUE_INVENTORY '))
                   for x in lines if x.startswith('P0_QUEUE_INVENTORY ')]
    import_sets = [json.loads(x.removeprefix('P0_QUEUE_IMPORTS '))
                   for x in lines if x.startswith('P0_QUEUE_IMPORTS ')]
    require(len(inventories) == len(import_sets) == 1,
            'Missing or duplicate complete-owned inventory/import list.')
    inventory, imports = inventories[0], import_sets[0]
    names = sorted(d['name'] for d in declarations)
    require(inventory['module'] == MODULE and names and len(names) == len(set(names))
            and names == sorted(inventory['serialized']) == sorted(inventory['environment']),
            'Serialized/environment/declaration inventory differs.')
    require(all(d['module'] == MODULE and not any(d[k] for k in ['unsafe', 'partial', 'axiom'])
                and set(d['axioms']) <= ALLOWED_AXIOMS for d in declarations),
            'Unsafe, partial, axiom declaration or forbidden transitive axiom.')
    require({MODULE + '.fastDet', MODULE + '.fastDet_eq'} <= set(names),
            'Public determinant definition or correctness theorem missing.')
    require(len(imports) == len(set(imports)), 'Duplicate imported module names.')
    project = sorted(x for x in imports if x.startswith('ImbalancedChen.'))
    require(project == [MODULE], 'Unexpected project import in determinant audit.')
    require(set(DIRECT_IMPORTS) <= set(imports), 'Direct external imports missing from environment.')
    return declarations, inventory, imports


def main():
    require(len(sys.argv) == 4, 'Pass materialized source path, full publication SHA, and source SHA.')
    input_path = Path(sys.argv[1]).resolve(strict=True)
    publication, source_sha = sys.argv[2:]
    require(re.fullmatch(r'[0-9a-f]{40}', publication), 'Publication must be a lowercase full Git SHA.')
    require(source_sha == SOURCE_SHA, 'Caller source hash differs from frozen unchanged source.')
    require(input_path.is_file() and input_path.stat().st_size == SOURCE_BYTES
            and digest(input_path) == SOURCE_SHA, 'Transported source bytes differ from frozen source.')
    require(not ROOT.exists() and not ROOT.is_symlink(), 'Preserve existing attempt: dedicated root already exists.')
    ROOT.mkdir()
    state = {
        'schema': 'p25-p1-fastdet-strict-v1', 'module': MODULE,
        'status': 'PREFLIGHT', 'accepted': False, 'started_utc': now(),
        'publication_commit': publication, 'capsule_root': str(ROOT),
        'receipt_path_convention': 'capsule-relative; runtime and source-origin fields explicitly external',
        'strict_flags': FLAGS, 'stage_wall_limit_seconds': 600, 'stages': {},
        'dependency_modules_compiled': [], 'required_owned_names': [MODULE + '.fastDet', MODULE + '.fastDet_eq'],
        'direct_imports': DIRECT_IMPORTS, 'expected_project_closure': [MODULE],
        'allowed_transitive_axioms': sorted(ALLOWED_AXIOMS),
        'host_correctness_credit': False, 'remote_checkout_performed': False,
        'remote_git_object_inspection_performed': False,
        'scope': {'unchanged_generic_determinant_owner': True, 'cell00_row00_arithmetic_proved': False,
                  'geometric_jensen_binding_proved': False, 'Q96_proved': False, 'P2_5_proved': False},
    }
    frozen = {}

    def write():
        save_json(ROOT / 'RESULT.json', state)

    def freeze(path):
        path = Path(path)
        require(path.is_file(), f'Missing frozen file: {path}')
        value = digest(path)
        require(str(path) not in frozen or frozen[str(path)] == value, f'Frozen file changed: {path}')
        frozen[str(path)] = value
        return value

    def check_frozen():
        for path, sha in frozen.items():
            require(Path(path).is_file() and digest(path) == sha, f'Frozen file changed: {path}')

    def stage(label, command, env):
        check_frozen()
        path = ROOT / 'logs' / (label.upper() + '.log')
        entry = {'command': command, 'cwd': str(ROOT), 'status': 'RUNNING',
                 'started_utc': now(), 'log': str(path.relative_to(ROOT)), 'wall_limit_seconds': 600}
        state['stages'][label] = entry
        write()
        print('P25_P1_FASTDET_STAGE_START', label, flush=True)
        start = time.monotonic()
        with path.open('wb') as stream:
            process = subprocess.Popen(command, cwd=ROOT, env=env, stdout=stream,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            timed_out = False
            try:
                exit_code = process.wait(timeout=600)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(process.pid, signal.SIGKILL)
                process.wait(timeout=30)
                exit_code = 124
        entry.update(status='PASSED' if exit_code == 0 and not timed_out else 'FAILED',
                     exit_code=exit_code, timed_out=timed_out,
                     seconds=round(time.monotonic() - start, 3), ended_utc=now(),
                     log_sha256=digest(path), log_bytes=path.stat().st_size)
        freeze(path)
        write()
        print('P25_P1_FASTDET_STAGE_RESULT', label,
              json.dumps({k: entry[k] for k in ['exit_code', 'timed_out', 'seconds', 'log_bytes', 'log_sha256']},
                         sort_keys=True), flush=True)
        if exit_code or timed_out:
            state.update(status=label.upper() + '_FAILED', failed_stage=label)
            write()
            print(path.read_text(errors='replace')[-6000:], flush=True)
            raise RuntimeError(f'{label} gate failed; no acceptance capsule is produced.')
        check_frozen()

    try:
        for folder in ['src/ImbalancedChen', 'lib/ImbalancedChen', 'audit', 'logs', 'runner']:
            (ROOT / folder).mkdir(parents=True)
        runner_copy = ROOT / 'runner/run_p1_fastdet_cloud.py'
        shutil.copyfile(Path(__file__).resolve(), runner_copy)
        freeze(runner_copy)
        source_copy = ROOT / 'src/ImbalancedChen/P2Winner9FastDetPure.lean'
        shutil.copyfile(input_path, source_copy)
        freeze(input_path)
        freeze(source_copy)
        require(digest(source_copy) == SOURCE_SHA and source_copy.stat().st_size == SOURCE_BYTES,
                'Copied source differs from transported source.')
        source_text = source_copy.read_text()
        require(re.findall(r'^import\s+([^\s]+)\s*$', source_text, re.MULTILINE) == DIRECT_IMPORTS,
                'Original direct imports changed.')
        require('namespace ' + MODULE in source_text and 'end ' + MODULE in source_text,
                'Original namespace changed.')
        require(not re.search(r'\b(sorry|admit|axiom|unsafe|partial|native_decide|implemented_by|extern)\b', source_text),
                'Source contains a forbidden escape token.')
        origin = {
            'commit': publication, 'path': SOURCE_PATH, 'sha256': SOURCE_SHA, 'bytes': SOURCE_BYTES,
            'binding_kind': 'caller-supplied publication identity with frozen exact-source SHA256',
            'independently_verified_remote_git_object': False,
        }
        provenance = {
            'schema': 'p25-caller-source-transport-v1', 'source_origin': origin,
            'transport': 'caller_materialized_source', 'materialized_input': record(input_path, relative=False),
            'source_copy': record(source_copy), 'source_bytes_verified': True,
            'remote_checkout_performed': False, 'remote_git_object_inspection_performed': False,
            'note': 'Caller publishes and transports source, e.g. by base64. This runner verifies bytes; it does not certify remote Git membership.',
        }
        save_json(ROOT / 'SOURCE_PROVENANCE.json', provenance)
        freeze(ROOT / 'SOURCE_PROVENANCE.json')
        state.update(runner=record(runner_copy), source_origin=origin, source_copy=record(source_copy),
                     source_provenance=record(ROOT / 'SOURCE_PROVENANCE.json'))
        audit = ROOT / 'audit/Audit.lean'
        require('__AUDIT_SOURCE__' not in AUDIT_SOURCE, 'Unmaterialized audit template.')
        audit.write_text(AUDIT_SOURCE)
        freeze(audit)
        state.update(audit_source=record(audit), audit_template_origin={
            'path': 'docs/source-only/20261126-p2-5-cell00-decoded/TYPED_PAYLOAD_AUDIT.lean',
            'sha256': AUDIT_TEMPLATE_SHA,
            'transformation': 'Replace only ImbalancedChen.P2Saving16Cell00TypedPayload by target module.'})
        require(LEAN.is_file() and CHECKER.is_file(), 'Pinned Lean or leanchecker is missing.')
        freeze(LEAN)
        freeze(CHECKER)
        version = checked_output([str(LEAN), '--version'])
        require('4.33.0-rc1' in version and (LEAN_COMMIT in version or LEAN_COMMIT[:7] in version),
                'Lean version or toolchain commit differs.')
        manifest = MATHLIB / 'lake-manifest.json'
        require(digest(manifest) == MANIFEST_SHA, 'Mathlib dependency manifest hash differs.')
        manifest_data = json.loads(manifest.read_text())
        actual_package_pins = {x['name']: x['rev'] for x in manifest_data['packages']}
        require(actual_package_pins == PACKAGE_PINS, 'Mathlib package revision map differs.')
        toolchain_file = MATHLIB / 'lean-toolchain'
        require(toolchain_file.read_text().strip() == 'leanprover/lean4:v4.33.0-rc1',
                'Mathlib lean-toolchain differs.')
        freeze(manifest)
        freeze(toolchain_file)
        mathlib_actual = git_pin(MATHLIB, MATHLIB_PIN)
        mathlib_lib = MATHLIB / '.lake/build/lib/lean'
        standard_lib = TOOLCHAIN_ROOT / 'lib/lean'
        require(mathlib_lib.is_dir() and standard_lib.is_dir(), 'Missing Mathlib or toolchain compiled library.')
        providers = [('mathlib', mathlib_lib)]
        package_records = {}
        for name, pin in PACKAGE_PINS.items():
            path = MATHLIB.parent / name
            actual = git_pin(path, pin)
            compiled = path / '.lake/build/lib/lean'
            # Cli is a Lake dependency; it need not have a compiled directory for these Lean imports.
            require(name == 'Cli' or compiled.is_dir(), f'Missing compiled package: {name}')
            package_records[name] = {'path': str(path), 'git_commit': actual,
                                     'expected_git_commit': pin,
                                     'compiled_lib': str(compiled) if compiled.is_dir() else None}
            if compiled.is_dir():
                providers.append(('package:' + name, compiled))
        providers.append(('toolchain', standard_lib))
        for provider, path in providers:
            require(not (path / 'ImbalancedChen').exists(),
                    f'Unexpected project-object fallback under external provider {provider}')
        env = os.environ.copy()
        env['PATH'] = str(LEAN.parent) + os.pathsep + env.get('PATH', '')
        env['LEAN_PATH'] = os.pathsep.join([str(ROOT / 'lib'), *[str(p) for name, p in providers if name != 'toolchain']])
        # The selected executable supplies its own standard library; inherited overrides are forbidden.
        env.pop('LEAN_SYSROOT', None)
        env.pop('LEAN_SRC_PATH', None)
        runtime = {
            'schema': 'p25-p1-fastdet-runtime-v1',
            'toolchain': {'root': str(TOOLCHAIN_ROOT), 'expected_commit': LEAN_COMMIT,
                          'version': version, 'lean': record(LEAN, relative=False),
                          'leanchecker': record(CHECKER, relative=False), 'compiled_lib': str(standard_lib)},
            'mathlib': {'path': str(MATHLIB), 'git_commit': mathlib_actual, 'expected_git_commit': MATHLIB_PIN,
                        'manifest': record(manifest, relative=False),
                        'lean_toolchain': record(toolchain_file, relative=False), 'compiled_lib': str(mathlib_lib)},
            'packages': package_records, 'LEAN_PATH': env['LEAN_PATH'],
            'providers': {name: {'compiled_lib': str(path)} for name, path in providers},
            'strict_flags': FLAGS, 'stage_wall_limit_seconds': 600,
            'git_checks_are_read_only': True,
            'compiled_external_hash_collection': 'All provider .olean files and existing private/server companions snapshotted before gates; actual audit-import files rechecked against that snapshot after gates.',
        }
        save_json(ROOT / 'RUNTIME.json', runtime)
        freeze(ROOT / 'RUNTIME.json')
        state['runtime'] = record(ROOT / 'RUNTIME.json')

        # The actual transitive import set is learned from the final audit. Its
        # byte provenance must nevertheless precede every gate, so snapshot all
        # eligible provider objects first. Unrelated provider files need not be
        # unchanged later; only actual imports are selected and rechecked below.
        snapshot_started = now()
        print('P25_P1_FASTDET_EXTERNAL_SNAPSHOT_START', flush=True)
        before_entries = []
        before_index = {}
        for provider, root in providers:
            for object_file in sorted(root.rglob('*.olean')):
                require(object_file.is_file(), f'Non-file external object: {object_file}')
                paths = [object_file]
                paths += [object_file.with_name(object_file.name + suffix)
                          for suffix in ['.private', '.server']
                          if object_file.with_name(object_file.name + suffix).is_file()]
                for path in paths:
                    relative_path = str(path.relative_to(root))
                    key = (provider, relative_path)
                    require(key not in before_index, f'Duplicate external snapshot entry: {key}')
                    item = {'provider': provider, 'relative_path': relative_path,
                            **record(path, relative=False)}
                    before_index[key] = item
                    before_entries.append(item)
        require(before_entries, 'Empty external object snapshot.')
        before_snapshot = {
            'schema': 'p25-external-olean-before-snapshot-v1', 'module': MODULE,
            'started_utc': snapshot_started, 'finished_utc': now(),
            'timing': 'Completed and frozen before normal compilation, replay, and complete-owned audit.',
            'provider_roots': {name: str(path) for name, path in providers},
            'scope': 'Every provider *.olean and its existing .private/.server companions; unrelated files are not required to remain unchanged.',
            'file_count': len(before_entries), 'entries': before_entries,
        }
        snapshot_path = ROOT / 'PRE_GATE_EXTERNAL_SNAPSHOT.json'
        save_json(snapshot_path, before_snapshot)
        freeze(snapshot_path)
        snapshot_record = record(snapshot_path)
        state['external_pre_gate_snapshot'] = snapshot_record
        write()
        print('P25_P1_FASTDET_EXTERNAL_SNAPSHOT_COMPLETE', len(before_entries),
              snapshot_record['sha256'], flush=True)

        def require_before_match(provider, relative_path, path):
            prior = before_index.get((provider, relative_path))
            require(prior is not None, f'Actual imported object was absent before gates: {provider}/{relative_path}')
            current = record(path, relative=False)
            require(all(current[k] == prior[k] for k in ['path', 'bytes', 'sha256']),
                    f'Actual imported object changed after pre-gate snapshot: {provider}/{relative_path}')
            freeze(path)
            return current

        def external_record(module):
            require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", module),
                    f'Unexpected external module name: {module}')
            relative_path = module.replace('.', '/') + '.olean'
            found = [(name, root / relative_path) for name, root in providers if (root / relative_path).is_file()]
            require(len(found) == 1, f'External module missing or shadowed: {module}')
            provider, path = found[0]
            before_providers = [name for name, _ in providers if (name, relative_path) in before_index]
            require(before_providers == [provider],
                    f'Actual imported module provider was missing or shadowed before gates: {module}')
            item = {'module': module, 'provider': provider, 'relative_path': relative_path,
                    **require_before_match(provider, relative_path, path), 'companions': []}
            for suffix in ['.private', '.server']:
                companion = path.with_name(path.name + suffix)
                companion_relative = relative_path + suffix
                existed_before = (provider, companion_relative) in before_index
                require(companion.is_file() == existed_before,
                        f'Actual imported companion set changed after pre-gate snapshot: {provider}/{companion_relative}')
                if companion.is_file():
                    item['companions'].append({'relative_path': companion_relative,
                        **require_before_match(provider, companion_relative, companion)})
            return item

        direct_fingerprints = [external_record(m) for m in DIRECT_IMPORTS]
        state['external_direct_imports_before_gates'] = direct_fingerprints
        state['status'] = 'VERIFYING_UNCHANGED_OWNER'
        write()
        object_path = ROOT / 'lib/ImbalancedChen/P2Winner9FastDetPure.olean'
        require(not object_path.exists(), 'New target object unexpectedly exists.')
        stage('normal', [str(LEAN), *FLAGS, '--root=' + str(ROOT / 'src'),
                         '-o', str(object_path), str(source_copy)], env)
        require(object_path.is_file(), 'Strict compile did not produce the target object.')
        freeze(object_path)
        object_companions = []
        for suffix in ['.private', '.server']:
            path = object_path.with_name(object_path.name + suffix)
            if path.is_file():
                freeze(path)
                object_companions.append(record(path))
        state.update(object=record(object_path), object_companions=object_companions)
        write()
        stage('replay', [str(CHECKER), '--verbose', MODULE], env)
        stage('audit', [str(LEAN), *FLAGS, '--root=' + str(ROOT / 'audit'), str(audit)], env)
        declarations, inventory, imports = parse_audit(ROOT / 'logs/AUDIT.log')
        save_json(ROOT / 'OWNED_DECLARATIONS.json', declarations)
        save_json(ROOT / 'OWNED_INVENTORY.json', inventory)
        freeze(ROOT / 'OWNED_DECLARATIONS.json')
        freeze(ROOT / 'OWNED_INVENTORY.json')
        external_entries = [external_record(m) for m in sorted(imports) if m != MODULE]
        external = {
            'schema': 'p25-external-olean-closure-v1', 'module': MODULE,
            'scope': 'Complete audited import environment, conservatively including audit-only Lean.Util.CollectAxioms dependencies.',
            'collection_timing': 'All listed bytes were snapshotted before gates; actual audit-import files and companion sets were rechecked unchanged after all three gates.',
            'external_pre_gate_snapshot': snapshot_record,
            'all_actual_imports_match_pre_gate_snapshot': True,
            'source_direct_imports': DIRECT_IMPORTS, 'audit_direct_extra_imports': ['Lean.Util.CollectAxioms'],
            'audit_environment_imports': sorted(imports), 'actual_project_closure': [MODULE],
            'provider_roots': {name: str(path) for name, path in providers},
            'external_module_count': len(external_entries), 'entries': external_entries,
            'receiver_requirement': 'Map each provider to the same pinned environment; require every .olean and listed companion SHA256 before reuse. This list is not a source-only minimal closure.',
        }
        save_json(ROOT / 'EXTERNAL_IMPORTS.json', external)
        freeze(ROOT / 'EXTERNAL_IMPORTS.json')
        require(git_pin(MATHLIB, MATHLIB_PIN) == mathlib_actual, 'Mathlib changed during gates.')
        for name, pin in PACKAGE_PINS.items():
            git_pin(MATHLIB.parent / name, pin)
        check_frozen()
        state.update(status='NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED', accepted=True, ended_utc=now(),
                     owned_count=len(declarations), owned_declarations=declarations,
                     declarations=record(ROOT / 'OWNED_DECLARATIONS.json'),
                     inventory=record(ROOT / 'OWNED_INVENTORY.json'),
                     actual_project_closure=[MODULE], external_imports=record(ROOT / 'EXTERNAL_IMPORTS.json'),
                     external_module_count=len(external_entries),
                     historical_two_gate_object={'sha256': HISTORICAL_OBJECT_SHA,
                                                 'same_bytes_as_new_object': digest(object_path) == HISTORICAL_OBJECT_SHA,
                                                 'used_as_acceptance_evidence': False},
                     frozen_files_sha256=dict(sorted(frozen.items())))
        write()
        # RESULT cannot contain its own hash or the archive hash. Transport is a separate outer receipt.
        files = ['RESULT.json', 'SOURCE_PROVENANCE.json', 'RUNTIME.json', 'EXTERNAL_IMPORTS.json',
                 'PRE_GATE_EXTERNAL_SNAPSHOT.json',
                 'OWNED_DECLARATIONS.json', 'OWNED_INVENTORY.json', 'runner/run_p1_fastdet_cloud.py',
                 'src/ImbalancedChen/P2Winner9FastDetPure.lean', 'lib/ImbalancedChen/P2Winner9FastDetPure.olean',
                 'audit/Audit.lean', 'logs/NORMAL.log', 'logs/REPLAY.log', 'logs/AUDIT.log']
        files += [x['path'] for x in object_companions]
        files = sorted(files)
        require(len(files) == len(set(files)), 'Duplicate capsule payload paths.')
        manifest_value = {'schema': 'p25-fastdet-capsule-files-v1', 'module': MODULE,
                          'publication_commit': publication, 'files': [record(ROOT / name) for name in files],
                          'excluded_to_avoid_hash_cycles': ['CAPSULE_FILES.json', 'accepted.tar.gz', 'CAPSULE_TRANSPORT.json']}
        save_json(ROOT / 'CAPSULE_FILES.json', manifest_value)
        archive = ROOT / 'accepted.tar.gz'
        with tarfile.open(archive, 'w:gz') as tar:
            for name in [*files, 'CAPSULE_FILES.json']:
                path = ROOT / name
                require(path.is_file() and not path.is_symlink() and '..' not in Path(name).parts
                        and not Path(name).is_absolute(), f'Unsafe capsule entry: {name}')
                tar.add(path, arcname=name, recursive=False)
        transport = {'schema': 'p25-fastdet-capsule-transport-v1', 'module': MODULE, 'accepted': True,
                     'publication_commit': publication, 'archive': record(archive),
                     'result': record(ROOT / 'RESULT.json'), 'manifest': record(ROOT / 'CAPSULE_FILES.json'),
                     'source_sha256': SOURCE_SHA, 'object_sha256': digest(object_path),
                     'remote_checkout_performed': False, 'remote_git_object_inspection_performed': False}
        save_json(ROOT / 'CAPSULE_TRANSPORT.json', transport)
        print('P25_P1_FASTDET_ACCEPTED', json.dumps({'owned_count': len(declarations),
              'external_module_count': len(external_entries), 'transport': transport}, sort_keys=True), flush=True)
        return 0
    except Exception as error:
        state.update(accepted=False, ended_utc=now(), error=str(error), traceback=traceback.format_exc())
        if state['status'] not in {'NORMAL_FAILED', 'REPLAY_FAILED', 'AUDIT_FAILED'}:
            state['status'] = 'VERIFICATION_FAILED'
        write()
        print('P25_P1_FASTDET_FAILED', str(error), flush=True)
        return 1


if __name__ == '__main__':
    sys.exit(main())
