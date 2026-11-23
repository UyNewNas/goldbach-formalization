#!/usr/bin/env python3
"""Complete authenticated generated-C facets, without replacing any existing file.

This is a derivative of the recorded CDC restore procedure, not an update to its
frozen scripts, manifests, traces, or receipts. No compiler or builder is run.
"""
from __future__ import annotations

import argparse
import collections
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import tomllib
import zipfile

BASE = Path('/workspace/artifacts/cdc-qualified-p6')
CHECKPOINT = Path('/workspace/artifacts/t01-fifth-objects-42753193835-1/CHECKPOINT.json')
PROTOCOL = Path('/workspace/goldbach-formalization/docs/source-only/20261113-resume/coherent-cache-tools/checkpoint_original_protocol.py')
PROJECTS = {
    'p6': (Path('/workspace/blue-p6-build'), BASE / 'INSTALL_RECEIPT.json'),
    'member': (Path('/workspace/blue-member-build'), Path('/workspace/artifacts/cdc-qualified-member/INSTALL_RECEIPT.json')),
    'prototype': (Path('/workspace/blue-reindex-build'), Path('/workspace/blue-reindex-build-evidence/COPIED_ARTIFACT_CANDIDATES.json')),
}
EXCLUDED = {
    'ImbalancedChen.P2ContinuousSieveRational',
    'ImbalancedChen.P6OriginalLiteralLogIntegralPrices',
    'ImbalancedChen.P6OriginalLiteralMeshPrices',
    'ImbalancedChen.P6OriginalLogPolynomialBound',
    'ImbalancedChen.P6OriginalLogPolynomialRows',
    'ImbalancedChen.P6OriginalSeventhCorrectionIdentity',
    'ImbalancedChen.P5U7OriginalOmegaIntegral',
    'ImbalancedChen.P5U7OriginalBuchstabLipschitz',
    'ImbalancedChen.P5U7OriginalOmegaFubini',
    'ImbalancedChen.P5OrderedFactorTupleRectangleReindex',
}


def sha(path: Path) -> str:
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def token(path: Path):
    s = path.stat()
    return (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)


def read(path: Path):
    return json.loads(path.read_text())


def write_new(path: Path, value):
    with path.open('x') as f:
        json.dump(value, f, indent=2)
        f.write('\n')


def atomic_missing(destination: Path, data: bytes) -> bool:
    """Link a complete temporary file into a missing name; never overwrite."""
    destination.parent.mkdir(parents=True, exist_ok=True)
    fd, name = tempfile.mkstemp(prefix='.cdc-generated-c-', dir=destination.parent)
    tmp = Path(name)
    try:
        with os.fdopen(fd, 'wb') as f:
            f.write(data)
            f.flush()
            os.fsync(f.fileno())
        try:
            os.link(tmp, destination, follow_symlinks=False)
            return True
        except FileExistsError:
            return False
    finally:
        tmp.unlink()


def active_sources() -> set[str]:
    result = set()
    for proc in Path('/proc').glob('[0-9]*/cmdline'):
        try:
            args = [p.decode(errors='replace') for p in proc.read_bytes().split(b'\0') if p]
            if not args:
                continue
            executable = Path(args[0]).name
            # Include a wrapper waiting for its guard's serial lock.
            compiler_names = {'lean', 'lean-runtime', 'leanir', 'clang',
                              'lean-wrapper.py', 'leanir-wrapper.py', 'clang-wrapper.py'}
            python_wrapper = executable.startswith('python') and len(args) > 1 and Path(args[1]).name in compiler_names
            if executable not in compiler_names and not python_wrapper:
                continue
            for arg in args:
                if arg.startswith('/') and arg.endswith(('.lean', '.ir', '.c')):
                    result.add(str(Path(arg).resolve()))
        except (FileNotFoundError, PermissionError, ProcessLookupError):
            continue
    return result


class Auditor:
    def __init__(self):
        self.cache = {}
        self.checked = {}

    def check(self, path: Path, expected: str, size=None):
        # The stat token and fresh content digest bind the physical file; avoid
        # repeatedly resolving every ancestor of millions of shared import paths.
        key = str(path)
        before = token(path)
        if size is not None and before[2] != size:
            raise ValueError('Wrong size: ' + str(path))
        old = self.cache.get(key)
        got = old[1] if old is not None and old[0] == before else sha(path)
        if token(path) != before:
            raise ValueError('Changed while hashing: ' + str(path))
        if got != expected:
            raise ValueError('SHA256 mismatch: ' + str(path))
        self.cache[key] = (before, got)
        self.checked[key] = {'path': key, 'sha256': got, 'stat_identity': before}
        return before

    def unchanged(self, paths):
        return all(token(p) == stamp for p, stamp in paths)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--apply', action='store_true')
    parser.add_argument('--prototype-agreed', action='store_true')
    parser.add_argument('--prototype-completed', type=Path,
                        help='Owner-supplied JSON list of completed/Replayed module names')
    parser.add_argument('--only-project', choices=list(PROJECTS), action='append')
    parser.add_argument('--exclude-module', action='append', default=[])
    args = parser.parse_args()
    executed_helper_sha256 = sha(Path(__file__))
    args.out.mkdir(parents=True, exist_ok=False)
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    manifest_path = BASE / 'MANIFEST.json'
    m = read(manifest_path)
    cp = read(CHECKPOINT)
    audit = Auditor()
    protected = [manifest_path, CHECKPOINT, BASE / 'INSTALL_RECEIPT.json',
                 Path('/workspace/artifacts/cdc-qualified-member/INSTALL_RECEIPT.json'),
                 Path('/workspace/artifacts/install_cdc_p6_portable.py'),
                 Path('/workspace/artifacts/seed_cdc_member_portable.py'),
                 Path('/workspace/artifacts/add_architect_cdc_p6.py'), PROTOCOL]
    for state in Path('/workspace/blue-build-tools').glob('*runtime-evidence/state.json'):
        protected.append(state)
        protected.extend(state.parent.glob('*wrapper.py'))
    originals = {str(p): {'sha256': sha(p), 'stat_identity': token(p)} for p in protected}
    assert m['original_runtime_audit_valid'] and m['original_package_source_pins_valid'] and m['runtime_policy_matches']
    audit.check(CHECKPOINT, m['checkpoint_sha256'])
    for row in m['runtime_binary_checks']:
        assert row['matched']
        audit.check(Path(row['local']), row['expected'])
    for row in m['abi_checks']:
        if row['kind'] == 'pinned-toolchain-shared-library-ABI':
            assert row['matched']
            audit.check(Path(row['local']), row['expected'])
    archive = Path(m['archive']['path'])
    audit.check(archive, m['archive']['sha256'], m['archive']['bytes'])
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location('original_checkpoint_protocol', PROTOCOL)
    protocol = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(protocol)
    boundary = {r.get('module'): r for r in cp['all_guarded_package_compilations']
                if r.get('module') in m['modules'] and m['modules'][r['module']]['group'] == 'boundary'}
    supplement = []
    excluded = EXCLUDED | set(args.exclude_module)
    project_keys = args.only_project or ['p6', 'member'] + (['prototype'] if args.prototype_agreed else [])
    if 'prototype' in project_keys:
        assert args.prototype_agreed and args.prototype_completed is not None
        approval = read(args.prototype_completed)
        approval_rows = {r['module']: r for r in approval['modules']}
        prototype_completed = {r['module'] for r in approval['modules']}
        assert approval['owner'] == '/root/blue_inventory' and approval['count'] == len(prototype_completed)
        originals[str(args.prototype_completed)] = {'sha256': sha(args.prototype_completed), 'stat_identity': token(args.prototype_completed)}
    write_new(args.out / 'SESSION_START.json', {'helper_sha256': executed_helper_sha256,
              'started_utc': started, 'protected_originals': originals, 'archive_sha256': m['archive']['sha256'],
              'archive_verified': True, 'source_or_proof_or_trace_writes_permitted': False})
    result = []
    with zipfile.ZipFile(archive) as z:
        for key in project_keys:
            project, prior_path = PROJECTS[key]
            prior = read(prior_path)
            allowed = set(prior['modules']) if key != 'prototype' else prototype_completed & {r['module'] for r in prior}
            if key == 'member':
                assert prior['source_qualification_manifest']['sha256'] == originals[str(manifest_path)]['sha256']
            if key == 'p6':
                assert prior['source_qualification_manifest_sha256'] == originals[str(manifest_path)]['sha256']
            for index, name in enumerate(sorted(allowed)):
                if index % 25 == 0:
                    print(json.dumps({'phase': 'qualifying', 'project': key, 'group_index': index, 'total': len(allowed)}), flush=True)
                entry = {'project': key, 'module': name}
                result.append(entry)
                if name not in m['modules']:
                    entry['status'] = 'SKIP_NO_QUALIFIED_CDC_GROUP'; continue
                r = m['modules'][name]
                if name in excluded or r['reasons']:
                    entry['status'] = 'SKIP_EXCLUDED_OR_UNQUALIFIED'; continue
                package = '.lake/packages/goldbach' if r['group'] == 'native' else '.lake/packages/LeanArchitect' if r['group'] == 'boundary' else ''
                package_root = project / package
                source = package_root / r['source']['install_path']
                relative = Path(*name.split('.'))
                stem = package_root / '.lake/build/lib/lean' / relative
                ir = package_root / '.lake/build/ir' / relative
                cpath = ir.with_suffix('.c')
                hpath = ir.with_suffix('.c.hash')
                if cpath.exists() and hpath.exists():
                    entry['status'] = 'SKIP_ALREADY_COMPLETE'; continue
                try:
                    if str(source.resolve()) in active_sources() or str(cpath.resolve()) in active_sources():
                        entry['status'] = 'SKIP_ACTIVE_COMPILER_GROUP'; continue
                    source_token = audit.check(source, r['source']['sha256'], r['source']['bytes'])
                    # Fail fast on a real physical import-size mismatch before
                    # rechecking thousands of otherwise unchanged common imports.
                    for ident in r['import_part_keys']:
                        part = m['import_parts'][ident]
                        preflight = Path(part['local'])
                        if preflight.is_relative_to(Path(m['target_project'])):
                            preflight = project / preflight.relative_to(Path(m['target_project']))
                        if preflight.stat().st_size != part['bytes']:
                            raise ValueError('Preflight imported size mismatch: ' + str(preflight))
                    if key == 'prototype':
                        approved = approval_rows[name]
                        assert approved['source']['identity']['sha256'] == r['source']['sha256']
                        for artifact in approved['proof_artifact_snapshot']:
                            audit.check(Path(artifact['path']), artifact['sha256'], artifact['bytes'])
                    assert not r['setup_options'], 'Unsupported nonempty options'
                    config = tomllib.loads((package_root / 'lakefile.toml').read_text())
                    assert not config.get('leanOptions'), 'Current package options changed'
                    expected_args = ['-DmaxRecDepth=100000', '-DmaxHeartbeats=4000000'] if r['group'] == 'project' else []
                    assert config.get('moreLeanArgs', []) == expected_args, 'Current traced arguments differ'
                    assert all(not lib.get('moreLeanArgs') and not lib.get('leanOptions') for lib in config.get('lean_lib', [])), 'Library argument override'
                    trace_path = stem.with_suffix('.trace')
                    trace = read(trace_path)
                    assert trace['schemaVersion'] == '2025-09-10' and trace['synthetic'] is False
                    arg_caption = 'Module.leanArgs: #[' + ', '.join(expected_args) + ']'
                    assert any(x[0] == arg_caption for x in trace['inputs']), 'Saved trace arguments differ'
                    facets = [f for f in r['facets'] if f['install_path'].endswith(('.c', '.c.hash'))]
                    if r['group'] == 'boundary':
                        original = boundary[name]
                        assert original['output_bound_command'] and original['lake_completed_trace']
                        assert not original['missing_actual_import_artifacts']
                        facets = []
                        for f in original['facet_files']:
                            if f['original_path'].endswith(('.c', '.c.hash')):
                                rel = '.lake/packages/LeanArchitect/' + f['original_path'].split('/.lake/packages/LeanArchitect/', 1)[1]
                                facets.append(dict(f, install_path=rel, archive_payload=f['payload']))
                        supplement.append({'module': name, 'project': key, 'facets': facets})
                    assert {Path(f['install_path']).suffix for f in facets} == {'.c', '.hash'}, 'Incomplete authentic C facet pair'
                    # Check genuine existing proof/output bytes against the qualified group.
                    watched = [(source, source_token), (trace_path, token(trace_path))]
                    for f in r['facets']:
                        if f['install_path'].endswith(('.olean', '.olean.server', '.olean.private', '.ilean', '.ir', '.ir.sig')):
                            p = project / f['install_path']
                            watched.append((p, audit.check(p, f['sha256'], f['bytes'])))
                    # Rebind every actual imported physical part to its historical SHA.
                    import_bindings = []
                    for ident in r['import_part_keys']:
                        part = m['import_parts'][ident]
                        p = Path(part['local'])
                        if p.is_relative_to(Path(m['target_project'])):
                            p = project / p.relative_to(Path(m['target_project']))
                        stamp = audit.check(p, part['sha256'], part['bytes'])
                        import_bindings.append((p, stamp))
                    watched.extend(import_bindings)
                    # Check all source dependencies recorded by the qualification too.
                    imported_source_count = 0
                    setup_facet = next(f for f in r['facets'] if f['install_path'].endswith('.setup.json'))
                    historical_setup = json.loads(z.read(setup_facet['archive_payload']))
                    assert historical_setup['name'] == name and historical_setup['options'] == r['setup_options']
                    assert not historical_setup['dynlibs'] and not historical_setup['plugins']
                    for imported in historical_setup['importArts']:
                        check = m['import_source_checks'].get(imported)
                        if not check:
                            continue
                        p = Path(check['local'])
                        if p.is_relative_to(Path(m['target_project'])):
                            p = project / p.relative_to(Path(m['target_project']))
                        stamp = audit.check(p, check['expected'])
                        watched.append((p, stamp)); imported_source_count += 1
                    payloads = []
                    for f in sorted(facets, key=lambda f: f['install_path'].endswith('.hash')):
                        data = z.read(f['archive_payload'])
                        assert len(data) == f['bytes'] and hashlib.sha256(data).hexdigest() == f['sha256']
                        dest = project / f['install_path']
                        assert str(dest).endswith(('.c', '.c.hash')) and dest.resolve().is_relative_to(Path('/workspace'))
                        if dest.exists():
                            audit.check(dest, f['sha256'], f['bytes'])
                        payloads.append((dest, data, f))
                    cdata = next(data for dest, data, f in payloads if dest.suffix == '.c')
                    hdata = next(data for dest, data, f in payloads if dest.suffix == '.hash')
                    assert trace['outputs']['c'].split('.', 1)[0] == hdata.decode().strip(), 'C descriptor/sidecar mismatch'
                    # Existing complete descriptors (excluding the absent C) must bind.
                    descrs = {k:v for k,v in trace['outputs'].items() if k != 'c'}
                    assert all(x['matched'] for x in protocol.lake_descriptor_binding(descrs, stem, ir))
                    if not audit.unchanged(watched):
                        raise ValueError('Inputs/outputs changed during qualification')
                    current_active = active_sources()
                    if str(source.resolve()) in current_active or str(cpath.resolve()) in current_active:
                        entry['status'] = 'SKIP_ACTIVE_COMPILER_GROUP'; continue
                    entry.update(source_sha256=r['source']['sha256'], depHash=trace['depHash'],
                                 original_import_map_sha256=r['actual_import_map_sha256_verified'],
                                 imported_parts_checked=len(import_bindings), imported_sources_checked=imported_source_count,
                                 trace_sha256=sha(trace_path), facets=[])
                    for dest, data, f in payloads:
                        current_active = active_sources()
                        if str(source.resolve()) in current_active or str(cpath.resolve()) in current_active:
                            raise ValueError('Group became active before facet installation')
                        if not audit.unchanged(watched):
                            raise ValueError('Group inputs changed before facet installation')
                        if dest.exists():
                            audit.check(dest, f['sha256'], f['bytes'])
                            state = 'EXISTING_MATCH_PRESERVED'
                        elif args.apply:
                            intent = {'project': key, 'module': name, 'phase': 'BEFORE_ATOMIC_MISSING_INSTALL',
                                      'path': str(dest), 'sha256': f['sha256'], 'bytes': f['bytes'],
                                      'archive_payload': f['archive_payload'], 'source_sha256': entry['source_sha256'],
                                      'trace_sha256': entry['trace_sha256'], 'depHash': entry['depHash'],
                                      'original_import_map_sha256': entry['original_import_map_sha256']}
                            with (args.out / 'FACET_RESTORE_JOURNAL.jsonl').open('a') as journal:
                                journal.write(json.dumps(intent) + '\n'); journal.flush(); os.fsync(journal.fileno())
                            state = 'INSTALLED_AUTHENTIC_MISSING_FACET' if atomic_missing(dest, data) else 'RACE_EXISTING_PRESERVED'
                            with (args.out / 'FACET_RESTORE_JOURNAL.jsonl').open('a') as journal:
                                journal.write(json.dumps(dict(intent, phase=state)) + '\n'); journal.flush(); os.fsync(journal.fileno())
                            audit.check(dest, f['sha256'], f['bytes'])
                        else:
                            state = 'WOULD_INSTALL_AUTHENTIC_MISSING_FACET'
                        entry['facets'].append({'path': str(dest), 'sha256': f['sha256'], 'bytes': f['bytes'],
                                                'archive_payload': f['archive_payload'], 'status': state})
                    for dest, data, f in payloads:
                        if args.apply:
                            audit.check(dest, f['sha256'], f['bytes'])
                    assert sha(trace_path) == entry['trace_sha256'], 'Trace changed during installation'
                    assert audit.unchanged(watched), 'Inputs/outputs changed during installation'
                    entry['status'] = 'COMPLETED' if args.apply else 'QUALIFIED_PLAN'
                except (ValueError, AssertionError, KeyError, FileNotFoundError, StopIteration) as e:
                    entry['status'] = 'SKIP_QUALIFICATION_MISMATCH'
                    entry['reason'] = str(e)
    assert sha(Path(__file__)) == executed_helper_sha256, 'Helper changed during execution'
    for p, expected in originals.items():
        assert sha(Path(p)) == expected['sha256'], 'Protected original modified: ' + p
    write_new(args.out / 'ARCHITECT_C_SUPPLEMENT.json', {'checkpoint_sha256': m['checkpoint_sha256'], 'groups': supplement})
    write_new(args.out / 'PHYSICAL_INPUT_AUDIT.json', list(audit.checked.values()))
    receipt = {
        'schema': 'authentic-generated-c-facet-completion-v1', 'started_utc': started,
        'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'apply': args.apply, 'helper_sha256': executed_helper_sha256,
        'archive_sha256': m['archive']['sha256'], 'protected_originals': originals,
        'originals_unchanged': True, 'trace_rebasing': False, 'compiler_invoked': False,
        'sources_proof_objects_or_traces_written': False, 'native_executable_bytes_installed': False,
        'physical_input_audit_sha256': sha(args.out / 'PHYSICAL_INPUT_AUDIT.json'),
        'groups': result, 'group_status_counts': dict(collections.Counter((r['status'] for r in result))),
        'facet_status_counts': dict(collections.Counter(f['status'] for r in result for f in r.get('facets', []))),
    }
    write_new(args.out / 'CORRECTION_RECEIPT.json', receipt)
    print(json.dumps({k:receipt[k] for k in ['apply', 'group_status_counts', 'facet_status_counts']}, indent=2))


if __name__ == '__main__':
    main()
