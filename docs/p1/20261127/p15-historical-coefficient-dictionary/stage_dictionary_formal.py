#!/usr/bin/env python3
"""Stage only exact bound dictionary entrypoints. INPUTS=None disables all I/O."""
from pathlib import Path
import argparse
import ast
import hashlib
import json
import os
import re
import subprocess
import sys
sys.dont_write_bytecode = True

REPO = Path('/workspace/goldbach-formalization')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
INSTALL_ROOT = Path('/workspace/p1-complete-proof/20261127-p15-dictionary-source-install-v1')
PACKAGE = 'docs/p1/20261127/p15-historical-coefficient-dictionary/'
SCRIPT = PACKAGE + 'stage_dictionary_formal.py'
AO = '74926278c913d45401225c1b7e08185c9eec57e9'
AN = '938a761761f0e8a96404f843488f0a733818b156'
SOURCE = 'ImbalancedChen/P1OriginalHistoricalCoefficientDictionary.lean'
ORIGIN = 'docs/source-only/20261127/p1-historical-coefficient-dictionary-if-neg-repair/P1OriginalHistoricalCoefficientDictionary.lean'
SOURCE_FP = {'bytes': 9107, 'sha256': 'eb78b1ba6ced1f441b8b923210ef1fc32c107b307be69c0c3f6d2b8fd91d97ff'}
UNBOUND_ENTRYPOINTS = {
    'run_dictionary.py': {'bytes': 44560, 'sha256': 'ec53f3bb5ba43ee38295a0ff7fb102ccf6350decceb20a8067fbbc9c88e1a32a'},
    'install_dictionary_source.py': {'bytes': 9775, 'sha256': '74711a9f3c4331db4f92f073c372751cf4aa97b3fb94379e4fc4230826085379'},
}
INPUTS = {'entrypoints': {'install_dictionary_source.py': {'bytes': 10675,
                                                  'sha256': '76ce06c274f5e90f9aec1b11937943820520ea106f419e4a350949119ea27c57'},
                 'run_dictionary.py': {'bytes': 45460,
                                       'sha256': 'b9945bc538fef6baf4608367c166c3c48f088087a85f2af442278f9fd31f7d3f'}},
 'runtime_inputs': {'canonical_source': {'bytes': 9107,
                                         'sha256': 'eb78b1ba6ced1f441b8b923210ef1fc32c107b307be69c0c3f6d2b8fd91d97ff'},
                    'geometry': {'mode': 'accepted',
                                 'reader': {'bytes': 43509,
                                            'sha256': 'e52e170a0d06b40b3d52020a2f2627df48dbd621c53099c696a8a0caac5703ff'},
                                 'reader_path': 'docs/p1/20261127/p15-remaining-typei-geometry/run_geometry.py',
                                 'readonly_report': {'bytes': 39914,
                                                     'sha256': '6b83cb528cc7310f103650ddf4f3c01e14ef8851dd5d709d424894305d7f564b'},
                                 'source_commit': '938a761761f0e8a96404f843488f0a733818b156'},
                    'probe_document': {'bytes': 88316,
                                       'sha256': '01236d55c4b7d0434066be11b504aaae013ccdfebb6388f5c587e2ab4906561c'},
                    'probe_job': 'job_d2088f6dcc48496082022225e68d2920',
                    'probe_publication': '74926278c913d45401225c1b7e08185c9eec57e9'},
 'source_origin': {'bytes': 9107,
                   'commit': '74926278c913d45401225c1b7e08185c9eec57e9',
                   'path': 'docs/source-only/20261127/p1-historical-coefficient-dictionary-if-neg-repair/P1OriginalHistoricalCoefficientDictionary.lean',
                   'sha256': 'eb78b1ba6ced1f441b8b923210ef1fc32c107b307be69c0c3f6d2b8fd91d97ff'}}


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def valid_pin(row):
    return (isinstance(row, dict) and set(row) == {'bytes', 'sha256'} and
            type(row['bytes']) is int and row['bytes'] > 0 and isinstance(row['sha256'], str) and
            re.fullmatch('[0-9a-f]{64}', row['sha256']) is not None)


def require_bound_inputs():
    require(__debug__ and isinstance(INPUTS, dict) and
            INPUTS.get('source_origin') == {'commit': AO, 'path': ORIGIN, **SOURCE_FP} and
            isinstance(INPUTS.get('entrypoints'), dict) and set(INPUTS['entrypoints']) == set(UNBOUND_ENTRYPOINTS) and
            all(valid_pin(row) for row in INPUTS['entrypoints'].values()),
            'dictionary formal staging INPUTS are unbound')
    runtime = INPUTS.get('runtime_inputs')
    require(isinstance(runtime, dict) and runtime.get('canonical_source') == SOURCE_FP and
            runtime.get('probe_publication') == AO and valid_pin(runtime.get('probe_document')) and
            isinstance(runtime.get('probe_job'), str) and re.fullmatch('job_[0-9a-f]{32}', runtime['probe_job']),
            'actual successful AO probe runtime INPUTS are unbound')
    geo = runtime.get('geometry')
    require(isinstance(geo, dict) and geo.get('mode') == 'accepted' and geo.get('source_commit') == AN and
            geo.get('reader_path') == 'docs/p1/20261127/p15-remaining-typei-geometry/run_geometry.py' and
            valid_pin(geo.get('reader')) and valid_pin(geo.get('readonly_report')),
            'complete original AN Geometry readonly identity is unbound')


def inputs_assignment(raw):
    text = raw.decode('utf-8')
    nodes = [node for node in ast.parse(text).body if isinstance(node, ast.Assign) and
             any(isinstance(target, ast.Name) and target.id == 'INPUTS' for target in node.targets)]
    require(len(nodes) == 1 and len(nodes[0].targets) == 1 and nodes[0].col_offset == 0,
            'exactly one top-level INPUTS assignment is required')
    node = nodes[0]
    value = ast.literal_eval(node.value)
    lines = text.splitlines(keepends=True)
    restored = ''.join(lines[:node.lineno - 1]) + 'INPUTS = None\n' + ''.join(lines[node.end_lineno:])
    return value, restored.encode('utf-8')


def validate_final_payload(name, raw):
    require_bound_inputs()
    require(name in UNBOUND_ENTRYPOINTS and fp(raw) == INPUTS['entrypoints'][name],
            'final published entrypoint fingerprint differs')
    value, unbound = inputs_assignment(raw)
    require(value == INPUTS['runtime_inputs'] and fp(unbound) == UNBOUND_ENTRYPOINTS[name],
            'entrypoint changed beyond the exact reviewed v2 INPUTS binding')


def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)


def gitstate():
    return {name: fp(git(*args)) for name, args in {
        'head': ['rev-parse', 'HEAD'], 'status': ['status', '--porcelain=v1', '--untracked-files=all'],
        'worktree_diff': ['diff', '--binary'], 'index_diff': ['diff', '--cached', '--binary']}.items()}


def put(path, raw):
    require(path.parent.resolve() == path.parent and path.resolve() == path,
            'staging path traverses a symlink')
    path.parent.mkdir(parents=True, exist_ok=True)
    require(path.parent.resolve() == path.parent, 'staging parent changed')
    if os.path.lexists(path):
        require(path.is_file() and not path.is_symlink() and path.read_bytes() == raw,
                'different existing entrypoint cannot be overwritten')
        return
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o644)
    with os.fdopen(descriptor, 'wb') as stream:
        stream.write(raw); stream.flush(); os.fsync(stream.fileno())
    directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def stage(publication, executed):
    require_bound_inputs()
    require(isinstance(publication, str) and re.fullmatch('[0-9a-f]{40}', publication) and
            publication not in (AO, AN), 'a unique new formal publication after AO is required')
    before = gitstate()
    subprocess.run(['git', '-c', 'maintenance.auto=false', 'fetch', '--no-tags', '--no-write-fetch-head',
                    'origin', publication], cwd=REPO, check=True)
    require(subprocess.run(['git', 'merge-base', '--is-ancestor', AO, publication], cwd=REPO).returncode == 0,
            'formal publication must descend from AO')
    require(executed == git('show', publication + ':' + SCRIPT), 'executed stager differs from publication')
    origin = git('show', AO + ':' + ORIGIN)
    require(fp(origin) == SOURCE_FP and git('show', publication + ':' + ORIGIN) == origin and
            git('show', publication + ':' + SOURCE) == origin, 'canonical/source-only AO proof identity differs')
    payloads = {name: git('show', publication + ':' + PACKAGE + name) for name in UNBOUND_ENTRYPOINTS}
    for name, raw in payloads.items():
        validate_final_payload(name, raw)
    files = []
    for name, root in [('run_dictionary.py', ROOT), ('install_dictionary_source.py', INSTALL_ROOT)]:
        path = root / publication / 'published-entrypoints' / name
        put(path, payloads[name])
        files.append({'source': PACKAGE + name, 'path': str(path), **fp(payloads[name])})
    after = gitstate()
    require(before == after, 'Git head/status/worktree/index changed during staging')
    receipt = {'schema': 'p15_dictionary_formal_entrypoints_staging_v1',
        'status': 'EXACT_DICTIONARY_FORMAL_ENTRYPOINTS_STAGED', 'commit': publication, 'files': files,
        'source_origin': INPUTS['source_origin'], 'immutable_unbound_v2_entrypoints': UNBOUND_ENTRYPOINTS,
        'entrypoint_changes_only_bind_INPUTS': True, 'original_git_state_unchanged': True, 'git_state': after,
        'canonical_source_installed': False, 'normal_or_kernel_commands_executed': 0,
        'new_owner_accepted': False, 'whole_P1_5_complete': False}
    path = ROOT / publication / 'published-entrypoints/DICTIONARY_STAGING_RECEIPT.json'
    put(path, (json.dumps(receipt, sort_keys=True, indent=2) + '\n').encode())
    print(json.dumps({'receipt_path': str(path), **receipt}, sort_keys=True), flush=True)
    return 0


def main():
    require_bound_inputs()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--publication', required=True)
    args = parser.parse_args()
    path = Path(__file__)
    require(path.is_file() and not path.is_symlink(), 'stager must be a regular file')
    return stage(args.publication, path.read_bytes())


if __name__ == '__main__':
    try:
        require_bound_inputs()
        os.environ.update({'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                           'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'})
        raise SystemExit(main())
    except Exception as error:
        print(json.dumps({'status': 'DICTIONARY_FORMAL_STAGING_HOLD', 'error_type': type(error).__name__,
            'error': str(error), 'canonical_source_installed': False, 'new_owner_accepted': False,
            'whole_P1_5_complete': False}), flush=True)
        raise SystemExit(3)
