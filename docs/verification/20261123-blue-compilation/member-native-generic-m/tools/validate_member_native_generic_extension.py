#!/usr/bin/env python3
"""Replay exact built Member native modules and export all defining-module types/axioms.

Uses the repository's existing, tested environment-inventory audit, including
private/generated declarations and structure fields. No project source is edited.
"""
from pathlib import Path
import argparse
import collections
import datetime
import fcntl
import hashlib
import json
import re
import subprocess
import time

PROJECT = Path('/workspace/blue-member-build')
MODULE_ROOT = PROJECT / '.lake/packages/goldbach'
ROOT = Path('/workspace/blue-member-native-generic-extension-validation')
GUARD = ['python3', '/workspace/blue-build-tools/run_guarded.py']


def digest(path):
    return {'bytes': path.stat().st_size,
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def run(command, directory, label, stdin=None):
    record = {'command': command, 'cwd': str(PROJECT),
              'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    save(directory / (label + '-process.json'), record)
    started = time.monotonic()
    with (directory / (label + '.log')).open('wb') as output:
        result = subprocess.run(command, cwd=PROJECT, input=stdin,
                                stdout=output, stderr=subprocess.STDOUT)
    record.update(exit_code=result.returncode, elapsed_seconds=time.monotonic() - started,
                  finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  log_sha256=digest(directory / (label + '.log'))['sha256'])
    if stdin is not None:
        record['stdin_sha256'] = hashlib.sha256(stdin).hexdigest()
    save(directory / (label + '-process.json'), record)
    print(json.dumps(record), flush=True)
    if result.returncode:
        print((directory / (label + '.log')).read_text()[-18000:])
        raise SystemExit(result.returncode)
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--resume-audit', action='store_true', help='Reuse a successful kernel replay and unchanged exact source/output snapshot after an audit-tooling failure')
    parser.add_argument('modules', nargs='+')
    args = parser.parse_args()
    assert len(set(args.modules)) == len(args.modules)
    assert all(re.fullmatch(r'MathlibNt\.[A-Za-z0-9_.]+', m) for m in args.modules)
    lock = (ROOT / 'controller.lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    if args.resume_audit:
        assert args.out.is_dir()
    else:
        args.out.mkdir(parents=True, exist_ok=False)
    paths = []
    for module in args.modules:
        relative = module.replace('.', '/')
        paths += [MODULE_ROOT / (relative + '.lean'),
                  MODULE_ROOT / '.lake/build/lib/lean' / (relative + '.olean'),
                  MODULE_ROOT / '.lake/build/lib/lean' / (relative + '.ilean'),
                  MODULE_ROOT / '.lake/build/ir' / (relative + '.c'),
                  MODULE_ROOT / '.lake/build/ir' / (relative + '.setup.json'),
                  MODULE_ROOT / '.lake/build/lib/lean' / (relative + '.trace')]
    before = {str(path): digest(path) for path in paths}
    if args.resume_audit:
        assert before == json.loads((args.out / 'SOURCE_AND_OUTPUTS_BEFORE.json').read_text())
    else:
        save(args.out / 'SOURCE_AND_OUTPUTS_BEFORE.json', before)
    template_path = Path('/workspace/goldbach-formalization/verification/VariableEnvelopeBoxesAudit.lean')
    template = template_path.read_text()
    body = template[template.index('open Lean Elab Command in'):]
    module_array = '  let modules := #[\n    ' + ',\n    '.join('`' + m for m in args.modules) + ']\n'
    body, count = re.subn(r'  let modules := #\[.*?\]\n(?=  let allowed)', module_array, body, count=1, flags=re.S)
    assert count == 1
    body = body.replace('unless m == `verification.VariableEnvelopeBoundary || count > 0 do',
                        'unless count > 0 do').replace('VE_AUDIT_', 'NATIVE_AUDIT_')
    inventory_before = '  let names := env.constants.fold (init := #[]) fun names name _ =>\n    match env.getModuleIdxFor? name with\n    | some idx => if modules.contains env.header.moduleNames[idx]! then names.push name else names\n    | none => names\n'
    inventory_after = '  let moduleNames := env.header.moduleNames\n  let foldNames := env.constants.fold (init := #[]) fun names name _ =>\n    match env.getModuleIdxFor? name with\n    | some idx => if modules.contains moduleNames[idx.toNat]! then names.push name else names\n    | none => names\n  let names := foldNames.qsort Name.lt\n  let inventory := Json.mkObj [("cached_fold", toJson (names.map Name.toString))]\n  liftIO <| IO.println s!"NATIVE_AUDIT_NAME_SETS {inventory.compress}"\n'
    assert body.count(inventory_before) == 1
    body = body.replace(inventory_before, inventory_after)
    body = body.replace('env.header.moduleNames[idx]!', 'moduleNames[idx.toNat]!')
    code = ('\n'.join('import ' + module for module in args.modules) +
            '\nimport Lean.Util.CollectAxioms\n\nset_option pp.all true\n\n' + body)
    (args.out / 'ModuleAudit.lean').write_text(code)
    if args.resume_audit:
        kernel = json.loads((args.out / 'kernel-process.json').read_text())
        assert kernel['exit_code'] == 0
        assert kernel['command'] == GUARD + ['lake', 'env', 'leanchecker', '--verbose', *args.modules]
        assert kernel['log_sha256'] == digest(args.out / 'kernel.log')['sha256']
    else:
        kernel = run(GUARD + ['lake', 'env', 'leanchecker', '--verbose', *args.modules], args.out, 'kernel')
    actual = [line.removeprefix('replaying ') for line in (args.out / 'kernel.log').read_text().splitlines()
              if line.startswith('replaying ')]
    assert len(actual) == len(set(actual)) == len(args.modules) and set(actual) == set(args.modules)
    audit = run(GUARD + ['lake', 'env', 'lean', '-DmaxRecDepth=100000',
                         '-DmaxHeartbeats=4000000', '--stdin'], args.out, 'types-axioms', code.encode())
    raw = (args.out / 'types-axioms.log').read_text()
    name_sets = [json.loads(line.removeprefix('NATIVE_AUDIT_NAME_SETS ')) for line in raw.splitlines()
                 if line.startswith('NATIVE_AUDIT_NAME_SETS ')]
    assert len(name_sets) == 1
    name_sets = name_sets[0]
    assert len(name_sets['cached_fold']) == len(set(name_sets['cached_fold']))
    name_set_bytes = ('\n'.join(name_sets['cached_fold']) + '\n').encode()
    inventory_check = dict(schema='member_native_complete_owned_inventory_cached_fold_v1',
                           method='cached header, complete environment constant fold with exact defining-module owner; no private/generated filtering',
                           inventory_scope='All constants selected by exact defining-module owner; private/generated retained', count=len(name_sets['cached_fold']),
                           names_sha256=hashlib.sha256(name_set_bytes).hexdigest(),
                           private_name_count=sum(n.startswith('_private.') for n in name_sets['cached_fold']),
                           names=name_sets['cached_fold'], actual_audit_exit_code=audit['exit_code'])
    save(args.out / 'INVENTORY_NAME_SET_CHECK.json', inventory_check)
    declarations = [json.loads(line.removeprefix('NATIVE_AUDIT_DECL ')) for line in raw.splitlines()
                    if line.startswith('NATIVE_AUDIT_DECL ')]
    counts = [json.loads(line.removeprefix('NATIVE_AUDIT_MODULE ')) for line in raw.splitlines()
              if line.startswith('NATIVE_AUDIT_MODULE ')]
    totals = [int(line.removeprefix('NATIVE_AUDIT_COUNT ')) for line in raw.splitlines()
              if line.startswith('NATIVE_AUDIT_COUNT ')]
    assert len(totals) == 1 and totals[0] == len(declarations) == len({x['name'] for x in declarations})
    observed_counts = collections.Counter(x['module'] for x in declarations)
    assert set(observed_counts) == set(args.modules) and all(observed_counts[x['module']] == x['count'] for x in counts)
    assert '⋯' not in raw and '...' not in raw
    assert sorted(item['name'] for item in declarations) == sorted(name_sets['cached_fold'])
    axioms = sorted({axiom for item in declarations for axiom in item['axioms']})
    assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}
    after = {str(path): digest(path) for path in paths}
    assert before == after
    save(args.out / 'SOURCE_AND_OUTPUTS_AFTER.json', after)
    save(args.out / 'DECLARATION_TYPES_AXIOMS.json', declarations)
    result = {'schema': 'member_native_module_kernel_type_axiom_inventory_v1',
              'result': 'PASS_EXACT_MODULE_REPLAY_FULL_OWNED_DECLARATION_TYPES_AND_STANDARD_AXIOMS',
              'modules': args.modules, 'kernel': kernel, 'types_and_axioms': audit,
              'declaration_counts': dict(observed_counts), 'declarations': declarations,
              'observed_axioms': axioms, 'source_and_five_outputs_per_module': after,
              'sources_and_outputs_unchanged': True,
              'inventory_method': 'Cached moduleNames; original complete env.constants.fold and defining-module ownership semantics, no private/generated filtering',
              'inventory_crosscheck': inventory_check,
              'audit_driver': {'path': str(Path(__file__)), **digest(Path(__file__))},
              'audit_template': {'path': str(template_path), **digest(template_path)},
              'replay_scope': 'exact named modules relative to their existing imports; no fresh all-import replay claim'}
    save(args.out / 'VALIDATION_RESULTS.json', result)
    print(json.dumps({key: result[key] for key in ['result', 'declaration_counts', 'observed_axioms']}))


if __name__ == '__main__':
    main()
