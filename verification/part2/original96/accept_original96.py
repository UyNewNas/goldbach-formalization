#!/usr/bin/env python3
"""Accept the original96 and original P160-division owners with frozen drivers."""
from pathlib import Path
import base64
from collections import Counter
import hashlib
import json
import os
import subprocess
import sys
import tarfile
import time

ROOT = Path.cwd().resolve()
assert ROOT == Path('/workspace/p2-1-original96-20261126')
HERE = ROOT / 'verification/part2/original96'
PRIVATE = ROOT / '.lake/p2-private'
ATTEMPTS = ROOT / 'evidence/original96-acceptance'
ATTEMPTS.mkdir(parents=True, exist_ok=True)
RECORD = ATTEMPTS / f'attempt-{len(list(ATTEMPTS.glob("attempt-*"))) + 1:03d}'
RECORD.mkdir()
MODULES = ['ImbalancedChen.Certificates.P2OriginalLog96Series',
           'ImbalancedChen.Certificates.P2OriginalLog96',
           'ImbalancedChen.Certificates.P2OriginalP160DirectDivision']
DEPENDENCY = 'ImbalancedChen.Certificates.RationalLogCertificate'
DEPENDENCY_SOURCE = '4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22'
DEPENDENCIES = list(json.loads((HERE / 'accepted-dependencies.json').read_text())['modules'])
BASELINE = '8657cfffef159185f73c6a04ae4d31c846c0d0a9'
LEAN = '/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean'
CHECKER = str(Path(LEAN).with_name('leanchecker'))
EXPECTED_LEAN = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
EXPECTED_CHECKER = 'ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a'
MATHLIB = Path('/workspace/compile-deps/mathlib')
PIN = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
REUSED_TOOL_HASHES = {
    'run_winner9_private_checks.py': '164bc271d8806ed45ebdd71c8f394c4706d7cfdaf4a121b633d738e094bad7ac',
    'run_winner9_private_audit.py': '571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5',
    'winner9_private_audit_template.lean': '9b06e11c365836a2e118e91788947057e96249e2dcbbd7a46a7f4fa9d2c5d7eb',
    'inspect_winner9_owner_native.py': '9460e319b2f247b4deb6c4c12ad7b59732bfde939f5dc68e541b4a5714aed90d',
    'winner9_external_snapshot.py': 'a57b658beef42ebfe75ccb09d84f7f1ee7252c289f267396063c93ae5e0bbedf',
}

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def require(condition, reason):
    if not condition:
        raise RuntimeError(reason)

def git(repo, *args, data=None):
    return subprocess.run(['git', '-C', str(repo), *args], input=data,
        check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout

def snapshot():
    result = {}
    for module in [*DEPENDENCIES, *MODULES]:
        rel = Path(module.replace('.', '/'))
        for p in [ROOT / rel.with_suffix('.lean'),
                  PRIVATE / 'lib' / rel.with_suffix('.olean')]:
            if p.is_file():
                result[str(p.relative_to(ROOT))] = sha(p)
    return result

records = []
reviewed = json.loads((HERE / 'reviewed-inputs.json').read_text())
reviewed[str((HERE / 'reviewed-inputs.json').relative_to(ROOT))] = sha(HERE / 'reviewed-inputs.json')

def verify_reviewed_inputs():
    for rel, expected in reviewed.items():
        path = (ROOT / rel).resolve()
        require(path.is_relative_to(ROOT), 'reviewed input escaped project')
        require(sha(path) == expected, 'reviewed input changed: ' + rel)

env = dict(os.environ)
mathlib_libs = [MATHLIB / '.lake/build/lib/lean'] + [
    MATHLIB / '.lake/packages' / package / '.lake/build/lib/lean'
    for package in ['plausible', 'LeanSearchClient', 'importGraph', 'proofwidgets',
                    'aesop', 'Qq', 'batteries', 'Cli']]
env['LEAN_PATH'] = ':'.join(str(p) for p in mathlib_libs)

def run(argv, label, *, execution_env=None):
    verify_reviewed_inputs()
    before = snapshot()
    started = time.monotonic()
    log = RECORD / (label + '.log')
    with log.open('wb') as stream:
        r = subprocess.run(argv, cwd=ROOT, env=execution_env or env,
                           stdout=stream, stderr=subprocess.STDOUT)
    item = {'argv': argv, 'exit_code': r.returncode,
            'elapsed_seconds': time.monotonic() - started,
            'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log),
            'inputs_before': before, 'inputs_after': snapshot()}
    records.append(item)
    verify_reviewed_inputs()
    (RECORD / 'commands.json').write_text(json.dumps(records, indent=2) + '\n')
    print(json.dumps({k: v for k, v in item.items() if not k.startswith('inputs_')}), flush=True)
    if r.returncode:
        print(log.read_text(errors='replace')[-24000:], flush=True)
        raise RuntimeError(label + ' failed')
    if label != 'strict-compile':
        require(item['inputs_before'] == item['inputs_after'], label + ' changed proof inputs')

try:
    verify_reviewed_inputs()
    for name, expected in REUSED_TOOL_HASHES.items():
        require(sha(ROOT / 'verification/part2' / name) == expected, 'frozen audit tool changed: ' + name)
    require(sha(LEAN) == EXPECTED_LEAN, 'unexpected Lean binary')
    require(sha(CHECKER) == EXPECTED_CHECKER, 'unexpected independent checker')
    require(git(MATHLIB, 'rev-parse', 'HEAD').decode().strip() == PIN, 'Mathlib pin mismatch')
    dep_rel = Path(DEPENDENCY.replace('.', '/'))
    require(sha(ROOT / dep_rel.with_suffix('.lean')) == DEPENDENCY_SOURCE,
            'dependency source differs from accepted source')
    from prepare_cache import prepare
    cache_provenance = prepare(ROOT, PRIVATE / 'lib')
    source_repo = next((p for p in [Path('/workspace/goldbach-p2'),
        Path('/workspace/p25-q96-baseline-8657')] if (p / '.git').exists()), None)
    require(source_repo is not None, 'baseline Git repository unavailable')
    baseline = ROOT / '.lake/original96-baseline'
    baseline_dep = baseline / dep_rel.with_suffix('.lean')
    if not baseline.exists():
        subprocess.run(['git', 'clone', '--shared', '--no-checkout', str(source_repo), str(baseline)],
                       check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        git(baseline, 'update-ref', '--no-deref', 'HEAD', BASELINE)
        git(baseline, 'read-tree', 'HEAD')
        git(baseline, 'update-index', '--skip-worktree', '-z', '--stdin',
            data=git(baseline, 'ls-files', '-z'))
        baseline_dep.parent.mkdir(parents=True, exist_ok=True)
        baseline_dep.write_bytes(git(baseline, 'show', BASELINE + ':' + str(dep_rel.with_suffix('.lean'))))
        git(baseline, 'update-index', '--no-skip-worktree', str(dep_rel.with_suffix('.lean')))
        (baseline / '.lake/build/lib/lean').mkdir(parents=True)
    require(git(baseline, 'rev-parse', 'HEAD').decode().strip() == BASELINE, 'baseline moved')
    require(not any((baseline / '.lake/build/lib/lean').rglob('*')), 'baseline lib must remain empty')
    require(not git(baseline, 'status', '--porcelain', '--untracked-files=no').strip(),
            'isolated sparse baseline is not clean')
    require(sha(baseline_dep) == DEPENDENCY_SOURCE, 'baseline source mismatch')
    record_path = PRIVATE / 'records.json'
    if not record_path.exists():
        record_path.write_text(json.dumps(cache_provenance['original_selected_records'], indent=2) + '\n')
    provenance = {'cache_reuse': cache_provenance,
        'baseline': str(baseline), 'baseline_commit': BASELINE,
        'lean_sha256': sha(LEAN), 'leanchecker_sha256': sha(CHECKER),
        'mathlib_commit': PIN, 'mathlib_search_paths': [str(p) for p in mathlib_libs],
        'audit_driver_sha256': sha(ROOT / 'verification/part2/run_winner9_private_audit.py'),
        'compile_driver_sha256': sha(ROOT / 'verification/part2/run_winner9_private_checks.py'),
        'reviewed_inputs': reviewed, 'pinned_reused_tools': REUSED_TOOL_HASHES}
    (RECORD / 'preflight.json').write_text(json.dumps(provenance, indent=2) + '\n')
    run(['python3', '-B', 'verification/part2/run_winner9_private_checks.py',
         '--baseline-root', str(baseline), '--workers', '1', '--threads', '1',
         '--memory-mb', '6144', *MODULES], 'strict-compile')
    run(['python3', '-B', 'verification/part2/run_winner9_private_audit.py',
         '--memory-mb', '6144', '--summary-name', 'p21-original96-audit.json', *MODULES], 'owned-audit')
    summary = json.loads((PRIVATE / 'audit/p21-original96-audit.json').read_text())
    require(summary['all_accepted'] and summary['accepted'] == summary['requested'] == len(MODULES),
            'not all new owners accepted')
    names = []
    owner_execution = {}
    for module in MODULES:
        receipt = json.loads((PRIVATE / 'audit' / module / 'latest.json').read_text())
        require(receipt['accepted'], 'owner has no accepted receipt')
        require(receipt['replay']['command'] == [CHECKER, '--verbose', module] and
                receipt['replay']['exit_code'] == 0 and receipt['replay']['inputs_unchanged'] and
                receipt['audit']['exit_code'] == 0 and receipt['audit']['inputs_unchanged'],
                'owner replay/audit execution mismatch')
        owner_execution[module] = {'replay_reused': receipt['replay'].get('reused', False),
                                  'audit_reused_this_attempt': summary['modules'][module]['reused']}
        decl_path = next(path for path in receipt['artifacts'] if path.endswith('/declarations.json'))
        owned = json.loads((ROOT / decl_path).read_text())
        names.extend(item['name'] for item in owned['declarations'])
    duplicates = {name: count for name, count in Counter(names).items() if count != 1}
    require(not duplicates, 'new owners have duplicate declarations')
    proof_env = dict(env)
    proof_env['LEAN_PATH'] = str(PRIVATE / 'lib') + ':' + env['LEAN_PATH']
    run([LEAN, '-DwarningAsError=true', '-DmaxRecDepth=50000', '-DmaxHeartbeats=40000000',
         'verification/part2/original96/PublicContract.lean'], 'public-contract', execution_env=proof_env)
    run([LEAN, '-DwarningAsError=true', '-DmaxRecDepth=50000', '-DmaxHeartbeats=40000000',
         'verification/part2/original96/P160DivisionContract.lean'], 'p160-division-contract', execution_env=proof_env)
    run(['python3', '-B', 'verification/part2/original96/check_source_outputs.py', 'inputs'],
        'comparison-inputs', execution_env=proof_env)
    inputs = RECORD / 'comparison-inputs.log'
    require(sha(inputs) == 'c37c7a4903a1a2ac0f6633e72da277a4d7d7929c86b7c3b6c5811b57d1b6d4ac',
            'regenerated comparison input differs from the primary canonical sequence')
    run([LEAN, '--run', 'verification/part2/original96/SourceOutputComparison.lean', str(inputs)],
        'lean-source-outputs', execution_env=proof_env)
    output = RECORD / 'lean-source-outputs.log'
    run(['python3', '-B', 'verification/part2/original96/check_source_outputs.py', 'compare', str(output)],
        'python-source-comparison', execution_env=proof_env)
    comparison = json.loads((RECORD / 'python-source-comparison.log').read_text())
    require(comparison['compared'] == 20290, 'unexpected comparison count')
    final = {'status': 'ACCEPTED_ORIGINAL96_INCREMENT', 'modules': MODULES,
        'owned_declarations': len(names), 'unique_owned_declarations': len(set(names)),
        'duplicate_owned_declarations': duplicates, 'audit': summary,
        'source_comparison': comparison, 'proof_inputs': snapshot(),
        'reviewed_inputs': reviewed, 'owner_execution': owner_execution,
        'freshly_compiled_this_attempt': [line.split()[1] for line in
            (RECORD / 'strict-compile.log').read_text().splitlines() if line.startswith('PASS ')],
        'full_p2_1_complete': False, 'full_p2_complete': False,
        'python_vm_formalized': False, 'python_source_blob': 'ad918b5084fb83ff58d7cbb8cb23fa3e4e47ddce',
        'proof_lean_path': proof_env['LEAN_PATH']}
    (RECORD / 'summary.json').write_text(json.dumps(final, indent=2) + '\n')
    archive = ROOT / f'original96-acceptance-{RECORD.name}.tar.xz'
    with tarfile.open(archive, 'w:xz') as tar:
        for module in [*DEPENDENCIES, *MODULES]:
            rel = module.replace('.', '/') + '.lean'
            tar.add(ROOT / rel, arcname=rel)
        for rel in [
                    'verification/part2/original96', '.lake/p2-private', str(RECORD.relative_to(ROOT)),
                    'docs/verification/20261126-p2-1-original96/source']:
            tar.add(ROOT / rel, arcname=rel)
        for rel in ['run_winner9_private_checks.py', 'run_winner9_private_audit.py',
                    'winner9_private_audit_template.lean', 'inspect_winner9_owner_native.py',
                    'winner9_external_snapshot.py']:
            tar.add(ROOT / 'verification/part2' / rel, arcname='verification/part2/' + rel)
    require(archive.stat().st_size < 1200000, 'archive exceeds bounded stdout transfer budget')
    print('P21_ORIGINAL96_ACCEPTANCE ' + json.dumps(final), flush=True)
    print('P21_ORIGINAL96_ARCHIVE ' + json.dumps({'path': str(archive),
        'bytes': archive.stat().st_size, 'sha256': sha(archive)}), flush=True)
    print('P21_ORIGINAL96_ARCHIVE_BASE64 ' + base64.b64encode(archive.read_bytes()).decode(), flush=True)
except Exception as error:
    (RECORD / 'failure.json').write_text(json.dumps({'error': str(error), 'commands': records}, indent=2) + '\n')
    raise
