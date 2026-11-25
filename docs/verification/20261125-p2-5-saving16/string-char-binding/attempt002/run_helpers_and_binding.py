#!/usr/bin/env python3
"""Run two published, independently gated diagnostics and export their evidence."""
from pathlib import Path
import base64
import datetime
import hashlib
import json
import subprocess
import sys

ROOT = Path('/workspace/p25-q96-20261125')
PACKAGE = 'docs/verification/20261125-p2-5-saving16/string-char-binding/attempt002'
LAUNCHER_PATH = PACKAGE + '/run_helpers_and_binding.py'
HELPER_RUNNER = 'docs/source-only/20261125-p2-5-parser-reuse/run-current-parser-reuse.py'
HELPER_SHA = 'e452ff500f3f0ddfa54741c446b100f974a1c12397b83952e9de5e51aabe6b22'
BINDING_RUNNER = PACKAGE + '/run_diagnostic.py'
BINDING_SHA = 'ef3fbe73a7927e1525874bf70be3b5b609059ff48be2ed71ebeb208a350b5f34'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def output(command):
    return subprocess.check_output(command, cwd=ROOT, text=True).strip()


def main():
    publication, previous = sys.argv[1:3]
    for value in [publication, previous]:
        assert len(value) == 40 and all(c in '0123456789abcdef' for c in value)
    assert output(['git', 'rev-parse', 'HEAD']) == previous
    assert not output(['git', 'status', '--porcelain', '--untracked-files=no'])
    subprocess.check_call(['git', 'merge-base', '--is-ancestor', previous, publication], cwd=ROOT)

    def published(path):
        return subprocess.check_output(['git', 'show', publication + ':' + path], cwd=ROOT)

    assert Path(__file__).read_bytes() == published(LAUNCHER_PATH)
    out = ROOT / '.lake/p25-helpers-and-binding-attempt002'
    assert not out.exists()
    out.mkdir(parents=True)
    runners = []
    for name, path, expected in [('helpers.py', HELPER_RUNNER, HELPER_SHA),
                                 ('binding.py', BINDING_RUNNER, BINDING_SHA)]:
        raw = published(path)
        assert sha(raw) == expected
        target = out / name
        target.write_bytes(raw)
        runners.append(target)
    state = {'schema': 'p25-published-helper-and-binding-launcher-v1',
             'publication_commit': publication, 'previous_commit': previous,
             'launcher_sha256': sha(Path(__file__).read_bytes()),
             'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
             'helper_acceptance_independent_of_binding': True,
             'P2_5_proved': False, 'production_binding_credit': False}
    helper_code = subprocess.call([sys.executable, str(runners[0]), publication,
                                   previous, '--attempt', '2'], cwd=ROOT)
    state['helper_runner_exit'] = helper_code
    # The binding runner accepts either the explicit previous or publication
    # HEAD, and rechecks its own fixed source, input and toolchain context.
    binding_code = subprocess.call([sys.executable, str(runners[1]), publication,
                                    previous], cwd=ROOT)
    state['binding_runner_exit'] = binding_code
    state['ended_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    (out / 'RESULT.json').write_text(json.dumps(state, indent=2, sort_keys=True) + '\n')

    paths = set(p for parent in [out,
                ROOT / '.lake/p25-parser-reuse/attempt-002',
                ROOT / '.lake/diagnostic/p25-string-char-binding-attempt002']
                if parent.is_dir() for p in parent.rglob('*') if p.is_file())
    audit_root = ROOT / '.lake/p2-private/audit'
    summary = audit_root / 'p25-parser-reuse-owned-audit.json'
    if summary.is_file():
        paths.add(summary)
    for name in ['P2OriginalSaving19CharInputBridge', 'P2OriginalSaving19SourceJson',
                 'P2OriginalSaving19SourceJsonCharInput', 'P2OriginalSaving19PackedChars']:
        module = audit_root / ('ImbalancedChen.' + name)
        latest = module / 'latest.json'
        if latest.is_file():
            paths.add(latest)
        # Include the newest numbered attempt for each owner; unchanged accepted
        # helpers may reuse an existing receipt, whose binding the driver checks.
        attempts = sorted(p for p in module.glob('attempt-*') if p.is_dir())
        if attempts:
            paths.update(p for p in attempts[-1].rglob('*') if p.is_file())
    ordered = sorted(paths, key=lambda p: (
        0 if p.name in ['RESULT.json', 'latest.json'] else
        1 if p.name.endswith('audit.json') else
        2 if p.suffix in ['.log', '.json', '.txt'] else 3, str(p)))
    manifest, included, omitted = [], [], []
    used = 0
    for path in ordered:
        raw = path.read_bytes()
        row = {'path': str(path.relative_to(ROOT)), 'bytes': len(raw), 'sha256': sha(raw)}
        manifest.append(row)
        if '/lib/' not in str(path) and path.suffix in ['.json', '.log', '.txt', '.lean', '.py'] and used + len(raw) <= 1100000:
            included.append(dict(row, data_base64=base64.b64encode(raw).decode()))
            used += len(raw)
        else:
            omitted.append(row)
    print('P25_HELPER_BINDING_EXPORT_JSON ' + json.dumps({
        'schema': 'p25-helper-binding-attempt002-export-v1',
        'publication_commit': publication, 'state': state,
        'manifest': manifest, 'included_files': included,
        'unexported_files': omitted}, separators=(',', ':')), flush=True)
    return 0 if helper_code == 0 and binding_code == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
