"""Package the 135-module continuation/Fricke receipt and its source commit."""
import argparse
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[1]
BASE = '1613c8c0138ef450429ba94b4f6b207e294e89bd'
DOCS = ROOT / 'docs/part3-distribution/p34-all-level-20261127'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path, required=True)
    parser.add_argument('--source-commit', required=True)
    args = parser.parse_args()
    receipt = args.receipt.resolve()
    report = json.loads((receipt / 'report.json').read_text())
    if report['status'] != 'PASSED' or report['replayed_module_count'] != 135:
        raise ValueError('Expected the complete passed 135-module continuation/Fricke receipt')

    def verify_logs(directory, data):
        for stage in data['stages']:
            log = directory / (stage['name'] + '.log')
            if stage['exit_code'] != 0 or sha(log.read_bytes()) != stage['log_sha256']:
                raise ValueError('Stage log differs from accepted receipt: ' + str(log))

    verify_logs(receipt, report)
    payload = {}

    def add(name, data):
        if name in payload or name.startswith('/') or '..' in Path(name).parts:
            raise ValueError('Invalid or duplicate archive member')
        payload[name] = data

    sources = {}
    for module, binding in report['bindings'].items():
        path = module.replace('.', '/') + '.lean'
        content = subprocess.check_output(['git', 'show', args.source_commit + ':' + path], cwd=ROOT)
        if sha(content) != binding['source_sha256'] or (ROOT / path).read_bytes() != content:
            raise ValueError('Source commit differs from verified bytes: ' + path)
        sources[path] = sha(content)
        add('sources/' + path, content)
    for path, digest in report['verification_input_sha256'].items():
        content = subprocess.check_output(['git', 'show', args.source_commit + ':' + path], cwd=ROOT)
        if sha(content) != digest or (ROOT / path).read_bytes() != content:
            raise ValueError('Verifier commit differs from verified bytes: ' + path)
        add('inputs/' + path, content)
    delta = []
    decl = re.compile(r'^(?:private\s+)?(?:theorem|lemma|def|abbrev|structure|inductive)\s+([^\s(:{]+)', re.M)
    for path in sources:
        before = subprocess.check_output(['git', 'show', BASE + ':' + path], cwd=ROOT)
        after = (ROOT / path).read_bytes()
        if before == after:
            continue
        old, new = before.decode('utf-8-sig'), after.decode('utf-8-sig')
        if decl.findall(old) != decl.findall(new):
            raise ValueError('Production explicit declaration list changed: ' + path)
        delta.append({'path': path, 'baseline_sha256': sha(before), 'current_sha256': sha(after),
                      'source_explicit_names': decl.findall(new),
                      'diff': ''.join(difflib.unified_diff(old.splitlines(True), new.splitlines(True),
                                                         fromfile=BASE + '/' + path, tofile=path))})
    source_binding = {'source_commit': args.source_commit, 'baseline': BASE, 'source_sha256': sources,
                      'source_tree': subprocess.check_output(['git', 'rev-parse',
                          args.source_commit + '^{tree}'], cwd=ROOT, text=True).strip(),
                      'verification_report_sha256': sha((receipt / 'report.json').read_bytes()),
                      'production_files_repaired': len(delta),
                      'note': 'Final source delta; no authenticated historical failed-source snapshot claim'}
    for name, data in [('SOURCE_BINDINGS.json', source_binding), ('SOURCE_DELTA.json', delta)]:
        content = json.dumps(data, ensure_ascii=False, indent=2).encode()
        (DOCS / name).write_bytes(content)
        add(name, content)
    for name in ('SOURCE_SCOPE.md', 'REVIEW.md', 'ACCEPTANCE.md'):
        path = str((DOCS / name).relative_to(ROOT))
        content = subprocess.check_output(['git', 'show', args.source_commit + ':' + path], cwd=ROOT)
        if content != (DOCS / name).read_bytes():
            raise ValueError('Acceptance document differs from source commit: ' + path)
        add(name, content)
    packager = 'verification/package_p34_all_level.py'
    content = subprocess.check_output(['git', 'show', args.source_commit + ':' + packager], cwd=ROOT)
    if content != Path(__file__).read_bytes():
        raise ValueError('Packager source differs from source commit')
    add('inputs/' + packager, content)
    prior = ROOT / '.lake/p34-fourier-k/all-level-verification-r4'
    prior_report = json.loads((prior / 'report.json').read_text())
    if prior_report['status'] != 'PASSED' or prior_report['replayed_module_count'] != 133:
        raise ValueError('Expected the separate completed 133-module receipt')
    verify_logs(prior, prior_report)
    for path, digest in prior_report['verification_input_sha256'].items():
        content = subprocess.check_output(['git', 'show', args.source_commit + ':' + path], cwd=ROOT)
        if sha(content) != digest or content != (ROOT / path).read_bytes():
            raise ValueError('Preceding receipt input differs: ' + path)
        member = 'inputs/' + path
        if member not in payload:
            add(member, content)
    for module, binding in prior_report['bindings'].items():
        if report['bindings'][module]['source_sha256'] != binding['source_sha256'] or \
                report['bindings'][module]['object_sha256'] != binding['object_sha256']:
            raise ValueError('Preceding 133-module object changed: ' + module)
    for path in sorted(prior.iterdir()):
        if path.is_file():
            add('preceding-all-level/' + path.name, path.read_bytes())
    for path in sorted(receipt.iterdir()):
        if path.is_file():
            add('verification/' + path.name, path.read_bytes())
    for module in report['project_modules']:
        obj = ROOT / '.lake/p34-fourier-k/objects' / (module.replace('.', '/') + '.receipt.json')
        state = json.loads(obj.read_text())
        binding = report['bindings'][module]
        if (state['exit_code'] != 0 or state['object_sha256'] != binding['object_sha256']
                or sha(obj.with_suffix('').with_suffix('.olean').read_bytes()) != binding['object_sha256']
                or state['binding']['source_sha256'] != binding['source_sha256']
                or state['binding']['flags'] != binding['strict_flags']
                or state['binding']['fingerprint'] != report['environment']
                or state['log'] != binding['origin_log']
                or sha(Path(state['log']).read_bytes()) != binding['origin_log_sha256']):
            raise ValueError('Current object receipt differs from accepted binding: ' + module)
        for dependency, digest in state['binding']['dependencies'].items():
            if report['bindings'][dependency]['object_sha256'] != digest:
                raise ValueError('Current dependency receipt differs: ' + module)
        add('object-receipts/' + obj.name, obj.read_bytes())
    for run in sorted((ROOT / '.lake/p34-fourier-k/runs').iterdir()):
        run_report = run / 'report.json'
        if not run_report.exists():
            continue
        scope = json.loads(run_report.read_text()).get('order', [])
        if not set(scope).issubset(report['project_modules']):
            continue
        for path in sorted(run.iterdir()):
            if path.is_file():
                add('build-history/' + run.name + '/' + path.name, path.read_bytes())
    for label in ('all-level-verification-r1', 'all-level-verification-r2', 'all-level-verification-r3'):
        for path in sorted((ROOT / '.lake/p34-fourier-k' / label).glob('*')):
            if path.suffix == '.log' or path.name == 'report.json':
                add('diagnostics/' + label + '/' + path.name, path.read_bytes())
    for name in ('all-level-owner-diagnostic.log', 'all-level-owner-all-mismatches.lean',
                 'all-level-owner-all-mismatches.log', 'packager-log-guard-regression.log'):
        add('diagnostics/' + name, (ROOT / '.lake/p34-fourier-k' / name).read_bytes())
    manifest = {name: {'bytes': len(data), 'sha256': sha(data)} for name, data in payload.items()}
    add('ARCHIVE_MEMBERS.json', json.dumps(manifest, indent=2).encode())
    archive = DOCS / 'evidence.zip'
    if archive.exists():
        raise ValueError('Refusing to overwrite an existing evidence archive')
    with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for name, data in sorted(payload.items()):
            z.writestr(name, data)
    with zipfile.ZipFile(archive) as z:
        if z.testzip() is not None or len(z.namelist()) != len(payload):
            raise ValueError('Archive CRC or member count differs')
        for name, info in manifest.items():
            data = z.read(name)
            if sha(data) != info['sha256'] or len(data) != info['bytes']:
                raise ValueError('Archive member differs: ' + name)
    summary = {'archive_bytes': archive.stat().st_size, 'archive_sha256': sha(archive.read_bytes()),
               'payload_members': len(manifest), 'source_commit': args.source_commit,
               'verification_status': report['status']}
    (DOCS / 'ARCHIVE.json').write_text(json.dumps(summary, indent=2))
    verification = DOCS / 'verification'
    verification.mkdir(exist_ok=False)
    for name in ('report.json', 'declarations.json', 'theorem-types.txt'):
        (verification / name).write_bytes((receipt / name).read_bytes())
    print(json.dumps(summary))


if __name__ == '__main__':
    main()
