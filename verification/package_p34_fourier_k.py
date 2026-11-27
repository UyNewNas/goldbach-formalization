"""Package a passed native receipt and bind its source bytes to a Git commit."""
import argparse
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[1]
BASE = '6a91582b56814dd0133a7e36094efabb2f6dcecd'
DOCS = ROOT / 'docs/part3-distribution/p34-fourier-k-20261127'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path, required=True)
    parser.add_argument('--source-commit', required=True)
    args = parser.parse_args()
    receipt = args.receipt.resolve()
    report = json.loads((receipt / 'report.json').read_text())
    if report['status'] != 'PASSED' or report['replayed_module_count'] != 105:
        raise ValueError('Expected the complete passed 105-module supplier receipt')
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
    for name in ('SOURCE_SCOPE.md', 'REVIEW.md'):
        add(name, (DOCS / name).read_bytes())
    packager = 'verification/package_p34_fourier_k.py'
    content = subprocess.check_output(['git', 'show', args.source_commit + ':' + packager], cwd=ROOT)
    if content != Path(__file__).read_bytes():
        raise ValueError('Packager source differs from source commit')
    add('inputs/' + packager, content)
    for path in sorted(receipt.iterdir()):
        if path.is_file():
            add('verification/' + path.name, path.read_bytes())
    for module in report['project_modules']:
        obj = ROOT / '.lake/p34-fourier-k/objects' / (module.replace('.', '/') + '.receipt.json')
        add('object-receipts/' + obj.name, obj.read_bytes())
    for run in sorted((ROOT / '.lake/p34-fourier-k/runs').iterdir()):
        for path in sorted(run.iterdir()):
            if path.is_file():
                add('build-history/' + run.name + '/' + path.name, path.read_bytes())
    for label in ('verification-r1', 'verification-r2'):
        for path in sorted((ROOT / '.lake/p34-fourier-k' / label).glob('*')):
            if path.suffix == '.log' or path.name == 'report.json':
                add('diagnostics/' + label + '/' + path.name, path.read_bytes())
    for name in ('pin-gate-red.log', 'pin-gate-green.log', 'python-suite.log',
                 'python-suite-configured.log', 'python-suite-toolchain.log'):
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
