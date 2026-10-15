#!/usr/bin/env python3
"""Restore only hash-bound COMPILED prerequisites from one fixed P0 artifact.

Run after bootstrap, before run.py. This does not execute any proof binary.
run.py must still compare each direct imported object signature before reuse;
all requested leaves are excluded so they must compile, replay and audit anew.
"""
from pathlib import Path
import datetime, hashlib, json, shutil, stat, subprocess, sys, zipfile

ROOT = Path(__file__).resolve().parents[4]

def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

def main():
    archive = Path(sys.argv[1]).resolve()
    incoming = ROOT / '.lake/p0-reuse-input'
    anchor_path = ROOT / 'verification/parts/p0/queue/reuse-38674170679.json'
    anchor = json.loads(anchor_path.read_text())
    assert sha(archive) == anchor['artifact_sha256'], 'Wrong original artifact ZIP'
    assert not incoming.exists(), 'Refusing an existing extraction directory'
    with zipfile.ZipFile(archive) as z:
        infos = z.infolist()
        names = [i.filename for i in infos]
        assert len(names) == len(set(names)), 'Duplicate archive entry'
        for info in infos:
            path = Path(info.filename)
            assert not path.is_absolute() and '..' not in path.parts and '\\' not in info.filename
            assert not stat.S_ISLNK(info.external_attr >> 16), 'Archive symlink'
        incoming.mkdir(parents=True)
        for info in infos:
            destination = incoming / info.filename
            if info.is_dir():
                destination.mkdir(parents=True, exist_ok=True)
            else:
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(z.read(info))
    bootstrap = json.loads((ROOT / '.lake/p0-queue/bootstrap/receipt.json').read_text())
    assert bootstrap['status'] == 'PASS_OFFICIAL_CACHE_ONLY'
    assert all(not p.is_symlink() for p in incoming.rglob('*')), 'Artifact contains symlinks'
    index_path = incoming / 'fresh-index.json'
    assert sha(index_path) == anchor['fresh_index_sha256'], 'Wrong artifact index'
    index = json.loads(index_path.read_text())
    receipts = {}
    for relative, expected in anchor['receipt_sha256'].items():
        p = incoming / relative
        assert sha(p) == expected, 'Wrong producer receipt'
        receipt = json.loads(p.read_text())
        if relative != 'bootstrap/receipt.json':
            assert receipt['source_commit'] == anchor['source_commit']
            assert receipt['verifier_sha256']['verification/parts/p0/queue/run.py'] == anchor['producer_runner_sha256']
            receipts[receipt['run_id']] = receipt
    lean = Path(subprocess.check_output(['elan', 'which', 'lean'], text=True).strip())
    lean_sha = sha(lean)
    pins = {p: sha(ROOT / p) for p in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']}
    requests = json.loads((ROOT / 'automation/dispatch.json').read_text())['requests']
    targets = {m for req in requests for m in req['modules']}
    overlay = ROOT / '.lake/p0-queue/fresh-objects'
    destination_index = ROOT / '.lake/p0-queue/fresh-index.json'
    assert not overlay.exists() and not destination_index.exists(), 'Refusing an existing object/index overlay'
    restored = {}
    skipped = {}
    for module, entry in index.items():
        source = bootstrap['target_source_walk'].get(module)
        if module in targets or source is None:
            skipped[module] = 'target must rebuild' if module in targets else 'outside selected source closure'
            continue
        signature = entry['inputs']
        if (signature['source_sha256'] != source['sha256'] or signature['pins'] != pins
                or signature['lean_sha256'] != lean_sha
                or signature['command_policy'] != ['-t0', '-j2', '-M4096']):
            skipped[module] = 'current source/pin/runtime/command identity differs'
            continue
        assert sha(ROOT / source['path']) == source['sha256']
        producer = receipts[entry['producer_run_id']]
        assert entry['replayed'] is False
        assert producer['compiled_objects'][module] == entry['objects']
        stages = [s for s in producer['stages'] if s['label'] == 'compile-' + module]
        assert len(stages) == 1 and stages[0]['exit_code'] == 0
        assert stages[0]['command'][:4] == [str(lean), '-t0', '-j2', '-M4096']
        for original_path, expected in entry['objects'].items():
            destination = Path(original_path)
            relative = destination.relative_to(overlay)
            assert relative.as_posix().startswith(module.replace('.', '/') + '.'), 'Unexpected companion path'
            archived = incoming / 'fresh-objects' / relative
            assert archived.is_file() and sha(archived) == expected, 'Object digest mismatch'
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(archived, destination)
            assert sha(destination) == expected
        entry['producer_ci'] = {k: anchor[k] for k in ['repository', 'run_id', 'attempt', 'source_commit', 'artifact_id', 'artifact_sha256']}
        entry['verification_level'] = 'COMPILED_NOT_REPLAYED'
        restored[module] = entry
    # A candidate with any missing/changed direct object is discarded, as are
    # its dependent candidates. Never let stale overlay files shadow rebuilds.
    while True:
        rejected = [m for m, e in restored.items()
                    if any(not Path(p).is_file() or sha(Path(p)) != h
                           for parts in e['inputs']['dependency_objects'].values()
                           for p, h in parts.items())]
        if not rejected:
            break
        for module in rejected:
            for p in restored[module]['objects']:
                Path(p).unlink()
            del restored[module]
            skipped[module] = 'direct imported object identity differs or is missing'
    overlay.mkdir(parents=True, exist_ok=True)
    destination_index.write_text(json.dumps(restored, indent=2) + '\n')
    receipt = {'status': 'STAGED_COMPILED_PREREQUISITES_ONLY',
               'anchor_sha256': sha(anchor_path), 'script_sha256': sha(Path(__file__)),
               'source_artifact': anchor, 'restored_modules': sorted(restored), 'skipped_modules': skipped,
               'acceptance': 'Not accepted yet: run.py must match each complete direct-import object signature; targets always rebuild/replay/audit.',
               'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    (ROOT / '.lake/p0-queue/reuse-staging.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'restored': len(restored), 'skipped': len(skipped), 'status': receipt['status']}))

if __name__ == '__main__':
    main()
