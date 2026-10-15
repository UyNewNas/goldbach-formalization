#!/usr/bin/env python3
"""Restore exact compiled prerequisites from explicitly frozen original ZIPs.

Only each artifact's directly bound successful compile stages supply objects.
Inherited index entries are not producers. Targets always rebuild/replay/audit.
"""
from pathlib import Path
import datetime, hashlib, json, shutil, stat, subprocess, sys, zipfile

ROOT = Path(__file__).resolve().parents[4]
CATALOG = 'verification/parts/p0/queue/reuse-anchors.json'

def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

def extract(archive, incoming, anchor):
    assert sha(archive) == anchor['artifact_sha256'], 'Wrong original artifact ZIP'
    assert not incoming.exists(), 'Refusing an existing extraction directory'
    with zipfile.ZipFile(archive) as z:
        infos = z.infolist()
        names = [i.filename for i in infos]
        assert len(names) == len(set(names)), 'Duplicate archive entry'
        normalized = set()
        for info in infos:
            path = Path(info.filename)
            assert not path.is_absolute() and '..' not in path.parts and '\\' not in info.filename
            assert path.as_posix() not in normalized, 'Normalized archive path collision'
            normalized.add(path.as_posix())
            kind = stat.S_IFMT(info.external_attr >> 16)
            assert kind in (0, stat.S_IFREG, stat.S_IFDIR), 'Non-regular archive entry'
        incoming.mkdir(parents=True)
        for info in infos:
            destination = incoming / info.filename
            if info.is_dir():
                destination.mkdir(parents=True, exist_ok=True)
            else:
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(z.read(info))
    assert all(not p.is_symlink() for p in incoming.rglob('*')), 'Artifact contains symlinks'

def main():
    catalog_path = ROOT / CATALOG
    catalog = json.loads(catalog_path.read_text())
    dispatch = json.loads((ROOT / 'automation/dispatch.json').read_text())
    ids = dispatch.get('reuse_artifact_ids', [])
    assert 1 <= len(ids) <= 3 and len(ids) == len(set(ids)), 'Invalid fixed artifact selection'
    assert len(sys.argv[1:]) == len(ids), 'Missing original artifact archive'
    anchors = [catalog['artifacts'][str(i)] for i in ids]
    bootstrap = json.loads((ROOT / '.lake/p0-queue/bootstrap/receipt.json').read_text())
    assert bootstrap['status'] == 'PASS_OFFICIAL_CACHE_ONLY'
    lean = Path(subprocess.check_output(['elan', 'which', 'lean'], text=True).strip())
    lean_sha = sha(lean)
    pins = {p: sha(ROOT / p) for p in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']}
    targets = {m for req in dispatch['requests'] for m in req['modules']}
    overlay = ROOT / '.lake/p0-queue/fresh-objects'
    destination_index = ROOT / '.lake/p0-queue/fresh-index.json'
    assert not overlay.exists() and not destination_index.exists(), 'Refusing an existing object/index overlay'
    candidates = {}
    skipped = {}
    for ident, anchor, arg in zip(ids, anchors, sys.argv[1:], strict=True):
        assert anchor['artifact_id'] == ident and anchor['repository'] == 'UyNewNas/goldbach-formalization'
        incoming = ROOT / ('.lake/p0-reuse-input-' + str(ident))
        extract(Path(arg).resolve(), incoming, anchor)
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
                assert receipt['run_id'] not in receipts, 'Duplicate producer receipt'
                receipts[receipt['run_id']] = receipt
        for module, entry in index.items():
            key = str(ident) + ':' + module
            source = bootstrap['target_source_walk'].get(module)
            if module in targets or source is None:
                skipped[key] = 'target must rebuild' if module in targets else 'outside selected source closure'
                continue
            if entry['producer_run_id'] not in receipts:
                skipped[key] = 'inherited entry; requires its separate original producer anchor'
                continue
            signature = entry['inputs']
            if (signature['source_sha256'] != source['sha256'] or signature['pins'] != pins
                    or signature['lean_sha256'] != lean_sha
                    or signature['command_policy'] != ['-t0', '-j2', '-M4096']):
                skipped[key] = 'current source/pin/runtime/command identity differs'
                continue
            assert sha(ROOT / source['path']) == source['sha256']
            producer = receipts[entry['producer_run_id']]
            assert entry['replayed'] is False
            assert producer['compiled_objects'][module] == entry['objects']
            stages = [s for s in producer['stages'] if s['label'] == 'compile-' + module]
            assert len(stages) == 1 and stages[0]['exit_code'] == 0
            assert stages[0]['command'][:4] == [str(lean), '-t0', '-j2', '-M4096']
            archived_parts = {}
            for original_path, expected in entry['objects'].items():
                destination = Path(original_path)
                relative = destination.relative_to(overlay)
                assert relative.as_posix().startswith(module.replace('.', '/') + '.'), 'Unexpected companion path'
                archived = incoming / 'fresh-objects' / relative
                assert archived.is_file() and sha(archived) == expected, 'Object digest mismatch'
                archived_parts[original_path] = archived
            assert str(overlay / (module.replace('.', '/') + '.olean')) in entry['objects'], 'Missing primary object'
            provenance = {k: anchor[k] for k in ['repository', 'run_id', 'attempt', 'source_commit', 'artifact_id', 'artifact_sha256']}
            if module in candidates:
                prior = candidates[module]['entry']
                assert prior['inputs'] == signature and prior['objects'] == entry['objects'], 'Conflicting exact producer objects'
                prior['corroborating_producers'].append(provenance)
                continue
            entry['producer_ci'] = provenance
            entry['corroborating_producers'] = [provenance]
            entry['verification_level'] = 'COMPILED_NOT_REPLAYED'
            candidates[module] = {'entry': entry, 'parts': archived_parts}
    restored = {}
    for module, candidate in candidates.items():
        entry = candidate['entry']
        for original_path, archived in candidate['parts'].items():
            destination = Path(original_path)
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(archived, destination)
            assert sha(destination) == entry['objects'][original_path]
        restored[module] = entry
    # Prune the union recursively. An incompatible official or producer object
    # invalidates every dependent candidate instead of leaving a shadow object.
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
            skipped['union:' + module] = 'direct imported object identity differs or is missing'
    overlay.mkdir(parents=True, exist_ok=True)
    destination_index.write_text(json.dumps(restored, indent=2) + '\n')
    receipt = {'status': 'STAGED_COMPILED_PREREQUISITES_ONLY',
               'anchor_sha256': sha(catalog_path), 'script_sha256': sha(Path(__file__)),
               'source_artifacts': anchors, 'restored_modules': sorted(restored), 'skipped_modules': skipped,
               'acceptance': 'No new replay claimed. Historical complete leaf receipts remain valid. run.py checks full direct imports; targets always rebuild/replay/audit.',
               'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    (ROOT / '.lake/p0-queue/reuse-staging.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'restored': len(restored), 'skipped': len(skipped), 'status': receipt['status']}))

if __name__ == '__main__':
    main()
