#!/usr/bin/env python3
"""Stage the hash-selected subset in an empty external directory; audit literal imports.

This does not install a toolchain, copy all dependencies, elaborate Lean, or
assert that the checkout's other modules match their own provenance pins.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
MANIFEST = Path(__file__).with_name('INSTALL_MANIFEST.json')

def digest(data):
    return hashlib.sha256(data).hexdigest()

def checked(path, expected):
    data = (ROOT / path).read_bytes()
    actual = digest(data)
    if actual != expected:
        raise ValueError(f'{path}: expected {expected}, got {actual}')
    return data

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('stage', type=Path, help='new, empty directory outside checkout')
    args = ap.parse_args()
    stage = args.stage.resolve()
    if stage == ROOT or ROOT in stage.parents:
        raise ValueError('stage must be outside the checkout')
    if stage.exists() and any(stage.iterdir()):
        raise ValueError('stage must be empty')
    stage.mkdir(parents=True, exist_ok=True)
    manifest = json.loads(MANIFEST.read_text())
    targets = set()
    for item in manifest['records']:
        target = Path(item['target'])
        if target in targets or target.is_absolute() or '..' in target.parts:
            raise ValueError(f'invalid or duplicate target: {target}')
        targets.add(target)
        if 'hash_registry' in item and item['sha256'] not in (ROOT / item['hash_registry']).read_text():
            raise ValueError(f"registry does not bind source hash: {item['source']}")
        data = checked(item['source'], item['sha256'])
        dst = stage / target
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_bytes(data)
    overlay = manifest['namespace_overlay']
    checked(overlay['patch'], overlay['patch_sha256'])
    data = checked(overlay['source'], overlay['source_sha256'])
    before = (b'open P1OriginalVariableFourthContinuation (finiteMax)\n'
              b'open P2OriginalFourthCapProducerInterface (producerEligible)')
    after = b'open P1OriginalVariableFourthContinuation (finiteMax producerEligible)'
    if data.count(before) != 1:
        raise ValueError('namespace overlay context is not unique')
    data = data.replace(before, after)
    if digest(data) != overlay['target_sha256']:
        raise ValueError('namespace overlay output hash mismatch')
    dst = stage / overlay['target']
    if dst.exists():
        raise ValueError('duplicate namespace overlay target')
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_bytes(data)
    # Verify that the two staged List-scope files are exactly the reviewed
    # overlays of their original sources, and that the recorded patch is intact.
    list_patch = 'docs/source-only/20261112-resume/t03/EARLY_LIST_SCOPE.patch'
    checked(list_patch, '3b3031443bdbb6aa34dab65fe58b07c62ad8363e389f1a684e7f533d736582b3')
    originals = {
        'P4AOriginalEarlyTupleCarriers.lean': '0a84e536f8a2308eaa1db6b98631e97d8cdbbc90248eb118e0f5eaf7222d17fc',
        'P4AOriginalEarlyTupleComparison.lean': '0ae717c64d9bfe7c077a698428cfc70d43de0537fa9705e409d715cadfb2c7ec',
    }
    for name, sha in originals.items():
        source = 'docs/source-only/20261110-yellow-closure-10t/t03_saved87_actual_gain/successor_early_135/' + name
        original = checked(source, sha)
        before = b'open scoped Classical BigOperators\n'
        if original.count(before) != 1:
            raise ValueError(f'List overlay context is not unique: {name}')
        expected = original.replace(before, b'open scoped Classical BigOperators List\n')
        if expected != (stage / 'ImbalancedChen' / name).read_bytes():
            raise ValueError(f'List overlay mismatch: {name}')
    # Walk literal imports. A root path's existence is NOT a version/olean check.
    pending = ['ImbalancedChen.P4AOriginalFiniteAll22FineDensity']
    visited, missing, external = {}, {}, set()
    while pending:
        module = pending.pop()
        if module in visited or module in missing:
            continue
        if not module.startswith('ImbalancedChen.'):
            external.add(module)
            continue
        rel = Path(*module.split('.')).with_suffix('.lean')
        src = stage / rel if (stage / rel).is_file() else ROOT / rel
        if not src.is_file():
            missing[module] = str(rel)
            continue
        content = src.read_text()
        imports = []
        for line in content.splitlines():
            match = re.match(r'^\s*import\s+([A-Za-z0-9_\. ]+)', line)
            if match:
                imports.extend(match.group(1).split())
        visited[module] = {'origin': 'stage' if stage in src.parents else 'checkout',
                           'path': str(src.relative_to(stage if stage in src.parents else ROOT)),
                           'sha256': digest(src.read_bytes()), 'imports': imports}
        pending.extend(imports)
    print(json.dumps({'staged_count':len(targets)+1, 'visited_project_modules':len(visited),
                      'missing_project_modules':missing, 'external_modules':sorted(external),
                      'visited':visited},indent=2,ensure_ascii=False,sort_keys=True))

if __name__ == '__main__':
    main()
