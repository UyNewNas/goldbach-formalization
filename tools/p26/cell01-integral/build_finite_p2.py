"""Build only absent finite rows on P2 after the selected suppliers qualify."""
import argparse
import json
import os
from pathlib import Path
import shutil

import build_finite_p1 as builder
import qualify_suppliers as qualifier

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-cell01-next-20261128')
BASE = Path('/workspace/p26-cell01-finite-p2-20261128')


def main(rows):
    parent_path = STAGE / 'qualification/RUN.json'
    parent_pin = qualifier.pin(parent_path)
    parent = json.loads(parent_path.read_text())
    assert parent['status'] == 'succeeded' and parent['formal_acceptance']
    context_path = Path(parent['recovered_context']['path'])
    context_pin = qualifier.pin(context_path)
    assert context_pin == parent['recovered_context']
    context = json.loads(context_path.read_text())
    qualifier.validate(context)
    core_path = STAGE / 'verification-core/RUN.json'
    core_pin = qualifier.pin(core_path)
    core = json.loads(core_path.read_text())
    assert core['status'] == 'succeeded' and core['formal_acceptance']
    assert core['qualification_parent'] == parent_pin
    for info in core['project_closure'].values():
        assert qualifier.pin(Path(info['source']['path'])) == info['source']
        obj = info.get('new_object', info.get('reused_object'))
        assert obj is not None and qualifier.pin(Path(obj['path'])) == obj
    manifest_path = BASE / 'MANIFEST.json'
    assert not manifest_path.exists(), 'Freeze each prepared source set; do not change old receipts.'
    BASE.mkdir(exist_ok=True)
    current = BASE / 'selected-base'
    current.mkdir(exist_ok=True)
    for name, target in [('objects', STAGE / 'objects'), ('sources', ROOT)]:
        alias = current / name
        if alias.exists(): assert alias.resolve() == target.resolve()
        else: alias.symlink_to(target, target_is_directory=True)
    objects = BASE / 'objects'
    objects.mkdir(exist_ok=True)
    for item in context['native_artifacts']:
        source = Path(item['path'])
        target = objects / source.relative_to(STAGE / 'objects')
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists(): os.link(source, target)
        assert qualifier.pin(target)['sha256'] == item['sha256']
    imports = STAGE / 'FINITE_IMPORT_TEMPLATE.json'
    shutil.copyfile(imports, BASE / imports.name)
    template = STAGE / 'generic-transport/OwnedAudit.lean'
    raw = template.read_text().replace('ImbalancedChen.P2OriginalSaving19OriginalFloorTransport',
        'ImbalancedChen.P2OriginalSaving19Cell01Row098Finite').replace(
        'P26_ORIGINAL_TRANSPORT_AUDIT', 'P26_GEOMETRY01_AUDIT')
    frozen = BASE / 'OwnedTemplate.lean'
    if frozen.exists(): assert frozen.read_text() == raw
    else: frozen.write_text(raw)
    files = {}
    for row in rows:
        name = f'ImbalancedChen/P2OriginalSaving19Cell01Row{row:03d}Finite.lean'
        source = ROOT / name
        target = BASE / 'project' / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        files['project/' + name] = qualifier.pin(target)
    manifest = {'formal_acceptance': False, 'P2_6_complete': False,
        'source_base_commit': 'f38d08fdcf952b52a7bd97d03158eb89917a21d0',
        'edit': 'Remove precisely unused simp arguments; original declarations, values and ordinals unchanged.',
        'files': files, 'qualification_parent': parent_pin, 'core_parent': core_pin,
        'wrapper_source': qualifier.pin(Path(__file__))}
    manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
    builder.BASE, builder.CURRENT = BASE, current
    builder.OLD = BASE / 'unused-empty-old-base'
    builder.PACKAGES = Path('/workspace/compile-deps/mathlib/.lake/packages')
    builder.EXTRA_SEARCH = [Path('/workspace/compile-deps/mathlib/.lake/build/lib/lean')]
    builder.RUNTIME_LABEL = 'P2'
    builder.main(rows)
    assert qualifier.pin(context_path) == context_pin
    qualifier.validate(context)
    assert qualifier.pin(parent_path) == parent_pin and qualifier.pin(core_path) == core_pin
    assert qualifier.pin(Path(__file__)) == manifest['wrapper_source']
    for info in core['project_closure'].values():
        assert qualifier.pin(Path(info['source']['path'])) == info['source']
        obj = info.get('new_object', info.get('reused_object'))
        assert obj is not None and qualifier.pin(Path(obj['path'])) == obj


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('rows', nargs='+', type=int)
    main(parser.parse_args().rows)
