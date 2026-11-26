#!/usr/bin/env python3
"""One complete 515-module external namespace provider, without compilation."""
from pathlib import Path
import hashlib
import os
import sys
import tarfile

sys.dont_write_bytecode = True
from join_common import need

CONTEXT_PIN = {'bytes': 12878196, 'sha256': 'b36a9153969abb3cbac96c3d74bea3e0c366ca3a673cdfe7456a7e655f2241c0'}
COUNTS = {'MathlibNt': 444, 'AnalyticNumberTheory': 44, 'Architect': 9, 'PrimeNumberTheoremAnd': 18}
GOLDBACH = Path('/workspace/goldbach-p3/.lake/packages/goldbach/.lake/build/lib/lean')
ARCHITECT = Path('/workspace/goldbach-p3/.lake/packages/LeanArchitect/.lake/build/lib/lean')
P3_ROOTS = {namespace: ARCHITECT if namespace == 'Architect' else GOLDBACH for namespace in COUNTS}
MISSING = {
    'MathlibNt.SieveTheory.LiLiuGoldbachB10RosserFactor',
    'MathlibNt.SieveTheory.LiLiuGoldbachB8RosserFactor',
    'MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiChenAdaptiveDepthAbsorption',
    'MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiChenParameterBridge',
    'MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiDensityBoundingSieveBridge',
    'MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma147JurkatRichertInterval',
    'MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserAllDepth',
    'MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserDensityEndpointDirect',
    'MathlibNt.SieveTheory.SuzukiClaim145SourceParameters',
    'MathlibNt.SieveTheory.SuzukiUpperRosserDensityEndpointDirect',
}


def selected_context(rows):
    selected = {r['module']: r for r in rows if r['module'].split('.')[0] in COUNTS}
    need(len({r['module'] for r in rows}) == len(rows) and len(selected) == 515
         and all(sum(name.split('.')[0] == namespace for name in selected) == count
                 for namespace, count in COUNTS.items()) and MISSING <= set(selected),
         'External provider must contain the complete accepted 515-module namespace selection')
    return selected


def capsule_bytes(F, cfg, selected, frozen):
    archive = frozen.add(cfg['archive']['path'], cfg['archive'])
    manifest = frozen.add(cfg['manifest']['path'], cfg['manifest'])
    meta = F.read(manifest['path'])
    need(meta['schema'] == 'p26_cell01_external10_runtime_capsule_v1'
         and F.same(meta['original_context'], CONTEXT_PIN)
         and meta['module_count'] == 10 and meta['object_bytes'] == 2193920
         and meta['sidecar_files'] == 0 and meta['row001_files_included'] is False
         and meta['source_receipt_log_bodies_included'] is False
         and meta['Lean_commands'] == meta['new_proof_credit'] == 0,
         'Unexpected ten-object external capsule authority or scope')
    modules = {row['module']: row for row in meta['modules']}
    need(len(meta['modules']) == len(modules) == 10 and set(modules) == MISSING
         and all(modules[name] == selected[name] and selected[name]['sidecars'] == [] for name in MISSING),
         'Transferred external object does not equal the original accepted module context')
    expected = {}
    for row in meta['members']:
        name = row['module']
        member = 'objects/' + str(F.relative(name))
        need(name in MISSING and row['member'] == member and member not in expected
             and row['original'] == selected[name]['object'], 'Unexpected external capsule member')
        expected[member] = row['original']
    need(len(expected) == 10, 'Incomplete ten-object capsule inventory')
    expected['MANIFEST.json'] = manifest
    payload = {}
    with tarfile.open(archive['path'], 'r:xz') as stream:
        for item in stream:
            need(item.isfile() and item.name in expected and item.name not in payload
                 and item.size == expected[item.name]['bytes'], 'Unsafe or changed external capsule member')
            data = stream.extractfile(item).read()
            need((len(data), hashlib.sha256(data).hexdigest()) ==
                 (expected[item.name]['bytes'], expected[item.name]['sha256']), 'External capsule body pin differs')
            payload[item.name] = data
    need(set(payload) == set(expected), 'Incomplete external capsule body readback')
    return payload, archive, manifest


def materialize(F, destination, marker, planned, blobs, frozen):
    """Existing complete files are read-only; partial or changed state stops."""
    destination = F.canonical(destination)
    completed = destination / 'PROVIDER.json'
    if destination.exists():
        need(completed.is_file(), 'PARTIAL_EXTERNAL_PROVIDER_REQUIRES_INSPECTION')
        need(F.read(completed) == marker, 'External provider belongs to another immutable input set')
    else:
        destination.mkdir(parents=True)
        for row in planned:
            path = F.within(destination, destination / row['member'])
            path.parent.mkdir(parents=True, exist_ok=True)
            F.canonical(path)
            if row['method'] == 'hardlink_existing_P3':
                F.pinned(row['source']['path'], row['accepted'])
                os.link(row['source']['path'], path)
            else:
                need(row['method'] == 'exact_P1_capsule_body', 'Unknown external install method')
                with path.open('xb') as stream:
                    stream.write(blobs[row['capsule_member']])
            frozen.add(path, row['accepted'])
        # A marker is written only after every planned body has been checked.
        for row in planned:
            F.pinned(destination / row['member'], row['accepted'])
        F.write(destination, completed, marker)
    actual = set()
    for path in destination.rglob('*'):
        F.canonical(path, True)
        if path.is_file():
            actual.add(path.relative_to(destination).as_posix())
    need(actual == {row['member'] for row in planned} | {'PROVIDER.json'},
         'External provider has missing or unmanifested files')
    for row in planned:
        frozen.add(destination / row['member'], row['accepted'])
    frozen.add(completed)
    return destination


def install(F, cfg, context_current, frozen):
    current = frozen.add(context_current['path'], CONTEXT_PIN)
    selected = selected_context(F.read(current['path']))
    destination = F.canonical(cfg['destination'])
    for root in set(P3_ROOTS.values()):
        F.canonical(root, True)
        F.disjoint(destination, root)
    for role in ('archive', 'manifest'):
        F.disjoint(destination, Path(cfg[role]['path']).parent)
    payload, archive, capsule_manifest = capsule_bytes(F, cfg, selected, frozen)
    planned = []
    for module, accepted in sorted(selected.items()):
        relative = F.relative(module)
        original = Path(accepted['object']['path'])
        need(str(original).endswith('/' + str(relative)), 'Accepted external object suffix differs')
        declared = {ref['path']: ref for ref in accepted['sidecars']}
        need(len(declared) == len(accepted['sidecars']) and
             set(declared) <= {str(p) for p in F.V.sidecar_paths(original)}, 'Unknown accepted external sidecar')
        if module in MISSING:
            need(not declared, 'Ten restored original modules must have no sidecars')
            planned.append({'module': module, 'member': str(relative), 'accepted': accepted['object'],
                            'method': 'exact_P1_capsule_body', 'capsule_member': 'objects/' + str(relative)})
            continue
        source = F.canonical(P3_ROOTS[module.split('.')[0]] / relative, True)
        current_sides = [F.fp(p) for p in F.V.sidecar_paths(source) if p.exists() or p.is_symlink()]
        need(F.sidecar_signature(current_sides) == F.sidecar_signature(accepted['sidecars']),
             'Existing external sidecars differ from the accepted context')
        pairs = [(source, relative, accepted['object'])]
        for old in accepted['sidecars']:
            suffix = next(s for s in ('.olean.server', '.olean.private', '.ir') if old['path'].endswith(s))
            member = Path(module.replace('.', '/') + suffix)
            pairs.append((P3_ROOTS[module.split('.')[0]] / member, member, old))
        for path, member, ref in pairs:
            actual = frozen.add(path, ref)
            planned.append({'module': module, 'member': str(member), 'accepted': ref,
                            'method': 'hardlink_existing_P3', 'source': actual})
    need(len({row['member'] for row in planned}) == len(planned)
         and len({row['module'] for row in planned}) == 515
         and sum(row['method'] == 'exact_P1_capsule_body' for row in planned) == 10,
         'Incomplete or conflicting combined external provider')
    marker = {'schema': 'p26_cell01_complete515_external_provider_v1',
              'accepted_context': current, 'capsule_archive': archive, 'capsule_manifest': capsule_manifest,
              'namespace_counts': COUNTS, 'module_count': 515, 'existing_P3_modules': 505,
              'transferred_P1_modules': 10, 'members': planned, 'Lean_commands': 0, 'new_proof_credit': 0}
    root = materialize(F, destination, marker, planned, payload, frozen)
    need(not (root / 'ImbalancedChen').exists(), 'Project namespace in external-only provider')
    current_rows = F.V.module_byte_context(list(selected), [root])
    need(len(current_rows) == 515 and all(F.same(row['object'], selected[row['module']]['object'])
         and F.sidecar_signature(row['sidecars']) == F.sidecar_signature(selected[row['module']]['sidecars'])
         for row in current_rows), 'Combined provider does not resolve all 515 accepted module bytes')
    return root
