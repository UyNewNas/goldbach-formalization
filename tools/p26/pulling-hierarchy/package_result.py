"""Package only the verified generic and original Cell05 hierarchy pilot."""
import hashlib
import io
import json
from pathlib import Path
import shutil
import tarfile

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-cell00-next-20261128')
OUT = ROOT / 'docs/verification/20261128-p26-grouped-separation'
NAMES = {'ImbalancedChen.P2OriginalSaving19GroupedSeparation',
         *{'ImbalancedChen.P2OriginalSaving19Cell05GroupedSeparation' + x
           for x in ['Data', 'Signs', 'Complete']}}


def pin(path):
    raw = path.read_bytes()
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def checked(item):
    path = Path(item['path'])
    assert pin(path) == {k: item[k] for k in ['bytes', 'sha256']}
    return path


def main():
    parent = ROOT / 'docs/verification/20261128-p26-cell00-integral/CAPSULE.json'
    parent_data = json.loads(parent.read_text())
    assert parent_data['formal_acceptance']
    OUT.mkdir(parents=True, exist_ok=True)
    owners, declarations, catalog, phases = {}, [], {}, {}
    receipt_paths = []
    for phase in ['grouped', 'grouped05']:
        folder = STAGE / ('verification-' + phase)
        receipt = folder / 'RUN.json'
        run = json.loads(receipt.read_text())
        assert run['status'] == 'succeeded' and run['formal_acceptance']
        assert run['P2_6_complete'] is False
        assert all(c['exit_code'] == 0 for c in run['commands'])
        target = OUT / phase
        target.mkdir(exist_ok=True)
        shutil.copyfile(receipt, target / 'RUN.json')
        shutil.copyfile(folder / 'owned-declarations.json', target / 'owned-declarations.json')
        for c in run['commands']:
            path = checked(c['log'])
            shutil.copyfile(path, target / path.name)
        for module, count in run['owned_counts'].items():
            assert module not in owners
            owners[module] = count
        items = json.loads((folder / 'owned-declarations.json').read_text())
        assert len(items) == run['owned_declarations']
        declarations.extend(items)
        for module, info in run['project_closure'].items():
            checked(info['source'])
            obj = info.get('new_object', info.get('reused_object'))
            assert obj is not None
            checked(obj)
            if module in catalog:
                assert info['source'] == catalog[module]['source']
                prior = catalog[module].get('new_object', catalog[module].get('reused_object'))
                assert {k: obj[k] for k in ['bytes', 'sha256']} == {k: prior[k] for k in ['bytes', 'sha256']}
            catalog[module] = info
        phases[phase] = pin(target / 'RUN.json')
        receipt_paths.append(receipt)
    assert set(owners) == NAMES
    assert not any(m.startswith('ImbalancedChen.P2OriginalSaving19Cell05Separation') for m in catalog)
    assert len(declarations) == len({d['name'] for d in declarations})
    for d in declarations:
        assert not (d['unsafe'] or d['partial'] or d['axiom'])
        assert set(d['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
        assert '⋯' not in d['type']
    external = STAGE / 'FINAL_EXTERNAL_READBACK.json'
    assert external.stat().st_mtime >= max(p.stat().st_mtime for p in receipt_paths)
    data = json.loads(external.read_text())
    assert data['status'] == 'matched' and not data['problems']
    assert pin(external) == parent_data['final_external_readback']
    shutil.copyfile(external, OUT / external.name)
    proposal = STAGE / 'PULLING_FORMS_05.json'
    p = json.loads(proposal.read_text())
    assert p['formal_acceptance'] is False and p['rows'] == 56
    assert len(p['nodes']) == 49 and len(p['forms']) == 45
    assert sum(len(n['separators']) for n in p['nodes']) == 61
    shutil.copyfile(proposal, OUT / 'CELL05_ADVISORY_PROPOSAL.json')
    advisory = json.loads((STAGE / 'PULLING_PROPOSAL_CAPSULE.json').read_text())
    assert advisory['formal_acceptance'] is False
    archive_source = checked(advisory['archive'])
    shutil.copyfile(archive_source, OUT / archive_source.name)
    shutil.copyfile(STAGE / 'PULLING_PROPOSAL_CAPSULE.json', OUT / 'ALL13_ADVISORY_CAPSULE.json')
    archive = OUT / 'project-objects.tar.xz'
    members = {}
    for module in sorted(NAMES):
        info = catalog[module]
        obj = info.get('new_object', info.get('reused_object'))
        members['objects/' + module.replace('.', '/') + '.olean'] = checked(obj)
    with tarfile.open(archive, 'w:xz', preset=6) as tar:
        for name, path in sorted(members.items()):
            raw = path.read_bytes()
            info = tarfile.TarInfo(name)
            info.size, info.mode, info.mtime = len(raw), 0o644, 0
            tar.addfile(info, io.BytesIO(raw))
    with tarfile.open(archive, 'r:xz') as tar:
        assert len(tar.getmembers()) == 4
        for entry in tar:
            assert tar.extractfile(entry).read() == members[entry.name].read_bytes()
    (OUT / 'owned-declarations.json').write_text(json.dumps(declarations, indent=2) + '\n')
    result = {'schema': 'p26_original_cell05_grouped_separation_v1',
              'formal_acceptance': True, 'P2_6_complete': False,
              'original_full_snapshot_verified': False,
              'scope': 'Generic rational sibling-group composition and all-pairs almost-everywhere disjointness of all56 original Cell05 physical simplices through49 nodes and61 closed sibling witnesses.',
              'new_modules': 4, 'owned_declarations': len(declarations),
              'normal_commands': 4, 'stock_kernel_commands': 4, 'full_owned_audits': 2,
              'original_rows': 56, 'branching_nodes': 49, 'sibling_pairs': 61, 'forms': 45,
              'original_quadratic_pair_certificate_imported': False,
              'other_original_families_accepted': False,
              'all13_host_proposal_is_formal_proof': False,
              'project_closure_modules': len(catalog),
              'archive': {'name': archive.name, **pin(archive)},
              'qualified_context_parent': pin(parent), 'phases': phases,
              'owned_inventory': pin(OUT / 'owned-declarations.json'),
              'final_external_readback': pin(external), 'packager_source': pin(Path(__file__))}
    (OUT / 'CAPSULE.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result), flush=True)


if __name__ == '__main__': main()
