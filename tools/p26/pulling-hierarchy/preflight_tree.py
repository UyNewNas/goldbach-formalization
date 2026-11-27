"""Advisory exact original pulling-tree reconstruction; no Lean credit."""
import hashlib
import json
from pathlib import Path

ROOT = Path('/workspace/p26-proof-continuation-20261127')
ledger = json.loads((ROOT / 'docs/verification/20261125-p26/ORIGINAL_INPUT_SCALE.json').read_text())
results = []
for source in ledger['all_inputs']:
    if source['family'] != 'geometry':
        continue
    raw = Path(source['resolved_actual_path']).read_bytes()
    assert len(raw) == source['bytes'] and hashlib.sha256(raw).hexdigest() == source['sha256']
    data = json.loads(raw)
    faces = {tuple(sorted(f['vertices'])): f for f in data['face_ledger']}
    assert len(faces) == len(data['face_ledger'])
    rows = {tuple(sorted(r['vertex_ids'])): i for i, r in enumerate(data['simplices'])}
    assert len(rows) == len(data['simplices'])
    stats = {'nodes': 0, 'leaves': 0, 'branch_pairs': 0, 'max_children': 0}
    selected = []

    def walk(vertices, ancestors):
        assert len(ancestors) <= 8
        if len(vertices) == 1:
            ids = tuple(sorted(ancestors + vertices))
            assert len(ids) == len(set(ids)) == 9
            selected.append(rows[ids])
            stats['leaves'] += 1
            return
        face = faces[vertices]
        assert face['dimension'] == 8 - len(ancestors)
        pivot = face['pivot']
        assert pivot in vertices
        children = [tuple(sorted(f)) for f in face['facet_sets'] if pivot not in f]
        assert children and all(len(c) < len(vertices) and set(c) <= set(vertices) for c in children)
        stats['nodes'] += 1
        stats['max_children'] = max(stats['max_children'], len(children))
        stats['branch_pairs'] += len(children) * (len(children) - 1) // 2
        for child in children:
            walk(child, ancestors + (pivot,))

    walk(tuple(range(len(data['vertices']))), ())
    assert len(selected) == len(rows) and sorted(selected) == list(range(len(rows)))
    results.append({'cell': source['cell'], **stats,
                    'all_simplex_pairs': len(rows) * (len(rows) - 1) // 2,
                    'exact_original_leaf_cover': True, 'source': source,
                    'formal_acceptance': False})
out = Path('/workspace/p26-cell00-next-20261128/PULLING_TREE_PREFLIGHT.json')
out.write_text(json.dumps({'formal_acceptance': False, 'cells': results}, indent=2) + '\n')
print(json.dumps([{k: v for k, v in x.items() if k != 'source'} for x in results], indent=2))
