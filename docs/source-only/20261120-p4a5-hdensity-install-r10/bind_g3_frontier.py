#!/usr/bin/env python3
"""Bind two literal G3 frontier imports to the recorded source-only selection."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
OLD = ROOT / 'docs/source-only/20261119-p4a5-hdensity-install-r8'
G3 = ROOT / 'docs/source-only/20261110-yellow-closure-10t/t05_all22_actual_density/G3_REGISTRY.json'
assert hashlib.sha256(G3.read_bytes()).hexdigest() == 'c0da5890b26433b464fd52cb278e8987b41b70873666bd23edd9bcdbdf63886d'
g3 = json.loads(G3.read_text())
old_audit = json.loads((OLD / 'IMPORT_AUDIT.json').read_text())
manifest = json.loads((OLD / 'INSTALL_MANIFEST.json').read_text())
manifest['baseline'] = '2de9b04a73959081ea84303a0f96bfbe005fad35'
manifest['scope'] = 'partial source-only stage, including two conditional G3 frontier selections; compatibility not established'
rows = []
for leaf in ('P4AOriginalNewFifthMean', 'P4AOriginalNewFifthPhysical'):
    module = 'ImbalancedChen.' + leaf
    selected = [x for x in g3['supplement_sources'] if x.get('module') == module]
    assert len(selected) == 1
    item = selected[0]
    path = item['repository_path']
    target = item['stage_as']
    assert target == 'ImbalancedChen/' + leaf + '.lean'
    assert old_audit['missing_project_modules'][module] == target
    data = (ROOT / path).read_bytes()
    assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256']
    imports = [m.group(1) for line in data.decode('utf-8').splitlines()
               if (m := re.fullmatch(r'\s*import\s+([A-Za-z0-9_.]+)\s*', line))]
    assert imports == item['direct_imports']
    importers = [{'module': name, 'sha256': x['sha256'], 'path': x['path'], 'origin': x['origin']}
                 for name, x in old_audit['visited'].items() if module in x['imports']]
    assert importers
    manifest['records'].append({'source': path, 'target': target, 'sha256': item['sha256'],
        'hash_registry': str(G3.relative_to(ROOT)),
        'selection': 'conditional_original_G3_selection_pending_P4A5_elaboration',
        'selection_evidence': 'prior literal import frontier; original G3 registry path, byte length, SHA and direct imports match; no accepted object'})
    rows.append({'module': module, 'source': path, 'target': target, 'sha256': item['sha256'],
                 'bytes': item['bytes'], 'direct_imports': imports, 'direct_importers': importers})
(HERE / 'INSTALL_MANIFEST.json').write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'scope': 'source identity and literal imports only; no Lean execution',
 'registry': str(G3.relative_to(ROOT)), 'registry_sha256': hashlib.sha256(G3.read_bytes()).hexdigest(),
 'compatibility': 'conditional, uncompiled', 'sources': rows}, indent=2))
