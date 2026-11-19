#!/usr/bin/env python3
"""Bind the three actual next imports to the registered G3 source versions."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
OLD = ROOT / 'docs/source-only/20261120-p4a5-hdensity-install-r10'
BASE = ROOT / 'docs/source-only/20261110-yellow-closure-10t/t05_all22_actual_density'
registries = {'G3_REGISTRY.json': 'c0da5890b26433b464fd52cb278e8987b41b70873666bd23edd9bcdbdf63886d',
              'REGISTRY.json': '7242b3ae59e3c171eef6d0366f81824a95d41daaca5c0ea29d2876682bc1e4ea'}
for name, sha in registries.items():
    assert hashlib.sha256((BASE / name).read_bytes()).hexdigest() == sha
G3 = json.loads((BASE / 'G3_REGISTRY.json').read_text())
REG = json.loads((BASE / 'REGISTRY.json').read_text())
previous = json.loads((OLD / 'IMPORT_AUDIT.json').read_text())
manifest = json.loads((OLD / 'INSTALL_MANIFEST.json').read_text())
manifest['baseline'] = '0cdc909bad0d65fbb6761c7bbc46aa95a4e935d6'
manifest['scope'] = 'partial source-only stage; three new registry-bound frontier selections conditional on full compatibility'
rows = []
for leaf in ('P4AOriginalNewFifthOwners', 'P4AOriginalNewFifthIntegral', 'P4AOriginalFull87JointPhysicalBudget'):
    module = 'ImbalancedChen.' + leaf
    if leaf == 'P4AOriginalFull87JointPhysicalBudget':
        chosen = [x for x in REG['primary_sources'] if x.get('module') == module]
        registry = 'REGISTRY.json'
    else:
        chosen = [x for x in G3['supplement_sources'] if x.get('module') == module]
        registry = 'G3_REGISTRY.json'
    assert len(chosen) == 1
    item = chosen[0]
    path, target = item['repository_path'], item['stage_as']
    assert target == 'ImbalancedChen/' + leaf + '.lean'
    assert previous['missing_project_modules'][module] == target
    data = (ROOT / path).read_bytes()
    assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256']
    declared = [v if isinstance(v, str) else v['module'] for v in item['direct_imports']]
    actual = [m.group(1) for line in data.decode('utf-8').splitlines()
              if (m := re.fullmatch(r'\s*import\s+([A-Za-z0-9_.]+)\s*', line))]
    assert actual == declared
    if leaf == 'P4AOriginalFull87JointPhysicalBudget':
        exact = G3['direct_imports_by_module'][module]
        assert (exact['sha256'], exact['bytes'], exact['repository_path']) == (item['sha256'], item['bytes'], path)
    importers = [{'module': name, 'sha256': x['sha256'], 'path': x['path'], 'origin': x['origin']}
                 for name, x in previous['visited'].items() if module in x['imports']]
    assert importers
    manifest['records'].append({'source': path, 'target': target, 'sha256': item['sha256'],
        'hash_registry': str((BASE / registry).relative_to(ROOT)),
        'selection': 'conditional_original_G3_selection_pending_P4A5_elaboration',
        'selection_evidence': 'previous literal frontier; same-chain exact path, length, SHA and direct imports; no accepted object'})
    rows.append({'module': module, 'source': path, 'target': target, 'bytes': item['bytes'],
                 'sha256': item['sha256'], 'registry': str((BASE / registry).relative_to(ROOT)),
                 'direct_imports': actual, 'direct_importers': importers})
(HERE / 'PHASE1_INSTALL_MANIFEST.json').write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'scope': 'exact source identity and literal imports; no Lean execution',
                 'registry_sha256': registries, 'compatibility': 'conditional, uncompiled', 'sources': rows}, indent=2))
