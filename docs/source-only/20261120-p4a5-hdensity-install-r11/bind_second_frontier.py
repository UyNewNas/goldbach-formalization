#!/usr/bin/env python3
"""Bind six newly exposed literal imports, without asserting variant compatibility."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
BASE = ROOT / 'docs/source-only/20261110-yellow-closure-10t/t05_all22_actual_density'
T04 = ROOT / 'docs/source-only/20261110-yellow-closure-10t/t04_compiler_physical_payment/REGISTRY.json'

def load_checked(path, digest):
    data = path.read_bytes()
    assert hashlib.sha256(data).hexdigest() == digest, str(path)
    return json.loads(data)

g3 = load_checked(BASE / 'G3_REGISTRY.json', 'c0da5890b26433b464fd52cb278e8987b41b70873666bd23edd9bcdbdf63886d')
reg = load_checked(BASE / 'REGISTRY.json', '7242b3ae59e3c171eef6d0366f81824a95d41daaca5c0ea29d2876682bc1e4ea')
t04 = load_checked(T04, '279ed3950cf692f472d4a604cf780a713f709c0b73ff975badf7be1b989b4b82')
previous = load_checked(HERE / 'PHASE1_AUDIT.json', '91870b781fde46ffa4735727dfd514ec6f1248d25695f0b3467db796e9499e89')
manifest = load_checked(HERE / 'PHASE1_INSTALL_MANIFEST.json', 'ca8a2177bec571e9f6737238f9727a7847630d4f742f493f15fd0213ce867078')
manifest['scope'] = 'partial source-only stage; two waves of G3 frontier selections conditional on full compatibility'
leaves = ('Entry3NewFifthTypedOwners', 'P4AFull87CompilerPhysicalPayment',
          'P4AOriginalFull87CompiledCounting', 'P4AOriginalNewFifthArchive',
          'P4AOriginalNewFifthCoverage', 'P5FullArchiveOwnerIntegralAssembly')
rows = []
for leaf in leaves:
    module = 'ImbalancedChen.' + leaf
    if leaf == 'P4AFull87CompilerPhysicalPayment':
        parent = next(x for x in reg['primary_sources'] if x['module'] == 'ImbalancedChen.P4AOriginalFull87JointPhysicalBudget')
        item = next(x for x in parent['direct_imports'] if x['module'] == module)
        registry = BASE / 'REGISTRY.json'
        entry = t04['proofs'][leaf + '.lean']
        assert entry['namespace'] == module
        assert (entry['sha256'], entry['bytes'], entry['install_as']) == (item['sha256'], item['bytes'], 'ImbalancedChen/' + leaf + '.lean')
        declared = entry['imports']
    elif leaf == 'P4AOriginalFull87CompiledCounting':
        item = next(x for x in reg['primary_sources'] if x['module'] == module)
        registry = BASE / 'REGISTRY.json'
        declared = [x['module'] for x in item['direct_imports']]
    elif leaf in ('P4AOriginalNewFifthArchive', 'P4AOriginalNewFifthCoverage'):
        item = next(x for x in g3['supplement_sources'] if x['module'] == module)
        registry = BASE / 'G3_REGISTRY.json'
        declared = item['direct_imports']
    else:
        item = g3['direct_imports_by_module'][module]
        registry = BASE / 'G3_REGISTRY.json'
        declared = None
    path = item['repository_path']
    target = 'ImbalancedChen/' + leaf + '.lean'
    assert previous['missing_project_modules'][module] == target
    data = (ROOT / path).read_bytes()
    assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256']
    actual = [m.group(1) for line in data.decode().splitlines()
              if (m := re.fullmatch(r'\s*import\s+([A-Za-z0-9_.]+)\s*', line))]
    if declared is not None:
        assert actual == declared
    importers = [{'module': name, 'sha256': x['sha256'], 'path': x['path'], 'origin': x['origin']}
                 for name, x in previous['visited'].items() if module in x['imports']]
    assert importers
    manifest['records'].append({'source': path, 'target': target, 'sha256': item['sha256'],
        'hash_registry': str(registry.relative_to(ROOT)),
        'selection': 'conditional_original_G3_selection_pending_P4A5_elaboration',
        'selection_evidence': 'phase-one literal frontier; same-chain exact source identity; no accepted object'})
    rows.append({'module': module, 'source': path, 'target': target, 'bytes': item['bytes'],
                 'sha256': item['sha256'], 'registry': str(registry.relative_to(ROOT)),
                 'direct_imports': actual, 'direct_imports_registry_checked': declared is not None,
                 'direct_importers': importers})
(HERE / 'INSTALL_MANIFEST.json').write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'scope': 'exact source identity and literal imports; no Lean execution',
                 'compatibility': 'conditional, uncompiled', 'sources': rows}, indent=2))
