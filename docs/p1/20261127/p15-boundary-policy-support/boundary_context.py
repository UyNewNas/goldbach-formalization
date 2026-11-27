"""Read the actual accepted Coefficient owner and reuse the 53 old inputs.

This helper executes no compiler, worker, install, build or cloud operation.
The caller must supply real original Coefficient adapter/PASS/readonly pins.
The 13 added modules keep the original Dictionary source and full 21-position
artifact bindings. The new Boundary graph is 56 dependencies plus one target.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import sys
from types import ModuleType, SimpleNamespace

sys.dont_write_bytecode = True
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
COEFFICIENT = 'ImbalancedChen.P1SignedExitCoefficientDifference'
TARGET = 'ImbalancedChen.P1HistoricalBoundaryPolicyDifferenceSupport'
NAME = 'P1HistoricalBoundaryPolicyDifferenceSupport.lean'
LIVE = 'ImbalancedChen/' + NAME
SOURCE_PIN = {'bytes': 20316, 'sha256': '7ac7742c3a9ada5d3a8f1e5c6e37526b5acc7d6d89d791cd61387f06fcb9b9c2'}
IMPORTS = [COEFFICIENT, 'ImbalancedChen.FirstExitValidSelection', 'ImbalancedChen.HistoricalPrefixCertificate']
EXTENSION_SOURCE_PINS = {'ImbalancedChen.ActualSelectedPrefixCapSelector': {'bytes': 12043,
                                                    'sha256': '3a96c94bd454cb3cdaa59970eb032474337b97db53680cf7f6fa5d00415a9aa8'},
 'ImbalancedChen.BufferedFirstCubeGeometry': {'bytes': 6401,
                                              'sha256': 'be65e75cc81b6d1275dde681e0de1a95add9da3ab18949b94f8595c6c3c6829c'},
 'ImbalancedChen.CompactLocalThreshold': {'bytes': 1841,
                                          'sha256': 'bac41a819e3196063b2e28fa390dc0a5ba22fa75cb88d93687f1cc63ccbba4d6'},
 'ImbalancedChen.HistoricalPrefixCertificate': {'bytes': 21277,
                                                'sha256': 'b66bb9aae758648095779c507a20172e8ef9eee3f9647bf8c0b847c8a28ccfa9'},
 'ImbalancedChen.SelectedPrefixBoxCap': {'bytes': 17651,
                                         'sha256': 'a6cc561425e128c917a3dc0511bc8095befac404b40a6dee04e6a2612ac75e55'},
 'ImbalancedChen.SelectedPrefixCompactCaps': {'bytes': 3030,
                                              'sha256': '9d36a74fe7cad9ff9b1e4edd91fa872d5c7553eaadd6161385e1877e1c884937'},
 'ImbalancedChen.SelectedPrefixRationalMesh': {'bytes': 7628,
                                               'sha256': '89d6fb42f80ec67075febcb3b1f11a9f6915c02074d45c398ede962c30ad0c3a'},
 'ImbalancedChen.VariableEnvelope': {'bytes': 7292,
                                     'sha256': 'ec0fc1a6099e6667015e90306d18cf05b43c556ef8ad8e2f99c91f967e0f4b8c'},
 'ImbalancedChen.VariableEnvelopeBoxes': {'bytes': 11246,
                                          'sha256': 'a564a26ca50503c595e4ec8722baea77d6e390ad03f063afe6c36ba164bd36cc'},
 'ImbalancedChen.VariableEnvelopeCertificates': {'bytes': 15185,
                                                 'sha256': '20eb454668f0121d5cbc969eb6e7fc5307f2eee03c60fab976c1064347a89c36'},
 'ImbalancedChen.VariableEnvelopeConsequences': {'bytes': 5763,
                                                 'sha256': '0ebf8e9ad18fccd621c53f4db1968927e99cc9a1ac5ea4ff68e8cb9cb01b8b54'},
 'ImbalancedChen.VariableEnvelopeRegularity': {'bytes': 7653,
                                               'sha256': 'c91fda06f64c413f3136986dff1ef9367ad3f692d28dd78927eed993d1446d8c'},
 'ImbalancedChen.VariableEnvelopeScaled': {'bytes': 10884,
                                           'sha256': '4f5873c8f4edeec34dd458e21b351f73098a04e33bb1828fc3b639a3e8e7a787'}}
EXTENSION_INVENTORY_PIN = {'bytes': 29870, 'sha256': '9fed3397a7ee4ac8689a12638fdd30fe76d0ece245c579792f780c56f366d4f9'}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def fingerprint(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def canonical_pin(value):
    return fingerprint(json.dumps(value, sort_keys=True, separators=(',', ':'),
                                  ensure_ascii=False).encode())


def regular(path):
    need(path.is_file() and not path.is_symlink() and path.resolve() == path,
         'expected original regular file: ' + str(path))
    return path.read_bytes()


def valid_pin(row):
    return (isinstance(row, dict) and set(row) == {'path', 'bytes', 'sha256'} and
            isinstance(row['path'], str) and Path(row['path']).is_absolute() and
            type(row['bytes']) is int and row['bytes'] > 0 and
            isinstance(row['sha256'], str) and re.fullmatch('[0-9a-f]{64}', row['sha256']))


def bound(row):
    need(valid_pin(row), 'actual parent file path/bytes/SHA256 required')
    raw = regular(Path(row['path']))
    need(fingerprint(raw) == {key: row[key] for key in ('bytes', 'sha256')},
         'original Coefficient receipt/adapter changed')
    return raw


def load(binding, source_commit):
    # Do not guess a future acceptance identity or execute before it exists.
    need(isinstance(binding, dict) and set(binding) ==
         {'source_commit', 'adapter', 'formal_pass', 'readonly_receipt'} and
         isinstance(binding['source_commit'], str) and
         re.fullmatch('[0-9a-f]{40}', binding['source_commit']) and
         all(valid_pin(binding[key]) for key in ('adapter', 'formal_pass', 'readonly_receipt')) and
         isinstance(source_commit, str) and re.fullmatch('[0-9a-f]{40}', source_commit),
         'actual accepted Coefficient identity and exact Boundary source commit required')
    commit = binding['source_commit']
    adapter = ROOT / commit / 'published-entrypoints/run_coefficient.py'
    need(binding['adapter']['path'] == str(adapter) and
         binding['formal_pass']['path'] == str(ROOT / commit / 'signed-exit-coefficient-operation/PASS.json'),
         'original Coefficient identity/receipt routes must be retained')
    raw = bound(binding['adapter'])
    parent = ModuleType('original_coefficient_acceptance')
    parent.__file__ = str(adapter)
    exec(compile(raw, str(adapter), 'exec'), parent.__dict__)
    need((parent.REPO, parent.PROJECT, parent.ROOT, parent.TARGET) ==
         (REPO, PROJECT, ROOT, COEFFICIENT), 'original Coefficient environment differs')
    pc = parent.load(commit)
    readonly = parent.check(pc)
    need(readonly['status'] == 'REVALIDATED' and readonly['normal_or_kernel_commands_executed'] == 0 and
         readonly['identity'] == pc.ident and readonly['identity']['module'] == COEFFICIENT and
         readonly['identity']['commit'] == commit and
         json.loads(bound(binding['formal_pass']))['identity'] == pc.ident and
         json.loads(bound(binding['readonly_receipt'])) == readonly,
         'Coefficient has not supplied actual complete original acceptance')
    # Original contexts are reachable through the unchanged published loaders.
    policy = pc.x.c
    partition = policy.x.c
    dictionary = partition.x.retained
    manifest = json.loads(pc.g.pinned(partition.support.AG, pc.g.MANIFEST, pc.g.MANIFEST_SHA))
    rows = manifest['project_sources']
    old_graph = {module: row['imports'] for module, row in rows.items()}
    old53 = pc.s.h.closure(old_graph, IMPORTS[1:])
    old40 = set(partition.x.spec.graph)
    extension = old53 - old40
    need(len(old53) == 53 and len(old40) == 40 and old40 <= old53 and
         extension == set(EXTENSION_SOURCE_PINS), 'expected exactly the recorded 13-module extension')
    normal, full = dictionary.documents['normal_context'], dictionary.documents['full_context']
    need(old53 <= set(full['preserved_dependency_artifacts']) and
         all(rows[module]['sha256'] == normal['project_sources'][module] ==
             full['selected_live_sources'][module] for module in old53),
         '53 old sources do not match the original Dictionary input context')
    pins = {module: full['preserved_dependency_artifacts'][module] for module in sorted(extension)}
    need(canonical_pin(pins) == EXTENSION_INVENTORY_PIN,
         'original complete 13-module artifact inventory differs')
    for module in extension:
        expected = EXTENSION_SOURCE_PINS[module]
        need(rows[module]['sha256'] == expected['sha256'] and
             fingerprint(regular(PROJECT / pc.s.h.module_path(module))) == expected and
             set(pins[module]) == set(pc.g.artifact_paths(module)) and
             pc.g.module_artifacts(pc.s, module) == pins[module],
             'old extension source or full artifact inventory differs: ' + module)
        stem = '.lake/build/lib/lean/' + module.replace('.', '/')
        need(all(pins[module][stem + ext] == normal['dependency_objects_and_traces'][stem + ext]
                 for ext in ('.olean', '.trace')), 'original extension object/trace references disagree')
    graph = {**pc.spec.graph, **{module: old_graph[module] for module in extension}}
    sources = {**pc.spec.sources, **{module: rows[module]['sha256'] for module in extension}}
    live_graph, live_sources = pc.s.h.project_graph(PROJECT, IMPORTS)
    need(len(graph) == len(sources) == 56 and live_graph == graph and
         {module: row['sha256'] for module, row in live_sources.items()} == sources and
         pc.s.h.closure(graph, IMPORTS) == set(graph) and TARGET not in graph,
         'Boundary dependencies are not exactly 53 old plus Partition/Policy/Coefficient')
    source = pc.x.parent.git(source_commit, LIVE)
    need(fingerprint(source) == SOURCE_PIN and pc.s.h.imports(source) == IMPORTS and
         not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', source.decode()),
         'unchanged complete Boundary source differs')
    spec = SimpleNamespace(graph={**graph, TARGET: IMPORTS},
        sources={**sources, TARGET: SOURCE_PIN['sha256']},
        manifest={'project_sources': {TARGET: {'all_imports': IMPORTS}}})
    need(len(spec.graph) == 57 and pc.s.h.closure(spec.graph, [TARGET]) == set(spec.graph),
         'Boundary formal graph differs')
    return SimpleNamespace(parent=parent, pc=pc, g=pc.g, s=pc.s, spec=spec,
        source=source, commit=source_commit, binding=binding, partition=partition,
        dictionary=dictionary, extension_pins=pins, readonly=readonly)


def fresh(c):
    roots = [path / TARGET for path in ROOT.iterdir() if path.is_dir() and
             re.fullmatch('[0-9a-f]{40}', path.name) and os.path.lexists(path / TARGET)]
    need(not roots, 'prior or partial Boundary owner must be preserved')
    artifacts = c.g.module_artifacts(c.s, TARGET)
    c.g.require_fresh_owner(TARGET, artifacts)
    path = PROJECT / LIVE
    source = regular(path) if os.path.lexists(path) else None
    need(source is None or source == c.source, 'foreign installed Boundary source')
    stem = PROJECT / '.lake/build/lib/lean' / TARGET.replace('.', '/')
    need(all(not os.path.lexists(Path(str(stem) + ext)) for ext in ('.trace.nobuild', '.ir.sig.hash')),
         'partial extra Boundary artifact')
    return {'source': None if source is None else fingerprint(source), 'artifacts': artifacts}


def retained(c):
    owner = c.parent.accepted(c.pc)
    need(c.g.module_artifacts(c.s, COEFFICIENT) == owner['binding']['all_observed_target_artifacts'] and
         c.g.file_binding(PROJECT / c.s.h.module_path(COEFFICIENT)) == c.parent.SOURCE_PIN['sha256'],
         'accepted Coefficient source/artifacts differ')
    observed = {module: c.g.module_artifacts(c.s, module) for module in c.extension_pins}
    need(observed == c.extension_pins and canonical_pin(observed) == EXTENSION_INVENTORY_PIN and
         all(fingerprint(regular(PROJECT / c.s.h.module_path(module))) == source
             for module, source in EXTENSION_SOURCE_PINS.items()), 'old 13-module extension changed')
    stem = PROJECT / '.lake/build/lib/lean' / COEFFICIENT.replace('.', '/')
    return {'original_coefficient_inputs': c.parent.retained(c.pc),
        'coefficient_acceptance_references': c.binding,
        'coefficient_owner_binding': canonical_pin(owner),
        'coefficient_extra_metadata': {ext: c.partition.support.metadata(Path(str(stem) + ext))
                                       for ext in ('.trace.nobuild', '.ir.sig.hash')},
        'dictionary_acceptance_reference': c.dictionary.reference,
        'source_manifest': {'commit': c.partition.support.AG, 'path': c.g.MANIFEST, 'sha256': c.g.MANIFEST_SHA},
        'extension_sources': EXTENSION_SOURCE_PINS, 'extension_full_artifact_inventory': EXTENSION_INVENTORY_PIN}
