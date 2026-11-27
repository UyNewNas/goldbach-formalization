"""Read accepted Boundary and merge the original Dictionary input graph.

No compiler, install, build or acceptance mutation is performed here. There
are 293 existing inputs: the original Dictionary's 289-module graph plus four
already accepted signed-exit owners. The selected 5545-byte bridge is the only
new target; one scoped Sublist relation is written explicitly, with unchanged
proof bodies. Actual Boundary adapter/PASS/readonly pins are mandatory.
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
BOUNDARY = 'ImbalancedChen.P1HistoricalBoundaryPolicyDifferenceSupport'
DICTIONARY = 'ImbalancedChen.P1OriginalHistoricalCoefficientDictionary'
TARGET = 'ImbalancedChen.P1OriginalHistoricalFirstDisagreement'
PUBLIC_NAMESPACE = TARGET
NAME = 'P1OriginalHistoricalFirstDisagreement.lean'
LIVE = 'ImbalancedChen/' + NAME
SOURCE_ORIGIN_COMMIT = '04039b4cd13346897207edf8bbf6b7e7f92e9cc4'
SOURCE_ORIGIN_PATH = 'docs/p1/20261127/p15-source-continuation/medium/' + NAME
SOURCE_PIN = {'bytes': 5545, 'sha256': '00b11f60f73300ff8443ed72367c19f6c817fa5384d1449296b929a0155731ec'}
ORIGINAL_SOURCE_PIN = {'bytes': 5533, 'sha256': 'edb45d7c44440fdb68937fc0931c95c7a7ab0532ec26b1f20002b8669c8700a2'}
SOURCE_ORIGIN_REFERENCE = {'commit': SOURCE_ORIGIN_COMMIT, 'path': SOURCE_ORIGIN_PATH,
                           **ORIGINAL_SOURCE_PIN}
SOURCE_REPAIR = {'kind': 'spell_one_scoped_sublist_relation_as_List.Sublist',
    'original_source': ORIGINAL_SOURCE_PIN, 'selected_source': SOURCE_PIN,
    'source_bytes_unchanged': False, 'proof_bodies_unchanged': True}
IMPORTS = [DICTIONARY, BOUNDARY]
DICTIONARY_COMMIT = '040d46058821746c69c5183b3f6c22792287c4ba'
DICTIONARY_SOURCE_PIN = {'bytes': 9107, 'sha256': 'eb78b1ba6ced1f441b8b923210ef1fc32c107b307be69c0c3f6d2b8fd91d97ff'}
DICTIONARY_GRAPH_PIN = {'bytes': 36999, 'sha256': '8f5874eeb5f30615c7a156317f1d1af92d1cdc307f44fb3ac98bceb141a22f4a'}
FORMAL_GRAPH_PIN = {'bytes': 37729, 'sha256': '646e86891ad8a08e32dc74509976fbcf3fc7b14c92d3449589e261360cae3753'}
EXTENSION_INVENTORY_PIN = {'bytes': 553295, 'sha256': '968be6a5e07a9c3738ec3377fc1b9c4fceafc553244968c7210a8c9315a1fa58'}
EXPECTED_PUBLIC = {
    PUBLIC_NAMESPACE + '.nonzero_has_changed_rough_factor',
    PUBLIC_NAMESPACE + '.nonzero_has_actual_first_disagreement'}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def fingerprint(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def canonical_pin(value):
    return fingerprint(json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode())


def regular(path):
    need(path.is_file() and not path.is_symlink() and path.resolve() == path,
         'expected original regular file: ' + str(path))
    return path.read_bytes()


def verify_selected_source(original, selected):
    need(fingerprint(original) == ORIGINAL_SOURCE_PIN and fingerprint(selected) == SOURCE_PIN,
         'original or selected bridge source pin differs')
    old = b'state.selectedPrefix.reverse <+ roughPrimeUniverse N cap w z'
    new = b'List.Sublist state.selectedPrefix.reverse (roughPrimeUniverse N cap w z)'
    need(original.count(old) == 1 and selected == original.replace(old, new),
         'bridge repair extends beyond the one explicit Sublist relation')


def valid_pin(row):
    return (isinstance(row, dict) and set(row) == {'path', 'bytes', 'sha256'} and
            isinstance(row['path'], str) and Path(row['path']).is_absolute() and
            type(row['bytes']) is int and row['bytes'] > 0 and
            isinstance(row['sha256'], str) and re.fullmatch('[0-9a-f]{64}', row['sha256']))


def bound(row):
    need(valid_pin(row), 'actual Boundary file path/bytes/SHA256 required')
    raw = regular(Path(row['path']))
    need(fingerprint(raw) == {key: row[key] for key in ('bytes', 'sha256')},
         'original Boundary receipt/adapter changed')
    return raw


def public_source_names(raw):
    need(fingerprint(raw) == SOURCE_PIN and
         re.findall(r'^namespace (\S+)', raw.decode(), re.MULTILINE) == [PUBLIC_NAMESPACE],
         'original bridge source/namespace differs')
    names = {PUBLIC_NAMESPACE + '.' + name for private, kind, name in
        re.findall(r'^(private )?(def|theorem) (\w+)\b', raw.decode(), re.MULTILINE) if not private}
    need(names == EXPECTED_PUBLIC, 'original bridge public interface differs')
    return names


def load(binding, source_commit):
    need(isinstance(binding, dict) and set(binding) ==
         {'source_commit', 'adapter', 'formal_pass', 'readonly_receipt'} and
         isinstance(binding['source_commit'], str) and re.fullmatch('[0-9a-f]{40}', binding['source_commit']) and
         all(valid_pin(binding[key]) for key in ('adapter', 'formal_pass', 'readonly_receipt')) and
         isinstance(source_commit, str) and re.fullmatch('[0-9a-f]{40}', source_commit),
         'actual accepted Boundary identity and exact bridge source commit required')
    commit = binding['source_commit']
    adapter = ROOT / commit / 'published-entrypoints/run_boundary.py'
    need(binding['adapter']['path'] == str(adapter) and
         binding['formal_pass']['path'] == str(ROOT / commit / 'boundary-policy-operation/PASS.json'),
         'original Boundary identity/receipt routes must be retained')
    parent = ModuleType('original_boundary_acceptance')
    parent.__file__ = str(adapter)
    exec(compile(bound(binding['adapter']), str(adapter), 'exec'), parent.__dict__)
    need((parent.REPO, parent.PROJECT, parent.ROOT, parent.TARGET) ==
         (REPO, PROJECT, ROOT, BOUNDARY), 'original Boundary environment differs')
    pc = parent.load(commit)
    readonly = parent.check(pc)
    need(readonly['status'] == 'REVALIDATED' and readonly['normal_or_kernel_commands_executed'] == 0 and
         readonly['identity'] == pc.ident and readonly['identity']['module'] == BOUNDARY and
         readonly['identity']['commit'] == commit and
         json.loads(bound(binding['formal_pass']))['identity'] == pc.ident and
         json.loads(bound(binding['readonly_receipt'])) == readonly,
         'Boundary has not supplied actual complete original acceptance')
    dictionary, partition = pc.x.dictionary, pc.x.partition
    normal, full = dictionary.documents['normal_context'], dictionary.documents['full_context']
    manifest = json.loads(pc.g.pinned(partition.support.AG, pc.g.MANIFEST, pc.g.MANIFEST_SHA))
    rows = manifest['project_sources']
    graph = {module: row['imports'] for module, row in rows.items()}
    dictionary_path = pc.s.h.module_path(DICTIONARY)
    dictionary_source = regular(PROJECT / dictionary_path)
    need(fingerprint(dictionary_source) == DICTIONARY_SOURCE_PIN and
         dictionary_source == pc.g.git_file(DICTIONARY_COMMIT, dictionary_path) and
         normal['project_sources'][DICTIONARY] == DICTIONARY_SOURCE_PIN['sha256'],
         'original accepted Dictionary source differs')
    # The Dictionary root is newer than the fixed manifest. Its exact accepted
    # source supplies the two project imports; the 288 lower rows stay fixed.
    graph[DICTIONARY] = [module for module in pc.s.h.imports(dictionary_source)
                         if module.startswith('ImbalancedChen.')]
    active = pc.s.h.closure(graph, [DICTIONARY])
    need(len(active) == 289 and active == set(normal['project_sources']) == set(full['selected_live_sources']) and
         active - {DICTIONARY} == set(full['preserved_dependency_artifacts']) and
         all(rows[module]['sha256'] == normal['project_sources'][module] == full['selected_live_sources'][module]
             for module in active - {DICTIONARY}), 'Dictionary original 289-source graph differs')
    dictionary_graph = {module: graph[module] for module in active}
    need(canonical_pin(dictionary_graph) == DICTIONARY_GRAPH_PIN,
         'original Dictionary dependency topology differs')
    overlap = active & set(pc.spec.graph)
    extension = active - set(pc.spec.graph)
    need(len(pc.spec.graph) == 57 and len(overlap) == 53 and len(extension) == 236 and DICTIONARY in extension and
         all(dictionary_graph[module] == pc.spec.graph[module] and
             normal['project_sources'][module] == pc.spec.sources[module] for module in overlap),
         'Dictionary/Boundary graph overlap differs')
    pins = {module: full['preserved_dependency_artifacts'][module] for module in extension - {DICTIONARY}}
    pins[DICTIONARY] = dictionary.owner['all_observed_target_artifacts']
    need(canonical_pin(pins) == EXTENSION_INVENTORY_PIN and all(len(row) == 21 for row in pins.values()),
         'original complete 236-module extension inventory differs')
    for module, expected in pins.items():
        need(set(expected) == set(pc.g.artifact_paths(module)) and pc.g.module_artifacts(pc.s, module) == expected,
             'original extension artifacts differ: ' + module)
        if module != DICTIONARY:
            stem = '.lake/build/lib/lean/' + module.replace('.', '/')
            need(all(expected[stem + ext] == normal['dependency_objects_and_traces'][stem + ext]
                     for ext in ('.olean', '.trace')), 'original extension object/trace references disagree')
    merged = {**dictionary_graph, **pc.spec.graph}
    sources = {**normal['project_sources'], **pc.spec.sources}
    live_graph, live_sources = pc.s.h.project_graph(PROJECT, IMPORTS)
    need(len(merged) == len(sources) == 293 and live_graph == merged and
         {module: row['sha256'] for module, row in live_sources.items()} == sources and
         pc.s.h.closure(merged, IMPORTS) == set(merged) and TARGET not in merged,
         'bridge dependencies are not exactly the original 293 inputs')
    source = pc.g.git_file(source_commit, LIVE)
    verify_selected_source(pc.g.git_file(SOURCE_ORIGIN_COMMIT, SOURCE_ORIGIN_PATH), source)
    need(fingerprint(source) == SOURCE_PIN and pc.s.h.imports(source) == IMPORTS and
         not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', source.decode()),
         'selected 5545-byte bridge source differs')
    public_source_names(source)
    spec = SimpleNamespace(graph={**merged, TARGET: IMPORTS},
        sources={**sources, TARGET: SOURCE_PIN['sha256']},
        manifest={'project_sources': {TARGET: {'all_imports': IMPORTS}}})
    need(len(spec.graph) == 294 and canonical_pin(spec.graph) == FORMAL_GRAPH_PIN and
         pc.s.h.closure(spec.graph, [TARGET]) == set(spec.graph), 'bridge formal graph differs')
    return SimpleNamespace(parent=parent, pc=pc, g=pc.g, s=pc.s, spec=spec, verifier=pc.verifier,
        source=source, commit=source_commit, binding=binding, dictionary=dictionary, partition=partition,
        extension_pins=pins, extension_sources={module: sources[module] for module in extension}, readonly=readonly)


def fresh(c):
    roots = [path / TARGET for path in ROOT.iterdir() if path.is_dir() and
             re.fullmatch('[0-9a-f]{40}', path.name) and os.path.lexists(path / TARGET)]
    need(not roots, 'prior or partial bridge owner must be preserved')
    artifacts = c.g.module_artifacts(c.s, TARGET)
    c.g.require_fresh_owner(TARGET, artifacts)
    path = PROJECT / LIVE
    source = regular(path) if os.path.lexists(path) else None
    need(source is None or source == c.source, 'foreign installed bridge source')
    stem = PROJECT / '.lake/build/lib/lean' / TARGET.replace('.', '/')
    need(all(not os.path.lexists(Path(str(stem) + ext)) for ext in ('.trace.nobuild', '.ir.sig.hash')),
         'partial extra bridge artifact')
    return {'source': None if source is None else fingerprint(source), 'artifacts': artifacts}


def retained(c):
    owner = c.parent.accepted(c.pc)
    need(c.g.module_artifacts(c.s, BOUNDARY) == owner['binding']['all_observed_target_artifacts'] and
         c.g.file_binding(PROJECT / c.s.h.module_path(BOUNDARY)) == c.parent.SOURCE_PIN['sha256'],
         'accepted Boundary source/artifacts differ')
    observed = {module: c.g.module_artifacts(c.s, module) for module in c.extension_pins}
    sources = {module: c.g.file_binding(PROJECT / c.s.h.module_path(module)) for module in c.extension_sources}
    need(observed == c.extension_pins and canonical_pin(observed) == EXTENSION_INVENTORY_PIN and
         sources == c.extension_sources, 'original 236-module input extension changed')
    stem = PROJECT / '.lake/build/lib/lean' / BOUNDARY.replace('.', '/')
    return {'original_boundary_inputs': c.parent.retained(c.pc),
        'boundary_acceptance_references': c.binding, 'boundary_owner_binding': canonical_pin(owner),
        'boundary_extra_metadata': {ext: c.partition.support.metadata(Path(str(stem) + ext))
                                   for ext in ('.trace.nobuild', '.ir.sig.hash')},
        'dictionary_acceptance_reference': c.dictionary.reference,
        'dictionary_graph': DICTIONARY_GRAPH_PIN,
        'extension_sources': canonical_pin(sources), 'extension_full_artifact_inventory': EXTENSION_INVENTORY_PIN}
