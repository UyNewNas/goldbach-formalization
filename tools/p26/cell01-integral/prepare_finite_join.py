"""Bind the exact finite objects to the accepted P2 context without rebuilding."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
OLD = Path('/workspace/p26-cell01-next-20261128')
PARENT = OLD / 'CURRENT_ACCEPTED_CONTEXT.json'
BATCHES = [
    ('/workspace/p26-cell01-finite-p2-20261128', list(range(9, 25))),
    ('/workspace/p26-cell01-finite-p2-25-56-20261128', list(range(25, 57))),
    ('/workspace/p26-cell01-finite-p2-57-88-20261128', list(range(57, 89))),
    ('/workspace/p26-cell01-finite-p2-89-97-107-129-20261128', [*range(89, 98), *range(107, 130)]),
    ('/workspace/p26-cell01-finite-p2-130-143-20261128', list(range(130, 144))),
]
BASE_IMPORTS = [
    'ImbalancedChen.P2OriginalSaving19Cell05SourceAttachment',
    'ImbalancedChen.P2OriginalSaving19Cell00SourceAttachment',
    'ImbalancedChen.P2OriginalSaving19Cell05GroupedSeparationComplete',
    'ImbalancedChen.P2OriginalSaving19Cell01Row000OriginalFloorBridge',
    'ImbalancedChen.P2OriginalSaving19OriginalFloorTransport',
    'ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorInterface',
    'ImbalancedChen.P2OriginalSaving19Cell01GroupedSeparationSigns',
]


def pin(path):
    raw = path.read_bytes()
    return {'path': str(path), 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def check(item):
    assert pin(Path(item['path'])) == item, item['path']


def module_name(row):
    return f'ImbalancedChen.P2OriginalSaving19Cell01Row{row:03d}Finite'


def prepare(rows, stage):
    assert rows == sorted(set(rows)) and rows and all(1 <= r < 144 for r in rows)
    parent_pin, parent = pin(PARENT), json.loads(PARENT.read_text())
    assert parent['formal_acceptance'] and len(parent['project_closure']) == 1341
    watched = [parent_pin, *parent['phase_parents'].values(), *parent['runtime'].values(),
               *parent['native_artifacts']]
    supplier_run = json.loads(Path(parent['phase_parents']['qualification']['path']).read_text())
    for key, name in [('replay_source', 'ReplayJoin.lean'),
                      ('audit_source', 'OwnedSuppliersAudit.lean')]:
        assert pin(HERE / name) == supplier_run[key]
        watched.append(supplier_run[key])
    core_run = json.loads(Path(parent['phase_parents']['core']['path']).read_text())
    external_readback = core_run['final_external_readback']
    check(external_readback)
    report = json.loads(Path(external_readback['path']).read_text())
    assert report['status'] == 'matched' and report['problems'] == []
    assert report['unique_physical_files_hashed'] == 54309
    external_plan = report['plan']
    check(external_plan)
    external_relative = 'tools/p26/analytic-closure/verify_external_inputs.py'
    original = subprocess.check_output(['git', 'show',
        'e4205213a17d2c9690c463b8c75235b436ce6745:' + external_relative], cwd=ROOT)
    external_verifier = pin(ROOT / external_relative)
    assert external_verifier['bytes'] == len(original)
    assert external_verifier['sha256'] == hashlib.sha256(original).hexdigest()
    watched += [external_readback, external_plan, external_verifier]
    watched += [
        {'path': '/workspace/goldbach-research/eighth-third-minorant-extension-20261009-a23-s23_low-01-cell.witness.json',
         'bytes': 470901, 'sha256': 'e19eee9d7e282cd3a618a71f12e93bcce28319485c9d0fd31bbeaf9f81a995a4'},
        {'path': '/workspace/goldbach-research/eighth-third-moment-refinement-20261009-a23-low-01.witness.json',
         'bytes': 75094, 'sha256': '03e9360189414e240818a191e5b53102aa5e8c3a1e7c18fbd8553ba020078d8c'},
    ]
    for info in parent['project_closure'].values():
        watched += [info['source'], info['selected_object']]
    incoming, batches = {}, []
    legacy = set(rows) & {*range(1, 9), *range(98, 107)}
    recovered_path = OLD / 'RECOVERED_FINITE17.json'
    recovered = json.loads(recovered_path.read_text())
    assert recovered['formal_acceptance'] is False
    watched.append(pin(recovered_path))
    for folder, name, sha, source_prefix, ordinals in [
        ('first8-transport', 'first8-finite.tar.xz',
         'c8d3f55eca7b5c31bb32e1b21fea639f609095156f500c32706fc3bfa09478fc', 'sources', set(range(1, 9))),
        ('c9-transport', 'evidence.tar.xz',
         '9cf583475d3e45f67e3ba44da270658a916ee1a118986d7f0a671ac232c8007c', 'project', set(range(98, 107))),
    ]:
        selected = legacy & ordinals
        if not selected: continue
        archive = OLD / folder / name
        assert pin(archive)['sha256'] == sha
        watched.append(pin(archive))
        expected = {}
        for row in selected:
            module = module_name(row)
            entries = [i for i in recovered['modules'] if i['module'] == module]
            assert len(entries) == 1 and entries[0]['current_P2_import_qualification'] is False
            info = entries[0]
            assert info['source']['path'] == str(ROOT / (module.replace('.', '/') + '.lean'))
            check(info['source']); check(info['object'])
            incoming[module] = {'source': info['source'], 'object': info['object'], 'origin': 'immutable-legacy-transport'}
            for key, prefix, extension in [('source', source_prefix, '.lean'), ('object', 'objects', '.olean')]:
                expected[prefix + '/' + module.replace('.', '/') + extension] = info[key]
        with tarfile.open(archive) as tar:
            found = set()
            for entry in tar:
                if entry.name in expected:
                    raw = tar.extractfile(entry).read()
                    item = expected[entry.name]
                    assert len(raw) == item['bytes'] and hashlib.sha256(raw).hexdigest() == item['sha256']
                    found.add(entry.name)
            assert found == set(expected)
    for folder, ordinals in BATCHES:
        selected = set(rows) & set(ordinals)
        if not selected: continue
        base = Path(folder)
        batch = base / ('batch-' + '-'.join(map(str, ordinals)))
        summary_path = batch / 'SUMMARY.json'
        summary = json.loads(summary_path.read_text())
        assert summary['status'] == 'passed_local_finite_checks' and summary['formal_acceptance'] is False
        assert summary['rows'] == ordinals and summary['owned_declarations'] == 292 * len(ordinals)
        assert len(summary['results']) == len(ordinals)
        watched += [pin(summary_path), summary['inputs']]
        check(summary['inputs'])
        inputs = json.loads(Path(summary['inputs']['path']).read_text())
        assert len(inputs) == summary['external_and_project_inputs_rechecked']
        watched.extend(inputs)
        prepared_path = base / 'MANIFEST.json'
        prepared = json.loads(prepared_path.read_text())
        assert prepared['qualification_parent'] == parent['phase_parents']['qualification']
        assert prepared['core_parent'] == parent['phase_parents']['core']
        watched += [pin(prepared_path), prepared['wrapper_source']]
        for row, item in zip(ordinals, summary['results']):
            if row not in selected: continue
            check(item)
            run = json.loads(Path(item['path']).read_text())
            module = module_name(row)
            assert run['row'] == row and run['module'] == module
            assert run['status'] == 'passed_local_finite_checks' and run['owned_declarations'] == 292
            assert run['inputs'] == summary['inputs']
            assert [c['label'] for c in run['commands']] == ['normal', 'kernel', 'owned']
            for command in run['commands']:
                assert command['exit_code'] == 0
                watched.append(command['log'])
            source = pin(ROOT / (module.replace('.', '/') + '.lean'))
            assert all(source[k] == run['source'][k] for k in ['bytes', 'sha256'])
            watched += [item, run['source'], run['object'], run['audit_source']]
            incoming[module] = {'source': source, 'object': run['object'], 'origin': 'completed-pinned-P2-finite-checks'}
        batches.append({'summary': pin(summary_path), 'rows_used': sorted(selected)})
    assert set(incoming) == {module_name(row) for row in rows}
    selected_inputs = {}
    for item in watched:
        if item['path'] in selected_inputs: assert selected_inputs[item['path']] == item
        selected_inputs[item['path']] = item
    for item in selected_inputs.values(): check(item)
    objects = stage / 'objects'

    def install(source, relative, expected):
        target = objects / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists(): os.link(source, target)
        actual = pin(target)
        assert all(actual[k] == expected[k] for k in ['bytes', 'sha256'])
        return actual

    catalog = {}
    for module, info in parent['project_closure'].items():
        target = install(info['selected_object']['path'], module.replace('.', '/') + '.olean', info['selected_object'])
        catalog[module] = {'source': info['source'], 'selected_object': target, 'origin': 'accepted-current1341'}
    for module, info in incoming.items():
        assert module not in catalog
        check(info['source']); check(info['object'])
        target = install(info['object']['path'], module.replace('.', '/') + '.olean', info['object'])
        catalog[module] = {'source': info['source'], 'selected_object': target, 'origin': info['origin']}
    parent_root = Path(parent['lean_path'].split(':')[0])
    native = [install(i['path'], Path(i['path']).relative_to(parent_root), i) for i in parent['native_artifacts']]
    assert len(catalog) == 1341 + len(rows) and len(native) == 555
    context = {'schema': 'p26_cell01_finite_join_inputs_v1', 'formal_acceptance': False,
        'P2_6_complete': False, 'accepted_parent': parent_pin, 'ordinals': rows,
        'incoming_modules': sorted(incoming), 'project_closure': catalog,
        'native_artifacts': native, 'runtime': parent['runtime'],
        'lean_path': str(objects) + ':' + parent['lean_path'].split(':', 1)[1],
        'selected_inputs': list(selected_inputs.values()), 'batch_receipts': batches,
        'external_plan': external_plan, 'external_verifier_source': external_verifier,
        'preparer_source': pin(Path(__file__))}
    stage.mkdir(parents=True, exist_ok=True)
    context_path = stage / 'JOIN_INPUTS.json'
    raw = json.dumps(context, indent=2) + '\n'
    if context_path.exists(): assert context_path.read_text() == raw
    else: context_path.write_text(raw)
    modules_path = stage / 'INCOMING_MODULES.json'
    raw = json.dumps(sorted(incoming), indent=2) + '\n'
    if modules_path.exists(): assert modules_path.read_text() == raw
    else: modules_path.write_text(raw)
    replay = (HERE / 'ReplayJoin.lean').read_text().replace('P26_CELL01', 'P26_CELL01_FINITE')
    replay = replay.replace('wanted.size == 407', 'wanted.size == ' + str(len(rows)))
    start = replay.index('  let baseImports : Array Import := #[')
    end = replay.index('  let (_, fullState)', start)
    replay = replay[:start] + ('  let baseImports : Array Import := #[\n' +
        ',\n'.join('    { module := `' + n + ' }' for n in BASE_IMPORTS) + ']\n' +
        '  let (_, baseState) ← (importModulesCore baseImports).run\n' +
        '  let base ← finalizeImport baseState baseImports {} 0 false false\n' +
        '  let allImports := baseImports ++ #[\n' +
        ',\n'.join('    { module := `' + n + ' }' for n in sorted(incoming)) + ']\n') + replay[end:]
    audit = (HERE / 'OwnedSuppliersAudit.lean').read_text()
    audit = ''.join('import ' + n + '\n' for n in BASE_IMPORTS + sorted(incoming)) + audit[audit.index('import Lean.Util.CollectAxioms'):]
    start = audit.index('  for moduleName in #[')
    end = audit.index('] do\n    let some idx', start)
    audit = audit[:start] + '  for moduleName in #[\n' + ',\n'.join('      `' + n for n in sorted(incoming)) + audit[end:]
    audit = audit.replace('P26_CELL01_SUPPLIER_AUDIT', 'P26_CELL01_FINITE_AUDIT').replace(
        'p26Cell01SharedProofBodyCheck', 'p26Cell01FiniteSharedProofBodyCheck')
    for name, text in [('ReplayJoin.lean', replay), ('OwnedAudit.lean', audit)]:
        path = stage / name
        if path.exists(): assert path.read_text() == text
        else: path.write_text(text)
    assert pin(PARENT) == parent_pin
    return context_path


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stage', required=True, type=Path)
    parser.add_argument('--rows', nargs='+', type=int, default=list(range(1, 144)))
    args = parser.parse_args()
    print(prepare(args.rows, args.stage))
