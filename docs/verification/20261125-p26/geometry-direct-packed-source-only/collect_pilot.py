#!/usr/bin/env python3
"""Freeze a measured four-owner direct-packed pilot; never run a compiler."""
from pathlib import Path
import argparse
import hashlib
import json
import re


ROOT = Path(__file__).resolve().parent


def fp(path):
    path = Path(path)
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data),
            'sha256': hashlib.sha256(data).hexdigest()}


def save(path, data):
    data = data.encode() if isinstance(data, str) else data
    if path.exists():
        assert path.read_bytes() == data, ('Frozen delivery drift', str(path))
    else:
        path.write_bytes(data)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    work = args.out.resolve()
    progress = json.loads((work / 'PILOT_PROGRESS.json').read_text())
    assert progress['accepted_pilot_owner_count'] == 4
    assert progress['full_cell_parse_proved'] is False
    cell = progress['cell']
    assert 1 <= cell <= 12
    expected = [f'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData{cell:02d}',
                f'ImbalancedChen.P2OriginalSaving19Geometry{cell:02d}DirectInput',
                f'ImbalancedChen.P2OriginalSaving19Geometry{cell:02d}DirectMetadata05',
                f'ImbalancedChen.P2OriginalSaving19Geometry{cell:02d}DirectActive8EnumerationBlock000']
    assert progress['accepted_modules'] == expected
    frozen = json.loads((work / 'FROZEN_SUPPLIERS.json').read_text())['inputs']
    inputs = []
    for row in frozen:
        assert fp(row['source']['path']) == row['source']
        assert fp(row['object']['path']) == row['object']
        copied = work / 'objects' / (row['module'].replace('.', '/') + '.olean')
        copied_fp = fp(copied)
        assert (copied_fp['bytes'], copied_fp['sha256']) == (row['object']['bytes'], row['object']['sha256'])
        inputs.append({**row, 'copied_object': copied_fp, 'role': 'frozen_supplier',
                       'recompiled': False})
    assert len(inputs) == 6
    owners = []
    all_axioms = set()
    failures = []
    for module in expected:
        short = module.split('.')[-1]
        owner_path = work / 'owners' / (short + '.json')
        manifest = json.loads(owner_path.read_text())
        assert manifest['module'] == module
        assert fp(manifest['source']['path']) == manifest['source']
        assert fp(manifest['fixture']['path']) == manifest['fixture']
        obj = fp(work / 'objects' / (module.replace('.', '/') + '.olean'))
        selected = {}
        for mode in ['normal', 'kernel']:
            matches = []
            for path in sorted((work / 'logs' / short).glob(mode + '-*-result.json')):
                record = json.loads(path.read_text())
                assert fp(record['log']['path']) == record['log']
                if record['status'] != 'succeeded':
                    failures.append(fp(path))
                    continue
                if record['source'] != manifest['source']:
                    continue
                assert record['exit_code'] == 0 and record['object'] == obj
                assert record['rss_limit_bytes'] == 4 * 1024**3
                assert record['wall_seconds'] == 180
                assert record['accepted_dependencies_recompiled'] is False
                matches.append((path, record))
            assert len(matches) == 1, (module, mode, 'Expected one accepted current-source receipt')
            selected[mode] = matches[0]
        normal = selected['normal'][1]
        kernel = selected['kernel'][1]
        assert normal['attempt'] == kernel['attempt']
        source_text = Path(manifest['source']['path']).read_text()
        theorem_count = len(re.findall(r'(?m)^theorem\s+', source_text))
        printed_count = len(re.findall(r'(?m)^#print axioms\s+', source_text))
        log_text = Path(normal['log']['path']).read_text()
        output_count = len(re.findall(r"(?m)^'[^']+' (?:depends on axioms:|does not depend on any axioms)", log_text))
        assert theorem_count == printed_count == output_count
        axioms = set(normal['printed_axioms'])
        assert axioms <= {'propext', 'Quot.sound', 'Classical.choice'}
        all_axioms |= axioms
        summary = {
            'module': module, 'source': manifest['source'], 'object': obj,
            'owner_manifest': fp(owner_path), 'scope': manifest['scope'],
            'planned_obligations': manifest['planned_obligations'],
            'project_imports': manifest['project_imports'],
            'theorems_printed_and_checked': theorem_count,
            'printed_axioms': sorted(axioms),
            'normal_receipt': fp(selected['normal'][0]),
            'kernel_receipt': fp(selected['kernel'][0]),
            'normal_seconds': normal['elapsed_seconds'],
            'normal_peak_rss_bytes': normal['peak_rss_bytes'],
            'kernel_seconds': kernel['elapsed_seconds'],
            'kernel_peak_rss_bytes': kernel['peak_rss_bytes'],
        }
        owners.append(summary)
        inputs.append({'module': module, 'source': manifest['source'], 'object': obj,
                       'project_imports': manifest['project_imports'], 'role': 'new_pilot_owner',
                       'normal_receipt': summary['normal_receipt'],
                       'kernel_receipt': summary['kernel_receipt']})
    assert len(inputs) == 10 and len({row['module'] for row in inputs}) == 10
    known = {row['module'] for row in inputs}
    for row in inputs:
        assert set(row['project_imports']) <= known
    source_inputs = {'project_closure_count': 10, 'frozen_supplier_count': 6,
                     'new_owner_count': 4, 'inputs': inputs}
    save(work / 'SOURCE_INPUTS.json', json.dumps(source_inputs, indent=2) + '\n')
    source_manifest = {
        'cell': cell, 'status': 'FOUR_OWNER_DIRECT_PACKED_PILOT_NORMAL_AND_KERNEL_PASSED',
        'bootstrap': fp(work / 'BOOTSTRAP.json'), 'raw_plan': fp(work / 'RAW_PLAN.json'),
        'source_inputs': fp(work / 'SOURCE_INPUTS.json'),
        'frozen_suppliers': fp(work / 'FROZEN_SUPPLIERS.json'),
        'runner': fp(work / 'run_owner.py'),
        'generators': [fp(ROOT / name) for name in ['generate.py', 'raw_planner.py',
                       'fragment_templates.py', 'run_pilot.py', 'collect_pilot.py']],
        'design': fp(ROOT / 'DESIGN.md'), 'owners': owners,
        'new_theorem_count': sum(row['theorems_printed_and_checked'] for row in owners),
        'axioms_union': sorted(all_axioms), 'preserved_failed_receipts': failures,
        'whole_array_value_proved': False, 'whole_cell_parse_proved': False,
        'typed_geometry_decoding_proved': False, 'all13_pass_claimed': False,
        'cell00_reparsed': False, 'production_modified': False,
        'remote_jobs_submitted': False, 'host_plan_is_proof': False,
    }
    save(work / 'SOURCE_MANIFEST.json', json.dumps(source_manifest, indent=2) + '\n')
    table = '\n'.join(
        f"| `{row['module'].split('.')[-1]}` | {row['normal_seconds']:.3f} | "
        f"{row['normal_peak_rss_bytes']:,} | {row['kernel_seconds']:.3f} | "
        f"{row['kernel_peak_rss_bytes']:,} |" for row in owners)
    report = f'''# Cell {cell:02d}: direct packed original-reader pilot

Four new owners passed normal compilation and independent kernel replay, each
within the unchanged 4 GiB process-tree RSS / 180 second / one-thread limits.
Six accepted suppliers were reused without compilation. The project closure
contains ten modules. Source and object identities are recorded in
SOURCE_MANIFEST.json and SOURCE_INPUTS.json.

| Owner | Normal seconds | Normal peak bytes | Kernel seconds | Kernel peak bytes |
|---|---:|---:|---:|---:|
{table}

The input owner is the exact production v4 DataNN source in an explicitly recorded
private mirror. The raw original was byte-checked against its existing provenance;
CRLF is unchanged. The input interfaces concern the production packed constant,
not an old flat character diagnostic value.

The metadata owner proves the original reader's transition through all five
selected original metadata fields. The array owner proves one actual grouped
active8_enumeration transition, first for arbitrary fuel/tail/accumulator and then
for its exact compact-input interval. The reader's residual call is retained.

This is a measured partial pilot. It does not prove the whole array, whole cell
parse, typed geometry decoding, numerical checks, P1 original-path acceptance,
or all thirteen cells. The generator explicitly holds a selected child exceeding
its owner span policy for a later grouped supplier. Host tokenization and SHA
checks only produce and bind candidates; all claimed reader equations are Lean
theorems. No cell00 parser or accepted supplier was recompiled.

The {source_manifest['new_theorem_count']} new theorems all have printed axiom
reports; their union is {', '.join(sorted(all_axioms)) or 'empty'}. Any failed
attempt receipts remain listed separately in SOURCE_MANIFEST.json.
'''
    save(work / 'PILOT_REPORT.md', report)
    print(json.dumps({'source_manifest': fp(work / 'SOURCE_MANIFEST.json'),
                      'source_inputs': fp(work / 'SOURCE_INPUTS.json'),
                      'report': fp(work / 'PILOT_REPORT.md')}, indent=2))


if __name__ == '__main__':
    main()
