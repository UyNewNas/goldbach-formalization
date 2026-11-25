#!/usr/bin/env python3
"""Sequential new-owner checking; preserve every attempt and stop on failure."""
from pathlib import Path
import argparse
import json
import subprocess
import sys
from generate_full import FullEngine, WORK, fp


def check(record):
    short = record['module'].split('.')[-1]
    for mode in ['normal', 'kernel']:
        folder = WORK / 'logs' / short
        folder.mkdir(parents=True, exist_ok=True)
        results = list(folder.glob(mode + '-*-result.json'))
        accepted = []
        for path in results:
            row = json.loads(path.read_text())
            if row['status'] == 'succeeded' and row['source'] == record['source']:
                assert row['exit_code'] == 0 and fp(row['object']['path']) == row['object']
                assert fp(row['log']['path']) == row['log']
                assert row['source_object_invariants_before'] == row['source_object_invariants_after']
                accepted.append(row)
        if accepted:
            print(json.dumps({'module': record['module'], 'mode': mode,
                              'action': 'reuse accepted current-source owner'}), flush=True)
            continue
        assert not results, ('Preserve failure and use an explicitly reviewed new attempt', short, mode)
        driver = folder / (mode + '-initial-driver.log')
        assert not driver.exists()
        with driver.open('w') as out:
            done = subprocess.run([sys.executable, str(WORK / 'run_owner.py'), short, mode],
                                  cwd=WORK, stdout=out, stderr=subprocess.STDOUT)
        result = folder / (mode + '-initial-result.json')
        if result.exists():
            row = json.loads(result.read_text())
            print(json.dumps({k: row[k] for k in ['module', 'mode', 'status',
                             'elapsed_seconds', 'peak_rss_bytes', 'source', 'object']}), flush=True)
        else:
            print(driver.read_text(), flush=True)
        assert done.returncode == 0, ('Stopped at failed owner', short, mode, str(driver))
    progress_path = WORK / 'PROGRESS.json'
    progress = json.loads(progress_path.read_text()) if progress_path.exists() else {
        'new_accepted_owners': [], 'frozen_suppliers_recompiled': False,
        'cell00_reparsed': False, 'whole_cell_parse_proved': False,
        'typed_geometry_proved': False, 'remote_jobs_submitted': False}
    if record['module'] not in progress['new_accepted_owners']:
        progress['new_accepted_owners'].append(record['module'])
    progress['new_accepted_owner_count'] = len(progress['new_accepted_owners'])
    progress['last_accepted_source'] = record['source']
    progress['last_completed_obligations'] = record['planned_obligations']
    progress['whole_cell_parse_proved'] |= bool(record['planned_obligations'].get('whole_parse_success_theorem', False))
    progress_path.write_text(json.dumps(progress, indent=2) + '\n')


def ensure(engine, short, produce):
    module = 'ImbalancedChen.' + short
    frozen = {r['module']: r for r in json.loads((WORK / 'FROZEN_SUPPLIERS.json').read_text())['inputs']}
    if module in frozen:
        row = frozen[module]
        assert fp(row['source']['path']) == row['source'] and fp(row['object']['path']) == row['object']
        print(json.dumps({'module': module, 'action': 'reuse frozen supplier; no compilation'}), flush=True)
        return
    path = WORK / 'owners' / (short + '.json')
    record = json.loads(path.read_text()) if path.exists() else produce()
    assert fp(record['source']['path']) == record['source']
    check(record)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('key', default='active8_enumeration', nargs='?')
    ap.add_argument('--through-block', type=int)
    ap.add_argument('--complete-field', action='store_true')
    args = ap.parse_args()
    engine = FullEngine()
    tag = engine.field_tag(args.key)
    ensure(engine, engine.tag + tag + 'Header', lambda: engine.field_header(args.key))
    node, groups = engine.block_plan(args.key)
    last = len(groups) - 1 if args.through_block is None else args.through_block
    assert 0 <= last < len(groups)
    for index in range(last + 1):
        ensure(engine, engine.tag + tag + f'Block{index:03d}',
               lambda i=index: engine.array_block_owner(args.key, i))
    if args.complete_field:
        assert last == len(groups) - 1
        ensure(engine, engine.tag + tag + 'Value', lambda: engine.array_value(args.key))
        ensure(engine, engine.tag + tag + 'Field', lambda: engine.array_field(args.key))
    print(json.dumps({'key': args.key, 'through_block': last, 'block_count': len(groups),
                      'field_complete': args.complete_field, 'whole_cell_parse_proved': False}), flush=True)


if __name__ == '__main__':
    main()
