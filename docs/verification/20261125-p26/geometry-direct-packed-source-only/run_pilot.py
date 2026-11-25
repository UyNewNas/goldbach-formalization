#!/usr/bin/env python3
"""One selected new-cell pilot; fixed 4 GiB/180 s normal then kernel checks."""
from pathlib import Path
import argparse
import json
import subprocess
import sys
from generate import Engine, fp


def check(engine, manifest):
    short = manifest['module'].split('.')[-1]
    for mode in ['normal', 'kernel']:
        logs = engine.work / 'logs' / short
        logs.mkdir(parents=True, exist_ok=True)
        receipts = list(logs.glob(mode + '-*-result.json'))
        matched = [json.loads(path.read_text()) for path in receipts]
        matched = [record for record in matched if record['status'] == 'succeeded' and record['source'] == manifest['source']]
        if matched:
            for record in matched:
                assert record['exit_code'] == 0 and fp(record['object']['path']) == record['object']
                assert fp(record['log']['path']) == record['log']
            print(json.dumps({'module': manifest['module'], 'mode': mode, 'action': 'reuse accepted owner'}), flush=True)
            continue
        assert not receipts, ('Prior failure requires preserved source and an explicit reviewed attempt', short, mode)
        driver = logs / (mode + '-initial-driver.log'); assert not driver.exists()
        with driver.open('w') as output:
            done = subprocess.run([sys.executable, str(engine.work / 'run_owner.py'), short, mode],
                                  cwd=engine.work, stdout=output, stderr=subprocess.STDOUT)
        result = logs / (mode + '-initial-result.json')
        if result.exists():
            record = json.loads(result.read_text())
            print(json.dumps({k: record[k] for k in ['module', 'mode', 'status', 'source',
                             'elapsed_seconds', 'peak_rss_bytes', 'object']}), flush=True)
        else:
            print(driver.read_text(), flush=True)
        if done.returncode:
            raise SystemExit(done.returncode)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cell', type=int, required=True)
    parser.add_argument('--raw', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args(); engine = Engine(args.cell, args.raw, args.out)
    manifests = []
    for produce in [engine.data_owner, engine.input_owner, engine.metadata_owner, engine.array_block_owner]:
        manifest = produce('active8_enumeration', 0) if produce == engine.array_block_owner else produce()
        check(engine, manifest); manifests.append(manifest)
        (engine.work / 'PILOT_PROGRESS.json').write_text(json.dumps({
            'cell': engine.cell, 'accepted_pilot_owner_count': len(manifests),
            'accepted_modules': [m['module'] for m in manifests],
            'full_cell_parse_proved': False, 'all13_pass_claimed': False,
            'cell00_reparsed': False, 'production_modified': False, 'remote_jobs_submitted': False}, indent=2) + '\n')
    print(json.dumps({'cell': engine.cell, 'pilot_owners_passed': len(manifests),
                      'full_cell_parse_proved': False}), flush=True)


if __name__ == '__main__':
    main()
