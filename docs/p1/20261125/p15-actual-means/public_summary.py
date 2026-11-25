#!/usr/bin/env python3
"""Publish only aggregate counts, public owner identities and cryptographic bindings."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile

sys.dont_write_bytecode = True
import run_selected as runner

REVIEW = runner.ROOT / 'reviews/actual-means-final.json'
OUTPUT = runner.ROOT / 'reviews/actual-means-public.json'
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def need(condition):
    if not condition:
        raise ValueError('verification failed')


def read(path):
    need(path.is_file() and path.resolve() == path)
    return path.read_bytes()


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def build(commit, review):
    raw = read(review)
    r = json.loads(raw)
    need(re.fullmatch('[0-9a-f]{40}', commit) and r['current_source_commit'] == commit)
    need(r['schema'] == 'p15_retained_actual_means_review_v1' and r['all_23_accepted'] is True)
    need(r['context_and_inventory_stable'] is True and not r['failures'] and r['whole_P1_complete'] is False)
    need(r['context_before'] == r['context_after'] and r['git_before'] == r['git_after'])
    sources = r['context_after']['project_sources']
    need(set(r['owners']) == set(runner.TARGETS) and len(r['owners']) == 23 and len(sources) == 304)
    for name, digest in sources.items():
        need(re.fullmatch(r'ImbalancedChen(\.[A-Za-z0-9_]+)+', name))
        need(sha(read(runner.PROJECT / (name.replace('.', '/') + '.lean'))) == digest)
    owners, axioms = {}, set()
    for owner in runner.TARGETS:
        row = r['owners'][owner]
        original = row['original_source_commit']
        need(re.fullmatch('[0-9a-f]{40}', original) and row['source_sha256'] == sources[owner])
        folder = runner.ROOT / original / owner
        refs = row['receipts']
        audit = Path(refs['audit_plan']['path']).parent
        need(audit.parent == folder / 'audits' and re.fullmatch('[0-9a-f]{20}', audit.name))
        lane = audit / 'lane-0'
        paths = {'normal': folder / 'normal' / owner / 'NORMAL_PASS.json',
                 'audit_plan': audit / 'AUDIT_PLAN.json', 'audit_result': lane / 'VALIDATION_RESULTS.json'}
        hashes, records = {}, {}
        for key, path in paths.items():
            data = read(path)
            hashes[key] = sha(data)
            need(refs[key] == {'path': str(path), 'bytes': len(data), 'sha256': hashes[key]})
            records[key] = json.loads(data)
        result = records['audit_result']
        need(records['normal']['module'] == owner and records['normal']['source_commit'] == original)
        need(records['audit_plan']['source_review_head'] == original and result['plan_sha256'] == hashes['audit_plan'])
        need(result['modules'] == {owner: sources[owner]} and result['status'] == 'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS')
        log = read(lane / 'all-owned-types-axioms.log')
        need(sha(log) == result['audit_command']['log_sha256'] and b'sorryAx' not in log)
        exports = json.loads(read(lane / 'OWNED_EXPORTS.json'))
        need(exports == [json.loads(line) for line in re.findall(rb'AUDIT_RECORD (\{[^\n]+\})', log)])
        for entry in exports:
            need(entry['module'] == owner and entry['kind'] != 'axiom' and set(entry['axioms']) <= AXIOMS)
            need(type(entry['is_private']) is bool)
            axioms.update(entry['axioms'])
        public = sum(not entry['is_private'] for entry in exports)
        need(len(exports) == result['total_owned_exports'] == row['total_owned_exports'])
        need(public == result['total_public_exports'] == row['total_public_exports'])
        owners[owner] = {'original_source_commit': original, 'source_sha256': sources[owner],
                         'receipt_sha256': hashes, 'owned_count': len(exports), 'public_count': public}
    need(read(review) == raw)
    canonical = json.dumps(sources, sort_keys=True, separators=(',', ':')).encode()
    return {'repository': 'UyNewNas/goldbach-formalization', 'source_commit': commit, 'owners': owners,
            'owned_count': sum(o['owned_count'] for o in owners.values()),
            'public_count': sum(o['public_count'] for o in owners.values()), 'observed_axioms': sorted(axioms),
            'project_source_count': len(sources), 'project_source_map_sha256': sha(canonical),
            'source_runtime_unchanged': True, 'git_unchanged': True, 'review_sha256': sha(raw),
            'whole_P1_complete': False, 'whole_P1_5_complete': False}


def publish(data):
    with tempfile.NamedTemporaryFile(dir=OUTPUT.parent) as temp:
        temp.write(data)
        temp.flush()
        os.fsync(temp.fileno())
        try:
            os.link(temp.name, OUTPUT)
        except FileExistsError:
            need(read(OUTPUT) == data)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    try:
        summary = build(parser.parse_args().source_commit, REVIEW)
        encoded = json.dumps(summary, sort_keys=True, separators=(',', ':'))
        publish((encoded + '\n').encode())
        print('PUBLIC_ACCEPTANCE_SUMMARY ' + encoded)
    except Exception:
        sys.exit('Public summary verification failed.')
