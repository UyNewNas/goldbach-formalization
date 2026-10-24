#!/usr/bin/env python3
"""Bind sequential warm-build caches to audited source/partition provenance.

Receipts are integrity evidence inside trusted CI caches, not signed attestations.
They never replace the authoritative final all-target build or proof gates.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

from full_source_shards import make_manifest, require, select_targets

GUARD = 'verification/parts/p0/ci_runtime_guard.py'
PINS = ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')
CLAIM = 'Compilation-only warm-shard cache provenance. No kernel replay, axiom audit, or proof acceptance. Final full production build and all existing gates remain authoritative.'


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical(value) -> str:
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True)


def valid_hash(value) -> bool:
    return isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value) is not None


def evidence(raw: bytes) -> dict:
    text = raw.decode('utf-8')
    json.loads(text)
    return {'sha256': sha(raw), 'json_text': text}


def read_evidence(record: dict) -> dict:
    require(isinstance(record, dict) and isinstance(record.get('json_text'), str), 'missing embedded evidence')
    require(sha(record['json_text'].encode()) == record.get('sha256'), 'tampered embedded evidence digest')
    value = json.loads(record['json_text'])
    require(isinstance(value, dict), 'evidence must be a JSON object')
    return value


def current_pins(repo: Path, source: dict) -> dict:
    actual_head = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD']).decode().strip()
    require(actual_head == source['head'], 'inventory HEAD differs from current checkout')
    rows = {r['path']: r for r in source['files']}
    result = {}
    for name in (*PINS, GUARD):
        digest = sha((repo / name).read_bytes())
        require(name in rows and rows[name]['sha256'] == digest, f'current file differs from inventory: {name}')
        result[name] = digest
    result['toolchain_pin'] = (repo / 'lean-toolchain').read_text().strip()
    return result


def validate_manifest(source: dict, manifest: dict, count: int) -> None:
    require(manifest == make_manifest(source, count), 'shard manifest does not match complete current source inventory/partition')


def validate_build(report: dict, source: dict, selected: list[str]) -> None:
    require(report.get('head') == source['head'], 'build report HEAD mismatch')
    require(type(report.get('exit_code')) is int and report['exit_code'] == 0, 'shard build did not exit successfully')
    require(report.get('all_requested_targets_passed') is True, 'requested targets did not all pass')
    require(report.get('requested_targets') == selected and report.get('requested_target_count') == len(selected),
            'build report requested targets differ from exact shard')
    full = set(selected) == set(source['targets'])
    require(report.get('all_production_targets_passed') is full and report.get('full_production_scope_requested') is full,
            'build report falsely promotes partial scope')
    expected = {m: 'build_passed_or_validated_cache' if m in set(selected) else 'outside_this_build_shard'
                for m in source['targets']}
    require(report.get('targets') == expected, 'build target outcomes do not match shard scope')
    source_rows = {r['path']: r for r in source['files']}
    rows = report.get('files')
    require(isinstance(rows, list) and len(rows) == len(source_rows), 'build report file coverage incomplete')
    require(len({r['path'] for r in rows}) == len(rows), 'duplicate build report file')
    for row in rows:
        original = dict(row)
        status = original.pop('build_status', None)
        if not row.get('module'):
            require(original.pop('run_status', None) == 'not_run_nonproduction', 'nonproduction run status missing or false')
            require(original.pop('compiled_by_this_build', None) is False, 'nonproduction file falsely marked compiled')
            require(original.pop('build_reason', None) == source_rows.get(row['path'], {}).get('disposition', 'not_a_production_build_target'),
                    'nonproduction disposition reason differs')
        require(original == source_rows.get(row['path']), 'build report source file differs from inventory')
        require(status == (expected[row['module']] if row.get('module') else 'not_a_production_build_target'),
                'build report file outcome differs from scope')
    require(valid_hash(report.get('log_sha256')), 'build log digest missing')


def validate_runtime(audit: dict, state: dict, state_digest: str, pins: dict) -> None:
    require(audit.get('status') == 'PASS_RUNTIME_GUARD_ONLY', 'runtime audit did not pass')
    require(type(audit.get('source_commands')) is int and audit['source_commands'] > 0, 'runtime audit has no source commands')
    require(type(audit.get('compiler_commands')) is int and audit['compiler_commands'] >= audit['source_commands'], 'invalid compiler command count')
    require(audit.get('probe') is True, 'runtime audit probe missing')
    require(audit.get('lean_elab_async') is False and state.get('lean_elab_async') is False, 'elaboration scheduling is not fixed false')
    require(type(audit.get('lean_memory_mib')) is int and audit['lean_memory_mib'] == 6144
            and type(state.get('lean_memory_mib')) is int and state['lean_memory_mib'] == 6144, 'runtime memory budget is not 6144 MiB')
    require(audit.get('state_sha256') == state_digest, 'audit is not bound to embedded runtime state')
    require(valid_hash(audit.get('command_log_sha256')), 'command log digest missing')
    require(state.get('guard_sha256') == pins[GUARD], 'runtime guard differs from current guard source')
    environment = state.get('environment', {})
    require(environment.get('P0_LEAN_ELAB_ASYNC') == 'false' and environment.get('CI_LEAN_MEMORY_MIB') == '6144', 'runtime environment flags differ')
    require(environment.get('ELAN_TOOLCHAIN') == pins['toolchain_pin'], 'runtime toolchain pin differs')
    inputs = state.get('input_sha256')
    require(isinstance(inputs, dict) and len(inputs) == len(PINS), 'runtime input hashes incomplete')
    normalized = {Path(path).name: value for path, value in inputs.items()}
    require(normalized == {name: pins[name] for name in PINS}, 'runtime input hashes differ from current pins')
    runtime = state.get('runtime_sha256')
    require(isinstance(runtime, dict) and bool(runtime) and all(valid_hash(h) for h in runtime.values()), 'runtime binary hashes missing or malformed')
    realbin = state.get('realbin')
    require(isinstance(realbin, str) and bool(realbin), 'runtime real binary directory missing')
    for tool in ('lean', 'lake', 'leanchecker', 'leanir', 'clang', 'leanc', 'llvm-ar', 'leantar'):
        require(str(Path(realbin) / tool) in runtime, f'pinned runtime hash missing: {tool}')


def create_receipt(source: dict, manifest: dict, build_raw: bytes, audit_raw: bytes, state_raw: bytes,
                   pins: dict, cache_key: str, index: int, count: int) -> dict:
    validate_manifest(source, manifest, count)
    selected = select_targets(manifest, index)
    require(isinstance(cache_key, str) and bool(cache_key.strip()) and '\n' not in cache_key, 'invalid cache key')
    build_evidence, audit_evidence, state_evidence = map(evidence, (build_raw, audit_raw, state_raw))
    report, audit, state = map(read_evidence, (build_evidence, audit_evidence, state_evidence))
    validate_build(report, source, selected)
    validate_runtime(audit, state, state_evidence['sha256'], pins)
    payload = {'schema': 1, 'claim': CLAIM, 'compilation_only': True, 'proof_acceptance': False,
               'source_head': source['head'], 'source_identity_sha256': manifest['source_identity_sha256'],
               'source_files': manifest['source_files'], 'pins': pins,
               'partition_manifest_sha256': sha(canonical(manifest).encode()),
               'all_targets': manifest['all_targets'], 'shards': manifest['shards'],
               'index': index, 'count': count, 'cache_key': cache_key,
               'selected_targets': selected, 'source_compilation_success': True,
               'build_report': build_evidence, 'runtime_audit': audit_evidence, 'runtime_state': state_evidence}
    serialized = canonical(payload)
    return {'receipt_sha256': sha(serialized.encode()), 'receipt': json.loads(serialized)}


def real_runtime_hashes(state: dict) -> dict:
    realbin = state.get('realbin')
    runtime = state.get('runtime_sha256')
    require(isinstance(realbin, str) and bool(realbin) and isinstance(runtime, dict), 'current pinned runtime identity missing')
    result = {tool: runtime.get(str(Path(realbin) / tool))
              for tool in ('lean', 'lake', 'leanchecker', 'leanir', 'clang', 'leanc', 'llvm-ar', 'leantar')}
    require(all(valid_hash(value) for value in result.values()), 'current pinned runtime binary hashes incomplete')
    return result


def verify_receipts(source: dict, manifest: dict, receipts: dict[str, dict], pins: dict, count: int,
                    current_state: dict) -> dict:
    validate_manifest(source, manifest, count)
    expected_files = {f'shard-{i}.json' for i in range(1, count + 1)}
    require(set(receipts) == expected_files, 'missing, extra, or incorrectly named shard receipts')
    keys = set()
    require(current_state.get('guard_sha256') == pins[GUARD], 'current runtime guard differs from current source')
    require({Path(path).name: digest for path, digest in current_state.get('input_sha256', {}).items()}
            == {name: pins[name] for name in PINS}, 'current runtime input pins differ')
    require(current_state.get('environment', {}).get('ELAN_TOOLCHAIN') == pins['toolchain_pin'],
            'current runtime toolchain pin differs')
    runtime_reference = real_runtime_hashes(current_state)
    for index in range(1, count + 1):
        envelope = receipts[f'shard-{index}.json']
        require(isinstance(envelope, dict) and isinstance(envelope.get('receipt'), dict), 'malformed receipt envelope')
        receipt = envelope['receipt']
        require(envelope.get('receipt_sha256') == sha(canonical(receipt).encode()), 'tampered receipt digest')
        require(receipt.get('index') == index and receipt.get('count') == count, 'wrong/duplicate receipt index or count')
        # Regeneration rechecks every evidence field against the current inventory,
        # partition, guard and pins; unknown or changed fields also fail equality.
        expected = create_receipt(source, manifest,
                                  receipt['build_report']['json_text'].encode(),
                                  receipt['runtime_audit']['json_text'].encode(),
                                  receipt['runtime_state']['json_text'].encode(),
                                  pins, receipt['cache_key'], index, count)
        require(envelope == expected, 'receipt does not match current source/partition/pins or embedded evidence')
        require(receipt['cache_key'] not in keys, 'duplicate shard cache key')
        keys.add(receipt['cache_key'])
        state = read_evidence(receipt['runtime_state'])
        real = real_runtime_hashes(state)
        require(real == runtime_reference, 'pinned real runtime binary hashes differ from current final-job runtime')
    return {'status': 'PASS_STAGING_CACHE_PROVENANCE_ONLY', 'source_head': source['head'],
            'verified_shards': count, 'production_target_count': len(source['targets']),
            'claim': CLAIM, 'all_production_targets_passed': False,
            'final_authoritative_build_still_required': True}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    for command in ('create', 'verify'):
        p = sub.add_parser(command)
        p.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[1])
        p.add_argument('--inventory', type=Path, required=True)
        p.add_argument('--manifest', type=Path, required=True)
        p.add_argument('--count', type=int, default=4)
        p.add_argument('--output', type=Path, required=command == 'create')
        if command == 'create':
            for name in ('build-report', 'audit', 'state'):
                p.add_argument('--' + name, type=Path, required=True)
            p.add_argument('--cache-key', required=True)
            p.add_argument('--index', type=int, required=True)
        else:
            p.add_argument('--receipts-dir', type=Path, required=True)
            p.add_argument('--state', type=Path, required=True, help='Current final-job runtime state')
    args = parser.parse_args()
    try:
        source = json.loads(args.inventory.read_text())
        manifest = json.loads(args.manifest.read_text())
        pins = current_pins(args.repo, source)
        if args.command == 'create':
            state_now = json.loads(args.state.read_text())
            audit_now = json.loads(args.audit.read_text())
            require(sha(Path(state_now['log']).read_bytes()) == audit_now.get('command_log_sha256'),
                    'compiler command log changed after runtime audit')
            result = create_receipt(source, manifest, args.build_report.read_bytes(), args.audit.read_bytes(),
                                    args.state.read_bytes(), pins, args.cache_key, args.index, args.count)
        else:
            receipts = {p.name: json.loads(p.read_text()) for p in args.receipts_dir.glob('shard-*.json')}
            result = verify_receipts(source, manifest, receipts, pins, args.count, json.loads(args.state.read_text()))
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps({'status': 'CREATED_COMPILATION_ONLY_RECEIPT', 'index': args.index})
              if args.command == 'create' else json.dumps(result))
        return 0
    except (ValueError, KeyError, TypeError, OSError, subprocess.CalledProcessError) as error:
        print(f'Shard receipt {args.command} failed: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
