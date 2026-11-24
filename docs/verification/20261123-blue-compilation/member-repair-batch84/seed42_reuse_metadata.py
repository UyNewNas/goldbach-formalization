"""Batch84 metadata composition only; no formal-tool, lock or process calls."""
from pathlib import Path
import hashlib
import json

SEED = 'ImbalancedChen.P2Winner9CompleteSeedBlock42'
ARCHIVE = 'ImbalancedChen.P5SubdivisionStoredParentArchive'
LEAF_PIN_FILE_SHA256 = '3ce10ec461d6a66fb72754cc96b28c7e758c69780ec00cd209144d3ca7842a93'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
FLAGS = ['-t0', '-j2', '-M12288', 'maxRecDepth=100000', 'maxHeartbeats=4000000']


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def read_json(path):
    return json.loads(Path(path).read_bytes())


def write_exact(path, value):
    """Never overwrite a different old record, even after a partial retry."""
    path = Path(path)
    data = (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()
    if path.exists():
        assert path.read_bytes() == data, ('existing_record_differs', str(path))
    else:
        with path.open('xb') as stream:
            stream.write(data)


def source_plus_five(project, module):
    rel = module.replace('.', '/')
    paths = [rel + '.lean', '.lake/build/lib/lean/' + rel + '.olean',
             '.lake/build/lib/lean/' + rel + '.ilean', '.lake/build/ir/' + rel + '.c',
             '.lake/build/ir/' + rel + '.setup.json', '.lake/build/lib/lean/' + rel + '.trace']
    return {rel: {'bytes': (project / rel).stat().st_size, 'sha256': sha(project / rel)}
            for rel in paths}


def parse_complete_owned(log_path, module):
    raw = Path(log_path).read_bytes()
    text = raw.decode('utf-8')
    assert not any(t in text for t in ['sorryAx', '…', '⋯', '...'])
    records, inventories, counts, totals = [], [], [], []
    for line in text.splitlines():
        if line.startswith('AUDIT_RECORD '):
            records.append(json.loads(line[len('AUDIT_RECORD '):]))
        elif line.startswith('MEMBER_OWNED_NAMES '):
            inventories.append(json.loads(line[len('MEMBER_OWNED_NAMES '):]))
        elif line.startswith('MEMBER_OWNED_MODULE '):
            counts.append(json.loads(line[len('MEMBER_OWNED_MODULE '):]))
        elif line.startswith('MEMBER_OWNED_COUNT '):
            totals.append(int(line[len('MEMBER_OWNED_COUNT '):]))
    names = [record['name'] for record in records]
    assert records and len(names) == len(set(names))
    assert inventories == [{'names': names}]
    assert counts == [{'count': len(records), 'module': module}]
    assert totals == [len(records)]
    for record in records:
        assert set(record) == {'name', 'module', 'kind', 'is_private', 'type',
                               'type_expression', 'universe_parameters', 'axioms'}
        assert record['module'] == module
        assert record['kind'] in {'theorem', 'definition', 'opaque', 'quotient',
                                  'inductive', 'constructor', 'recursor'}
        assert type(record['is_private']) is bool
        assert record['is_private'] == record['name'].startswith('_private.')
        assert isinstance(record['type'], str) and record['type']
        assert isinstance(record['type_expression'], str) and record['type_expression']
        assert not any(token in record[field]
                       for field in ['type', 'type_expression']
                       for token in ['sorryAx', '…', '⋯', '...'])
        assert isinstance(record['universe_parameters'], list)
        assert all(isinstance(x, str) for x in record['universe_parameters'])
        assert isinstance(record['axioms'], list) and set(record['axioms']) <= ALLOWED
    return records


def _checked_receipt(root, relative, expected_hash=None):
    path = root / relative
    if expected_hash is not None:
        assert sha(path) == expected_hash, ('receipt_pin', str(path))
    receipt = read_json(path)
    assert receipt['exit_code'] == 0, ('old_receipt_not_successful', str(path))
    assert sha(root / receipt['log']) == receipt['log_sha256']
    return receipt


def verify_seed_leaf(root, project, state_path, expected, baselines=None):
    """Fresh hash-only validation, called before the unchanged normal/kernel loop."""
    assert set(expected) == {SEED, ARCHIVE}
    leaf = root / 'seed42-owned-only'
    assert sha(root / 'SEED42_REUSE_PINS.json') == LEAF_PIN_FILE_SHA256
    pins = read_json(root / 'SEED42_REUSE_PINS.json')
    for name, pin in pins.items():
        path = leaf / name
        assert path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256'], name
    result = read_json(leaf / 'SEED42_COMPLETE_OWNED_SUPPLEMENT_RESULT.json')
    assert result['status'] == 'PASS_CURRENT_SEED42_NORMAL_KERNEL_AND_COMPLETE_OWNED_WITH_NO_NORMAL_KERNEL_REPETITION'
    assert result['module'] == SEED
    assert result['source_sha256'] == expected[SEED]
    assert result['full_type_AST_universe_and_std3_axioms'] is True
    assert result['source_plus_five_outputs_stable'] is True
    assert result['archive_not_accepted_by_this_leaf_supplement'] is True
    records = parse_complete_owned(leaf / 'audit.log', SEED)
    assert records == read_json(leaf / 'OWNED_EXPORTS.json')
    public = [r for r in records if not r['is_private']]
    assert public == read_json(leaf / 'PUBLIC_EXPORTS.json')
    assert (len(records), len(public), len(records) - len(public)) == (17, 1, 16)
    assert (result['owned_total'], result['public_total'], result['private_total']) == (17, 1, 16)
    normal = _checked_receipt(root, SEED.split('.')[-1] + '-normal-command.json',
                              result['normal_receipt_sha256'])
    kernel = _checked_receipt(root, SEED.split('.')[-1] + '-kernel-command.json',
                              result['kernel_receipt_sha256'])
    guard = ['python3', '/workspace/blue-build-tools/run_guarded.py', '--state', str(state_path)]
    assert normal['argv'] == guard + ['lake', 'build', SEED + ':olean']
    assert kernel['argv'] == guard + ['lake', 'env', 'leanchecker', '--verbose', SEED]
    audit = read_json(leaf / 'AUDIT_COMMAND.json')
    assert audit == result['actual_audit_command'] and audit['exit_code'] == 0
    assert audit['no_original_module_normal_or_kernel_invocations'] is True
    assert sha(leaf / 'audit.log') == audit['log_sha256']
    assert audit['argv'] == guard + ['lake', 'env', 'lean', '-DmaxRecDepth=100000',
                                      '-DmaxHeartbeats=4000000', '--root=' + str(leaf),
                                      str(leaf / 'OwnedOnlyAudit.lean')]
    snapshot = read_json(leaf / 'SOURCE_PLUS_FIVE_BEFORE.json')
    assert len(snapshot) == 6 and source_plus_five(project, SEED) == snapshot
    assert read_json(root / (SEED.split('.')[-1] + '-AFTER_NORMAL.json')) == snapshot
    assert read_json(root / (SEED.split('.')[-1] + '-AFTER_KERNEL.json')) == snapshot
    if baselines is not None:
        assert baselines[SEED] == snapshot
    runtime = read_json(leaf / 'ACTUAL_AUDIT_RUNTIME.json')
    assert runtime['state'] == str(state_path) and runtime['state_sha256'] == sha(state_path)
    tail = (leaf / 'ACTUAL_GUARD_JOURNAL_TAIL.jsonl').read_bytes()
    assert hashlib.sha256(tail).hexdigest() == runtime['captured_tail_sha256']
    journal = Path(runtime['journal'])
    with journal.open('rb') as stream:
        stream.seek(runtime['before_byte_offset'])
        assert stream.read(runtime['after_byte_offset'] - runtime['before_byte_offset']) == tail
    assert runtime['actual_runtime'] in [json.loads(line) for line in tail.splitlines()]
    assert runtime['actual_runtime']['tool'] == 'lean' and runtime['actual_runtime']['cwd'] == str(project)
    assert str(leaf / 'OwnedOnlyAudit.lean') in runtime['actual_runtime']['command']
    assert all(flag in runtime['actual_runtime']['command'] for flag in FLAGS)
    lane = read_json(leaf / 'VALIDATION_LANE.json')
    assert lane['status'] == 'VALIDATION_LANE_FINISHED' and lane['exit_code'] == 0
    assert lane['state_sha256'] == sha(state_path)
    final = read_json(leaf / 'FINAL_REVIEW.json')
    assert final['status'] == 'PASS_SEED42_LEAF_NORMAL_NAMED_KERNEL_COMPLETE_OWNED_EVIDENCE_CHAIN'
    assert final['source_sha256'] == expected[SEED]
    source_event = final['actual_runtime_evidence']['actual_original_source_event']
    lo, hi = source_event['journal_byte_range']
    with journal.open('rb') as stream:
        stream.seek(lo)
        source_line = stream.read(hi - lo)
    assert hashlib.sha256(source_line).hexdigest() == source_event['raw_line_sha256']
    assert json.loads(source_line) == source_event['event']
    assert str(project / (SEED.replace('.', '/') + '.lean')) in source_event['event']['command']
    assert all(flag in source_event['event']['command'] for flag in FLAGS)
    return {'records': records, 'normal': normal, 'kernel': kernel, 'audit': audit,
            'snapshot': snapshot, 'runtime': runtime, 'source_event': source_event,
            'pins': pins, 'leaf': leaf}


def capture_archive_audit_runtime(root, state_path, offset):
    target = str(root / 'ArchiveOnlyAudit.lean')
    path = root / 'ARCHIVE_ONLY_AUDIT_RUNTIME.json'
    state = read_json(state_path)
    journal = Path(state['log'])
    tail_path = root / 'ARCHIVE_ONLY_ACTUAL_GUARD_JOURNAL_TAIL.jsonl'
    if offset is None:
        assert path.exists() and tail_path.exists(), 'Successful audit lacks runtime capture; do not rerun it.'
        runtime = read_json(path)
        assert runtime['state_sha256'] == sha(state_path)
        tail = tail_path.read_bytes()
    else:
        end = journal.stat().st_size
        with journal.open('rb') as stream:
            stream.seek(offset)
            tail = stream.read(end - offset)
        actual = [json.loads(line) for line in tail.splitlines()
                  if target in json.loads(line).get('command', [])]
        assert len(actual) == 1 and all(flag in actual[0]['command'] for flag in FLAGS)
        runtime = {'state': str(state_path), 'state_sha256': sha(state_path),
                   'journal': str(journal), 'before_byte_offset': offset,
                   'after_byte_offset': end, 'captured_tail_sha256': hashlib.sha256(tail).hexdigest(),
                   'actual_runtime': actual[0]}
        if tail_path.exists():
            assert tail_path.read_bytes() == tail
        else:
            with tail_path.open('xb') as stream:
                stream.write(tail)
        write_exact(path, runtime)
    assert runtime['journal'] == str(journal)
    assert runtime['captured_tail_sha256'] == hashlib.sha256(tail).hexdigest()
    with journal.open('rb') as stream:
        stream.seek(runtime['before_byte_offset'])
        assert stream.read(runtime['after_byte_offset'] - runtime['before_byte_offset']) == tail
    assert runtime['actual_runtime'] in [json.loads(line) for line in tail.splitlines()]
    assert runtime['actual_runtime']['tool'] == 'lean'
    assert target in runtime['actual_runtime']['command']
    assert all(flag in runtime['actual_runtime']['command'] for flag in FLAGS)
    return runtime


def collect_actual_runtime(root, project, state_path, seed, archive_audit):
    state = read_json(state_path)
    archive_source = str(project / (ARCHIVE.replace('.', '/') + '.lean'))
    archive_event = None
    with Path(state['log']).open('r', encoding='utf-8') as stream:
        for line in stream:
            event = json.loads(line)
            if event.get('tool') == 'lean' and archive_source in event.get('command', []):
                archive_event = event
    assert archive_event is not None and all(flag in archive_event['command'] for flag in FLAGS)
    events = {str(project / (SEED.replace('.', '/') + '.lean')): seed['source_event']['event'],
              str(seed['leaf'] / 'OwnedOnlyAudit.lean'): seed['runtime']['actual_runtime'],
              archive_source: archive_event,
              str(root / 'ArchiveOnlyAudit.lean'): archive_audit['actual_runtime']}
    assert len(events) == 4
    return {'state': str(state_path), 'state_sha256': sha(state_path),
            'serial_compiler_lock': state['slot'], 'actual_compiler_commands': events,
            'source_and_audit_events_separated_by_module': True,
            'seed_source_and_owned_events_reused_exact_not_reexecuted': True,
            'named_kernel_commands_in_validation_results_not_separate_journal_event_claim': True}
