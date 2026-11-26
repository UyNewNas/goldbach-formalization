# Only inspect existing olean module inventories. No -o, production compiler,
# audit runner, selector, registry writer, package exporter, or source edit.
out = Path('/workspace/p24-current322-serialized-names-b55-20261126/attempt-001')
scan_nodes = dict(prereq_nodes)
scan_nodes.update(a_nodes)
scan_order = [name for name in full if name in scan_nodes]
assert len(scan_order) == len(scan_nodes) == 322
assert set(full) - set(scan_order) == {B, W}
assert A in scan_nodes and B not in scan_nodes and W not in scan_nodes
scan_fingerprint = hashlib.sha256(('\n'.join(scan_order) + '\n').encode()).hexdigest()
registry_raw_before = registry.read_bytes()
records_before = json.loads(registry_raw_before)
registry_before_sha = hashlib.sha256(registry_raw_before).hexdigest()
assert external.verify() == native_before
before_frozen = snapshot(root, lib, full_nodes, toolchain, external)
assert before_frozen['external_snapshot'] == native_before
verify_compilation(records_before, scan_nodes, before_frozen)
assert not out.exists(), 'Do not overwrite an earlier diagnostic'
assert os.statvfs(root).f_bavail * os.statvfs(root).f_frsize >= 64 * 1024 * 1024
out.mkdir(parents=True, exist_ok=False)

def file_info(path):
    path = Path(path)
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': digest(path)}

def write_new_json(name, value):
    path = out / name
    raw = (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + '\n').encode()
    assert os.statvfs(root).f_bavail * os.statvfs(root).f_frsize >= len(raw) + 32 * 1024 * 1024
    with path.open('xb') as stream:
        stream.write(raw)
    assert path.read_bytes() == raw
    return file_info(path)

def write_new_gzip_json(name, value):
    raw = (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + '\n').encode()
    encoded = gzip.compress(raw, compresslevel=9, mtime=0)
    assert gzip.decompress(encoded) == raw
    path = out / name
    assert os.statvfs(root).f_bavail * os.statvfs(root).f_frsize >= len(encoded) + 32 * 1024 * 1024
    with path.open('xb') as stream:
        stream.write(encoded)
    actual = path.read_bytes()
    assert actual == encoded and gzip.decompress(actual) == raw
    return {'gzip': file_info(path), 'uncompressed_bytes': len(raw),
            'uncompressed_sha256': hashlib.sha256(raw).hexdigest(), 'exact_roundtrip_verified': True}

artifacts = {}
checks = {}
errors = []
stage = None
report = None
child = None
scan_source = None
rendered = None
raw_template = base64.b64decode(SERIALIZED_NAMES_TEMPLATE_BASE64, validate=True)
assert hashlib.sha256(raw_template).hexdigest() == SERIALIZED_NAMES_TEMPLATE_SHA256

def perform(name, action):
    try:
        action()
        checks[name] = True
    except Exception as error:
        checks[name] = False
        errors.append({'check': name, 'type': type(error).__name__, 'error': str(error),
                       'traceback': traceback.format_exc()})

def check_runtime_and_native():
    assert {name: digest(name) for name in runtime_expected} == runtime_expected
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=MATHLIB, text=True).strip() == PIN
    assert digest(snapshot_path) == snapshot_expected
    assert external.verify() == native_before

def check_registry():
    assert registry.read_bytes() == registry_raw_before, 'Current canonical registry bytes changed'

def current_frozen():
    nodes = project_nodes(root, W)
    assert list(nodes) == full
    assert {name: digest(node['source']) for name, node in nodes.items()} == sources_before
    mark_project_nodes(nodes, set(external.modules))
    return snapshot(root, lib, nodes, toolchain, external)

def check_all_sources_objects():
    current = current_frozen()
    artifacts['inputs_after'] = write_new_json('inputs-after.json', current)
    assert current == before_frozen, 'Full324 source/object/tool/native snapshot changed'
    verify_compilation(json.loads(registry_raw_before), scan_nodes, current)

def check_isolated_source():
    if scan_source is not None:
        assert scan_source.read_bytes() == rendered, 'Diagnostic source changed'
        assert not scan_source.with_suffix('.olean').exists(), 'Diagnostic unexpectedly wrote an object'

try:
    artifacts['inputs_before'] = write_new_json('inputs-before.json', before_frozen)
    artifacts['scope'] = write_new_json('scope.json', {
        'source_pin': pin, 'full324_ordered_fingerprint': ordered_expected,
        'current322_ordered_fingerprint': scan_fingerprint, 'current322': scan_order,
        'excluded': [B, W], 'registry_bytes': len(registry_raw_before),
        'registry_sha256': registry_before_sha,
        'current322_source_object_bindings': {n: before_frozen['project'][n] for n in scan_order},
        'diagnostic_only': True, 'canonical_credit': False,
    })
    rendered = raw_template.replace(b'__P24_EXPECTED_MODULE_NAMES__',
        ',\n'.join('    `' + name for name in scan_order).encode())
    assert raw_template.count(b'__P24_EXPECTED_MODULE_NAMES__') == 1
    assert b'__P24_EXPECTED_MODULE_NAMES__' not in rendered
    scan_source = out / 'SerializedNames.lean'
    with scan_source.open('xb') as stream:
        stream.write(rendered)
    artifacts['source'] = file_info(scan_source)
    env = external.environment(dict(os.environ))
    flags = ['-t0', '-j1', '-M11264', '-DwarningAsError=true',
             '-DmaxRecDepth=50000', '-DmaxHeartbeats=40000000']
    command = [LEAN, *flags, str(scan_source)]
    log = out / 'serialized-names.log'
    print('P24_SERIALIZED_322_BEGIN ' + json.dumps({'source_pin': pin, 'module_count': 322,
        'source_sha256': artifacts['source']['sha256'], 'output': str(out),
        'no_production_compile': True, 'canonical_credit': False}), flush=True)
    started = time.monotonic()
    timed_out = False
    with log.open('xb') as stream:
        child = subprocess.Popen(command, cwd=root, env=env, stdout=stream, stderr=subprocess.STDOUT)
        try:
            code = child.wait(timeout=300)
        except subprocess.TimeoutExpired:
            timed_out = True
            child.kill()
            code = child.wait()
    stage = {'command': command, 'exit_code': code, 'timed_out': timed_out,
             'elapsed_seconds': time.monotonic() - started, 'log': file_info(log)}
    if code != 0:
        if log.stat().st_size <= 20 * 1024:
            print('COMPLETE_LEAN_ERROR_LOG_BEGIN', flush=True)
            sys.stdout.buffer.write(log.read_bytes())
            sys.stdout.buffer.flush()
            print('COMPLETE_LEAN_ERROR_LOG_END', flush=True)
        else:
            print('Complete Lean output retained at ' + str(log) + '; not truncated.', flush=True)
    assert code == 0 and not timed_out, 'Serialized-name child did not finish successfully'
    imports, inventories, complete = [], [], []
    for line in log.read_text().splitlines():
        for prefix, records in [('P24_SERIALIZED_IMPORTS ', imports),
                                ('P24_SERIALIZED_MODULE ', inventories),
                                ('P24_SERIALIZED_COMPLETE ', complete)]:
            if line.startswith(prefix):
                records.append(json.loads(line[len(prefix):]))
                break
    assert len(imports) == 1 and len(complete) == 1
    assert [row['module'] for row in inventories] == scan_order
    assert len(inventories) == len({row['module'] for row in inventories}) == 322
    assert {n for n in imports[0] if n.startswith('ImbalancedChen.')} == set(scan_order)
    owners = {}
    within_module_duplicates = {}
    for row in inventories:
        assert row['legacy_data_complete'] is True
        assert isinstance(row['header_index'], int) and row['header_index'] >= 0
        names = row['serialized']
        assert isinstance(names, list) and names and len(names) == row['count']
        assert all(isinstance(n, str) and n for n in names)
        counts = {}
        for name in names:
            counts[name] = counts.get(name, 0) + 1
        repeated = {n: count for n, count in counts.items() if count > 1}
        if repeated:
            within_module_duplicates[row['module']] = repeated
        for name in counts:
            owners.setdefault(name, []).append(row['module'])
    total = sum(row['count'] for row in inventories)
    assert complete[0]['modules'] == 322 and complete[0]['serialized_occurrences'] == total
    assert complete[0]['merged_owner_filter_used'] is False
    assert complete[0]['diagnostic_only'] is True and complete[0]['original_owned_credit'] is False
    assert complete[0]['independent_replay'] is False and complete[0]['full_types_or_axioms_audited'] is False
    duplicates = {n: v for n, v in sorted(owners.items()) if len(v) > 1}
    report = {'source_pin': pin, 'registry_sha256': registry_before_sha,
              'full324_ordered_fingerprint': ordered_expected,
              'current322_ordered_fingerprint': scan_fingerprint,
              'modules': 322, 'serialized_occurrences': total, 'unique_names': len(owners),
              'module_counts': {r['module']: r['count'] for r in inventories},
              'duplicate_names': duplicates, 'within_module_duplicate_names': within_module_duplicates,
              'inventories': inventories,
              'source_object_bindings': {n: before_frozen['project'][n] for n in scan_order},
              'diagnostic_only': True, 'full_types_audited': False, 'axioms_audited': False,
              'independent_replay': False, 'original_owned_credit': False,
              'full324_credit': False, 'B_or_W_imported': False}
    artifacts['full_inventories'] = write_new_gzip_json('current322-serialized-inventories.json.gz', report)
    duplicate_report = {k: report[k] for k in ('source_pin','registry_sha256','modules',
        'serialized_occurrences','unique_names','duplicate_names','within_module_duplicate_names',
        'diagnostic_only','original_owned_credit','full324_credit')}
    artifacts['duplicates'] = write_new_gzip_json('current322-duplicate-names.json.gz', duplicate_report)
    small = json.dumps(duplicate_report, ensure_ascii=False)
    if len(small.encode()) <= 200 * 1024:
        print('P24_SERIALIZED_DUPLICATES ' + small, flush=True)
    else:
        print('Complete duplicates exceed 200 KiB stdout budget; lossless gzip retained, no records truncated.', flush=True)
    for module in scan_order:
        print('P24_SERIALIZED_MODULE_COUNT ' + json.dumps({'module':module, 'count':report['module_counts'][module]}), flush=True)
except Exception as error:
    errors.append({'check': 'diagnostic', 'type': type(error).__name__, 'error': str(error),
                   'traceback': traceback.format_exc()})
finally:
    if child is not None and child.poll() is None:
        child.kill()
        child.wait()
    perform('tracked_pin_sources_and_original_tools_unchanged', check_source)
    perform('runtime_and_qualified_native_unchanged', check_runtime_and_native)
    perform('complete_registry_bytes_unchanged', check_registry)
    perform('complete_full324_snapshot_and_current322_compilation_valid', check_all_sources_objects)
    perform('isolated_source_unchanged_and_no_diagnostic_object', check_isolated_source)
    scan_complete = report is not None and not errors and all(checks.values())
    return_code = 0 if scan_complete else (stage['exit_code'] if stage and stage['exit_code'] != 0 else 125)
    receipt = {'source_pin': pin, 'diagnostic_completed': scan_complete, 'exit_code': return_code,
        'current_compiled_scope': 322, 'full_scope': 324, 'full324_ordered_fingerprint': ordered_expected,
        'current322_ordered_fingerprint': scan_fingerprint, 'registry_before_sha256':registry_before_sha,
        'registry_after_sha256':digest(registry), 'stage':stage, 'postchecks':checks, 'errors':errors,
        'artifacts':artifacts, 'duplicate_count': len(report['duplicate_names']) if report else None,
        'duplicate_owner_modules':sorted({m for ms in report['duplicate_names'].values() for m in ms}) if report else None,
        'original_template_unchanged':True,'selector_unchanged_and_not_run':True,
        'no_production_source_or_object_written':True,'zero_budget_not_repeated':True,
        'canonical_credit':False,'original_owned_credit':False,'finite_credit':False,'full324_credit':False}
    receipt_info = write_new_json('receipt.json', receipt)
    print('P24_SERIALIZED_322_RESULT ' + json.dumps({'receipt':receipt_info,
        **{k:v for k,v in receipt.items() if k not in ('artifacts','stage')}}), flush=True)
    assert os.statvfs(root).f_bavail * os.statvfs(root).f_frsize >= 32 * 1024 * 1024
raise SystemExit(return_code)
