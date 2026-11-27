#!/usr/bin/env python3
"""Independent read-only review of Cell03 checkpoint-002-delta.

Uses git object reads and existing local files only. Does not invoke Lean,
rewrite sources/evidence, rebuild archives, or grant missing-owner credit.
Only the JSON review output is written beneath this review directory.
"""
from pathlib import Path
import argparse
import base64
import collections
import datetime
import functools
import hashlib
import json
import lzma
import re
import subprocess
import tarfile

HERE = Path(__file__).resolve().parent
SOURCE_COMMIT = '68703c066df26624af2f2d45b6e0b0a1fd365b6d'
BASELINE_COMMIT = 'a0eb3b8f66f47f382b0e551be1d5d7c319f8bdab'
BASELINE_DIR = 'docs/verification/20261127-p2-5-cell03-finite'
DELIVERY_SHA = 'd4041a9860b5374f826eea7f19bc20109615353b5a68127505e1deafb3bacaaf'
BASELINE_SHA = '197c79787aac8e6182926799e937e8b093020d627c42e8484398dca38d794760'
MANIFEST_SHA = '198f6d066f5851d1f03f997f6924948935b88ac7741a9af7d2f4d8b5e0b0248c'
PUBLIC_SHA = 'b3d3731344be22c564915f84a6a474ab6f1c0b9ce756d071f991249e46e75ef8'
TEMPLATE_SHA = 'cd452bddeee765b82187f03893cddb5f7136e3420591f0ea00c9bfe1028f670a'
APPENDIX_SHA = 'ff82f03c8c798556f2ed6e18ce4ed5a035057fa616b55664a105a9b5886aa202'
FLAGS = ['-t0', '-j1', '-M11264', '-DwarningAsError=true', '-DmaxRecDepth=1000000', '-DmaxHeartbeats=80000000']
LABELS = {'NORMAL': 'normal_log_sha256', 'REPLAY': 'stock_replay_log_sha256', 'AUDIT': 'complete_owned_audit_log_sha256'}
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
EQUATIONS = {'ImbalancedChen.P2OriginalSaving16OriginalArchive.rationalArrayField.eq_1',
             'ImbalancedChen.P2OriginalSaving16OriginalArchive.rationalField.eq_1'}


def need(ok, reason):
    if not ok:
        raise ValueError(reason)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def sha(p):
    with Path(p).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def read(p):
    return json.loads(Path(p).read_bytes())


def jsig(value):
    return digest(json.dumps(value, sort_keys=True, separators=(',', ':')).encode())


def marks(raw):
    result = collections.defaultdict(list)
    for line in raw.decode().splitlines():
        if line.startswith(('P0_QUEUE_', 'P25_PRIVATE_SCOPED_SIMP_INTERFACE ')):
            key, body = line.split(' ', 1)
            result[key].append(json.loads(body))
    return result


def decode_members(document):
    result = {}
    for name, row in document['files'].items():
        need(not Path(name).is_absolute() and '..' not in Path(name).parts, 'Unsafe evidence member: ' + name)
        raw = base64.b64decode(row['base64'], validate=True)
        need(len(raw) == row['bytes'] and digest(raw) == row['sha256'], 'Evidence byte/hash mismatch: ' + name)
        result[name] = raw
    return result


def review(args):
    root, repo = args.root.resolve(strict=True), args.repo.resolve(strict=True)
    checkpoint = root / 'checkpoint-002-delta'
    need(sha(checkpoint / 'DELIVERY_MANIFEST.json') == DELIVERY_SHA, 'Selected delta delivery changed')
    delivery = read(checkpoint / 'DELIVERY_MANIFEST.json')
    frozen = {checkpoint / 'DELIVERY_MANIFEST.json': DELIVERY_SHA}
    for name, row in delivery['deliverables'].items():
        p = checkpoint / name
        need(p.stat().st_size == row['bytes'] and sha(p) == row['sha256'], 'Delta deliverable mismatch: ' + name)
        frozen[p] = row['sha256']
    need(set(delivery['publish']) == set(delivery['deliverables']) - {'FULL_EVIDENCE_LOCAL_ONLY.json.xz'} and
         delivery['local_audit_only'] == ['FULL_EVIDENCE_LOCAL_ONLY.json.xz'], 'Publication would duplicate the full evidence bundle')

    @functools.cache
    def git_blob(commit, path):
        need(not Path(path).is_absolute() and '..' not in Path(path).parts, 'Unsafe git source path')
        return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=repo)

    # Bind both existing archives to their actual already-published Git pieces.
    parts = json.loads(git_blob(BASELINE_COMMIT, BASELINE_DIR + '/ARTIFACT_PARTS.json'))
    prior_archives = {'ACTUAL_EVIDENCE_DICT64.json.xz': root / 'checkpoint-001/ACTUAL_EVIDENCE_DICT64.json.xz',
                      'SIMPLEX05_NEW_DEPS.tar.xz': root / 'SIMPLEX05_NEW_DEPS.tar.xz'}
    published_parts_checked = 0
    for name, path in prior_archives.items():
        row = parts['artifacts'][name]
        raw = path.read_bytes()
        need(len(raw) == row['bytes'] and digest(raw) == row['sha256'], 'Published archive mismatch: ' + name)
        offset = 0
        for part in row['parts']:
            actual = git_blob(BASELINE_COMMIT, BASELINE_DIR + '/' + part['path'])
            need(part['offset'] == offset and len(actual) == part['bytes'] and digest(actual) == part['sha256'] and
                 actual == raw[offset:offset + len(actual)], 'Published archive part differs: ' + part['path'])
            offset += len(actual)
            published_parts_checked += 1
        need(offset == len(raw), 'Published archive part coverage incomplete')
        frozen[path] = row['sha256']
    need(frozen[prior_archives['ACTUAL_EVIDENCE_DICT64.json.xz']] == BASELINE_SHA, 'Wrong original 625-file evidence capsule')
    baseline_doc = json.loads(lzma.decompress(prior_archives['ACTUAL_EVIDENCE_DICT64.json.xz'].read_bytes()))
    baseline = decode_members(baseline_doc)
    need(len(baseline) == baseline_doc['file_count'] == 625, 'Original evidence count differs')
    delta_doc = json.loads(lzma.decompress((checkpoint / 'EVIDENCE_DELTA_DICT64.json.xz').read_bytes()))
    changed = decode_members(delta_doc)
    full_doc = json.loads(lzma.decompress((checkpoint / 'FULL_EVIDENCE_LOCAL_ONLY.json.xz').read_bytes()))
    full = decode_members(full_doc)
    references = delta_doc['reused_published_files']
    need(delta_doc['baseline_publication'] == BASELINE_COMMIT and delta_doc['baseline_evidence_sha256'] == BASELINE_SHA and
         len(changed) == delta_doc['new_or_revised_file_count'] == delivery['new_or_revised_evidence_files'] == 147 and
         len(references) == delivery['reused_evidence_files'] == 628, 'Delta count/base binding differs')
    reconstructed = {}
    reference_sources = collections.Counter()
    for name, row in references.items():
        need(name not in changed, 'Duplicate delta/reference member: ' + name)
        if row['source'] == 'published_evidence_capsule':
            need(row['member'] == name, 'Original capsule reference renamed')
            raw = baseline[row['member']]
        else:
            need(row['source'] == 'published_repository_file', 'Unknown evidence reference kind')
            raw = git_blob(BASELINE_COMMIT, row['repository_path'])
        need(len(raw) == row['bytes'] and digest(raw) == row['sha256'], 'Published reference mismatch: ' + name)
        reconstructed[name] = raw
        reference_sources[row['source']] += 1
    reconstructed.update(changed)
    need(reconstructed == full and len(full) == full_doc['file_count'] == delta_doc['full_current_file_count'] == 775,
         'Delta plus published references does not equal the full frozen evidence')
    revised = {name for name in changed if name in baseline}
    need(revised == {'DECODER_RESUME.log', 'SUMMARY_DECODER.json'} and set(baseline) <= set(full),
         'Unexpected replacement/removal of old evidence')
    need(reference_sources == {'published_evidence_capsule': 623, 'published_repository_file': 5},
         'Expected 623 original members plus 5 published failure files')
    need(all(changed[n] != baseline[n] for n in revised), 'Unchanged old file republished as a delta')
    files = reconstructed
    def fj(name):
        return json.loads(files[name])

    verification = read(checkpoint / 'VERIFICATION.json')
    index_doc = read(checkpoint / 'ACCEPTED_OBJECT_INDEX.json')
    index = index_doc['project_objects']
    need(verification['verified_checkpoint'] is True and verification['partial_checkpoint'] is True and
         verification['accepted'] is False and index_doc['all_63_accepted'] is False and
         len(index) == index_doc['accepted_new_owner_count'] == verification['accepted_new_owner_count'] == 55 and
         set(index) == set(verification['owners']), 'Wrong partial acceptance scope')
    need(all(document.get('P2_5_proved') is False for document in (delivery, delta_doc, full_doc, verification, index_doc)) and
         all(document.get('physical_geometry_proved') is False for document in (delta_doc, full_doc, verification, index_doc)) and
         verification['all_fourteen_cell_q96_endpoint_proved'] is False and
         delta_doc['complete_all_63'] is full_doc['complete_all_63'] is False, 'Unproved endpoint promoted')
    need(verification['successful_stages'] == {'NORMAL': 55, 'REPLAY': 55, 'AUDIT': 55} and
         verification['before_after_contexts_verified'] == 330 and
         verification['candidate_lean_sources_modified'] == verification['prior_project_owners_recompiled'] == 0,
         'Stage counts or source-reuse claim differs')
    need(verification['source_publication'] == SOURCE_COMMIT and
         digest(files['consolidate.py']) == verification['consolidator_sha256'], 'Source/consolidator origin changed')
    need(files['CHECKPOINT_VERIFICATION_002.json'] == (checkpoint / 'VERIFICATION.json').read_bytes(),
         'Packaged final checkpoint differs from its evidence member')

    package_relative = 'docs/source-only/20261127-p2-5-cell03-finite'
    package = repo / package_relative
    source_manifest_raw = git_blob(SOURCE_COMMIT, package_relative + '/MANIFEST.json')
    expected_raw = git_blob(SOURCE_COMMIT, package_relative + '/PUBLIC_EXPECTATIONS.json')
    need(digest(source_manifest_raw) == MANIFEST_SHA == verification['source_manifest_sha256'] and
         source_manifest_raw == (package / 'MANIFEST.json').read_bytes() and
         digest(expected_raw) == PUBLIC_SHA == verification['public_expectations_sha256_from_original_source_commit'] and
         expected_raw == (package / 'PUBLIC_EXPECTATIONS.json').read_bytes(), 'Original manifest/public expectations changed')
    source_manifest = json.loads(source_manifest_raw)
    candidates = {q['module']: q for q in source_manifest['local_topological_order']}
    expected = json.loads(expected_raw)['modules']
    need(len(candidates) == len(expected) == 63 and set(candidates) == set(expected), 'Original source scope differs')
    missing = set(candidates) - set(index)
    need(missing == set(verification['missing_new_owners']) and len(missing) == 8, 'Missing-owner accounting differs')
    inputs = fj('INPUTS.json')
    need(inputs['manifest_sha256'] == MANIFEST_SHA and inputs['source_publication'] == SOURCE_COMMIT,
         'Input evidence has different source publication')
    runtime = inputs['runtime_hashes']
    need(len(runtime) == inputs['external_files'] == verification['external_files_frozen_and_rehashed'] == 15940 and
         jsig(runtime) == inputs['external_map_sha256'] == verification['external_map_sha256'], 'Runtime map binding differs')
    external_modules = {p.removesuffix('.olean').split('/lib/lean/', 1)[1].replace('/', '.')
                        for p in runtime if p.endswith('.olean')}
    need(len(external_modules) == inputs['external_modules'] == verification['external_modules_frozen'] == 5312,
         'External module count differs')
    compiler_root = repo.parent / 'p25-compiler'
    for original, h in runtime.items():
        if original.startswith('/mathlib/'):
            p = compiler_root / 'mathlib' / original.removeprefix('/mathlib/')
        else:
            prefix = '/workspace/toolchains/lean-4.33.0-rc1-linux/'
            need(original.startswith(prefix), 'Unexpected runtime path')
            p = compiler_root / 'lean-4.33.0-rc1-linux' / original.removeprefix(prefix)
        need(sha(p) == h, 'Current finite runtime differs: ' + original)

    checkpoint_path = repo / source_manifest['full_existing_object_checkpoint']['path']
    need(sha(checkpoint_path) == source_manifest['full_existing_object_checkpoint']['sha256'] ==
         inputs['historical_checkpoint_sha256'], 'Historical 246-object checkpoint changed')
    historical_all = read(checkpoint_path)['project_objects']
    historical = inputs['historical_project_objects']
    need(len(historical_all) == 246 and len(historical) == verification['prior_project_owners_reused'] == 17,
         'Historical dependency count differs')
    object_hashes = {m: q['sha256'] for m, q in historical.items()}
    object_hashes.update({m: q['sha256'] for m, q in index.items()})
    source_graph = verification['source_graph']
    need(set(source_graph) == set(historical) | set(candidates) and len(source_graph) == 80,
         'Source graph does not cover exactly 63 candidates plus 17 historical modules')
    sources, imports = {}, {}
    for m, row in source_graph.items():
        p = repo / row['path']
        raw = p.read_bytes()
        need(raw == git_blob(SOURCE_COMMIT, row['path']) and digest(raw) == row['sha256'],
             'Source differs from original publication: ' + m)
        direct = re.findall(r'^import (ImbalancedChen\.[\w.]+)', raw.decode(), re.M)
        need(direct == row['imports'], 'Source import graph differs: ' + m)
        if m in candidates:
            q = candidates[m]
            need(q['sha256'] == row['sha256'] and q['direct_project_imports'] == direct and
                 len(raw) == q['bytes'] and row['path'] == package_relative + '/' + q['path'],
                 'Original candidate manifest row differs: ' + m)
        else:
            q = historical[m]
            need(all(q[k] == v for k, v in historical_all[m].items()) and row['sha256'] == q['source_sha256'],
                 'Historical source/object lineage differs: ' + m)
        sources[m], imports[m] = raw, direct
        frozen[p] = row['sha256']
    visiting = set()
    @functools.cache
    def closure(m):
        need(m not in visiting, 'Project import cycle: ' + m)
        visiting.add(m)
        result = {m}.union(*(closure(d) for d in imports[m]))
        visiting.remove(m)
        return frozenset(result)
    need(set().union(*(closure(m) for m in candidates)) - set(candidates) == set(historical),
         'Historical dependency closure differs')
    for m in index:
        need(closure(m) <= set(object_hashes), 'Accepted owner depends on an unaccepted owner: ' + m)
    for m, row in {**historical, **index}.items():
        p = root / 'objects' / (m.replace('.', '/') + '.olean')
        need(p.stat().st_size == row['bytes'] and sha(p) == row['sha256'] and
             not any(Path(str(p) + s).exists() for s in ('.private', '.server')), 'Current accepted object differs: ' + m)
    for m in missing:
        need(not (root / 'objects' / (m.replace('.', '/') + '.olean')).exists(), 'Unaccounted object for pending owner: ' + m)

    # Verify all 55 cache objects in the two existing archives, without extraction.
    old_object_modules = {m for m, row in index.items() if row['object_origin']['archive'] == 'SIMPLEX05_NEW_DEPS.tar.xz'}
    new_object_modules = set(index) - old_object_modules
    need(len(old_object_modules) == index_doc['reused_published_object_count'] == delivery['reused_published_objects'] == 7 and
         len(new_object_modules) == index_doc['objects_in_this_new_archive'] == delivery['new_objects_in_archive'] == 48,
         'Old/new cache partition differs')
    transfer = read(root / 'SIMPLEX05_MINIMAL_TRANSFER.json')
    old_seven = {m for m, row in transfer['project_dependencies'].items() if row['kind'] == 'new_Cell03_accepted_object'}
    need(old_object_modules == old_seven, 'The seven already-published objects were not excluded exactly')
    archive_records = {}
    for path, modules in [(prior_archives['SIMPLEX05_NEW_DEPS.tar.xz'], old_object_modules),
                          (checkpoint / 'NEW_ACCEPTED_OBJECTS.tar.xz', new_object_modules)]:
        archive_sha = sha(path)
        wanted = {index[m]['archive_member']: m for m in modules}
        with tarfile.open(path, 'r:xz') as tar:
            members = tar.getmembers()
            need(len(members) == len(wanted) and {member.name for member in members} == set(wanted) and
                 all(member.isfile() for member in members), 'Archive scope or member type differs: ' + path.name)
            for member in members:
                m = wanted[member.name]
                row = index[m]
                need(member.name == 'objects/' + m.replace('.', '/') + '.olean' and member.size == row['bytes'] and
                     hashlib.file_digest(tar.extractfile(member), 'sha256').hexdigest() == row['sha256'],
                     'Cache member bytes differ: ' + m)
                origin = row['object_origin']
                need(origin['archive_sha256'] == archive_sha, 'Cache origin archive binding differs: ' + m)
                if m in old_object_modules:
                    need(origin['publication_commit'] == BASELINE_COMMIT and origin['publication_directory'] == BASELINE_DIR,
                         'Old object publication differs: ' + m)
        archive_records[path.name] = {'sha256': archive_sha, 'bytes': path.stat().st_size, 'objects_checked': len(modules)}

    template_path = repo / 'docs/source-only/20261126-p2-5-cell00-decoded/TYPED_PAYLOAD_AUDIT.lean'
    appendix_path = repo / 'docs/source-only/20261126-p2-5-cell00-field-split/PRIVATE_SCOPED_SIMP_AUDIT_APPENDIX.lean'
    need(sha(template_path) == TEMPLATE_SHA == inputs['audit_template_sha256'] == verification['audit_template_sha256'] and
         sha(appendix_path) == APPENDIX_SHA == verification['private_scoped_simp_appendix_sha256'], 'Original complete audit templates changed')
    template = template_path.read_text()
    # Generated equation declarations may recur, but must match accepted Cell01 types and axioms exactly.
    equation_reference = None
    for m in ['ImbalancedChen.P2Saving16Cell01Simplex00Decode', 'ImbalancedChen.P2Saving16Cell01Simplex01Decode']:
        q = historical_all[m]
        p = compiler_root / q['result_path']
        need(sha(p) == q['result_sha256'], 'Accepted Cell01 equation-reference receipt changed')
        old = read(p)
        log = p.parent / 'AUDIT.log'
        need(sha(log) == old['complete_owned_audit_log_sha256'], 'Accepted Cell01 equation-reference audit changed')
        eqs = {d['name']: {k: v for k, v in d.items() if k != 'module'} for d in marks(log.read_bytes())['P0_QUEUE_DECL']
               if d['name'] in EQUATIONS}
        need(set(eqs) == EQUATIONS and (equation_reference is None or eqs == equation_reference), 'Cell01 generated-equation references disagree')
        equation_reference = eqs

    owned, seen_names, equation_occurrences, stage_times = {}, {}, collections.defaultdict(list), collections.Counter()
    actual_external_counts = collections.Counter()
    owner_records = {}
    for m, row in sorted(index.items()):
        name, folder = m.split('.')[-1], 'evidence/' + m.split('.')[-1] + '/'
        raw = files[folder + 'RESULT.json']
        r = json.loads(raw)
        vrow = verification['owners'][m]
        need(digest(raw) == row['result_sha256'] == vrow['result_sha256'] and r['accepted'] is True and r['module'] == m and
             r['source_sha256'] == row['source_sha256'] == source_graph[m]['sha256'] and
             r['object_sha256'] == row['sha256'] == vrow['object_sha256'] and r['object_bytes'] == row['bytes'] == vrow['object_bytes'] and
             r['manifest_sha256'] == MANIFEST_SHA, 'Owner source/object receipt differs: ' + m)
        need(row['source_path'] == source_graph[m]['path'] and row['direct_project_imports'] == imports[m], 'Object index source differs: ' + m)
        audit = template.replace('P2Saving16Cell00TypedPayload', name)
        if name == 'P2Saving16Cell03ScalarDecode':
            audit = audit.replace('names.size > 0', 'names.size == 0')
        private_names = []
        if name == 'P2Saving16Cell03FieldSimp':
            private_names = re.findall(r'^private theorem (\w+)', sources[m].decode(), re.M)
            strings = ',\n    '.join(json.dumps('ImbalancedChen.P2Saving16Cell03FieldDecode.' + n) for n in private_names)
            appendix = appendix_path.read_text().replace('Cell00', 'Cell03')
            appendix = re.sub(r'(let expected : Array String := #\[).*?(\]\n  let simpTheorems)',
                              lambda z: z[1] + strings + z[2], appendix, count=1, flags=re.S)
            audit += '\n' + appendix
        need(files['audits/' + name + '.lean'] == audit.encode() and digest(audit.encode()) == r['audit_sha256'] == vrow['audit_sha256'],
             'Auditor differs from exact original template: ' + m)
        stages = fj(folder + 'STAGES.json')
        need(stages == r['stages'] and [(s['stage'], s['exit_code']) for s in stages] == [(label, 0) for label in LABELS],
             'Incomplete accepted stage sequence: ' + m)
        commands = {'NORMAL': [inputs['compiler'], *FLAGS, '--root=' + str(package), '-o',
                               str(root / 'objects' / (m.replace('.', '/') + '.olean')), str(repo / row['source_path'])],
                    'REPLAY': [inputs['stock_checker'], '-v', m],
                    'AUDIT': [inputs['compiler'], *FLAGS, '--root=' + str(root / 'audits'), str(root / 'audits' / (name + '.lean'))]}
        deps = {d: object_hashes[d] for d in closure(m) - {m}}
        for stage in stages:
            label = stage['stage']
            need(stage['argv'] == commands[label] and stage['log_sha256'] == digest(files[folder + label + '.log']) ==
                 r[LABELS[label]] == vrow[LABELS[label]], 'Actual command or stage log differs: ' + m + '/' + label)
            stage_times[label] += stage['elapsed_seconds']
            before, after = [fj(folder + label + '_' + phase + '_CONTEXT.json') for phase in ('BEFORE', 'AFTER')]
            need(before['started_utc'] <= before['ended_utc'] <= stage['started_utc'] <= after['started_utc'] <= after['ended_utc'],
                 'Actual local stage/context ordering differs: ' + m)
            for phase, context in [('BEFORE', before), ('AFTER', after)]:
                need(context['external_files'] == 15940 and context['external_map_sha256'] == inputs['external_map_sha256'] and
                     context['manifest_sha256'] == MANIFEST_SHA and context['source_sha256'] == row['source_sha256'] and
                     context['project_dependencies'] == deps, 'Stage dependency/source/runtime context differs: ' + m)
                need(context.get('owner_object_sha256') == (None if (label, phase) == ('NORMAL', 'BEFORE') else row['sha256']),
                     'Owner object changed between stages: ' + m)
        data = marks(files[folder + 'AUDIT.log'])
        need(len(data['P0_QUEUE_INVENTORY']) == len(data['P0_QUEUE_IMPORTS']) == 1, 'Missing/duplicate native inventory: ' + m)
        inventory, = data['P0_QUEUE_INVENTORY']
        imported, = data['P0_QUEUE_IMPORTS']
        declarations = data['P0_QUEUE_DECL']
        names = [d['name'] for d in declarations]
        need(inventory['module'] == m and declarations == fj(folder + 'DECLARATIONS.json') and
             len(names) == len(set(names)) == len(inventory['serialized']) == len(inventory['environment']) ==
             r['owned_count'] == row['owned_count'] == vrow['owned_count'] and
             sorted(names) == sorted(inventory['serialized']) == sorted(inventory['environment']), 'Incomplete owned inventory: ' + m)
        need((not names) == (name == 'P2Saving16Cell03ScalarDecode') and set(expected[m]) <= set(names) and
             len(expected[m]) == r['public_expectations_matched'], 'Public lower bound or import-only exception differs: ' + m)
        need(len(imported) == len(set(imported)) == r['imports_count'] and
             {i for i in imported if i.startswith('ImbalancedChen.')} == closure(m) == set(r['project_imports']) and
             set(imported) - closure(m) <= external_modules and
             len(set(imported) - closure(m)) == r['external_modules'], 'Actual imported closure differs: ' + m)
        actual_external_counts[r['external_modules']] += 1
        for declaration in declarations:
            need(declaration['module'] == m and all(declaration.get(k) is False for k in ('unsafe', 'partial', 'axiom')) and
                 isinstance(declaration['type'], str) and declaration['type'] and '⋯' not in declaration['type'] and
                 isinstance(declaration['axioms'], list) and set(declaration['axioms']) <= AXIOMS, 'Invalid owned declaration: ' + declaration['name'])
            normalized = {k: v for k, v in declaration.items() if k != 'module'}
            dname = declaration['name']
            if dname in EQUATIONS:
                need(normalized == equation_reference[dname], 'Generated equation differs from accepted Cell01: ' + dname)
                equation_occurrences[dname].append(m)
            if dname in seen_names:
                need(dname in EQUATIONS and seen_names[dname] == normalized, 'Unexpected differing cross-owner declaration: ' + dname)
            seen_names[dname] = normalized
        need(sorted({a for d in declarations for a in d['axioms']}) == r['transitive_axioms'], 'Transitive axiom summary differs')
        if private_names:
            scope, = data['P25_PRIVATE_SCOPED_SIMP_INTERFACE']
            expected_private = {'ImbalancedChen.P2Saving16Cell03FieldDecode.' + n for n in private_names}
            matches = scope['matches']
            need(scope['module'] == m and scope['scope'] == 'ImbalancedChen.P2Saving16Cell03FieldDecode' and
                 len(expected_private) == len(matches) == scope['required_count'] == scope['matched_count'] == 576 and
                 {d['user_name'] for d in matches} == expected_private and len({d['actual_name'] for d in matches}) == 576 and
                 {d['actual_name'] for d in matches} <= set(names), 'Private scoped simp interface differs')
        else:
            need(not data['P25_PRIVATE_SCOPED_SIMP_INTERFACE'], 'Unexpected scoped simp audit record')
        owned[m] = len(names)
        owner_records[m] = {'source_sha256': row['source_sha256'], 'object_sha256': row['sha256'],
                            'receipt_sha256': row['result_sha256'], 'owned_count': len(names),
                            'closure_size': len(closure(m)), 'stages_checked': 3, 'contexts_checked': 6}
    need(sum(owned.values()) == verification['total_new_owned_declarations'] == 3127 and
         len(seen_names) == verification['distinct_owned_declaration_names'] == 3093 and
         owned == verification['owned_declarations_by_module'] and
         dict(equation_occurrences) == verification['repeated_generated_equation_names'], 'Actual complete declaration counts differ')
    need({k: round(v, 3) for k, v in stage_times.items()} == verification['stage_wall_seconds_sum'], 'Stage timing aggregate differs')

    # Historical failed audit and all three resource-terminated attempts remain evidence.
    failures = []
    for name, raw in files.items():
        if name.endswith('/STAGES.json') and name.startswith(('evidence/', 'failed-attempts/')):
            for stage in json.loads(raw):
                if stage['exit_code'] != 0:
                    log_path = str(Path(name).parent / (stage['stage'] + '.log'))
                    need(digest(files[log_path]) == stage['log_sha256'], 'Historical failure log differs')
                    failures.append({'stages_file': name, **stage})
    need(sorted(failures, key=lambda x: x['stages_file']) == sorted(verification['historical_failed_stages'], key=lambda x: x['stages_file']) and
         collections.Counter(s['stage'] for s in failures) == {'NORMAL': 3, 'AUDIT': 1}, 'Failure history was omitted or promoted')
    for suffix in ('05', '10', '18'):
        m = 'ImbalancedChen.P2Saving16Cell03Simplex' + suffix + 'Decode'
        folder = 'evidence/' + m.split('.')[-1] + '/'
        stages = fj(folder + 'STAGES.json')
        need(len(stages) == 1 and stages[0]['exit_code'] == -9 and stages[0]['stage'] == 'NORMAL' and
             files[folder + 'NORMAL.log'] == b'' and m in missing, 'Resource failure reclassified: ' + m)
        for phase in ('BEFORE', 'AFTER'):
            c = fj(folder + 'NORMAL_' + phase + '_CONTEXT.json')
            need(not c.get('owner_object_sha256') and c['source_sha256'] == source_graph[m]['sha256'] and
                 c['external_map_sha256'] == inputs['external_map_sha256'] and
                 c['project_dependencies'] == {d: object_hashes[d] for d in closure(m) - {m}}, 'Resource failure inputs differ: ' + m)
    simp = 'evidence/P2Saving16Cell03FieldSimp/'
    old_stages = fj(simp + 'failed-public-empty-inference/STAGES.json')
    need([s['exit_code'] for s in old_stages] == [0, 0, 1] and old_stages[:2] == fj(simp + 'RESULT.json')['stages'][:2] and
         files[simp + 'failed-public-empty-inference/AUDIT.lean'].decode().replace('names.size == 0', 'names.size > 0') ==
         files['audits/P2Saving16Cell03FieldSimp.lean'].decode(), 'FieldSimp repair did not preserve original successful stages')
    prior_index = read(root / 'checkpoint-001/NEW_ACCEPTED_OBJECTS.json')['project_objects']
    need(len(prior_index) == 45 and set(prior_index) <= set(index), 'Original 45-owner checkpoint lost acceptance')
    for m, q in prior_index.items():
        need(q['sha256'] == index[m]['sha256'] and q['source_sha256'] == index[m]['source_sha256'] and
             q['result_sha256'] == index[m]['result_sha256'], 'Previously accepted owner was repeated or changed: ' + m)
    for p, h in frozen.items():
        need(sha(p) == h, 'Input changed during independent review: ' + str(p))

    return {'schema': 'p25-cell03-independent-delta-review-v1', 'review_passed': True,
            'source_publication': SOURCE_COMMIT, 'baseline_publication': BASELINE_COMMIT,
            'checkpoint_delivery_sha256': DELIVERY_SHA, 'review_script_sha256': sha(Path(__file__)),
            'baseline_members_verified': 625, 'reused_reference_sources': dict(reference_sources),
            'new_or_revised_members_verified': 147, 'full_reconstructed_members_verified': 775,
            'revised_baseline_members': sorted(revised), 'published_archive_parts_verified': published_parts_checked,
            'accepted_owner_count': 55, 'prior_accepted_owners_unchanged': 45, 'newly_accepted_since_baseline': 10,
            'source_graph_modules_verified_against_68703': 80, 'current_external_files_rehashed': 15940,
            'frozen_external_modules': 5312, 'actual_external_module_count_distribution': dict(actual_external_counts),
            'historical_dependency_objects_verified': 17,
            'object_archives_verified': archive_records, 'complete_owned_records': 3127,
            'distinct_declaration_names': 3093, 'repeated_equations_verified_against_Cell01': dict(equation_occurrences),
            'successful_stages_checked': 165, 'contexts_checked': 330, 'exact_audit_programs_checked': 55,
            'private_scoped_simp_theorems_checked': 576, 'historical_failed_stages_preserved': dict(collections.Counter(s['stage'] for s in failures)),
            'missing_owners': sorted(missing), 'all_63_accepted': False, 'physical_geometry_proved': False,
            'P2_5_proved': False, 'gaps_found_in_claimed_55_owner_checkpoint': [], 'lean_invocations': 0, 'remote_jobs': 0,
            'review_completed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'owners': owner_records}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path('/workspace/scratch/674430b6afba/cell03-verify'))
    parser.add_argument('--repo', type=Path, default=Path('/workspace/scratch/ffd83d72c265/goldbach-formalization'))
    args = parser.parse_args()
    try:
        result = review(args)
    except Exception as error:
        (HERE / 'REVIEW_FAILED.json').write_text(json.dumps({'review_passed': False, 'error': str(error),
            'P2_5_proved': False, 'review_script_sha256': sha(Path(__file__))}, indent=2) + '\n')
        raise
    (HERE / 'REVIEW.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('owners', 'repeated_equations_verified_against_Cell01')}, indent=2))


if __name__ == '__main__':
    main()
