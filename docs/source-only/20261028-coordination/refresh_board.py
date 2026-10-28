"""Root-only source/board inventory; never calls a compiler or proof checker."""
from pathlib import Path
import ast
import collections
import datetime
import hashlib
import json
import re
import subprocess

BASE = Path(__file__).resolve().parent
REPO = BASE.parents[2]
WORKSPACE = REPO.parent
SITE = WORKSPACE / 'sites/goldbach-proof-progress-20261021'
BATCHES = ['20261028-resume-30', '20261028-resume-30b', '20261028-resume-30c', '20261028-resume-30d', '20261028-resume-30e', '20261028-resume-30f', '20261028-resume-30g']

def read(p):
    return json.loads(p.read_text(encoding='utf-8-sig'))

def write(p, x):
    p.write_text(json.dumps(x, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def verified_head_fields(head, publication, extra_publication, metadata_publication=None):
    for receipt, name, key in [(publication, 'PUBLICATION.json', 'head'),
                               (extra_publication, 'EXTRA_PUBLICATION.json', 'commit'),
                               (metadata_publication or {}, 'METADATA_PUBLICATION.json', 'commit')]:
        if receipt.get('remote_exact_sha_verified') and receipt.get(key) == head:
            return {'commit': head, 'remoteExactShaVerified': True,
                    'remote': 'Exact SHA in dated root publication receipt',
                    'receipt': 'docs/source-only/20261028-coordination/' + name,
                    'receiptCapturedUtc': receipt.get('captured_utc')}
    return {'commit': head, 'remoteExactShaVerified': False,
            'remote': 'This current HEAD has no matching remote verification in the dated proof/extra receipts; no remote check was run by this inventory.'}

def sync_production_census_fields(update, census):
    source = update.setdefault('sourceCensus', {})
    source.update({'localLeanFiles': census.get('local_lean_files'),
                   'trackedLeanFiles': census.get('tracked_HEAD_lean_files'),
                   'trackedHeadLeanFiles': census.get('tracked_HEAD_lean_files'),
                   'trackedIndexLeanFiles': census.get('tracked_index_lean_files'),
                   'capturedUtc': census.get('captured_utc'), 'censusHead': census.get('HEAD'),
                   'scope': 'Fresh production file-path census only; docs/source-only and packages excluded. Historical formal acceptance is unchanged.',
                   'snapshotOnly': True, 'pureCodeLines': None,
                   'basis': f"Dated path census {census.get('captured_utc')}: local {census.get('local_lean_files')}, tracked HEAD {census.get('tracked_HEAD_lean_files')}, existing user index {census.get('tracked_index_lean_files')}. Index differences reflect pre-existing staged state; no deletion or index mutation is claimed.",
                   'trackedLeanFilesBasis': 'Git HEAD, not the current staged index.',
                   'indexScope': 'Existing user-index snapshot, not source disappearance or new formal credit.',
                   'receipt': 'docs/source-only/20261028-coordination/PRODUCTION_CENSUS.json',
                   'lexicalRecountPerformed': False})

def sync_roster_fields(update, roster, proof_tasks):
    """Use the dated direct observation, never the assignment plan, for live labels."""
    counts, plan = roster.get('observed_counts', {}), roster.get('plan', {})
    observed = {}
    for item in roster.get('agents', []):
        state = item.get('observed_state')
        raw = item.get('agent_status')
        if not state:
            state = raw if isinstance(raw, str) else next(iter(raw), 'unknown') if isinstance(raw, dict) else 'unknown'
        observed[item['agent_name']] = state
    for key, state in [('active_running_including_root', 'running'), ('completed', 'completed'),
                       ('interrupted', 'interrupted'), ('errored_capacity', 'error')]:
        for name in roster.get(key, []):
            observed.setdefault(name, state)
    captured = roster.get('captured_utc') or roster.get('captured_host_utc_minute')
    update['rosterSnapshot'] = {
        'path': './current-roster.json', 'capturedUtcMinute': roster.get('captured_host_utc_minute'),
        'capturedUtc': captured, 'captureWindowUtc': roster.get('capture_window_utc'),
        'authority': roster.get('authority'), 'listedThreadCount': counts.get('all_listed_threads_including_root'),
        'runningIncludingRoot': counts.get('running_including_root'), 'runningChildren': counts.get('running_children'),
        'plannedChildLimit': plan.get('child_thread_active_limit'), 'plan': plan,
        'capacityErrors': counts.get('capacity_errors'), 'completed': counts.get('completed'),
        'interrupted': counts.get('interrupted'), 'activeRatio': counts.get('active_children_vs_limit'),
        'priorityProofWorkers': plan.get('priority_proof_workers'),
        'observedRoleCounts': roster.get('observed_role_counts', {}),
        'note': 'Counts and states belong only to this dated direct snapshot; plan allocation is not platform capacity.'}

    def slot(name, owners):
        states = collections.Counter(observed.get(owner, 'not_listed') for owner in owners)
        status = 'running' if states['running'] else 'completed' if owners and states['completed'] == len(owners) else 'interrupted' if states['interrupted'] else 'pending'
        details = ', '.join(f'{count} {state}' for state, count in sorted(states.items()))
        return {'name': name, 'owner': ', '.join(owners), 'status': status,
                'observedOwnerIds': [owner for owner in owners if owner in observed], 'stateCounts': dict(states),
                'capturedUtc': captured, 'focus': f'Direct snapshot {captured}: {details}. Original proof targets remain OPEN.'}

    lanes = collections.OrderedDict()
    for task in proof_tasks:
        lanes.setdefault(task['lane'], []).append('/root/' + task['id'])
    slots = [slot(lane, owners) for lane, owners in lanes.items()]
    reviewers = ['/root/dependency_inventory', '/root/manuscript_map', '/root/review_lower',
                 '/root/review_upper', '/root/review_certificate', '/root/review_pp_transfer']
    extra_reviewer = '/root/manuscript_map/review_physical'
    if extra_reviewer in observed:
        reviewers.append(extra_reviewer)
    for name, owners in [('adopted-integration', ['/root/adopted_plan']),
                         ('independent-review', reviewers), ('compiler-intake', ['/root/intake_inventory']),
                         ('ops', ['/root/board_resume30'])]:
        slots.append(slot(name, owners))
    update['leadSlots'] = slots

def sync_pause_fields(update, pause):
    """Apply explicit root stop evidence without reading quota or changing source bytes."""
    if pause.get('operation_state') != 'paused':
        return
    update['operationState'] = 'paused'
    update['pauseState'] = pause
    update['candidateStatus'] = 'paused_original_targets_open'
    for step in update.get('internalSteps', []):
        if step.get('status') != 'deferred':
            step['status'] = 'paused_open'
    for item in update.get('graph', {}).get('nodes', []):
        if item.get('status') != 'deferred':
            item['status'] = 'paused_open'
    for slot in update.get('leadSlots', []):
        if slot.get('name') not in ['ops', 'compiler-intake'] and slot.get('status') != 'completed':
            slot['status'] = 'paused'
            slot['focus'] += ' Root stopped proof/review generation; existing partials only, original targets OPEN.'

def pause_source_snapshot(snapshot, pause):
    """Mark active stopped scope separately from preserved historical review evidence."""
    if pause.get('operation_state') != 'paused':
        return
    active = pause.get('active_batch')
    snapshot['operation_state'] = 'paused'
    snapshot['pause_state'] = pause
    for task in snapshot.get('tasks', []):
        task.setdefault('latest_recorded_review_status_before_pause', task.get('review_status'))
        task['status'] = 'paused_unreviewed'
        task['review_status'] = 'PAUSED_UNREVIEWED'
        task['active_execution_status'] = 'paused'
        for item in task.get('batches', []):
            if item.get('batch') == active:
                item.setdefault('review_evidence_status_before_pause', item.get('review_status'))
                item['status'] = 'paused_unreviewed'
                item['review_status'] = 'PAUSED_UNREVIEWED'
                item['generation_state'] = 'paused'
                item['review_scope_note'] = 'Existing file evidence only; complete active-batch review not accepted.'
    for row in snapshot.get('batch_summaries', []):
        if row.get('batch') == active:
            row.update(operation_state='paused', publication=row.get('publication') if row.get('remote_reachable_from_verified_head') else 'paused_local_snapshot', reviewed_tasks=0,
                       paused_tasks=row.get('tasks', 0))
    summary = snapshot.get('summary', {})
    summary['operation_state'] = 'paused'
    summary['active_batch_paused_tasks'] = len(snapshot.get('tasks', []))
    summary['active_batch_reviewed_tasks'] = 0
    summary['latest_delivery_reviewed_tasks'] = 0

# Reuse just the bounded lexer function; do not execute the older refresh script.
tree = ast.parse((REPO / 'docs/source-only' / BATCHES[0] / 'refresh_snapshot.py').read_text(encoding='utf-8'))
lexer = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'lean_code')
exec(compile(ast.Module(body=[lexer], type_ignores=[]), '<frozen source lexer>', 'exec'))

def strings(x):
    if isinstance(x, str): return [x]
    if isinstance(x, list): return [s for item in x for s in strings(item)]
    if isinstance(x, dict): return [s for item in x.values() for s in strings(item)]
    return []

def review_rows(x):
    out = []
    if isinstance(x, dict):
        tid = x.get('task_id') or x.get('task') or x.get('id')
        status = x.get('status') or x.get('verdict') or x.get('review_status')
        if tid and status: out.append((tid, status, x))
        for item in x.values(): out.extend(review_rows(item))
    elif isinstance(x, list):
        for item in x: out.extend(review_rows(item))
    return out

def source_entry(p):
    raw = p.read_text(encoding='utf-8-sig')
    code, closed = lean_code(raw)
    item = {'path': p.relative_to(REPO).as_posix(), 'sha256': sha(p),
            'lines': len(raw.splitlines()),
            'declarations': len(re.findall(r'(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|instance)\s', code)),
            'lexer_closed': closed,
            'forbidden_code_tokens': re.findall(r'\b(?:sorry|admit|axiom|unsafe)\b', code),
            'imports': re.findall(r'(?m)^import\s+(\S+)', code)}
    mapping = intake_index.get(item['path'])
    if mapping:
        item.update({'module_name': mapping.get('module_name'),
                     'installation_target': mapping.get('intended_install_relative_path'),
                     'intake_status': mapping.get('mapping_status') if mapping.get('source_sha256') == item['sha256'] else 'SNAPSHOT_STALE',
                     'ready_to_install': False})
    else:
        item['intake_status'] = 'MAPPING_NOT_YET_RECORDED'
    return item

now = datetime.datetime.now(datetime.timezone.utc).isoformat()
pause_path = BASE / 'PAUSE_STATE.json'
pause = read(pause_path) if pause_path.exists() else {}
publication = read(BASE / 'PUBLICATION.json')
local_freeze_path = BASE / 'F_LOCAL_FREEZE.json'
local_freeze = read(local_freeze_path) if local_freeze_path.exists() else {}
paused_pub_path = BASE / 'PAUSED_G_PUBLICATION.json'
paused_pub = read(paused_pub_path) if paused_pub_path.exists() else {}
extra_publication_path = BASE / 'EXTRA_PUBLICATION.json'
extra_publication = read(extra_publication_path) if extra_publication_path.exists() else {}
metadata_publication_path = BASE / 'METADATA_PUBLICATION.json'
metadata_publication = read(metadata_publication_path) if metadata_publication_path.exists() else {}
published_batches = {item['batch'] for item in publication['batches']}
intake_path = BASE / 'INTAKE_MANIFEST.json'
intake = read(intake_path) if intake_path.exists() else {}
intake_index = {item['source_path'].removeprefix(REPO.name + '/'): item for item in intake.get('candidates', [])}
initial = read(REPO / 'docs/source-only' / BATCHES[0] / 'TASKS.json')
combined = {t['id']: {**t, 'sources': [], 'batches': [], 'task_complete': False} for t in initial['tasks']}
summaries, snapshots, all_sources = [], {}, []
for name in BATCHES:
    folder = REPO / 'docs/source-only' / name
    ledger = read(folder / 'TASKS.json')
    dispatch_path = folder / 'DISPATCH_RECEIPT.json'
    dispatch_rows = read(dispatch_path).get('agents', []) if dispatch_path.exists() else []
    dispatch_by_id = {row['task_id']: row for row in dispatch_rows if row.get('task_id')}
    reviews = {}
    for p in sorted((folder / 'reviews').glob('*.json')):
        for tid, status, row in review_rows(read(p)):
            reviews[tid] = (status, row, p)
    entries = []
    for task in ledger['tasks']:
        tid = task['id']; dest = folder / tid
        dispatch = dispatch_by_id.get(tid, {})
        dispatch_status = dispatch.get('dispatch_status', task.get('dispatch_status', 'not_separately_recorded'))
        rp, report = dest / 'REGISTRY.json', dest / 'REPORT.md'
        reg = read(rp) if rp.exists() else {}
        sources = [source_entry(p) for p in sorted(dest.glob('*.lean'))]
        delivered = bool(sources and rp.exists() and report.exists())
        review = reviews.get(tid)
        reviewed = bool(review and review[0] == 'SOURCE_REVIEW_PASS' and delivered)
        remaining = list(dict.fromkeys(s for k, v in reg.items() if k.startswith('remaining') for s in strings(v)))
        if not remaining: remaining = strings(reg.get('hypotheses_not_eliminated', []))
        item = {**task, 'batch': name, 'sources': sources, 'remaining': remaining,
                'status': 'source_reviewed_task_open' if reviewed else 'source_delivered_review_pending' if delivered else 'writing',
                'dispatch_status': dispatch_status,
                'review_status': review[0] if reviewed else 'PENDING',
                'compiled': False, 'formal_credit': 0, 'task_complete': False,
                'local_step_complete': bool(reg.get('local_step_complete', reg.get('complete_module', False))),
                'delivered': delivered, 'author_original_task_complete': bool(reg.get('task_complete', False))}
        if not delivered and dispatch_status in ['waiting_predecessor', 'ready_pending_dispatch']:
            item['status'] = dispatch_status
        if review:
            item['review_path'] = review[2].relative_to(REPO).as_posix()
        if delivered:
            item['registry_sha256'] = sha(rp); item['report_sha256'] = sha(report)
        entries.append(item)
        target = combined[tid]
        target['batches'].append(item)
        target['sources'].extend(sources)
        if delivered:
            target.update({k: item[k] for k in ['remaining', 'status', 'review_status', 'review_path'] if k in item})
        target['active_target'] = task['target']
        target['active_batch'] = BATCHES[-1]
        target['active_dispatch_status'] = dispatch_status
        target['compiled'] = False; target['formal_credit'] = 0; target['task_complete'] = False
        all_sources.extend(sources)
    batch_sources = [s for item in entries for s in item['sources']]
    batch_paused = pause.get('operation_state') == 'paused' and name == pause.get('active_batch')
    if batch_paused:
        for item in entries:
            item['review_evidence_status_before_pause'] = item['review_status']
            item.update(status='paused_unreviewed', review_status='PAUSED_UNREVIEWED', generation_state='paused',
                        review_scope_note='Existing file evidence only; complete active-batch review not accepted.')
    summary = {'batch': name, 'publication': 'pushed_exact_bytes' if name in published_batches else 'paused_local_snapshot' if batch_paused else 'local_in_progress',
               'tasks': len(entries), 'delivered_tasks': sum(t['delivered'] for t in entries),
               'dispatch_counts': dict(collections.Counter(t['dispatch_status'] for t in entries)),
               'reviewed_tasks': sum(t['review_status'] == 'SOURCE_REVIEW_PASS' for t in entries),
               'source_files': len(batch_sources), 'raw_lines': sum(s['lines'] for s in batch_sources),
               'lexical_declarations': sum(s['declarations'] for s in batch_sources),
               'task_complete': 0, 'formal_credit': 0, 'compiled': False,
               'source_scan_issues': [s['path'] for s in batch_sources if not s['lexer_closed'] or s['forbidden_code_tokens']]}
    if name == local_freeze.get('batch') and name not in published_batches:
        summary.update(publication='reviewed_frozen_local_remote_pending', local_commit=local_freeze.get('commit'),
                       remote_exact_sha_verified=False, local_freeze_receipt='docs/source-only/20261028-coordination/F_LOCAL_FREEZE.json')
    summary['source_files_scope'] = 'Top-level per-author Lean candidates; nested frozen predecessor copies excluded.'
    if batch_paused and paused_pub.get('remote_reachable_from_verified_head'):
        summary.update(publication='paused_pushed_snapshot', remote_reachable_from_verified_head=True, remote_verified_head=paused_pub.get('remote_verified_head'))
    if batch_paused:
        summary['raw_lean_files'] = len(list(folder.rglob('*.lean')))
        summary['nested_non_candidate_lean_files'] = summary['raw_lean_files'] - len(batch_sources)
    summaries.append(summary)
    snapshots[name] = {'captured_utc': now, 'main_theorem': 'OPEN', 'summary': summary, 'tasks': entries}
    if batch_paused:
        snapshots[name].update(operation_state='paused', pause_state=pause)
    write(BASE / (name + '.json'), snapshots[name])

tasks = list(combined.values())
pending = [{'id': f"{t['id']}-next-{i+1}", 'parent': t['id'], 'lane': t['lane'], 'target': text,
            'status': 'open_remaining_obligation', 'owner_lane': '/root/' + t['id'],
            'responsibility': 'user_compiler' if re.match(r'(?i)^(compiler|compilation|all (held |source-only )?imports|all source-only dependencies)', text) else 'internal_proof_or_connection',
            'compiled': False, 'formal_credit': 0}
           for t in tasks for i, text in enumerate(t.get('remaining', []))]
summary = {'tasks': len(tasks), 'delivered_tasks': sum(bool(t['sources']) for t in tasks),
           'reviewed_tasks': sum(any(b['review_status'] == 'SOURCE_REVIEW_PASS' for b in t['batches']) for t in tasks),
           'latest_delivery_reviewed_tasks': sum(t.get('review_status') == 'SOURCE_REVIEW_PASS' for t in tasks),
           'source_files': len(all_sources), 'raw_lines': sum(s['lines'] for s in all_sources),
           'lexical_declarations': sum(s['declarations'] for s in all_sources), 'task_complete': 0,
           'formal_credit': 0, 'compiled': False, 'pending_obligations': len(pending),
           'source_scan_issues': [s['path'] for s in all_sources if not s['lexer_closed'] or s['forbidden_code_tokens']]}
summary['active_dispatch_counts'] = dict(collections.Counter(t.get('active_dispatch_status', 'not_separately_recorded') for t in tasks))
extra_by_id = {}
for name in BATCHES:
    extra_path = REPO / 'docs/source-only' / name / 'EXTRA_TASKS.json'
    if not extra_path.exists():
        continue
    for task in read(extra_path).get('tasks', []):
        folder = Path(task['source_directory'])
        if not folder.is_absolute():
            folder = REPO / folder
        extra = {**task, 'checklist_file': extra_path.relative_to(REPO).as_posix(),
                 'sources': [source_entry(p) for p in sorted(folder.glob('*.lean'))],
                 'task_complete': False, 'compiled': False, 'formal_credit': 0,
                 'counts_toward_regular_thirty': False}
        for filename, key in [('REGISTRY.json', 'registry_sha256'), ('REPORT.md', 'report_sha256')]:
            path = folder / filename
            if path.exists():
                extra[key] = sha(path)
        acceptance_path, independent_path = folder / 'ROOT_ACCEPTANCE.json', folder / 'reviews/independent.json'
        if acceptance_path.exists() and independent_path.exists():
            acceptance, independent = read(acceptance_path), read(independent_path)
            if independent.get('status') == 'SOURCE_REVIEW_PASS' and acceptance.get('review_sha256') == sha(independent_path):
                extra.update(status='source_reviewed_task_open', review_status='SOURCE_REVIEW_PASS',
                             review_scope=independent.get('status_scope'), reviewed_utc=independent.get('reviewed_utc'),
                             root_acceptance=acceptance_path.relative_to(REPO).as_posix(),
                             remote_publication_status='Determined separately by exact root publication receipt.')
        extra_by_id[task['id']] = extra
extra_tasks = list(extra_by_id.values())
extra_sources = [source for task in extra_tasks for source in task['sources']]
extra_summary = {'integration_owners': len({task['owner'] for task in extra_tasks}),
                 'registered_steps': len(extra_tasks), 'source_files': len(extra_sources),
                 'raw_lines': sum(s['lines'] for s in extra_sources),
                 'lexical_declarations': sum(s['declarations'] for s in extra_sources),
                 'counts_toward_regular_thirty': False, 'task_complete': 0, 'compiled': False, 'formal_credit': 0}
snapshot = {'schema': 'paper-first-multi-batch-source-snapshot-v1', 'captured_utc': now, 'goal': '1+1.748',
            'main_theorem': 'OPEN', 'summary': summary, 'batch_summaries': summaries, 'active_batch': BATCHES[-1],
            'extra_tasks': extra_tasks, 'extra_summary': extra_summary,
            'tasks': tasks, 'measurement_note': 'Raw text lines and lexical declaration syntax. No compilation, numerical replay, kernel acceptance or new formal credit.'}
snapshot['compiler_intake'] = {'captured_utc': intake.get('captured_utc'), 'summary': intake.get('summary'),
                               'scope': 'Proposed direct module/source mapping only; no installation, recursive import/axiom closure or kernel acceptance.'}
pause_source_snapshot(snapshot, pause)
if pause.get('operation_state') == 'paused':
    for item in pending:
        item['status'] = 'paused_open_obligation'
write(BASE / 'SOURCE_BATCHES.json', snapshot)
write(BASE / 'NEXT_ACTIONS.json', {'captured_utc': now, 'count': len(pending),
                                'operation_state': pause.get('operation_state', 'active'), 'pause_state': pause,
                                'active_steps': [{'id': t['id'], 'owner': '/root/' + t['id'], 'batch': t['active_batch'],
                                                  'target': t['active_target'], 'status': t.get('active_execution_status', t.get('active_dispatch_status', 'not_separately_recorded'))} for t in tasks],
                                'tasks': pending, 'extra_tasks': extra_tasks, 'extra_summary': extra_summary,
                                'extra_active_steps': [{'id': t['id'], 'owner': t['owner'], 'reviewer': t.get('reviewer'),
                                                        'target': t.get('current_target'), 'status': t.get('status'),
                                                        'counts_toward_regular_thirty': False}
                                                       for t in extra_tasks if t.get('status') != 'frozen_published_proposal']})
write(SITE / 'dist/resume30.json', snapshot)

# Root only: inspect just token_count rate limits, never other session contents.
quota = None
session = Path(r'C:\Users\timot\.codex\sessions\2026\10\28')
for p in session.glob('*01a18252-991a-7922-8389-fc3c129e127a.jsonl'):
    for line in p.open(encoding='utf-8'):
        try: event = json.loads(line)
        except ValueError: continue
        data = event.get('payload', {})
        if data.get('type') != 'token_count' or not data.get('rate_limits'): continue
        limits = data['rate_limits']
        used = max((w['used_percent'] for w in [limits.get('primary'), limits.get('secondary')] if w), default=None)
        if used is not None:
            quota = {'captured_utc': event.get('timestamp'), 'usedPercent': used, 'remainingPercent': 100-used,
                     'stopAtOrBelowPercent': 10, 'source': 'root session token_count.rate_limits; minimum remaining across reported windows'}
if quota: write(BASE / 'ROOT_QUOTA.json', quota)

update = read(SITE / 'dist/current-update.json')
roster_path = BASE / 'ROSTER_CAPTURE.json'
if roster_path.exists():
    roster = read(roster_path)
    sync_roster_fields(update, roster, tasks)
    write(SITE / 'dist/current-roster.json', roster)
active_plan = read(REPO / 'docs/source-only' / BATCHES[-1] / 'TASKS.json').get('plan_allocation')
if active_plan:
    update['futurePlan'] = {**active_plan, 'source': 'docs/source-only/' + BATCHES[-1] + '/TASKS.json',
                            'note': 'Root-approved future allocation; dated actual roster observations remain unchanged.'}
head = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=REPO, capture_output=True, text=True, check=True).stdout.strip()
repo_update = update['repositoryUpdate']
repo_update.update({'formalizationCommit': head, 'commitUrl': 'https://github.com/UyNewNas/goldbach-formalization/commit/' + head,
                    'sourceState': 'manuscript-internal source proposals; uncompiled, zero formal credit',
                    'delta': f"{len(BATCHES)} source batches; {summary['source_files']} Lean proposals, {summary['raw_lines']} raw lines, {sum(s['reviewed_tasks'] for s in summaries)} independently reviewed local deliveries. All 30 original targets OPEN; new kernel credit 0.",
                    'localSourceBatch': {'path': BASE.relative_to(REPO).as_posix(), 'captured_utc': now, 'summary': summary,
                                         'batch_summaries': summaries, 'source_review_is_kernel_acceptance': False},
                    'latestCommit': verified_head_fields(head, publication, extra_publication, metadata_publication)})
repo_update['sourceArchive']['historical'] = True
repo_update['latestSource'] = {'name': f'{len(published_batches)} reviewed 30-task source bundles', 'path': 'docs/source-only/' + sorted(published_batches)[-1],
                              'sourceState': 'Pushed exact-byte proposals; no production installation, compilation or kernel acceptance'}
repo_update['localSourceBatch']['published'] = bool(paused_pub.get('remote_reachable_from_verified_head'))
repo_update['localSourceBatch']['publication_note'] = f'{len(published_batches)} reviewed source batches pushed; the active paused unreviewed snapshot is also uploaded when its separate remote ancestry receipt is true. No compiler or formal credit.'
if local_freeze:
    repo_update['localFrozenSource'] = {key: local_freeze.get(key) for key in
                                      ['batch', 'commit', 'captured_utc', 'publication_status', 'source_reviewed_tasks', 'remote_exact_sha_verified', 'compiled', 'formal_credit']}
    repo_update['localFrozenSource']['receipt'] = 'docs/source-only/20261028-coordination/F_LOCAL_FREEZE.json'
production_census_path = BASE / 'PRODUCTION_CENSUS.json'
if production_census_path.exists():
    sync_production_census_fields(update, read(production_census_path))
update.setdefault('siteSource', {})['openingMetadataScope'] = 'Preserved original source-helper opening metadata; opening version/commit are historical, not a current live-version claim.'
site_receipt_path = BASE / 'SITE_PUBLICATION.json'
if site_receipt_path.exists():
    site_receipt = read(site_receipt_path)
    update['siteSource']['latestRecordedPublication'] = {
        key: site_receipt.get(key) for key in ['captured_utc', 'project_id', 'source_commit', 'version', 'version_id', 'deployment_id', 'status', 'url']}
    update['siteSource']['latestRecordedPublication']['receipt'] = 'docs/source-only/20261028-coordination/SITE_PUBLICATION.json'
connections = {
    'medium': 'Current source work connects the literal same-paperPsi S1 to its owned atlas, genuine S2 mixed-tail/receiver binding and actual S3/Poisson carriers. Low/high conductor and weighted Gram payments are scoped source proposals; full actual (14)/(15) insertion, P1/P2 and spectral return remain OPEN.',
    'prime-products': 'Current proposals preserve full-q marked inner/wall reconstruction, real present-rank derivative dictionaries and complete-modulus Fourier accounting. P1 double periodization, both axes and P2 are INTERNAL deductions still requiring actual source assembly, not deferred primitive wrappers. Full same-rho HB/Brun/PP remains OPEN.',
    'upper': 'Actual ascending-cell and common-ancestor source proposals remain scoped. Fifth saving uses 64 children per parent; 128 was the two named-parent total. Full adopted-bank ownership/trim, all87 domains, same-rho limits and current K remain OPEN.',
    'chen-weights': 'Original same-Q twenty-one-term sifted-count comparison, signed child corrections and exact low/high selected masks are being connected to true enhanced action families. H248 is not assumed equal to an ordinary rho density; full licensed child costs and paired lower mean remain OPEN.',
    'lower': 'Current proposals include actual mixed W/tent mesh/query losses, same-rho finite wall payment, tied n48 weighted log moments and genuine negative-single support. Complete adopted L5/L6 bank/SourceForm binding, all-modulus uniform approximation and the full lower functional remain OPEN.',
    'certificate': 'Actual row21/22 mixed/Q6 and directed source floors, original320-term independent proxy and same-Q enhanced-action semantics are separate source obligations. Closed finite decision bodies are UNEVALUATED; full T10 integration, H248 analytic induction/seed, positive-K switch licences, mask/fibre reserves and current c remain OPEN.',
    'bad-mass': 'Current work binds independently defined selected callers/present ranks, actual late-policy range and complete-product proper-power/tail payments, preserving product=T and the same coprime mean. A single-modulus wall or abstract lambda6 range is not a complete supplier; D12 and final even-N transfer remain OPEN.'
}
for step in update['internalSteps']:
    if step['id'] in connections:
        step['currentConnection'] = connections[step['id']]
        step['credit'] = 'UNCOMPILED_ZERO_CREDIT'
update['resume30'] = {'snapshot': 'resume30.json', 'captured_utc': now, **summary, 'batch_summaries': summaries,
                      'operation_state': pause.get('operation_state', 'active'),
                      'extra_summary': extra_summary,
                      'extra_checklist': extra_tasks[-1].get('checklist_file') if extra_tasks else None,
                      'extra_checklists': sorted({t['checklist_file'] for t in extra_tasks})}
update['goalLabel'] = '1+1.748'
sync_pause_fields(update, pause)
if quota:
    update['rootQuota'] = {**quota, 'snapshotCapturedUtcMinute': quota['captured_utc'],
                           'evidence': 'Root-only rate-limit snapshot; children never inspect quota.'}
write(SITE / 'dist/current-update.json', update)
print(json.dumps({'summary': summary, 'batches': summaries, 'quota': quota}, ensure_ascii=False))
