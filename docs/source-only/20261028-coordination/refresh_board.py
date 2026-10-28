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
BATCHES = ['20261028-resume-30', '20261028-resume-30b', '20261028-resume-30c', '20261028-resume-30d', '20261028-resume-30e', '20261028-resume-30f']

def read(p):
    return json.loads(p.read_text(encoding='utf-8-sig'))

def write(p, x):
    p.write_text(json.dumps(x, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def verified_head_fields(head, publication, extra_publication):
    for receipt, name, key in [(publication, 'PUBLICATION.json', 'head'),
                               (extra_publication, 'EXTRA_PUBLICATION.json', 'commit')]:
        if receipt.get('remote_exact_sha_verified') and receipt.get(key) == head:
            return {'commit': head, 'remoteExactShaVerified': True,
                    'remote': 'Exact SHA in dated root publication receipt',
                    'receipt': 'docs/source-only/20261028-coordination/' + name,
                    'receiptCapturedUtc': receipt.get('captured_utc')}
    return {'commit': head, 'remoteExactShaVerified': False,
            'remote': 'This current HEAD has no matching remote verification in the dated proof/extra receipts; no remote check was run by this inventory.'}

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
        status = 'running' if states['running'] else 'completed' if owners and states['completed'] == len(owners) else 'pending'
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
    if observed.get(extra_reviewer) == 'running':
        reviewers.append(extra_reviewer)
    for name, owners in [('adopted-integration', ['/root/adopted_plan']),
                         ('independent-review', reviewers), ('compiler-intake', ['/root/intake_inventory']),
                         ('ops', ['/root/board_resume30'])]:
        slots.append(slot(name, owners))
    update['leadSlots'] = slots

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
publication = read(BASE / 'PUBLICATION.json')
extra_publication_path = BASE / 'EXTRA_PUBLICATION.json'
extra_publication = read(extra_publication_path) if extra_publication_path.exists() else {}
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
    reviews = {}
    for p in sorted((folder / 'reviews').glob('*.json')):
        for tid, status, row in review_rows(read(p)):
            reviews[tid] = (status, row, p)
    entries = []
    for task in ledger['tasks']:
        tid = task['id']; dest = folder / tid
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
                'review_status': review[0] if reviewed else 'PENDING',
                'compiled': False, 'formal_credit': 0, 'task_complete': False,
                'local_step_complete': bool(reg.get('local_step_complete', reg.get('complete_module', False))),
                'delivered': delivered, 'author_original_task_complete': bool(reg.get('task_complete', False))}
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
        target['compiled'] = False; target['formal_credit'] = 0; target['task_complete'] = False
        all_sources.extend(sources)
    batch_sources = [s for item in entries for s in item['sources']]
    summary = {'batch': name, 'publication': 'pushed_exact_bytes' if name in published_batches else 'local_in_progress',
               'tasks': len(entries), 'delivered_tasks': sum(t['delivered'] for t in entries),
               'reviewed_tasks': sum(t['review_status'] == 'SOURCE_REVIEW_PASS' for t in entries),
               'source_files': len(batch_sources), 'raw_lines': sum(s['lines'] for s in batch_sources),
               'lexical_declarations': sum(s['declarations'] for s in batch_sources),
               'task_complete': 0, 'formal_credit': 0, 'compiled': False,
               'source_scan_issues': [s['path'] for s in batch_sources if not s['lexer_closed'] or s['forbidden_code_tokens']]}
    summaries.append(summary)
    snapshots[name] = {'captured_utc': now, 'main_theorem': 'OPEN', 'summary': summary, 'tasks': entries}
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
write(BASE / 'SOURCE_BATCHES.json', snapshot)
write(BASE / 'NEXT_ACTIONS.json', {'captured_utc': now, 'count': len(pending),
                                'active_steps': [{'id': t['id'], 'owner': '/root/' + t['id'], 'batch': t['active_batch'],
                                                 'target': t['active_target'], 'status': 'assigned'} for t in tasks],
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
                    'latestCommit': verified_head_fields(head, publication, extra_publication)})
repo_update['sourceArchive']['historical'] = True
repo_update['latestSource'] = {'name': f'{len(published_batches)} reviewed 30-task source bundles', 'path': 'docs/source-only/' + sorted(published_batches)[-1],
                              'sourceState': 'Pushed exact-byte proposals; no production installation, compilation or kernel acceptance'}
repo_update['localSourceBatch']['published'] = False
repo_update['localSourceBatch']['publication_note'] = f'{len(published_batches)} batches pushed; later batches are working snapshots, including unfinished files.'
update['sourceCensus']['snapshotOnly'] = True
update['sourceCensus']['scope'] = 'Historical production-tree census; current source-only batches are counted separately below.'
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
    'upper': 'Actual ascending cells0/1/2, new common-ancestor constructor and two named parents/full128 directed saving have scoped source proposals. The new common-refined policy is not silently identified with the older chain. Full adopted-bank ownership/trim, all87 domains, same-rho limits and current K remain OPEN.',
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
                      'extra_summary': extra_summary, 'extra_checklist': 'docs/source-only/' + BATCHES[-1] + '/EXTRA_TASKS.json'}
update['goalLabel'] = '1+1.748'
if quota:
    update['rootQuota'] = {**quota, 'snapshotCapturedUtcMinute': quota['captured_utc'],
                           'evidence': 'Root-only rate-limit snapshot; children never inspect quota.'}
write(SITE / 'dist/current-update.json', update)
print(json.dumps({'summary': summary, 'batches': summaries, 'quota': quota}, ensure_ascii=False))
