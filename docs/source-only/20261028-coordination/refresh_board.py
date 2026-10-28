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
BATCHES = ['20261028-resume-30', '20261028-resume-30b', '20261028-resume-30c', '20261028-resume-30d']

def read(p):
    return json.loads(p.read_text(encoding='utf-8-sig'))

def write(p, x):
    p.write_text(json.dumps(x, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

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
    return {'path': p.relative_to(REPO).as_posix(), 'sha256': sha(p),
            'lines': len(raw.splitlines()),
            'declarations': len(re.findall(r'(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|instance)\s', code)),
            'lexer_closed': closed,
            'forbidden_code_tokens': re.findall(r'\b(?:sorry|admit|axiom|unsafe)\b', code),
            'imports': re.findall(r'(?m)^import\s+(\S+)', code)}

now = datetime.datetime.now(datetime.timezone.utc).isoformat()
publication = read(BASE / 'PUBLICATION.json')
published_batches = {item['batch'] for item in publication['batches']}
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
snapshot = {'schema': 'paper-first-multi-batch-source-snapshot-v1', 'captured_utc': now, 'goal': '1+1.748',
            'main_theorem': 'OPEN', 'summary': summary, 'batch_summaries': summaries, 'active_batch': BATCHES[-1],
            'tasks': tasks, 'measurement_note': 'Raw text lines and lexical declaration syntax. No compilation, numerical replay, kernel acceptance or new formal credit.'}
write(BASE / 'SOURCE_BATCHES.json', snapshot)
write(BASE / 'NEXT_ACTIONS.json', {'captured_utc': now, 'count': len(pending),
                                'active_steps': [{'id': t['id'], 'owner': '/root/' + t['id'], 'batch': t['active_batch'],
                                                 'target': t['active_target'], 'status': 'assigned'} for t in tasks],
                                'tasks': pending})
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
head = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=REPO, capture_output=True, text=True, check=True).stdout.strip()
repo_update = update['repositoryUpdate']
repo_update.update({'formalizationCommit': head, 'commitUrl': 'https://github.com/UyNewNas/goldbach-formalization/commit/' + head,
                    'sourceState': 'manuscript-internal source proposals; uncompiled, zero formal credit',
                    'delta': f"{len(BATCHES)} source batches; {summary['source_files']} Lean proposals, {summary['raw_lines']} raw lines, {sum(s['reviewed_tasks'] for s in summaries)} independently reviewed local deliveries. All 30 original targets OPEN; new kernel credit 0.",
                    'localSourceBatch': {'path': BASE.relative_to(REPO).as_posix(), 'captured_utc': now, 'summary': summary,
                                         'batch_summaries': summaries, 'source_review_is_kernel_acceptance': False},
                    'latestCommit': {'commit': head, 'remote': 'exact branch SHA verified after push; see root publication receipt'}})
repo_update['sourceArchive']['historical'] = True
repo_update['latestSource'] = {'name': f'{len(published_batches)} reviewed 30-task source bundles', 'path': 'docs/source-only/' + sorted(published_batches)[-1],
                              'sourceState': 'Pushed exact-byte proposals; no production installation, compilation or kernel acceptance'}
repo_update['localSourceBatch']['published'] = False
repo_update['localSourceBatch']['publication_note'] = f'{len(published_batches)} batches pushed; later batches are working snapshots, including unfinished files.'
update['sourceCensus']['snapshotOnly'] = True
update['sourceCensus']['scope'] = 'Historical production-tree census; current source-only batches are counted separately below.'
update['siteSource'].update({'nativeLatestVersionAtOpening': 67, 'sourceBaseCommit': 'ad4776053a52b6ad94a8aa02fb8a1d752954a178',
                            'openedState': 'Source helper opened the existing owner-private checkout; audience unchanged.'})
connections = {
    'medium': 'Same-paperPsi S1/S2 and original common-q/d Cauchy ordering are being connected in batch 3. Actual low-conductor and fixed-k high-conductor pieces are source proposals; weighted (14), Gram (15), full spectral return remain OPEN.',
    'prime-products': 'All16 reverse projection and sorted physical block atoms, actual Euclidean Fourier, two-long mode reconstruction and cutoff budgets are local source proposals. Full actual W_N/HB/Brun identity, uniform same-rho PP and tails remain OPEN.',
    'upper': 'Actual physical q-fibre, even-retained policy relation, frozen chronology and two named parents/all64 children are being connected. Full owner clipping/reserves, all87 domains, same-rho density and current K remain OPEN.',
    'chen-weights': 'Rounded U6, native unmasked-low U10 and high-complement U11 now have a same-rho finite ledger proposal. Signed distribution estimates and full paired lower mean remain OPEN.',
    'lower': 'Mixed W/tent local chambers, trace, true integer square gates, n48 key decoder and L5/L6 knot masses have reviewed local proposals. Common approximation, actual rough supplier, per-row mass and full lower functional remain OPEN.',
    'certificate': 'Ordinary saved-minus-defect <= independent proxy <= selected-union integral is source-reviewed; enhanced chord domains, finite action-bank payment and row21/22 Jacobians are local proposals. H_B endpoint licences, exact floors, full aggregate loss and current c remain OPEN.',
    'bad-mass': 'Actual Family proper-power and reciprocal-tail source proposals preserve signed same-rho count/mean and product=T collision. Native all-k Family, polynomial modulus payment, D12 and final even threshold remain OPEN.'
}
for step in update['internalSteps']:
    if step['id'] in connections:
        step['currentConnection'] = connections[step['id']]
        step['credit'] = 'UNCOMPILED_ZERO_CREDIT'
update['resume30'] = {'snapshot': 'resume30.json', 'captured_utc': now, **summary, 'batch_summaries': summaries}
update['goalLabel'] = '1+1.748'
if quota:
    update['rootQuota'] = {**quota, 'snapshotCapturedUtcMinute': quota['captured_utc'],
                           'evidence': 'Root-only rate-limit snapshot; children never inspect quota.'}
write(SITE / 'dist/current-update.json', update)
print(json.dumps({'summary': summary, 'batches': summaries, 'quota': quota}, ensure_ascii=False))
