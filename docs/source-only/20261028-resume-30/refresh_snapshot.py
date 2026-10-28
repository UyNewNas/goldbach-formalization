"""Refresh source-only delivery facts. Never invokes Lean or changes proof credit."""
from pathlib import Path
import collections
import datetime
import hashlib
import json
import re

BASE = Path(__file__).resolve().parent
REPO = BASE.parents[2]
WORKSPACE = REPO.parent
SITE = WORKSPACE / 'sites/goldbach-proof-progress-20261021'

def read(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))

def write(path, data):
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def lean_code(text):
    """Strip nested comments and string literals for a bounded source inventory."""
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth += 1; i += 2
            elif text.startswith('-/', i): depth -= 1; i += 2
            else:
                if text[i] == '\n': out.append('\n')
                i += 1
        elif string:
            if text[i] == '\\': i += 2
            elif text[i] == '"': string = False; out.append(' '); i += 1
            else:
                if text[i] == '\n': out.append('\n')
                i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        elif text.startswith('/-', i): depth = 1; out.append(' '); i += 2
        elif text[i] == '"': string = True; i += 1
        else: out.append(text[i]); i += 1
    return ''.join(out), depth == 0 and not string

def strings(value):
    if isinstance(value, str): return [value]
    if isinstance(value, list): return [s for x in value for s in strings(x)]
    if isinstance(value, dict): return [s for x in value.values() for s in strings(x)]
    return []

def review_rows(value):
    result = []
    if isinstance(value, dict):
        tid = value.get('task_id') or value.get('task') or value.get('id')
        status = value.get('status') or value.get('verdict') or value.get('review_status')
        if tid and status: result.append((tid, status, value))
        for x in value.values(): result.extend(review_rows(x))
    elif isinstance(value, list):
        for x in value: result.extend(review_rows(x))
    return result

now = datetime.datetime.now(datetime.timezone.utc).isoformat()
ledger = read(BASE / 'TASKS.json')
reviews = {}
review_files = []
for path in sorted((BASE / 'reviews').glob('*.json')):
    data = read(path)
    review_files.append({'path': str(path.relative_to(REPO)).replace('\\', '/'), 'sha256': digest(path)})
    for tid, status, row in review_rows(data): reviews[tid] = (status, row, path)

entries, all_sources, pending, unsafe = [], [], [], []
for task in ledger['tasks']:
    tid = task['id']
    folder = BASE / tid
    rp = folder / 'REGISTRY.json'
    reg = read(rp) if rp.exists() else {}
    sources = []
    for source in sorted(folder.glob('*.lean')):
        raw = source.read_text(encoding='utf-8-sig')
        code, closed = lean_code(raw)
        hits = re.findall(r'\b(?:sorry|admit|axiom|unsafe)\b', code)
        decl = len(re.findall(r'(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|instance)\s', code))
        item = {'path': str(source.relative_to(REPO)).replace('\\', '/'), 'sha256': digest(source),
                'lines': len(raw.splitlines()), 'declarations': decl, 'lexer_closed': closed,
                'forbidden_code_tokens': hits, 'imports': re.findall(r'(?m)^import\s+(\S+)', code)}
        sources.append(item); all_sources.append(item)
        if hits or not closed: unsafe.append(item['path'])
    delivered = bool(sources and rp.exists() and (folder / 'REPORT.md').exists())
    rev = reviews.get(tid)
    remaining = strings(reg.get('remaining', reg.get('remaining_obligations', reg.get('hypotheses_not_eliminated', []))))
    # Preserve the full original task; local source completion is a separate fact.
    original_closed = bool(reg.get('task_complete', False))
    task.update({'status': 'source_delivered_review_pending' if delivered else 'writing',
                 'compiled': False, 'formal_credit': 0, 'task_complete': original_closed,
                 'local_source_complete': reg.get('complete_module'), 'sources': sources,
                 'review_status': rev[0] if rev else 'PENDING', 'remaining': remaining})
    if rev:
        task['status'] = 'source_reviewed_task_open' if not original_closed else 'source_reviewed_task_claimed_closed'
        task['review_path'] = str(rev[2].relative_to(REPO)).replace('\\', '/')
    entries.append(task.copy())
    for i, text in enumerate(remaining):
        pending.append({'id': f'{tid}-next-{i+1}', 'parent': tid, 'lane': task['lane'],
                        'target': text, 'status': 'unassigned', 'compiled': False, 'formal_credit': 0})

summary = {'tasks': len(entries), 'delivered_tasks': sum(t['status'] != 'writing' for t in entries),
           'source_files': len(all_sources), 'raw_lines': sum(s['lines'] for s in all_sources),
           'lexical_declarations': sum(s['declarations'] for s in all_sources),
           'reviewed_tasks': sum(t['review_status'] != 'PENDING' for t in entries),
           'task_complete': sum(t['task_complete'] for t in entries), 'formal_credit': 0,
           'compiled': False, 'pending_obligations': len(pending), 'source_scan_issues': unsafe}
snapshot = {'schema': 'paper-first-resume-30-source-snapshot-v1', 'captured_utc': now,
            'goal': '1+1.748', 'main_theorem': 'OPEN', 'summary': summary, 'tasks': entries,
            'review_files': review_files,
            'measurement_note': 'Raw text lines and lexical declaration syntax only; no compiler declaration census, kernel validation or new formal credit.'}
ledger['updated_utc'] = now
write(BASE / 'TASKS.json', ledger)
write(BASE / 'DELIVERABLES.json', snapshot)
write(BASE / 'NEXT_ACTIONS.json', {'captured_utc': now, 'count': len(pending), 'tasks': pending})
write(SITE / 'dist/resume30.json', snapshot)

# Read only the root session token-count events; children never inspect quota.
quota = None
session_dir = Path(r'C:\Users\timot\.codex\sessions\2026\10\28')
for path in session_dir.glob('*01a18252-991a-7922-8389-fc3c129e127a.jsonl'):
    for line in path.open(encoding='utf-8'):
        try: event = json.loads(line)
        except ValueError: continue
        p = event.get('payload', {})
        if p.get('type') == 'token_count' and p.get('rate_limits'):
            limits = p['rate_limits']
            windows = [limits.get('primary'), limits.get('secondary')]
            used = max((w['used_percent'] for w in windows if w), default=None)
            if used is not None:
                quota = {'captured_utc': event.get('timestamp'), 'usedPercent': used,
                         'remainingPercent': 100-used, 'stopLinePercent': 10,
                         'source': 'root session token_count.rate_limits; minimum remaining across reported windows'}
if quota: write(BASE / 'ROOT_QUOTA.json', quota)

update = read(SITE / 'dist/current-update.json')
update['resume30'] = {'snapshot': 'resume30.json', 'captured_utc': now, **summary}
update['goalLabel'] = '1+1.748'
if quota:
    update['rootQuota'] = {**update.get('rootQuota', {}), **quota,
                          'snapshotCapturedUtcMinute': quota['captured_utc']}
update['repositoryUpdate']['localSourceBatch'] = {
    'path': str(BASE.relative_to(REPO)).replace('\\', '/'), 'captured_utc': now,
    'summary': summary, 'published': False, 'source_review_is_kernel_acceptance': False}
update['repositoryUpdate']['delta'] = (
    f'本轮30个独立代码任务：已交付{summary["delivered_tasks"]}项、'
    f'{summary["source_files"]}份新Lean源码、{summary["raw_lines"]}行原始文本；'
    f'{summary["reviewed_tasks"]}项已有独立源码审阅。全部未编译，新增内核验收0；原分配目标继续按各项剩余义务推进。')
write(SITE / 'dist/current-update.json', update)
print(json.dumps({'summary': summary, 'quota': quota}, ensure_ascii=False))
