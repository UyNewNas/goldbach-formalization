from pathlib import Path
import base64, datetime, hashlib, json, os, subprocess, sys, time

root = Path('/workspace/p25-q96-20261125')
shared = Path('/workspace/goldbach-p3')
publication, previous = sys.argv[1:3]
lean = Path('/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean')
runner_path = 'docs/verification/20261125-p2-5-saving16/string-char-binding/run_diagnostic.py'
probe_path = 'docs/source-only/20261125-p2-5-parser-reuse/packed-repair/PackedCharsOwnedFlags.lean'
module = 'ImbalancedChen.P2OriginalSaving19PackedChars'
source_path = 'ImbalancedChen/P2OriginalSaving19PackedChars.lean'
source_sha = 'cf65b9e0f3b0a4735cdb962d9b317ed29e8f39c8507647bab04f7e48800ad001'
object_sha = 'b8a8059126905b41a26a67b69ef2d03242fa35c6da9681d505d176600424e006'
probe_sha = '163b3b10305aa3f0c9855b33031b28d782b7622fd4726037844be533b4ab4cef'
flags = ['-t0', '-j1', '-M11264', '-DwarningAsError=true', '-DmaxRecDepth=50000', '-DmaxHeartbeats=40000000']

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def published(path):
    return subprocess.check_output(['git', 'show', publication + ':' + path], cwd=root)

def saved(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')

assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip() == previous
assert not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=root, text=True).strip()
subprocess.check_call(['git', 'fetch', '--negotiation-tip=' + previous, 'origin', publication], cwd=shared)
assert subprocess.check_output(['git', 'rev-parse', 'FETCH_HEAD'], cwd=shared, text=True).strip() == publication
subprocess.check_call(['git', 'merge-base', '--is-ancestor', previous, publication], cwd=root)
assert sha(lean) == 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
diag = root / '.lake/diagnostic/p25-packed-flags-attempt001'
assert not diag.exists()
diag.mkdir(parents=True)
probe = diag / 'PackedCharsOwnedFlags.lean'
probe.write_bytes(published(probe_path))
assert sha(probe) == probe_sha
assert sha(root/source_path) == hashlib.sha256(published(source_path)).hexdigest() == source_sha
obj = root / '.lake/p2-private/lib/ImbalancedChen/P2OriginalSaving19PackedChars.olean'
assert sha(obj) == object_sha
record = json.loads((root/'.lake/p2-private/records.json').read_text())[module]
assert record['source_sha256'] == source_sha and record['object_sha256'] == object_sha and record['exit_code'] == 0
assert record['closure_signature'] == 'e75d0a887f71d1801e7ea3f754bdb376329256656946592aa06b8a4131cb3829'
audit_path = 'docs/source-only/20261125-p2-5-parser-reuse/p3-attempt-001/p2-private/audit/ImbalancedChen.P2OriginalSaving19PackedChars/attempt-001/audit.log'
audit_raw = published(audit_path)
assert hashlib.sha256(audit_raw).hexdigest() == '17c914836322cf17b44f7aa73f857d52acc65006d544c852813682d911884717'
inventory = [json.loads(l[len('P0_QUEUE_INVENTORY '):]) for l in audit_raw.decode().splitlines() if l.startswith('P0_QUEUE_INVENTORY ')]
assert len(inventory) == 1 and sorted(inventory[0]['serialized']) == sorted(inventory[0]['environment'])
assert len(inventory[0]['serialized']) == 120
env = dict(os.environ)
env.pop('LEAN_SRC_PATH', None)
env['LEAN_SYSROOT'] = str(lean.parent.parent)
env['LEAN_PATH'] = str(root/'.lake/p2-private/lib')
command = [str(lean), *flags, str(probe)]
started = time.monotonic()
timed_out = False
with (diag/'FLAGS.log').open('w') as log:
    try:
        process = subprocess.run(command, cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT, timeout=120)
        code = process.returncode
    except subprocess.TimeoutExpired:
        timed_out = True
        code = -1
lines = (diag/'FLAGS.log').read_text().splitlines()
rows = [json.loads(l[len('PACKEDCHARS_FLAG '):]) for l in lines if l.startswith('PACKEDCHARS_FLAG ')]
counts = [int(l[len('PACKEDCHARS_COMPLETE_OWNED_COUNT '):]) for l in lines if l.startswith('PACKEDCHARS_COMPLETE_OWNED_COUNT ')]
complete = (code == 0 and not timed_out and counts == [120] and len(rows) == 120 and len({r['name'] for r in rows}) == 120
            and sorted(r['name'] for r in rows) == sorted(inventory[0]['serialized'])
            and sha(probe) == probe_sha and sha(obj) == object_sha and sha(root/source_path) == source_sha)
flag_result = {'schema': 'p25-packed-owned-actual-flags-v1', 'publication_commit': publication,
               'source_sha256': source_sha, 'object_sha256': object_sha, 'probe_sha256': probe_sha,
               'command': command, 'exit_code': code, 'timed_out': timed_out, 'seconds': round(time.monotonic()-started,3),
               'inventory_count': len(rows), 'complete_inventory_matched': complete, 'declarations': rows,
               'flagged': [r for r in rows if any(r[k] for k in ['unsafe','partial','axiom'])],
               'full_owned_acceptance': False, 'scope': 'Metadata diagnosis only; the original complete audit remains rejected.',
               'log_sha256': sha(diag/'FLAGS.log')}
saved(diag/'RESULT.json', flag_result)
print('P25_PACKED_FLAGS_RESULT ' + json.dumps({k:flag_result[k] for k in ['exit_code','seconds','inventory_count','complete_inventory_matched','flagged','full_owned_acceptance']}), flush=True)

# Read the pinned installation's existing String API source for possible reuse.
api = []
source_dir = lean.parent.parent/'src/lean/Init/Data/String'
if source_dir.is_dir():
    for p in sorted(source_dir.rglob('*.lean')):
        text = p.read_text().splitlines()
        hits = []
        for i, line in enumerate(text):
            if any(name in line for name in ['ofList_append','toList_append','ofList_toList','toList_inj','ofList_inj']):
                hits.append({'line':i+1, 'context':'\n'.join(text[max(0,i-2):min(len(text),i+6)])})
        if hits:
            api.append({'path':str(p),'sha256':sha(p),'hits':hits[:30]})
saved(diag/'LEAN_STRING_API_OBSERVATIONS.json', {'source_root':str(source_dir),'present':source_dir.is_dir(),'files':api,'proof_credit':False})

runner = root/'.lake/p25-string-char-binding-published.py'
assert not runner.exists()
runner.write_bytes(published(runner_path))
print('P25_STRING_CHAR_PUBLISHED_RUNNER ' + publication + ' ' + sha(runner), flush=True)
run_code = subprocess.call([sys.executable, str(runner), publication, previous], cwd=root)
binding_dir = root/'.lake/diagnostic/p25-string-char-binding-attempt001'
manifest, included, omitted = [], [], []
used = 0
paths = sorted(p for parent in [binding_dir, diag] if parent.is_dir() for p in parent.rglob('*') if p.is_file())
paths.sort(key=lambda p:(0 if p.name=='RESULT.json' else 1 if p.suffix in ['.log','.json','.txt'] else 2, str(p)))
for p in paths:
    raw = p.read_bytes()
    row = {'path':str(p.relative_to(root)),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}
    manifest.append(row)
    if '/lib/' not in str(p) and p.suffix in ['.json','.log','.txt','.lean','.py'] and used+len(raw)<=1200000:
        included.append(dict(row,data_base64=base64.b64encode(raw).decode()))
        used += len(raw)
    else:
        omitted.append(row)
print('P25_STRING_CHAR_EXPORT_JSON ' + json.dumps({'schema':'p25-string-char-and-flags-actual-export-v1',
      'publication_commit':publication,'runner_exit':run_code,'flags_complete':complete,
      'manifest':manifest,'included_files':included,'unexported_files':omitted},separators=(',',':')), flush=True)
raise SystemExit(0 if run_code==0 and complete else 1)
