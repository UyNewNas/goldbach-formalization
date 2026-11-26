set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python -B - <<'PY'
import base64,hashlib,io,json,lzma,pathlib,subprocess,tarfile
root=pathlib.Path('/workspace/p2-4-compact-proof-20261125')
pin='b55fa93d39e6a4ddf2abd37b9b8481078e329f70'
registry=root/'.lake/p2-private/records.json'
if not registry.is_file():
    raise RuntimeError('Expected frozen registry path does not exist')
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''): h.update(b)
    return h.hexdigest()
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==pin
before=sha(registry)
assert before=='3e71aab7f7b54dea5bddf99a09cc87310105979237a639e07f8988403dc74445'
dirs={
 'logpoint':pathlib.Path('/workspace/P24ContainsEquationRepair20261126/Attempt001'),
 'raw-b':root/'.lake/p24-B-raw-defeq/b55-attempt-001',
 'serialized322':pathlib.Path('/workspace/p24-current322-serialized-names-b55-20261126/attempt-001')
}
members=[]; excluded=[]; payload=[]
for label,d in dirs.items():
    assert d.is_dir() and not d.is_symlink()
    for p in sorted(d.rglob('*')):
        assert not p.is_symlink(), str(p)
        if not p.is_file(): continue
        name=label+'/'+p.relative_to(d).as_posix()
        if any(s in p.suffixes for s in ('.olean','.ilean','.o','.c')):
            excluded.append({'name':name,'reason':'compiled object; bound by original diagnostic receipt, not transported'})
            continue
        b=p.read_bytes()
        assert len(b)<16777216,(str(p),len(b))
        members.append({'name':name,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
        payload.append((name,b))
index={'source_pin':pin,'registry_sha256':before,'members':members,'excluded':excluded,'transport_only':True,'new_proof_credit':False}
payload.append(('FILES.json',(json.dumps(index,ensure_ascii=False,sort_keys=True,indent=2)+'\n').encode()))
buf=io.BytesIO()
with tarfile.open(fileobj=buf,mode='w',format=tarfile.PAX_FORMAT) as tf:
    for name,b in payload:
        t=tarfile.TarInfo(name);t.size=len(b);t.mode=0o644;t.mtime=0;t.uid=t.gid=0
        tf.addfile(t,io.BytesIO(b))
raw=buf.getvalue();data=lzma.compress(raw,preset=6)
assert len(data)<=1400000,('transport exceeds bounded stdout',len(data))
assert sha(registry)==before
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==pin
descriptor={'archive_bytes':len(data),'archive_sha256':hashlib.sha256(data).hexdigest(),'tar_bytes':len(raw),'tar_sha256':hashlib.sha256(raw).hexdigest(),'members':len(payload),'file_payload_bytes':sum(len(b) for _,b in payload),'excluded_count':len(excluded),'source_pin':pin,'registry_unchanged':True,'production_files_written':0,'proof_credit':False}
print('P24_DIAGNOSTIC_TRANSPORT '+json.dumps(descriptor,sort_keys=True),flush=True)
print('P24_ARCHIVE_BASE64 '+base64.b64encode(data).decode(),flush=True)
PY
