from pathlib import Path
import base64,hashlib,json,os,subprocess,sys
payload=json.loads(base64.b64decode('__PAYLOAD__'))
parent=Path('/workspace/p29-atlas-20261126')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(parent/'spec-chain009.json')=='ff34b8c601012e0df6af30bb0eac5dcf3403700231034d701cb37bb2b167a338'
assert sha(parent/'logbox-frozen-20261126/.lake/p2-private/records.json')=='6cfe940c2fecc1a015458ae7b7814274e78289f47d5fe4b9f9f5f25478b58028'
scalar='ImbalancedChen.P5RoughLogGridSmoothPartition'
scalar_root=parent/'run-003-P5RoughLogGridSmoothPartition'
scalar_receipt=scalar_root/'.lake/p2-private/audit'/scalar/'latest.json'
assert sha(scalar_receipt)=='22d9648220e1dd959c55b3893bddbff920492af91f63c25f70a3d4dad091b3a1'
receipt=json.loads(scalar_receipt.read_text())
assert receipt['accepted'] is True and receipt['replay']['inputs_unchanged'] and receipt['audit']['inputs_unchanged']
assert receipt['object_sha256']=='5ea2c93bfcef3446a1dc2a30db15339ab11671cabe059b5965112504420e14a1'
for path,text in payload.items():
    dest=parent/path
    assert not dest.exists(),'refuse overwrite '+str(dest)
    dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_text(text)
spec=json.loads((parent/'spec-chain010.json').read_text())
known={scalar:str(scalar_root)}
# Exact already-qualified source/object/receipt identities; never replay successful gates.
for short,version,source_hash,object_hash,receipt_hash in [
 ('Part5OriginalCausalSmoothAtlas','008','e46455cfdd0952c12567c42c01153c65305169b2916cae86a0c3046db91b754a','45b9d0d3da4e3675d59419f7f13fd3e48776045cec799ceafe0d9ebbaa30647b','84d6a7805768adc610bd37b8d46cdeb3c12d3fccb8947ed4601c48db39fd7c2c'),
 ('P2OriginalSmoothReadoutCore','008','acd7841385d5313fea4382b460048455e532c95d5724aaef44f09bcd84169753','fc1207087366f8f28d33736a97e3ad7048998c9bbd110e0ea3b6d3da1ce78feb','779461e9e03102c9c8697d7a760c087756eccef74fcccbef2b46f0847a66acf9'),
 ('P2FiniteMarkedGamma5AtlasEulerBudget','009','2a1117c5da6946a3779abc0c71ba0170057f9be788ce32d720fb8858c90ebb25','43384102ef05efa8e450c855985a030f89cd41f3e11968277488ed605db2dd94','98294bc61f48c813f765f2b45e0c919464ac8a8c57e4dd46221bf3c8da987260')]:
    name='ImbalancedChen.'+short;origin=parent/('run-'+version+'-'+short)
    rp=origin/'.lake/p2-private/audit'/name/'latest.json'
    assert sha(rp)==receipt_hash,'accepted receipt changed '+name
    ar=json.loads(rp.read_text());rr=json.loads((origin/'.lake/p2-private/records.json').read_text())[name]
    assert ar['accepted'] and ar['replay']['exit_code']==0 and ar['audit']['exit_code']==0
    assert ar['replay']['inputs_unchanged'] and ar['audit']['inputs_unchanged']
    assert sha(origin/'ImbalancedChen'/(short+'.lean'))==ar['source_sha256']==rr['source_sha256']==spec[name]['source_sha256']==source_hash
    assert sha(origin/'.lake/p2-private/lib/ImbalancedChen'/(short+'.olean'))==ar['object_sha256']==rr['object_sha256']==object_hash
    known[name]=str(origin)
    print('REUSE_PINNED_QUALIFIED',name,str(origin),flush=True)
modules=['P2FiniteMarkedGamma5AtlasFamily']
for short in modules:
    name='ImbalancedChen.'+short
    for candidate in [Path('/workspace/p2-saving16-20261125'),Path('/workspace/p2-9-20261125'),*sorted(parent.glob('run-*'))]:
        reg=candidate/'.lake/p2-private/records.json'
        if not reg.is_file():continue
        rec=json.loads(reg.read_text()).get(name,{})
        if rec.get('source_sha256')!=spec[name]['source_sha256']:continue
        obj=candidate/'.lake/p2-private/lib'/Path(*name.split('.')).with_suffix('.olean')
        if not obj.is_file():continue
        ap=candidate/'.lake/p2-private/audit'/name/'latest.json'
        assert ap.is_file(),'source-matching old object needs original audit; do not duplicate compile'
        ar=json.loads(ap.read_text())
        assert ar.get('accepted') is True and ar['object_sha256']==rec['object_sha256']==sha(obj)
        assert ar['replay']['inputs_unchanged'] and ar['audit']['inputs_unchanged']
        known[name]=str(candidate);print('REUSE_EXISTING_QUALIFIED',name,str(candidate),flush=True);break
for short in modules:
    name='ImbalancedChen.'+short
    if name in known:continue
    print('START_NEW_TARGET',name,flush=True)
    status=subprocess.run([sys.executable,str(parent/'scripts/atlas-target-chain010.py'),short,'010',json.dumps(known)],cwd=parent,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'}).returncode
    if status:sys.exit(status)
    known[name]=str(parent/('run-010-'+short))
print('QUALIFIED_CHAIN',json.dumps(known,sort_keys=True),flush=True)
