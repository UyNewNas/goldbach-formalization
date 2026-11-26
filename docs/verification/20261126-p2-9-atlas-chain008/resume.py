from pathlib import Path
import base64,hashlib,json,os,subprocess,sys
payload=json.loads(base64.b64decode('__PAYLOAD__'))
parent=Path('/workspace/p29-atlas-20261126')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(parent/'spec-chain007.json')=='98ac789c0af681a9ab90e496ce897c89df8d83d66c1357dd1695c2afcced09f7'
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
spec=json.loads((parent/'spec-chain008.json').read_text())
known={scalar:str(scalar_root)}
modules=['Part5OriginalCausalSmoothAtlas','P2OriginalSmoothReadoutCore','P2FiniteMarkedGamma5AtlasEulerBudget','P2FiniteMarkedGamma5AtlasFamily']
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
    status=subprocess.run([sys.executable,str(parent/'scripts/atlas-target-chain008.py'),short,'008',json.dumps(known)],cwd=parent,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'}).returncode
    if status:sys.exit(status)
    known[name]=str(parent/('run-008-'+short))
print('QUALIFIED_CHAIN',json.dumps(known,sort_keys=True),flush=True)
