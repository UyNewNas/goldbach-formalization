#!/usr/bin/env python3
"""Apply two source-verified Suzuki namespace adaptations, uncompiled."""
import hashlib,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parent
R20=ROOT/'docs/source-only/20261120-p4a5-hdensity-install-r20';native=Path(sys.argv[1]).resolve(strict=True)
rev='09b97db5764ade1246bfb77206baa1b124760958';nativepath='MathlibNt/SieveTheory/LinearSieve/Suzuki/SuzukiProposition118SourceSeriesPairing.lean';blob='eee5859f2f858c3c82fb37e65f2cbe172096c74a'
git=['git','--git-dir='+str(native)];actual=subprocess.check_output(git+['rev-parse',rev+':'+nativepath],text=True).strip();assert actual==blob
source=subprocess.check_output(git+['cat-file','blob',actual]);assert b'namespace MathlibNt.SieveTheory\n' in source
assert b'noncomputable def suzukiProposition118SourceTPlus (s : \xe2\x84\x9d)' in source
assert b'theorem suzukiLayer_one_two_odd_nonneg {s : \xe2\x84\x9d}' in source
manifest_bytes=(R20/'INSTALL_MANIFEST.json').read_bytes();audit_bytes=(R20/'IMPORT_AUDIT.json').read_bytes();assert hashlib.sha256(manifest_bytes).hexdigest()=='a5685528f157ca3c420105f0f68608b07f8b1d8364887f42b4c17be3b0ec5b7f';assert hashlib.sha256(audit_bytes).hexdigest()=='99dfb888497fa8b632f8969657e766a27317ba54325eaa27a356bf9f731c4263'
a=json.loads(audit_bytes);m=json.loads(manifest_bytes);module='ImbalancedChen.P1FourthNearOneKernel';item=a['visited'][module];assert item['origin']=='checkout';original=(ROOT/item['path']).read_bytes();assert hashlib.sha256(original).hexdigest()=='83fc7aa451aa3a40d9112f511b3d869045117a79eb7d4ba3f6c6626d96c1f19d'
changes=[('MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.suzukiProposition118SourceTPlus','MathlibNt.SieveTheory.suzukiProposition118SourceTPlus'),('MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.suzukiLayer_one_two_odd_nonneg','MathlibNt.SieveTheory.suzukiLayer_one_two_odd_nonneg')]
b=original
for old,new in changes:
 assert b.count(old.encode())==1;b=b.replace(old.encode(),new.encode())
check=b
for old,new in changes:
 assert check.count(new.encode())==1;check=check.replace(new.encode(),old.encode())
assert check==original
out=HERE/'P1FourthNearOneKernel.lean';out.write_bytes(b);sha=hashlib.sha256(b).hexdigest();bsha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();target='ImbalancedChen/P1FourthNearOneKernel.lean';assert not any(x['target']==target for x in m['records'])
m['records'].append({'source':str(out.relative_to(ROOT)),'target':target,'sha256':sha,'selection':'minimal_native_namespace_overlay_source_only_uncompiled','selection_evidence':'exact original SHA, actual pinned native declaration source and two fully qualified name substitutions'})
m['baseline']='b108c2232e9261ea27261a3831d66e9a484d7976';m['scope']='r20 import overlays plus two precise native namespace adaptations; uncompiled'
(HERE/'INSTALL_MANIFEST.json').write_text(json.dumps(m,indent=2,ensure_ascii=False)+'\n')
(HERE/'NAMESPACE_EVIDENCE.json').write_text(json.dumps({'status':'SOURCE_ONLY_NOT_ELABORATED','module':module,'original_sha256':hashlib.sha256(original).hexdigest(),'overlay_sha256':sha,'overlay_git_blob_sha1':bsha,'native_commit':rev,'native_source_path':nativepath,'native_source_blob':blob,'native_source_sha256':hashlib.sha256(source).hexdigest(),'changes':[{'old':x,'new':y,'count':1} for x,y in changes],'other_bytes_unchanged':True,'mathematical_statements_changed':False},indent=2)+'\n')
print('original',hashlib.sha256(original).hexdigest(),'overlay',sha,'blob',bsha)
