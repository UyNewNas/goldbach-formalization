"""Validate an explicit approved dependency overlay; never call it a clean pin."""
from pathlib import Path
import subprocess,json,hashlib
BASE_PIN='09b97db5764ade1246bfb77206baa1b124760958'
DEADLINE='2026-10-30T14:30:00Z'
AUTH='Sentinel_9f35e4053850819193569fe0f7bff980'
SUZUKI='MathlibNt/SieveTheory/LinearSieve/Suzuki/SuzukiFiniteAbel.lean'
IMPORT_ONLY={'MathlibNt/AnalyticNumberTheory/LargeSieve/LiLiuPrereqFouvrySmoothCutoff.lean','MathlibNt/SieveTheory/LiLiuGoldbachOnePlusOneNineFinite.lean'}
NAMES=['finiteNodeAtomSum','finiteNodeVariationSum','finiteNodeStieltjesSum']
sha=lambda b:hashlib.sha256(b).hexdigest()
def allowed_bytes(relative,original,entry):
 if relative==SUZUKI:
  assert entry.get('names')==NAMES, 'wrong recursive-def allowlist'
  expected=original
  for name in NAMES:
   old=('\ndef '+name+' ').encode();assert expected.count(old)==1
   expected=expected.replace(old,('\nnoncomputable def '+name+' ').encode())
  return expected
 assert relative in IMPORT_ONLY, 'file outside this three-file overlay phase; Wiener/Zeta need separate manifest/validator approval'
 imports=entry.get('replacementImports')
 assert isinstance(imports,list) and imports and len(imports)==len(set(imports))
 assert all(isinstance(i,str) and i and all(c.isalnum() or c in '._' for c in i) and i!='Mathlib' for i in imports), 'invalid explicit import replacement'
 assert original.startswith(b'import Mathlib\n'), 'unexpected original leading import'
 return ('\n'.join('import '+i for i in imports)+'\n').encode()+original[len(b'import Mathlib\n'):]
def validate(root,manifest_path,archive=None):
 root=Path(root);manifest_path=Path(manifest_path).resolve();raw=manifest_path.read_bytes();m=json.loads(raw)
 assert m['status']=='AUTHORIZED_OVERLAY_NOT_ORIGINAL_FIXED_SOURCE' and m['package']=='goldbach'
 assert m['authorizationReference']==AUTH and m['absoluteRoundDeadlineUtc']==DEADLINE
 assert m['basePin']==BASE_PIN and m['files']
 assert set(m['files']) <= ({SUZUKI}|IMPORT_ONLY)
 pkg=root/'.lake/packages/goldbach'
 head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=pkg,text=True).strip();assert head==BASE_PIN
 patchpath=(manifest_path.parent/m['patchFile']).resolve();assert patchpath.parent==manifest_path.parent, 'patch must be sibling artifact'
 patch=patchpath.read_bytes();assert sha(patch)==m['patchSha256']
 currentPatch=subprocess.check_output(['git','diff','--no-ext-diff','--binary','HEAD','--'],cwd=pkg)
 assert currentPatch==patch, 'full working-tree patch differs from approved patch bytes'
 # Check staged+unstaged tracked differences against HEAD, with no rename/path ambiguity.
 changed=subprocess.check_output(['git','diff','--name-only','--no-renames','-z','HEAD','--'],cwd=pkg).split(b'\0')
 changed={p.decode() for p in changed if p};assert changed==set(m['files']), 'extra or missing modified files'
 untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard','-z'],cwd=pkg)
 assert not untracked, 'unapproved untracked files in patched package'
 reports={}
 if archive is not None:
  archive=Path(archive);archive.mkdir(exist_ok=False)
  (archive/'manifest.json').write_bytes(raw);(archive/'dependency.patch').write_bytes(patch)
 for relative,entry in m['files'].items():
  assert Path(relative).as_posix()==relative and not Path(relative).is_absolute() and '..' not in Path(relative).parts
  original=subprocess.check_output(['git','show',BASE_PIN+':'+relative],cwd=pkg)
  blob=subprocess.check_output(['git','rev-parse',BASE_PIN+':'+relative],cwd=pkg,text=True).strip()
  current=(pkg/relative).read_bytes()
  assert sha(original)==entry['baseSha256'] and blob==entry['baseGitBlob']
  assert current==allowed_bytes(relative,original,entry), 'overlay changes exceed approved exact operation'
  assert sha(current)==entry['patchedSha256']
  reports[relative]={'baseSha256':sha(original),'patchedSha256':sha(current),'baseGitBlob':blob,'exactApprovedOperation':True}
  if archive is not None:
   for kind,data in [('base',original),('patched',current)]:
    dest=archive/kind/relative;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
 return {'status':'VERIFIED_EXPLICIT_APPROVED_OVERLAY_NOT_ORIGINAL_FIXED_SOURCE','package':'goldbach','basePin':head,'authorizationReference':AUTH,'manifestSha256':sha(raw),'patchSha256':sha(patch),'files':reports,'trackedClean':False,'onlyApprovedOverlayDirty':True,'absoluteRoundDeadlineUtc':DEADLINE}
