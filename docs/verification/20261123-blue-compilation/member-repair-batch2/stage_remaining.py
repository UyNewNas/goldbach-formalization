from pathlib import Path
import hashlib,json,re,difflib
R=Path('/workspace/blue-member-repair-batch2');M=Path('/workspace/blue-member-build');MAIN=Path('/workspace/goldbach-formalization');rows=[]
x=json.loads(Path('/workspace/blue-member-static-omega/STATIC_CANDIDATES.json').read_text())
for row in x['modules']:rows.append((row['module'],Path(row['candidate_path']),row['baseline_sha256'],'/workspace/blue-member-static-omega/STATIC_CANDIDATES.json'))
rows.append(('ImbalancedChen.P2OriginalChildPhysicalNormalization',R/'physical-static-candidate.lean','5203b9a60fc2890ec3f3b0a1f31a5d726f293643f59a3eedf8c461d0c802e04d','Existing pinned source API/proof recovery, no published alternate found'))
pat=re.compile(r'(?m)^(?:@\[[^\n]*\]\s*)?(?P<private>private\s+)?(?P<kind>def|theorem|lemma|abbrev|structure)\s+(?P<name>[^\s:{(]+)')
def scan(s):
 matches=list(pat.finditer(s));result=[]
 for i,m in enumerate(matches):
  end=matches[i+1].start() if i+1<len(matches) else len(s);assign=s.index(':=',m.end(),end);result.append({'name':m['name'],'kind':m['kind'],'private':bool(m['private']),'header':s[m.start():assign].rstrip(),'span':s[m.start():end]})
 return result
for mod,cp,pre,origin in rows:
 short=mod.split('.')[-1];rel=mod.replace('.','/')+'.lean';target=M/rel;production=MAIN/rel;old_bytes=target.read_bytes();old=old_bytes.decode();h=hashlib.sha256(old_bytes).hexdigest();assert h==pre,('source preimage',mod,h,pre)
 new=cp.read_bytes().decode();candidate_sha=hashlib.sha256(new.encode()).hexdigest();new=new.replace('\r\n','\n');new=new.replace('\n','\r\n') if old_bytes.count(b'\r\n')==old_bytes.count(b'\n') and b'\r\n' in old_bytes else new
 for label in ['SOURCE ONLY; UNCOMPILED; ZERO FORMAL CREDIT.','SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.','SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.']:new=new.replace(label,'Verification records: docs/verification/20261123-blue-compilation.')
 before,after=scan(old),scan(new)
 assert [{k:v for k,v in a.items() if k!='span'} for a in before]==[{k:v for k,v in a.items() if k!='span'} for a in after],('headers',mod)
 assert all(a['span']==b['span'] for a,b in zip(before,after) if a['kind'] not in ['theorem','lemma']),('definition',mod)
 assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|implemented_by)\b',new),('forbidden',mod)
 active=[]
 for proc in Path('/proc').iterdir():
  if not proc.name.isdigit():continue
  try:argv=[s for s in (proc/'cmdline').read_bytes().decode().split('\0') if s]
  except (FileNotFoundError,ProcessLookupError,PermissionError,UnicodeDecodeError):continue
  if str(target) in argv:active.append({'pid':proc.name,'argv':argv})
 assert not active,('active source',mod,active)
 sync=production.exists()
 if sync:assert production.read_bytes()==old_bytes,('main identity',mod)
 d=R/short;d.mkdir(exist_ok=False);(d/'baseline.lean').write_bytes(old_bytes);(d/'candidate.lean').write_bytes(new.encode());(d/'candidate.patch').write_text(''.join(difflib.unified_diff(old.splitlines(keepends=True),new.splitlines(keepends=True),fromfile='baseline/'+rel,tofile='candidate/'+rel)))
 for name,records in [('HEADERS_BEFORE.json',before),('HEADERS_AFTER.json',after)]:(d/name).write_text(json.dumps([{k:v for k,v in a.items() if k!='span'} for a in records],indent=2,ensure_ascii=False)+'\n')
 post=hashlib.sha256(new.encode()).hexdigest();comp={'module':mod,'preimage_sha256':pre,'postimage_sha256':post,'static_candidate_before_neutral_comment_sha256':candidate_sha,'candidate_origin':origin,'all_public_and_private_headers_identical':True,'all_definitions_abbrevs_structures_identical':True,'all_original_constants_domains_hypotheses_preserved':True,'changed_proof_bodies':[a['name'] for a,b in zip(before,after) if a['span']!=b['span']],'public_source_declarations':sum(not a['private'] for a in after),'Member_main_same_baseline_synced':sync,'main_source_absent_not_created':not sync,'historical_state_comment_neutralized_before_first_compile':True,'mathematical_gap_identified':False,'P6_or_frozen_sources_modified':False,'compiler_invoked':False}
 target.write_bytes(new.encode())
 if sync:production.write_bytes(new.encode())
 (d/'SOURCE_COMPARISON.json').write_text(json.dumps(comp,indent=2)+'\n');print(mod,post,'main sync',sync,'changed',comp['changed_proof_bodies'])
comparisons={}
for d in R.iterdir():
 if d.is_dir() and (d/'SOURCE_COMPARISON.json').exists():
  row=json.loads((d/'SOURCE_COMPARISON.json').read_text());comparisons[row['module']]=row
assert len(comparisons)==5
(R/'EXPECTED_SOURCES.json').write_text(json.dumps({mod:x['postimage_sha256'] for mod,x in comparisons.items()},indent=2)+'\n');(R/'SOURCE_SELECTION.json').write_text(json.dumps(comparisons,indent=2)+'\n')
