import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation');out=root/'.lake/proof-continuation/source-reviews'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
oldp=out/'20261016-U8HarmonicMean-owner-semantics.json';assert sha(oldp)=='6c6884aaba1731567523bf9245cb8f0abc7844927c33168172474358b1ef4aa0';o=json.loads(oldp.read_text());p=root/'ImbalancedChen/CurrentChenUpsilon8HarmonicMean.lean';assert sha(p)==o['source_sha256'];q=root/'ImbalancedChen/CurrentChenUpsilon9HarmonicMean.lean';assert sha(q)=='1e50dc27e37d79eccd1b6cd3974963d78ebca651c369e85e2f524b6126d7cc35';s=q.read_text().splitlines()
for a in o['fixed_public_API']:
 if a['path']==str(q):
  lo,hi=(31,43) if 'affine forms' in a['role'] else (98,117)
  a['lines']=[lo,hi];a['literal_source_excerpt']='\n'.join(s[lo-1:hi])
o['metadata_correction']={'prior_report_path':str(oldp),'prior_report_sha256':sha(oldp),'prior_preserved_unchanged':True,'correction':'Correct two owned U9Harmonic source excerpt line ranges to include their true public definition/theorem headers. No source, mathematical claim, declaration extraction, dependency graph, provider/pin or byte binding changed.'};dp=out/'20261016-U8HarmonicMean-owner-proper-dag.json';assert sha(dp)=='3ff72159240517d5cc504da65d497d3e36d62d70acb02aa0dd71bb2f0a0b4195';o['same_proper_DAG_report']={'path':str(dp),'sha256':sha(dp)}
newp=out/'20261016-U8HarmonicMean-owner-semantics-api-corrected.json';assert not newp.exists();newp.write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n',encoding='utf-8');print(str(newp));print(sha(newp))