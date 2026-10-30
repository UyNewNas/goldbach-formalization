from pathlib import Path
import os,json,hashlib,shlex
import runtime_guard as g
b=Path(__file__).resolve().parent
root=b.parent/'goldbach-formalization'
real=Path('/workspace/shared/lean-tools/lean-4.33.0-rc1-linux/bin')
# Local vendor distribution binding, not a GitHub Actions installation claim.
os.environ['LEAN_NUM_THREADS']='2'
state=g.prepare(root,b,b/'runtime',real,Path('/nonexistent-not-used'),verify_action=False)
state['installationScope']='local pinned official vendor distribution, no CI action-install equivalence asserted'
state['officialLeanCheckerSourceSha256']=g.sha(real.parent/'src/lean/LeanChecker.lean')
g.write_json(b/'runtime/state.json',state)
with (b/'env.sh').open('w') as f:
 for k,v in state['environment'].items(): f.write('export '+k+'='+shlex.quote(v)+'\n')
 f.write('export PATH='+shlex.quote(state['shadow']+'/bin')+':"$PATH"\n')
official=(real.parent/'src/lean/LeanChecker.lean').read_text()
candidate=(b/'ExactReplay.lean').read_text()
a=official.index('unsafe def replayFromImports ')
z=official.index('\n\n',official.index("  env'.freeRegions",a))
function=official[a:z].strip()
x=candidate.index('unsafe def replayFromImports ')
y=candidate.index('\n\nend ExactReplay',x)
assert function==candidate[x:y].strip(), 'replay implementation drift'
report={'status':'FRESH_SOURCE_COMPARISON_PASS','official_source':str(real.parent/'src/lean/LeanChecker.lean'),'official_source_sha256':g.sha(real.parent/'src/lean/LeanChecker.lean'),'candidate_source_sha256':g.sha(b/'ExactReplay.lean'),'copied_function_identical':True,'function_sha256':hashlib.sha256((function+'\n').encode()).hexdigest(),'function_bytes':len((function+'\n').encode()),'scope':'exact own declarations against imported environment; not replayFromFresh'}
g.write_json(b/'ExactReplay-source-comparison.json',report)
print('Source comparison and local guard initialized')
