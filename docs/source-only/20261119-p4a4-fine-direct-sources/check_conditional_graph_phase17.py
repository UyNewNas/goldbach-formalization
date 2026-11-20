"""Reconstruct a name-only import graph; not an installation or Lean check."""
import argparse, collections, json, re
from pathlib import Path
p=argparse.ArgumentParser()
p.add_argument('--manifest',type=Path,required=True)
p.add_argument('--phase9',type=Path,required=True)
p.add_argument('--phase15',type=Path,required=True)
p.add_argument('--candidate-root',type=Path,required=True)
p.add_argument('--local-root',type=Path,action='append',required=True)
a=p.parse_args();nodes={}
for f in json.loads(a.manifest.read_text())['files']:
 nodes[f['module']]=(f.get('imports',[]),'manifest')
for f in json.loads(a.phase9.read_text())['records']:
 nodes[f['module']]=(f['direct_imports'],'phase9')
for root in a.local_root:
 for path in (root/'ImbalancedChen').rglob('*.lean'):
  module='.'.join(path.relative_to(root).with_suffix('').parts)
  nodes[module]=(re.findall(r'^import\s+([^\s]+)',path.read_text(),re.M),str(root))
for f in json.loads(a.phase15.read_text())['source_rows']:
 nodes[f['module']]=(f['direct_imports'],'phase15')
def walk():
 todo=['ImbalancedChen.P4AOriginalFiniteAll22FineCofinalCoefficient']
 seen=set();missing=set();external=set();sources=collections.Counter()
 while todo:
  item=todo.pop()
  if item in seen: continue
  seen.add(item)
  if item not in nodes:
   missing.add(item);continue
  imports,source=nodes[item];sources[source]+=1
  for name in imports:
   if name.startswith('ImbalancedChen.'):todo.append(name)
   else:external.add(name)
 return {'visited':len(seen),'known':len(seen)-len(missing),'missing':sorted(missing),'external':len(external),'sources':dict(sources)}
before=walk()
for path in (a.candidate_root/'ImbalancedChen').rglob('*.lean'):
 module='.'.join(path.relative_to(a.candidate_root).with_suffix('').parts)
 nodes[module]=(re.findall(r'^import\s+([^\s]+)',path.read_text(),re.M),'candidate_only')
after=walk()
assert before['known']==1792 and len(before['missing'])==4
assert after['known']==1805 and after['missing']==[] and after['external']==232
assert after['sources']['manifest']==1575 and after['sources']['candidate_only']==13
print(json.dumps({'before':before,'after':after,'scope':'CONDITIONAL_NAME_GRAPH_NOT_COMPILED'},sort_keys=True))
