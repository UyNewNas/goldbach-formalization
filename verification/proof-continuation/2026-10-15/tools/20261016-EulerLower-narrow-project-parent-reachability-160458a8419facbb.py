import sys
sys.dont_write_bytecode=True
from pathlib import Path
import re,json,collections,hashlib
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation')
starts=['ActualPrimeBoxMass','FullPowerEulerNormalization','SieveDimensionComparison']
targets={'RoughPowerParameters','RoughAbsoluteDensity'}
results=[]
for start in starts:
    todo=collections.deque([(start,[start])]);seen=set();found={}
    while todo:
        name,path=todo.popleft()
        if name in seen:continue
        seen.add(name)
        if name in targets:
            found[name]=path
            if targets<=found.keys():break
        p=root/'ImbalancedChen'/f'{name}.lean'
        if not p.is_file():continue
        # Only literal leading project import lines; no foreign traversal or source-body audit.
        for line in p.read_text().splitlines():
            m=re.fullmatch(r'import ImbalancedChen\.([A-Za-z0-9_]+)',line.strip())
            if m:todo.append((m.group(1),path+[m.group(1)]))
            elif line.strip() and not line.startswith('import '):break
    results.append({'start':start,'project_header_nodes_seen':len(seen),'positive_paths':found,'not_reached_by_project_import_edges':sorted(targets-found.keys())})
print(json.dumps(results,indent=2))