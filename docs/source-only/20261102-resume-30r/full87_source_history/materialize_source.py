"""Source-text materialization only. No source producer or mathematical guard runs.

Reads pinned literal Lean segments and original JSON row strings; copies the
former unchanged and emits the fourteen missing ascending row tables and exact
row-name selectors. Never evaluates a row at a point, LP, integral, or proof.
"""
from pathlib import Path
import hashlib
import json
import re
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
ARCHIVE = ROOT / '.lake/proof-continuation/source-reviews/drafts/20261028-EvidenceLocator/chen-numerical-evidence-20261010.zip'
BASE = 'chen-numerical-evidence-20261010-renewal-v2/goldbach-research/'

def digest(data):
    return hashlib.sha256(data).hexdigest()

reused = [
 ('P4AOriginalSeed7Unequal15Literal', '4020d46ce412fe75bfaca2104268c4c11b773a1dcb567e55e31174f8b0a3d6c3', '20261028-Upper-Sol6-Phase13-Seed7Unequal15Literal.txt'),
 ('P4AOriginalFirstFailureH5H7Literal', '74cd02eda48dee3b82de2c135d09bda9663f2f73371df368f848818de577660c', '20261028-Upper-Sol6-Phase11-FirstFailureH5H7Literal.txt')]
receipts = []
for module, sha, filename in reused:
    path = ROOT / 'docs/source-only/20261028-paper-first/cohort04/upper/sources' / sha / filename
    raw = path.read_bytes()
    text = raw.decode('utf-8-sig')
    start = text.index('import ')
    marker = 'end ImbalancedChen.' + module
    end = text.index(marker, start) + len(marker)
    segment = text[start:end]
    output = ('/- Source-only mechanical reuse. Original declarations unchanged.\n'
              'Only non-Lean envelope removed. See SOURCE_RECEIPT.json. -/\n\n' + segment + '\n')
    (HERE / (module + '.lean')).write_text(output, encoding='utf-8', newline='\n')
    receipts.append(dict(path=str(path.relative_to(ROOT)).replace('\\','/'), sha256=digest(raw),
        segment_sha256=digest(segment.encode()), module='ImbalancedChen.'+module,
        output=module+'.lean', mode='exact segment extraction; no mathematical novelty'))

with zipfile.ZipFile(ARCHIVE) as z:
    def read(name):
        raw = z.read(BASE+name)
        receipts.append(dict(archive=str(ARCHIVE.relative_to(ROOT)).replace('\\','/'),
            entry=BASE+name, sha256=digest(raw), bytes=len(raw), mode='read JSON row strings only'))
        return json.loads(raw)
    asc = read('eighth-prefix-family-20261009-navigation.json')['strict_cells']
    nine = read('eighth-unequal-parent-nine-20261009-family-navigation.json')['strict_cells']
    fiftyA = read('eighth-unequal-parent-fifty-20261009-navigation.json')
    fiftyD = read('eighth-unequal-parent-fifty-desc-20261009-navigation.json')
    failures = read('eighth-history-first-failure-20261009-navigation.json')['groups']
    h5 = next(g['strict_cells'] for g in failures if g['separation']=='H5')
    h7 = next(g['strict_cells'] for g in failures if g['separation']=='H7')

kept = [c for c in asc if c['cell_id'] != 7]
pool = []
indices = []
for c in kept:
    ids = []
    for row in c['affine_constraints']:
        vec = tuple(row['affine'])
        if vec not in pool:
            pool.append(vec)
        ids.append(pool.index(vec))
    indices.append(ids)

def vector(xs): return '![' + ', '.join(map(str,xs)) + ']'
def fset(xs): return '{' + ', '.join(map(str,xs)) + '}'

lines = ['import Mathlib.Data.Fin.VecNotation', 'import Mathlib.Tactic', '',
 '/-! SOURCE ONLY. Literal source transcription, not a new numerical certificate.',
 'Original ascending family IDs 0..14 except 7, in original order.',
 'No geometry, centre, facet, integral, or finite proof is evaluated. -/', '',
 'namespace ImbalancedChen.P4AOriginalAscendingFourteenAffineSource',
 'noncomputable section', 'open scoped Classical BigOperators', '',
 'def originalId : Fin 14 → ℕ := ' + vector(c['cell_id'] for c in kept),
 'def leftMasks : Fin 14 → Finset ℕ :=',
 '  ![' + ',\n    '.join(fset(c['left_masks']) for c in kept) + ']', '',
 f'def literalPool : Fin {len(pool)} → Fin 9 → ℚ :=',
 '  ![' + ',\n    '.join(vector(v) for v in pool) + ']', '',
 f'def literalIndex : Fin 14 → Fin 96 → Fin {len(pool)} :=',
 '  ![' + ',\n    '.join(vector(v) for v in indices) + ']', '',
 'def rows (i : Fin 14) (r : Fin 96) : Fin 9 → ℚ := literalPool (literalIndex i r)', '',
 'end', 'end ImbalancedChen.P4AOriginalAscendingFourteenAffineSource', '']
(HERE/'P4AOriginalAscendingFourteenAffineSource.lean').write_text('\n'.join(lines),encoding='utf-8',newline='\n')

groups = [('ascending', kept[0], 6), ('seed', asc[7], 6), ('nine',nine[0],9),
          ('fiftyA',fiftyA,50),('fiftyD',fiftyD,50),('h5',h5[0],9),('h7',h7[0],9)]
selector_receipt = []
for tag,c,winner in groups:
    names=[r['name'] for r in c['affine_constraints']]
    def find(pred):
        matches=[i for i,n in enumerate(names) if pred(n)]
        if len(matches)!=1: raise ValueError((tag,matches))
        return matches[0]
    histories=[find(lambda n: ('first' in n and 'history' in n))]
    histories += [find(lambda n,j=j: ('H'+str(j)+' below') in n) for j in (3,5,7)]
    w=find(lambda n:'W below' in n)
    gap=find(lambda n:n=='new cap improvement')
    terminal=find(lambda n:'residual below3' in n)
    license=find(lambda n:n.startswith('new ') and 'license buffered' in n)
    full=[find(lambda n,j=j:n=='full square '+str(j+1)) for j in range(8)]
    complement=[]
    for j in range(8):
        hits=[i for i,n in enumerate(names) if n.endswith('remaining square '+str(j+1))]
        complement.append(hits[0] if hits else 0)
    if tag in ('ascending','seed'): side=find(lambda n:'winner6 descending' in n)
    elif tag=='nine': side=find(lambda n:'third winner6 descending' in n)
    elif tag=='fiftyA': side=find(lambda n:n=='minorant B3 ascending license')
    else: side=0
    common=list(range(10))+histories+[w,gap,terminal,license]+full+complement+[side]
    branches=[i for i,n in enumerate(names) if n.startswith('old subset ')]
    selector_receipt.append(dict(family=tag, row_count=len(names),common=common,branches=branches,winner=winner,
        common_names=[names[i] for i in common]))

with (HERE/'SOURCE_RECEIPT.json').open('w',encoding='utf-8') as f:
    json.dump(dict(status='TEXT_ONLY_UNEVALUATED',sources=receipts,ascending_row_count=sum(map(len,indices)),
      ascending_pool_size=len(pool), selectors=selector_receipt,
      source_producers_executed=False,guards_evaluated=False,lean_compiled=False),f,indent=2,ensure_ascii=False)
    f.write('\n')

out=['/- Source row positions copied from the original named rows. -/']
for r in selector_receipt:
    out.append(r['family']+' common '+vector(r['common']))
    out.append(r['family']+' branches '+vector(r['branches']))
(HERE/'ROW_SELECTORS.txt').write_text('\n'.join(out)+'\n',encoding='utf-8')
print('Materialized two unchanged Lean segments, fourteen ascending source tables, and row-name receipts. No guards evaluated.')
