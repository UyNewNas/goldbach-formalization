"""Copy original source bytes/affine strings only; never execute a producer.

No point, vertex, guard, integral, budget, Lean body or saved sum is evaluated.
The source tuple selectors are the retained records in the manuscript's
sixth local-additions and nonsingleton inventories.  Existing eleven-cell
semantics and fourth/fifth materializations are imported, not regenerated.
"""
from pathlib import Path
import hashlib
import io
import json
import zipfile

ROOT = Path(__file__).resolve().parents[5]
OUT = Path(__file__).resolve().parent
ARCHIVE = ROOT / 'goldbach-proof-continuation/.lake/proof-continuation/source-reviews/drafts/20261028-EvidenceLocator/chen-numerical-evidence-20261010.zip'
PUBLIC = ROOT / 'chen-imbalanced-semiprimes/paper/release-20261101/numerical-supplement/witnesses'
PREFIX = 'chen-numerical-evidence-20261010-renewal-v2/goldbach-research/'
receipt = []

def read_archive(name):
    with zipfile.ZipFile(ARCHIVE) as z:
        raw = z.read(PREFIX + name)
    receipt.append(dict(path=str(ARCHIVE), entry=PREFIX+name,
                        sha256=hashlib.sha256(raw).hexdigest(), bytes=len(raw)))
    return raw

def public(number):
    p = PUBLIC / f'record-{number:04d}.json'
    raw = p.read_bytes()
    receipt.append(dict(path=str(p), sha256=hashlib.sha256(raw).hexdigest(), bytes=len(raw)))
    return json.loads(raw)

def nav(name):
    return json.loads(read_archive(name))['records']

cells = []
def add(c, stage, mask, descending, mapped, selector, license_index, comparison):
    # Copy every affine coefficient string verbatim, retaining row order.
    cells.append(dict(stage=stage, mask=mask, descending=descending,
        mapped=mapped, selector=selector, license_index=license_index,
        comparison=comparison, rows=c['affine_constraints'],
        identities=c.get('constant_identities', [])))

for n,stage,mask,desc,lic in [(741,0,33,True,46),(749,1,34,False,47),(757,2,34,True,47)]:
    for i,c in enumerate(public(n)['cells']):
        # G9/G10 comparison charts are R0 then D33, literally.
        comp = 0 if stage == 0 or i == 0 else 1
        add(c,stage,mask,desc,True,dict(record=n,cell=i),lic,comp)

for name,stage,desc in [
    ('sixth-lower-clip-window-navigation-20261009.json',3,False),
    ('sixth-lower-desc34-window-20261009-navigation.json',4,True)]:
    records = nav(name)
    i,c = next((i,c) for i,c in enumerate(records) if c['pattern']==1371)
    add(c,stage,34,desc,False,dict(entry=name,record=i,pattern=1371),42,0)

for name,patterns,branch_field,stage,mask in [
    ('sixth-lower-mask33-cells-20261009-navigation.json',[1867],'cap_branch',5,33),
    ('sixth-lower-mask50-cells-20261009-navigation.json',[1353,1355],'cap_branch',5,50),
    ('sixth-lower-mask33-upgrade-20261009-navigation.json',[1371],'cap_branch',6,33)]:
    for i,c in enumerate(nav(name)):
        if c['pattern'] not in patterns:
            continue
        if stage==6 and c['cap_branch']!=1:
            continue
        desc = True if mask==33 else bool(c['cap_branch'])
        add(c,stage,mask,desc,False,dict(entry=name,record=i,pattern=c['pattern'],
            cap_branch=c['cap_branch']),42,2 if stage==6 else 0)

for i,c in enumerate(public(712)['cells']):
    add(c,7,33,bool(c['newbranch']),False,dict(record=712,cell=i,
        pattern=c['pattern'],newbranch=c['newbranch'],oldfail=c['oldfail']),50,0)

# Exact NPY materialization.  This is an unzip, with no NumPy import,
# data conversion, arithmetic check, parser execution or numerical replay.
npz = read_archive('sixth-prefix-expanded-cover-400.npz')
with zipfile.ZipFile(io.BytesIO(npz)) as z:
    names = z.namelist()
    npy = z.read('cells.npy')
provenance = OUT/'provenance'
provenance.mkdir(exist_ok=True)
(provenance/'OriginalSixthCells.npy').write_bytes(npy)
receipt.append(dict(materialized='provenance/OriginalSixthCells.npy',
                    npz_entry='cells.npy', sha256=hashlib.sha256(npy).hexdigest(),bytes=len(npy)))

def q(s):
    return '('+str(s)+')'
def vec(values):
    return '!['+', '.join(map(q,values))+']'
def cases(field,conv=str):
    return '\n'.join(f'  | {i} => {conv(c[field])}' for i,c in enumerate(cells))

lines = ['import Mathlib.Data.Fin.VecNotation','import Mathlib.Tactic','',
'/-! Original source strings only. SOURCE ONLY / UNCOMPILED / finite bodies UNEVALUATED.',
'G13 comparison corrections have no action here. Existing G7 eleven cells are reused.',
'The nineteen extra genuine actions follow the original same-node chronology. -/',
'namespace ImbalancedChen.P4AOriginalSixthLaterLiteral','noncomputable section',
'abbrev Point := Fin 6 → ℝ','abbrev Affine := Fin 7 → ℝ',
'abbrev Cell := Fin 19','',
'def rows : Cell → List Affine',]
for i,c in enumerate(cells):
    lines.append(f'  | {i} => [')
    for j,r in enumerate(c['rows']):
        lines.append('    '+vec(r['affine'])+(',' if j+1<len(c['rows']) else '')+f' -- {j}: '+r['name'])
    lines.append('  ]')
lines += ['', 'def stage : Cell → ℕ',cases('stage'),
          '', 'def mask : Cell → ℕ',cases('mask'),
          '', 'def descending : Cell → Bool',cases('descending',lambda b:'true' if b else 'false'),
          '', 'def mapped : Cell → Bool',cases('mapped',lambda b:'true' if b else 'false'),
          '', 'def comparisonChart : Cell → ℕ',cases('comparison'),
          '', 'def licenseIndex : Cell → ℕ',cases('license_index'),
          '', 'def oppositeLicenseRow : Cell → Affine']
for i,c in enumerate(cells):
    lines.append(f"  | {i} => {vec(c['rows'][c['license_index']]['affine'])}")
lines += ['', 'theorem oppositeLicenseRow_mem (c : Cell) : oppositeLicenseRow c ∈ rows c := by',
'  fin_cases c <;> simp [oppositeLicenseRow, rows]', '',
'end','end ImbalancedChen.P4AOriginalSixthLaterLiteral','']
(OUT/'P4AOriginalSixthLaterLiteral.lean').write_text('\n'.join(lines),encoding='utf-8')
(OUT/'SOURCE_RECEIPT.json').write_text(json.dumps(dict(archive=str(ARCHIVE),
    source_records=receipt, later_cells=cells,
    numerical_execution=False, note='raw source copying only; no source result is treated as a theorem'),
    ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(later_cells=len(cells),literal_rows=sum(len(c['rows']) for c in cells),
    npy_bytes=len(npy),npy_header_hex=npy[:128].hex(),
    files=['P4AOriginalSixthLaterLiteral.lean','provenance/OriginalSixthCells.npy','SOURCE_RECEIPT.json'])))
