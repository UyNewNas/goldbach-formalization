import argparse
import hashlib
import json
import re
from fractions import Fraction
from pathlib import Path

parser = argparse.ArgumentParser(description='Check selected later-sixth Q96 sums; not a Lean proof replay.')
parser.add_argument('--project-dir', required=True, type=Path)
parser.add_argument('--receipts', required=True, type=Path)
parser.add_argument('--output', required=True, type=Path)
args = parser.parse_args()
data = args.project_dir / '../tmp/publication-20261010/verification-renewal-v2/_runs/full-final'
receipts = json.loads(args.receipts.read_text())
docs = []
for row in receipts:
    raw = (data / row['name']).read_bytes()
    if len(raw) != row['bytes'] or hashlib.sha256(raw).hexdigest() != row['sha256']:
        raise ValueError('fixture identity mismatch: ' + row['name'])
    docs.append(json.loads(raw))

files = [0,0,1,1,2,2,3,4,5,5,6,6,6,6,7,8,8,8,8,9,9]
offsets = [0,1,0,1,0,1,0,0,0,3,0,1,2,3,0,0,1,2,3,0,1]
nav = [None,None,None,None,None,None,(10,8),(11,8),(12,11),(12,28),
       (13,6),(13,7),(13,23),(13,24),(14,1),None,None,None,None,None,None]
patterns = [1371,1867,1371,1371,1371,1371,1371,1371,1867,1867,1353,1355,1353,1355,1371,1355,1355,1867,1867,1371,1371]
counts = [420,225,231,390,180,378,626,274,599,101,6,1,6,6,120,60,153,322,1,390,300]
slots = [0,0,1,1,2,2,3,4,5,5,5,5,5,5,5,6,6,6,6,5,5]
expected = [148834609033428677786865,306737545112876482463163,187277743940187526723019,
            670429887277013841791829,2*198410119216276585672773,8*5023185001132087792027,
            16*581521529176619227721]
source_dir = args.project_dir / 'ImbalancedChen'
archive_bytes = (source_dir / 'P2OriginalLaterSixthArchive.lean').read_bytes()
kernel_bytes = (source_dir / 'P2OriginalLaterSixthKernel.lean').read_bytes()
if hashlib.sha256(archive_bytes).hexdigest() != 'b76b2559bcff838a680d0b931fba5817d709da35d395eaa21ca31190be38128d':
    raise ValueError('archive Lean source identity mismatch')
if hashlib.sha256(kernel_bytes).hexdigest() != '5cb132dd52bac5cd4c6bf5914dff23b4f3da78db33df7b752adae8c556dadbdd':
    raise ValueError('kernel Lean source identity mismatch')
archive = archive_bytes.decode()
kernel = kernel_bytes.decode()
def array_body(text, declaration, marker='!'):
    match = re.search(r'\bdef\s+' + re.escape(declaration) + r'\b[^\n]*:=\s*' + re.escape(marker) + r'\[(.*?)\]', text, re.S)
    if not match:
        raise ValueError('missing Lean array: ' + declaration)
    return match.group(1)
def nums(text, declaration):
    return [int(x.strip()) for x in array_body(text, declaration).split(',')]
if nums(archive, 'file') != files or nums(archive, 'offset') != offsets or nums(archive, 'pattern') != patterns or nums(archive, 'pieceCount') != counts:
    raise ValueError('archive array mismatch')
if nums(kernel, 'slot') != slots:
    raise ValueError('kernel slot mapping mismatch')
lean_names = re.findall(r'"([^"]+)"', array_body(archive, 'names', '#'))
if lean_names != [x['name'] for x in receipts]:
    raise ValueError('Lean document-name array mismatch')
nav_tokens = re.findall(r'none|some\s*\(\s*\d+\s*,\s*\d+\s*\)', array_body(archive, 'nav'))
lean_nav = [None if x == 'none' else tuple(map(int, re.findall(r'\d+', x))) for x in nav_tokens]
if lean_nav != nav:
    raise ValueError('Lean navigation mapping mismatch')
slot_theorem = re.search(r'theorem\s+original_slot_totals\b.*?=\s*!\[(.*?)\]\s*s\s*:=', archive, re.S)
if not slot_theorem:
    raise ValueError('Lean original_slot_totals array missing')
def product_of_integer_literals(expression):
    parts = expression.strip().split('*')
    if not all(x.strip().isdigit() for x in parts):
        raise ValueError('unexpected Lean numerical expression')
    result = 1
    for x in parts:
        result *= int(x.strip())
    return result
if [product_of_integer_literals(x) for x in slot_theorem.group(1).split(',')] != expected:
    raise ValueError('Lean original_slot_totals mismatch')
if 'if 3≤(file i).val ∧ (file i).val≤7 then "jensen_floor_Q96" else "floor_Q96"' not in archive:
    raise ValueError('Lean floor-key selection mismatch')
totals = [0]*7
piece_receipts = []
roundings_checked = 0
auxiliary_roundings_checked = 0
for i in range(21):
    f, off = files[i], offsets[i]
    geometry = docs[f] if f in (3,4) else docs[f]['cells'][off]
    gates = geometry if nav[i] is None else docs[nav[i][0]]['records'][nav[i][1]]
    if gates['pattern'] != patterns[i] or (f not in (3,4) and geometry['pattern'] != patterns[i]):
        raise ValueError('pattern mismatch: ' + str(i))
    vertices = geometry['vertices']
    simplices = geometry['simplices']
    if len(simplices) != counts[i]:
        raise ValueError('simplex count mismatch: ' + str(i))
    floor_key = 'jensen_floor_Q96' if 3 <= f <= 7 else 'floor_Q96'
    subtotal = 0
    for number, simplex in enumerate(simplices):
        if simplex['simplex_id'] != number or len(simplex['vertex_ids']) != 7:
            raise ValueError(f'simplex shape mismatch: {i}/{number}')
        if any(v < 0 or v >= len(vertices) for v in simplex['vertex_ids']):
            raise ValueError(f'vertex index outside bounds: {i}/{number}')
        claimed_floor = int(simplex[floor_key])
        exact_key = ('exact_jensen_lower' if 'exact_jensen_lower' in simplex else
                     'weighted_jensen_bound' if 'weighted_jensen_bound' in simplex else 'exact_lower')
        exact = Fraction(simplex[exact_key]) * (1 << 96)
        if claimed_floor != exact.numerator // exact.denominator:
            raise ValueError(f'Q96 rounding mismatch: {i}/{number}')
        roundings_checked += 1
        if 'max_factor_floor_Q96' in simplex:
            exact_max = Fraction(simplex['exact_max_factor_lower']) * (1 << 96)
            if int(simplex['max_factor_floor_Q96']) != exact_max.numerator // exact_max.denominator:
                raise ValueError(f'max-factor rounding mismatch: {i}/{number}')
            auxiliary_roundings_checked += 1
        elif 'max_floor_Q96' in simplex:
            exact_max = Fraction(simplex['max_bound']) * (1 << 96)
            if int(simplex['max_floor_Q96']) != exact_max.numerator // exact_max.denominator:
                raise ValueError(f'max rounding mismatch: {i}/{number}')
            auxiliary_roundings_checked += 1
        subtotal += claimed_floor
    totals[slots[i]] += subtotal
    piece_receipts.append({'piece':i,'slot':slots[i],'fixture':receipts[f]['name'],
                           'offset':off,'count':len(simplices),'q96_sum':str(subtotal),
                           'navigation':None if nav[i] is None else [receipts[nav[i][0]]['name'],nav[i][1]]})
if totals != expected:
    raise ValueError('Q96 slot totals mismatch: '+repr(totals))
cells=docs[8]['cells']
q=1<<96
lower=[Fraction(cell['gain_lower'])*q for cell in cells]
if len(cells)!=4 or any(x.denominator!=1 for x in lower) or sum(lower)!=expected[6]:
    raise ValueError('G14 four-cell aggregate mismatch')
if any(piece_receipts[15+i]['q96_sum'] != str(lower[i].numerator) for i in range(4)):
    raise ValueError('G14 per-cell floor mismatch')
report={'fixtures':len(receipts),'pieces':len(piece_receipts),'simplices':sum(counts),
        'recorded_q96_roundings_checked':roundings_checked,
        'auxiliary_q96_roundings_checked':auxiliary_roundings_checked,
        'slot_totals':[str(x) for x in totals], 'expected_slot_totals_match':True,
        'g14_cell_q96_numerators':[str(x.numerator) for x in lower],
        'g14_cell_counts':[len(x['simplices']) for x in cells],
        'g14_gain_lower_sum_q96':str(sum(lower).numerator),
        'piece_receipts':piece_receipts}
args.output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ('fixtures','pieces','simplices','recorded_q96_roundings_checked','auxiliary_q96_roundings_checked','slot_totals','expected_slot_totals_match','g14_cell_q96_numerators','g14_cell_counts','g14_gain_lower_sum_q96')}))
