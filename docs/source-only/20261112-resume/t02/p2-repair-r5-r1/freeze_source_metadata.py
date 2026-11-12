"""Static source/AST/hash metadata only; never loads Lean or candidate programs."""
from pathlib import Path
import difflib
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
LOG = ROOT / 'output/resume-20261112/ci-watch-v2/43203705975-batch-build.log'


def identity(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
            'git_blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()}


def write(name, value):
    (HERE / name).write_bytes((json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode())


def mask(text):
    out = list(text); i = 0
    while i < len(text):
        begin = i
        if text[i:i+2] == '--':
            i = text.find('\n', i)
            if i == -1: i = len(text)
        elif text[i:i+2] == '/-':
            depth = 1; i += 2
            while depth:
                assert i < len(text), 'Unclosed Lean comment'
                if text[i:i+2] == '/-': depth += 1; i += 2
                elif text[i:i+2] == '-/': depth -= 1; i += 2
                else: i += 1
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\': i += 2
                elif text[i] == '"': i += 1; break
                else: i += 1
        else:
            i += 1; continue
        for j in range(begin, i):
            if text[j] != '\n': out[j] = ' '
    return ''.join(out)


COMMAND = re.compile(r'(?m)^(?:(?:private|protected|noncomputable|unsafe)\s+)*(?:theorem|lemma|def|abbrev|inductive|structure|instance|namespace|end|open|section|local|set_option|attribute|variable|export|include|omit)\b')
DECL = re.compile(r'(?:(?:private|protected|noncomputable|unsafe)\s+)*(theorem|lemma|def|abbrev|inductive|structure|instance)\s+([^\s(:]+)')


def partition(text):
    masked = mask(text)
    positions = list(COMMAND.finditer(masked))
    headers, definitions, nonproof, last = [], [], [], 0
    for i, position in enumerate(positions):
        end = positions[i+1].start() if i+1 < len(positions) else len(text)
        declaration = DECL.match(masked, position.start())
        if not declaration: continue
        kind, name = declaration.groups()
        if kind in ['theorem', 'lemma']:
            by = re.search(r':=\s*by\b', masked[position.start():end])
            assert by, (name, 'Expected a proof body')
            proof = position.start() + by.end()
            headers.append({'name': name, 'kind': kind, 'header': text[position.start():proof]})
            nonproof.extend([text[last:proof], '\n<PROOF_BODY>\n']); last = end
        else:
            definitions.append({'name': name, 'kind': kind, 'complete_command': text[position.start():end]})
    nonproof.append(text[last:])
    return headers, definitions, ''.join(nonproof)


assert identity(LOG.read_bytes())['sha256'] == 'fcd185532b750e89ff0efd7f6625c014b5efa54ecb00ec036abd9426fad51877'
lines = LOG.read_text(encoding='utf-8').splitlines()
errors = []
for i, line in enumerate(lines):
    match = re.match(r'error: (ImbalancedChen/[^:]+):(\d+):(\d+): (.*)', line)
    if match:
        stop = next((j for j in range(i+1, len(lines)) if re.match(r'(?:error:|warning:|trace:|[✔✖⚠ℹ])', lines[j])), len(lines))
        errors.append({'log_line_1based': i+1, 'source': match[1], 'source_line': int(match[2]),
                       'source_column': int(match[3]), 'message': match[4], 'diagnostic': '\n'.join(lines[i:stop])})
assert len(errors) == 13
write('ACTUAL_ERROR_INDEX.json', {'run':43203705975,'job':131133389626,'log':identity(LOG.read_bytes()),'diagnostics':errors})
(HERE / 'ACTUAL_ERROR_EXCERPT.txt').write_bytes(('\n\n'.join(f"log line {r['log_line_1based']}\n{r['diagnostic']}" for r in errors)+'\n').encode())
selected = json.loads((HERE / 'SELECTED_ORIGINALS.json').read_text(encoding='utf-8'))
records, patch_all, all_old_headers, all_new_headers = [], [], [], []
for row in selected['records']:
    original = HERE / 'original' / row['install_path']; repaired = HERE / 'repaired' / row['install_path']
    a, b = original.read_bytes(), repaired.read_bytes()
    assert identity(a) == {k: row[k] for k in ['bytes','sha256','git_blob']}
    ah, ad, an = partition(a.decode()); bh, bd, bn = partition(b.decode())
    assert ah == bh, row['module']
    assert ad == bd, row['module']
    assert an == bn, row['module']
    patch = ''.join(difflib.unified_diff(a.decode().splitlines(True), b.decode().splitlines(True),
                        fromfile='original/'+row['install_path'], tofile='repaired/'+row['install_path']))
    patch_path = HERE / 'patches' / (original.stem + '.patch'); patch_path.parent.mkdir(exist_ok=True)
    patch_path.write_bytes(patch.encode()); patch_all.append(patch)
    all_old_headers += ['MODULE '+row['module']+'\n'+x['header'] for x in ah]
    all_new_headers += ['MODULE '+row['module']+'\n'+x['header'] for x in bh]
    records.append({'module':row['module'],'original_selected_record':row,'original':identity(a),'repaired':identity(b),
                    'header_count':len(ah),'complete_headers':ah,'complete_definition_count':len(ad),
                    'complete_definitions':ad,'nonproof_text_sha256':hashlib.sha256(an.encode()).hexdigest(),
                    'all_nonproof_bytes_unchanged':True,'patch':patch_path.relative_to(HERE).as_posix(),
                    'error_count':sum(x['source']==row['install_path'] for x in errors)})
(HERE/'P2_REPAIR_R5.patch').write_bytes(''.join(patch_all).encode())
(HERE/'DECLARATION_HEADERS.original.txt').write_bytes(('\n\n'.join(all_old_headers)+'\n').encode())
(HERE/'DECLARATION_HEADERS.repaired.txt').write_bytes(('\n\n'.join(all_new_headers)+'\n').encode())
report = '''P2 r5 source-only repair of actual run43203705975 / job131133389626.

Evidence is the uniquely downloaded light artifact13940417344, ZIP SHA0c297298cfb1a6d7749096ace40abcb24f1c037d6209b857034ac4f9e4553251, and actual91531B batch-build.log SHA fcd185532b750e89ff0efd7f6625c014b5efa54ecb00ec036abd9426fad51877. Full compile failed13 actual source diagnostics across5 targets. Strict singleton FinitePi preflight passed5 exact declarations; full102 kernel/owner/types was not reached. Job heavy retention was still running when this light evidence was received. No terminal/full acceptance is inferred.

Original selection comes from frozen v5 manifest. P4AOriginalRange32MassCeil uses actual e687 r4 bytes; the other four are exact eb035 baseline bytes. All original and repaired theorem headers, complete definitions, imports, data, parameters, namespaces and nonproof source text are identical. There is no additional open/qualification exception in r5. Static source partitioning and explicit unified patches record the proof-only boundary; this is not successful elaborated-type or kernel equivalence evidence.

Range32 and Balanced: simplify only Nat.cast_ofNat in the real output of existing divNat_sound before applying the existing half-mass equality; the interval arithmetic operation tree remains unchanged. Balanced and Safe: case-split the existing TentSide when giving dependent guard proof arguments, preserving every original branch/root/residual predicate. Dispatch: case-split TentSide in usable guard proof arguments; after the case equation has already rewritten the goal, use reflexive constructor equality in winner cases. Clipped: use the existing two linear bounds directly to prove t<=2+d, avoiding the imported same-name addition lemma; explicitly type the local eventual subset as a Set BoxPoint. Safe: normalize 2*(b-a)/log to2*((b-a)/log) before linear arithmetic; separate the numeral/order/identifier tokens in the local reciprocal-mean inequality; first prove the existing product inequality then add flo by linear arithmetic, avoiding the incompatible imported addition helper.

R5-r1 additionally makes the subtrahend in the new independent hprod binding explicit, as required by static review; see R5_R1_ERRATA.json. The first frozen r5 remains intact.

These are proof expression, elaboration and API/name/token/normal-form repairs; no mathematical gap is asserted or hidden by a new assumption. No premise is weakened, theorem removed, definition changed, trust increased, axiom/sorry/native_decide introduced, or resource profile altered. Prior r2/r3/r4 and v1-v5 frozen packages stay untouched. No Lean/Lake/LSP/env/setup/stage/checker/producer/guard or new fixture was run locally. T10 source review and a new root-owned exact GitHub run remain necessary.
'''
(HERE/'REPAIR_REPORT.txt').write_bytes(report.encode())
registry = {'schema':'P2-actual-r4-failure-source-repair-r5','status':'FROZEN_SOURCE_ONLY_PENDING_T10_AND_GITHUB',
            'manifest':{'path':'output/resume-20261112/p2-validation-v5/P2_VALIDATION_MANIFEST.json','sha256':selected['manifest_sha256']},
            'failure_evidence':{'run':43203705975,'job':131133389626,'log':identity(LOG.read_bytes()),'source_diagnostics':len(errors)},
            'modules':records,'only_nonproof_change':None,'all_prior_frozen_packages_untouched':True,
            'local_Lean_Lake_LSP_stage_guard_checker_proof_runtime_execution':False,
            'mathematical_gap_claimed':False,'mathematical_premises_changed':False}
registry['independent_review_errata'] = json.loads((HERE/'R5_R1_ERRATA.json').read_text(encoding='utf-8'))
write('REPAIR_REGISTRY.json',registry)
files = [{'path':p.relative_to(HERE).as_posix(),**identity(p.read_bytes())} for p in sorted(HERE.rglob('*'))
         if p.is_file() and p.name != 'FREEZE_SHA256.json']
write('FREEZE_SHA256.json',{'status':'FROZEN_STATIC_SOURCE_ONLY','files':files})
print(json.dumps({'registry':identity((HERE/'REPAIR_REGISTRY.json').read_bytes()),'freeze':identity((HERE/'FREEZE_SHA256.json').read_bytes()),
                  'file_count':len(files)+1,'headers':sum(r['header_count'] for r in records),'definitions':sum(r['complete_definition_count'] for r in records),
                  'sources':[{'module':r['module'],**r['repaired']} for r in records]}))
