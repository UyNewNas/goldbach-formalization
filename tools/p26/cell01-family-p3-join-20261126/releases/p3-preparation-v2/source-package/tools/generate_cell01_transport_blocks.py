#!/usr/bin/env python3
"""Author closed, ordered 16-row transport blocks; default is the first block.

This only writes new source. It computes no moment or floor, invokes no Lean,
and never edits an existing finite owner, generic owner, or generated block.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PREFIX = 'ImbalancedChen.P2OriginalSaving19'
INTERFACE = PREFIX + 'Cell01OriginalFloorInterface'
GENERIC = PREFIX + 'OriginalFloorTransport'
GENERIC_SHA = '9f4b64321975f8eb567484982abc622ee77ac222c90a6d117b2acc7a0f39b574'
ROW000 = PREFIX + 'Cell01Row000OriginalFloorBridge'
ROW000_SHA = '044746b6376ae5efdac05dd97b77ba9840c91435001acf3e7a402015b272ede8'


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def module_path(module):
    return REPO / (module.replace('.', '/') + '.lean')


def fp(path):
    data = path.read_bytes()
    return {'path': str(path.relative_to(REPO)), 'bytes': len(data),
            'sha256': hashlib.sha256(data).hexdigest()}


def finite_pins():
    series_path = REPO / 'tools/p26/cell01-rest/SOURCE_SERIES_MANIFEST.json'
    series = json.loads(series_path.read_text())
    rows = {row['ordinal']: row['source'] for row in series['rows']}
    rows[1] = series['accepted_row001_source']
    need(set(rows) == set(range(1, 144)), 'Incomplete original finite ordinal sequence')
    checked = {}
    names = ('deviationDenominators_ne', 'gapScale_ne', 'gap_encoding', 'deviation_encoding',
             'prefix_floor_checks', 'all_Q80_bounds', 'raw_vertices_eq', 'raw_row_eq',
             'raw_moment_row_eq')
    for ordinal in range(1, 144):
        path = module_path(PREFIX + f'Cell01Row{ordinal:03d}Finite')
        pin = fp(path)
        need(all(pin[k] == rows[ordinal][k] for k in ('bytes', 'sha256')),
             f'Original finite source differs: {ordinal}')
        text = path.read_text()
        need(all(re.search(r'\btheorem\s+' + name + r'\b', text) for name in names),
             f'Missing finite interface: {ordinal}')
        need(f'geometryRowsTyped{ordinal:03d}' in text and f'momentTypedRecord{ordinal:03d}' in text,
             f'Typed original ordinal differs: {ordinal}')
        checked[ordinal] = pin
    return checked, fp(series_path)


def block_module(block):
    return PREFIX + f'Cell01OriginalFloorBlock{16 * block:03d}_{16 * block + 15:03d}'


def row_source(ordinal):
    row = f'{ordinal:03d}'
    typed = '''  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds'''
    if ordinal == 0:
        typed = '''  ⟨P2OriginalSaving19Cell01Row000OriginalFloorBridge.original_floor_formula,
    P2OriginalSaving19Cell01Row000OriginalFloorBridge.original_Q80_bounds⟩'''
    return f'''
namespace Row{row}

open P2OriginalSaving19Cell01Row{row}
open P2OriginalSaving19Cell01Row{row}MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW{row}_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
{typed}

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt ({ordinal} : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices ({ordinal} : Fin 144)) vertices
    (rawGeometryRow ({ordinal} : Fin 144)) row
    (rawMomentRow ({ordinal} : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row{row}
'''


def render(block):
    start, stop = block * 16, block * 16 + 16
    name = block_module(block)
    imports = [INTERFACE]
    imports += [ROW000 if i == 0 else PREFIX + f'Cell01Row{i:03d}Finite'
                for i in range(start, stop)]
    header = '\n'.join('import ' + module for module in imports)
    header += '\nimport Mathlib.Tactic.FinCases\n'
    header += f'''
/-!
SOURCE CANDIDATE / NOT COMPILED. Closed original rationalMoment/floor transports
for the original cell01 ordinals {start} through {stop - 1}, in that order.
The original finite facts and raw bindings are imported unchanged. No encoded
moment arithmetic is recomputed, and no original floor target is a premise.
This is a 16-row block, not an assertion for all 144 rows or any integral.
-/
namespace {name}

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19OriginalFloorTransport
open P2OriginalSaving19Cell01OriginalFloorInterface
'''
    body = ''.join(row_source(i) for i in range(start, stop))
    tail = f'''
/-- This map retains the original ordinal; it does not reorder the rows. -/
def originalOrdinal (i : Fin 16) : Fin 144 :=
  ⟨{start} + i.val, by have hi := i.isLt; omega⟩

theorem originalOrdinal_value (i : Fin 16) :
    (originalOrdinal i).val = {start} + i.val := rfl

theorem all_original_floor_and_bounds (i : Fin 16) :
    OriginalFloorAndBoundsAt (originalOrdinal i) := by
  fin_cases i
'''
    tail += ''.join(f'  · exact Row{i:03d}.raw_original_floor_and_bounds\n' for i in range(start, stop))
    tail += f'''
#print axioms originalOrdinal_value
#print axioms all_original_floor_and_bounds

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_{start:03d}_{stop - 1:03d}_complete"
  err.flush

end {name}
'''
    return header + body + tail


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--blocks', type=int, nargs='+', default=[0])
    parser.add_argument('--report', type=Path, default=HERE / 'cell01-blocks-pilot' / 'GENERATION.json')
    args = parser.parse_args()
    need(args.blocks == sorted(set(args.blocks)) and all(0 <= b < 9 for b in args.blocks),
         'Blocks must be a unique ordered subset of 0 through 8')
    checked, series = finite_pins()
    need(fp(module_path(GENERIC))['sha256'] == GENERIC_SHA, 'Generic source changed')
    need(fp(module_path(ROW000))['sha256'] == ROW000_SHA, 'Accepted row000 bridge changed')
    need(module_path(INTERFACE).is_file(), 'Missing separately authored raw interface')
    outputs = [(module_path(block_module(b)), render(b)) for b in args.blocks]
    report = args.report.absolute()
    for path in [p for p, _ in outputs] + [report]:
        need('..' not in path.parts and path.resolve() == path and not path.is_symlink() and
             not path.exists(), f'Refusing existing/noncanonical output: {path}')
    for path, text in outputs:
        need(not re.search(r'\b(axiom|sorry|admit|native_decide|unsafe)\b', text),
             'Forbidden source mechanism')
        with path.open('x') as stream:
            stream.write(text)
    after, after_series = finite_pins()
    need(after == checked and after_series == series, 'Finite sources changed during authoring')
    need(fp(module_path(GENERIC))['sha256'] == GENERIC_SHA and
         fp(module_path(ROW000))['sha256'] == ROW000_SHA, 'Existing transport source changed')
    value = {'status': 'SOURCE_ONLY_NOT_COMPILED', 'blocks': args.blocks,
        'source_outputs': [fp(path) for path, _ in outputs], 'shared_interface': fp(module_path(INTERFACE)),
        'generic_supplier': fp(module_path(GENERIC)), 'accepted_row000_supplier': fp(module_path(ROW000)),
        'all_143_finite_sources_checked_unchanged': [checked[i] for i in range(1, 144)],
        'finite_series_manifest': series, 'new_numeric_calculations': 0,
        'proof_premises_on_closed_row_theorems': 0, 'Lean_invoked': False,
        'cloud_jobs_submitted': 0, 'Git_or_STATUS_changed': False}
    report.parent.mkdir(parents=True, exist_ok=True)
    with report.open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')
    print(json.dumps({'report': fp(report), 'outputs': value['source_outputs'],
                      'finite_sources_unchanged': len(checked), 'Lean_invoked': False}, indent=2))


if __name__ == '__main__':
    main()
