#!/usr/bin/env python3
"""Local-only scalable original-geometry candidates; never an acceptance tool.

Parser fragments keep the reviewed direct-packed templates.  A typed leaf
imports only its matching parser leaf, not a whole-array value or preceding
typed leaf.  Every generated assertion remains pending normal/kernel/owned QA.
"""
from pathlib import Path
from types import SimpleNamespace
import argparse
import hashlib
import importlib.util
import json
import re
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
LEGACY = REPO / 'docs/verification/20261125-p26/geometry-direct-packed-source-only'
sys.path.insert(0, str(LEGACY))
import generate as legacy
import raw_planner as base
import fragment_templates as fragments
sys.path.insert(0, str(HERE))
from quotation import record_value
from row_templates import render_row

legacy.OWNER_RAW_BUDGET = 65536


def fp(path):
    path = Path(path)
    data = path.read_bytes()
    return {'path': str(path.relative_to(REPO)) if path.is_relative_to(REPO) else str(path),
            'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def write_new(path, text):
    path = Path(path)
    data = text.encode() if isinstance(text, str) else text
    if path.exists():
        assert path.read_bytes() == data, ('Candidate drift; use a new file or explicit reviewed revision', path)
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)


class Engine(legacy.Engine):
    def __init__(self, cell, raw_root, rows_per_leaf=8):
        self.cell = cell
        self.project = REPO
        self.tag = f'P2OriginalSaving19Geometry{cell:02d}Scalable'
        self.ns = f'ImbalancedChen.P2OriginalSaving19Geometry{cell:02d}ScalableParsing'
        self.typed_ns = f'ImbalancedChen.P2OriginalSaving19Geometry{cell:02d}ScalableDecoding'
        self.raw_origin = raw_root / f'eighth-third-minorant-extension-20261009-a23-s23_low-{cell:02d}-cell.witness.json'
        self.raw = self.raw_origin.read_bytes()
        expected = next(x for x in json.loads((REPO / 'docs/verification/20261125-p26/archive-v4/INPUT_PATHS.json').read_text())['paths']
                        if x['family'] == 'geometry' and x['cell'] == cell)
        assert len(self.raw) == expected['bytes']
        assert hashlib.sha256(self.raw).hexdigest() == expected['sha256']
        assert self.raw.isascii()
        self.expected = {'module': f'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData{cell:02d}'}
        self.node = base.RawPlanner(self.raw).value(0)
        assert self.node.kind == 'obj' and self.node.start == 0
        assert all(x in base.WHITE for x in self.raw[self.node.end:])
        keys = [x.key.scalar for x in self.node.fields]
        assert len(set(keys)) == len(keys)
        self.fields = {x.key.scalar: x for x in self.node.fields}
        self.rows_per_leaf = rows_per_leaf
        self.records = []
        fragments.configure(cell, self.raw, self.chunks_for)

    def save(self, short, text, scope, plan):
        assert short.startswith(self.tag)
        text = text.replace('\ndef ', '\nnoncomputable def ')
        assert not re.search(r'\b(?:sorry|admit|native_decide|unsafe)\b|(?m:^\s*axiom\b)', text)
        path = REPO / 'ImbalancedChen' / (short + '.lean')
        write_new(path, text)
        row = {'module': 'ImbalancedChen.' + short, 'source': fp(path), 'scope': scope,
               'project_imports': re.findall(r'(?m)^import\s+(ImbalancedChen\.\S+)', text),
               'planned_obligations': plan, 'cell': self.cell, 'normal_kernel_owned_accepted': False}
        self.records.append(row)
        return row

    def block_plan(self, key):
        node = self.fields[key].value
        assert key == 'simplices', 'Pilot deliberately limits leaves to the original simplex row array.'
        chunks = self.chunks_for(node, max_items=1)
        groups = [chunks[i:i + self.rows_per_leaf] for i in range(0, len(chunks), self.rows_per_leaf)]
        return node, groups

    def typed_leaf(self, block):
        node, groups = self.block_plan('simplices')
        group = groups[block]
        first, after = group[0]['first'], group[-1]['after']
        ids = list(range(first, after))
        short = self.tag + f'TypedRows{block:03d}'
        parser_short = self.tag + f'SimplicesBlock{block:03d}'
        source = f'''import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.{parser_short}

/-! Local typed certificates for original cell {self.cell:02d}, rows {first} through {after-1}.
This owner imports only its own original parser leaf.  No cumulative typed
prefix, whole-array parser value, or completed geometric archive is imported.
The original rational decoder and GeometryRow record fields are unchanged. -/
namespace {self.typed_ns}
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open {self.ns}
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

'''
        chunk = {'index': block, 'first': first, 'after': after,
                 'start': group[0]['start'], 'end': group[-1]['end']}
        q = SimpleNamespace(
            chunks_for=lambda _: [chunk], FIELDS={'simplices': node}, base=base,
            item_name=lambda tag, i: f'geometry{tag}Json{i:03d}',
            typed_name=lambda tag, i: f'geometry{tag}Typed{i:03d}',
            decode_name=lambda tag, i: f'decode_geometry_{tag}_{i:03d}',
            orig_push=lambda _key, i: f'SimplicesBlock{i:03d}.blockPush',
            record_value=record_value,
            mark=lambda label: legacy.marker(f'SCALABLE_{self.cell:02d}_{label}'))
        names, row_plans = [], []
        for index in ids:
            body, declared, row_plan = render_row(q, index)
            source += body
            names.extend(declared)
            row_plans.append(row_plan)
            typed = f'geometryRowsTyped{index:03d}'
            shape = f'geometryRow{index:03d}_shape'
            vertex_count = len(self.fields['vertices'].value.children)
            source += f'''theorem {shape} :
    {typed}.simplexId = {index} ∧
    {typed}.vertexIds.size = 9 ∧ {typed}.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, {typed}.vertexIds[i.val]! < {vertex_count}) ∧
    {typed}.factorMaxima.size = 10 ∧ {typed}.gapWeightedMeans.size = 10 := by
  decide +kernel

'''
            names.append(shape)
        raw = f'geometryRowsJsonBlock{block:03d}'
        typed = f'geometryRowsTypedBlock{block:03d}'
        source += f'noncomputable def {raw} : List SourceJson := [' + ', '.join(f'geometryRowsJson{i:03d}' for i in ids) + ']\n'
        source += f'noncomputable def {typed} : List GeometryRow := [' + ', '.join(f'geometryRowsTyped{i:03d}' for i in ids) + ']\n\n'
        source += f'''theorem geometry_Rows_block_{block:03d}_push_eq (acc : List SourceJson) :
    SimplicesBlock{block:03d}.blockPush acc = [{', '.join(f'geometryRowsJson{i:03d}' for i in reversed(ids))}] ++ acc := by rfl

theorem geometry_Rows_block_{block:03d}_reverse (acc : List SourceJson) :
    (SimplicesBlock{block:03d}.blockPush acc).reverse = acc.reverse ++ {raw} := by
  rw [geometry_Rows_block_{block:03d}_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_{block:03d} :
    {raw}.mapM decodeGeometryRow = .ok {typed} := by
  simp only [{raw}, {typed}, List.mapM_cons, List.mapM_nil,
    {', '.join(f'decode_geometry_Rows_{i:03d}' for i in ids)}]
  rfl

theorem geometry_Rows_block_{block:03d}_length : {typed}.length = {len(ids)} := by rfl

'''
        names.extend([f'geometry_Rows_block_{block:03d}_push_eq', f'geometry_Rows_block_{block:03d}_reverse',
                      f'decode_geometry_Rows_block_{block:03d}', f'geometry_Rows_block_{block:03d}_length'])
        source += '\n'.join('#print axioms ' + n for n in names) + f'\n\nend {self.typed_ns}\n'
        return self.save(short, source, 'Independent local typed leaf and literal row shape facts', {
            'rows': [first, after], 'matching_parser': 'ImbalancedChen.' + parser_short,
            'raw_span': [group[0]['start'], group[-1]['end']], 'row_plans': row_plans,
            'row_shape_vertex_upper_bound': vertex_count,
            'vertex_array_decode_count_binding_claimed': False,
            'whole_geometry_decoded': False, 'cumulative_typed_import': False})

    def paired_node(self, left=0, right=1):
        assert right == left + 1
        _, groups = self.block_plan('simplices')
        a, b = groups[left], groups[right]
        assert not b[-1]['final'], 'This pilot demonstrates an interior continuation node.'
        start, end = a[0]['start'], b[-1]['end']
        before, after = a[0]['before_offset'], b[-1]['after_offset']
        short = self.tag + f'RowsNode{left:03d}To{right:03d}'
        source = f'''import ImbalancedChen.{self.tag}TypedRows{left:03d}
import ImbalancedChen.{self.tag}TypedRows{right:03d}

/-! Binary composition of two independent original cell {self.cell:02d} row leaves.
This is an interior original-parser transition and matching typed list decode;
it is not a whole-cell parser or geometry acceptance theorem. -/
namespace {self.typed_ns}.Node{left:03d}To{right:03d}
set_option maxRecDepth 1000000
set_option Elab.async false
open ImbalancedChen.P2OriginalSaving19Archive
open {self.ns}

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  SimplicesBlock{right:03d}.blockPush (SimplicesBlock{left:03d}.blockPush acc)
noncomputable def jsonRows : List SourceJson :=
  geometryRowsJsonBlock{left:03d} ++ geometryRowsJsonBlock{right:03d}
noncomputable def typedRows : List GeometryRow :=
  geometryRowsTypedBlock{left:03d} ++ geometryRowsTypedBlock{right:03d}

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + {before}) (SourceJson.white (sourceRest {start})) acc =
      SourceJson.array (fuel + {after}) (SourceJson.white (sourceRest {end})) (blockPush acc) :=
  (SimplicesBlock{left:03d}.array_block_original fuel acc).trans
    (SimplicesBlock{right:03d}.array_block_original fuel (SimplicesBlock{left:03d}.blockPush acc))

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonRows := by
  unfold blockPush jsonRows
  rw [geometry_Rows_block_{right:03d}_reverse, geometry_Rows_block_{left:03d}_reverse,
    List.append_assoc]

theorem original_rows_decode : jsonRows.mapM decodeGeometryRow = .ok typedRows := by
  simp only [jsonRows, typedRows, List.mapM_append,
    decode_geometry_Rows_block_{left:03d}, decode_geometry_Rows_block_{right:03d}]
  rfl

theorem rows_length : typedRows.length = {b[-1]['after']-a[0]['first']} := by
  simp only [typedRows, List.length_append,
    geometry_Rows_block_{left:03d}_length, geometry_Rows_block_{right:03d}_length]

#print axioms array_original
#print axioms blockPush_reverse
#print axioms original_rows_decode
#print axioms rows_length
end {self.typed_ns}.Node{left:03d}To{right:03d}
'''
        return self.save(short, source, 'Binary parser/typed assembly with bounded fan-in', {
            'rows': [a[0]['first'], b[-1]['after']], 'raw_span': [start, end],
            'children': [left, right], 'whole_geometry_decoded': False})


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--raw-root', type=Path, default=Path('/workspace/p26-original-inputs'))
    args = ap.parse_args()
    records, inputs = [], []
    for cell in [5, 12]:
        e = Engine(cell, args.raw_root)
        inputs.append({'cell': cell, 'input': fp(e.raw_origin),
                       'row_count_host_plan': len(e.fields['simplices'].value.children)})
        e.input_owner()
        count = len(e.block_plan('simplices')[1])
        blocks = [0, 1] if cell == 5 else [0, count // 2, count - 1]
        for block in blocks:
            e.array_block_owner('simplices', block)
            e.typed_leaf(block)
        if cell == 5:
            e.paired_node()
        records.extend(e.records)
    known = {row['module']: row for row in records}
    suppliers = {}
    def visit(module):
        if module in known or module in suppliers:
            return
        path = REPO / (module.replace('.', '/') + '.lean')
        text = path.read_text()
        deps = re.findall(r'(?m)^import\s+(ImbalancedChen\.\S+)', text)
        suppliers[module] = {'module': module, 'source': fp(path), 'project_imports': deps,
                             'must_reuse_accepted_object': True}
        for dep in deps:
            visit(dep)
    for row in records:
        for dep in row['project_imports']:
            visit(dep)
    manifest = {'status': 'SOURCE_ONLY_NOT_COMPILED', 'normal_kernel_owned_accepted': False,
                'generator': fp(Path(__file__)), 'inputs': inputs, 'owners': records,
                'supplier_source_registry': list(suppliers.values()),
                'owner_count': len(records), 'supplier_count': len(suppliers),
                'accepted_suppliers_recompiled': False, 'raw_parser_changed': False,
                'typed_decoder_changed': False, 'whole_cells_decoded': [],
                'P2_6_complete': False,
                'template_inputs': [fp(LEGACY / p) for p in ['generate.py', 'raw_planner.py', 'fragment_templates.py']] +
                                   [fp(HERE / p) for p in ['row_templates.py', 'quotation.py']]}
    write_new(HERE / 'SOURCE_MANIFEST.json', json.dumps(manifest, indent=2) + '\n')
    write_new(HERE / 'cloud_order.txt', '\n'.join(row['module'] for row in records) + '\n')
    print(json.dumps({'owner_count': len(records), 'supplier_count': len(suppliers),
                      'source_bytes': sum(row['source']['bytes'] for row in records),
                      'manifest': str(HERE / 'SOURCE_MANIFEST.json')}))


if __name__ == '__main__':
    main()
