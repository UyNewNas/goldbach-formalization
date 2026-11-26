#!/usr/bin/env python3
"""Local-only cell05 field candidates using original bounded parser fragments."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
spec = importlib.util.spec_from_file_location('published_cell05_scalable', HERE.parent / 'scalable/generate_pilot.py')
pilot = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pilot)
from quotation import record_value

TAG = 'P2OriginalSaving19Geometry05Scalable'
ARRAY_KEYS = ['active8_enumeration', 'vertices', 'vertex_values',
              'all_original_constraint_minima', 'facet_vertices', 'face_ledger']
TYPED = {
    'vertices': ('Vertices', 'Array ℚ', 'rationalArray'),
    'vertex_values': ('VertexValues', 'VertexValues', 'decodeVertexValues'),
    'facet_vertices': ('FacetVertices', 'Array Nat', '(SourceJson.Decode.read (α := Array Nat))'),
    'face_ledger': ('Faces', 'FaceRecord', 'decodeFace'),
}
BATCHES = {
    'a_vertices_facets': ['vertices', 'facet_vertices'],
    'b_active8': ['active8_enumeration'],
    'c_values_faces': ['vertex_values', 'face_ledger'],
    'd_minima': ['all_original_constraint_minima'],
}


def pin(path):
    data = Path(path).read_bytes()
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def fp(path):
    path = Path(path)
    return {'path': str(path.relative_to(REPO)), **pin(path)}


def write_new(path, value):
    path = Path(path)
    data = value if isinstance(value, bytes) else value.encode() if isinstance(value, str) else (json.dumps(value, indent=2) + '\n').encode()
    if path.exists():
        assert path.read_bytes() == data, ('Frozen phase2 source drift', str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('xb') as out:
            out.write(data)


def frozen_prior():
    docs = REPO / 'docs/verification/20261126-p26'
    names = set((docs / 'scalable-geometry-cell05/HANDOFF_STAGING_FILES.txt').read_text().splitlines())
    names.update((docs / 'scalable-geometry-cell05-complete/HANDOFF_STAGING_FILES_V3.txt').read_text().splitlines())
    return [fp(REPO / name) for name in sorted(names)]


class FieldsEngine(pilot.Engine):
    def __init__(self):
        super().__init__(5, HERE.parent / 'scalable-cell05-complete/baseline/raw05-history/original-input')
        self.field_index = {field.key.scalar: index for index, field in enumerate(self.node.fields)}
        self.protected = frozen_prior()
        self.protected_sources = {Path(row['path']).stem for row in self.protected if row['path'].startswith('ImbalancedChen/')}
        self.array_roots = {}

    def save(self, short, text, scope, plan):
        assert short.startswith(TAG) and short not in self.protected_sources, ('Protected owner write', short)
        return super().save(short, text, scope, plan)

    def head(self, imports, description):
        return ''.join('import ' + module + '\n' for module in imports) + f'''
/-! {description}
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace {self.ns}
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

'''

    def block_plan(self, key):
        assert key in ARRAY_KEYS
        node = self.fields[key].value
        chunks = self.chunks_for(node, max_items=2, max_bytes=768)
        groups, group = [], []
        for chunk in chunks:
            if group and (len(group) == 8 or chunk['end'] - group[0]['start'] > 65536):
                groups.append(group)
                group = []
            group.append(chunk)
        if group:
            groups.append(group)
        return node, groups

    @staticmethod
    def field_tag(key):
        return ''.join(word.title() for word in key.split('_'))

    def typed_leaf(self, key, block):
        item_tag, typ, decoder = TYPED[key]
        parser_tag = self.field_tag(key)
        node, groups = self.block_plan(key)
        group = groups[block]
        first, after = group[0]['first'], group[-1]['after']
        short = TAG + f'Typed{item_tag}{block:03d}'
        parser = parser_tag + f'Block{block:03d}'
        text = f'''import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.{TAG}{parser}

/-! Local original {key} decoding, indices {first} through {after-1}.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace {self.typed_ns}
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open {self.ns}
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

'''
        names, raw_names, typed_names = [], [], []
        for index in range(first, after):
            raw = f'geometry{item_tag}Json{index:03d}'
            typed = f'geometry{item_tag}Typed{index:03d}'
            decode = f'decode_geometry_{item_tag}_{index:03d}'
            shape = f'geometry{item_tag}_{index:03d}_shape'
            child = node.children[index]
            raw_names.append(raw)
            typed_names.append(typed)
            text += f'''noncomputable def {raw} : SourceJson :=
  ({parser}.blockPush []).get ⟨{after-index-1}, by decide +kernel⟩

noncomputable def {typed} : {typ} :=
  {record_value(key, child)}

theorem {decode} : {decoder} {raw} = .ok {typed} := by decide +kernel

'''
            if key == 'vertices':
                assert len(child.children) == 8
                proposition = f'{typed}.size = 8'
            elif key == 'vertex_values':
                fields = {field.key.scalar: field.value for field in child.fields}
                assert len(fields['factors'].children) == 10
                proposition = f'{typed}.factors.size = 10'
            elif key == 'facet_vertices':
                ids = [int(item.scalar) for item in child.children]
                assert len(set(ids)) == len(ids) and all(0 <= value < 28 for value in ids)
                proposition = (f'{typed}.size = {len(ids)} ∧ {typed}.toList.Nodup ∧\n'
                               f'    (∀ i : Fin {len(ids)}, {typed}[i.val]! < 28)')
            else:
                fields = {field.key.scalar: field.value for field in child.fields}
                ids = [int(item.scalar) for item in fields['vertices'].children]
                assert len(set(ids)) == len(ids) and all(0 <= value < 28 for value in ids)
                assert 0 <= int(fields['pivot'].scalar) < 28 and int(fields['dimension'].scalar) <= 8
                proposition = (f'{typed}.vertices.size = {len(ids)} ∧ {typed}.vertices.toList.Nodup ∧\n'
                               f'    (∀ i : Fin {len(ids)}, {typed}.vertices[i.val]! < 28) ∧\n'
                               f'    {typed}.pivot < 28 ∧ {typed}.dimension ≤ 8')
            text += f'theorem {shape} : {proposition} := by decide +kernel\n\n'
            names.extend([decode, shape])
        raw_block = f'geometry{item_tag}JsonBlock{block:03d}'
        typed_block = f'geometry{item_tag}TypedBlock{block:03d}'
        push = f'geometry_{item_tag}_block_{block:03d}_push_eq'
        reverse = f'geometry_{item_tag}_block_{block:03d}_reverse'
        decode = f'decode_geometry_{item_tag}_block_{block:03d}'
        length = f'geometry_{item_tag}_block_{block:03d}_length'
        text += f'''noncomputable def {raw_block} : List SourceJson := [{', '.join(raw_names)}]
noncomputable def {typed_block} : List ({typ}) := [{', '.join(typed_names)}]

theorem {push} (acc : List SourceJson) :
    {parser}.blockPush acc = [{', '.join(reversed(raw_names))}] ++ acc := by rfl

theorem {reverse} (acc : List SourceJson) :
    ({parser}.blockPush acc).reverse = acc.reverse ++ {raw_block} := by
  rw [{push}, List.reverse_append]
  rfl

theorem {decode} : {raw_block}.mapM {decoder} = .ok {typed_block} := by
  simp only [{raw_block}, {typed_block}, List.mapM_cons, List.mapM_nil,
    {', '.join(f'decode_geometry_{item_tag}_{index:03d}' for index in range(first, after))}]
  rfl

theorem {length} : {typed_block}.length = {after-first} := by rfl

'''
        names.extend([push, reverse, decode, length])
        text += '\n'.join('#print axioms ' + name for name in names) + f'\nend {self.typed_ns}\n'
        return self.save(short, text, 'Independent typed leaf and finite literal shape facts', {
            'key': key, 'indices': [first, after], 'matching_parser': 'ImbalancedChen.' + TAG + parser,
            'raw_span': [group[0]['start'], group[-1]['end']], 'literal_vertex_bound': 28,
            'vertex_array_decode_count_binding_claimed': False, 'whole_geometry_decoded': False,
            'cumulative_typed_import': False})

    def leaf(self, key, index):
        parser_tag = self.field_tag(key)
        prefix = f'{self.ns}.{parser_tag}Block{index:03d}'
        result = {'first': index, 'last': index, 'module': TAG + f'{parser_tag}Block{index:03d}',
                  'push': prefix + '.blockPush', 'parse': prefix + '.array_block_original', 'typed': key in TYPED}
        if key in TYPED:
            item_tag, typ, decoder = TYPED[key]
            result.update(module=TAG + f'Typed{item_tag}{index:03d}', typ=typ, decoder=decoder,
                          json=f'{self.typed_ns}.geometry{item_tag}JsonBlock{index:03d}',
                          values=f'{self.typed_ns}.geometry{item_tag}TypedBlock{index:03d}',
                          reverse=f'{self.typed_ns}.geometry_{item_tag}_block_{index:03d}_reverse',
                          decode=f'{self.typed_ns}.decode_geometry_{item_tag}_block_{index:03d}',
                          length=f'{self.typed_ns}.geometry_{item_tag}_block_{index:03d}_length')
        return result

    def node_owner(self, key, left, right):
        assert left['last'] + 1 == right['first']
        _, groups = self.block_plan(key)
        a, b = left['first'], right['last']
        first, last = groups[a][0], groups[b][-1]
        nested = self.field_tag(key) + f'Node{a:03d}To{b:03d}'
        ns = self.typed_ns if key in TYPED else self.ns
        result = (f'.ok (.arr ((blockPush acc).reverse), sourceRest {last["end"]})' if last['final'] else
                  f'SourceJson.array (fuel + {last["after_offset"]}) (SourceJson.white (sourceRest {last["end"]})) (blockPush acc)')
        text = f'''import ImbalancedChen.{left['module']}
import ImbalancedChen.{right['module']}

/-! Balanced original {key} composition, leaf interval {a} through {b}. -/
namespace {ns}.{nested}
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open {self.ns}

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  {right['push']} ({left['push']} acc)

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + {first['before_offset']}) (SourceJson.white (sourceRest {first['start']})) acc =
      {result} :=
  ({left['parse']} fuel acc).trans
    ({right['parse']} fuel ({left['push']} acc))

'''
        names = ['array_original']
        child = {'first': a, 'last': b, 'module': TAG + nested,
                 'push': f'{ns}.{nested}.blockPush', 'parse': f'{ns}.{nested}.array_original', 'typed': key in TYPED}
        if key in TYPED:
            _, typ, decoder = TYPED[key]
            text += f'''noncomputable def jsonItems : List SourceJson := {left['json']} ++ {right['json']}
noncomputable def typedItems : List ({typ}) := {left['values']} ++ {right['values']}

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonItems := by
  unfold blockPush jsonItems
  rw [{right['reverse']}, {left['reverse']}, List.append_assoc]

theorem original_items_decode : jsonItems.mapM {decoder} = .ok typedItems := by
  simp only [jsonItems, typedItems, List.mapM_append, {left['decode']}, {right['decode']}]
  rfl

theorem items_length : typedItems.length = {last['after']-first['first']} := by
  simp only [typedItems, List.length_append, {left['length']}, {right['length']}]

'''
            names += ['blockPush_reverse', 'original_items_decode', 'items_length']
            child.update(typ=typ, decoder=decoder, json=f'{ns}.{nested}.jsonItems',
                         values=f'{ns}.{nested}.typedItems', reverse=f'{ns}.{nested}.blockPush_reverse',
                         decode=f'{ns}.{nested}.original_items_decode', length=f'{ns}.{nested}.items_length')
        text += '\n'.join('#print axioms ' + name for name in names) + f'\nend {ns}.{nested}\n'
        self.save(TAG + nested, text, 'Balanced original parser and optional typed composition', {
            'key': key, 'indices': [first['first'], last['after']], 'raw_span': [first['start'], last['end']],
            'children': [[left['first'], left['last']], [right['first'], right['last']]],
            'typed_decode_composed': key in TYPED, 'original_array_terminator_consumed': last['final'],
            'whole_geometry_decoded': False})
        return child

    def balanced_root(self, key):
        _, groups = self.block_plan(key)

        def build(first, last):
            if first == last:
                return self.leaf(key, first)
            middle = (first + last) // 2
            return self.node_owner(key, build(first, middle), build(middle + 1, last))

        root = build(0, len(groups) - 1)
        self.array_roots[key] = root
        return root

    def array_value(self, key, root):
        node = self.fields[key].value
        nested = self.field_tag(key) + 'Value'
        value = f'.arr ({root["json"]})' if root['typed'] else f'.arr (({root["push"]} []).reverse)'
        text = self.head(['ImbalancedChen.' + root['module']], f'Complete original {key} array value from a balanced tree.')
        text += f'''namespace {nested}

noncomputable def arrayOpenChars : List Char := ['[']
noncomputable def arrayValue : SourceJson := {value}

'''
        text += self.emit_split('array_open', node.start, node.start + 1, 'arrayOpenChars')
        proof = (f'''by
  simpa only [arrayValue, {root['reverse']}, List.reverse_nil, List.nil_append]
    using ({root['parse']} fuel [])''' if root['typed'] else root['parse'] + ' fuel []')
        text += f'''theorem value_array_open (fuel : Nat) :
    SourceJson.value (fuel + {node.need}) (sourceRest {node.start}) =
      SourceJson.array (fuel + {node.need-1}) (SourceJson.white (sourceRest {node.start+1})) [] :=
  (congrArg (SourceJson.value (fuel + {node.need})) array_open_split).trans (by rfl)

theorem array_all_blocks (fuel : Nat) :
    SourceJson.array (fuel + {node.need-1}) (SourceJson.white (sourceRest {node.start+1})) [] =
      .ok (arrayValue, sourceRest {node.end}) := {proof}

theorem value_array_original (fuel : Nat) :
    SourceJson.value (fuel + {node.need}) (sourceRest {node.start}) =
      .ok (arrayValue, sourceRest {node.end}) :=
  (value_array_open fuel).trans (array_all_blocks fuel)

'''
        text += self.foot(['array_open_prefix', 'array_open_split', 'value_array_open', 'array_all_blocks', 'value_array_original'], nested)
        return self.save(TAG + nested, text, 'Original array value with exact unchanged remainder', {
            'key': key, 'array_span': [node.start, node.end], 'items': len(node.children),
            'root': root, 'whole_geometry_decoded': False})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--batch', choices=list(BATCHES), required=True)
    args = parser.parse_args()
    engine = FieldsEngine()
    if args.batch == 'a_vertices_facets':
        engine.metadata_owner(5)
    for key in BATCHES[args.batch]:
        _, groups = engine.block_plan(key)
        for index in range(len(groups)):
            engine.array_block_owner(key, index)
            if key in TYPED:
                engine.typed_leaf(key, index)
        engine.array_value(key, engine.balanced_root(key))
    assert frozen_prior() == engine.protected
    counts = {'a_vertices_facets': 10, 'b_active8': 22, 'c_values_faces': 27, 'd_minima': 14}
    assert len(engine.records) == counts[args.batch]
    manifest = {'schema': 'cell05_fields_source_candidates_v1', 'batch': args.batch,
                'status': 'SOURCE_ONLY_NOT_COMPILED', 'owners': engine.records, 'owner_count': len(engine.records),
                'generator': fp(Path(__file__)), 'original_input': fp(engine.raw_origin),
                'original_input_bytes': 201042, 'vertices_host_plan': 28, 'rows_host_plan': 56,
                'array_roots': engine.array_roots, 'protected_previous_files': engine.protected,
                'raw_parser_changed': False, 'typed_decoder_changed': False,
                'normal_kernel_owned_accepted': False, 'whole_geometry_decoded': False,
                'geometry_or_integral_semantics_claimed': False, 'P2_6_complete': False}
    write_new(HERE / 'batches' / args.batch / 'SOURCE_MANIFEST.json', manifest)
    write_new(HERE / 'batches' / args.batch / 'owner_order.txt', ''.join(row['module'] + '\n' for row in engine.records))
    print(json.dumps({'batch': args.batch, 'status': manifest['status'], 'new_owners': len(engine.records),
                      'source_bytes': sum(row['source']['bytes'] for row in engine.records),
                      'previous_checkpoint_files_unchanged': len(engine.protected), 'new_Lean_steps': 0}))


if __name__ == '__main__':
    main()
