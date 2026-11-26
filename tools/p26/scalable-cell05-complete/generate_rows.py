#!/usr/bin/env python3
"""Local-only reconstruction of the remaining five cell05 row leaves and tree."""
from pathlib import Path
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
spec = importlib.util.spec_from_file_location('published_scalable_pilot', HERE.parent / 'scalable/generate_pilot.py')
pilot = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pilot)
from prepare_baseline import fp, protected_files, write_new

TAG = 'P2OriginalSaving19Geometry05Scalable'
NODES = [(2, 2, 3, 3), (4, 4, 5, 5), (0, 1, 2, 3), (4, 5, 6, 6), (0, 3, 4, 6)]
SHORTS = [TAG + kind + f'{index:03d}' for index in range(2, 7) for kind in ('SimplicesBlock', 'TypedRows')]
SHORTS += [TAG + f'RowsNode{a:03d}To{d:03d}' for a, b, c, d in NODES]


class CompleteRows(pilot.Engine):
    def save(self, short, text, scope, plan):
        assert short in SHORTS, ('Attempt to modify a published owner', short)
        return super().save(short, text, scope, plan)

    def child(self, first, last):
        if first == last:
            return dict(module=TAG + f'TypedRows{first:03d}',
                        push=f'SimplicesBlock{first:03d}.blockPush',
                        json=f'geometryRowsJsonBlock{first:03d}', typed=f'geometryRowsTypedBlock{first:03d}',
                        parse=f'SimplicesBlock{first:03d}.array_block_original',
                        reverse=f'geometry_Rows_block_{first:03d}_reverse',
                        decode=f'decode_geometry_Rows_block_{first:03d}',
                        length=f'geometry_Rows_block_{first:03d}_length')
        node = f'Node{first:03d}To{last:03d}'
        return dict(module=TAG + f'Rows{node}', push=node + '.blockPush', json=node + '.jsonRows',
                    typed=node + '.typedRows', parse=node + '.array_original',
                    reverse=node + '.blockPush_reverse', decode=node + '.original_rows_decode',
                    length=node + '.rows_length')

    def assembly_node(self, a, b, c, d):
        assert b + 1 == c
        _, groups = self.block_plan('simplices')
        left, right = self.child(a, b), self.child(c, d)
        first, last = groups[a][0], groups[d][-1]
        terminal = last['final']
        short = TAG + f'RowsNode{a:03d}To{d:03d}'
        result = (f'.ok (.arr ((blockPush acc).reverse), sourceRest {last["end"]})' if terminal else
                  f'SourceJson.array (fuel + {last["after_offset"]}) (SourceJson.white (sourceRest {last["end"]})) (blockPush acc)')
        text = f'''import ImbalancedChen.{left['module']}
import ImbalancedChen.{right['module']}

/-! Balanced original cell 05 row parser and typed-list composition.
Only the original simplices array is assembled here; whole geometry decoding
and all geometric or integral claims remain outside this owner. -/
namespace {self.typed_ns}.Node{a:03d}To{d:03d}
set_option maxRecDepth 1000000
set_option Elab.async false
open ImbalancedChen.P2OriginalSaving19Archive
open {self.ns}

noncomputable def blockPush (acc : List SourceJson) : List SourceJson :=
  {right['push']} ({left['push']} acc)
noncomputable def jsonRows : List SourceJson := {left['json']} ++ {right['json']}
noncomputable def typedRows : List GeometryRow := {left['typed']} ++ {right['typed']}

theorem array_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + {first['before_offset']}) (SourceJson.white (sourceRest {first['start']})) acc =
      {result} :=
  ({left['parse']} fuel acc).trans
    ({right['parse']} fuel ({left['push']} acc))

theorem blockPush_reverse (acc : List SourceJson) :
    (blockPush acc).reverse = acc.reverse ++ jsonRows := by
  unfold blockPush jsonRows
  rw [{right['reverse']}, {left['reverse']}, List.append_assoc]

theorem original_rows_decode : jsonRows.mapM decodeGeometryRow = .ok typedRows := by
  simp only [jsonRows, typedRows, List.mapM_append, {left['decode']}, {right['decode']}]
  rfl

theorem rows_length : typedRows.length = {last['after']-first['first']} := by
  simp only [typedRows, List.length_append, {left['length']}, {right['length']}]

'''
        names = ['array_original', 'blockPush_reverse', 'original_rows_decode', 'rows_length']
        if terminal:
            text += f'''theorem array_empty_original (fuel : Nat) :
    SourceJson.array (fuel + {first['before_offset']}) (SourceJson.white (sourceRest {first['start']})) [] =
      .ok (.arr jsonRows, sourceRest {last['end']}) := by
  rw [array_original, blockPush_reverse, List.reverse_nil, List.nil_append]

'''
            names.append('array_empty_original')
        text += '\n'.join('#print axioms ' + name for name in names) + f'\nend {self.typed_ns}.Node{a:03d}To{d:03d}\n'
        return self.save(short, text, 'Balanced original row parser/typed assembly', {
            'rows': [first['first'], last['after']], 'raw_span': [first['start'], last['end']],
            'children': [[a, b], [c, d]], 'original_array_terminator_consumed': terminal,
            'whole_geometry_decoded': False})


def main():
    protected = protected_files()
    raw_root = HERE / 'baseline/raw05-history/original-input'
    e = CompleteRows(5, raw_root)
    assert len(e.raw) == 201042
    assert len(e.fields['vertices'].value.children) == 28
    assert len(e.fields['simplices'].value.children) == 56
    assert len(e.block_plan('simplices')[1]) == 7
    for index in range(2, 7):
        e.array_block_owner('simplices', index)
        e.typed_leaf(index)
    for node in NODES:
        e.assembly_node(*node)
    assert [row['module'].split('.')[-1] for row in e.records] == SHORTS
    manifest = {
        'schema': 'cell05_row_network_recovered_candidate_v2', 'status': 'SOURCE_ONLY_NOT_COMPILED',
        'lost_unpublished_v1_archive': {'bytes': 299364, 'sha256': '8e583044f314355106423bb4c3d382d905f500896e137868d75aebd90ed1925f'},
        'byte_identity_with_lost_v1_claimed': False, 'candidate_sources_newly_frozen_after_recovery': True,
        'generator': fp(Path(__file__)), 'input': fp(e.raw_origin), 'input_bytes': 201042,
        'vertex_count_host_plan': 28, 'row_count_host_plan': 56, 'new_row_interval': [16, 56],
        'owners': e.records, 'owner_count': 15, 'published_files': protected,
        'normal_kernel_owned_accepted': False, 'old_owners_recompiled': False,
        'raw_parser_changed': False, 'typed_decoder_changed': False, 'whole_geometry_decoded': False,
        'P2_6_complete': False,
    }
    write_new(HERE / 'ROW_NETWORK_SOURCE_MANIFEST.json', manifest)
    write_new(HERE / 'row_network_order.txt', ''.join(row['module'] + '\n' for row in e.records))
    docs = REPO / 'docs/verification/20261126-p26/scalable-geometry-cell05-complete'
    inventory = [{'key': f.key.scalar, 'prefix_start': f.prefix_start, 'value_start': f.value.start,
                  'value_end': f.value.end, 'prefix_end': f.prefix_end,
                  'children': len(f.value.children), 'need': f.value.need}
                 for f in e.node.fields]
    write_new(docs / 'ORIGINAL_FIELD_INVENTORY.json', {'status': 'HOST_PLAN_NOT_LEAN_PROOF',
              'input': fp(e.raw_origin), 'root_end': e.node.end, 'trailing_bytes': len(e.raw)-e.node.end,
              'fields': inventory, 'whole_geometry_decoded': False})
    assert protected_files() == protected
    print(json.dumps({'status': 'SOURCE_ONLY_NOT_COMPILED', 'new_owners': 15,
                      'source_bytes': sum(row['source']['bytes'] for row in e.records),
                      'old_70_files_unchanged': True, 'new_Lean_steps': 0}))


if __name__ == '__main__':
    main()
