#!/usr/bin/env python3
"""Locally author original cell05 top-level parse/decode connection sources."""
from pathlib import Path
import importlib.util
import json
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


fields = load('cell05_frozen_field_generator', HERE.parent / 'scalable-cell05-fields/generate_arrays.py')
full = load('cell01_frozen_top_level_template', REPO / 'docs/verification/20261125-p26/cell01-geometry-active8/generate_full.py')
base = fields.pilot.base
fp, pin, write_new = fields.fp, fields.pin, fields.write_new
TAG = fields.TAG
BATCH = 'a_parse_decode'


def frozen_prior():
    rows = {row['path']: row for row in fields.frozen_prior()}
    handoff = REPO / 'docs/verification/20261126-p26/scalable-geometry-cell05-fields/workflow-v1/HANDOFF_STAGING_FILES.txt'
    for name in handoff.read_text().splitlines():
        rows[name] = fp(REPO / name)
    return [rows[name] for name in sorted(rows)]


class ConnectionsEngine(fields.FieldsEngine):
    prior = full.FullEngine.prior
    field_header = full.FullEngine.field_header
    array_field = full.FullEngine.array_field

    def __init__(self):
        super().__init__()
        self.protected = frozen_prior()
        self.protected_sources = {Path(row['path']).stem for row in self.protected
                                  if row['path'].startswith('ImbalancedChen/')}
        self.roots = {}
        self.source_templates = [fp(Path(__file__)), fp(Path(fields.__file__)), fp(Path(full.__file__))]
        for path in sorted((HERE.parent / 'scalable-cell05-fields/batches').glob('*/SOURCE_MANIFEST.json')):
            manifest = json.loads(path.read_text())
            self.roots.update(manifest['array_roots'])
        ns = self.typed_ns + '.Node000To006'
        self.roots['simplices'] = {
            'first': 0, 'last': 6, 'module': TAG + 'RowsNode000To006',
            'push': ns + '.blockPush', 'parse': ns + '.array_original',
            'typed': True, 'typ': 'GeometryRow', 'decoder': 'decodeGeometryRow',
            'json': ns + '.jsonRows', 'values': ns + '.typedRows',
            'reverse': ns + '.blockPush_reverse', 'decode': ns + '.original_rows_decode',
            'length': ns + '.rows_length'}
        assert len(self.raw) == 201042 and self.node.end == 201040
        assert self.raw[self.node.end:] == b'\r\n'
        assert len(self.node.fields) == 14 and len(self.roots) == 7
        self.payload = json.loads(self.raw)
        assert self.payload['dimension'] == 8 and self.payload['physical_jacobian'] == 1
        assert len(self.payload['vertices']) == 28 and len(self.payload['simplices']) == 56

    def scalar_field(self):
        key = 'physical_volume'
        field, index = self.fields[key], self.field_index[key]
        prior_module, prior_acc, prior_whole = self.prior(key)
        need = 1 + max(field.key.quoted_need, field.value.need)
        actual = len(self.raw) - index
        assert field.separator == ',' and index == 12
        text = self.head([prior_module], 'Exact original physical_volume field and original comma.')
        text += f'''namespace PhysicalVolumeField

noncomputable def fieldChars : List Char := {base.chars(self.raw, field.prefix_start, field.prefix_end)}
noncomputable def fieldKey : String := String.ofList {base.quote_list(key)}
noncomputable def fieldValue : SourceJson := {base.lean_node(field.value)}
noncomputable def fieldAcc : List (String × SourceJson) := (fieldKey, fieldValue) :: {prior_acc}

theorem object_scalar (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + {need}) (SourceJson.white (fieldChars ++ tail)) {prior_acc} =
      SourceJson.object (fuel + {need-1}) (SourceJson.white tail) fieldAcc := by rfl

'''
        text += self.emit_split('field_original', field.prefix_start, field.prefix_end, 'fieldChars')
        text += f'''theorem object_original_field :
    SourceJson.object {actual} (SourceJson.white (sourceRest {field.prefix_start})) {prior_acc} =
      SourceJson.object {actual-1} (SourceJson.white (sourceRest {field.prefix_end})) fieldAcc :=
  (congrArg (fun chars => SourceJson.object {actual} (SourceJson.white chars) {prior_acc})
    field_original_split).trans (object_scalar {actual-need} (sourceRest {field.prefix_end}))

theorem sourceChars_through_field :
    SourceJson.value {len(self.raw)+1} sourceChars =
      SourceJson.object {actual-1} (SourceJson.white (sourceRest {field.prefix_end})) fieldAcc :=
  {prior_whole}.trans object_original_field

'''
        text += self.foot(['object_scalar', 'field_original_prefix', 'field_original_split',
                           'object_original_field', 'sourceChars_through_field'], 'PhysicalVolumeField')
        return self.save(TAG + 'PhysicalVolumeField', text, 'Original scalar field and exact parent-object continuation',
                         {'key': key, 'field_span': [field.prefix_start, field.prefix_end],
                          'actual_object_fuels': [actual, actual-1], 'original_scalar_preserved': True})

    def whole_value(self):
        field, index = self.fields['integral_gap'], self.field_index['integral_gap']
        need = 1 + max(field.key.quoted_need, field.value.need)
        actual = len(self.raw) - index
        assert index == 13 and field.separator == '}' and field.prefix_end == self.node.end
        text = self.head(['ImbalancedChen.' + TAG + 'PhysicalVolumeField'],
                         'Original integral_gap, closing object and complete original value equation.')
        text += f'''noncomputable def finalFieldChars : List Char := {base.chars(self.raw, field.prefix_start, field.prefix_end)}
noncomputable def finalFieldKey : String := String.ofList {base.quote_list('integral_gap')}
noncomputable def finalFieldValue : SourceJson := {base.lean_node(field.value)}
noncomputable def originalGeometryJson05 : SourceJson :=
  .obj (((finalFieldKey, finalFieldValue) :: PhysicalVolumeField.fieldAcc).reverse)

theorem object_final_field (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + {need}) (SourceJson.white (finalFieldChars ++ tail)) PhysicalVolumeField.fieldAcc =
      .ok (originalGeometryJson05, tail) := by rfl

'''
        text += self.emit_split('final_field', field.prefix_start, field.prefix_end, 'finalFieldChars')
        text += f'''theorem final_field_original :
    SourceJson.object {actual} (SourceJson.white (sourceRest {field.prefix_start})) PhysicalVolumeField.fieldAcc =
      .ok (originalGeometryJson05, sourceRest {self.node.end}) :=
  (congrArg (fun chars => SourceJson.object {actual} (SourceJson.white chars) PhysicalVolumeField.fieldAcc)
    final_field_split).trans (object_final_field {actual-need} (sourceRest {self.node.end}))

theorem sourceChars_whole_value :
    SourceJson.value {len(self.raw)+1} sourceChars =
      .ok (originalGeometryJson05, sourceRest {self.node.end}) :=
  PhysicalVolumeField.sourceChars_through_field.trans final_field_original

theorem geometryPacked05_whole_value :
    SourceJson.value {len(self.raw)+1} geometryPacked05.toList =
      .ok (originalGeometryJson05, (geometryPacked05.drop {self.node.end}).toList) :=
  sourceChars_whole_value

'''
        text += self.foot(['object_final_field', 'final_field_prefix', 'final_field_split',
                           'final_field_original', 'sourceChars_whole_value', 'geometryPacked05_whole_value'])
        return self.save(TAG + 'WholeValue', text, 'Complete actual original object value with exact CRLF remainder',
                         {'last_field_span': [field.prefix_start, field.prefix_end], 'original_fields': 14,
                          'root_end': self.node.end, 'tail_bytes': len(self.raw)-self.node.end,
                          'whole_value_success_candidate': True})

    def whole_parse(self):
        text = self.head(['ImbalancedChen.' + TAG + 'WholeValue',
                          'ImbalancedChen.P2OriginalSaving19ParseFromValue00'],
                         'Original parser success for the complete production-packed cell05, including final CRLF.')
        text += f'''noncomputable def finalTailChars : List Char := {base.chars(self.raw, self.node.end, len(self.raw))}

'''
        text += self.emit_split('final_tail', self.node.end, len(self.raw), 'finalTailChars')
        text += f'''theorem sourceRest_exact_tail : sourceRest {self.node.end} = finalTailChars :=
  final_tail_split.trans (by rw [sourceRest_end, List.append_nil])

theorem sourceRest_white_tail : SourceJson.white (sourceRest {self.node.end}) = [] :=
  (congrArg SourceJson.white sourceRest_exact_tail).trans (by rfl)

theorem sourceChars_parseChars : SourceJson.parseChars sourceChars = .ok originalGeometryJson05 := by
  apply SourceJson.parseChars_of_value_eq
  · simpa only [sourceChars_length] using sourceChars_whole_value
  · exact sourceRest_white_tail

theorem geometryPacked05_parseChars :
    SourceJson.parseChars geometryPacked05.toList = .ok originalGeometryJson05 :=
  sourceChars_parseChars

theorem geometryPacked05_original_parse :
    SourceJson.parse (String.ofList geometryPacked05.toList) = .ok originalGeometryJson05 :=
  (SourceJson.parse_ofList sourceChars).trans sourceChars_parseChars

'''
        text += self.foot(['final_tail_prefix', 'final_tail_split', 'sourceRest_exact_tail',
                           'sourceRest_white_tail', 'sourceChars_parseChars', 'geometryPacked05_parseChars',
                           'geometryPacked05_original_parse'])
        return self.save(TAG + 'WholeParse', text, 'Original complete packed-input parser success',
                         {'input_bytes': len(self.raw), 'final_tail': 'CRLF', 'original_fields': 14,
                          'whole_parse_success_candidate': True, 'typed_decode_in_separate_owner': True})

    def decode_fields(self):
        template = REPO / 'ImbalancedChen/P2OriginalSaving19Geometry01DirectDecodeFields.lean'
        self.source_templates.append(fp(template))
        text = template.read_text()
        old_arrays = [
            ('VerticesValue.arrayAcc003.reverse', 'vertices'),
            ('VertexValuesValue.arrayAcc005.reverse', 'vertex_values'),
            ('SimplicesValue.arrayAcc073.reverse', 'simplices'),
            ('FacetVerticesValue.arrayAcc001.reverse', 'facet_vertices'),
            ('FaceLedgerValue.arrayAcc020.reverse', 'face_ledger')]
        for old, key in old_arrays:
            assert text.count(old) == 1
            text = text.replace(old, self.roots[key]['json'])
        text = text.replace('Geometry01Direct', 'Geometry05Scalable')
        text = text.replace('originalGeometryJson01', 'originalGeometryJson05').replace('cell01', 'cell05')
        indices = self.payload['facet_original_indices']
        assert len(indices) == 11
        text, n = re.subn(r'(noncomputable def geometryDecodedFacetOriginalIndices : Array Nat := )[^\n]+',
                          lambda match: match[1] + '#[' + ', '.join(map(str, indices)) + ']', text)
        assert n == 1
        text, n = re.subn(r'  change SourceJson.Decode.read \(α := Array Nat\) .* = \.ok geometryDecodedFacetOriginalIndices',
                          lambda _: '  change SourceJson.Decode.read (α := Array Nat) (' +
                          base.lean_node(self.fields['facet_original_indices'].value) +
                          ') = .ok geometryDecodedFacetOriginalIndices', text)
        assert n == 1 and 'Geometry01' not in text and 'arrayAcc' not in text
        return self.save(TAG + 'DecodeFields', text, 'Original decoder getters and symbolic five-array composition',
                         {'metadata_dimension': 8, 'metadata_physical_jacobian': 1,
                          'facet_original_indices': indices, 'original_fields_preserved': 14,
                          'original_decoder_definition_changed': False,
                          'symbolic_lemma_requires_all_five_array_decode_equations': True})

    def decoded(self):
        keys = ['vertices', 'vertex_values', 'simplices', 'facet_vertices', 'face_ledger']
        imports = ['ImbalancedChen.' + TAG + suffix for suffix in ['DecodeFields', 'WholeParse']]
        imports += ['ImbalancedChen.' + self.roots[key]['module'] for key in keys]
        jsons = ' '.join(self.roots[key]['json'] for key in keys)
        arrays = ' '.join(self.roots[key]['values'] + '.toArray' for key in keys)
        proofs = '\n'.join('      (mapM_array_of_list_ok ' + self.roots[key]['decoder'] + ' ' +
                           self.roots[key]['json'] + '\n        ' + self.roots[key]['values'] + ' ' +
                           self.roots[key]['decode'] + ')' for key in keys)
        text = ''.join('import ' + module + '\n' for module in imports)
        text += f'''
/-! Complete original cell05 parsing and the actual original Geometry decoder.
This candidate uses exactly the original parser-bound typed array networks.
No geometric interpretation, integral equality or full P2.6 completion is claimed. -/
namespace {self.typed_ns}.Complete
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open {self.ns}
open {self.typed_ns}

noncomputable def concreteGeometry05 : Geometry :=
  geometryWithDecodedArrays {arrays}

theorem decode_originalGeometryJson05 :
    decodeGeometry originalGeometryJson05 = .ok concreteGeometry05 :=
  (congrArg decodeGeometry originalGeometryJson05_eq_object).trans
    (decodeGeometry_of_array_decodes {jsons}
      {arrays}
{proofs})

theorem geometryPacked05_parse_decode :
    (SourceJson.parse (String.ofList geometryPacked05.toList) >>= decodeGeometry) =
      .ok concreteGeometry05 :=
  geometry_parse_decode_of_equalities (String.ofList geometryPacked05.toList)
    originalGeometryJson05 concreteGeometry05 geometryPacked05_original_parse decode_originalGeometryJson05

#print axioms decode_originalGeometryJson05
#print axioms geometryPacked05_parse_decode

end {self.typed_ns}.Complete
'''
        return self.save(TAG + 'Decoded', text, 'Actual original packed input parsed and decoded to concrete Geometry05',
                         {'whole_parse_decode_candidate': True, 'original_input_bytes': len(self.raw),
                          'vertices': 28, 'rows': 56, 'facet_indices': 11, 'facets': 11, 'faces': 45,
                          'five_typed_roots': {key: self.roots[key] for key in keys},
                          'geometry_or_integral_semantics_claimed': False})


def main():
    engine = ConnectionsEngine()
    engine.array_value('simplices', engine.roots['simplices'])
    for field in engine.node.fields[5:12]:
        assert field.value.kind == 'arr'
        engine.field_header(field.key.scalar)
        engine.array_field(field.key.scalar)
    engine.scalar_field()
    engine.whole_value()
    engine.whole_parse()
    engine.decode_fields()
    engine.decoded()
    assert len(engine.records) == 20
    assert frozen_prior() == engine.protected
    manifest = {
        'schema': 'cell05_connections_source_candidates_v1', 'batch': BATCH,
        'status': 'SOURCE_ONLY_NOT_COMPILED', 'owners': engine.records, 'owner_count': len(engine.records),
        'generator': fp(Path(__file__)), 'source_templates': engine.source_templates,
        'original_input': fp(engine.raw_origin), 'original_input_bytes': len(engine.raw),
        'original_field_order': [field.key.scalar for field in engine.node.fields],
        'root_end': engine.node.end, 'final_tail_bytes': len(engine.raw)-engine.node.end,
        'vertices_host_plan': 28, 'rows_host_plan': 56, 'array_roots': engine.roots,
        'protected_previous_files': engine.protected,
        'raw_parser_changed': False, 'typed_decoder_changed': False,
        'normal_kernel_owned_accepted': False, 'whole_geometry_decoded_accepted': False,
        'geometry_or_integral_semantics_claimed': False, 'P2_6_complete': False}
    batch = HERE / 'batches' / BATCH
    write_new(batch / 'SOURCE_MANIFEST.json', manifest)
    write_new(batch / 'owner_order.txt', ''.join(row['module'] + '\n' for row in engine.records))
    print(json.dumps({'batch': BATCH, 'status': manifest['status'], 'new_owners': len(engine.records),
                      'source_bytes': sum(row['source']['bytes'] for row in engine.records),
                      'previous_checkpoint_files_unchanged': len(engine.protected), 'new_Lean_steps_run': 0}))


if __name__ == '__main__':
    main()
