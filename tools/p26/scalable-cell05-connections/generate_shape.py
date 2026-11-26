#!/usr/bin/env python3
"""Author finite-shape transport to the actual original cell05 decoder output."""
from pathlib import Path
import json
import sys

sys.dont_write_bytecode = True
from generate_connections import ConnectionsEngine, HERE, REPO, TAG, fields, fp, write_new
from generate_connections import frozen_prior as frozen_row_and_fields

BATCH = 'b_finite_shape'
TYPED_NS = 'ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding'
SHAPE_NS = 'ImbalancedChen.P2OriginalSaving19Geometry05ScalableShape'
ROW_NODES = [(0, 0, 1, 1), (2, 2, 3, 3), (4, 4, 5, 5), (0, 1, 2, 3),
             (4, 5, 6, 6), (0, 3, 4, 6)]


def frozen_prior():
    rows = {row['path']: row for row in frozen_row_and_fields()}
    handoff = REPO / 'docs/verification/20261126-p26/scalable-geometry-cell05-connections/a_parse_decode/HANDOFF_STAGING_FILES.txt'
    for name in handoff.read_text().splitlines():
        rows[name] = fp(REPO / name)
    return [rows[name] for name in sorted(rows)]


def row_list(first, last):
    if first == last:
        return f'geometryRowsTypedBlock{first:03d}'
    return f'Node{first:03d}To{last:03d}.typedRows'


def row_fact(first, last):
    return f'rows_{first:03d}_to_{last:03d}_shape'


def membership_proof(block, witnesses):
    assert witnesses
    return ('by\n  intro item hitem\n'
            f'  simp only [{block}, List.mem_cons, List.not_mem_nil, or_false] at hitem\n'
            '  rcases hitem with ' + ' | '.join('rfl' for _ in witnesses) + '\n' +
            ''.join('  · exact ' + witness + '\n' for witness in witnesses))


class ShapeEngine(ConnectionsEngine):
    def __init__(self):
        super().__init__()
        self.protected = frozen_prior()
        self.protected_sources = {Path(row['path']).stem for row in self.protected
                                  if row['path'].startswith('ImbalancedChen/')}
        self.required_local_shape = []
        self.field_manifest = json.loads((HERE.parent / 'scalable-cell05-fields/FIELDS_SOURCE_MANIFEST.json').read_text())

    def header(self, imports, namespace, description):
        return ''.join('import ' + module + '\n' for module in imports) + f'''
/-! {description}
All input lists come from the original parser-bound typed leaf networks.
This source-only candidate has no geometric or integral interpretation. -/
namespace {SHAPE_NS}{namespace}
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open {TYPED_NS}

'''

    def footer(self, namespace, names):
        return '\n'.join('#print axioms ' + name for name in names) + f'\nend {SHAPE_NS}{namespace}\n'

    def row_shapes(self):
        text = self.header(['ImbalancedChen.' + TAG + 'RowsNode000To006'], '.Rows',
                           'Finite shape for all 56 original typed rows, by existing local facts and balanced membership.')
        text += '''def RowShape (vertexCount : Nat) (row : GeometryRow) : Prop :=
  row.vertexIds.size = 9 ∧ row.vertexIds.toList.Nodup ∧
  (∀ i : Fin 9, row.vertexIds[i.val]! < vertexCount) ∧
  row.factorMaxima.size = 10 ∧ row.gapWeightedMeans.size = 10

'''
        names = []
        for block in range(7):
            name = row_fact(block, block)
            value = row_list(block, block)
            witnesses = []
            for index in range(block * 8, (block + 1) * 8):
                local = f'geometryRow{index:03d}_shape'
                self.required_local_shape.append(TYPED_NS + '.' + local)
                witnesses.append(local + '.2')
                assert self.payload['simplices'][index]['simplex_id'] == index
            text += f'theorem {name} : ∀ row ∈ {value}, RowShape 28 row := '
            text += membership_proof(value, witnesses) + '\n'
            names.append(name)
        for a, b, c, d in ROW_NODES:
            name = row_fact(a, d)
            text += f'''theorem {name} : ∀ row ∈ {row_list(a,d)}, RowShape 28 row := by
  intro row hrow
  change row ∈ {row_list(a,b)} ++ {row_list(c,d)} at hrow
  exact (List.mem_append.mp hrow).elim ({row_fact(a,b)} row) ({row_fact(c,d)} row)

'''
            names.append(name)
        for block in range(7):
            first = block * 8
            name = f'row_identifiers_block_{block:03d}'
            text += f'''theorem {name} : ∀ r : Fin 8,
    (Node000To006.typedRows.toArray[{first} + r.val]!).simplexId = {first} + r.val := by
  decide +kernel

'''
            names.append(name)
        text += '''theorem all_row_identifiers : ∀ r : Fin 56,
    (Node000To006.typedRows.toArray[r.val]!).simplexId = r.val := by
  intro r
  have hr := r.isLt
'''
        indent = '  '
        for block in range(6):
            first = block * 8
            text += indent + f'by_cases h{block} : r.val < {first+8}\n'
            if block == 0:
                text += indent + '· simpa only [Nat.zero_add] using row_identifiers_block_000 ⟨r.val, h0⟩\n'
            else:
                text += indent + f'· have hb : r.val - {first} < 8 := by omega\n'
                text += indent + f'  have he : {first} + (r.val - {first}) = r.val := by omega\n'
                text += indent + f'  simpa only [he] using row_identifiers_block_{block:03d} ⟨r.val - {first}, hb⟩\n'
            text += indent + '·\n'
            indent += '  '
        text += indent + 'have hb : r.val - 48 < 8 := by omega\n'
        text += indent + 'have he : 48 + (r.val - 48) = r.val := by omega\n'
        text += indent + 'simpa only [he] using row_identifiers_block_006 ⟨r.val - 48, hb⟩\n\n'
        names.append('all_row_identifiers')
        text += self.footer('.Rows', names)
        return self.save(TAG + 'ShapeRows', text, 'Original row-local shape transported through the balanced 56-row list',
                         {'rows': 56, 'existing_local_shape_facts_reused': 56, 'balanced_membership_nodes': 6,
                          'new_identifier_projection_blocks': 7, 'identifier_checks_per_block': 8,
                          'new_full_record_decisions': 0, 'row_bound': 28})

    def array_value_name(self, key, first, last):
        tag = fields.TYPED[key][0]
        if first == last:
            return f'geometry{tag}TypedBlock{first:03d}'
        return f'{self.field_tag(key)}Node{first:03d}To{last:03d}.typedItems'

    def array_fact(self, key, first, last):
        return f'{key}_{first:03d}_to_{last:03d}_shape'

    def array_shapes(self):
        keys = ['vertices', 'vertex_values', 'facet_vertices', 'face_ledger']
        imports = ['ImbalancedChen.' + self.roots[key]['module'] for key in keys]
        text = self.header(imports, '.Arrays',
                           'Finite shape for the original vertices, vertex values, facets and face ledger.')
        text += '''def VertexShape (dimension : Nat) (vertex : Array ℚ) : Prop :=
  vertex.size = dimension

def ValueShape (value : VertexValues) : Prop := value.factors.size = 10

def FacetShape (vertexCount : Nat) (facet : Array Nat) : Prop :=
  facet.toList.Nodup ∧ (∀ i : Fin facet.size, facet[i.val]! < vertexCount)

def FaceShape (vertexCount dimension : Nat) (face : FaceRecord) : Prop :=
  face.vertices.toList.Nodup ∧
  (∀ i : Fin face.vertices.size, face.vertices[i.val]! < vertexCount) ∧
  face.pivot < vertexCount ∧ face.dimension ≤ dimension

theorem facet_shape_of_fixed_size (facet : Array Nat) (n : Nat)
    (h : facet.size = n ∧ facet.toList.Nodup ∧
      (∀ i : Fin n, facet[i.val]! < 28)) : FacetShape 28 facet := by
  refine ⟨h.2.1, ?_⟩
  simpa only [h.1] using h.2.2

theorem face_shape_of_fixed_size (face : FaceRecord) (n : Nat)
    (h : face.vertices.size = n ∧ face.vertices.toList.Nodup ∧
      (∀ i : Fin n, face.vertices[i.val]! < 28) ∧
      face.pivot < 28 ∧ face.dimension ≤ 8) : FaceShape 28 8 face := by
  refine ⟨h.2.1, ?_, h.2.2.2.1, h.2.2.2.2⟩
  simpa only [h.1] using h.2.2.1

'''
        names = ['facet_shape_of_fixed_size', 'face_shape_of_fixed_size']
        predicates = {'vertices': 'VertexShape 8', 'vertex_values': 'ValueShape',
                      'facet_vertices': 'FacetShape 28', 'face_ledger': 'FaceShape 28 8'}
        counts = {}
        for key in keys:
            predicate = predicates[key]
            item_tag = fields.TYPED[key][0]
            _, groups = self.block_plan(key)
            counts[key] = len(self.payload[key])
            for block, group in enumerate(groups):
                first, after = group[0]['first'], group[-1]['after']
                name, value = self.array_fact(key, block, block), self.array_value_name(key, block, block)
                witnesses = []
                for index in range(first, after):
                    local = f'geometry{item_tag}_{index:03d}_shape'
                    self.required_local_shape.append(TYPED_NS + '.' + local)
                    if key == 'facet_vertices':
                        witness = 'facet_shape_of_fixed_size _ _ ' + local
                    elif key == 'face_ledger':
                        witness = 'face_shape_of_fixed_size _ _ ' + local
                    else:
                        witness = local
                    witnesses.append(witness)
                text += f'theorem {name} : ∀ item ∈ {value}, {predicate} item := '
                text += membership_proof(value, witnesses) + '\n'
                names.append(name)
            for row in self.field_manifest['owners']:
                plan = row['planned_obligations']
                if plan.get('key') != key or not plan.get('typed_decode_composed'):
                    continue
                (a, b), (c, d) = plan['children']
                name = self.array_fact(key, a, d)
                text += f'''theorem {name} : ∀ item ∈ {self.array_value_name(key,a,d)}, {predicate} item := by
  intro item hitem
  change item ∈ {self.array_value_name(key,a,b)} ++ {self.array_value_name(key,c,d)} at hitem
  exact (List.mem_append.mp hitem).elim ({self.array_fact(key,a,b)} item) ({self.array_fact(key,c,d)} item)

'''
                names.append(name)
        text += self.footer('.Arrays', names)
        return self.save(TAG + 'ShapeArrays', text, 'Original array-local finite shape transported through balanced lists',
                         {'array_counts': counts, 'existing_local_shape_facts_reused': sum(counts.values()),
                          'new_full_record_decisions': 0,
                          'vertex_dimension': 8, 'vertex_factors': 10, 'index_bound': 28,
                          'face_dimension_bound': 8, 'facet_and_face_vertex_ids_nodup': True})

    def complete_shape(self):
        text = self.header(['ImbalancedChen.' + TAG + suffix for suffix in ['Decoded', 'ShapeRows', 'ShapeArrays']], '',
                           'Complete finite shape of the actual original cell05 decoder output.')
        text += f'''open {TYPED_NS}.Complete
open {SHAPE_NS}.Rows
open {SHAPE_NS}.Arrays

theorem property_of_list_toArray {{α : Type}} [Inhabited α]
    (items : List α) (property : α → Prop)
    (h : ∀ item ∈ items, property item) (index : Nat)
    (hi : index < items.toArray.size) : property (items.toArray[index]!) := by
  rw [getElem!_pos items.toArray index hi]
  apply h
  simpa using (Array.getElem_mem_toList hi)

theorem dimension : concreteGeometry05.dimension = 8 := by rfl
theorem physical_jacobian : concreteGeometry05.physicalJacobian = 1 := by rfl
theorem row_count : concreteGeometry05.rows.size = 56 := by rfl
theorem vertex_count : concreteGeometry05.vertices.size = 28 := by rfl
theorem vertex_values_count : concreteGeometry05.vertexValues.size = 28 := by rfl
theorem vertex_values_size : concreteGeometry05.vertexValues.size = concreteGeometry05.vertices.size := by rfl
theorem facet_count : concreteGeometry05.facetOriginalIndices.size = 11 := by rfl
theorem facet_vertices_count : concreteGeometry05.facetVertices.size = 11 := by rfl
theorem face_count : concreteGeometry05.faces.size = 45 := by rfl

theorem facet_original_indices_nodup : concreteGeometry05.facetOriginalIndices.toList.Nodup := by
  decide +kernel

theorem facet_original_indices_bound : ∀ i : Fin 11,
    concreteGeometry05.facetOriginalIndices[i.val]! < 97 := by
  decide +kernel

theorem all_rows : ∀ r : Fin 56,
    let row := concreteGeometry05.rows[r.val]!
    row.simplexId = r.val ∧
    row.vertexIds.size = 9 ∧ row.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, row.vertexIds[i.val]! < concreteGeometry05.vertices.size) ∧
    row.factorMaxima.size = 10 ∧ row.gapWeightedMeans.size = 10 := by
  intro r
  change (Node000To006.typedRows.toArray[r.val]!).simplexId = r.val ∧
    RowShape 28 (Node000To006.typedRows.toArray[r.val]!)
  exact ⟨all_row_identifiers r,
    property_of_list_toArray Node000To006.typedRows (RowShape 28)
      rows_000_to_006_shape r.val (by change r.val < 56; exact r.isLt)⟩

theorem all_vertices : ∀ v : Fin 28,
    (concreteGeometry05.vertices[v.val]!).size = concreteGeometry05.dimension ∧
    (concreteGeometry05.vertexValues[v.val]!).factors.size = 10 := by
  intro v
  change VertexShape 8 (VerticesNode000To001.typedItems.toArray[v.val]!) ∧
    ValueShape (VertexValuesNode000To003.typedItems.toArray[v.val]!)
  exact ⟨property_of_list_toArray VerticesNode000To001.typedItems (VertexShape 8)
      vertices_000_to_001_shape v.val (by change v.val < 28; exact v.isLt),
    property_of_list_toArray VertexValuesNode000To003.typedItems ValueShape
      vertex_values_000_to_003_shape v.val (by change v.val < 28; exact v.isLt)⟩

theorem all_facets : ∀ f : Fin 11,
    let facet := concreteGeometry05.facetVertices[f.val]!
    facet.toList.Nodup ∧
    (∀ i : Fin facet.size, facet[i.val]! < concreteGeometry05.vertices.size) := by
  intro f
  change FacetShape 28 (geometryFacetVerticesTypedBlock000.toArray[f.val]!)
  exact property_of_list_toArray geometryFacetVerticesTypedBlock000 (FacetShape 28)
    facet_vertices_000_to_000_shape f.val (by change f.val < 11; exact f.isLt)

theorem all_faces : ∀ f : Fin 45,
    let face := concreteGeometry05.faces[f.val]!
    face.vertices.toList.Nodup ∧
    (∀ i : Fin face.vertices.size, face.vertices[i.val]! < concreteGeometry05.vertices.size) ∧
    face.pivot < concreteGeometry05.vertices.size ∧ face.dimension ≤ concreteGeometry05.dimension := by
  intro f
  change FaceShape 28 8 (FaceLedgerNode000To004.typedItems.toArray[f.val]!)
  exact property_of_list_toArray FaceLedgerNode000To004.typedItems (FaceShape 28 8)
    face_ledger_000_to_004_shape f.val (by change f.val < 45; exact f.isLt)

structure GeometryShape (geometry : Geometry) : Prop where
  dimension : geometry.dimension = 8
  physicalJacobian : geometry.physicalJacobian = 1
  rowCount : geometry.rows.size = 56
  vertexCount : geometry.vertices.size = 28
  vertexValuesCount : geometry.vertexValues.size = 28
  facetCount : geometry.facetOriginalIndices.size = 11
  facetVerticesCount : geometry.facetVertices.size = 11
  faceCount : geometry.faces.size = 45
  facetIndicesNodup : geometry.facetOriginalIndices.toList.Nodup
  facetIndicesBound : ∀ i : Fin geometry.facetOriginalIndices.size,
    geometry.facetOriginalIndices[i.val]! < 97
  rows : ∀ r : Fin geometry.rows.size,
    let row := geometry.rows[r.val]!
    row.simplexId = r.val ∧ RowShape geometry.vertices.size row
  vertices : ∀ v : Fin geometry.vertices.size,
    (geometry.vertices[v.val]!).size = geometry.dimension ∧
    (geometry.vertexValues[v.val]!).factors.size = 10
  facets : ∀ f : Fin geometry.facetVertices.size,
    FacetShape geometry.vertices.size (geometry.facetVertices[f.val]!)
  faces : ∀ f : Fin geometry.faces.size,
    FaceShape geometry.vertices.size geometry.dimension (geometry.faces[f.val]!)

theorem concreteGeometry05_shape : GeometryShape concreteGeometry05 where
  dimension := dimension
  physicalJacobian := physical_jacobian
  rowCount := row_count
  vertexCount := vertex_count
  vertexValuesCount := vertex_values_count
  facetCount := facet_count
  facetVerticesCount := facet_vertices_count
  faceCount := face_count
  facetIndicesNodup := facet_original_indices_nodup
  facetIndicesBound := by simpa only [facet_count] using facet_original_indices_bound
  rows := by simpa only [row_count, RowShape] using all_rows
  vertices := by simpa only [vertex_count] using all_vertices
  facets := by simpa only [facet_vertices_count, FacetShape] using all_facets
  faces := by simpa only [face_count, FaceShape] using all_faces

theorem geometryPacked05_parse_decode_shape :
    (SourceJson.parse (String.ofList geometryPacked05.toList) >>= decodeGeometry) =
      .ok concreteGeometry05 ∧ GeometryShape concreteGeometry05 :=
  ⟨geometryPacked05_parse_decode, concreteGeometry05_shape⟩

'''
        names = ['property_of_list_toArray', 'dimension', 'physical_jacobian', 'row_count', 'vertex_count',
                 'vertex_values_count', 'vertex_values_size', 'facet_count', 'facet_vertices_count', 'face_count',
                 'facet_original_indices_nodup', 'facet_original_indices_bound', 'all_rows', 'all_vertices',
                 'all_facets', 'all_faces', 'concreteGeometry05_shape', 'geometryPacked05_parse_decode_shape']
        text += self.footer('', names)
        return self.save(TAG + 'Shape', text, 'Original packed parse/decode equation conjoined with finite shape of its actual output',
                         {'actual_decoder_output': TYPED_NS + '.Complete.concreteGeometry05',
                          'original_input_bytes': 201042, 'rows': 56, 'vertices': 28, 'dimension': 8,
                          'vertex_values': 28, 'facets': 11, 'faces': 45, 'original_constraints_count_host': 97,
                          'uses_existing_local_shape_facts': 168, 'new_facet_index_nat_checks': 2,
                          'whole_parse_decode_shape_candidate': True,
                          'geometric_or_integral_interpretation': False})


def main():
    engine = ShapeEngine()
    engine.row_shapes()
    engine.array_shapes()
    engine.complete_shape()
    assert len(engine.records) == 3
    assert len(engine.required_local_shape) == 168 and len(set(engine.required_local_shape)) == 168
    assert frozen_prior() == engine.protected
    manifest = {
        'schema': 'cell05_connections_source_candidates_v1', 'batch': BATCH,
        'status': 'SOURCE_ONLY_NOT_COMPILED', 'owners': engine.records, 'owner_count': len(engine.records),
        'generator': fp(Path(__file__)), 'source_templates': engine.source_templates,
        'original_input': fp(engine.raw_origin), 'original_input_bytes': 201042,
        'original_field_order': [field.key.scalar for field in engine.node.fields],
        'vertices_host_plan': 28, 'rows_host_plan': 56, 'array_roots': engine.roots,
        'required_local_shape_declarations': engine.required_local_shape,
        'protected_previous_files': engine.protected,
        'raw_parser_changed': False, 'typed_decoder_changed': False,
        'normal_kernel_owned_accepted': False, 'whole_geometry_decoded_accepted': False,
        'geometry_or_integral_semantics_claimed': False, 'P2_6_complete': False}
    batch = HERE / 'batches' / BATCH
    write_new(batch / 'SOURCE_MANIFEST.json', manifest)
    write_new(batch / 'owner_order.txt', ''.join(row['module'] + '\n' for row in engine.records))
    print(json.dumps({'batch': BATCH, 'status': manifest['status'], 'new_owners': len(engine.records),
                      'source_bytes': sum(row['source']['bytes'] for row in engine.records),
                      'existing_local_shape_facts_reused': 168,
                      'previous_checkpoint_files_unchanged': len(engine.protected), 'new_Lean_steps_run': 0}))


if __name__ == '__main__':
    main()
