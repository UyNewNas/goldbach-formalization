#!/usr/bin/env python3
"""Specialize the original shape clauses, changing only the concrete bindings."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parent
original=ROOT/'provenance/OriginalArchive.lean'
data=original.read_bytes();text=data.decode()
assert hashlib.sha256(data).hexdigest()=='f48ba6e6522a3a76bd81ef1be15875563163a4df6e7891c1422b6562ee31ed49'
cell=re.search(r'def CellShape \(c : Fin 13\) : Prop :=\n(.*?)\n\ninstance \(c : Fin 13\)',text,re.S).group(1)
row=re.search(r'def RowShape \(r : OriginalRowIndex\) : Prop :=\n(.*?)\n\ninstance \(r : OriginalRowIndex\)',text,re.S).group(1)
cell_replacements=[('let g := geometry c','let g := concreteGeometry00'),
                   ('let m := moments c','let m := momentConcrete00'),
                   ('originalRowCount c','56'),('c.val','0'),
                   ('geometryWitnessName c','"eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json"')]
row_replacements=[('let g := rawGeometryRow r','let g := concreteGeometry00.rows[r.val]!'),
                  ('let m := rawMomentRow r','let m := momentConcrete00.rows[r.val]!'),
                  ('r.2.val','r.val'),('(geometry r.1).vertices.size','concreteGeometry00.vertices.size')]

def specialize(body,replacements):
    for before,after in replacements:
        assert before in body,before
        body=body.replace(before,after)
    return body

concrete_cell=specialize(cell,cell_replacements)
concrete_row=specialize(row,row_replacements)
bounded_row=concrete_row.replace('let g := concreteGeometry00.rows[r.val]!',
                                'let g := P2OriginalSaving19Geometry00BoundedAccess.boundedRow r').replace(
    'let m := momentConcrete00.rows[r.val]!',
    'let m := momentConcrete00.rows[r.val]\'(P2OriginalSaving19Moment00Shape.row_bound r)')
source='''import ImbalancedChen.P2OriginalSaving19Geometry00BoundedAccess
import ImbalancedChen.P2OriginalSaving19Moment00Shape

/-! Exact original CellShape and RowShape clauses specialized to the certified
concrete cell00 values, expected 56 rows and original witness filename. The
Archive input maps/getter aliases are not asserted here. Original schemas,
metadata, record order, predicates and numerical floors are unchanged. -/
namespace ImbalancedChen.P2OriginalSaving19Cell00Shape
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding
open ImbalancedChen.P2OriginalSaving19Moment00Decoding

def CellShape00 : Prop :=
'''+concrete_cell+'''

def RowShape00 (r : Fin 56) : Prop :=
'''+concrete_row+'''

def BoundedRowShape00 (r : Fin 56) : Prop :=
'''+bounded_row+'''

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_SHAPE before_opaque_cell_composition"
  err.flush

theorem cell_shape : CellShape00 :=
  ⟨P2OriginalSaving19Geometry00Shape.dimension,
    P2OriginalSaving19Geometry00Shape.physical_jacobian,
    P2OriginalSaving19Geometry00Shape.row_count,
    P2OriginalSaving19Moment00Shape.row_count,
    P2OriginalSaving19Geometry00Shape.vertex_values_size,
    P2OriginalSaving19Geometry00Shape.all_vertices,
    P2OriginalSaving19Moment00Shape.metadata⟩

theorem row_shape (r : Fin 56) : RowShape00 r := by
  rcases P2OriginalSaving19Geometry00Shape.all_rows r with
    ⟨hid, hsize, hnodup, hbounds, hmaxima, hmeans⟩
  have hm := P2OriginalSaving19Moment00Shape.row_ids_and_floor_sizes r
  exact ⟨hid, hm.1, hsize, hnodup, hbounds, hmaxima, hmeans, hm.2⟩

theorem row_shape_bounded (r : Fin 56) : BoundedRowShape00 r := by
  rcases P2OriginalSaving19Geometry00BoundedAccess.row_properties r with
    ⟨hid, hsize, hnodup, hbounds, hmaxima, hmeans⟩
  have hm := P2OriginalSaving19Moment00Shape.row_ids_and_floor_sizes_bounded r
  exact ⟨hid, hm.1, hsize, hnodup, hbounds, hmaxima, hmeans, hm.2⟩

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL00_SHAPE exact_original_joint_clauses_complete"
  err.flush

#print axioms cell_shape
#print axioms row_shape
#print axioms row_shape_bounded
end ImbalancedChen.P2OriginalSaving19Cell00Shape
'''
p=ROOT/'project/ImbalancedChen/P2OriginalSaving19Cell00Shape.lean';assert not p.exists();p.write_text(source)
manifest={'original_source':{'path':str(original),'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)},
          'original_CellShape_body_sha256':hashlib.sha256(cell.encode()).hexdigest(),
          'original_RowShape_body_sha256':hashlib.sha256(row.encode()).hexdigest(),
          'CellShape_binding_substitutions':cell_replacements,'RowShape_binding_substitutions':row_replacements,
          'all_remaining_predicate_bytes_preserved':True,
          'source':{'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':len(p.read_bytes())},
          'Archive_CellShape0_or_RowShape_alias_theorem_claimed':False,
          'moment_metadata_and_row_shape_recomputed':False,'floor_validity_claimed':False}
q=ROOT/'SHAPE_SPECIALIZATION.json';assert not q.exists();q.write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(manifest['source'],indent=2))
