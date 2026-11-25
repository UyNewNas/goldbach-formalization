from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parent
BASE=json.loads((ROOT/'MANIFEST.json').read_text())
raw=Path(BASE['fixture']['path']).read_bytes()
assert len(raw)==195134 and hashlib.sha256(raw).hexdigest()==BASE['fixture']['sha256'] and raw.isascii()
physical=raw[20:47]
assert physical==b'\r\n  "physical_jacobian": 1,'
header=raw[47:77]
assert header==b'\r\n  "facet_original_indices": '
array=raw[77:178]
assert array.startswith(b'[\r\n') and array.endswith(b'\r\n  ]')
assert raw[178:179]==b','
facet=raw[47:179]
tokens=re.findall(rb'[0-9]+',array)
assert tokens==[b'7',b'8',b'9',b'14',b'18',b'19',b'34',b'39',b'61',b'75',b'82']
def qc(c): return "'"+{'\r':'\\r','\n':'\\n','\t':'\\t','\\':'\\\\',"'":"\\'"}.get(c,c)+"'"
def ql(b): return '['+', '.join(qc(c) for c in b.decode('ascii'))+']'
def marker(t): return 'run_cmd do\n  let err ← IO.getStderr\n  err.putStrLn "P26_FIRST_THREE '+t+'"\n  err.flush\n'
items='[\n    '+',\n    '.join('.number (String.ofList '+ql(t)+')' for t in tokens)+'\n  ]'
ns='ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic'
source='''import ImbalancedChen.P2OriginalSaving19DimensionPrefix00

/-!
Exactly the next two original geometry00 fields, preserving CRLF, commas,
original object accumulators, duplicate-key checks and array item order.
Raw slices and candidate AST nodes are generated mechanically. The original
SourceJson equations below certify them. No full remaining-tail copy and no
whole-parser success guard is introduced.
-/
namespace '''+ns+'''

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

def dimensionAcc00 : List (String × SourceJson) := [(dimensionKey00, dimensionValue00)]

def physicalPrefixChars00 : List Char := '''+ql(physical)+'''
def physicalKey00 : String := String.ofList '''+ql(b'physical_jacobian')+'''
def physicalValue00 : SourceJson := .number (String.ofList ['1'])
def physicalAcc00 : List (String × SourceJson) :=
  (physicalKey00, physicalValue00) :: dimensionAcc00

def facetIndicesHeaderChars00 : List Char := '''+ql(header)+'''
def facetIndicesArrayChars00 : List Char := '''+ql(array)+'''
def facetIndicesPrefixChars00 : List Char := '''+ql(facet)+'''
def facetIndicesKey00 : String := String.ofList '''+ql(b'facet_original_indices')+'''
def facetIndicesItems00 : List SourceJson := '''+items+'''
def facetIndicesValue00 : SourceJson := .arr facetIndicesItems00
def facetIndicesAcc00 : List (String × SourceJson) :=
  (facetIndicesKey00, facetIndicesValue00) :: physicalAcc00

'''+marker('before_raw_slice_bindings')+'''
theorem geometryChars00_physical_prefix :
    (geometryChars00.drop 20).take 27 = physicalPrefixChars00 := by
  rfl

theorem geometryChars00_facet_indices_prefix :
    (geometryChars00.drop 47).take 132 = facetIndicesPrefixChars00 := by
  rfl

theorem facet_indices_prefix_decomposition :
    facetIndicesPrefixChars00 =
      facetIndicesHeaderChars00 ++ facetIndicesArrayChars00 ++ [','] := by
  rfl

'''+marker('after_raw_slice_bindings')+'''
theorem geometryChars00_physical_split :
    geometryChars00.drop 20 = physicalPrefixChars00 ++ geometryChars00.drop 47 := by
  calc
    geometryChars00.drop 20 =
        (geometryChars00.drop 20).take 27 ++ (geometryChars00.drop 20).drop 27 :=
      (List.take_append_drop 27 (geometryChars00.drop 20)).symm
    _ = physicalPrefixChars00 ++ (geometryChars00.drop 20).drop 27 :=
      congrArg (fun p => p ++ (geometryChars00.drop 20).drop 27)
        geometryChars00_physical_prefix
    _ = physicalPrefixChars00 ++ geometryChars00.drop 47 := by
      rw [List.drop_drop]

theorem geometryChars00_facet_indices_split :
    geometryChars00.drop 47 = facetIndicesPrefixChars00 ++ geometryChars00.drop 179 := by
  calc
    geometryChars00.drop 47 =
        (geometryChars00.drop 47).take 132 ++ (geometryChars00.drop 47).drop 132 :=
      (List.take_append_drop 132 (geometryChars00.drop 47)).symm
    _ = facetIndicesPrefixChars00 ++ (geometryChars00.drop 47).drop 132 :=
      congrArg (fun p => p ++ (geometryChars00.drop 47).drop 132)
        geometryChars00_facet_indices_prefix
    _ = facetIndicesPrefixChars00 ++ geometryChars00.drop 179 := by
      rw [List.drop_drop]

'''+marker('after_exact_tail_splits')+'''
/-- This retains the prior dimension field and evaluates the original
nonempty-accumulator duplicate-key check, rather than assuming it away. -/
theorem object_physical_prefix (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (physicalPrefixChars00 ++ tail))
      dimensionAcc00 =
    SourceJson.object (fuel + 18) (SourceJson.white tail) physicalAcc00 := by
  rfl

'''+marker('after_physical_reader_step')+'''
/-- Exact eleven-item value, with an arbitrary untouched continuation. -/
theorem value_facet_indices_array (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 13) (facetIndicesArrayChars00 ++ tail) =
      .ok (facetIndicesValue00, tail) := by
  rfl

'''+marker('after_eleven_item_value')+'''
/-- A quoted expression of the original post-value continuation. Its equality
with the original object reader, including duplicate-key checking, is proved
in object_facet_indices_header below. -/
def facetIndicesAfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending =>
      .ok (.obj (((facetIndicesKey00, result.1) :: physicalAcc00).reverse), ending)
  | ',' :: ending =>
      SourceJson.object fuel (SourceJson.white ending)
        ((facetIndicesKey00, result.1) :: physicalAcc00)
  | _ => .error "object separator missing"

theorem object_facet_indices_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (facetIndicesHeaderChars00 ++ rest))
      physicalAcc00 =
      (SourceJson.value (fuel + 23) rest).bind (facetIndicesAfterValue00 (fuel + 23)) := by
  rfl

'''+marker('after_facet_object_header')+'''
theorem object_facet_indices_prefix (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (facetIndicesPrefixChars00 ++ tail))
      physicalAcc00 =
      SourceJson.object (fuel + 23) (SourceJson.white tail) facetIndicesAcc00 := by
  have hinput : facetIndicesPrefixChars00 ++ tail =
      facetIndicesHeaderChars00 ++ (facetIndicesArrayChars00 ++ (',' :: tail)) := by
    rw [facet_indices_prefix_decomposition]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  calc
    SourceJson.object (fuel + 24) (SourceJson.white (facetIndicesPrefixChars00 ++ tail))
        physicalAcc00 =
      SourceJson.object (fuel + 24)
        (SourceJson.white (facetIndicesHeaderChars00 ++ (facetIndicesArrayChars00 ++ (',' :: tail))))
        physicalAcc00 :=
      congrArg (fun s => SourceJson.object (fuel + 24) (SourceJson.white s) physicalAcc00)
        hinput
    _ = (SourceJson.value (fuel + 23) (facetIndicesArrayChars00 ++ (',' :: tail))).bind
        (facetIndicesAfterValue00 (fuel + 23)) :=
      object_facet_indices_header fuel (facetIndicesArrayChars00 ++ (',' :: tail))
    _ = (Except.ok (facetIndicesValue00, ',' :: tail)).bind
        (facetIndicesAfterValue00 (fuel + 23)) :=
      congrArg (fun r => r.bind (facetIndicesAfterValue00 (fuel + 23)))
        (value_facet_indices_array (fuel + 10) (',' :: tail))
    _ = SourceJson.object (fuel + 23) (SourceJson.white tail) facetIndicesAcc00 := by
      rfl

'''+marker('after_composed_facet_field')+'''
theorem geometryChars00_physical_step :
    SourceJson.object 195133 (SourceJson.white (geometryChars00.drop 20)) dimensionAcc00 =
      SourceJson.object 195132 (SourceJson.white (geometryChars00.drop 47)) physicalAcc00 := by
  exact (congrArg (fun s => SourceJson.object 195133 (SourceJson.white s) dimensionAcc00)
      geometryChars00_physical_split).trans
    (object_physical_prefix 195114 (geometryChars00.drop 47))

theorem geometryChars00_facet_indices_step :
    SourceJson.object 195132 (SourceJson.white (geometryChars00.drop 47)) physicalAcc00 =
      SourceJson.object 195131 (SourceJson.white (geometryChars00.drop 179)) facetIndicesAcc00 := by
  exact (congrArg (fun s => SourceJson.object 195132 (SourceJson.white s) physicalAcc00)
      geometryChars00_facet_indices_split).trans
    (object_facet_indices_prefix 195108 (geometryChars00.drop 179))

theorem geometryChars00_through_facet_indices :
    SourceJson.value 195135 geometryChars00 =
      SourceJson.object 195131 (SourceJson.white (geometryChars00.drop 179)) facetIndicesAcc00 := by
  exact geometryChars00_dimension_step.trans
    (geometryChars00_physical_step.trans geometryChars00_facet_indices_step)

'''+marker('after_closed_complete_input_composition')+'''
#print axioms geometryChars00_physical_prefix
#print axioms geometryChars00_facet_indices_prefix
#print axioms geometryChars00_physical_split
#print axioms geometryChars00_facet_indices_split
#print axioms object_physical_prefix
#print axioms value_facet_indices_array
#print axioms object_facet_indices_header
#print axioms object_facet_indices_prefix
#print axioms geometryChars00_physical_step
#print axioms geometryChars00_facet_indices_step
#print axioms geometryChars00_through_facet_indices

end '''+ns+'\n'
p=ROOT/'ImbalancedChen/P2OriginalSaving19FirstThreeFields00.lean'
assert not p.exists()
p.write_text(source)
def fp(p):
 b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
deps=[fp(ROOT/'objects/ImbalancedChen'/f'{name}.olean') for name in ['P2OriginalSaving19CharacterCore00','P2OriginalSaving19CharacterLength00','P2OriginalSaving19DimensionPrefix00']]
manifest={**BASE,'status':'prepared_not_compiled','scope':'closed original object-state transitions through physical_jacobian and 11-item facet indices; no whole parse',
 'files':[{'module':'ImbalancedChen.P2OriginalSaving19FirstThreeFields00','path':str(p.relative_to(ROOT)),'sha256':fp(p)['sha256'],'bytes':fp(p)['bytes']}],
 'reused_new_input_objects':deps,'raw_slices':[{'field':'physical_jacobian','start':20,'end':47,'bytes':27,'sha256':hashlib.sha256(physical).hexdigest()},{'field':'facet_original_indices','start':47,'end':179,'bytes':132,'sha256':hashlib.sha256(facet).hexdigest()},{'field':'facet_array_value','start':77,'end':178,'bytes':101,'sha256':hashlib.sha256(array).hexdigest()}],
 'candidate_array_digit_tokens':[t.decode() for t in tokens],'array_items':11,'line_endings_preserved':'CRLF','suffix_copies_generated':False,
 'original_object_accumulators_and_duplicate_checks_preserved':True,'original_parser_changed':False,'host_JSON_parser_used':False,
 'closed_fuel_transitions':[195135,195133,195132,195131],'order':['first-three normal','first-three kernel if normal succeeds'],'whole_parse_retried':False}
(ROOT/'FIRST_THREE_FIELDS_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'source':fp(p),'slices':manifest['raw_slices'],'dependency_objects':deps,'whole_parse_retried':False},indent=2))
