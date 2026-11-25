import ImbalancedChen.P2OriginalSaving19DimensionPrefix00

/-!
Exactly the next two original geometry00 fields, preserving CRLF, commas,
original object accumulators, duplicate-key checks and array item order.
Raw slices and candidate AST nodes are generated mechanically. The original
SourceJson equations below certify them. No full remaining-tail copy and no
whole-parser success guard is introduced.
-/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

def dimensionAcc00 : List (String × SourceJson) := [(dimensionKey00, dimensionValue00)]

def physicalPrefixChars00 : List Char := ['\r', '\n', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'j', 'a', 'c', 'o', 'b', 'i', 'a', 'n', '"', ':', ' ', '1', ',']
def physicalKey00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'j', 'a', 'c', 'o', 'b', 'i', 'a', 'n']
def physicalValue00 : SourceJson := .number (String.ofList ['1'])
def physicalAcc00 : List (String × SourceJson) :=
  (physicalKey00, physicalValue00) :: dimensionAcc00

def facetIndicesHeaderChars00 : List Char := ['\r', '\n', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ']
def facetIndicesArrayChars00 : List Char := ['[', '\r', '\n', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ']']
def facetIndicesPrefixChars00 : List Char := ['\r', '\n', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', '6', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', '7', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', '8', '2', '\r', '\n', ' ', ' ', ']', ',']
def facetIndicesKey00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 'o', 'r', 'i', 'g', 'i', 'n', 'a', 'l', '_', 'i', 'n', 'd', 'i', 'c', 'e', 's']
def facetIndicesItems00 : List SourceJson := [
    .number (String.ofList ['7']),
    .number (String.ofList ['8']),
    .number (String.ofList ['9']),
    .number (String.ofList ['1', '4']),
    .number (String.ofList ['1', '8']),
    .number (String.ofList ['1', '9']),
    .number (String.ofList ['3', '4']),
    .number (String.ofList ['3', '9']),
    .number (String.ofList ['6', '1']),
    .number (String.ofList ['7', '5']),
    .number (String.ofList ['8', '2'])
  ]
def facetIndicesValue00 : SourceJson := .arr facetIndicesItems00
def facetIndicesAcc00 : List (String × SourceJson) :=
  (facetIndicesKey00, facetIndicesValue00) :: physicalAcc00

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FIRST_THREE before_raw_slice_bindings"
  err.flush

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

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FIRST_THREE after_raw_slice_bindings"
  err.flush

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

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FIRST_THREE after_exact_tail_splits"
  err.flush

/-- This retains the prior dimension field and evaluates the original
nonempty-accumulator duplicate-key check, rather than assuming it away. -/
theorem object_physical_prefix (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (physicalPrefixChars00 ++ tail))
      dimensionAcc00 =
    SourceJson.object (fuel + 18) (SourceJson.white tail) physicalAcc00 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FIRST_THREE after_physical_reader_step"
  err.flush

/-- Exact eleven-item value, with an arbitrary untouched continuation. -/
theorem value_facet_indices_array (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 13) (facetIndicesArrayChars00 ++ tail) =
      .ok (facetIndicesValue00, tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FIRST_THREE after_eleven_item_value"
  err.flush

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

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FIRST_THREE after_facet_object_header"
  err.flush

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

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FIRST_THREE after_composed_facet_field"
  err.flush

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

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FIRST_THREE after_closed_complete_input_composition"
  err.flush

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

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
