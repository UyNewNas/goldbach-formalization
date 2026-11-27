import ImbalancedChen.P2OriginalSaving19ArchiveSchema
import ImbalancedChen.P2OriginalSaving19Moment05Parse

/-! Original moment05 metadata decoded to exact fields, leaving the original record list abstract.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment05Parsing

noncomputable def momentObjectWithRecords (records : List SourceJson) : SourceJson :=
  .obj (((momentRecordsFieldKey, .arr records) :: momentMetadataAcc009).reverse)

noncomputable def momentMetadataDecoded_cellId : Nat := 5

theorem get_moment_metadata_000 (records : List SourceJson) :
    (momentObjectWithRecords records).getObjValAs? Nat "cell_id" =
      .ok momentMetadataDecoded_cellId := by
  change SourceJson.Decode.read (α := Nat) momentMetadataField000Value = .ok momentMetadataDecoded_cellId
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_metadata_000_complete"
  err.flush

noncomputable def momentMetadataDecoded_sourceWitness : String := (String.ofList ['e', 'i', 'g', 'h', 't', 'h', '-', 't', 'h', 'i', 'r', 'd', '-', 'm', 'i', 'n', 'o', 'r', 'a', 'n', 't', '-', 'e', 'x', 't', 'e', 'n', 's', 'i', 'o', 'n', '-', '2', '0', '2', '6', '1', '0', '0', '9', '-', 'a', '2', '3', '-', 's', '2', '3', '_', 'l', 'o', 'w', '-', '0', '5', '-', 'c', 'e', 'l', 'l', '.', 'w', 'i', 't', 'n', 'e', 's', 's', '.', 'j', 's', 'o', 'n'])

theorem get_moment_metadata_001 (records : List SourceJson) :
    (momentObjectWithRecords records).getObjValAs? String "source_witness" =
      .ok momentMetadataDecoded_sourceWitness := by
  change SourceJson.Decode.read (α := String) momentMetadataField001Value = .ok momentMetadataDecoded_sourceWitness
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_metadata_001_complete"
  err.flush

noncomputable def momentMetadataDecoded_dimension : Nat := 8

theorem get_moment_metadata_002 (records : List SourceJson) :
    (momentObjectWithRecords records).getObjValAs? Nat "dimension" =
      .ok momentMetadataDecoded_dimension := by
  change SourceJson.Decode.read (α := Nat) momentMetadataField002Value = .ok momentMetadataDecoded_dimension
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_metadata_002_complete"
  err.flush

noncomputable def momentMetadataDecoded_verticesPerSimplex : Nat := 9

theorem get_moment_metadata_003 (records : List SourceJson) :
    (momentObjectWithRecords records).getObjValAs? Nat "vertices_per_simplex" =
      .ok momentMetadataDecoded_verticesPerSimplex := by
  change SourceJson.Decode.read (α := Nat) momentMetadataField003Value = .ok momentMetadataDecoded_verticesPerSimplex
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_metadata_003_complete"
  err.flush

noncomputable def momentMetadataDecoded_factorCount : Nat := 10

theorem get_moment_metadata_004 (records : List SourceJson) :
    (momentObjectWithRecords records).getObjValAs? Nat "factor_count" =
      .ok momentMetadataDecoded_factorCount := by
  change SourceJson.Decode.read (α := Nat) momentMetadataField004Value = .ok momentMetadataDecoded_factorCount
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_metadata_004_complete"
  err.flush

noncomputable def momentMetadataDecoded_logDegree : Nat := 6

theorem get_moment_metadata_005 (records : List SourceJson) :
    (momentObjectWithRecords records).getObjValAs? Nat "log_degree" =
      .ok momentMetadataDecoded_logDegree := by
  change SourceJson.Decode.read (α := Nat) momentMetadataField005Value = .ok momentMetadataDecoded_logDegree
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_metadata_005_complete"
  err.flush

noncomputable def momentMetadataDecoded_expDegree : Nat := 3

theorem get_moment_metadata_006 (records : List SourceJson) :
    (momentObjectWithRecords records).getObjValAs? Nat "exp_degree" =
      .ok momentMetadataDecoded_expDegree := by
  change SourceJson.Decode.read (α := Nat) momentMetadataField006Value = .ok momentMetadataDecoded_expDegree
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_metadata_006_complete"
  err.flush

noncomputable def momentMetadataDecoded_logDenominatorText : String := String.ofList ['1', '2', '0', '8', '9', '2', '5', '8', '1', '9', '6', '1', '4', '6', '2', '9', '1', '7', '4', '7', '0', '6', '1', '7', '6']

theorem get_moment_metadata_007 (records : List SourceJson) :
    (momentObjectWithRecords records).getObjValAs? String "log_floor_denominator" =
      .ok momentMetadataDecoded_logDenominatorText := by
  change SourceJson.Decode.read (α := String) momentMetadataField007Value = .ok momentMetadataDecoded_logDenominatorText
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_metadata_007_complete"
  err.flush

noncomputable def momentMetadataDecoded_finalDenominatorText : String := String.ofList ['7', '9', '2', '2', '8', '1', '6', '2', '5', '1', '4', '2', '6', '4', '3', '3', '7', '5', '9', '3', '5', '4', '3', '9', '5', '0', '3', '3', '6']

theorem get_moment_metadata_008 (records : List SourceJson) :
    (momentObjectWithRecords records).getObjValAs? String "final_floor_denominator" =
      .ok momentMetadataDecoded_finalDenominatorText := by
  change SourceJson.Decode.read (α := String) momentMetadataField008Value = .ok momentMetadataDecoded_finalDenominatorText
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_metadata_008_complete"
  err.flush

noncomputable def momentMetadataDecoded_logDenominator : Int := (1208925819614629174706176 : Int)

theorem parse_moment_metadata_logDenominator :
    parseInteger momentMetadataDecoded_logDenominatorText = .ok momentMetadataDecoded_logDenominator := by decide +kernel

noncomputable def momentMetadataDecoded_finalDenominator : Int := (79228162514264337593543950336 : Int)

theorem parse_moment_metadata_finalDenominator :
    parseInteger momentMetadataDecoded_finalDenominatorText = .ok momentMetadataDecoded_finalDenominator := by decide +kernel

noncomputable def momentMomentsWithRows (rows : Array MomentRecord) : Moments := {
  cellId := momentMetadataDecoded_cellId
  sourceWitness := momentMetadataDecoded_sourceWitness
  dimension := momentMetadataDecoded_dimension
  verticesPerSimplex := momentMetadataDecoded_verticesPerSimplex
  factorCount := momentMetadataDecoded_factorCount
  logDegree := momentMetadataDecoded_logDegree
  expDegree := momentMetadataDecoded_expDegree
  logDenominator := momentMetadataDecoded_logDenominator
  finalDenominator := momentMetadataDecoded_finalDenominator
  rows := rows }

theorem get_moment_records_field (records : List SourceJson) :
    (momentObjectWithRecords records).getObjVal? "records" = .ok (.arr records) := by rfl

theorem decodeMoments_momentObjectWithRecords (records : List SourceJson) :
    decodeMoments (momentObjectWithRecords records) =
      (records.toArray.mapM decodeMomentRecord).bind (fun rows => .ok (momentMomentsWithRows rows)) := by
  simp only [decodeMoments,
    get_moment_metadata_000, get_moment_metadata_001, get_moment_metadata_002,
    get_moment_metadata_003, get_moment_metadata_004, get_moment_metadata_005,
    get_moment_metadata_006, get_moment_metadata_007, get_moment_metadata_008,
    get_moment_records_field, SourceJson.getArr?]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_metadata_decoder_factorization_complete"
  err.flush

#print axioms get_moment_metadata_000
#print axioms get_moment_metadata_001
#print axioms get_moment_metadata_002
#print axioms get_moment_metadata_003
#print axioms get_moment_metadata_004
#print axioms get_moment_metadata_005
#print axioms get_moment_metadata_006
#print axioms get_moment_metadata_007
#print axioms get_moment_metadata_008
#print axioms parse_moment_metadata_logDenominator
#print axioms parse_moment_metadata_finalDenominator
#print axioms get_moment_records_field
#print axioms decodeMoments_momentObjectWithRecords

end ImbalancedChen.P2OriginalSaving19Moment05Decoding
