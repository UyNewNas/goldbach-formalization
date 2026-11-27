import ImbalancedChen.P2OriginalSaving19Moment05DecodeMetadata

/-! Abstract monadic composition of the original decoder. No concrete record list is reduced here.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment05Parsing

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 abstract_rows_before_glue"
  err.flush

theorem decodeMoments_of_records_decode
    (sourceRecords : List SourceJson) (typedRecords : List MomentRecord)
    (hrecords : sourceRecords.mapM decodeMomentRecord = .ok typedRecords) :
    decodeMoments (momentObjectWithRecords sourceRecords) =
      .ok (momentMomentsWithRows typedRecords.toArray) := by
  rw [decodeMoments_momentObjectWithRecords, List.mapM_toArray, hrecords]
  rfl

theorem parse_decode_of_parse_and_decode
    (text : String) (parsed : SourceJson) (decoded : Moments)
    (hparse : SourceJson.parse text = .ok parsed)
    (hdecode : decodeMoments parsed = .ok decoded) :
    (SourceJson.parse text >>= decodeMoments) = .ok decoded := by
  rw [hparse]
  exact hdecode

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 abstract_rows_glue_complete"
  err.flush

#print axioms decodeMoments_of_records_decode
#print axioms parse_decode_of_parse_and_decode

end ImbalancedChen.P2OriginalSaving19Moment05Decoding
