import ImbalancedChen.P2OriginalSaving19Moment05DecodeFromRows
import ImbalancedChen.P2OriginalSaving19Moment05DecodedBlock013

/-! Complete original moment05 parse followed by the unchanged decodeMoments returns this concrete Moments value.
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
  err.putStrLn "P26_MOMENT05 typed_whole_before_concrete_value"
  err.flush

noncomputable def momentConcrete05 : Moments :=
  momentMomentsWithRows momentTypedRowsThroughBlock013.toArray

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_whole_after_concrete_value"
  err.flush

theorem decode_momentRootValue : decodeMoments momentRootValue = .ok momentConcrete05 :=
  decodeMoments_of_records_decode momentRecordsAcc056.reverse momentTypedRowsThroughBlock013
    decode_moment_records_through_block_013

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 typed_whole_after_opaque_decoder_application"
  err.flush

theorem momentPacked05_parse_decode :
    (SourceJson.parse (String.ofList momentPacked05.toList) >>= decodeMoments) =
      .ok momentConcrete05 :=
  parse_decode_of_parse_and_decode (String.ofList momentPacked05.toList) momentRootValue
    momentConcrete05 momentPacked05_parse decode_momentRootValue

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05 whole_original_typed_moments_complete"
  err.flush

#print axioms decode_momentRootValue
#print axioms momentPacked05_parse_decode

end ImbalancedChen.P2OriginalSaving19Moment05Decoding
