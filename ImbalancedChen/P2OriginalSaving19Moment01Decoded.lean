import ImbalancedChen.P2OriginalSaving19MomentParseDecodeBridge
import ImbalancedChen.P2OriginalSaving19Moment01DecodeFromRows
import ImbalancedChen.P2OriginalSaving19Moment01DecodedBlock035

/-! Complete original moment01 parse followed by the unchanged decodeMoments returns this concrete Moments value.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

open ImbalancedChen.P2OriginalSaving19Moment01Parsing

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_whole_before_concrete_value"
  err.flush

noncomputable def momentConcrete01 : Moments :=
  momentMomentsWithRows momentTypedRowsThroughBlock035.toArray

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_whole_after_concrete_value"
  err.flush

theorem decode_momentRootValue : decodeMoments momentRootValue = .ok momentConcrete01 :=
  decodeMoments_of_records_decode momentRecordsAcc144.reverse momentTypedRowsThroughBlock035
    decode_moment_records_through_block_035

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 typed_whole_after_opaque_decoder_application"
  err.flush

theorem momentPacked01_parse_decode :
    (SourceJson.parse (String.ofList momentPacked01.toList) >>= decodeMoments) =
      .ok momentConcrete01 :=
  P2OriginalSaving19MomentParseDecodeBridge.parse_decode_of_parse_and_decode
    (String.ofList momentPacked01.toList) momentRootValue momentConcrete01
    momentPacked01_parse decode_momentRootValue

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01 whole_original_typed_moments_complete"
  err.flush

#print axioms decode_momentRootValue
#print axioms momentPacked01_parse_decode

end ImbalancedChen.P2OriginalSaving19Moment01Decoding
