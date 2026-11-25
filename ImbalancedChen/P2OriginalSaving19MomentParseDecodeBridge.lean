import ImbalancedChen.P2OriginalSaving19ArchiveSchema

/-! Exact generic parse/bind proof extracted from the accepted Moment00 glue.
This module contains no concrete data and rechecks no input or record. -/
namespace ImbalancedChen.P2OriginalSaving19MomentParseDecodeBridge

open P2OriginalSaving19Archive

theorem parse_decode_of_parse_and_decode
    (text : String) (parsed : SourceJson) (decoded : Moments)
    (hparse : SourceJson.parse text = .ok parsed)
    (hdecode : decodeMoments parsed = .ok decoded) :
    (SourceJson.parse text >>= decodeMoments) = .ok decoded := by
  rw [hparse]
  exact hdecode

#print axioms parse_decode_of_parse_and_decode

end ImbalancedChen.P2OriginalSaving19MomentParseDecodeBridge
