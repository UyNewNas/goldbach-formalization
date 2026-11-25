import ImbalancedChen.P2OriginalSaving19MomentFloorConsumer
import ImbalancedChen.P2OriginalSaving19ArchiveSchema
import ImbalancedChen.P2OriginalSaving19SourceJson
import ImbalancedChen.P2OriginalSaving19ArchivePackedInputs
import ImbalancedChen.P2OriginalSaving19SourceJsonCharInput

/-!
SOURCE CANDIDATE, NOT COMPILED OR ACCEPTED. New input representation, requiring
fresh Core acceptance. The old v2 Core object/export acceptance is not reused.
All 26 original files are quoted separately by their data owners; Core only
assembles already quoted complete characters. The byte-preserved original
schemas and decoders are imported from ArchiveSchema. The parse_ofList bridges
preserve the entire original parser result; they assert no concrete parse success.
ArchiveSchema and this changed Core each require their own fresh acceptance.
-/
namespace ImbalancedChen.P2OriginalSaving19Archive

set_option maxRecDepth 1000000

noncomputable def geometryText : Fin 13 → String :=
  fun c => String.ofList (geometryChars c)

noncomputable def momentText : Fin 13 → String :=
  fun c => String.ofList (momentChars c)

noncomputable def geometryParse (c : Fin 13) : Except String Geometry :=
  SourceJson.parse (geometryText c) >>= decodeGeometry

noncomputable def momentParse (c : Fin 13) : Except String Moments :=
  SourceJson.parse (momentText c) >>= decodeMoments

noncomputable def geometry (c : Fin 13) : Geometry := (geometryParse c).toOption.getD default
noncomputable def moments (c : Fin 13) : Moments := (momentParse c).toOption.getD default

/-- Exact input-representation bridge, including unchanged typed decoding.
This does not discharge a parse-success, shape, or numerical obligation. -/
theorem geometryParse_eq_parseChars (c : Fin 13) :
    geometryParse c = (SourceJson.parseChars (geometryChars c) >>= decodeGeometry) :=
  congrArg (fun result => result >>= decodeGeometry)
    (SourceJson.parse_ofList (geometryChars c))

theorem momentParse_eq_parseChars (c : Fin 13) :
    momentParse c = (SourceJson.parseChars (momentChars c) >>= decodeMoments) :=
  congrArg (fun result => result >>= decodeMoments)
    (SourceJson.parse_ofList (momentChars c))

end ImbalancedChen.P2OriginalSaving19Archive
