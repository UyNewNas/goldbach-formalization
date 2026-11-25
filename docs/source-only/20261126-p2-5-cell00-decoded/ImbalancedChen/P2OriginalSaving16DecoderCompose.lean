import ImbalancedChen.P2OriginalSaving16DecoderChars

/-!
Composition equations for the unchanged decoder. Array computations are
expressed using the standard library's proved `List.mapM_toArray` equality,
so separately checked scalar and record results can be reused.
-/

namespace ImbalancedChen.P2OriginalSaving16OriginalArchive

open P2OriginalSaving19Archive (SourceJson)

theorem decodeString_str (s : String) :
    (SourceJson.Decode.read (.str s) : Except String String) = .ok s := rfl

theorem getObjValAs_of_lookup {α : Type} [SourceJson.Decode α]
    (j : SourceJson) (key : String) (v : SourceJson)
    (h : j.getObjVal? key = .ok v) :
    j.getObjValAs? α key = SourceJson.Decode.read v := by
  unfold SourceJson.getObjValAs?
  rw [h]
  rfl

theorem rationalField_of_string (j : SourceJson) (key s : String)
    (h : j.getObjValAs? String key = .ok s) :
    rationalField j key = parseRational s := by
  unfold rationalField
  rw [h]
  rfl

theorem rationalArrayField_of_lookup (j : SourceJson) (key : String) (v : SourceJson)
    (h : j.getObjVal? key = .ok v) :
    rationalArrayField j key = rationalArray v := by
  unfold rationalArrayField
  rw [h]
  rfl

theorem rationalArray_arr (items : List SourceJson) :
    rationalArray (.arr items) =
      List.toArray <$> items.mapM (fun v => do parseRational (← v.getStr?)) := by
  change items.toArray.mapM (fun v => do parseRational (← v.getStr?)) = _
  exact List.mapM_toArray

theorem decodeArray_arr {α : Type} [SourceJson.Decode α] (items : List SourceJson) :
    (SourceJson.Decode.read (.arr items) : Except String (Array α)) =
      List.toArray <$> items.mapM SourceJson.Decode.read := by
  change items.toArray.mapM SourceJson.Decode.read = _
  exact List.mapM_toArray

end ImbalancedChen.P2OriginalSaving16OriginalArchive
