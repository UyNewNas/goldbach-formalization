import ImbalancedChen.P2OriginalSaving19ArchiveSchema

/-! Exact symbolic elimination of String.ofList/toList roundtrips in the
original rational decoder. The original slash split, integer recognition,
nonzero denominator and all field getters remain explicit proof obligations.
No parser or typed-decoder definition is changed. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED rational_chars_before_generic"
  err.flush

theorem original_rational_fraction_of_chars
    (ns ds : List Char) (n d : Int)
    (hnoslash : ns.all (fun c => c != '/') = true)
    (hn : SourceJson.intChars ns = some n)
    (hd : SourceJson.intChars ds = some d)
    (hne : d ≠ 0) :
    parseRational (String.ofList (ns ++ '/' :: ds)) = .ok ((n : ℚ) / (d : ℚ)) := by
  have ht : (ns ++ '/' :: ds).takeWhile (fun c => c != '/') = ns := by
    simpa using (List.takeWhile_append_of_pos (l₂ := '/' :: ds)
      (List.all_eq_true.mp hnoslash))
  simp only [parseRational, String.toList_ofList, ht, List.drop_left,
    parseInteger, hn, hd]
  simp only [bind, Except.bind, hne, if_false]
  rfl

theorem original_rational_integer_of_chars
    (cs : List Char) (n : Int)
    (hnoslash : cs.all (fun c => c != '/') = true)
    (hn : SourceJson.intChars cs = some n) :
    parseRational (String.ofList cs) = .ok (n : ℚ) := by
  have ht : cs.takeWhile (fun c => c != '/') = cs := by
    simpa using (List.takeWhile_append_of_pos (l₂ := ([] : List Char))
      (List.all_eq_true.mp hnoslash))
  simp only [parseRational, String.toList_ofList, ht, List.drop_length,
    parseInteger, hn]
  rfl

theorem original_rationalField_of_string
    (j : SourceJson) (key text : String) (value : ℚ)
    (hfield : j.getObjVal? key = .ok (.str text))
    (hvalue : parseRational text = .ok value) :
    rationalField j key = .ok value := by
  unfold rationalField jsonRational
  rw [hfield]
  exact hvalue

theorem original_geometryRow_of_fields
    (j : SourceJson) (r : GeometryRow) (floorText : String)
    (hid : j.getObjValAs? Nat "simplex_id" = .ok r.simplexId)
    (hids : j.getObjValAs? (Array Nat) "vertex_ids" = .ok r.vertexIds)
    (hvolume : rationalField j "physical_volume" = .ok r.physicalVolume)
    (hgap : rationalField j "mean_gap" = .ok r.meanGap)
    (hmaxima : rationalArrayField j "factor_maxima" = .ok r.factorMaxima)
    (hmeans : rationalArrayField j "gap_weighted_means" = .ok r.gapWeightedMeans)
    (hjensen : rationalField j "jensen_bound" = .ok r.jensenBound)
    (hfloorText : j.getObjValAs? String "jensen_floor_Q96" = .ok floorText)
    (hfloor : parseInteger floorText = .ok r.jensenFloorQ96) :
    decodeGeometryRow j = .ok r := by
  cases r
  simp only [decodeGeometryRow, hid, hids, hvolume, hgap, hmaxima, hmeans,
    hjensen, hfloorText, hfloor, bind, Except.bind]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED rational_chars_generic_complete"
  err.flush

#print axioms original_rational_fraction_of_chars
#print axioms original_rational_integer_of_chars
#print axioms original_rationalField_of_string
#print axioms original_geometryRow_of_fields
end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
