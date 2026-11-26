import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectFacetVerticesValue

/-! Original facet_vertices typed block 0, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacetVerticesJson000 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨11, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped000 : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 25, 26, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_000_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_000 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson000 = .ok geometryFacetVerticesTyped000 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_000_decoded"
  err.flush

noncomputable def geometryFacetVerticesJson001 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨10, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped001 : Array Nat :=
  #[0, 2, 4, 6, 7, 9, 12, 14, 15, 17, 18, 19, 22, 26, 27, 31, 33, 35, 37, 39]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_001_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_001 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson001 = .ok geometryFacetVerticesTyped001 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_001_decoded"
  err.flush

noncomputable def geometryFacetVerticesJson002 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨9, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped002 : Array Nat :=
  #[1, 3, 5, 8, 10, 11, 13, 16, 20, 21, 23, 24, 25, 28, 29, 30, 32, 34, 36, 38]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_002_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_002 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson002 = .ok geometryFacetVerticesTyped002 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_002_decoded"
  err.flush

noncomputable def geometryFacetVerticesJson003 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨8, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped003 : Array Nat :=
  #[14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 30, 31, 32, 33]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_003_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_003 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson003 = .ok geometryFacetVerticesTyped003 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_003_decoded"
  err.flush

noncomputable def geometryFacetVerticesJson004 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped004 : Array Nat :=
  #[4, 5, 12, 13, 17, 25, 26, 27, 28, 29, 34, 35, 38, 39]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_004_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_004 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson004 = .ok geometryFacetVerticesTyped004 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_004_decoded"
  err.flush

noncomputable def geometryFacetVerticesJson005 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped005 : Array Nat :=
  #[0, 1, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_005_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_005 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson005 = .ok geometryFacetVerticesTyped005 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_005_decoded"
  err.flush

noncomputable def geometryFacetVerticesJson006 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped006 : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 22, 23, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_006_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_006 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson006 = .ok geometryFacetVerticesTyped006 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_006_decoded"
  err.flush

noncomputable def geometryFacetVerticesJson007 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped007 : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 17, 25, 26, 27, 28, 29, 36, 37, 38, 39]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_007_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_007 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson007 = .ok geometryFacetVerticesTyped007 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_007_decoded"
  err.flush

noncomputable def geometryFacetVerticesJson008 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped008 : Array Nat :=
  #[0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 30, 31, 36, 37]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_008_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_008 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson008 = .ok geometryFacetVerticesTyped008 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_008_decoded"
  err.flush

noncomputable def geometryFacetVerticesJson009 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped009 : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 8, 9, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_009_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_009 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson009 = .ok geometryFacetVerticesTyped009 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_009_decoded"
  err.flush

noncomputable def geometryFacetVerticesJson010 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped010 : Array Nat :=
  #[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_010_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_010 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson010 = .ok geometryFacetVerticesTyped010 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_010_decoded"
  err.flush

noncomputable def geometryFacetVerticesJson011 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped011 : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_011_before_decode"
  err.flush

theorem decode_geometry_FacetVertices_011 :
    (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson011 = .ok geometryFacetVerticesTyped011 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_011_decoded"
  err.flush

noncomputable def geometryFacetVerticesJsonBlock000 : List SourceJson := [geometryFacetVerticesJson000, geometryFacetVerticesJson001, geometryFacetVerticesJson002, geometryFacetVerticesJson003, geometryFacetVerticesJson004, geometryFacetVerticesJson005, geometryFacetVerticesJson006, geometryFacetVerticesJson007, geometryFacetVerticesJson008, geometryFacetVerticesJson009, geometryFacetVerticesJson010, geometryFacetVerticesJson011]
noncomputable def geometryFacetVerticesTypedBlock000 : List (Array Nat) := [geometryFacetVerticesTyped000, geometryFacetVerticesTyped001, geometryFacetVerticesTyped002, geometryFacetVerticesTyped003, geometryFacetVerticesTyped004, geometryFacetVerticesTyped005, geometryFacetVerticesTyped006, geometryFacetVerticesTyped007, geometryFacetVerticesTyped008, geometryFacetVerticesTyped009, geometryFacetVerticesTyped010, geometryFacetVerticesTyped011]
noncomputable def geometryFacetVerticesTypedThroughBlock000 : List (Array Nat) := geometryFacetVerticesTypedBlock000

theorem geometry_FacetVertices_block_000_push_eq (acc : List SourceJson) :
    FacetVerticesBlock000.blockPush acc = [geometryFacetVerticesJson011, geometryFacetVerticesJson010, geometryFacetVerticesJson009, geometryFacetVerticesJson008, geometryFacetVerticesJson007, geometryFacetVerticesJson006, geometryFacetVerticesJson005, geometryFacetVerticesJson004, geometryFacetVerticesJson003, geometryFacetVerticesJson002, geometryFacetVerticesJson001, geometryFacetVerticesJson000] ++ acc := by rfl

theorem geometry_FacetVertices_block_000_reverse (acc : List SourceJson) :
    (FacetVerticesBlock000.blockPush acc).reverse = acc.reverse ++ geometryFacetVerticesJsonBlock000 := by
  rw [geometry_FacetVertices_block_000_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_FacetVertices_block_000 :
    geometryFacetVerticesJsonBlock000.mapM (SourceJson.Decode.read (α := Array Nat)) = .ok geometryFacetVerticesTypedBlock000 := by
  simp only [geometryFacetVerticesJsonBlock000, geometryFacetVerticesTypedBlock000, List.mapM_cons, List.mapM_nil,
    decode_geometry_FacetVertices_000, decode_geometry_FacetVertices_001, decode_geometry_FacetVertices_002, decode_geometry_FacetVertices_003, decode_geometry_FacetVertices_004, decode_geometry_FacetVertices_005, decode_geometry_FacetVertices_006, decode_geometry_FacetVertices_007, decode_geometry_FacetVertices_008, decode_geometry_FacetVertices_009, decode_geometry_FacetVertices_010, decode_geometry_FacetVertices_011]
  rfl

theorem decode_geometry_FacetVertices_through_block_000 :
    FacetVerticesValue.arrayAcc001.reverse.mapM (SourceJson.Decode.read (α := Array Nat)) = .ok geometryFacetVerticesTypedThroughBlock000 := by
  change (FacetVerticesBlock000.blockPush FacetVerticesValue.arrayAcc000).reverse.mapM (SourceJson.Decode.read (α := Array Nat)) = _
  rw [geometry_FacetVertices_block_000_reverse]
  exact decode_geometry_FacetVertices_block_000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED FacetVertices_block_000_complete"
  err.flush

#print axioms decode_geometry_FacetVertices_000
#print axioms decode_geometry_FacetVertices_001
#print axioms decode_geometry_FacetVertices_002
#print axioms decode_geometry_FacetVertices_003
#print axioms decode_geometry_FacetVertices_004
#print axioms decode_geometry_FacetVertices_005
#print axioms decode_geometry_FacetVertices_006
#print axioms decode_geometry_FacetVertices_007
#print axioms decode_geometry_FacetVertices_008
#print axioms decode_geometry_FacetVertices_009
#print axioms decode_geometry_FacetVertices_010
#print axioms decode_geometry_FacetVertices_011
#print axioms geometry_FacetVertices_block_000_push_eq
#print axioms geometry_FacetVertices_block_000_reverse
#print axioms decode_geometry_FacetVertices_block_000
#print axioms decode_geometry_FacetVertices_through_block_000

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
