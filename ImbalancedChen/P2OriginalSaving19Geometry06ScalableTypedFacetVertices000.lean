import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableFacetVerticesBlock000

/-! Local original facet_vertices decoding, indices 0 through 10.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacetVerticesJson000 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨10, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped000 : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 21, 22, 23, 24, 25, 26, 27, 28, 31, 32]

theorem decode_geometry_FacetVertices_000 : (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson000 = .ok geometryFacetVerticesTyped000 := by decide +kernel

theorem geometryFacetVertices_000_shape : geometryFacetVerticesTyped000.size = 28 ∧ geometryFacetVerticesTyped000.toList.Nodup ∧
    (∀ i : Fin 28, geometryFacetVerticesTyped000[i.val]! < 33) := by decide +kernel

noncomputable def geometryFacetVerticesJson001 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨9, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped001 : Array Nat :=
  #[0, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 27, 28, 29, 30, 31, 32]

theorem decode_geometry_FacetVertices_001 : (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson001 = .ok geometryFacetVerticesTyped001 := by decide +kernel

theorem geometryFacetVertices_001_shape : geometryFacetVerticesTyped001.size = 28 ∧ geometryFacetVerticesTyped001.toList.Nodup ∧
    (∀ i : Fin 28, geometryFacetVerticesTyped001[i.val]! < 33) := by decide +kernel

noncomputable def geometryFacetVerticesJson002 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨8, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped002 : Array Nat :=
  #[0, 1, 2, 4, 5, 6, 8, 10, 13, 15, 18, 20, 21, 22, 23, 27, 29, 32]

theorem decode_geometry_FacetVertices_002 : (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson002 = .ok geometryFacetVerticesTyped002 := by decide +kernel

theorem geometryFacetVertices_002_shape : geometryFacetVerticesTyped002.size = 18 ∧ geometryFacetVerticesTyped002.toList.Nodup ∧
    (∀ i : Fin 18, geometryFacetVerticesTyped002[i.val]! < 33) := by decide +kernel

noncomputable def geometryFacetVerticesJson003 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped003 : Array Nat :=
  #[7, 9, 11, 12, 14, 16, 17, 19, 24, 25, 26, 28, 30, 31]

theorem decode_geometry_FacetVertices_003 : (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson003 = .ok geometryFacetVerticesTyped003 := by decide +kernel

theorem geometryFacetVertices_003_shape : geometryFacetVerticesTyped003.size = 14 ∧ geometryFacetVerticesTyped003.toList.Nodup ∧
    (∀ i : Fin 14, geometryFacetVerticesTyped003[i.val]! < 33) := by decide +kernel

noncomputable def geometryFacetVerticesJson004 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped004 : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 9, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]

theorem decode_geometry_FacetVertices_004 : (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson004 = .ok geometryFacetVerticesTyped004 := by decide +kernel

theorem geometryFacetVertices_004_shape : geometryFacetVerticesTyped004.size = 20 ∧ geometryFacetVerticesTyped004.toList.Nodup ∧
    (∀ i : Fin 20, geometryFacetVerticesTyped004[i.val]! < 33) := by decide +kernel

noncomputable def geometryFacetVerticesJson005 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped005 : Array Nat :=
  #[8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]

theorem decode_geometry_FacetVertices_005 : (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson005 = .ok geometryFacetVerticesTyped005 := by decide +kernel

theorem geometryFacetVertices_005_shape : geometryFacetVerticesTyped005.size = 24 ∧ geometryFacetVerticesTyped005.toList.Nodup ∧
    (∀ i : Fin 24, geometryFacetVerticesTyped005[i.val]! < 33) := by decide +kernel

noncomputable def geometryFacetVerticesJson006 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped006 : Array Nat :=
  #[0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 18, 19, 20, 21, 23, 25, 26, 27, 28, 29, 30, 31, 32]

theorem decode_geometry_FacetVertices_006 : (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson006 = .ok geometryFacetVerticesTyped006 := by decide +kernel

theorem geometryFacetVertices_006_shape : geometryFacetVerticesTyped006.size = 28 ∧ geometryFacetVerticesTyped006.toList.Nodup ∧
    (∀ i : Fin 28, geometryFacetVerticesTyped006[i.val]! < 33) := by decide +kernel

noncomputable def geometryFacetVerticesJson007 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped007 : Array Nat :=
  #[0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]

theorem decode_geometry_FacetVertices_007 : (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson007 = .ok geometryFacetVerticesTyped007 := by decide +kernel

theorem geometryFacetVertices_007_shape : geometryFacetVerticesTyped007.size = 28 ∧ geometryFacetVerticesTyped007.toList.Nodup ∧
    (∀ i : Fin 28, geometryFacetVerticesTyped007[i.val]! < 33) := by decide +kernel

noncomputable def geometryFacetVerticesJson008 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped008 : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

theorem decode_geometry_FacetVertices_008 : (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson008 = .ok geometryFacetVerticesTyped008 := by decide +kernel

theorem geometryFacetVertices_008_shape : geometryFacetVerticesTyped008.size = 20 ∧ geometryFacetVerticesTyped008.toList.Nodup ∧
    (∀ i : Fin 20, geometryFacetVerticesTyped008[i.val]! < 33) := by decide +kernel

noncomputable def geometryFacetVerticesJson009 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped009 : Array Nat :=
  #[1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 26, 27, 28, 29, 30, 31, 32]

theorem decode_geometry_FacetVertices_009 : (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson009 = .ok geometryFacetVerticesTyped009 := by decide +kernel

theorem geometryFacetVertices_009_shape : geometryFacetVerticesTyped009.size = 28 ∧ geometryFacetVerticesTyped009.toList.Nodup ∧
    (∀ i : Fin 28, geometryFacetVerticesTyped009[i.val]! < 33) := by decide +kernel

noncomputable def geometryFacetVerticesJson010 : SourceJson :=
  (FacetVerticesBlock000.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacetVerticesTyped010 : Array Nat :=
  #[0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 29, 30, 31, 32]

theorem decode_geometry_FacetVertices_010 : (SourceJson.Decode.read (α := Array Nat)) geometryFacetVerticesJson010 = .ok geometryFacetVerticesTyped010 := by decide +kernel

theorem geometryFacetVertices_010_shape : geometryFacetVerticesTyped010.size = 28 ∧ geometryFacetVerticesTyped010.toList.Nodup ∧
    (∀ i : Fin 28, geometryFacetVerticesTyped010[i.val]! < 33) := by decide +kernel

noncomputable def geometryFacetVerticesJsonBlock000 : List SourceJson := [geometryFacetVerticesJson000, geometryFacetVerticesJson001, geometryFacetVerticesJson002, geometryFacetVerticesJson003, geometryFacetVerticesJson004, geometryFacetVerticesJson005, geometryFacetVerticesJson006, geometryFacetVerticesJson007, geometryFacetVerticesJson008, geometryFacetVerticesJson009, geometryFacetVerticesJson010]
noncomputable def geometryFacetVerticesTypedBlock000 : List (Array Nat) := [geometryFacetVerticesTyped000, geometryFacetVerticesTyped001, geometryFacetVerticesTyped002, geometryFacetVerticesTyped003, geometryFacetVerticesTyped004, geometryFacetVerticesTyped005, geometryFacetVerticesTyped006, geometryFacetVerticesTyped007, geometryFacetVerticesTyped008, geometryFacetVerticesTyped009, geometryFacetVerticesTyped010]

theorem geometry_FacetVertices_block_000_push_eq (acc : List SourceJson) :
    FacetVerticesBlock000.blockPush acc = [geometryFacetVerticesJson010, geometryFacetVerticesJson009, geometryFacetVerticesJson008, geometryFacetVerticesJson007, geometryFacetVerticesJson006, geometryFacetVerticesJson005, geometryFacetVerticesJson004, geometryFacetVerticesJson003, geometryFacetVerticesJson002, geometryFacetVerticesJson001, geometryFacetVerticesJson000] ++ acc := by rfl

theorem geometry_FacetVertices_block_000_reverse (acc : List SourceJson) :
    (FacetVerticesBlock000.blockPush acc).reverse = acc.reverse ++ geometryFacetVerticesJsonBlock000 := by
  rw [geometry_FacetVertices_block_000_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_FacetVertices_block_000 : geometryFacetVerticesJsonBlock000.mapM (SourceJson.Decode.read (α := Array Nat)) = .ok geometryFacetVerticesTypedBlock000 := by
  simp only [geometryFacetVerticesJsonBlock000, geometryFacetVerticesTypedBlock000, List.mapM_cons, List.mapM_nil,
    decode_geometry_FacetVertices_000, decode_geometry_FacetVertices_001, decode_geometry_FacetVertices_002, decode_geometry_FacetVertices_003, decode_geometry_FacetVertices_004, decode_geometry_FacetVertices_005, decode_geometry_FacetVertices_006, decode_geometry_FacetVertices_007, decode_geometry_FacetVertices_008, decode_geometry_FacetVertices_009, decode_geometry_FacetVertices_010]
  rfl

theorem geometry_FacetVertices_block_000_length : geometryFacetVerticesTypedBlock000.length = 11 := by rfl

#print axioms decode_geometry_FacetVertices_000
#print axioms geometryFacetVertices_000_shape
#print axioms decode_geometry_FacetVertices_001
#print axioms geometryFacetVertices_001_shape
#print axioms decode_geometry_FacetVertices_002
#print axioms geometryFacetVertices_002_shape
#print axioms decode_geometry_FacetVertices_003
#print axioms geometryFacetVertices_003_shape
#print axioms decode_geometry_FacetVertices_004
#print axioms geometryFacetVertices_004_shape
#print axioms decode_geometry_FacetVertices_005
#print axioms geometryFacetVertices_005_shape
#print axioms decode_geometry_FacetVertices_006
#print axioms geometryFacetVertices_006_shape
#print axioms decode_geometry_FacetVertices_007
#print axioms geometryFacetVertices_007_shape
#print axioms decode_geometry_FacetVertices_008
#print axioms geometryFacetVertices_008_shape
#print axioms decode_geometry_FacetVertices_009
#print axioms geometryFacetVertices_009_shape
#print axioms decode_geometry_FacetVertices_010
#print axioms geometryFacetVertices_010_shape
#print axioms geometry_FacetVertices_block_000_push_eq
#print axioms geometry_FacetVertices_block_000_reverse
#print axioms decode_geometry_FacetVertices_block_000
#print axioms geometry_FacetVertices_block_000_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
