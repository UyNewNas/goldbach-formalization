import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableVertexValuesBlock000

/-! Local original vertex_values decoding, indices 0 through 7.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryVertexValuesJson000 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped000 : VertexValues :=
  { gap := ((1452881 : ℚ) / (220000000 : ℚ)),
    factors := #[((18890533 : ℚ) / (220000000 : ℚ)), ((10171707 : ℚ) / (110000000 : ℚ)), ((2390621 : ℚ) / (22000000 : ℚ)), ((10015637 : ℚ) / (110000000 : ℚ)), ((10015637 : ℚ) / (110000000 : ℚ)), ((734379 : ℚ) / (10000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((3390569 : ℚ) / (110000000 : ℚ))] }

theorem decode_geometry_VertexValues_000 : decodeVertexValues geometryVertexValuesJson000 = .ok geometryVertexValuesTyped000 := by decide +kernel

theorem geometryVertexValues_000_shape : geometryVertexValuesTyped000.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson001 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped001 : VertexValues :=
  { gap := ((328073 : ℚ) / (49000000 : ℚ)),
    factors := #[((853127 : ℚ) / (9800000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((4265621 : ℚ) / (39200000 : ℚ)), ((17828137 : ℚ) / (196000000 : ℚ)), ((17828137 : ℚ) / (196000000 : ℚ)), ((14328169 : ℚ) / (196000000 : ℚ)), ((7328233 : ℚ) / (196000000 : ℚ)), ((54687 : ℚ) / (1531250 : ℚ)), ((54687 : ℚ) / (1531250 : ℚ)), ((54687 : ℚ) / (1750000 : ℚ))] }

theorem decode_geometry_VertexValues_001 : decodeVertexValues geometryVertexValuesJson001 = .ok geometryVertexValuesTyped001 := by decide +kernel

theorem geometryVertexValues_001_shape : geometryVertexValuesTyped001.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson002 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped002 : VertexValues :=
  { gap := ((496799 : ℚ) / (73600000 : ℚ)),
    factors := #[((32297087 : ℚ) / (368000000 : ℚ)), ((17390541 : ℚ) / (184000000 : ℚ)), ((8015621 : ℚ) / (73600000 : ℚ)), ((33453137 : ℚ) / (368000000 : ℚ)), ((33453137 : ℚ) / (368000000 : ℚ)), ((26828169 : ℚ) / (368000000 : ℚ)), ((828121 : ℚ) / (23000000 : ℚ)), ((828121 : ℚ) / (23000000 : ℚ)), ((828121 : ℚ) / (23000000 : ℚ)), ((5796847 : ℚ) / (184000000 : ℚ))] }

theorem decode_geometry_VertexValues_002 : decodeVertexValues geometryVertexValuesJson002 = .ok geometryVertexValuesTyped002 := by decide +kernel

theorem geometryVertexValues_002_shape : geometryVertexValuesTyped002.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson003 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped003 : VertexValues :=
  { gap := ((1171703 : ℚ) / (172000000 : ℚ)),
    factors := #[((15234547 : ℚ) / (172000000 : ℚ)), ((525 : ℚ) / (5504 : ℚ)), ((75 : ℚ) / (688 : ℚ)), ((125 : ℚ) / (1376 : ℚ)), ((125 : ℚ) / (1376 : ℚ)), ((25 : ℚ) / (344 : ℚ)), ((25 : ℚ) / (688 : ℚ)), ((25 : ℚ) / (688 : ℚ)), ((5921703 : ℚ) / (172000000 : ℚ)), ((175 : ℚ) / (5504 : ℚ))] }

theorem decode_geometry_VertexValues_003 : decodeVertexValues geometryVertexValuesJson003 = .ok geometryVertexValuesTyped003 := by decide +kernel

theorem geometryVertexValues_003_shape : geometryVertexValuesTyped003.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson004 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped004 : VertexValues :=
  { gap := ((984203 : ℚ) / (150500000 : ℚ)),
    factors := #[((13125043 : ℚ) / (150500000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((75 : ℚ) / (688 : ℚ)), ((125 : ℚ) / (1376 : ℚ)), ((125 : ℚ) / (1376 : ℚ)), ((25 : ℚ) / (344 : ℚ)), ((25 : ℚ) / (688 : ℚ)), ((25 : ℚ) / (688 : ℚ)), ((25 : ℚ) / (688 : ℚ)), ((54687 : ℚ) / (1750000 : ℚ))] }

theorem decode_geometry_VertexValues_004 : decodeVertexValues geometryVertexValuesJson004 = .ok geometryVertexValuesTyped004 := by decide +kernel

theorem geometryVertexValues_004_shape : geometryVertexValuesTyped004.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson005 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped005 : VertexValues :=
  { gap := ((1171703 : ℚ) / (172000000 : ℚ)),
    factors := #[((477 : ℚ) / (5504 : ℚ)), ((16077953 : ℚ) / (172000000 : ℚ)), ((75 : ℚ) / (688 : ℚ)), ((125 : ℚ) / (1376 : ℚ)), ((125 : ℚ) / (1376 : ℚ)), ((25 : ℚ) / (344 : ℚ)), ((25 : ℚ) / (688 : ℚ)), ((25 : ℚ) / (688 : ℚ)), ((25 : ℚ) / (688 : ℚ)), ((175 : ℚ) / (5504 : ℚ))] }

theorem decode_geometry_VertexValues_005 : decodeVertexValues geometryVertexValuesJson005 = .ok geometryVertexValuesTyped005 := by decide +kernel

theorem geometryVertexValues_005_shape : geometryVertexValuesTyped005.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson006 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped006 : VertexValues :=
  { gap := ((5389757 : ℚ) / (808000000 : ℚ)),
    factors := #[((70078153 : ℚ) / (808000000 : ℚ)), ((7546791 : ℚ) / (80800000 : ℚ)), ((44109411 : ℚ) / (404000000 : ℚ)), ((36921991 : ℚ) / (404000000 : ℚ)), ((18296847 : ℚ) / (202000000 : ℚ)), ((14703137 : ℚ) / (202000000 : ℚ)), ((14703137 : ℚ) / (404000000 : ℚ)), ((14703137 : ℚ) / (404000000 : ℚ)), ((14703137 : ℚ) / (404000000 : ℚ)), ((2515597 : ℚ) / (80800000 : ℚ))] }

theorem decode_geometry_VertexValues_006 : decodeVertexValues geometryVertexValuesJson006 = .ok geometryVertexValuesTyped006 := by decide +kernel

theorem geometryVertexValues_006_shape : geometryVertexValuesTyped006.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson007 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped007 : VertexValues :=
  { gap := ((546807 : ℚ) / (88000000 : ℚ)),
    factors := #[((8015629 : ℚ) / (88000000 : ℚ)), ((2140609 : ℚ) / (22000000 : ℚ)), ((4828113 : ℚ) / (44000000 : ℚ)), ((5921903 : ℚ) / (66000000 : ℚ)), ((5921903 : ℚ) / (66000000 : ℚ)), ((1609371 : ℚ) / (22000000 : ℚ)), ((1609371 : ℚ) / (44000000 : ℚ)), ((1609371 : ℚ) / (44000000 : ℚ)), ((2140609 : ℚ) / (66000000 : ℚ)), ((2140609 : ℚ) / (66000000 : ℚ))] }

theorem decode_geometry_VertexValues_007 : decodeVertexValues geometryVertexValuesJson007 = .ok geometryVertexValuesTyped007 := by decide +kernel

theorem geometryVertexValues_007_shape : geometryVertexValuesTyped007.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJsonBlock000 : List SourceJson := [geometryVertexValuesJson000, geometryVertexValuesJson001, geometryVertexValuesJson002, geometryVertexValuesJson003, geometryVertexValuesJson004, geometryVertexValuesJson005, geometryVertexValuesJson006, geometryVertexValuesJson007]
noncomputable def geometryVertexValuesTypedBlock000 : List (VertexValues) := [geometryVertexValuesTyped000, geometryVertexValuesTyped001, geometryVertexValuesTyped002, geometryVertexValuesTyped003, geometryVertexValuesTyped004, geometryVertexValuesTyped005, geometryVertexValuesTyped006, geometryVertexValuesTyped007]

theorem geometry_VertexValues_block_000_push_eq (acc : List SourceJson) :
    VertexValuesBlock000.blockPush acc = [geometryVertexValuesJson007, geometryVertexValuesJson006, geometryVertexValuesJson005, geometryVertexValuesJson004, geometryVertexValuesJson003, geometryVertexValuesJson002, geometryVertexValuesJson001, geometryVertexValuesJson000] ++ acc := by rfl

theorem geometry_VertexValues_block_000_reverse (acc : List SourceJson) :
    (VertexValuesBlock000.blockPush acc).reverse = acc.reverse ++ geometryVertexValuesJsonBlock000 := by
  rw [geometry_VertexValues_block_000_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_VertexValues_block_000 : geometryVertexValuesJsonBlock000.mapM decodeVertexValues = .ok geometryVertexValuesTypedBlock000 := by
  simp only [geometryVertexValuesJsonBlock000, geometryVertexValuesTypedBlock000, List.mapM_cons, List.mapM_nil,
    decode_geometry_VertexValues_000, decode_geometry_VertexValues_001, decode_geometry_VertexValues_002, decode_geometry_VertexValues_003, decode_geometry_VertexValues_004, decode_geometry_VertexValues_005, decode_geometry_VertexValues_006, decode_geometry_VertexValues_007]
  rfl

theorem geometry_VertexValues_block_000_length : geometryVertexValuesTypedBlock000.length = 8 := by rfl

#print axioms decode_geometry_VertexValues_000
#print axioms geometryVertexValues_000_shape
#print axioms decode_geometry_VertexValues_001
#print axioms geometryVertexValues_001_shape
#print axioms decode_geometry_VertexValues_002
#print axioms geometryVertexValues_002_shape
#print axioms decode_geometry_VertexValues_003
#print axioms geometryVertexValues_003_shape
#print axioms decode_geometry_VertexValues_004
#print axioms geometryVertexValues_004_shape
#print axioms decode_geometry_VertexValues_005
#print axioms geometryVertexValues_005_shape
#print axioms decode_geometry_VertexValues_006
#print axioms geometryVertexValues_006_shape
#print axioms decode_geometry_VertexValues_007
#print axioms geometryVertexValues_007_shape
#print axioms geometry_VertexValues_block_000_push_eq
#print axioms geometry_VertexValues_block_000_reverse
#print axioms decode_geometry_VertexValues_block_000
#print axioms geometry_VertexValues_block_000_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
