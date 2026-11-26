import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableVertexValuesBlock003

/-! Local original vertex_values decoding, indices 24 through 27.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryVertexValuesJson024 : SourceJson :=
  (VertexValuesBlock003.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped024 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2765797 : ℚ) / (36000000 : ℚ)), ((2765797 : ℚ) / (36000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((1171879 : ℚ) / (12000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((234379 : ℚ) / (3600000 : ℚ)), ((1171943 : ℚ) / (36000000 : ℚ)), ((1171847 : ℚ) / (36000000 : ℚ)), ((1171823 : ℚ) / (36000000 : ℚ)), ((1171823 : ℚ) / (36000000 : ℚ))] }

theorem decode_geometry_VertexValues_024 : decodeVertexValues geometryVertexValuesJson024 = .ok geometryVertexValuesTyped024 := by decide +kernel

theorem geometryVertexValues_024_shape : geometryVertexValuesTyped024.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson025 : SourceJson :=
  (VertexValuesBlock003.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped025 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2765773 : ℚ) / (36000000 : ℚ)), ((2765773 : ℚ) / (36000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((1171879 : ℚ) / (12000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((234379 : ℚ) / (3600000 : ℚ)), ((1171943 : ℚ) / (36000000 : ℚ)), ((1171847 : ℚ) / (36000000 : ℚ)), ((1171847 : ℚ) / (36000000 : ℚ)), ((1171823 : ℚ) / (36000000 : ℚ))] }

theorem decode_geometry_VertexValues_025 : decodeVertexValues geometryVertexValuesJson025 = .ok geometryVertexValuesTyped025 := by decide +kernel

theorem geometryVertexValues_025_shape : geometryVertexValuesTyped025.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson026 : SourceJson :=
  (VertexValuesBlock003.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped026 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((5109443 : ℚ) / (60000000 : ℚ)), ((5109443 : ℚ) / (60000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327857 : ℚ) / (180000000 : ℚ)), ((16828033 : ℚ) / (180000000 : ℚ)), ((234379 : ℚ) / (3600000 : ℚ)), ((2203129 : ℚ) / (60000000 : ℚ)), ((5109563 : ℚ) / (180000000 : ℚ)), ((5109443 : ℚ) / (180000000 : ℚ)), ((5109443 : ℚ) / (180000000 : ℚ))] }

theorem decode_geometry_VertexValues_026 : decodeVertexValues geometryVertexValuesJson026 = .ok geometryVertexValuesTyped026 := by decide +kernel

theorem geometryVertexValues_026_shape : geometryVertexValuesTyped026.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson027 : SourceJson :=
  (VertexValuesBlock003.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped027 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((5109419 : ℚ) / (60000000 : ℚ)), ((5109419 : ℚ) / (60000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((16828009 : ℚ) / (180000000 : ℚ)), ((234379 : ℚ) / (3600000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((5109539 : ℚ) / (180000000 : ℚ)), ((5109539 : ℚ) / (180000000 : ℚ)), ((5109419 : ℚ) / (180000000 : ℚ))] }

theorem decode_geometry_VertexValues_027 : decodeVertexValues geometryVertexValuesJson027 = .ok geometryVertexValuesTyped027 := by decide +kernel

theorem geometryVertexValues_027_shape : geometryVertexValuesTyped027.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJsonBlock003 : List SourceJson := [geometryVertexValuesJson024, geometryVertexValuesJson025, geometryVertexValuesJson026, geometryVertexValuesJson027]
noncomputable def geometryVertexValuesTypedBlock003 : List (VertexValues) := [geometryVertexValuesTyped024, geometryVertexValuesTyped025, geometryVertexValuesTyped026, geometryVertexValuesTyped027]

theorem geometry_VertexValues_block_003_push_eq (acc : List SourceJson) :
    VertexValuesBlock003.blockPush acc = [geometryVertexValuesJson027, geometryVertexValuesJson026, geometryVertexValuesJson025, geometryVertexValuesJson024] ++ acc := by rfl

theorem geometry_VertexValues_block_003_reverse (acc : List SourceJson) :
    (VertexValuesBlock003.blockPush acc).reverse = acc.reverse ++ geometryVertexValuesJsonBlock003 := by
  rw [geometry_VertexValues_block_003_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_VertexValues_block_003 : geometryVertexValuesJsonBlock003.mapM decodeVertexValues = .ok geometryVertexValuesTypedBlock003 := by
  simp only [geometryVertexValuesJsonBlock003, geometryVertexValuesTypedBlock003, List.mapM_cons, List.mapM_nil,
    decode_geometry_VertexValues_024, decode_geometry_VertexValues_025, decode_geometry_VertexValues_026, decode_geometry_VertexValues_027]
  rfl

theorem geometry_VertexValues_block_003_length : geometryVertexValuesTypedBlock003.length = 4 := by rfl

#print axioms decode_geometry_VertexValues_024
#print axioms geometryVertexValues_024_shape
#print axioms decode_geometry_VertexValues_025
#print axioms geometryVertexValues_025_shape
#print axioms decode_geometry_VertexValues_026
#print axioms geometryVertexValues_026_shape
#print axioms decode_geometry_VertexValues_027
#print axioms geometryVertexValues_027_shape
#print axioms geometry_VertexValues_block_003_push_eq
#print axioms geometry_VertexValues_block_003_reverse
#print axioms decode_geometry_VertexValues_block_003
#print axioms geometry_VertexValues_block_003_length
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
