import ImbalancedChen.P2OriginalSaving16DecoderChars
import ImbalancedChen.P2Saving16Cell00TypedPayload

/-!
Exact scalar decoding certificates for the proposed cell00 payload.
Each statement is checked against the unchanged original decoder; the
character representation equations only remove proved string round trips.
-/
namespace ImbalancedChen.P2Saving16Cell00ScalarDecode
open P2OriginalSaving16OriginalArchive
open P2Saving16Cell00TypedPayload

theorem rational000_decoded :
    parseRational (String.ofList ['1']) = .ok rational000 := by
  rw [parseRational_ofList]
  rfl

theorem rational001_decoded :
    parseRational (String.ofList ['8', '/', '7']) = .ok rational001 := by
  rw [parseRational_ofList]
  rfl

theorem rational002_decoded :
    parseRational (String.ofList ['1', '6', '/', '7']) = .ok rational002 := by
  rw [parseRational_ofList]
  rfl

theorem rational003_decoded :
    parseRational (String.ofList ['1', '/', '7']) = .ok rational003 := by
  rw [parseRational_ofList]
  rfl

theorem rational004_decoded :
    parseRational (String.ofList ['4', '0', '/', '7']) = .ok rational004 := by
  rw [parseRational_ofList]
  rfl

theorem rational005_decoded :
    parseRational (String.ofList ['2', '0', '/', '7']) = .ok rational005 := by
  rw [parseRational_ofList]
  rfl

theorem rational006_decoded :
    parseRational (String.ofList ['6', '/', '7']) = .ok rational006 := by
  rw [parseRational_ofList]
  rfl

theorem rational007_decoded :
    parseRational (String.ofList ['3', '4', '/', '2', '1']) = .ok rational007 := by
  rw [parseRational_ofList]
  rfl

theorem rational008_decoded :
    parseRational (String.ofList ['4']) = .ok rational008 := by
  rw [parseRational_ofList]
  rfl

theorem rational009_decoded :
    parseRational (String.ofList ['5', '8', '5', '9', '4', '2', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']) = .ok rational009 := by
  rw [parseRational_ofList]
  rfl

theorem rational010_decoded :
    parseRational (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok rational010 := by
  rw [parseRational_ofList]
  rfl

theorem rational011_decoded :
    parseRational (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']) = .ok rational011 := by
  rw [parseRational_ofList]
  rfl

theorem rational012_decoded :
    parseRational (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0']) = .ok rational012 := by
  rw [parseRational_ofList]
  rfl

theorem rational013_decoded :
    parseRational (String.ofList ['1', '3', '1', '6', '7', '3', '/', '8', '0', '0', '0', '0', '0']) = .ok rational013 := by
  rw [parseRational_ofList]
  rfl

theorem rational014_decoded :
    parseRational (String.ofList ['7', '8', '4', '6', '3', '/', '8', '0', '0', '0', '0', '0']) = .ok rational014 := by
  rw [parseRational_ofList]
  rfl

theorem rational015_decoded :
    parseRational (String.ofList ['2', '5', '2', '5', '3', '/', '8', '0', '0', '0', '0', '0']) = .ok rational015 := by
  rw [parseRational_ofList]
  rfl

theorem rational016_decoded :
    parseRational (String.ofList ['1', '1', '2', '7', '5', '3', '/', '4', '0', '0', '0', '0', '0', '0']) = .ok rational016 := by
  rw [parseRational_ofList]
  rfl

theorem rational017_decoded :
    parseRational (String.ofList ['2', '0', '4', '5', '3', '2', '2', '9', '/', '1', '2', '4', '0', '0', '0', '0', '0', '0']) = .ok rational017 := by
  rw [parseRational_ofList]
  rfl

theorem rational018_decoded :
    parseRational (String.ofList ['1', '2', '1', '7', '1', '8', '9', '9', '/', '1', '2', '4', '0', '0', '0', '0', '0', '0']) = .ok rational018 := by
  rw [parseRational_ofList]
  rfl

theorem rational019_decoded :
    parseRational (String.ofList ['3', '8', '9', '0', '5', '6', '9', '/', '1', '2', '4', '0', '0', '0', '0', '0', '0']) = .ok rational019 := by
  rw [parseRational_ofList]
  rfl

theorem rational020_decoded :
    parseRational (String.ofList ['7', '/', '2', '5', '6']) = .ok rational020 := by
  rw [parseRational_ofList]
  rfl

theorem rational021_decoded :
    parseRational (String.ofList ['1', '3', '9', '2', '1', '9', '1', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']) = .ok rational021 := by
  rw [parseRational_ofList]
  rfl

theorem rational022_decoded :
    parseRational (String.ofList ['8', '2', '8', '1', '2', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']) = .ok rational022 := by
  rw [parseRational_ofList]
  rfl

theorem rational023_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0']) = .ok rational023 := by
  rw [parseRational_ofList]
  rfl

theorem rational024_decoded :
    parseRational (String.ofList ['2', '9', '8', '4', '3', '0', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']) = .ok rational024 := by
  rw [parseRational_ofList]
  rfl

theorem rational025_decoded :
    parseRational (String.ofList ['1', '4', '9', '0', '6', '7', '7', '/', '1', '6', '8', '0', '0', '0', '0', '0']) = .ok rational025 := by
  rw [parseRational_ofList]
  rfl

theorem rational026_decoded :
    parseRational (String.ofList ['1', '3', '9', '2', '1', '9', '2', '7', '/', '8', '4', '0', '0', '0', '0', '0', '0']) = .ok rational026 := by
  rw [parseRational_ofList]
  rfl

theorem rational027_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']) = .ok rational027 := by
  rw [parseRational_ofList]
  rfl

theorem rational028_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']) = .ok rational028 := by
  rw [parseRational_ofList]
  rfl

theorem rational029_decoded :
    parseRational (String.ofList ['5', '9', '6', '8', '6', '3', '/', '5', '6', '0', '0', '0', '0', '0']) = .ok rational029 := by
  rw [parseRational_ofList]
  rfl

theorem rational030_decoded :
    parseRational (String.ofList ['7', '4', '5', '3', '3', '6', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0']) = .ok rational030 := by
  rw [parseRational_ofList]
  rfl

theorem rational031_decoded :
    parseRational (String.ofList ['4', '4', '7', '0', '3', '1', '7', '7', '/', '2', '6', '8', '0', '0', '0', '0', '0', '0']) = .ok rational031 := by
  rw [parseRational_ofList]
  rfl

theorem rational032_decoded :
    parseRational (String.ofList ['2', '6', '4', '2', '1', '8', '8', '7', '/', '2', '6', '8', '0', '0', '0', '0', '0', '0']) = .ok rational032 := by
  rw [parseRational_ofList]
  rfl

theorem rational033_decoded :
    parseRational (String.ofList ['8', '1', '4', '0', '5', '9', '7', '/', '2', '6', '8', '0', '0', '0', '0', '0', '0']) = .ok rational033 := by
  rw [parseRational_ofList]
  rfl

theorem rational034_decoded :
    parseRational (String.ofList ['7', '6', '4', '0', '5', '7', '3', '/', '2', '6', '8', '0', '0', '0', '0', '0', '0']) = .ok rational034 := by
  rw [parseRational_ofList]
  rfl

theorem rational035_decoded :
    parseRational (String.ofList ['4', '0', '7', '9', '6', '9', '2', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']) = .ok rational035 := by
  rw [parseRational_ofList]
  rfl

theorem rational036_decoded :
    parseRational (String.ofList ['2', '4', '0', '7', '8', '1', '3', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']) = .ok rational036 := by
  rw [parseRational_ofList]
  rfl

theorem rational037_decoded :
    parseRational (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']) = .ok rational037 := by
  rw [parseRational_ofList]
  rfl

theorem rational038_decoded :
    parseRational (String.ofList ['6', '8', '5', '9', '3', '2', '3', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']) = .ok rational038 := by
  rw [parseRational_ofList]
  rfl

theorem rational039_decoded :
    parseRational (String.ofList ['2', '0', '1', '5', '6', '2', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok rational039 := by
  rw [parseRational_ofList]
  rfl

theorem rational040_decoded :
    parseRational (String.ofList ['3', '2', '8', '1', '2', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok rational040 := by
  rw [parseRational_ofList]
  rfl

theorem rational041_decoded :
    parseRational (String.ofList ['1', '3', '1', '8', '3', '/', '3', '7', '5', '0', '0', '0']) = .ok rational041 := by
  rw [parseRational_ofList]
  rfl

theorem rational042_decoded :
    parseRational (String.ofList ['6', '5', '6', '2', '7', '/', '2', '4', '0', '0', '0', '0', '0']) = .ok rational042 := by
  rw [parseRational_ofList]
  rfl

theorem rational043_decoded :
    parseRational (String.ofList ['1', '7', '1', '8', '5', '9', '/', '4', '0', '0', '0', '0', '0', '0']) = .ok rational043 := by
  rw [parseRational_ofList]
  rfl

theorem rational044_decoded :
    parseRational (String.ofList ['4', '3', '/', '2', '5', '6']) = .ok rational044 := by
  rw [parseRational_ofList]
  rfl

theorem rational045_decoded :
    parseRational (String.ofList ['1', '4', '0', '6', '1', '9', '/', '4', '0', '0', '0', '0', '0', '0']) = .ok rational045 := by
  rw [parseRational_ofList]
  rfl

theorem rational046_decoded :
    parseRational (String.ofList ['3', '2', '8', '1', '3', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok rational046 := by
  rw [parseRational_ofList]
  rfl

theorem rational047_decoded :
    parseRational (String.ofList ['5', '1', '5', '5', '8', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok rational047 := by
  rw [parseRational_ofList]
  rfl

theorem rational048_decoded :
    parseRational (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']) = .ok rational048 := by
  rw [parseRational_ofList]
  rfl

theorem rational049_decoded :
    parseRational (String.ofList ['2', '7', '6', '5', '6', '7', '7', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']) = .ok rational049 := by
  rw [parseRational_ofList]
  rfl

theorem rational050_decoded :
    parseRational (String.ofList ['6', '6', '1', '3', '3', '6', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0']) = .ok rational050 := by
  rw [parseRational_ofList]
  rfl

theorem rational051_decoded :
    parseRational (String.ofList ['5', '2', '2', '5', '8', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']) = .ok rational051 := by
  rw [parseRational_ofList]
  rfl

theorem rational052_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '4', '9', '1', '/', '4', '2', '0', '0', '0', '0', '0', '0']) = .ok rational052 := by
  rw [parseRational_ofList]
  rfl

theorem rational053_decoded :
    parseRational (String.ofList ['0']) = .ok rational053 := by
  rw [parseRational_ofList]
  rfl

theorem rational054_decoded :
    parseRational (String.ofList ['1', '0', '9', '3', '8', '3', '/', '2', '0', '0', '0', '0', '0', '0']) = .ok rational054 := by
  rw [parseRational_ofList]
  rfl

theorem rational055_decoded :
    parseRational (String.ofList ['7', '9', '6', '8', '7', '9', '/', '9', '0', '0', '0', '0', '0', '0']) = .ok rational055 := by
  rw [parseRational_ofList]
  rfl

theorem rational056_decoded :
    parseRational (String.ofList ['3', '9', '8', '4', '3', '0', '7', '/', '1', '2', '2', '0', '0', '0', '0', '0', '0']) = .ok rational056 := by
  rw [parseRational_ofList]
  rfl

theorem rational057_decoded :
    parseRational (String.ofList ['2', '8', '1', '2', '6', '3', '/', '3', '0', '0', '0', '0', '0', '0']) = .ok rational057 := by
  rw [parseRational_ofList]
  rfl

theorem rational058_decoded :
    parseRational (String.ofList ['2', '0', '1', '5', '8', '1', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0']) = .ok rational058 := by
  rw [parseRational_ofList]
  rfl

theorem rational059_decoded :
    parseRational (String.ofList ['1', '/', '7', '5', '0', '0', '0', '0']) = .ok rational059 := by
  rw [parseRational_ofList]
  rfl

theorem rational060_decoded :
    parseRational (String.ofList ['7', '4', '5', '3', '1', '3', '7', '/', '2', '2', '4', '0', '0', '0', '0', '0', '0']) = .ok rational060 := by
  rw [parseRational_ofList]
  rfl

theorem rational061_decoded :
    parseRational (String.ofList ['2', '7', '8', '9', '0', '6', '2', '1', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']) = .ok rational061 := by
  rw [parseRational_ofList]
  rfl

theorem rational062_decoded :
    parseRational (String.ofList ['3', '2', '8', '1', '2', '9', '/', '1', '5', '0', '0', '0', '0', '0']) = .ok rational062 := by
  rw [parseRational_ofList]
  rfl

theorem rational063_decoded :
    parseRational (String.ofList ['5', '2', '9', '6', '9', '6', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']) = .ok rational063 := by
  rw [parseRational_ofList]
  rfl

theorem rational064_decoded :
    parseRational (String.ofList ['3', '2', '7', '9', '6', '5', '4', '3', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']) = .ok rational064 := by
  rw [parseRational_ofList]
  rfl

theorem rational065_decoded :
    parseRational (String.ofList ['1', '2', '9', '6', '8', '6', '1', '/', '1', '2', '2', '0', '0', '0', '0', '0']) = .ok rational065 := by
  rw [parseRational_ofList]
  rfl

theorem rational066_decoded :
    parseRational (String.ofList ['8', '9', '0', '6', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0']) = .ok rational066 := by
  rw [parseRational_ofList]
  rfl

theorem rational067_decoded :
    parseRational (String.ofList ['1', '4', '5', '3', '1', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok rational067 := by
  rw [parseRational_ofList]
  rfl

theorem rational068_decoded :
    parseRational (String.ofList ['1', '5', '4', '6', '9', '0', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok rational068 := by
  rw [parseRational_ofList]
  rfl

theorem rational069_decoded :
    parseRational (String.ofList ['3', '8', '0', '8', '7', '/', '3', '7', '5', '0', '0', '0']) = .ok rational069 := by
  rw [parseRational_ofList]
  rfl

theorem rational070_decoded :
    parseRational (String.ofList ['2', '7', '6', '5', '6', '7', '7', '/', '2', '7', '0', '0', '0', '0', '0', '0']) = .ok rational070 := by
  rw [parseRational_ofList]
  rfl

theorem rational071_decoded :
    parseRational (String.ofList ['2', '7', '6', '5', '6', '7', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']) = .ok rational071 := by
  rw [parseRational_ofList]
  rfl

theorem rational072_decoded :
    parseRational (String.ofList ['7', '5', '4', '7', '1', '6', '7', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']) = .ok rational072 := by
  rw [parseRational_ofList]
  rfl

theorem rational073_decoded :
    parseRational (String.ofList ['1', '5', '9', '3', '8', '3', '/', '3', '6', '0', '0', '0', '0', '0']) = .ok rational073 := by
  rw [parseRational_ofList]
  rfl

theorem rational074_decoded :
    parseRational (String.ofList ['7', '9', '6', '9', '2', '7', '/', '1', '8', '0', '0', '0', '0', '0', '0']) = .ok rational074 := by
  rw [parseRational_ofList]
  rfl

theorem rational075_decoded :
    parseRational (String.ofList ['5', '3', '5', '9', '2', '5', '1', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0']) = .ok rational075 := by
  rw [parseRational_ofList]
  rfl

theorem rational076_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok rational076 := by
  rw [parseRational_ofList]
  rfl

theorem rational077_decoded :
    parseRational (String.ofList ['2', '3', '4', '3', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0']) = .ok rational077 := by
  rw [parseRational_ofList]
  rfl

theorem rational078_decoded :
    parseRational (String.ofList ['2', '2', '0', '7', '8', '0', '4', '1', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0']) = .ok rational078 := by
  rw [parseRational_ofList]
  rfl

theorem rational079_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '4', '9', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']) = .ok rational079 := by
  rw [parseRational_ofList]
  rfl

theorem rational080_decoded :
    parseRational (String.ofList ['5', '8', '5', '9', '4', '2', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']) = .ok rational080 := by
  rw [parseRational_ofList]
  rfl

theorem rational081_decoded :
    parseRational (String.ofList ['3', '6', '5', '6', '2', '9', '/', '4', '8', '0', '0', '0', '0', '0']) = .ok rational081 := by
  rw [parseRational_ofList]
  rfl

theorem rational082_decoded :
    parseRational (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '8', '0', '0', '0', '0', '0', '0']) = .ok rational082 := by
  rw [parseRational_ofList]
  rfl

theorem rational083_decoded :
    parseRational (String.ofList ['7', '4', '5', '3', '3', '6', '1', '/', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok rational083 := by
  rw [parseRational_ofList]
  rfl

theorem rational084_decoded :
    parseRational (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '4', '0', '0', '0', '0', '0', '0']) = .ok rational084 := by
  rw [parseRational_ofList]
  rfl

theorem rational085_decoded :
    parseRational (String.ofList ['3', '8', '7', '9', '6', '8', '3', '1', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0']) = .ok rational085 := by
  rw [parseRational_ofList]
  rfl

theorem rational086_decoded :
    parseRational (String.ofList ['3', '2', '8', '1', '3', '3', '/', '8', '0', '0', '0', '0', '0', '0']) = .ok rational086 := by
  rw [parseRational_ofList]
  rfl

theorem rational087_decoded :
    parseRational (String.ofList ['1', '2', '5', '0', '0', '1', '/', '2', '0', '0', '0', '0', '0', '0']) = .ok rational087 := by
  rw [parseRational_ofList]
  rfl

theorem rational088_decoded :
    parseRational (String.ofList ['3', '2', '8', '1', '3', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0']) = .ok rational088 := by
  rw [parseRational_ofList]
  rfl

theorem rational089_decoded :
    parseRational (String.ofList ['2', '6', '7', '1', '8', '8', '3', '/', '1', '4', '0', '0', '0', '0', '0', '0']) = .ok rational089 := by
  rw [parseRational_ofList]
  rfl

theorem rational090_decoded :
    parseRational (String.ofList ['4', '9', '6', '8', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0']) = .ok rational090 := by
  rw [parseRational_ofList]
  rfl

theorem rational091_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']) = .ok rational091 := by
  rw [parseRational_ofList]
  rfl

theorem rational092_decoded :
    parseRational (String.ofList ['3', '7', '7', '8', '1', '3', '7', '/', '1', '1', '2', '0', '0', '0', '0', '0']) = .ok rational092 := by
  rw [parseRational_ofList]
  rfl

theorem rational093_decoded :
    parseRational (String.ofList ['7', '8', '5', '9', '3', '7', '1', '/', '1', '2', '2', '0', '0', '0', '0', '0', '0']) = .ok rational093 := by
  rw [parseRational_ofList]
  rfl

theorem rational094_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0']) = .ok rational094 := by
  rw [parseRational_ofList]
  rfl

theorem rational095_decoded :
    parseRational (String.ofList ['3', '7', '5', '0', '0', '3', '/', '2', '0', '0', '0', '0', '0', '0']) = .ok rational095 := by
  rw [parseRational_ofList]
  rfl

theorem rational096_decoded :
    parseRational (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '4', '8', '8', '0', '0', '0', '0', '0', '0']) = .ok rational096 := by
  rw [parseRational_ofList]
  rfl

theorem rational097_decoded :
    parseRational (String.ofList ['3', '2', '8', '1', '3', '3', '/', '4', '0', '0', '0', '0', '0', '0']) = .ok rational097 := by
  rw [parseRational_ofList]
  rfl

theorem rational098_decoded :
    parseRational (String.ofList ['2', '6', '7', '1', '8', '9', '1', '/', '8', '0', '0', '0', '0', '0', '0']) = .ok rational098 := by
  rw [parseRational_ofList]
  rfl

theorem rational099_decoded :
    parseRational (String.ofList ['1', '1', '7', '1', '8', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']) = .ok rational099 := by
  rw [parseRational_ofList]
  rfl

theorem rational100_decoded :
    parseRational (String.ofList ['1', '3', '1', '7', '1', '9', '1', '1', '/', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok rational100 := by
  rw [parseRational_ofList]
  rfl

theorem rational101_decoded :
    parseRational (String.ofList ['1', '2', '4', '2', '2', '1', '1', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok rational101 := by
  rw [parseRational_ofList]
  rfl

theorem rational102_decoded :
    parseRational (String.ofList ['7', '4', '5', '3', '1', '3', '7', '/', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok rational102 := by
  rw [parseRational_ofList]
  rfl

theorem rational103_decoded :
    parseRational (String.ofList ['2', '6', '7', '1', '8', '8', '3', '/', '7', '0', '0', '0', '0', '0', '0']) = .ok rational103 := by
  rw [parseRational_ofList]
  rfl

theorem rational104_decoded :
    parseRational (String.ofList ['3', '8', '7', '7', '3', '5', '6', '8', '0', '8', '5', '7', '7', '9', '4', '6', '8', '9', '1', '0', '1', '7', '4', '0', '8', '3', '2', '1', '9', '1', '1', '/', '1', '6', '8', '3', '1', '0', '3', '2', '2', '9', '1', '6', '5', '0', '3', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational104 := by
  rw [parseRational_ofList]
  rfl

theorem rational105_decoded :
    parseRational (String.ofList ['2', '3', '4', '3', '1', '/', '6', '8', '6', '2', '5', '0', '0', '0']) = .ok rational105 := by
  rw [parseRational_ofList]
  rfl

theorem rational106_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']) = .ok rational106 := by
  rw [parseRational_ofList]
  rfl

theorem rational107_decoded :
    parseRational (String.ofList ['6', '9', '7', '3', '2', '9', '5', '8', '7', '/', '8', '5', '4', '0', '0', '0', '0', '0', '0', '0']) = .ok rational107 := by
  rw [parseRational_ofList]
  rfl

theorem rational108_decoded :
    parseRational (String.ofList ['7', '0', '2', '5', '7', '8', '1', '3', '1', '/', '8', '5', '4', '0', '0', '0', '0', '0', '0', '0']) = .ok rational108 := by
  rw [parseRational_ofList]
  rfl

theorem rational109_decoded :
    parseRational (String.ofList ['1', '1', '8', '7', '9', '8', '4', '6', '1', '9', '3', '4', '9', '/', '7', '1', '4', '7', '9', '8', '0', '0', '0', '0', '0', '0', '0']) = .ok rational109 := by
  rw [parseRational_ofList]
  rfl

theorem rational110_decoded :
    parseRational (String.ofList ['2', '6', '1', '5', '7', '4', '8', '8', '3', '2', '1', '/', '2', '6', '4', '7', '4', '0', '0', '0', '0', '0', '0', '0']) = .ok rational110 := by
  rw [parseRational_ofList]
  rfl

theorem rational111_decoded :
    parseRational (String.ofList ['7', '7', '0', '5', '4', '6', '0', '8', '2', '9', '1', '/', '7', '9', '4', '2', '2', '0', '0', '0', '0', '0', '0', '0']) = .ok rational111 := by
  rw [parseRational_ofList]
  rfl

theorem rational112_decoded :
    parseRational (String.ofList ['2', '5', '9', '4', '1', '1', '0', '7', '8', '0', '3', '/', '7', '9', '4', '2', '2', '0', '0', '0', '0', '0', '0', '0']) = .ok rational112 := by
  rw [parseRational_ofList]
  rfl

theorem rational113_decoded :
    parseRational (String.ofList ['1', '6', '4', '6', '6', '9', '8', '8', '8', '1', '/', '5', '2', '9', '4', '8', '0', '0', '0', '0', '0', '0']) = .ok rational113 := by
  rw [parseRational_ofList]
  rfl

theorem rational114_decoded :
    parseRational (String.ofList ['2', '4', '0', '8', '0', '1', '7', '0', '9', '2', '1', '/', '7', '9', '4', '2', '2', '0', '0', '0', '0', '0', '0', '0']) = .ok rational114 := by
  rw [parseRational_ofList]
  rfl

theorem rational115_decoded :
    parseRational (String.ofList ['8', '0', '2', '6', '7', '0', '5', '9', '9', '1', '/', '2', '6', '4', '7', '4', '0', '0', '0', '0', '0', '0', '0']) = .ok rational115 := by
  rw [parseRational_ofList]
  rfl

theorem rational116_decoded :
    parseRational (String.ofList ['6', '6', '4', '3', '3', '5', '9', '2', '3', '9', '/', '2', '3', '0', '5', '8', '0', '0', '0', '0', '0', '0', '0']) = .ok rational116 := by
  rw [parseRational_ofList]
  rfl

theorem rational117_decoded :
    parseRational (String.ofList ['1', '2', '4', '8', '6', '3', '7', '6', '6', '6', '6', '7', '2', '0', '8', '5', '5', '4', '5', '8', '2', '6', '2', '4', '2', '4', '7', '9', '5', '8', '2', '3', '3', '5', '7', '4', '3', '2', '0', '6', '5', '6', '8', '7', '5', '5', '2', '0', '0', '0', '0', '/', '2', '9', '0', '5', '0', '3', '7', '6', '4', '9', '1', '0', '1', '5', '8', '8', '6', '8', '5', '5', '9', '3', '5', '3', '5', '2', '3', '6', '0', '4', '9', '9', '2', '5', '0', '0', '1', '7', '9', '5', '4', '1', '6', '2', '6', '4', '9', '1', '2', '1', '3', '4', '6', '5', '7', '1', '1', '5', '2', '0', '8', '6', '9', '8', '0', '3', '4', '1']) = .ok rational117 := by
  rw [parseRational_ofList]
  rfl

theorem rational118_decoded :
    parseRational (String.ofList ['1', '7', '0', '8', '5', '6', '5', '3', '6', '5', '0', '1', '2', '6', '8', '5', '4', '6', '8', '9', '8', '0', '1', '8', '8', '8', '4', '5', '5', '8', '7', '5', '5', '8', '3', '2', '3', '4', '1', '2', '6', '0', '6', '5', '7', '0', '4', '8', '8', '4', '1', '1', '7', '6', '8', '7', '8', '0', '1', '7', '6', '9', '4', '8', '8', '3', '2', '7', '6', '3', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '6', '3', '6', '2', '2', '2', '2', '7', '8', '5', '9', '8', '5', '7', '1', '8', '2', '7', '1', '6', '7', '0', '7', '5', '7', '6', '2', '0', '8', '6', '2', '8', '1', '1', '7', '8', '0', '3', '0', '3', '1', '1', '9', '3', '8', '0', '8', '2', '5', '0', '2', '9', '6', '2', '3', '8', '1', '9', '7', '5', '6', '9', '7', '9', '2', '3', '8', '1', '3', '8', '7', '3', '1', '3', '0', '9', '5', '2', '5', '2', '6', '8', '8', '0', '3', '9', '5', '3', '0', '2', '8', '0', '9', '0', '4', '3', '6', '7', '4', '1', '4', '3']) = .ok rational118 := by
  rw [parseRational_ofList]
  rfl

theorem rational119_decoded :
    parseRational (String.ofList ['8', '7', '3', '1', '5', '2', '8', '0', '3', '7', '5', '6', '3', '1', '0', '4', '7', '4', '1', '6', '9', '3', '6', '0', '8', '5', '4', '2', '7', '5', '0', '7', '6', '3', '/', '7', '4', '8', '0', '4', '5', '8', '7', '9', '6', '2', '8', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational119 := by
  rw [parseRational_ofList]
  rfl

theorem rational120_decoded :
    parseRational (String.ofList ['1', '9', '7', '9', '8', '3', '0', '9', '1', '/', '2', '4', '0', '1', '8', '7', '5', '0', '0', '0']) = .ok rational120 := by
  rw [parseRational_ofList]
  rfl

theorem rational121_decoded :
    parseRational (String.ofList ['4', '9', '8', '6', '4', '8', '1', '1', '/', '6', '0', '0', '4', '6', '8', '7', '5', '0']) = .ok rational121 := by
  rw [parseRational_ofList]
  rfl

theorem rational122_decoded :
    parseRational (String.ofList ['2', '9', '7', '3', '2', '3', '0', '6', '5', '7', '1', '7', '/', '1', '7', '8', '6', '9', '9', '5', '0', '0', '0', '0', '0', '0']) = .ok rational122 := by
  rw [parseRational_ofList]
  rfl

theorem rational123_decoded :
    parseRational (String.ofList ['1', '9', '6', '2', '6', '4', '9', '8', '5', '7', '1', '/', '1', '9', '8', '5', '5', '5', '0', '0', '0', '0', '0', '0']) = .ok rational123 := by
  rw [parseRational_ofList]
  rfl

theorem rational124_decoded :
    parseRational (String.ofList ['1', '9', '2', '7', '2', '0', '3', '4', '4', '0', '3', '/', '1', '9', '8', '5', '5', '5', '0', '0', '0', '0', '0', '0']) = .ok rational124 := by
  rw [parseRational_ofList]
  rfl

theorem rational125_decoded :
    parseRational (String.ofList ['3', '8', '7', '9', '4', '3', '0', '9', '0', '8', '1', '/', '1', '1', '9', '1', '3', '3', '0', '0', '0', '0', '0', '0', '0']) = .ok rational125 := by
  rw [parseRational_ofList]
  rfl

theorem rational126_decoded :
    parseRational (String.ofList ['3', '6', '9', '3', '3', '3', '7', '2', '1', '9', '9', '/', '1', '1', '9', '1', '3', '3', '0', '0', '0', '0', '0', '0', '0']) = .ok rational126 := by
  rw [parseRational_ofList]
  rfl

theorem rational127_decoded :
    parseRational (String.ofList ['1', '8', '0', '0', '1', '4', '5', '1', '8', '7', '9', '/', '5', '9', '5', '6', '6', '5', '0', '0', '0', '0', '0', '0']) = .ok rational127 := by
  rw [parseRational_ofList]
  rfl

theorem rational128_decoded :
    parseRational (String.ofList ['1', '7', '8', '0', '0', '1', '9', '6', '5', '3', '1', '/', '5', '9', '5', '6', '6', '5', '0', '0', '0', '0', '0', '0']) = .ok rational128 := by
  rw [parseRational_ofList]
  rfl

theorem rational129_decoded :
    parseRational (String.ofList ['1', '6', '3', '5', '6', '9', '2', '8', '1', '9', '/', '5', '7', '6', '4', '5', '0', '0', '0', '0', '0', '0']) = .ok rational129 := by
  rw [parseRational_ofList]
  rfl

theorem rational130_decoded :
    parseRational (String.ofList ['4', '1', '3', '5', '0', '6', '1', '7', '9', '1', '9', '9', '8', '2', '9', '9', '1', '4', '0', '8', '3', '9', '9', '7', '9', '2', '0', '1', '4', '1', '5', '6', '0', '9', '3', '8', '9', '4', '2', '3', '9', '1', '3', '8', '6', '1', '1', '2', '0', '0', '0', '0', '/', '1', '8', '9', '8', '7', '1', '7', '4', '1', '7', '7', '1', '3', '4', '5', '6', '6', '5', '7', '2', '5', '0', '6', '7', '6', '6', '2', '4', '8', '6', '9', '2', '3', '2', '0', '2', '7', '3', '1', '7', '2', '6', '5', '5', '3', '2', '6', '2', '2', '3', '1', '0', '2', '3', '3', '4', '0', '8', '6', '3', '3', '1', '3', '5', '9', '7']) = .ok rational130 := by
  rw [parseRational_ofList]
  rfl

theorem rational131_decoded :
    parseRational (String.ofList ['2', '7', '6', '5', '9', '0', '5', '4', '1', '8', '8', '4', '2', '4', '3', '0', '8', '5', '5', '1', '1', '6', '2', '0', '8', '1', '9', '4', '3', '7', '8', '7', '7', '8', '6', '5', '9', '0', '9', '5', '8', '4', '7', '6', '0', '8', '6', '9', '6', '9', '8', '0', '5', '8', '7', '0', '0', '5', '8', '1', '4', '2', '0', '7', '2', '4', '2', '6', '0', '6', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '9', '0', '4', '4', '8', '4', '9', '9', '6', '1', '9', '3', '2', '3', '8', '7', '9', '8', '2', '0', '3', '1', '2', '0', '0', '2', '4', '2', '5', '9', '3', '7', '5', '9', '9', '6', '3', '2', '6', '5', '4', '7', '7', '9', '3', '0', '5', '9', '4', '7', '9', '9', '7', '2', '9', '0', '7', '2', '5', '1', '2', '5', '6', '4', '6', '8', '8', '9', '5', '7', '9', '7', '4', '8', '7', '8', '4', '7', '6', '8', '9', '7', '0', '2', '1', '8', '0', '2', '0', '7', '9', '6', '2', '9', '9', '5', '7']) = .ok rational131 := by
  rw [parseRational_ofList]
  rfl

theorem rational132_decoded :
    parseRational (String.ofList ['1', '6', '7', '6', '5', '8', '7', '4', '9', '9', '6', '2', '1', '7', '1', '8', '6', '9', '6', '7', '1', '7', '5', '3', '1', '1', '8', '7', '2', '4', '3', '/', '8', '6', '8', '6', '9', '8', '4', '4', '0', '8', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational132 := by
  rw [parseRational_ofList]
  rfl

theorem rational133_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']) = .ok rational133 := by
  rw [parseRational_ofList]
  rfl

theorem rational134_decoded :
    parseRational (String.ofList ['3', '5', '6', '4', '1', '2', '7', '/', '4', '2', '8', '9', '0', '6', '2', '5']) = .ok rational134 := by
  rw [parseRational_ofList]
  rfl

theorem rational135_decoded :
    parseRational (String.ofList ['5', '7', '4', '4', '7', '7', '9', '/', '6', '8', '6', '2', '5', '0', '0', '0']) = .ok rational135 := by
  rw [parseRational_ofList]
  rfl

theorem rational136_decoded :
    parseRational (String.ofList ['1', '3', '7', '0', '8', '0', '4', '3', '7', '1', '/', '8', '2', '3', '5', '0', '0', '0', '0', '0', '0']) = .ok rational136 := by
  rw [parseRational_ofList]
  rfl

theorem rational137_decoded :
    parseRational (String.ofList ['1', '0', '5', '4', '6', '5', '0', '1', '9', '/', '1', '0', '6', '7', '5', '0', '0', '0', '0', '0']) = .ok rational137 := by
  rw [parseRational_ofList]
  rfl

theorem rational138_decoded :
    parseRational (String.ofList ['3', '1', '0', '6', '7', '7', '8', '9', '3', '/', '3', '2', '0', '2', '5', '0', '0', '0', '0', '0']) = .ok rational138 := by
  rw [parseRational_ofList]
  rfl

theorem rational139_decoded :
    parseRational (String.ofList ['1', '7', '7', '7', '8', '7', '6', '8', '1', '/', '5', '4', '9', '0', '0', '0', '0', '0', '0', '0']) = .ok rational139 := by
  rw [parseRational_ofList]
  rfl

theorem rational140_decoded :
    parseRational (String.ofList ['3', '3', '8', '4', '2', '3', '8', '7', '/', '1', '0', '9', '8', '0', '0', '0', '0', '0', '0']) = .ok rational140 := by
  rw [parseRational_ofList]
  rfl

theorem rational141_decoded :
    parseRational (String.ofList ['8', '2', '4', '6', '2', '0', '3', '1', '/', '2', '7', '4', '5', '0', '0', '0', '0', '0', '0']) = .ok rational141 := by
  rw [parseRational_ofList]
  rfl

theorem rational142_decoded :
    parseRational (String.ofList ['2', '0', '3', '8', '3', '6', '0', '1', '/', '6', '8', '6', '2', '5', '0', '0', '0', '0']) = .ok rational142 := by
  rw [parseRational_ofList]
  rfl

theorem rational143_decoded :
    parseRational (String.ofList ['2', '3', '5', '5', '0', '8', '1', '4', '1', '/', '8', '2', '3', '5', '0', '0', '0', '0', '0', '0']) = .ok rational143 := by
  rw [parseRational_ofList]
  rfl

theorem rational144_decoded :
    parseRational (String.ofList ['1', '9', '8', '4', '9', '8', '8', '4', '4', '6', '6', '9', '6', '5', '0', '0', '3', '7', '8', '6', '3', '8', '6', '1', '0', '9', '6', '8', '0', '8', '4', '4', '6', '5', '7', '1', '9', '2', '3', '3', '7', '4', '0', '8', '0', '0', '0', '0', '/', '5', '5', '1', '2', '4', '4', '0', '9', '0', '8', '3', '4', '2', '7', '0', '7', '1', '6', '9', '6', '7', '8', '5', '5', '9', '3', '7', '7', '4', '6', '0', '7', '0', '7', '5', '4', '0', '8', '0', '0', '5', '0', '7', '7', '3', '2', '2', '1', '0', '5', '3', '7', '6', '2', '1', '6', '4', '1', '4', '6', '8', '3', '1', '4', '7']) = .ok rational144 := by
  rw [parseRational_ofList]
  rfl

theorem rational145_decoded :
    parseRational (String.ofList ['1', '4', '2', '9', '7', '2', '3', '4', '2', '1', '8', '0', '3', '7', '0', '6', '1', '4', '7', '8', '9', '2', '7', '5', '4', '7', '7', '2', '0', '2', '6', '0', '9', '5', '7', '2', '4', '2', '3', '0', '3', '1', '5', '1', '0', '8', '4', '0', '9', '7', '1', '7', '9', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '/', '1', '5', '3', '3', '2', '8', '2', '9', '8', '9', '5', '1', '1', '3', '9', '3', '6', '9', '9', '9', '6', '7', '2', '3', '2', '5', '5', '4', '9', '4', '5', '0', '1', '2', '7', '3', '4', '1', '8', '0', '8', '6', '6', '9', '9', '3', '4', '6', '1', '5', '7', '1', '3', '6', '6', '5', '3', '2', '7', '8', '3', '4', '2', '1', '5', '9', '9', '8', '9', '2', '5', '0', '8', '9', '8', '3', '5', '4', '7', '9']) = .ok rational145 := by
  rw [parseRational_ofList]
  rfl

theorem rational146_decoded :
    parseRational (String.ofList ['6', '7', '0', '6', '1', '3', '5', '3', '3', '5', '7', '5', '3', '7', '9', '1', '8', '9', '8', '5', '5', '5', '9', '1', '9', '0', '9', '8', '6', '1', '3', '/', '3', '4', '7', '4', '7', '9', '3', '7', '6', '3', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational146 := by
  rw [parseRational_ofList]
  rfl

theorem rational147_decoded :
    parseRational (String.ofList ['3', '1', '9', '3', '4', '5', '8', '8', '9', '/', '3', '8', '4', '3', '0', '0', '0', '0', '0', '0']) = .ok rational147 := by
  rw [parseRational_ofList]
  rfl

theorem rational148_decoded :
    parseRational (String.ofList ['1', '6', '0', '8', '5', '3', '8', '6', '6', '9', '/', '1', '9', '2', '1', '5', '0', '0', '0', '0', '0', '0']) = .ok rational148 := by
  rw [parseRational_ofList]
  rfl

theorem rational149_decoded :
    parseRational (String.ofList ['2', '9', '9', '8', '6', '3', '4', '3', '9', '/', '1', '8', '0', '1', '4', '0', '6', '2', '5', '0']) = .ok rational149 := by
  rw [parseRational_ofList]
  rfl

theorem rational150_decoded :
    parseRational (String.ofList ['1', '2', '7', '7', '0', '1', '4', '1', '9', '/', '1', '2', '8', '1', '0', '0', '0', '0', '0', '0']) = .ok rational150 := by
  rw [parseRational_ofList]
  rfl

theorem rational151_decoded :
    parseRational (String.ofList ['4', '1', '0', '4', '2', '5', '8', '7', '/', '4', '2', '7', '0', '0', '0', '0', '0', '0']) = .ok rational151 := by
  rw [parseRational_ofList]
  rfl

theorem rational152_decoded :
    parseRational (String.ofList ['1', '2', '4', '4', '5', '1', '4', '1', '3', '3', '/', '3', '8', '4', '3', '0', '0', '0', '0', '0', '0', '0']) = .ok rational152 := by
  rw [parseRational_ofList]
  rfl

theorem rational153_decoded :
    parseRational (String.ofList ['1', '1', '8', '4', '4', '8', '3', '9', '1', '1', '/', '3', '8', '4', '3', '0', '0', '0', '0', '0', '0', '0']) = .ok rational153 := by
  rw [parseRational_ofList]
  rfl

theorem rational154_decoded :
    parseRational (String.ofList ['7', '2', '1', '5', '4', '3', '/', '2', '4', '0', '1', '8', '7', '5', '0']) = .ok rational154 := by
  rw [parseRational_ofList]
  rfl

theorem rational155_decoded :
    parseRational (String.ofList ['5', '7', '0', '7', '3', '9', '7', '3', '/', '1', '9', '2', '1', '5', '0', '0', '0', '0', '0']) = .ok rational155 := by
  rw [parseRational_ofList]
  rfl

theorem rational156_decoded :
    parseRational (String.ofList ['5', '1', '5', '1', '7', '4', '2', '3', '/', '1', '8', '0', '1', '4', '0', '6', '2', '5', '0']) = .ok rational156 := by
  rw [parseRational_ofList]
  rfl

theorem rational157_decoded :
    parseRational (String.ofList ['1', '9', '8', '4', '9', '2', '4', '9', '0', '9', '4', '4', '5', '2', '0', '8', '3', '9', '8', '9', '8', '4', '1', '3', '7', '0', '2', '5', '0', '9', '3', '2', '9', '7', '4', '6', '5', '6', '6', '8', '4', '0', '3', '2', '0', '0', '0', '0', '/', '5', '5', '1', '2', '4', '4', '0', '9', '0', '8', '3', '4', '2', '7', '0', '7', '1', '6', '9', '6', '7', '8', '5', '5', '9', '3', '7', '7', '4', '6', '0', '7', '0', '7', '5', '4', '0', '8', '0', '0', '5', '0', '7', '7', '3', '2', '2', '1', '0', '5', '3', '7', '6', '2', '1', '6', '4', '1', '4', '6', '8', '3', '1', '4', '7']) = .ok rational157 := by
  rw [parseRational_ofList]
  rfl

theorem rational158_decoded :
    parseRational (String.ofList ['1', '5', '8', '0', '4', '0', '4', '0', '6', '3', '7', '1', '9', '8', '7', '0', '9', '8', '4', '7', '7', '4', '2', '1', '5', '8', '0', '6', '5', '9', '0', '7', '4', '3', '2', '2', '9', '4', '6', '4', '0', '8', '2', '2', '4', '7', '1', '5', '0', '0', '6', '9', '3', '2', '1', '9', '9', '2', '1', '8', '7', '5', '0', '/', '1', '6', '9', '4', '5', '0', '9', '4', '2', '1', '6', '0', '7', '7', '9', '3', '4', '3', '3', '9', '0', '7', '4', '5', '6', '6', '7', '9', '2', '9', '5', '3', '2', '1', '0', '3', '6', '0', '2', '0', '3', '0', '2', '7', '7', '0', '9', '3', '1', '2', '7', '7', '4', '5', '9', '9', '8', '5', '9', '2', '4', '5', '6', '8', '4', '5', '1', '3', '7', '1', '5', '2', '8', '7', '7', '6', '6', '6', '3', '3']) = .ok rational158 := by
  rw [parseRational_ofList]
  rfl

theorem rational159_decoded :
    parseRational (String.ofList ['2', '3', '9', '5', '0', '8', '6', '6', '3', '0', '0', '3', '0', '1', '6', '3', '1', '6', '6', '0', '8', '5', '0', '1', '1', '2', '8', '1', '9', '3', '7', '2', '8', '9', '0', '7', '/', '4', '4', '3', '4', '4', '9', '8', '7', '0', '7', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational159 := by
  rw [parseRational_ofList]
  rfl

theorem rational160_decoded :
    parseRational (String.ofList ['1', '1', '9', '9', '6', '4', '8', '9', '/', '1', '8', '3', '9', '1', '5', '0', '0', '0', '0', '0']) = .ok rational160 := by
  rw [parseRational_ofList]
  rfl

theorem rational161_decoded :
    parseRational (String.ofList ['1', '2', '7', '5', '2', '1', '7', '0', '6', '7', '0', '1', '9', '0', '9', '2', '3', '3', '9', '/', '1', '5', '4', '4', '4', '3', '3', '9', '9', '2', '1', '0', '4', '5', '0', '0', '0', '0', '0', '0']) = .ok rational161 := by
  rw [parseRational_ofList]
  rfl

theorem rational162_decoded :
    parseRational (String.ofList ['1', '2', '8', '8', '8', '2', '7', '0', '7', '2', '9', '8', '9', '7', '1', '5', '7', '3', '7', '/', '1', '5', '4', '4', '4', '3', '3', '9', '9', '2', '1', '0', '4', '5', '0', '0', '0', '0', '0', '0']) = .ok rational162 := by
  rw [parseRational_ofList]
  rfl

theorem rational163_decoded :
    parseRational (String.ofList ['3', '8', '5', '8', '3', '4', '4', '4', '7', '0', '2', '2', '0', '9', '0', '1', '6', '6', '7', '/', '2', '3', '1', '6', '6', '5', '0', '9', '8', '8', '1', '5', '6', '7', '5', '0', '0', '0', '0', '0']) = .ok rational163 := by
  rw [parseRational_ofList]
  rfl

theorem rational164_decoded :
    parseRational (String.ofList ['5', '0', '9', '0', '7', '1', '8', '2', '3', '1', '2', '3', '5', '6', '2', '4', '0', '7', '/', '5', '1', '4', '8', '1', '1', '3', '3', '0', '7', '0', '1', '5', '0', '0', '0', '0', '0', '0']) = .ok rational164 := by
  rw [parseRational_ofList]
  rfl

theorem rational165_decoded :
    parseRational (String.ofList ['4', '9', '9', '8', '8', '1', '6', '0', '7', '3', '6', '6', '4', '8', '1', '4', '0', '1', '/', '5', '1', '4', '8', '1', '1', '3', '3', '0', '7', '0', '1', '5', '0', '0', '0', '0', '0', '0']) = .ok rational165 := by
  rw [parseRational_ofList]
  rfl

theorem rational166_decoded :
    parseRational (String.ofList ['1', '0', '0', '3', '0', '8', '1', '0', '7', '8', '2', '3', '2', '0', '2', '4', '9', '8', '7', '/', '3', '0', '8', '8', '8', '6', '7', '9', '8', '4', '2', '0', '9', '0', '0', '0', '0', '0', '0', '0']) = .ok rational166 := by
  rw [parseRational_ofList]
  rfl

theorem rational167_decoded :
    parseRational (String.ofList ['9', '5', '4', '8', '3', '0', '9', '0', '1', '0', '7', '3', '3', '5', '7', '6', '0', '1', '/', '3', '0', '8', '8', '8', '6', '7', '9', '8', '4', '2', '0', '9', '0', '0', '0', '0', '0', '0', '0']) = .ok rational167 := by
  rw [parseRational_ofList]
  rfl

theorem rational168_decoded :
    parseRational (String.ofList ['2', '3', '2', '6', '7', '6', '4', '5', '3', '1', '2', '3', '5', '0', '5', '9', '7', '7', '/', '7', '7', '2', '2', '1', '6', '9', '9', '6', '0', '5', '2', '2', '5', '0', '0', '0', '0', '0']) = .ok rational168 := by
  rw [parseRational_ofList]
  rfl

theorem rational169_decoded :
    parseRational (String.ofList ['2', '2', '7', '9', '3', '8', '9', '8', '0', '5', '2', '9', '7', '3', '9', '0', '5', '7', '/', '7', '7', '2', '2', '1', '6', '9', '9', '6', '0', '5', '2', '2', '5', '0', '0', '0', '0', '0']) = .ok rational169 := by
  rw [parseRational_ofList]
  rfl

theorem rational170_decoded :
    parseRational (String.ofList ['6', '6', '0', '4', '9', '6', '4', '1', '4', '0', '6', '9', '7', '4', '9', '6', '2', '9', '/', '2', '3', '1', '6', '6', '5', '0', '9', '8', '8', '1', '5', '6', '7', '5', '0', '0', '0', '0', '0']) = .ok rational170 := by
  rw [parseRational_ofList]
  rfl

theorem rational171_decoded :
    parseRational (String.ofList ['7', '9', '3', '9', '7', '0', '5', '4', '7', '4', '3', '4', '9', '5', '5', '0', '9', '3', '3', '3', '5', '2', '0', '5', '3', '6', '3', '4', '9', '2', '6', '7', '4', '3', '5', '3', '2', '5', '5', '3', '6', '6', '6', '5', '0', '7', '5', '7', '1', '2', '0', '0', '0', '0', '0', '/', '4', '1', '2', '4', '2', '1', '3', '4', '8', '3', '8', '5', '6', '5', '6', '1', '0', '9', '9', '7', '7', '9', '9', '5', '8', '7', '2', '9', '3', '8', '0', '1', '9', '5', '8', '3', '9', '2', '5', '7', '8', '2', '1', '4', '5', '3', '1', '8', '8', '7', '8', '0', '7', '6', '8', '7', '4', '4', '1', '1', '8', '6', '3', '2', '4', '2', '0', '2', '9']) = .ok rational171 := by
  rw [parseRational_ofList]
  rfl

theorem rational172_decoded :
    parseRational (String.ofList ['2', '5', '4', '3', '9', '4', '4', '6', '1', '4', '6', '7', '1', '2', '8', '3', '5', '8', '1', '1', '1', '9', '1', '6', '8', '5', '2', '3', '1', '0', '6', '2', '4', '6', '2', '5', '7', '4', '5', '7', '7', '3', '2', '2', '8', '3', '4', '8', '5', '2', '6', '2', '0', '1', '4', '6', '3', '9', '6', '1', '3', '5', '8', '1', '4', '3', '3', '0', '9', '9', '1', '6', '7', '8', '7', '7', '4', '0', '1', '8', '6', '3', '7', '9', '6', '3', '1', '9', '5', '4', '3', '2', '5', '0', '4', '4', '0', '7', '8', '1', '7', '6', '3', '5', '4', '0', '3', '9', '8', '8', '0', '9', '0', '6', '3', '6', '7', '5', '8', '6', '1', '8', '1', '8', '2', '1', '4', '1', '5', '5', '1', '5', '7', '8', '5', '1', '8', '2', '1', '6', '3', '7', '9', '6', '6', '3', '7', '4', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '0', '6', '3', '2', '6', '2', '2', '2', '5', '9', '3', '6', '6', '2', '0', '2', '0', '6', '2', '9', '9', '2', '6', '3', '1', '7', '7', '3', '2', '4', '0', '6', '6', '4', '9', '8', '9', '4', '6', '1', '2', '1', '7', '2', '1', '4', '8', '9', '1', '7', '8', '8', '9', '9', '9', '0', '1', '5', '4', '2', '3', '1', '5', '9', '1', '1', '1', '4', '2', '7', '3', '9', '4', '9', '4', '3', '8', '6', '0', '5', '2', '7', '6', '7', '0', '9', '4', '8', '7', '7', '5', '3', '6', '8', '2', '9', '1', '2', '7', '1', '4', '2', '2', '4', '0', '8', '9', '1', '0', '0', '8', '0', '2', '1', '8', '3', '7', '1', '6', '7', '8', '2', '1', '1', '2', '7', '0', '7', '3', '2', '5', '6', '6', '5', '9', '4', '1', '5', '2', '3', '3', '2', '5', '5', '5', '4', '5', '7', '8', '6', '1', '7', '1', '1', '3', '9', '3', '4', '4', '0', '5', '5', '6', '2', '4', '6', '4', '2', '2', '4', '6', '6', '9', '3']) = .ok rational172 := by
  rw [parseRational_ofList]
  rfl

theorem rational173_decoded :
    parseRational (String.ofList ['1', '0', '7', '2', '9', '1', '2', '9', '6', '4', '9', '4', '4', '1', '1', '9', '2', '5', '2', '3', '7', '2', '3', '0', '4', '3', '0', '8', '0', '3', '2', '5', '3', '/', '6', '1', '0', '6', '5', '2', '2', '8', '1', '0', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational173 := by
  rw [parseRational_ofList]
  rfl

theorem rational174_decoded :
    parseRational (String.ofList ['9', '3', '7', '2', '1', '/', '3', '0', '1', '5', '0', '0', '0', '0', '0']) = .ok rational174 := by
  rw [parseRational_ofList]
  rfl

theorem rational175_decoded :
    parseRational (String.ofList ['2', '7', '9', '3', '3', '6', '6', '3', '7', '/', '3', '3', '7', '6', '8', '0', '0', '0', '0', '0']) = .ok rational175 := by
  rw [parseRational_ofList]
  rfl

theorem rational176_decoded :
    parseRational (String.ofList ['7', '0', '3', '0', '6', '5', '1', '3', '0', '9', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0', '0']) = .ok rational176 := by
  rw [parseRational_ofList]
  rfl

theorem rational177_decoded :
    parseRational (String.ofList ['4', '2', '1', '9', '4', '2', '2', '1', '0', '8', '7', '/', '2', '5', '3', '2', '6', '0', '0', '0', '0', '0', '0', '0']) = .ok rational177 := by
  rw [parseRational_ofList]
  rfl

theorem rational178_decoded :
    parseRational (String.ofList ['2', '3', '1', '6', '3', '4', '1', '5', '3', '/', '2', '3', '4', '5', '0', '0', '0', '0', '0', '0']) = .ok rational178 := by
  rw [parseRational_ofList]
  rfl

theorem rational179_decoded :
    parseRational (String.ofList ['1', '3', '6', '4', '6', '8', '7', '6', '9', '/', '1', '4', '0', '7', '0', '0', '0', '0', '0', '0']) = .ok rational179 := by
  rw [parseRational_ofList]
  rfl

theorem rational180_decoded :
    parseRational (String.ofList ['1', '1', '1', '3', '8', '2', '4', '5', '0', '1', '/', '3', '3', '7', '6', '8', '0', '0', '0', '0', '0', '0']) = .ok rational180 := by
  rw [parseRational_ofList]
  rfl

theorem rational181_decoded :
    parseRational (String.ofList ['5', '3', '0', '5', '3', '8', '3', '1', '6', '9', '/', '1', '6', '8', '8', '4', '0', '0', '0', '0', '0', '0', '0']) = .ok rational181 := by
  rw [parseRational_ofList]
  rfl

theorem rational182_decoded :
    parseRational (String.ofList ['2', '5', '2', '0', '8', '2', '4', '0', '2', '7', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0', '0']) = .ok rational182 := by
  rw [parseRational_ofList]
  rfl

theorem rational183_decoded :
    parseRational (String.ofList ['2', '4', '6', '0', '7', '8', '2', '9', '2', '7', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0', '0']) = .ok rational183 := by
  rw [parseRational_ofList]
  rfl

theorem rational184_decoded :
    parseRational (String.ofList ['1', '4', '4', '1', '2', '9', '4', '3', '8', '1', '/', '5', '0', '6', '5', '2', '0', '0', '0', '0', '0', '0']) = .ok rational184 := by
  rw [parseRational_ofList]
  rfl

theorem rational185_decoded :
    parseRational (String.ofList ['1', '6', '8', '7', '0', '2', '4', '1', '6', '3', '4', '0', '9', '5', '6', '7', '2', '1', '4', '1', '8', '1', '1', '3', '4', '5', '9', '1', '9', '5', '7', '2', '6', '3', '0', '8', '9', '4', '8', '5', '7', '4', '2', '0', '8', '0', '0', '0', '0', '0', '/', '5', '6', '4', '7', '3', '8', '7', '9', '8', '9', '6', '3', '7', '9', '2', '5', '7', '4', '2', '3', '9', '6', '0', '9', '2', '4', '2', '8', '2', '7', '3', '1', '2', '6', '7', '9', '1', '3', '0', '7', '8', '2', '4', '8', '6', '3', '3', '7', '7', '7', '3', '5', '6', '9', '4', '0', '9', '3', '4', '1', '4', '3', '9', '5', '7', '6', '7']) = .ok rational185 := by
  rw [parseRational_ofList]
  rfl

theorem rational186_decoded :
    parseRational (String.ofList ['1', '0', '7', '1', '0', '3', '1', '6', '5', '9', '6', '1', '1', '3', '4', '8', '3', '3', '4', '8', '0', '5', '8', '6', '2', '8', '7', '3', '0', '5', '7', '6', '9', '2', '1', '3', '3', '9', '9', '7', '7', '0', '2', '7', '9', '8', '9', '6', '7', '1', '6', '8', '6', '7', '0', '6', '6', '8', '7', '0', '7', '5', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '8', '3', '9', '3', '0', '7', '2', '6', '5', '9', '9', '4', '2', '2', '5', '6', '4', '5', '8', '0', '4', '0', '9', '3', '2', '1', '7', '9', '8', '7', '4', '1', '3', '2', '0', '8', '3', '3', '5', '6', '5', '9', '5', '3', '9', '8', '0', '0', '6', '9', '0', '1', '7', '7', '4', '2', '9', '0', '8', '8', '6', '3', '4', '7', '3', '1', '6', '4', '1', '9', '2', '6', '8', '1', '9', '0', '1', '5', '9', '2', '6', '9', '1', '6', '5', '5', '3', '8', '1', '0', '7']) = .ok rational186 := by
  rw [parseRational_ofList]
  rfl

theorem rational187_decoded :
    parseRational (String.ofList ['4', '2', '9', '1', '5', '1', '4', '4', '8', '8', '8', '1', '9', '4', '1', '8', '7', '3', '8', '0', '6', '4', '3', '0', '5', '0', '6', '8', '2', '0', '5', '2', '3', '/', '2', '4', '4', '2', '6', '0', '9', '1', '2', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational187 := by
  rw [parseRational_ofList]
  rfl

theorem rational188_decoded :
    parseRational (String.ofList ['3', '4', '9', '1', '7', '1', '0', '0', '7', '3', '/', '4', '2', '2', '1', '0', '0', '0', '0', '0', '0', '0']) = .ok rational188 := by
  rw [parseRational_ofList]
  rfl

theorem rational189_decoded :
    parseRational (String.ofList ['7', '0', '3', '0', '6', '5', '5', '5', '3', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0']) = .ok rational189 := by
  rw [parseRational_ofList]
  rfl

theorem rational190_decoded :
    parseRational (String.ofList ['2', '1', '0', '9', '7', '1', '0', '8', '4', '3', '3', '/', '1', '2', '6', '6', '3', '0', '0', '0', '0', '0', '0', '0']) = .ok rational190 := by
  rw [parseRational_ofList]
  rfl

theorem rational191_decoded :
    parseRational (String.ofList ['1', '1', '4', '0', '1', '9', '7', '3', '0', '9', '/', '3', '3', '7', '6', '8', '0', '0', '0', '0', '0', '0']) = .ok rational191 := by
  rw [parseRational_ofList]
  rfl

theorem rational192_decoded :
    parseRational (String.ofList ['1', '0', '3', '4', '7', '0', '3', '2', '6', '3', '/', '3', '3', '7', '6', '8', '0', '0', '0', '0', '0', '0']) = .ok rational192 := by
  rw [parseRational_ofList]
  rfl

theorem rational193_decoded :
    parseRational (String.ofList ['1', '2', '6', '0', '4', '1', '2', '7', '1', '7', '/', '4', '2', '2', '1', '0', '0', '0', '0', '0', '0', '0']) = .ok rational193 := by
  rw [parseRational_ofList]
  rfl

theorem rational194_decoded :
    parseRational (String.ofList ['1', '2', '3', '0', '3', '8', '9', '3', '5', '3', '/', '4', '2', '2', '1', '0', '0', '0', '0', '0', '0', '0']) = .ok rational194 := by
  rw [parseRational_ofList]
  rfl

theorem rational195_decoded :
    parseRational (String.ofList ['3', '6', '0', '3', '2', '3', '8', '0', '6', '3', '/', '1', '2', '6', '6', '3', '0', '0', '0', '0', '0', '0', '0']) = .ok rational195 := by
  rw [parseRational_ofList]
  rfl

theorem rational196_decoded :
    parseRational (String.ofList ['5', '2', '7', '1', '7', '8', '1', '7', '6', '1', '4', '3', '8', '7', '7', '3', '9', '8', '2', '6', '6', '0', '1', '9', '4', '9', '3', '0', '4', '8', '8', '2', '7', '7', '2', '1', '5', '8', '7', '0', '9', '7', '6', '0', '0', '0', '0', '0', '/', '1', '7', '6', '4', '8', '0', '4', '5', '6', '3', '3', '3', '2', '9', '9', '6', '1', '3', '5', '2', '3', '0', '8', '4', '0', '9', '3', '6', '1', '9', '2', '2', '3', '1', '7', '3', '9', '4', '2', '3', '8', '1', '0', '7', '9', '7', '8', '2', '7', '4', '3', '1', '7', '9', '9', '2', '8', '8', '2', '2', '9', '9', '4', '4', '7', '3']) = .ok rational196 := by
  rw [parseRational_ofList]
  rfl

theorem rational197_decoded :
    parseRational (String.ofList ['8', '3', '6', '7', '1', '6', '7', '0', '0', '8', '5', '1', '9', '9', '6', '0', '9', '7', '6', '3', '7', '2', '4', '7', '0', '1', '5', '8', '8', '7', '7', '3', '9', '2', '3', '7', '1', '0', '1', '7', '4', '5', '4', '1', '7', '5', '7', '9', '1', '5', '8', '7', '4', '4', '8', '8', '9', '7', '6', '5', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '7', '9', '2', '8', '6', '9', '5', '0', '9', '4', '6', '2', '4', '3', '3', '9', '0', '1', '0', '5', '7', '5', '1', '0', '5', '9', '6', '9', '8', '7', '1', '4', '2', '1', '6', '1', '2', '1', '4', '4', '6', '5', '3', '0', '1', '1', '3', '4', '9', '8', '5', '2', '2', '6', '0', '7', '8', '5', '0', '2', '0', '9', '0', '7', '9', '3', '1', '3', '9', '7', '5', '3', '0', '6', '8', '8', '0', '3', '5', '4', '9', '6', '5', '8', '7', '6', '8', '3', '6', '9']) = .ok rational197 := by
  rw [parseRational_ofList]
  rfl

theorem rational198_decoded :
    parseRational (String.ofList ['2', '4', '0', '1', '4', '5', '4', '6', '3', '7', '6', '1', '6', '3', '8', '8', '5', '2', '8', '9', '8', '5', '6', '3', '6', '5', '6', '9', '8', '4', '7', '0', '8', '3', '1', '0', '7', '/', '1', '7', '4', '9', '9', '2', '8', '9', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational198 := by
  rw [parseRational_ofList]
  rfl

theorem rational199_decoded :
    parseRational (String.ofList ['6', '9', '8', '3', '4', '2', '4', '3', '6', '7', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0', '0']) = .ok rational199 := by
  rw [parseRational_ofList]
  rfl

theorem rational200_decoded :
    parseRational (String.ofList ['7', '0', '3', '0', '6', '5', '9', '7', '5', '1', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0', '0']) = .ok rational200 := by
  rw [parseRational_ofList]
  rfl

theorem rational201_decoded :
    parseRational (String.ofList ['8', '4', '3', '8', '8', '4', '2', '5', '2', '9', '/', '5', '0', '6', '5', '2', '0', '0', '0', '0', '0', '0']) = .ok rational201 := by
  rw [parseRational_ofList]
  rfl

theorem rational202_decoded :
    parseRational (String.ofList ['1', '8', '4', '1', '7', '2', '0', '1', '0', '7', '/', '5', '6', '2', '8', '0', '0', '0', '0', '0', '0', '0']) = .ok rational202 := by
  rw [parseRational_ofList]
  rfl

theorem rational203_decoded :
    parseRational (String.ofList ['1', '7', '5', '3', '8', '0', '9', '8', '0', '9', '/', '5', '6', '2', '8', '0', '0', '0', '0', '0', '0', '0']) = .ok rational203 := by
  rw [parseRational_ofList]
  rfl

theorem rational204_decoded :
    parseRational (String.ofList ['8', '5', '4', '9', '2', '7', '3', '3', '/', '2', '8', '1', '4', '0', '0', '0', '0', '0', '0']) = .ok rational204 := by
  rw [parseRational_ofList]
  rfl

theorem rational205_decoded :
    parseRational (String.ofList ['4', '9', '2', '1', '5', '4', '8', '9', '7', '/', '1', '6', '8', '8', '4', '0', '0', '0', '0', '0', '0']) = .ok rational205 := by
  rw [parseRational_ofList]
  rfl

theorem rational206_decoded :
    parseRational (String.ofList ['7', '2', '0', '6', '4', '8', '0', '3', '4', '7', '/', '2', '5', '3', '2', '6', '0', '0', '0', '0', '0', '0', '0']) = .ok rational206 := by
  rw [parseRational_ofList]
  rfl

theorem rational207_decoded :
    parseRational (String.ofList ['1', '8', '4', '3', '7', '4', '6', '6', '5', '2', '9', '1', '4', '0', '3', '7', '1', '4', '0', '0', '7', '0', '9', '1', '4', '8', '2', '5', '9', '3', '3', '9', '3', '4', '3', '9', '4', '3', '3', '6', '4', '3', '6', '2', '2', '4', '0', '0', '0', '0', '0', '/', '7', '9', '0', '2', '0', '4', '8', '6', '7', '8', '6', '2', '4', '7', '7', '9', '5', '3', '1', '4', '1', '1', '5', '0', '9', '2', '7', '0', '7', '2', '5', '2', '0', '3', '8', '5', '5', '8', '0', '5', '7', '6', '9', '5', '6', '1', '5', '6', '2', '6', '4', '8', '6', '6', '5', '6', '9', '7', '1', '0', '8', '4', '6', '9']) = .ok rational207 := by
  rw [parseRational_ofList]
  rfl

theorem rational208_decoded :
    parseRational (String.ofList ['5', '1', '9', '8', '4', '7', '2', '5', '2', '4', '9', '6', '9', '1', '8', '2', '9', '0', '5', '6', '5', '5', '1', '5', '1', '8', '8', '9', '1', '8', '6', '5', '0', '4', '0', '6', '0', '7', '4', '6', '9', '1', '8', '1', '7', '7', '8', '4', '0', '8', '8', '3', '2', '9', '6', '7', '6', '7', '7', '8', '9', '5', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '6', '0', '9', '0', '9', '1', '8', '1', '0', '4', '5', '8', '3', '6', '0', '8', '0', '6', '1', '4', '2', '2', '5', '7', '5', '6', '0', '9', '0', '7', '5', '5', '4', '8', '9', '6', '6', '3', '1', '3', '2', '3', '7', '9', '7', '6', '0', '0', '0', '1', '1', '4', '2', '5', '8', '0', '7', '8', '6', '7', '8', '0', '3', '9', '7', '3', '8', '0', '4', '2', '8', '9', '0', '5', '5', '0', '7', '5', '7', '4', '1', '9', '5', '2', '4', '2', '8', '9']) = .ok rational208 := by
  rw [parseRational_ofList]
  rfl

theorem rational209_decoded :
    parseRational (String.ofList ['6', '8', '3', '0', '0', '9', '0', '8', '3', '3', '4', '0', '8', '1', '8', '1', '9', '1', '3', '0', '6', '7', '5', '2', '4', '9', '1', '4', '8', '1', '8', '8', '9', '1', '6', '6', '7', '8', '6', '6', '9', '9', '/', '2', '2', '1', '7', '1', '0', '7', '4', '4', '9', '8', '5', '3', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational209 := by
  rw [parseRational_ofList]
  rfl

theorem rational210_decoded :
    parseRational (String.ofList ['9', '6', '0', '4', '7', '0', '7', '5', '3', '2', '7', '5', '6', '8', '5', '5', '0', '0', '6', '8', '5', '0', '4', '4', '1', '1', '0', '8', '1', '8', '1', '5', '1', '7', '7', '8', '1', '2', '1', '5', '4', '1', '7', '0', '1', '5', '3', '1', '/', '8', '1', '5', '5', '1', '8', '6', '3', '3', '2', '7', '9', '7', '4', '3', '8', '5', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational210 := by
  rw [parseRational_ofList]
  rfl

theorem integer000_decoded :
    parseInteger (String.ofList ['3', '4', '0', '5', '3', '6', '9', '5', '6', '5', '7', '6']) = .ok integer000 := by
  rw [parseInteger_ofList]
  rfl

theorem integer001_decoded :
    parseInteger (String.ofList ['8', '6', '5', '7', '2', '3', '7', '7', '9', '0', '1', '4']) = .ok integer001 := by
  rw [parseInteger_ofList]
  rfl

theorem integer002_decoded :
    parseInteger (String.ofList ['1', '7', '2', '5', '4', '4', '5', '5', '2', '7', '6', '3', '1', '4', '7', '3']) = .ok integer002 := by
  rw [parseInteger_ofList]
  rfl

theorem integer003_decoded :
    parseInteger (String.ofList ['4', '4', '6', '8', '1', '0', '6', '3', '1', '8', '8', '7', '3', '9', '0', '0']) = .ok integer003 := by
  rw [parseInteger_ofList]
  rfl

theorem integer004_decoded :
    parseInteger (String.ofList ['2', '8', '5', '2', '9', '4', '6', '4', '5', '0', '7', '4']) = .ok integer004 := by
  rw [parseInteger_ofList]
  rfl

theorem integer005_decoded :
    parseInteger (String.ofList ['7', '3', '8', '7', '7', '0', '0', '7', '9', '5', '4', '8']) = .ok integer005 := by
  rw [parseInteger_ofList]
  rfl

theorem integer006_decoded :
    parseInteger (String.ofList ['2', '8', '5', '2', '8', '5', '5', '1', '3', '1', '1', '2']) = .ok integer006 := by
  rw [parseInteger_ofList]
  rfl

theorem integer007_decoded :
    parseInteger (String.ofList ['7', '3', '8', '9', '3', '0', '7', '3', '9', '4', '9', '2']) = .ok integer007 := by
  rw [parseInteger_ofList]
  rfl

theorem integer008_decoded :
    parseInteger (String.ofList ['1', '5', '2', '5', '2', '5', '6', '3', '3', '8', '2', '0', '7', '1', '4', '8']) = .ok integer008 := by
  rw [parseInteger_ofList]
  rfl

theorem integer009_decoded :
    parseInteger (String.ofList ['3', '9', '8', '0', '6', '7', '5', '8', '6', '3', '9', '9', '1', '6', '2', '2']) = .ok integer009 := by
  rw [parseInteger_ofList]
  rfl

theorem integer010_decoded :
    parseInteger (String.ofList ['2', '3', '6', '6', '7', '5', '4', '7', '6', '9', '2', '7']) = .ok integer010 := by
  rw [parseInteger_ofList]
  rfl

theorem integer011_decoded :
    parseInteger (String.ofList ['6', '1', '3', '1', '5', '1', '1', '4', '0', '8', '3', '8']) = .ok integer011 := by
  rw [parseInteger_ofList]
  rfl

theorem integer012_decoded :
    parseInteger (String.ofList ['2', '3', '6', '6', '6', '8', '4', '6', '2', '2', '2', '6']) = .ok integer012 := by
  rw [parseInteger_ofList]
  rfl

theorem integer013_decoded :
    parseInteger (String.ofList ['6', '1', '4', '2', '1', '5', '9', '5', '7', '0', '7', '5']) = .ok integer013 := by
  rw [parseInteger_ofList]
  rfl

theorem integer014_decoded :
    parseInteger (String.ofList ['1', '8', '4', '8', '5', '9', '2', '2', '4', '9', '8', '4', '7', '1', '1', '7']) = .ok integer014 := by
  rw [parseInteger_ofList]
  rfl

theorem integer015_decoded :
    parseInteger (String.ofList ['4', '7', '8', '4', '0', '7', '5', '1', '9', '7', '5', '0', '0', '6', '3', '1']) = .ok integer015 := by
  rw [parseInteger_ofList]
  rfl

end ImbalancedChen.P2Saving16Cell00ScalarDecode
