import ImbalancedChen.P2OriginalSaving16DecoderChars
import ImbalancedChen.P2Saving16Cell01TypedPayload
import ImbalancedChen.P2Saving16Cell00ScalarDecode

/-! Cell01 decoder proof candidates. SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/
namespace ImbalancedChen.P2Saving16Cell01ScalarDecode
open P2OriginalSaving16OriginalArchive
open P2Saving16Cell01TypedPayload

theorem rational000_decoded :
    parseRational (String.ofList ['1']) = .ok rational000 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational000_decoded

theorem rational001_decoded :
    parseRational (String.ofList ['2']) = .ok rational001 := by
  rw [parseRational_ofList]
  rfl

theorem rational002_decoded :
    parseRational (String.ofList ['3']) = .ok rational002 := by
  rw [parseRational_ofList]
  rfl

theorem rational003_decoded :
    parseRational (String.ofList ['1', '6', '/', '3']) = .ok rational003 := by
  rw [parseRational_ofList]
  rfl

theorem rational004_decoded :
    parseRational (String.ofList ['1', '9', '/', '1', '2']) = .ok rational004 := by
  rw [parseRational_ofList]
  rfl

theorem rational005_decoded :
    parseRational (String.ofList ['2', '/', '3']) = .ok rational005 := by
  rw [parseRational_ofList]
  rfl

theorem rational006_decoded :
    parseRational (String.ofList ['1', '/', '3']) = .ok rational006 := by
  rw [parseRational_ofList]
  rfl

theorem rational007_decoded :
    parseRational (String.ofList ['3', '9', '0', '6', '2', '9', '/', '2', '5', '0', '0', '0', '0', '0']) = .ok rational007 := by
  rw [parseRational_ofList]
  rfl

theorem rational008_decoded :
    parseRational (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']) = .ok rational008 := by
  rw [parseRational_ofList]
  rfl

theorem rational009_decoded :
    parseRational (String.ofList ['3', '9', '0', '6', '2', '9', '/', '5', '0', '0', '0', '0', '0', '0']) = .ok rational009 := by
  rw [parseRational_ofList]
  rfl

theorem rational010_decoded :
    parseRational (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']) = .ok rational010 := by
  rw [parseRational_ofList]
  rfl

theorem rational011_decoded :
    parseRational (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0']) = .ok rational011 := by
  rw [parseRational_ofList]
  rfl

theorem rational012_decoded :
    parseRational (String.ofList ['2', '1', '3', '4', '3', '8', '7', '/', '1', '3', '1', '5', '0', '0', '0', '0']) = .ok rational012 := by
  rw [parseRational_ofList]
  rfl

theorem rational013_decoded :
    parseRational (String.ofList ['7', '6', '7', '1', '8', '7', '/', '6', '5', '7', '5', '0', '0', '0']) = .ok rational013 := by
  rw [parseRational_ofList]
  rfl

theorem rational014_decoded :
    parseRational (String.ofList ['2', '1', '3', '4', '3', '8', '7', '/', '2', '6', '3', '0', '0', '0', '0', '0']) = .ok rational014 := by
  rw [parseRational_ofList]
  rfl

theorem rational015_decoded :
    parseRational (String.ofList ['9', '3', '4', '3', '6', '1', '/', '2', '6', '3', '0', '0', '0', '0', '0']) = .ok rational015 := by
  rw [parseRational_ofList]
  rfl

theorem rational016_decoded :
    parseRational (String.ofList ['3', '3', '4', '3', '7', '4', '3', '/', '1', '3', '1', '5', '0', '0', '0', '0', '0']) = .ok rational016 := by
  rw [parseRational_ofList]
  rfl

theorem rational017_decoded :
    parseRational (String.ofList ['1', '9', '5', '3', '1', '3', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok rational017 := by
  rw [parseRational_ofList]
  rfl

theorem rational018_decoded :
    parseRational (String.ofList ['2', '3', '4', '3', '7', '9', '/', '2', '4', '0', '0', '0', '0', '0']) = .ok rational018 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational077_decoded

theorem rational019_decoded :
    parseRational (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']) = .ok rational019 := by
  rw [parseRational_ofList]
  rfl

theorem rational020_decoded :
    parseRational (String.ofList ['1', '3', '0', '2', '0', '7', '/', '4', '0', '0', '0', '0', '0', '0']) = .ok rational020 := by
  rw [parseRational_ofList]
  rfl

theorem rational021_decoded :
    parseRational (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok rational021 := by
  rw [parseRational_ofList]
  rfl

theorem rational022_decoded :
    parseRational (String.ofList ['9', '1', '0', '9', '4', '2', '3', '/', '5', '5', '7', '5', '0', '0', '0', '0']) = .ok rational022 := by
  rw [parseRational_ofList]
  rfl

theorem rational023_decoded :
    parseRational (String.ofList ['1', '6', '2', '4', '9', '9', '9', '/', '1', '3', '9', '3', '7', '5', '0', '0']) = .ok rational023 := by
  rw [parseRational_ofList]
  rfl

theorem rational024_decoded :
    parseRational (String.ofList ['9', '1', '0', '9', '4', '2', '3', '/', '1', '1', '1', '5', '0', '0', '0', '0', '0']) = .ok rational024 := by
  rw [parseRational_ofList]
  rfl

theorem rational025_decoded :
    parseRational (String.ofList ['3', '8', '9', '0', '5', '6', '9', '/', '1', '1', '1', '5', '0', '0', '0', '0', '0']) = .ok rational025 := by
  rw [parseRational_ofList]
  rfl

theorem rational026_decoded :
    parseRational (String.ofList ['2', '5', '6', '2', '5', '0', '7', '/', '1', '1', '1', '5', '0', '0', '0', '0', '0']) = .ok rational026 := by
  rw [parseRational_ofList]
  rfl

theorem rational027_decoded :
    parseRational (String.ofList ['4', '9', '2', '9', '7', '1', '/', '3', '0', '0', '0', '0', '0', '0']) = .ok rational027 := by
  rw [parseRational_ofList]
  rfl

theorem rational028_decoded :
    parseRational (String.ofList ['6', '0', '1', '5', '7', '/', '6', '0', '0', '0', '0', '0']) = .ok rational028 := by
  rw [parseRational_ofList]
  rfl

theorem rational029_decoded :
    parseRational (String.ofList ['9', '6', '0', '9', '3', '/', '1', '0', '0', '0', '0', '0', '0']) = .ok rational029 := by
  rw [parseRational_ofList]
  rfl

theorem rational030_decoded :
    parseRational (String.ofList ['3', '2', '0', '3', '1', '/', '1', '0', '0', '0', '0', '0', '0']) = .ok rational030 := by
  rw [parseRational_ofList]
  rfl

theorem rational031_decoded :
    parseRational (String.ofList ['8', '3', '5', '9', '3', '/', '3', '0', '0', '0', '0', '0', '0']) = .ok rational031 := by
  rw [parseRational_ofList]
  rfl

theorem rational032_decoded :
    parseRational (String.ofList ['3', '9', '5', '3', '1', '4', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0']) = .ok rational032 := by
  rw [parseRational_ofList]
  rfl

theorem rational033_decoded :
    parseRational (String.ofList ['4', '8', '4', '3', '8', '1', '/', '4', '8', '0', '0', '0', '0', '0']) = .ok rational033 := by
  rw [parseRational_ofList]
  rfl

theorem rational034_decoded :
    parseRational (String.ofList ['7', '6', '5', '6', '1', '9', '/', '8', '0', '0', '0', '0', '0', '0']) = .ok rational034 := by
  rw [parseRational_ofList]
  rfl

theorem rational035_decoded :
    parseRational (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']) = .ok rational035 := by
  rw [parseRational_ofList]
  rfl

theorem rational036_decoded :
    parseRational (String.ofList ['6', '4', '0', '6', '1', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']) = .ok rational036 := by
  rw [parseRational_ofList]
  rfl

theorem rational037_decoded :
    parseRational (String.ofList ['1', '3', '9', '2', '1', '9', '1', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']) = .ok rational037 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational021_decoded

theorem rational038_decoded :
    parseRational (String.ofList ['1', '7', '9', '0', '6', '2', '9', '/', '1', '6', '8', '0', '0', '0', '0', '0']) = .ok rational038 := by
  rw [parseRational_ofList]
  rfl

theorem rational039_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']) = .ok rational039 := by
  rw [parseRational_ofList]
  rfl

theorem rational040_decoded :
    parseRational (String.ofList ['8', '2', '8', '1', '2', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']) = .ok rational040 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational022_decoded

theorem rational041_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '8', '4', '0', '0', '0', '0', '0', '0']) = .ok rational041 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational023_decoded

theorem rational042_decoded :
    parseRational (String.ofList ['9', '5', '3', '1', '0', '9', '/', '7', '0', '0', '0', '0', '0', '0']) = .ok rational042 := by
  rw [parseRational_ofList]
  rfl

theorem rational043_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '4', '9', '9', '/', '4', '2', '0', '0', '0', '0', '0', '0']) = .ok rational043 := by
  rw [parseRational_ofList]
  rfl

theorem rational044_decoded :
    parseRational (String.ofList ['1', '3', '9', '2', '1', '9', '2', '7', '/', '8', '4', '0', '0', '0', '0', '0', '0']) = .ok rational044 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational026_decoded

theorem rational045_decoded :
    parseRational (String.ofList ['8', '9', '5', '3', '1', '6', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']) = .ok rational045 := by
  rw [parseRational_ofList]
  rfl

theorem rational046_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']) = .ok rational046 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational091_decoded

theorem rational047_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']) = .ok rational047 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational027_decoded

theorem rational048_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']) = .ok rational048 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational028_decoded

theorem rational049_decoded :
    parseRational (String.ofList ['2', '8', '5', '9', '3', '3', '1', '/', '2', '1', '0', '0', '0', '0', '0', '0']) = .ok rational049 := by
  rw [parseRational_ofList]
  rfl

theorem rational050_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '4', '9', '1', '/', '4', '2', '0', '0', '0', '0', '0', '0']) = .ok rational050 := by
  exact ImbalancedChen.P2Saving16Cell00ScalarDecode.rational052_decoded

theorem rational051_decoded :
    parseRational (String.ofList ['2', '6', '1', '4', '0', '6', '6', '1', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok rational051 := by
  rw [parseRational_ofList]
  rfl

theorem rational052_decoded :
    parseRational (String.ofList ['3', '2', '9', '6', '8', '8', '7', '/', '3', '1', '2', '0', '0', '0', '0', '0']) = .ok rational052 := by
  rw [parseRational_ofList]
  rfl

theorem rational053_decoded :
    parseRational (String.ofList ['4', '8', '2', '8', '1', '1', '3', '/', '5', '2', '0', '0', '0', '0', '0', '0']) = .ok rational053 := by
  rw [parseRational_ofList]
  rfl

theorem rational054_decoded :
    parseRational (String.ofList ['1', '6', '0', '9', '3', '7', '1', '/', '5', '2', '0', '0', '0', '0', '0', '0']) = .ok rational054 := by
  rw [parseRational_ofList]
  rfl

theorem rational055_decoded :
    parseRational (String.ofList ['4', '3', '2', '8', '0', '8', '9', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok rational055 := by
  rw [parseRational_ofList]
  rfl

theorem rational056_decoded :
    parseRational (String.ofList ['2', '0', '1', '5', '6', '2', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok rational056 := by
  rw [parseRational_ofList]
  rfl

theorem rational057_decoded :
    parseRational (String.ofList ['3', '2', '8', '1', '2', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok rational057 := by
  rw [parseRational_ofList]
  rfl

theorem rational058_decoded :
    parseRational (String.ofList ['7', '0', '3', '1', '1', '/', '2', '0', '0', '0', '0', '0', '0']) = .ok rational058 := by
  rw [parseRational_ofList]
  rfl

theorem rational059_decoded :
    parseRational (String.ofList ['1', '0', '9', '3', '7', '7', '/', '4', '0', '0', '0', '0', '0', '0']) = .ok rational059 := by
  rw [parseRational_ofList]
  rfl

theorem rational060_decoded :
    parseRational (String.ofList ['1', '7', '1', '8', '6', '7', '/', '4', '0', '0', '0', '0', '0', '0']) = .ok rational060 := by
  rw [parseRational_ofList]
  rfl

theorem rational061_decoded :
    parseRational (String.ofList ['2', '0', '1', '5', '6', '2', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok rational061 := by
  rw [parseRational_ofList]
  rfl

theorem rational062_decoded :
    parseRational (String.ofList ['4', '2', '1', '8', '6', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok rational062 := by
  rw [parseRational_ofList]
  rfl

theorem rational063_decoded :
    parseRational (String.ofList ['3', '2', '8', '1', '2', '9', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok rational063 := by
  rw [parseRational_ofList]
  rfl

theorem rational064_decoded :
    parseRational (String.ofList ['3', '2', '8', '1', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok rational064 := by
  rw [parseRational_ofList]
  rfl

theorem rational065_decoded :
    parseRational (String.ofList ['1', '0', '3', '1', '2', '1', '/', '2', '4', '0', '0', '0', '0', '0']) = .ok rational065 := by
  rw [parseRational_ofList]
  rfl

theorem rational066_decoded :
    parseRational (String.ofList ['1', '0', '0', '7', '8', '3', '6', '1', '/', '6', '0', '0', '0', '0', '0', '0', '0']) = .ok rational066 := by
  rw [parseRational_ofList]
  rfl

theorem rational067_decoded :
    parseRational (String.ofList ['1', '6', '4', '0', '3', '8', '9', '/', '6', '0', '0', '0', '0', '0', '0', '0']) = .ok rational067 := by
  rw [parseRational_ofList]
  rfl

theorem rational068_decoded :
    parseRational (String.ofList ['2', '2', '2', '3', '4', '4', '1', '1', '/', '1', '3', '2', '0', '0', '0', '0', '0', '0']) = .ok rational068 := by
  rw [parseRational_ofList]
  rfl

theorem rational069_decoded :
    parseRational (String.ofList ['2', '8', '2', '8', '1', '3', '7', '/', '2', '6', '4', '0', '0', '0', '0', '0']) = .ok rational069 := by
  rw [parseRational_ofList]
  rfl

theorem rational070_decoded :
    parseRational (String.ofList ['4', '0', '4', '6', '8', '6', '3', '/', '4', '4', '0', '0', '0', '0', '0', '0']) = .ok rational070 := by
  rw [parseRational_ofList]
  rfl

theorem rational071_decoded :
    parseRational (String.ofList ['4', '0', '4', '6', '8', '6', '3', '/', '1', '3', '2', '0', '0', '0', '0', '0', '0']) = .ok rational071 := by
  rw [parseRational_ofList]
  rfl

theorem rational072_decoded :
    parseRational (String.ofList ['3', '5', '4', '6', '8', '3', '9', '/', '1', '3', '2', '0', '0', '0', '0', '0', '0']) = .ok rational072 := by
  rw [parseRational_ofList]
  rfl

theorem rational073_decoded :
    parseRational (String.ofList ['1', '0', '7', '9', '6', '8', '8', '7', '/', '6', '4', '0', '0', '0', '0', '0', '0']) = .ok rational073 := by
  rw [parseRational_ofList]
  rfl

theorem rational074_decoded :
    parseRational (String.ofList ['2', '9', '7', '3', '4', '3', '7', '1', '/', '2', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok rational074 := by
  rw [parseRational_ofList]
  rfl

theorem rational075_decoded :
    parseRational (String.ofList ['1', '0', '7', '9', '6', '8', '8', '7', '/', '1', '2', '8', '0', '0', '0', '0', '0', '0']) = .ok rational075 := by
  rw [parseRational_ofList]
  rfl

theorem rational076_decoded :
    parseRational (String.ofList ['8', '1', '4', '0', '5', '9', '7', '/', '2', '5', '6', '0', '0', '0', '0', '0', '0']) = .ok rational076 := by
  rw [parseRational_ofList]
  rfl

theorem rational077_decoded :
    parseRational (String.ofList ['1', '7', '0', '3', '1', '1', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']) = .ok rational077 := by
  rw [parseRational_ofList]
  rfl

theorem rational078_decoded :
    parseRational (String.ofList ['6', '1', '0', '9', '3', '7', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']) = .ok rational078 := by
  rw [parseRational_ofList]
  rfl

theorem rational079_decoded :
    parseRational (String.ofList ['9', '2', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0']) = .ok rational079 := by
  rw [parseRational_ofList]
  rfl

theorem rational080_decoded :
    parseRational (String.ofList ['1', '0', '0', '1', '5', '6', '3', '7', '/', '5', '9', '0', '0', '0', '0', '0', '0']) = .ok rational080 := by
  rw [parseRational_ofList]
  rfl

theorem rational081_decoded :
    parseRational (String.ofList ['2', '7', '3', '9', '0', '6', '2', '1', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0']) = .ok rational081 := by
  rw [parseRational_ofList]
  rfl

theorem rational082_decoded :
    parseRational (String.ofList ['1', '0', '0', '1', '5', '6', '3', '7', '/', '1', '1', '8', '0', '0', '0', '0', '0', '0']) = .ok rational082 := by
  rw [parseRational_ofList]
  rfl

theorem rational083_decoded :
    parseRational (String.ofList ['7', '3', '5', '9', '3', '4', '7', '/', '2', '3', '6', '0', '0', '0', '0', '0', '0']) = .ok rational083 := by
  rw [parseRational_ofList]
  rfl

theorem rational084_decoded :
    parseRational (String.ofList ['3', '0', '1', '5', '6', '0', '1', '/', '1', '1', '8', '0', '0', '0', '0', '0', '0']) = .ok rational084 := by
  rw [parseRational_ofList]
  rfl

theorem rational085_decoded :
    parseRational (String.ofList ['9', '2', '3', '4', '3', '7', '1', '/', '5', '4', '0', '0', '0', '0', '0', '0']) = .ok rational085 := by
  rw [parseRational_ofList]
  rfl

theorem rational086_decoded :
    parseRational (String.ofList ['1', '1', '8', '5', '9', '4', '5', '1', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']) = .ok rational086 := by
  rw [parseRational_ofList]
  rfl

theorem rational087_decoded :
    parseRational (String.ofList ['9', '2', '3', '4', '3', '7', '1', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']) = .ok rational087 := by
  rw [parseRational_ofList]
  rfl

theorem rational088_decoded :
    parseRational (String.ofList ['9', '2', '3', '4', '0', '8', '3', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']) = .ok rational088 := by
  rw [parseRational_ofList]
  rfl

theorem rational089_decoded :
    parseRational (String.ofList ['6', '5', '6', '2', '7', '/', '2', '7', '0', '0', '0', '0', '0']) = .ok rational089 := by
  rw [parseRational_ofList]
  rfl

theorem rational090_decoded :
    parseRational (String.ofList ['1', '6', '4', '0', '6', '3', '/', '6', '7', '5', '0', '0', '0', '0']) = .ok rational090 := by
  rw [parseRational_ofList]
  rfl

theorem rational091_decoded :
    parseRational (String.ofList ['2', '2', '0', '3', '0', '0', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0']) = .ok rational091 := by
  rw [parseRational_ofList]
  rfl

theorem rational092_decoded :
    parseRational (String.ofList ['9', '2', '3', '4', '3', '7', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']) = .ok rational092 := by
  rw [parseRational_ofList]
  rfl

theorem rational093_decoded :
    parseRational (String.ofList ['1', '1', '8', '5', '9', '4', '4', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']) = .ok rational093 := by
  rw [parseRational_ofList]
  rfl

theorem rational094_decoded :
    parseRational (String.ofList ['9', '2', '3', '4', '3', '7', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']) = .ok rational094 := by
  rw [parseRational_ofList]
  rfl

theorem rational095_decoded :
    parseRational (String.ofList ['9', '2', '3', '4', '0', '9', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']) = .ok rational095 := by
  rw [parseRational_ofList]
  rfl

theorem rational096_decoded :
    parseRational (String.ofList ['3', '2', '8', '1', '3', '3', '/', '1', '3', '5', '0', '0', '0', '0', '0']) = .ok rational096 := by
  rw [parseRational_ofList]
  rfl

theorem rational097_decoded :
    parseRational (String.ofList ['8', '2', '0', '3', '1', '/', '3', '3', '7', '5', '0', '0', '0']) = .ok rational097 := by
  rw [parseRational_ofList]
  rfl

theorem rational098_decoded :
    parseRational (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']) = .ok rational098 := by
  rw [parseRational_ofList]
  rfl

theorem rational099_decoded :
    parseRational (String.ofList ['4', '1', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '0']) = .ok rational099 := by
  rw [parseRational_ofList]
  rfl

theorem rational100_decoded :
    parseRational (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '0']) = .ok rational100 := by
  rw [parseRational_ofList]
  rfl

theorem rational101_decoded :
    parseRational (String.ofList ['1', '4', '2', '3', '4', '4', '9', '3', '/', '8', '2', '0', '0', '0', '0', '0', '0']) = .ok rational101 := by
  rw [parseRational_ofList]
  rfl

theorem rational102_decoded :
    parseRational (String.ofList ['4', '7', '9', '6', '8', '7', '3', '/', '4', '1', '0', '0', '0', '0', '0', '0']) = .ok rational102 := by
  rw [parseRational_ofList]
  rfl

theorem rational103_decoded :
    parseRational (String.ofList ['8', '1', '2', '5', '0', '3', '/', '1', '0', '2', '5', '0', '0', '0', '0']) = .ok rational103 := by
  rw [parseRational_ofList]
  rfl

theorem rational104_decoded :
    parseRational (String.ofList ['1', '5', '4', '6', '8', '6', '1', '/', '4', '1', '0', '0', '0', '0', '0', '0']) = .ok rational104 := by
  rw [parseRational_ofList]
  rfl

theorem rational105_decoded :
    parseRational (String.ofList ['1', '5', '4', '6', '8', '6', '1', '/', '8', '2', '0', '0', '0', '0', '0', '0']) = .ok rational105 := by
  rw [parseRational_ofList]
  rfl

theorem rational106_decoded :
    parseRational (String.ofList ['1', '5', '7', '2', '0', '3', '3', '6', '1', '/', '8', '9', '2', '0', '0', '0', '0', '0', '0']) = .ok rational106 := by
  rw [parseRational_ofList]
  rfl

theorem rational107_decoded :
    parseRational (String.ofList ['5', '2', '1', '4', '0', '6', '2', '1', '/', '4', '4', '6', '0', '0', '0', '0', '0', '0']) = .ok rational107 := by
  rw [parseRational_ofList]
  rfl

theorem rational108_decoded :
    parseRational (String.ofList ['1', '7', '7', '9', '6', '8', '8', '7', '/', '2', '2', '3', '0', '0', '0', '0', '0', '0']) = .ok rational108 := by
  rw [parseRational_ofList]
  rfl

theorem rational109_decoded :
    parseRational (String.ofList ['1', '6', '5', '4', '6', '8', '4', '7', '/', '4', '4', '6', '0', '0', '0', '0', '0', '0']) = .ok rational109 := by
  rw [parseRational_ofList]
  rfl

theorem rational110_decoded :
    parseRational (String.ofList ['1', '7', '0', '1', '5', '3', '8', '9', '/', '8', '9', '2', '0', '0', '0', '0', '0', '0']) = .ok rational110 := by
  rw [parseRational_ofList]
  rfl

theorem rational111_decoded :
    parseRational (String.ofList ['4', '6', '5', '9', '3', '7', '9', '/', '2', '6', '4', '0', '0', '0', '0', '0']) = .ok rational111 := by
  rw [parseRational_ofList]
  rfl

theorem rational112_decoded :
    parseRational (String.ofList ['7', '4', '5', '3', '2', '4', '1', '/', '6', '6', '0', '0', '0', '0', '0', '0']) = .ok rational112 := by
  rw [parseRational_ofList]
  rfl

theorem rational113_decoded :
    parseRational (String.ofList ['4', '5', '3', '1', '1', '9', '/', '5', '5', '0', '0', '0', '0', '0']) = .ok rational113 := by
  rw [parseRational_ofList]
  rfl

theorem rational114_decoded :
    parseRational (String.ofList ['4', '9', '6', '8', '7', '1', '/', '1', '3', '2', '0', '0', '0', '0', '0']) = .ok rational114 := by
  rw [parseRational_ofList]
  rfl

theorem rational115_decoded :
    parseRational (String.ofList ['4', '9', '6', '8', '7', '1', '/', '2', '6', '4', '0', '0', '0', '0', '0']) = .ok rational115 := by
  rw [parseRational_ofList]
  rfl

theorem rational116_decoded :
    parseRational (String.ofList ['7', '9', '2', '1', '7', '8', '3', '/', '6', '6', '0', '0', '0', '0', '0', '0']) = .ok rational116 := by
  rw [parseRational_ofList]
  rfl

theorem rational117_decoded :
    parseRational (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '3', '3', '0', '0', '0', '0', '0', '0']) = .ok rational117 := by
  rw [parseRational_ofList]
  rfl

theorem rational118_decoded :
    parseRational (String.ofList ['1', '5', '9', '3', '7', '4', '9', '/', '9', '0', '0', '0', '0', '0', '0']) = .ok rational118 := by
  rw [parseRational_ofList]
  rfl

theorem rational119_decoded :
    parseRational (String.ofList ['4', '1', '7', '1', '8', '9', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0']) = .ok rational119 := by
  rw [parseRational_ofList]
  rfl

theorem rational120_decoded :
    parseRational (String.ofList ['2', '8', '5', '9', '3', '8', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0']) = .ok rational120 := by
  rw [parseRational_ofList]
  rfl

theorem rational121_decoded :
    parseRational (String.ofList ['2', '8', '5', '9', '2', '8', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0']) = .ok rational121 := by
  rw [parseRational_ofList]
  rfl

theorem rational122_decoded :
    parseRational (String.ofList ['3', '2', '8', '1', '2', '7', '/', '9', '0', '0', '0', '0', '0', '0']) = .ok rational122 := by
  rw [parseRational_ofList]
  rfl

theorem rational123_decoded :
    parseRational (String.ofList ['3', '2', '8', '1', '2', '7', '/', '1', '8', '0', '0', '0', '0', '0', '0']) = .ok rational123 := by
  rw [parseRational_ofList]
  rfl

theorem rational124_decoded :
    parseRational (String.ofList ['5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']) = .ok rational124 := by
  rw [parseRational_ofList]
  rfl

theorem rational125_decoded :
    parseRational (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational125 := by
  rw [parseRational_ofList]
  rfl

theorem rational126_decoded :
    parseRational (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']) = .ok rational126 := by
  rw [parseRational_ofList]
  rfl

theorem rational127_decoded :
    parseRational (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']) = .ok rational127 := by
  rw [parseRational_ofList]
  rfl

end ImbalancedChen.P2Saving16Cell01ScalarDecode
