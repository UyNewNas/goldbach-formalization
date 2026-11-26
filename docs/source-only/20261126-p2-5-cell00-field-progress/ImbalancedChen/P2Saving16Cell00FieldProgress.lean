import ImbalancedChen.P2OriginalSaving16DecoderCompose
import ImbalancedChen.P2Saving16Cell00ScalarDecode

/-!
Candidate compositional certificate for the complete proposed cell00 record.
Every field and scalar must be checked against the unchanged original decoder.
This module does not replace JSON parsing or assume any closed success guard.
-/
namespace ImbalancedChen.P2Saving16Cell00FieldDecode
open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16OriginalArchive
open P2Saving16Cell00TypedPayload
open P2Saving16Cell00ScalarDecode

/- The original reader uses character-list strings. The simplifier normalizes
those strings before nested decoder calls are exposed. Literal-key aliases below
reuse the accepted scalar equations, and the Nat aliases specialize the accepted
generic character equation. No scalar parser computation is repeated here. -/
#check (900000 : Nat)
private theorem except_ok_bind {α β : Type} (a : α) (f : α → Except String β) :
    ((Except.ok a : Except String α) >>= f) = f a := rfl

#check (900001 : Nat)
private theorem except_ok_map {α β : Type} (a : α) (f : α → β) :
    f <$> (Except.ok a : Except String α) = .ok (f a) := rfl

#check (900002 : Nat)
private theorem except_pure_eq_ok {α : Type} (a : α) :
    (pure a : Except String α) = .ok a := rfl

attribute [local simp] except_ok_bind except_ok_map except_pure_eq_ok

#check (900003 : Nat)
private theorem nat000_literal_decoded :
    (SourceJson.Decode.read (.number "0") : Except String Nat) = .ok 0 :=
  decodeNat_number_ofList ['0']

#check (900004 : Nat)
private theorem nat001_literal_decoded :
    (SourceJson.Decode.read (.number "1") : Except String Nat) = .ok 1 :=
  decodeNat_number_ofList ['1']

#check (900005 : Nat)
private theorem nat002_literal_decoded :
    (SourceJson.Decode.read (.number "2") : Except String Nat) = .ok 2 :=
  decodeNat_number_ofList ['2']

#check (900006 : Nat)
private theorem nat003_literal_decoded :
    (SourceJson.Decode.read (.number "3") : Except String Nat) = .ok 3 :=
  decodeNat_number_ofList ['3']

#check (900007 : Nat)
private theorem nat004_literal_decoded :
    (SourceJson.Decode.read (.number "4") : Except String Nat) = .ok 4 :=
  decodeNat_number_ofList ['4']

#check (900008 : Nat)
private theorem nat005_literal_decoded :
    (SourceJson.Decode.read (.number "5") : Except String Nat) = .ok 5 :=
  decodeNat_number_ofList ['5']

#check (900009 : Nat)
private theorem nat006_literal_decoded :
    (SourceJson.Decode.read (.number "6") : Except String Nat) = .ok 6 :=
  decodeNat_number_ofList ['6']

#check (900010 : Nat)
private theorem nat007_literal_decoded :
    (SourceJson.Decode.read (.number "7") : Except String Nat) = .ok 7 :=
  decodeNat_number_ofList ['7']

#check (900011 : Nat)
private theorem nat008_literal_decoded :
    (SourceJson.Decode.read (.number "8") : Except String Nat) = .ok 8 :=
  decodeNat_number_ofList ['8']

#check (900012 : Nat)
private theorem nat009_literal_decoded :
    (SourceJson.Decode.read (.number "9") : Except String Nat) = .ok 9 :=
  decodeNat_number_ofList ['9']

#check (900013 : Nat)
private theorem nat010_literal_decoded :
    (SourceJson.Decode.read (.number "10") : Except String Nat) = .ok 10 :=
  decodeNat_number_ofList ['1', '0']

#check (900014 : Nat)
private theorem nat011_literal_decoded :
    (SourceJson.Decode.read (.number "11") : Except String Nat) = .ok 11 :=
  decodeNat_number_ofList ['1', '1']

#check (900015 : Nat)
private theorem nat012_literal_decoded :
    (SourceJson.Decode.read (.number "12") : Except String Nat) = .ok 12 :=
  decodeNat_number_ofList ['1', '2']

#check (900016 : Nat)
private theorem nat013_literal_decoded :
    (SourceJson.Decode.read (.number "13") : Except String Nat) = .ok 13 :=
  decodeNat_number_ofList ['1', '3']

#check (900017 : Nat)
private theorem nat014_literal_decoded :
    (SourceJson.Decode.read (.number "14") : Except String Nat) = .ok 14 :=
  decodeNat_number_ofList ['1', '4']

#check (900018 : Nat)
private theorem nat015_literal_decoded :
    (SourceJson.Decode.read (.number "15") : Except String Nat) = .ok 15 :=
  decodeNat_number_ofList ['1', '5']

#check (900019 : Nat)
private theorem nat016_literal_decoded :
    (SourceJson.Decode.read (.number "16") : Except String Nat) = .ok 16 :=
  decodeNat_number_ofList ['1', '6']

#check (900020 : Nat)
private theorem nat017_literal_decoded :
    (SourceJson.Decode.read (.number "17") : Except String Nat) = .ok 17 :=
  decodeNat_number_ofList ['1', '7']

#check (900021 : Nat)
private theorem nat018_literal_decoded :
    (SourceJson.Decode.read (.number "18") : Except String Nat) = .ok 18 :=
  decodeNat_number_ofList ['1', '8']

#check (900022 : Nat)
private theorem nat019_literal_decoded :
    (SourceJson.Decode.read (.number "19") : Except String Nat) = .ok 19 :=
  decodeNat_number_ofList ['1', '9']

#check (900023 : Nat)
private theorem nat020_literal_decoded :
    (SourceJson.Decode.read (.number "20") : Except String Nat) = .ok 20 :=
  decodeNat_number_ofList ['2', '0']

#check (900024 : Nat)
private theorem nat021_literal_decoded :
    (SourceJson.Decode.read (.number "21") : Except String Nat) = .ok 21 :=
  decodeNat_number_ofList ['2', '1']

#check (900025 : Nat)
private theorem nat022_literal_decoded :
    (SourceJson.Decode.read (.number "22") : Except String Nat) = .ok 22 :=
  decodeNat_number_ofList ['2', '2']

#check (900026 : Nat)
private theorem nat023_literal_decoded :
    (SourceJson.Decode.read (.number "23") : Except String Nat) = .ok 23 :=
  decodeNat_number_ofList ['2', '3']

#check (900027 : Nat)
private theorem nat024_literal_decoded :
    (SourceJson.Decode.read (.number "24") : Except String Nat) = .ok 24 :=
  decodeNat_number_ofList ['2', '4']

#check (900028 : Nat)
private theorem nat025_literal_decoded :
    (SourceJson.Decode.read (.number "25") : Except String Nat) = .ok 25 :=
  decodeNat_number_ofList ['2', '5']

#check (900029 : Nat)
private theorem nat026_literal_decoded :
    (SourceJson.Decode.read (.number "26") : Except String Nat) = .ok 26 :=
  decodeNat_number_ofList ['2', '6']

#check (900030 : Nat)
private theorem nat027_literal_decoded :
    (SourceJson.Decode.read (.number "27") : Except String Nat) = .ok 27 :=
  decodeNat_number_ofList ['2', '7']

#check (900031 : Nat)
private theorem nat028_literal_decoded :
    (SourceJson.Decode.read (.number "28") : Except String Nat) = .ok 28 :=
  decodeNat_number_ofList ['2', '8']

#check (900032 : Nat)
private theorem nat029_literal_decoded :
    (SourceJson.Decode.read (.number "29") : Except String Nat) = .ok 29 :=
  decodeNat_number_ofList ['2', '9']

#check (900033 : Nat)
private theorem nat030_literal_decoded :
    (SourceJson.Decode.read (.number "30") : Except String Nat) = .ok 30 :=
  decodeNat_number_ofList ['3', '0']

#check (900034 : Nat)
private theorem nat031_literal_decoded :
    (SourceJson.Decode.read (.number "31") : Except String Nat) = .ok 31 :=
  decodeNat_number_ofList ['3', '1']

#check (900035 : Nat)
private theorem nat032_literal_decoded :
    (SourceJson.Decode.read (.number "32") : Except String Nat) = .ok 32 :=
  decodeNat_number_ofList ['3', '2']

#check (900036 : Nat)
private theorem nat033_literal_decoded :
    (SourceJson.Decode.read (.number "33") : Except String Nat) = .ok 33 :=
  decodeNat_number_ofList ['3', '3']

#check (900037 : Nat)
private theorem nat034_literal_decoded :
    (SourceJson.Decode.read (.number "34") : Except String Nat) = .ok 34 :=
  decodeNat_number_ofList ['3', '4']

#check (900038 : Nat)
private theorem nat035_literal_decoded :
    (SourceJson.Decode.read (.number "35") : Except String Nat) = .ok 35 :=
  decodeNat_number_ofList ['3', '5']

#check (900039 : Nat)
private theorem nat036_literal_decoded :
    (SourceJson.Decode.read (.number "36") : Except String Nat) = .ok 36 :=
  decodeNat_number_ofList ['3', '6']

#check (900040 : Nat)
private theorem nat037_literal_decoded :
    (SourceJson.Decode.read (.number "37") : Except String Nat) = .ok 37 :=
  decodeNat_number_ofList ['3', '7']

#check (900041 : Nat)
private theorem nat038_literal_decoded :
    (SourceJson.Decode.read (.number "38") : Except String Nat) = .ok 38 :=
  decodeNat_number_ofList ['3', '8']

#check (900042 : Nat)
private theorem nat039_literal_decoded :
    (SourceJson.Decode.read (.number "39") : Except String Nat) = .ok 39 :=
  decodeNat_number_ofList ['3', '9']

#check (900043 : Nat)
private theorem nat040_literal_decoded :
    (SourceJson.Decode.read (.number "40") : Except String Nat) = .ok 40 :=
  decodeNat_number_ofList ['4', '0']

#check (900044 : Nat)
private theorem nat041_literal_decoded :
    (SourceJson.Decode.read (.number "41") : Except String Nat) = .ok 41 :=
  decodeNat_number_ofList ['4', '1']

#check (900045 : Nat)
private theorem nat042_literal_decoded :
    (SourceJson.Decode.read (.number "42") : Except String Nat) = .ok 42 :=
  decodeNat_number_ofList ['4', '2']

#check (900046 : Nat)
private theorem nat043_literal_decoded :
    (SourceJson.Decode.read (.number "43") : Except String Nat) = .ok 43 :=
  decodeNat_number_ofList ['4', '3']

#check (900047 : Nat)
private theorem nat044_literal_decoded :
    (SourceJson.Decode.read (.number "44") : Except String Nat) = .ok 44 :=
  decodeNat_number_ofList ['4', '4']

#check (900048 : Nat)
private theorem nat045_literal_decoded :
    (SourceJson.Decode.read (.number "45") : Except String Nat) = .ok 45 :=
  decodeNat_number_ofList ['4', '5']

#check (900049 : Nat)
private theorem nat046_literal_decoded :
    (SourceJson.Decode.read (.number "46") : Except String Nat) = .ok 46 :=
  decodeNat_number_ofList ['4', '6']

#check (900050 : Nat)
private theorem nat047_literal_decoded :
    (SourceJson.Decode.read (.number "47") : Except String Nat) = .ok 47 :=
  decodeNat_number_ofList ['4', '7']

#check (900051 : Nat)
private theorem nat048_literal_decoded :
    (SourceJson.Decode.read (.number "48") : Except String Nat) = .ok 48 :=
  decodeNat_number_ofList ['4', '8']

#check (900052 : Nat)
private theorem nat049_literal_decoded :
    (SourceJson.Decode.read (.number "49") : Except String Nat) = .ok 49 :=
  decodeNat_number_ofList ['4', '9']

#check (900053 : Nat)
private theorem nat050_literal_decoded :
    (SourceJson.Decode.read (.number "50") : Except String Nat) = .ok 50 :=
  decodeNat_number_ofList ['5', '0']

#check (900054 : Nat)
private theorem nat051_literal_decoded :
    (SourceJson.Decode.read (.number "51") : Except String Nat) = .ok 51 :=
  decodeNat_number_ofList ['5', '1']

#check (900055 : Nat)
private theorem nat052_literal_decoded :
    (SourceJson.Decode.read (.number "52") : Except String Nat) = .ok 52 :=
  decodeNat_number_ofList ['5', '2']

#check (900056 : Nat)
private theorem nat053_literal_decoded :
    (SourceJson.Decode.read (.number "53") : Except String Nat) = .ok 53 :=
  decodeNat_number_ofList ['5', '3']

#check (900057 : Nat)
private theorem nat054_literal_decoded :
    (SourceJson.Decode.read (.number "54") : Except String Nat) = .ok 54 :=
  decodeNat_number_ofList ['5', '4']

#check (900058 : Nat)
private theorem nat055_literal_decoded :
    (SourceJson.Decode.read (.number "55") : Except String Nat) = .ok 55 :=
  decodeNat_number_ofList ['5', '5']

#check (900059 : Nat)
private theorem nat056_literal_decoded :
    (SourceJson.Decode.read (.number "56") : Except String Nat) = .ok 56 :=
  decodeNat_number_ofList ['5', '6']

#check (900060 : Nat)
private theorem nat057_literal_decoded :
    (SourceJson.Decode.read (.number "57") : Except String Nat) = .ok 57 :=
  decodeNat_number_ofList ['5', '7']

#check (900061 : Nat)
private theorem nat058_literal_decoded :
    (SourceJson.Decode.read (.number "58") : Except String Nat) = .ok 58 :=
  decodeNat_number_ofList ['5', '8']

#check (900062 : Nat)
private theorem nat059_literal_decoded :
    (SourceJson.Decode.read (.number "59") : Except String Nat) = .ok 59 :=
  decodeNat_number_ofList ['5', '9']

#check (900063 : Nat)
private theorem nat060_literal_decoded :
    (SourceJson.Decode.read (.number "60") : Except String Nat) = .ok 60 :=
  decodeNat_number_ofList ['6', '0']

#check (900064 : Nat)
private theorem nat061_literal_decoded :
    (SourceJson.Decode.read (.number "61") : Except String Nat) = .ok 61 :=
  decodeNat_number_ofList ['6', '1']

#check (900065 : Nat)
private theorem nat062_literal_decoded :
    (SourceJson.Decode.read (.number "62") : Except String Nat) = .ok 62 :=
  decodeNat_number_ofList ['6', '2']

#check (900066 : Nat)
private theorem nat063_literal_decoded :
    (SourceJson.Decode.read (.number "63") : Except String Nat) = .ok 63 :=
  decodeNat_number_ofList ['6', '3']

#check (900067 : Nat)
private theorem nat065_literal_decoded :
    (SourceJson.Decode.read (.number "65") : Except String Nat) = .ok 65 :=
  decodeNat_number_ofList ['6', '5']

#check (900068 : Nat)
private theorem nat090_literal_decoded :
    (SourceJson.Decode.read (.number "90") : Except String Nat) = .ok 90 :=
  decodeNat_number_ofList ['9', '0']

attribute [local simp] nat000_literal_decoded nat001_literal_decoded nat002_literal_decoded nat003_literal_decoded nat004_literal_decoded nat005_literal_decoded nat006_literal_decoded nat007_literal_decoded nat008_literal_decoded nat009_literal_decoded nat010_literal_decoded nat011_literal_decoded nat012_literal_decoded nat013_literal_decoded nat014_literal_decoded nat015_literal_decoded nat016_literal_decoded nat017_literal_decoded nat018_literal_decoded nat019_literal_decoded nat020_literal_decoded nat021_literal_decoded nat022_literal_decoded nat023_literal_decoded nat024_literal_decoded nat025_literal_decoded nat026_literal_decoded nat027_literal_decoded nat028_literal_decoded nat029_literal_decoded nat030_literal_decoded nat031_literal_decoded nat032_literal_decoded nat033_literal_decoded nat034_literal_decoded nat035_literal_decoded nat036_literal_decoded nat037_literal_decoded nat038_literal_decoded nat039_literal_decoded nat040_literal_decoded nat041_literal_decoded nat042_literal_decoded nat043_literal_decoded nat044_literal_decoded nat045_literal_decoded nat046_literal_decoded nat047_literal_decoded nat048_literal_decoded nat049_literal_decoded nat050_literal_decoded nat051_literal_decoded nat052_literal_decoded nat053_literal_decoded nat054_literal_decoded nat055_literal_decoded nat056_literal_decoded nat057_literal_decoded nat058_literal_decoded nat059_literal_decoded nat060_literal_decoded nat061_literal_decoded nat062_literal_decoded nat063_literal_decoded nat065_literal_decoded nat090_literal_decoded

#check (900069 : Nat)
private theorem rational000_literal_decoded :
    parseRational "1" = .ok rational000 :=
  rational000_decoded

#check (900070 : Nat)
private theorem rational001_literal_decoded :
    parseRational "8/7" = .ok rational001 :=
  rational001_decoded

#check (900071 : Nat)
private theorem rational002_literal_decoded :
    parseRational "16/7" = .ok rational002 :=
  rational002_decoded

#check (900072 : Nat)
private theorem rational003_literal_decoded :
    parseRational "1/7" = .ok rational003 :=
  rational003_decoded

#check (900073 : Nat)
private theorem rational004_literal_decoded :
    parseRational "40/7" = .ok rational004 :=
  rational004_decoded

#check (900074 : Nat)
private theorem rational005_literal_decoded :
    parseRational "20/7" = .ok rational005 :=
  rational005_decoded

#check (900075 : Nat)
private theorem rational006_literal_decoded :
    parseRational "6/7" = .ok rational006 :=
  rational006_decoded

#check (900076 : Nat)
private theorem rational007_literal_decoded :
    parseRational "34/21" = .ok rational007 :=
  rational007_decoded

#check (900077 : Nat)
private theorem rational008_literal_decoded :
    parseRational "4" = .ok rational008 :=
  rational008_decoded

#check (900078 : Nat)
private theorem rational009_literal_decoded :
    parseRational "5859427/36000000" = .ok rational009 :=
  rational009_decoded

#check (900079 : Nat)
private theorem rational010_literal_decoded :
    parseRational "1171879/12000000" = .ok rational010 :=
  rational010_decoded

#check (900080 : Nat)
private theorem rational011_literal_decoded :
    parseRational "1171847/36000000" = .ok rational011 :=
  rational011_decoded

#check (900081 : Nat)
private theorem rational012_literal_decoded :
    parseRational "1171823/36000000" = .ok rational012 :=
  rational012_decoded

#check (900082 : Nat)
private theorem rational013_literal_decoded :
    parseRational "131673/800000" = .ok rational013 :=
  rational013_decoded

#check (900083 : Nat)
private theorem rational014_literal_decoded :
    parseRational "78463/800000" = .ok rational014 :=
  rational014_decoded

#check (900084 : Nat)
private theorem rational015_literal_decoded :
    parseRational "25253/800000" = .ok rational015 :=
  rational015_decoded

#check (900085 : Nat)
private theorem rational016_literal_decoded :
    parseRational "112753/4000000" = .ok rational016 :=
  rational016_decoded

#check (900086 : Nat)
private theorem rational017_literal_decoded :
    parseRational "20453229/124000000" = .ok rational017 :=
  rational017_decoded

#check (900087 : Nat)
private theorem rational018_literal_decoded :
    parseRational "12171899/124000000" = .ok rational018 :=
  rational018_decoded

#check (900088 : Nat)
private theorem rational019_literal_decoded :
    parseRational "3890569/124000000" = .ok rational019 :=
  rational019_decoded

#check (900089 : Nat)
private theorem rational020_literal_decoded :
    parseRational "7/256" = .ok rational020 :=
  rational020_decoded

#check (900090 : Nat)
private theorem rational021_literal_decoded :
    parseRational "13921919/84000000" = .ok rational021 :=
  rational021_decoded

#check (900091 : Nat)
private theorem rational022_literal_decoded :
    parseRational "828129/28000000" = .ok rational022 :=
  rational022_decoded

#check (900092 : Nat)
private theorem rational023_literal_decoded :
    parseRational "2484331/84000000" = .ok rational023 :=
  rational023_decoded

#check (900093 : Nat)
private theorem rational024_literal_decoded :
    parseRational "2984307/28000000" = .ok rational024 :=
  rational024_decoded

#check (900094 : Nat)
private theorem rational025_literal_decoded :
    parseRational "1490677/16800000" = .ok rational025 :=
  rational025_decoded

#check (900095 : Nat)
private theorem rational026_literal_decoded :
    parseRational "13921927/84000000" = .ok rational026 :=
  rational026_decoded

#check (900096 : Nat)
private theorem rational027_literal_decoded :
    parseRational "2484379/84000000" = .ok rational027 :=
  rational027_decoded

#check (900097 : Nat)
private theorem rational028_literal_decoded :
    parseRational "2484323/84000000" = .ok rational028 :=
  rational028_decoded

#check (900098 : Nat)
private theorem rational029_literal_decoded :
    parseRational "596863/5600000" = .ok rational029 :=
  rational029_decoded

#check (900099 : Nat)
private theorem rational030_literal_decoded :
    parseRational "7453361/84000000" = .ok rational030 :=
  rational030_decoded

#check (900100 : Nat)
private theorem rational031_literal_decoded :
    parseRational "44703177/268000000" = .ok rational031 :=
  rational031_decoded

#check (900101 : Nat)
private theorem rational032_literal_decoded :
    parseRational "26421887/268000000" = .ok rational032 :=
  rational032_decoded

#check (900102 : Nat)
private theorem rational033_literal_decoded :
    parseRational "8140597/268000000" = .ok rational033 :=
  rational033_decoded

#check (900103 : Nat)
private theorem rational034_literal_decoded :
    parseRational "7640573/268000000" = .ok rational034 :=
  rational034_decoded

#check (900104 : Nat)
private theorem rational035_literal_decoded :
    parseRational "40796927/244000000" = .ok rational035 :=
  rational035_decoded

#check (900105 : Nat)
private theorem rational036_literal_decoded :
    parseRational "24078137/244000000" = .ok rational036 :=
  rational036_decoded

#check (900106 : Nat)
private theorem rational037_literal_decoded :
    parseRational "7359347/244000000" = .ok rational037 :=
  rational037_decoded

#check (900107 : Nat)
private theorem rational038_literal_decoded :
    parseRational "6859323/244000000" = .ok rational038 :=
  rational038_decoded

#check (900108 : Nat)
private theorem rational039_literal_decoded :
    parseRational "2015623/12000000" = .ok rational039 :=
  rational039_decoded

#check (900109 : Nat)
private theorem rational040_literal_decoded :
    parseRational "328127/12000000" = .ok rational040 :=
  rational040_decoded

#check (900110 : Nat)
private theorem rational041_literal_decoded :
    parseRational "13183/375000" = .ok rational041 :=
  rational041_decoded

#check (900111 : Nat)
private theorem rational042_literal_decoded :
    parseRational "65627/2400000" = .ok rational042 :=
  rational042_decoded

#check (900112 : Nat)
private theorem rational043_literal_decoded :
    parseRational "171859/4000000" = .ok rational043 :=
  rational043_decoded

#check (900113 : Nat)
private theorem rational044_literal_decoded :
    parseRational "43/256" = .ok rational044 :=
  rational044_decoded

#check (900114 : Nat)
private theorem rational045_literal_decoded :
    parseRational "140619/4000000" = .ok rational045 :=
  rational045_decoded

#check (900115 : Nat)
private theorem rational046_literal_decoded :
    parseRational "328133/12000000" = .ok rational046 :=
  rational046_decoded

#check (900116 : Nat)
private theorem rational047_literal_decoded :
    parseRational "515581/12000000" = .ok rational047 :=
  rational047_decoded

#check (900117 : Nat)
private theorem rational048_literal_decoded :
    parseRational "18328073/108000000" = .ok rational048 :=
  rational048_decoded

#check (900118 : Nat)
private theorem rational049_literal_decoded :
    parseRational "2765677/108000000" = .ok rational049 :=
  rational049_decoded

#check (900119 : Nat)
private theorem rational050_literal_decoded :
    parseRational "6613361/84000000" = .ok rational050 :=
  rational050_decoded

#check (900120 : Nat)
private theorem rational051_literal_decoded :
    parseRational "522581/24000000" = .ok rational051 :=
  rational051_decoded

#check (900121 : Nat)
private theorem rational052_literal_decoded :
    parseRational "2484491/42000000" = .ok rational052 :=
  rational052_decoded

#check (900122 : Nat)
private theorem rational053_literal_decoded :
    parseRational "0" = .ok rational053 :=
  rational053_decoded

#check (900123 : Nat)
private theorem rational054_literal_decoded :
    parseRational "109383/2000000" = .ok rational054 :=
  rational054_decoded

#check (900124 : Nat)
private theorem rational055_literal_decoded :
    parseRational "796879/9000000" = .ok rational055 :=
  rational055_decoded

#check (900125 : Nat)
private theorem rational056_literal_decoded :
    parseRational "3984307/122000000" = .ok rational056 :=
  rational056_decoded

#check (900126 : Nat)
private theorem rational057_literal_decoded :
    parseRational "281263/3000000" = .ok rational057 :=
  rational057_decoded

#check (900127 : Nat)
private theorem rational058_literal_decoded :
    parseRational "2015813/54000000" = .ok rational058 :=
  rational058_decoded

#check (900128 : Nat)
private theorem rational059_literal_decoded :
    parseRational "1/750000" = .ok rational059 :=
  rational059_decoded

#check (900129 : Nat)
private theorem rational060_literal_decoded :
    parseRational "7453137/224000000" = .ok rational060 :=
  rational060_decoded

#check (900130 : Nat)
private theorem rational061_literal_decoded :
    parseRational "27890621/108000000" = .ok rational061 :=
  rational061_decoded

#check (900131 : Nat)
private theorem rational062_literal_decoded :
    parseRational "328129/1500000" = .ok rational062 :=
  rational062_decoded

#check (900132 : Nat)
private theorem rational063_literal_decoded :
    parseRational "5296967/28000000" = .ok rational063 :=
  rational063_decoded

#check (900133 : Nat)
private theorem rational064_literal_decoded :
    parseRational "32796543/244000000" = .ok rational064 :=
  rational064_decoded

#check (900134 : Nat)
private theorem rational065_literal_decoded :
    parseRational "1296861/12200000" = .ok rational065 :=
  rational065_decoded

#check (900135 : Nat)
private theorem rational066_literal_decoded :
    parseRational "890659/6000000" = .ok rational066 :=
  rational066_decoded

#check (900136 : Nat)
private theorem rational067_literal_decoded :
    parseRational "1453193/12000000" = .ok rational067 :=
  rational067_decoded

#check (900137 : Nat)
private theorem rational068_literal_decoded :
    parseRational "1546909/12000000" = .ok rational068 :=
  rational068_decoded

#check (900138 : Nat)
private theorem rational069_literal_decoded :
    parseRational "38087/375000" = .ok rational069 :=
  rational069_decoded

#check (900139 : Nat)
private theorem rational070_literal_decoded :
    parseRational "2765677/27000000" = .ok rational070 :=
  rational070_decoded

#check (900140 : Nat)
private theorem rational071_literal_decoded :
    parseRational "2765677/36000000" = .ok rational071 :=
  rational071_decoded

#check (900141 : Nat)
private theorem rational072_literal_decoded :
    parseRational "7547167/108000000" = .ok rational072 :=
  rational072_decoded

#check (900142 : Nat)
private theorem rational073_literal_decoded :
    parseRational "159383/3600000" = .ok rational073 :=
  rational073_decoded

#check (900143 : Nat)
private theorem rational074_literal_decoded :
    parseRational "796927/18000000" = .ok rational074 :=
  rational074_decoded

#check (900144 : Nat)
private theorem rational075_literal_decoded :
    parseRational "5359251/488000000" = .ok rational075 :=
  rational075_decoded

#check (900145 : Nat)
private theorem rational076_literal_decoded :
    parseRational "2484379/56000000" = .ok rational076 :=
  rational076_decoded

#check (900146 : Nat)
private theorem rational077_literal_decoded :
    parseRational "234379/2400000" = .ok rational077 :=
  rational077_decoded

#check (900147 : Nat)
private theorem rational078_literal_decoded :
    parseRational "22078041/488000000" = .ok rational078 :=
  rational078_decoded

#check (900148 : Nat)
private theorem rational079_literal_decoded :
    parseRational "2484491/28000000" = .ok rational079 :=
  rational079_decoded

#check (900149 : Nat)
private theorem rational080_literal_decoded :
    parseRational "5859427/24000000" = .ok rational080 :=
  rational080_decoded

#check (900150 : Nat)
private theorem rational081_literal_decoded :
    parseRational "365629/4800000" = .ok rational081 :=
  rational081_decoded

#check (900151 : Nat)
private theorem rational082_literal_decoded :
    parseRational "1171879/8000000" = .ok rational082 :=
  rational082_decoded

#check (900152 : Nat)
private theorem rational083_literal_decoded :
    parseRational "7453361/56000000" = .ok rational083 :=
  rational083_decoded

#check (900153 : Nat)
private theorem rational084_literal_decoded :
    parseRational "1171879/4000000" = .ok rational084 :=
  rational084_decoded

#check (900154 : Nat)
private theorem rational085_literal_decoded :
    parseRational "38796831/488000000" = .ok rational085 :=
  rational085_decoded

#check (900155 : Nat)
private theorem rational086_literal_decoded :
    parseRational "328133/8000000" = .ok rational086 :=
  rational086_decoded

#check (900156 : Nat)
private theorem rational087_literal_decoded :
    parseRational "125001/2000000" = .ok rational087 :=
  rational087_decoded

#check (900157 : Nat)
private theorem rational088_literal_decoded :
    parseRational "328133/24000000" = .ok rational088 :=
  rational088_decoded

#check (900158 : Nat)
private theorem rational089_literal_decoded :
    parseRational "2671883/14000000" = .ok rational089 :=
  rational089_decoded

#check (900159 : Nat)
private theorem rational090_literal_decoded :
    parseRational "496887/2800000" = .ok rational090 :=
  rational090_decoded

#check (900160 : Nat)
private theorem rational091_literal_decoded :
    parseRational "2484379/28000000" = .ok rational091 :=
  rational091_decoded

#check (900161 : Nat)
private theorem rational092_literal_decoded :
    parseRational "3778137/11200000" = .ok rational092 :=
  rational092_decoded

#check (900162 : Nat)
private theorem rational093_literal_decoded :
    parseRational "7859371/122000000" = .ok rational093 :=
  rational093_decoded

#check (900163 : Nat)
private theorem rational094_literal_decoded :
    parseRational "2484379/168000000" = .ok rational094 :=
  rational094_decoded

#check (900164 : Nat)
private theorem rational095_literal_decoded :
    parseRational "375003/2000000" = .ok rational095 :=
  rational095_decoded

#check (900165 : Nat)
private theorem rational096_literal_decoded :
    parseRational "7359347/488000000" = .ok rational096 :=
  rational096_decoded

#check (900166 : Nat)
private theorem rational097_literal_decoded :
    parseRational "328133/4000000" = .ok rational097 :=
  rational097_decoded

#check (900167 : Nat)
private theorem rational098_literal_decoded :
    parseRational "2671891/8000000" = .ok rational098 :=
  rational098_decoded

#check (900168 : Nat)
private theorem rational099_literal_decoded :
    parseRational "1171879/24000000" = .ok rational099 :=
  rational099_decoded

#check (900169 : Nat)
private theorem rational100_literal_decoded :
    parseRational "13171911/56000000" = .ok rational100 :=
  rational100_decoded

#check (900170 : Nat)
private theorem rational101_literal_decoded :
    parseRational "12422119/56000000" = .ok rational101 :=
  rational101_decoded

#check (900171 : Nat)
private theorem rational102_literal_decoded :
    parseRational "7453137/56000000" = .ok rational102 :=
  rational102_decoded

#check (900172 : Nat)
private theorem rational103_literal_decoded :
    parseRational "2671883/7000000" = .ok rational103 :=
  rational103_decoded

#check (900173 : Nat)
private theorem rational104_literal_decoded :
    parseRational "3877356808577946891017408321911/1683103229165039062500000000000000000000000000000000000000" = .ok rational104 :=
  rational104_decoded

#check (900174 : Nat)
private theorem rational105_literal_decoded :
    parseRational "23431/68625000" = .ok rational105 :=
  rational105_decoded

#check (900175 : Nat)
private theorem rational106_literal_decoded :
    parseRational "2484323/28000000" = .ok rational106 :=
  rational106_decoded

#check (900176 : Nat)
private theorem rational107_literal_decoded :
    parseRational "697329587/8540000000" = .ok rational107 :=
  rational107_decoded

#check (900177 : Nat)
private theorem rational108_literal_decoded :
    parseRational "702578131/8540000000" = .ok rational108 :=
  rational108_decoded

#check (900178 : Nat)
private theorem rational109_literal_decoded :
    parseRational "1187984619349/7147980000000" = .ok rational109 :=
  rational109_decoded

#check (900179 : Nat)
private theorem rational110_literal_decoded :
    parseRational "26157488321/264740000000" = .ok rational110 :=
  rational110_decoded

#check (900180 : Nat)
private theorem rational111_literal_decoded :
    parseRational "77054608291/794220000000" = .ok rational111 :=
  rational111_decoded

#check (900181 : Nat)
private theorem rational112_literal_decoded :
    parseRational "25941107803/794220000000" = .ok rational112 :=
  rational112_decoded

#check (900182 : Nat)
private theorem rational113_literal_decoded :
    parseRational "1646698881/52948000000" = .ok rational113 :=
  rational113_decoded

#check (900183 : Nat)
private theorem rational114_literal_decoded :
    parseRational "24080170921/794220000000" = .ok rational114 :=
  rational114_decoded

#check (900184 : Nat)
private theorem rational115_literal_decoded :
    parseRational "8026705991/264740000000" = .ok rational115 :=
  rational115_decoded

#check (900185 : Nat)
private theorem rational116_literal_decoded :
    parseRational "6643359239/230580000000" = .ok rational116 :=
  rational116_decoded

#check (900186 : Nat)
private theorem rational117_literal_decoded :
    parseRational "124863766667208554582624247958233574320656875520000/29050376491015886855935352360499250017954162649121346571152086980341" = .ok rational117 :=
  rational117_decoded

#check (900187 : Nat)
private theorem rational118_literal_decoded :
    parseRational "170856536501268546898018884558755832341260657048841176878017694883276390400000000000000/15636222278598571827167075762086281178030311938082502962381975697923813873130952526880395302809043674143" = .ok rational118 :=
  rational118_decoded

#check (900188 : Nat)
private theorem rational119_literal_decoded :
    parseRational "8731528037563104741693608542750763/748045879628906250000000000000000000000000000000000000000" = .ok rational119 :=
  rational119_decoded

#check (900189 : Nat)
private theorem rational120_literal_decoded :
    parseRational "197983091/2401875000" = .ok rational120 :=
  rational120_decoded

#check (900190 : Nat)
private theorem rational121_literal_decoded :
    parseRational "49864811/600468750" = .ok rational121 :=
  rational121_decoded

#check (900191 : Nat)
private theorem rational122_literal_decoded :
    parseRational "297323065717/1786995000000" = .ok rational122 :=
  rational122_decoded

#check (900192 : Nat)
private theorem rational123_literal_decoded :
    parseRational "19626498571/198555000000" = .ok rational123 :=
  rational123_decoded

#check (900193 : Nat)
private theorem rational124_literal_decoded :
    parseRational "19272034403/198555000000" = .ok rational124 :=
  rational124_decoded

#check (900194 : Nat)
private theorem rational125_literal_decoded :
    parseRational "38794309081/1191330000000" = .ok rational125 :=
  rational125_decoded

#check (900195 : Nat)
private theorem rational126_literal_decoded :
    parseRational "36933372199/1191330000000" = .ok rational126 :=
  rational126_decoded

#check (900196 : Nat)
private theorem rational127_literal_decoded :
    parseRational "18001451879/595665000000" = .ok rational127 :=
  rational127_decoded

#check (900197 : Nat)
private theorem rational128_literal_decoded :
    parseRational "17800196531/595665000000" = .ok rational128 :=
  rational128_decoded

#check (900198 : Nat)
private theorem rational129_literal_decoded :
    parseRational "1635692819/57645000000" = .ok rational129 :=
  rational129_decoded

#check (900199 : Nat)
private theorem rational130_literal_decoded :
    parseRational "4135061791998299140839979201415609389423913861120000/189871741771345665725067662486923202731726553262231023340863313597" = .ok rational130 :=
  rational130_decoded

#check (900200 : Nat)
private theorem rational131_literal_decoded :
    parseRational "2765905418842430855116208194378778659095847608696980587005814207242606750000000000000/49044849961932387982031200242593759963265477930594799729072512564688957974878476897021802079629957" = .ok rational131 :=
  rational131_decoded

#check (900201 : Nat)
private theorem rational132_literal_decoded :
    parseRational "1676587499621718696717531187243/868698440859375000000000000000000000000000000000000000000" = .ok rational132 :=
  rational132_decoded

#check (900202 : Nat)
private theorem rational133_literal_decoded :
    parseRational "2484331/28000000" = .ok rational133 :=
  rational133_decoded

#check (900203 : Nat)
private theorem rational134_literal_decoded :
    parseRational "3564127/42890625" = .ok rational134 :=
  rational134_decoded

#check (900204 : Nat)
private theorem rational135_literal_decoded :
    parseRational "5744779/68625000" = .ok rational135 :=
  rational135_decoded

#check (900205 : Nat)
private theorem rational136_literal_decoded :
    parseRational "1370804371/8235000000" = .ok rational136 :=
  rational136_decoded

#check (900206 : Nat)
private theorem rational137_literal_decoded :
    parseRational "105465019/1067500000" = .ok rational137 :=
  rational137_decoded

#check (900207 : Nat)
private theorem rational138_literal_decoded :
    parseRational "310677893/3202500000" = .ok rational138 :=
  rational138_decoded

#check (900208 : Nat)
private theorem rational139_literal_decoded :
    parseRational "177787681/5490000000" = .ok rational139 :=
  rational139_decoded

#check (900209 : Nat)
private theorem rational140_literal_decoded :
    parseRational "33842387/1098000000" = .ok rational140 :=
  rational140_decoded

#check (900210 : Nat)
private theorem rational141_literal_decoded :
    parseRational "82462031/2745000000" = .ok rational141 :=
  rational141_decoded

#check (900211 : Nat)
private theorem rational142_literal_decoded :
    parseRational "20383601/686250000" = .ok rational142 :=
  rational142_decoded

#check (900212 : Nat)
private theorem rational143_literal_decoded :
    parseRational "235508141/8235000000" = .ok rational143 :=
  rational143_decoded

#check (900213 : Nat)
private theorem rational144_literal_decoded :
    parseRational "198498844669650037863861096808446571923374080000/55124409083427071696785593774607075408005077322105376216414683147" = .ok rational144 :=
  rational144_decoded

#check (900214 : Nat)
private theorem rational145_literal_decoded :
    parseRational "142972342180370614789275477202609572423031510840971796875000000/15332829895113936999672325549450127341808669934615713665327834215998925089835479" = .ok rational145 :=
  rational145_decoded

#check (900215 : Nat)
private theorem rational146_literal_decoded :
    parseRational "6706135335753791898555919098613/3474793763437500000000000000000000000000000000000000000000" = .ok rational146 :=
  rational146_decoded

#check (900216 : Nat)
private theorem rational147_literal_decoded :
    parseRational "319345889/3843000000" = .ok rational147 :=
  rational147_decoded

#check (900217 : Nat)
private theorem rational148_literal_decoded :
    parseRational "1608538669/19215000000" = .ok rational148 :=
  rational148_decoded

#check (900218 : Nat)
private theorem rational149_literal_decoded :
    parseRational "299863439/1801406250" = .ok rational149 :=
  rational149_decoded

#check (900219 : Nat)
private theorem rational150_literal_decoded :
    parseRational "127701419/1281000000" = .ok rational150 :=
  rational150_decoded

#check (900220 : Nat)
private theorem rational151_literal_decoded :
    parseRational "41042587/427000000" = .ok rational151 :=
  rational151_decoded

#check (900221 : Nat)
private theorem rational152_literal_decoded :
    parseRational "1244514133/38430000000" = .ok rational152 :=
  rational152_decoded

#check (900222 : Nat)
private theorem rational153_literal_decoded :
    parseRational "1184483911/38430000000" = .ok rational153 :=
  rational153_decoded

#check (900223 : Nat)
private theorem rational154_literal_decoded :
    parseRational "721543/24018750" = .ok rational154 :=
  rational154_decoded

#check (900224 : Nat)
private theorem rational155_literal_decoded :
    parseRational "57073973/1921500000" = .ok rational155 :=
  rational155_decoded

#check (900225 : Nat)
private theorem rational156_literal_decoded :
    parseRational "51517423/1801406250" = .ok rational156 :=
  rational156_decoded

#check (900226 : Nat)
private theorem rational157_literal_decoded :
    parseRational "198492490944520839898413702509329746566840320000/55124409083427071696785593774607075408005077322105376216414683147" = .ok rational157 :=
  rational157_decoded

#check (900227 : Nat)
private theorem rational158_literal_decoded :
    parseRational "158040406371987098477421580659074322946408224715006932199218750/16945094216077934339074566792953210360203027709312774599859245684513715287766633" = .ok rational158 :=
  rational158_decoded

#check (900228 : Nat)
private theorem rational159_literal_decoded :
    parseRational "239508663003016316608501128193728907/44344987076250000000000000000000000000000000000000000000000" = .ok rational159 :=
  rational159_decoded

#check (900229 : Nat)
private theorem rational160_literal_decoded :
    parseRational "11996489/18391500000" = .ok rational160 :=
  rational160_decoded

#check (900230 : Nat)
private theorem rational161_literal_decoded :
    parseRational "1275217067019092339/15444339921045000000" = .ok rational161 :=
  rational161_decoded

#check (900231 : Nat)
private theorem rational162_literal_decoded :
    parseRational "1288827072989715737/15444339921045000000" = .ok rational162 :=
  rational162_decoded

#check (900232 : Nat)
private theorem rational163_literal_decoded :
    parseRational "3858344470220901667/23166509881567500000" = .ok rational163 :=
  rational163_decoded

#check (900233 : Nat)
private theorem rational164_literal_decoded :
    parseRational "509071823123562407/5148113307015000000" = .ok rational164 :=
  rational164_decoded

#check (900234 : Nat)
private theorem rational165_literal_decoded :
    parseRational "499881607366481401/5148113307015000000" = .ok rational165 :=
  rational165_decoded

#check (900235 : Nat)
private theorem rational166_literal_decoded :
    parseRational "1003081078232024987/30888679842090000000" = .ok rational166 :=
  rational166_decoded

#check (900236 : Nat)
private theorem rational167_literal_decoded :
    parseRational "954830901073357601/30888679842090000000" = .ok rational167 :=
  rational167_decoded

#check (900237 : Nat)
private theorem rational168_literal_decoded :
    parseRational "232676453123505977/7722169960522500000" = .ok rational168 :=
  rational168_decoded

#check (900238 : Nat)
private theorem rational169_literal_decoded :
    parseRational "227938980529739057/7722169960522500000" = .ok rational169 :=
  rational169_decoded

#check (900239 : Nat)
private theorem rational170_literal_decoded :
    parseRational "660496414069749629/23166509881567500000" = .ok rational170 :=
  rational170_decoded

#check (900240 : Nat)
private theorem rational171_literal_decoded :
    parseRational "7939705474349550933352053634926743532553666507571200000/412421348385656109977995872938019583925782145318878076874411863242029" = .ok rational171 :=
  rational171_decoded

#check (900241 : Nat)
private theorem rational172_literal_decoded :
    parseRational "254394461467128358111916852310624625745773228348526201463961358143309916787740186379631954325044078176354039880906367586181821415515785182163796637453125000000000/5063262225936620206299263177324066498946121721489178899901542315911142739494386052767094877536829127142240891008021837167821127073256659415233255545786171139344055624642246693" = .ok rational172 :=
  rational172_decoded

#check (900242 : Nat)
private theorem rational173_literal_decoded :
    parseRational "107291296494411925237230430803253/61065228105000000000000000000000000000000000000000000000000" = .ok rational173 :=
  rational173_decoded

#check (900243 : Nat)
private theorem rational174_literal_decoded :
    parseRational "93721/301500000" = .ok rational174 :=
  rational174_decoded

#check (900244 : Nat)
private theorem rational175_literal_decoded :
    parseRational "279336637/3376800000" = .ok rational175 :=
  rational175_decoded

#check (900245 : Nat)
private theorem rational176_literal_decoded :
    parseRational "7030651309/84420000000" = .ok rational176 :=
  rational176_decoded

#check (900246 : Nat)
private theorem rational177_literal_decoded :
    parseRational "42194221087/253260000000" = .ok rational177 :=
  rational177_decoded

#check (900247 : Nat)
private theorem rational178_literal_decoded :
    parseRational "231634153/2345000000" = .ok rational178 :=
  rational178_decoded

#check (900248 : Nat)
private theorem rational179_literal_decoded :
    parseRational "136468769/1407000000" = .ok rational179 :=
  rational179_decoded

#check (900249 : Nat)
private theorem rational180_literal_decoded :
    parseRational "1113824501/33768000000" = .ok rational180 :=
  rational180_decoded

#check (900250 : Nat)
private theorem rational181_literal_decoded :
    parseRational "5305383169/168840000000" = .ok rational181 :=
  rational181_decoded

#check (900251 : Nat)
private theorem rational182_literal_decoded :
    parseRational "2520824027/84420000000" = .ok rational182 :=
  rational182_decoded

#check (900252 : Nat)
private theorem rational183_literal_decoded :
    parseRational "2460782927/84420000000" = .ok rational183 :=
  rational183_decoded

#check (900253 : Nat)
private theorem rational184_literal_decoded :
    parseRational "1441294381/50652000000" = .ok rational184 :=
  rational184_decoded

#check (900254 : Nat)
private theorem rational185_literal_decoded :
    parseRational "16870241634095672141811345919572630894857420800000/5647387989637925742396092428273126791307824863377735694093414395767" = .ok rational185 :=
  rational185_decoded

#check (900255 : Nat)
private theorem rational186_literal_decoded :
    parseRational "1071031659611348334805862873057692133997702798967168670668707594240000000000/138393072659942256458040932179874132083356595398006901774290886347316419268190159269165538107" = .ok rational186 :=
  rational186_decoded

#check (900256 : Nat)
private theorem rational187_literal_decoded :
    parseRational "429151448881941873806430506820523/244260912420000000000000000000000000000000000000000000000000" = .ok rational187 :=
  rational187_decoded

#check (900257 : Nat)
private theorem rational188_literal_decoded :
    parseRational "3491710073/42210000000" = .ok rational188 :=
  rational188_decoded

#check (900258 : Nat)
private theorem rational189_literal_decoded :
    parseRational "703065553/8442000000" = .ok rational189 :=
  rational189_decoded

#check (900259 : Nat)
private theorem rational190_literal_decoded :
    parseRational "21097108433/126630000000" = .ok rational190 :=
  rational190_decoded

#check (900260 : Nat)
private theorem rational191_literal_decoded :
    parseRational "1140197309/33768000000" = .ok rational191 :=
  rational191_decoded

#check (900261 : Nat)
private theorem rational192_literal_decoded :
    parseRational "1034703263/33768000000" = .ok rational192 :=
  rational192_decoded

#check (900262 : Nat)
private theorem rational193_literal_decoded :
    parseRational "1260412717/42210000000" = .ok rational193 :=
  rational193_decoded

#check (900263 : Nat)
private theorem rational194_literal_decoded :
    parseRational "1230389353/42210000000" = .ok rational194 :=
  rational194_decoded

#check (900264 : Nat)
private theorem rational195_literal_decoded :
    parseRational "3603238063/126630000000" = .ok rational195 :=
  rational195_decoded

#check (900265 : Nat)
private theorem rational196_literal_decoded :
    parseRational "527178176143877398266019493048827721587097600000/176480456333299613523084093619223173942381079782743179928822994473" = .ok rational196 :=
  rational196_decoded

#check (900266 : Nat)
private theorem rational197_literal_decoded :
    parseRational "83671670085199609763724701588773923710174541757915874488976563200000000000/10792869509462433901057510596987142161214465301134985226078502090793139753068803549658768369" = .ok rational197 :=
  rational197_decoded

#check (900267 : Nat)
private theorem rational198_literal_decoded :
    parseRational "2401454637616388528985636569847083107/174992892480000000000000000000000000000000000000000000000000" = .ok rational198 :=
  rational198_decoded

#check (900268 : Nat)
private theorem rational199_literal_decoded :
    parseRational "6983424367/84420000000" = .ok rational199 :=
  rational199_decoded

#check (900269 : Nat)
private theorem rational200_literal_decoded :
    parseRational "7030659751/84420000000" = .ok rational200 :=
  rational200_decoded

#check (900270 : Nat)
private theorem rational201_literal_decoded :
    parseRational "8438842529/50652000000" = .ok rational201 :=
  rational201_decoded

#check (900271 : Nat)
private theorem rational202_literal_decoded :
    parseRational "1841720107/56280000000" = .ok rational202 :=
  rational202_decoded

#check (900272 : Nat)
private theorem rational203_literal_decoded :
    parseRational "1753809809/56280000000" = .ok rational203 :=
  rational203_decoded

#check (900273 : Nat)
private theorem rational204_literal_decoded :
    parseRational "85492733/2814000000" = .ok rational204 :=
  rational204_decoded

#check (900274 : Nat)
private theorem rational205_literal_decoded :
    parseRational "492154897/16884000000" = .ok rational205 :=
  rational205_decoded

#check (900275 : Nat)
private theorem rational206_literal_decoded :
    parseRational "7206480347/253260000000" = .ok rational206 :=
  rational206_decoded

#check (900276 : Nat)
private theorem rational207_literal_decoded :
    parseRational "184374665291403714007091482593393439433643622400000/7902048678624779531411509270725203855805769561562648665697108469" = .ok rational207 :=
  rational207_decoded

#check (900277 : Nat)
private theorem rational208_literal_decoded :
    parseRational "5198472524969182905655151889186504060746918177840883296767789516800000000000/86090918104583608061422575609075548966313237976000114258078678039738042890550757419524289" = .ok rational208 :=
  rational208_decoded

#check (900278 : Nat)
private theorem rational209_literal_decoded :
    parseRational "683009083340818191306752491481889166786699/22171074498538560000000000000000000000000000000000000000000000000" = .ok rational209 :=
  rational209_decoded

#check (900279 : Nat)
private theorem rational210_literal_decoded :
    parseRational "960470753275685500685044110818151778121541701531/81551863327974385248000000000000000000000000000000000000000000000000000000" = .ok rational210 :=
  rational210_decoded

#check (900280 : Nat)
private theorem integer000_literal_decoded :
    parseInteger "340536956576" = .ok integer000 :=
  integer000_decoded

#check (900281 : Nat)
private theorem integer001_literal_decoded :
    parseInteger "865723779014" = .ok integer001 :=
  integer001_decoded

#check (900282 : Nat)
private theorem integer002_literal_decoded :
    parseInteger "1725445527631473" = .ok integer002 :=
  integer002_decoded

#check (900283 : Nat)
private theorem integer003_literal_decoded :
    parseInteger "4468106318873900" = .ok integer003 :=
  integer003_decoded

#check (900284 : Nat)
private theorem integer004_literal_decoded :
    parseInteger "285294645074" = .ok integer004 :=
  integer004_decoded

#check (900285 : Nat)
private theorem integer005_literal_decoded :
    parseInteger "738770079548" = .ok integer005 :=
  integer005_decoded

#check (900286 : Nat)
private theorem integer006_literal_decoded :
    parseInteger "285285513112" = .ok integer006 :=
  integer006_decoded

#check (900287 : Nat)
private theorem integer007_literal_decoded :
    parseInteger "738930739492" = .ok integer007 :=
  integer007_decoded

#check (900288 : Nat)
private theorem integer008_literal_decoded :
    parseInteger "1525256338207148" = .ok integer008 :=
  integer008_decoded

#check (900289 : Nat)
private theorem integer009_literal_decoded :
    parseInteger "3980675863991622" = .ok integer009 :=
  integer009_decoded

#check (900290 : Nat)
private theorem integer010_literal_decoded :
    parseInteger "236675476927" = .ok integer010 :=
  integer010_decoded

#check (900291 : Nat)
private theorem integer011_literal_decoded :
    parseInteger "613151140838" = .ok integer011 :=
  integer011_decoded

#check (900292 : Nat)
private theorem integer012_literal_decoded :
    parseInteger "236668462226" = .ok integer012 :=
  integer012_decoded

#check (900293 : Nat)
private theorem integer013_literal_decoded :
    parseInteger "614215957075" = .ok integer013 :=
  integer013_decoded

#check (900294 : Nat)
private theorem integer014_literal_decoded :
    parseInteger "1848592249847117" = .ok integer014 :=
  integer014_decoded

#check (900295 : Nat)
private theorem integer015_literal_decoded :
    parseInteger "4784075197500631" = .ok integer015 :=
  integer015_decoded

attribute [local simp] rational000_literal_decoded rational001_literal_decoded rational002_literal_decoded rational003_literal_decoded rational004_literal_decoded rational005_literal_decoded rational006_literal_decoded rational007_literal_decoded rational008_literal_decoded rational009_literal_decoded rational010_literal_decoded rational011_literal_decoded rational012_literal_decoded rational013_literal_decoded rational014_literal_decoded rational015_literal_decoded rational016_literal_decoded rational017_literal_decoded rational018_literal_decoded rational019_literal_decoded rational020_literal_decoded rational021_literal_decoded rational022_literal_decoded rational023_literal_decoded rational024_literal_decoded rational025_literal_decoded rational026_literal_decoded rational027_literal_decoded rational028_literal_decoded rational029_literal_decoded rational030_literal_decoded rational031_literal_decoded rational032_literal_decoded rational033_literal_decoded rational034_literal_decoded rational035_literal_decoded rational036_literal_decoded rational037_literal_decoded rational038_literal_decoded rational039_literal_decoded rational040_literal_decoded rational041_literal_decoded rational042_literal_decoded rational043_literal_decoded rational044_literal_decoded rational045_literal_decoded rational046_literal_decoded rational047_literal_decoded rational048_literal_decoded rational049_literal_decoded rational050_literal_decoded rational051_literal_decoded rational052_literal_decoded rational053_literal_decoded rational054_literal_decoded rational055_literal_decoded rational056_literal_decoded rational057_literal_decoded rational058_literal_decoded rational059_literal_decoded rational060_literal_decoded rational061_literal_decoded rational062_literal_decoded rational063_literal_decoded rational064_literal_decoded rational065_literal_decoded rational066_literal_decoded rational067_literal_decoded rational068_literal_decoded rational069_literal_decoded rational070_literal_decoded rational071_literal_decoded rational072_literal_decoded rational073_literal_decoded rational074_literal_decoded rational075_literal_decoded rational076_literal_decoded rational077_literal_decoded rational078_literal_decoded rational079_literal_decoded rational080_literal_decoded rational081_literal_decoded rational082_literal_decoded rational083_literal_decoded rational084_literal_decoded rational085_literal_decoded rational086_literal_decoded rational087_literal_decoded rational088_literal_decoded rational089_literal_decoded rational090_literal_decoded rational091_literal_decoded rational092_literal_decoded rational093_literal_decoded rational094_literal_decoded rational095_literal_decoded rational096_literal_decoded rational097_literal_decoded rational098_literal_decoded rational099_literal_decoded rational100_literal_decoded rational101_literal_decoded rational102_literal_decoded rational103_literal_decoded rational104_literal_decoded rational105_literal_decoded rational106_literal_decoded rational107_literal_decoded rational108_literal_decoded rational109_literal_decoded rational110_literal_decoded rational111_literal_decoded rational112_literal_decoded rational113_literal_decoded rational114_literal_decoded rational115_literal_decoded rational116_literal_decoded rational117_literal_decoded rational118_literal_decoded rational119_literal_decoded rational120_literal_decoded rational121_literal_decoded rational122_literal_decoded rational123_literal_decoded rational124_literal_decoded rational125_literal_decoded rational126_literal_decoded rational127_literal_decoded rational128_literal_decoded rational129_literal_decoded rational130_literal_decoded rational131_literal_decoded rational132_literal_decoded rational133_literal_decoded rational134_literal_decoded rational135_literal_decoded rational136_literal_decoded rational137_literal_decoded rational138_literal_decoded rational139_literal_decoded rational140_literal_decoded rational141_literal_decoded rational142_literal_decoded rational143_literal_decoded rational144_literal_decoded rational145_literal_decoded rational146_literal_decoded rational147_literal_decoded rational148_literal_decoded rational149_literal_decoded rational150_literal_decoded rational151_literal_decoded rational152_literal_decoded rational153_literal_decoded rational154_literal_decoded rational155_literal_decoded rational156_literal_decoded rational157_literal_decoded rational158_literal_decoded rational159_literal_decoded rational160_literal_decoded rational161_literal_decoded rational162_literal_decoded rational163_literal_decoded rational164_literal_decoded rational165_literal_decoded rational166_literal_decoded rational167_literal_decoded rational168_literal_decoded rational169_literal_decoded rational170_literal_decoded rational171_literal_decoded rational172_literal_decoded rational173_literal_decoded rational174_literal_decoded rational175_literal_decoded rational176_literal_decoded rational177_literal_decoded rational178_literal_decoded rational179_literal_decoded rational180_literal_decoded rational181_literal_decoded rational182_literal_decoded rational183_literal_decoded rational184_literal_decoded rational185_literal_decoded rational186_literal_decoded rational187_literal_decoded rational188_literal_decoded rational189_literal_decoded rational190_literal_decoded rational191_literal_decoded rational192_literal_decoded rational193_literal_decoded rational194_literal_decoded rational195_literal_decoded rational196_literal_decoded rational197_literal_decoded rational198_literal_decoded rational199_literal_decoded rational200_literal_decoded rational201_literal_decoded rational202_literal_decoded rational203_literal_decoded rational204_literal_decoded rational205_literal_decoded rational206_literal_decoded rational207_literal_decoded rational208_literal_decoded rational209_literal_decoded rational210_literal_decoded integer000_literal_decoded integer001_literal_decoded integer002_literal_decoded integer003_literal_decoded integer004_literal_decoded integer005_literal_decoded integer006_literal_decoded integer007_literal_decoded integer008_literal_decoded integer009_literal_decoded integer010_literal_decoded integer011_literal_decoded integer012_literal_decoded integer013_literal_decoded integer014_literal_decoded integer015_literal_decoded

attribute [local simp] decodeString_str decodeNat_number_ofList decodeArray_arr rationalArray_arr
attribute [local simp] SourceJson.getStr? SourceJson.getArr? SourceJson.getObjValAs?
attribute [local simp] SourceJson.natChars SourceJson.digitsNat
attribute [local simp] rational000_decoded rational001_decoded rational002_decoded rational003_decoded rational004_decoded rational005_decoded rational006_decoded rational007_decoded rational008_decoded rational009_decoded rational010_decoded rational011_decoded rational012_decoded rational013_decoded rational014_decoded rational015_decoded rational016_decoded rational017_decoded rational018_decoded rational019_decoded rational020_decoded rational021_decoded rational022_decoded rational023_decoded rational024_decoded rational025_decoded rational026_decoded rational027_decoded rational028_decoded rational029_decoded rational030_decoded rational031_decoded rational032_decoded rational033_decoded rational034_decoded rational035_decoded rational036_decoded rational037_decoded rational038_decoded rational039_decoded rational040_decoded rational041_decoded rational042_decoded rational043_decoded rational044_decoded rational045_decoded rational046_decoded rational047_decoded rational048_decoded rational049_decoded rational050_decoded rational051_decoded rational052_decoded rational053_decoded rational054_decoded rational055_decoded rational056_decoded rational057_decoded rational058_decoded rational059_decoded rational060_decoded rational061_decoded rational062_decoded rational063_decoded rational064_decoded rational065_decoded rational066_decoded rational067_decoded rational068_decoded rational069_decoded rational070_decoded rational071_decoded rational072_decoded rational073_decoded rational074_decoded rational075_decoded rational076_decoded rational077_decoded rational078_decoded rational079_decoded rational080_decoded rational081_decoded rational082_decoded rational083_decoded rational084_decoded rational085_decoded rational086_decoded rational087_decoded rational088_decoded rational089_decoded rational090_decoded rational091_decoded rational092_decoded rational093_decoded rational094_decoded rational095_decoded rational096_decoded rational097_decoded rational098_decoded rational099_decoded rational100_decoded rational101_decoded rational102_decoded rational103_decoded rational104_decoded rational105_decoded rational106_decoded rational107_decoded rational108_decoded rational109_decoded rational110_decoded rational111_decoded rational112_decoded rational113_decoded rational114_decoded rational115_decoded rational116_decoded rational117_decoded rational118_decoded rational119_decoded rational120_decoded rational121_decoded rational122_decoded rational123_decoded rational124_decoded rational125_decoded rational126_decoded rational127_decoded rational128_decoded rational129_decoded rational130_decoded rational131_decoded rational132_decoded rational133_decoded rational134_decoded rational135_decoded rational136_decoded rational137_decoded rational138_decoded rational139_decoded rational140_decoded rational141_decoded rational142_decoded rational143_decoded rational144_decoded rational145_decoded rational146_decoded rational147_decoded rational148_decoded rational149_decoded rational150_decoded rational151_decoded rational152_decoded rational153_decoded rational154_decoded rational155_decoded rational156_decoded rational157_decoded rational158_decoded rational159_decoded rational160_decoded rational161_decoded rational162_decoded rational163_decoded rational164_decoded rational165_decoded rational166_decoded rational167_decoded rational168_decoded rational169_decoded rational170_decoded rational171_decoded rational172_decoded rational173_decoded rational174_decoded rational175_decoded rational176_decoded rational177_decoded rational178_decoded rational179_decoded rational180_decoded rational181_decoded rational182_decoded rational183_decoded rational184_decoded rational185_decoded rational186_decoded rational187_decoded rational188_decoded rational189_decoded rational190_decoded rational191_decoded rational192_decoded rational193_decoded rational194_decoded rational195_decoded rational196_decoded rational197_decoded rational198_decoded rational199_decoded rational200_decoded rational201_decoded rational202_decoded rational203_decoded rational204_decoded rational205_decoded rational206_decoded rational207_decoded rational208_decoded rational209_decoded rational210_decoded integer000_decoded integer001_decoded integer002_decoded integer003_decoded integer004_decoded integer005_decoded integer006_decoded integer007_decoded integer008_decoded integer009_decoded integer010_decoded integer011_decoded integer012_decoded integer013_decoded integer014_decoded integer015_decoded

#check (900296 : Nat)
theorem lookup_dimension : rawRoot.getObjVal? "dimension" = .ok rawDimension := by
  rfl

attribute [local simp] lookup_dimension

#check (900297 : Nat)
theorem lookup_physical_jacobian : rawRoot.getObjVal? "physical_jacobian" = .ok rawPhysicalJacobian := by
  rfl

attribute [local simp] lookup_physical_jacobian

#check (900298 : Nat)
theorem lookup_cell_id : rawRoot.getObjVal? "cell_id" = .ok rawCellId := by
  rfl

attribute [local simp] lookup_cell_id

#check (900299 : Nat)
theorem lookup_left_masks : rawRoot.getObjVal? "left_masks" = .ok rawLeftMasks := by
  rfl

attribute [local simp] lookup_left_masks

#check (900300 : Nat)
theorem lookup_right_masks : rawRoot.getObjVal? "right_masks" = .ok rawRightMasks := by
  rfl

attribute [local simp] lookup_right_masks

#check (900301 : Nat)
theorem lookup_facet_original_indices : rawRoot.getObjVal? "facet_original_indices" = .ok rawFacetOriginalIndices := by
  rfl

attribute [local simp] lookup_facet_original_indices

#check (900302 : Nat)
theorem lookup_positive_normal_balance : rawRoot.getObjVal? "positive_normal_balance" = .ok rawPositiveNormalBalance := by
  rfl

attribute [local simp] lookup_positive_normal_balance

#check (900303 : Nat)
theorem lookup_normal_rank : rawRoot.getObjVal? "normal_rank" = .ok rawNormalRank := by
  rfl

attribute [local simp] lookup_normal_rank

#check (900304 : Nat)
theorem lookup_active8_enumeration : rawRoot.getObjVal? "active8_enumeration" = .ok rawActive8 := by
  rfl

attribute [local simp] lookup_active8_enumeration

#check (900305 : Nat)
theorem lookup_vertices : rawRoot.getObjVal? "vertices" = .ok rawVertices := by
  rfl

attribute [local simp] lookup_vertices

#check (900306 : Nat)
theorem lookup_vertex_values : rawRoot.getObjVal? "vertex_values" = .ok rawVertexValues := by
  rfl

attribute [local simp] lookup_vertex_values

#check (900307 : Nat)
theorem lookup_all_original_constraint_minima : rawRoot.getObjVal? "all_original_constraint_minima" = .ok rawAllOriginalMinima := by
  rfl

attribute [local simp] lookup_all_original_constraint_minima

#check (900308 : Nat)
theorem lookup_facet_vertices : rawRoot.getObjVal? "facet_vertices" = .ok rawFacetVertices := by
  rfl

attribute [local simp] lookup_facet_vertices

#check (900309 : Nat)
theorem lookup_face_ledger : rawRoot.getObjVal? "face_ledger" = .ok rawFaceLedger := by
  rfl

attribute [local simp] lookup_face_ledger

#check (900310 : Nat)
theorem lookup_simplices : rawRoot.getObjVal? "simplices" = .ok rawSimplices := by
  rfl

attribute [local simp] lookup_simplices

#check (900311 : Nat)
theorem lookup_physical_volume : rawRoot.getObjVal? "physical_volume" = .ok rawPhysicalVolume := by
  rfl

attribute [local simp] lookup_physical_volume

#check (900312 : Nat)
theorem lookup_integral_gap : rawRoot.getObjVal? "integral_gap" = .ok rawIntegralGap := by
  rfl

attribute [local simp] lookup_integral_gap

#check (900313 : Nat)
theorem cellId_decoded :
    (SourceJson.Decode.read rawCellId : Except String (Nat)) = .ok cellId := by
  unfold rawCellId cellId
  simp

attribute [local simp] cellId_decoded

#check (900314 : Nat)
theorem cellId_field : rawRoot.getObjValAs? (Nat) "cell_id" = .ok cellId := by
  rw [getObjValAs_of_lookup rawRoot "cell_id" rawCellId lookup_cell_id]
  exact cellId_decoded

attribute [local simp] cellId_field

#check (900315 : Nat)
theorem dimension_decoded :
    (SourceJson.Decode.read rawDimension : Except String (Nat)) = .ok dimension := by
  unfold rawDimension dimension
  simp

attribute [local simp] dimension_decoded

#check (900316 : Nat)
theorem dimension_field : rawRoot.getObjValAs? (Nat) "dimension" = .ok dimension := by
  rw [getObjValAs_of_lookup rawRoot "dimension" rawDimension lookup_dimension]
  exact dimension_decoded

attribute [local simp] dimension_field

#check (900317 : Nat)
theorem physicalJacobian_decoded :
    (SourceJson.Decode.read rawPhysicalJacobian : Except String (Nat)) = .ok physicalJacobian := by
  unfold rawPhysicalJacobian physicalJacobian
  simp

attribute [local simp] physicalJacobian_decoded

#check (900318 : Nat)
theorem physicalJacobian_field : rawRoot.getObjValAs? (Nat) "physical_jacobian" = .ok physicalJacobian := by
  rw [getObjValAs_of_lookup rawRoot "physical_jacobian" rawPhysicalJacobian lookup_physical_jacobian]
  exact physicalJacobian_decoded

attribute [local simp] physicalJacobian_field

#check (900319 : Nat)
theorem leftMasks_decoded :
    (SourceJson.Decode.read rawLeftMasks : Except String (Array Nat)) = .ok leftMasks := by
  unfold rawLeftMasks leftMasks
  simp

attribute [local simp] leftMasks_decoded

#check (900320 : Nat)
theorem leftMasks_field : rawRoot.getObjValAs? (Array Nat) "left_masks" = .ok leftMasks := by
  rw [getObjValAs_of_lookup rawRoot "left_masks" rawLeftMasks lookup_left_masks]
  exact leftMasks_decoded

attribute [local simp] leftMasks_field

#check (900321 : Nat)
theorem rightMasks_decoded :
    (SourceJson.Decode.read rawRightMasks : Except String (Array Nat)) = .ok rightMasks := by
  unfold rawRightMasks rightMasks
  simp

attribute [local simp] rightMasks_decoded

#check (900322 : Nat)
theorem rightMasks_field : rawRoot.getObjValAs? (Array Nat) "right_masks" = .ok rightMasks := by
  rw [getObjValAs_of_lookup rawRoot "right_masks" rawRightMasks lookup_right_masks]
  exact rightMasks_decoded

attribute [local simp] rightMasks_field

#check (900323 : Nat)
theorem facetOriginalIndices_decoded :
    (SourceJson.Decode.read rawFacetOriginalIndices : Except String (Array Nat)) = .ok facetOriginalIndices := by
  unfold rawFacetOriginalIndices facetOriginalIndices
  simp

attribute [local simp] facetOriginalIndices_decoded

#check (900324 : Nat)
theorem facetOriginalIndices_field : rawRoot.getObjValAs? (Array Nat) "facet_original_indices" = .ok facetOriginalIndices := by
  rw [getObjValAs_of_lookup rawRoot "facet_original_indices" rawFacetOriginalIndices lookup_facet_original_indices]
  exact facetOriginalIndices_decoded

attribute [local simp] facetOriginalIndices_field

#check (900325 : Nat)
theorem normalRank_decoded :
    (SourceJson.Decode.read rawNormalRank : Except String (Nat)) = .ok normalRank := by
  unfold rawNormalRank normalRank
  simp

attribute [local simp] normalRank_decoded

#check (900326 : Nat)
theorem normalRank_field : rawRoot.getObjValAs? (Nat) "normal_rank" = .ok normalRank := by
  rw [getObjValAs_of_lookup rawRoot "normal_rank" rawNormalRank lookup_normal_rank]
  exact normalRank_decoded

attribute [local simp] normalRank_field

#check (900327 : Nat)
theorem facetVertices_decoded :
    (SourceJson.Decode.read rawFacetVertices : Except String (Array (Array Nat))) = .ok facetVertices := by
  unfold rawFacetVertices facetVertices
  simp

attribute [local simp] facetVertices_decoded

#check (900328 : Nat)
theorem facetVertices_field : rawRoot.getObjValAs? (Array (Array Nat)) "facet_vertices" = .ok facetVertices := by
  rw [getObjValAs_of_lookup rawRoot "facet_vertices" rawFacetVertices lookup_facet_vertices]
  exact facetVertices_decoded

attribute [local simp] facetVertices_field

#check (900329 : Nat)
theorem positiveNormalBalance_decoded : rationalArray rawPositiveNormalBalance = .ok positiveNormalBalance := by
  unfold rawPositiveNormalBalance positiveNormalBalance
  simp

attribute [local simp] positiveNormalBalance_decoded

#check (900330 : Nat)
theorem positiveNormalBalance_field : rationalArrayField rawRoot "positive_normal_balance" = .ok positiveNormalBalance := by
  rw [rationalArrayField_of_lookup rawRoot "positive_normal_balance" rawPositiveNormalBalance lookup_positive_normal_balance]
  exact positiveNormalBalance_decoded

attribute [local simp] positiveNormalBalance_field

#check (900331 : Nat)
theorem allOriginalMinima_decoded : rationalArray rawAllOriginalMinima = .ok allOriginalMinima := by
  unfold rawAllOriginalMinima allOriginalMinima
  simp

attribute [local simp] allOriginalMinima_decoded

#check (900332 : Nat)
theorem allOriginalMinima_field : rationalArrayField rawRoot "all_original_constraint_minima" = .ok allOriginalMinima := by
  rw [rationalArrayField_of_lookup rawRoot "all_original_constraint_minima" rawAllOriginalMinima lookup_all_original_constraint_minima]
  exact allOriginalMinima_decoded

attribute [local simp] allOriginalMinima_field

#check (900333 : Nat)
theorem vertex00_decoded : rationalArray rawVertex00 = .ok vertex00 := by
  unfold rawVertex00 vertex00
  simp

attribute [local simp] vertex00_decoded

#check (900334 : Nat)
theorem vertex01_decoded : rationalArray rawVertex01 = .ok vertex01 := by
  unfold rawVertex01 vertex01
  simp

attribute [local simp] vertex01_decoded

#check (900335 : Nat)
theorem vertex02_decoded : rationalArray rawVertex02 = .ok vertex02 := by
  unfold rawVertex02 vertex02
  simp

attribute [local simp] vertex02_decoded

#check (900336 : Nat)
theorem vertex03_decoded : rationalArray rawVertex03 = .ok vertex03 := by
  unfold rawVertex03 vertex03
  simp

attribute [local simp] vertex03_decoded

#check (900337 : Nat)
theorem vertex04_decoded : rationalArray rawVertex04 = .ok vertex04 := by
  unfold rawVertex04 vertex04
  simp

attribute [local simp] vertex04_decoded

#check (900338 : Nat)
theorem vertex05_decoded : rationalArray rawVertex05 = .ok vertex05 := by
  unfold rawVertex05 vertex05
  simp

attribute [local simp] vertex05_decoded

#check (900339 : Nat)
theorem vertex06_decoded : rationalArray rawVertex06 = .ok vertex06 := by
  unfold rawVertex06 vertex06
  simp

attribute [local simp] vertex06_decoded

#check (900340 : Nat)
theorem vertex07_decoded : rationalArray rawVertex07 = .ok vertex07 := by
  unfold rawVertex07 vertex07
  simp

attribute [local simp] vertex07_decoded

#check (900341 : Nat)
theorem vertex08_decoded : rationalArray rawVertex08 = .ok vertex08 := by
  unfold rawVertex08 vertex08
  simp

attribute [local simp] vertex08_decoded

#check (900342 : Nat)
theorem vertex09_decoded : rationalArray rawVertex09 = .ok vertex09 := by
  unfold rawVertex09 vertex09
  simp

attribute [local simp] vertex09_decoded

#check (900343 : Nat)
theorem vertex10_decoded : rationalArray rawVertex10 = .ok vertex10 := by
  unfold rawVertex10 vertex10
  simp

attribute [local simp] vertex10_decoded

#check (900344 : Nat)
theorem vertex11_decoded : rationalArray rawVertex11 = .ok vertex11 := by
  unfold rawVertex11 vertex11
  simp

attribute [local simp] vertex11_decoded

#check (900345 : Nat)
theorem vertex12_decoded : rationalArray rawVertex12 = .ok vertex12 := by
  unfold rawVertex12 vertex12
  simp

attribute [local simp] vertex12_decoded

#check (900346 : Nat)
theorem vertex13_decoded : rationalArray rawVertex13 = .ok vertex13 := by
  unfold rawVertex13 vertex13
  simp

attribute [local simp] vertex13_decoded

#check (900347 : Nat)
theorem vertex14_decoded : rationalArray rawVertex14 = .ok vertex14 := by
  unfold rawVertex14 vertex14
  simp

attribute [local simp] vertex14_decoded

#check (900348 : Nat)
theorem vertex15_decoded : rationalArray rawVertex15 = .ok vertex15 := by
  unfold rawVertex15 vertex15
  simp

attribute [local simp] vertex15_decoded

#check (900349 : Nat)
theorem vertices_mapped : rawVerticesItems.toArray.mapM rationalArray = .ok vertices := by
  unfold rawVerticesItems vertices
  simp

attribute [local simp] vertices_mapped

#check (900350 : Nat)
theorem simplex00_lookup_simplex_id :
    rawSimplex00.getObjVal? "simplex_id" = .ok (.number (String.ofList ['0'])) := by
  rfl

attribute [local simp] simplex00_lookup_simplex_id

#check (900351 : Nat)
theorem simplex00_lookup_vertex_ids :
    rawSimplex00.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex00_lookup_vertex_ids

#check (900352 : Nat)
theorem simplex00_lookup_physical_volume :
    rawSimplex00.getObjVal? "physical_volume" = .ok (.str (String.ofList ['3', '8', '7', '7', '3', '5', '6', '8', '0', '8', '5', '7', '7', '9', '4', '6', '8', '9', '1', '0', '1', '7', '4', '0', '8', '3', '2', '1', '9', '1', '1', '/', '1', '6', '8', '3', '1', '0', '3', '2', '2', '9', '1', '6', '5', '0', '3', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex00_lookup_physical_volume

#check (900353 : Nat)
theorem simplex00_lookup_mean_gap :
    rawSimplex00.getObjVal? "mean_gap" = .ok (.str (String.ofList ['2', '3', '4', '3', '1', '/', '6', '8', '6', '2', '5', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex00_lookup_mean_gap

#check (900354 : Nat)
theorem simplex00_lookup_factor_maxima :
    rawSimplex00.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '6', '8', '6', '3', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '0', '7', '8', '1', '3', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '8', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex00_lookup_factor_maxima

#check (900355 : Nat)
theorem simplex00_lookup_gap_weighted_means :
    rawSimplex00.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['6', '9', '7', '3', '2', '9', '5', '8', '7', '/', '8', '5', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '2', '5', '7', '8', '1', '3', '1', '/', '8', '5', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '7', '9', '8', '4', '6', '1', '9', '3', '4', '9', '/', '7', '1', '4', '7', '9', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '1', '5', '7', '4', '8', '8', '3', '2', '1', '/', '2', '6', '4', '7', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '0', '5', '4', '6', '0', '8', '2', '9', '1', '/', '7', '9', '4', '2', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '9', '4', '1', '1', '0', '7', '8', '0', '3', '/', '7', '9', '4', '2', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '6', '6', '9', '8', '8', '8', '1', '/', '5', '2', '9', '4', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '0', '8', '0', '1', '7', '0', '9', '2', '1', '/', '7', '9', '4', '2', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '0', '2', '6', '7', '0', '5', '9', '9', '1', '/', '2', '6', '4', '7', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '4', '3', '3', '5', '9', '2', '3', '9', '/', '2', '3', '0', '5', '8', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex00_lookup_gap_weighted_means

#check (900356 : Nat)
theorem simplex00_lookup_max_bound :
    rawSimplex00.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '2', '4', '8', '6', '3', '7', '6', '6', '6', '6', '7', '2', '0', '8', '5', '5', '4', '5', '8', '2', '6', '2', '4', '2', '4', '7', '9', '5', '8', '2', '3', '3', '5', '7', '4', '3', '2', '0', '6', '5', '6', '8', '7', '5', '5', '2', '0', '0', '0', '0', '/', '2', '9', '0', '5', '0', '3', '7', '6', '4', '9', '1', '0', '1', '5', '8', '8', '6', '8', '5', '5', '9', '3', '5', '3', '5', '2', '3', '6', '0', '4', '9', '9', '2', '5', '0', '0', '1', '7', '9', '5', '4', '1', '6', '2', '6', '4', '9', '1', '2', '1', '3', '4', '6', '5', '7', '1', '1', '5', '2', '0', '8', '6', '9', '8', '0', '3', '4', '1'])) := by
  rfl

attribute [local simp] simplex00_lookup_max_bound

#check (900357 : Nat)
theorem simplex00_lookup_jensen_bound :
    rawSimplex00.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '7', '0', '8', '5', '6', '5', '3', '6', '5', '0', '1', '2', '6', '8', '5', '4', '6', '8', '9', '8', '0', '1', '8', '8', '8', '4', '5', '5', '8', '7', '5', '5', '8', '3', '2', '3', '4', '1', '2', '6', '0', '6', '5', '7', '0', '4', '8', '8', '4', '1', '1', '7', '6', '8', '7', '8', '0', '1', '7', '6', '9', '4', '8', '8', '3', '2', '7', '6', '3', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '6', '3', '6', '2', '2', '2', '2', '7', '8', '5', '9', '8', '5', '7', '1', '8', '2', '7', '1', '6', '7', '0', '7', '5', '7', '6', '2', '0', '8', '6', '2', '8', '1', '1', '7', '8', '0', '3', '0', '3', '1', '1', '9', '3', '8', '0', '8', '2', '5', '0', '2', '9', '6', '2', '3', '8', '1', '9', '7', '5', '6', '9', '7', '9', '2', '3', '8', '1', '3', '8', '7', '3', '1', '3', '0', '9', '5', '2', '5', '2', '6', '8', '8', '0', '3', '9', '5', '3', '0', '2', '8', '0', '9', '0', '4', '3', '6', '7', '4', '1', '4', '3'])) := by
  rfl

attribute [local simp] simplex00_lookup_jensen_bound

#check (900358 : Nat)
theorem simplex00_lookup_max_floor_Q96 :
    rawSimplex00.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['3', '4', '0', '5', '3', '6', '9', '5', '6', '5', '7', '6'])) := by
  rfl

attribute [local simp] simplex00_lookup_max_floor_Q96

#check (900359 : Nat)
theorem simplex00_lookup_jensen_floor_Q96 :
    rawSimplex00.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['8', '6', '5', '7', '2', '3', '7', '7', '9', '0', '1', '4'])) := by
  rfl

attribute [local simp] simplex00_lookup_jensen_floor_Q96

#check (900360 : Nat)
theorem simplex00_decoded : decodeSimplex rawSimplex00 = .ok simplex00 := by
  unfold decodeSimplex simplex00
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex00_decoded

#check (900361 : Nat)
theorem simplex01_lookup_simplex_id :
    rawSimplex01.getObjVal? "simplex_id" = .ok (.number (String.ofList ['1'])) := by
  rfl

attribute [local simp] simplex01_lookup_simplex_id

#check (900362 : Nat)
theorem simplex01_lookup_vertex_ids :
    rawSimplex01.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex01_lookup_vertex_ids

#check (900363 : Nat)
theorem simplex01_lookup_physical_volume :
    rawSimplex01.getObjVal? "physical_volume" = .ok (.str (String.ofList ['8', '7', '3', '1', '5', '2', '8', '0', '3', '7', '5', '6', '3', '1', '0', '4', '7', '4', '1', '6', '9', '3', '6', '0', '8', '5', '4', '2', '7', '5', '0', '7', '6', '3', '/', '7', '4', '8', '0', '4', '5', '8', '7', '9', '6', '2', '8', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex01_lookup_physical_volume

#check (900364 : Nat)
theorem simplex01_lookup_mean_gap :
    rawSimplex01.getObjVal? "mean_gap" = .ok (.str (String.ofList ['2', '3', '4', '3', '1', '/', '6', '8', '6', '2', '5', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex01_lookup_mean_gap

#check (900365 : Nat)
theorem simplex01_lookup_factor_maxima :
    rawSimplex01.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '6', '8', '6', '3', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '0', '7', '8', '1', '3', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '8', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex01_lookup_factor_maxima

#check (900366 : Nat)
theorem simplex01_lookup_gap_weighted_means :
    rawSimplex01.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['1', '9', '7', '9', '8', '3', '0', '9', '1', '/', '2', '4', '0', '1', '8', '7', '5', '0', '0', '0']), .str (String.ofList ['4', '9', '8', '6', '4', '8', '1', '1', '/', '6', '0', '0', '4', '6', '8', '7', '5', '0']), .str (String.ofList ['2', '9', '7', '3', '2', '3', '0', '6', '5', '7', '1', '7', '/', '1', '7', '8', '6', '9', '9', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '6', '2', '6', '4', '9', '8', '5', '7', '1', '/', '1', '9', '8', '5', '5', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '2', '7', '2', '0', '3', '4', '4', '0', '3', '/', '1', '9', '8', '5', '5', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '7', '9', '4', '3', '0', '9', '0', '8', '1', '/', '1', '1', '9', '1', '3', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '9', '3', '3', '3', '7', '2', '1', '9', '9', '/', '1', '1', '9', '1', '3', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '0', '0', '1', '4', '5', '1', '8', '7', '9', '/', '5', '9', '5', '6', '6', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '8', '0', '0', '1', '9', '6', '5', '3', '1', '/', '5', '9', '5', '6', '6', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '3', '5', '6', '9', '2', '8', '1', '9', '/', '5', '7', '6', '4', '5', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex01_lookup_gap_weighted_means

#check (900367 : Nat)
theorem simplex01_lookup_max_bound :
    rawSimplex01.getObjVal? "max_bound" = .ok (.str (String.ofList ['4', '1', '3', '5', '0', '6', '1', '7', '9', '1', '9', '9', '8', '2', '9', '9', '1', '4', '0', '8', '3', '9', '9', '7', '9', '2', '0', '1', '4', '1', '5', '6', '0', '9', '3', '8', '9', '4', '2', '3', '9', '1', '3', '8', '6', '1', '1', '2', '0', '0', '0', '0', '/', '1', '8', '9', '8', '7', '1', '7', '4', '1', '7', '7', '1', '3', '4', '5', '6', '6', '5', '7', '2', '5', '0', '6', '7', '6', '6', '2', '4', '8', '6', '9', '2', '3', '2', '0', '2', '7', '3', '1', '7', '2', '6', '5', '5', '3', '2', '6', '2', '2', '3', '1', '0', '2', '3', '3', '4', '0', '8', '6', '3', '3', '1', '3', '5', '9', '7'])) := by
  rfl

attribute [local simp] simplex01_lookup_max_bound

#check (900368 : Nat)
theorem simplex01_lookup_jensen_bound :
    rawSimplex01.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['2', '7', '6', '5', '9', '0', '5', '4', '1', '8', '8', '4', '2', '4', '3', '0', '8', '5', '5', '1', '1', '6', '2', '0', '8', '1', '9', '4', '3', '7', '8', '7', '7', '8', '6', '5', '9', '0', '9', '5', '8', '4', '7', '6', '0', '8', '6', '9', '6', '9', '8', '0', '5', '8', '7', '0', '0', '5', '8', '1', '4', '2', '0', '7', '2', '4', '2', '6', '0', '6', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '9', '0', '4', '4', '8', '4', '9', '9', '6', '1', '9', '3', '2', '3', '8', '7', '9', '8', '2', '0', '3', '1', '2', '0', '0', '2', '4', '2', '5', '9', '3', '7', '5', '9', '9', '6', '3', '2', '6', '5', '4', '7', '7', '9', '3', '0', '5', '9', '4', '7', '9', '9', '7', '2', '9', '0', '7', '2', '5', '1', '2', '5', '6', '4', '6', '8', '8', '9', '5', '7', '9', '7', '4', '8', '7', '8', '4', '7', '6', '8', '9', '7', '0', '2', '1', '8', '0', '2', '0', '7', '9', '6', '2', '9', '9', '5', '7'])) := by
  rfl

attribute [local simp] simplex01_lookup_jensen_bound

#check (900369 : Nat)
theorem simplex01_lookup_max_floor_Q96 :
    rawSimplex01.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['1', '7', '2', '5', '4', '4', '5', '5', '2', '7', '6', '3', '1', '4', '7', '3'])) := by
  rfl

attribute [local simp] simplex01_lookup_max_floor_Q96

#check (900370 : Nat)
theorem simplex01_lookup_jensen_floor_Q96 :
    rawSimplex01.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['4', '4', '6', '8', '1', '0', '6', '3', '1', '8', '8', '7', '3', '9', '0', '0'])) := by
  rfl

attribute [local simp] simplex01_lookup_jensen_floor_Q96

#check (900371 : Nat)
theorem simplex01_decoded : decodeSimplex rawSimplex01 = .ok simplex01 := by
  unfold decodeSimplex simplex01
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex01_decoded

#check (900372 : Nat)
theorem simplex02_lookup_simplex_id :
    rawSimplex02.getObjVal? "simplex_id" = .ok (.number (String.ofList ['2'])) := by
  rfl

attribute [local simp] simplex02_lookup_simplex_id

#check (900373 : Nat)
theorem simplex02_lookup_vertex_ids :
    rawSimplex02.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex02_lookup_vertex_ids

#check (900374 : Nat)
theorem simplex02_lookup_physical_volume :
    rawSimplex02.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '6', '7', '6', '5', '8', '7', '4', '9', '9', '6', '2', '1', '7', '1', '8', '6', '9', '6', '7', '1', '7', '5', '3', '1', '1', '8', '7', '2', '4', '3', '/', '8', '6', '8', '6', '9', '8', '4', '4', '0', '8', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex02_lookup_physical_volume

#check (900375 : Nat)
theorem simplex02_lookup_mean_gap :
    rawSimplex02.getObjVal? "mean_gap" = .ok (.str (String.ofList ['2', '3', '4', '3', '1', '/', '6', '8', '6', '2', '5', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex02_lookup_mean_gap

#check (900376 : Nat)
theorem simplex02_lookup_factor_maxima :
    rawSimplex02.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '6', '8', '6', '3', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '0', '7', '8', '1', '3', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '8', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex02_lookup_factor_maxima

#check (900377 : Nat)
theorem simplex02_lookup_gap_weighted_means :
    rawSimplex02.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['3', '5', '6', '4', '1', '2', '7', '/', '4', '2', '8', '9', '0', '6', '2', '5']), .str (String.ofList ['5', '7', '4', '4', '7', '7', '9', '/', '6', '8', '6', '2', '5', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '0', '8', '0', '4', '3', '7', '1', '/', '8', '2', '3', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '5', '4', '6', '5', '0', '1', '9', '/', '1', '0', '6', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '0', '6', '7', '7', '8', '9', '3', '/', '3', '2', '0', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '7', '7', '8', '7', '6', '8', '1', '/', '5', '4', '9', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '8', '4', '2', '3', '8', '7', '/', '1', '0', '9', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '4', '6', '2', '0', '3', '1', '/', '2', '7', '4', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '3', '8', '3', '6', '0', '1', '/', '6', '8', '6', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '5', '5', '0', '8', '1', '4', '1', '/', '8', '2', '3', '5', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex02_lookup_gap_weighted_means

#check (900378 : Nat)
theorem simplex02_lookup_max_bound :
    rawSimplex02.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '9', '8', '4', '9', '8', '8', '4', '4', '6', '6', '9', '6', '5', '0', '0', '3', '7', '8', '6', '3', '8', '6', '1', '0', '9', '6', '8', '0', '8', '4', '4', '6', '5', '7', '1', '9', '2', '3', '3', '7', '4', '0', '8', '0', '0', '0', '0', '/', '5', '5', '1', '2', '4', '4', '0', '9', '0', '8', '3', '4', '2', '7', '0', '7', '1', '6', '9', '6', '7', '8', '5', '5', '9', '3', '7', '7', '4', '6', '0', '7', '0', '7', '5', '4', '0', '8', '0', '0', '5', '0', '7', '7', '3', '2', '2', '1', '0', '5', '3', '7', '6', '2', '1', '6', '4', '1', '4', '6', '8', '3', '1', '4', '7'])) := by
  rfl

attribute [local simp] simplex02_lookup_max_bound

#check (900379 : Nat)
theorem simplex02_lookup_jensen_bound :
    rawSimplex02.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '4', '2', '9', '7', '2', '3', '4', '2', '1', '8', '0', '3', '7', '0', '6', '1', '4', '7', '8', '9', '2', '7', '5', '4', '7', '7', '2', '0', '2', '6', '0', '9', '5', '7', '2', '4', '2', '3', '0', '3', '1', '5', '1', '0', '8', '4', '0', '9', '7', '1', '7', '9', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '/', '1', '5', '3', '3', '2', '8', '2', '9', '8', '9', '5', '1', '1', '3', '9', '3', '6', '9', '9', '9', '6', '7', '2', '3', '2', '5', '5', '4', '9', '4', '5', '0', '1', '2', '7', '3', '4', '1', '8', '0', '8', '6', '6', '9', '9', '3', '4', '6', '1', '5', '7', '1', '3', '6', '6', '5', '3', '2', '7', '8', '3', '4', '2', '1', '5', '9', '9', '8', '9', '2', '5', '0', '8', '9', '8', '3', '5', '4', '7', '9'])) := by
  rfl

attribute [local simp] simplex02_lookup_jensen_bound

#check (900380 : Nat)
theorem simplex02_lookup_max_floor_Q96 :
    rawSimplex02.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['2', '8', '5', '2', '9', '4', '6', '4', '5', '0', '7', '4'])) := by
  rfl

attribute [local simp] simplex02_lookup_max_floor_Q96

#check (900381 : Nat)
theorem simplex02_lookup_jensen_floor_Q96 :
    rawSimplex02.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['7', '3', '8', '7', '7', '0', '0', '7', '9', '5', '4', '8'])) := by
  rfl

attribute [local simp] simplex02_lookup_jensen_floor_Q96

#check (900382 : Nat)
theorem simplex02_decoded : decodeSimplex rawSimplex02 = .ok simplex02 := by
  unfold decodeSimplex simplex02
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex02_decoded

#check (900383 : Nat)
theorem simplex03_lookup_simplex_id :
    rawSimplex03.getObjVal? "simplex_id" = .ok (.number (String.ofList ['3'])) := by
  rfl

attribute [local simp] simplex03_lookup_simplex_id

#check (900384 : Nat)
theorem simplex03_lookup_vertex_ids :
    rawSimplex03.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex03_lookup_vertex_ids

#check (900385 : Nat)
theorem simplex03_lookup_physical_volume :
    rawSimplex03.getObjVal? "physical_volume" = .ok (.str (String.ofList ['6', '7', '0', '6', '1', '3', '5', '3', '3', '5', '7', '5', '3', '7', '9', '1', '8', '9', '8', '5', '5', '5', '9', '1', '9', '0', '9', '8', '6', '1', '3', '/', '3', '4', '7', '4', '7', '9', '3', '7', '6', '3', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex03_lookup_physical_volume

#check (900386 : Nat)
theorem simplex03_lookup_mean_gap :
    rawSimplex03.getObjVal? "mean_gap" = .ok (.str (String.ofList ['2', '3', '4', '3', '1', '/', '6', '8', '6', '2', '5', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex03_lookup_mean_gap

#check (900387 : Nat)
theorem simplex03_lookup_factor_maxima :
    rawSimplex03.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '6', '8', '6', '3', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '0', '7', '8', '1', '3', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '8', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex03_lookup_factor_maxima

#check (900388 : Nat)
theorem simplex03_lookup_gap_weighted_means :
    rawSimplex03.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['3', '1', '9', '3', '4', '5', '8', '8', '9', '/', '3', '8', '4', '3', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '0', '8', '5', '3', '8', '6', '6', '9', '/', '1', '9', '2', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '9', '8', '6', '3', '4', '3', '9', '/', '1', '8', '0', '1', '4', '0', '6', '2', '5', '0']), .str (String.ofList ['1', '2', '7', '7', '0', '1', '4', '1', '9', '/', '1', '2', '8', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '0', '4', '2', '5', '8', '7', '/', '4', '2', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '4', '4', '5', '1', '4', '1', '3', '3', '/', '3', '8', '4', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '4', '4', '8', '3', '9', '1', '1', '/', '3', '8', '4', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '2', '1', '5', '4', '3', '/', '2', '4', '0', '1', '8', '7', '5', '0']), .str (String.ofList ['5', '7', '0', '7', '3', '9', '7', '3', '/', '1', '9', '2', '1', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '1', '7', '4', '2', '3', '/', '1', '8', '0', '1', '4', '0', '6', '2', '5', '0'])]) := by
  rfl

attribute [local simp] simplex03_lookup_gap_weighted_means

#check (900389 : Nat)
theorem simplex03_lookup_max_bound :
    rawSimplex03.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '9', '8', '4', '9', '2', '4', '9', '0', '9', '4', '4', '5', '2', '0', '8', '3', '9', '8', '9', '8', '4', '1', '3', '7', '0', '2', '5', '0', '9', '3', '2', '9', '7', '4', '6', '5', '6', '6', '8', '4', '0', '3', '2', '0', '0', '0', '0', '/', '5', '5', '1', '2', '4', '4', '0', '9', '0', '8', '3', '4', '2', '7', '0', '7', '1', '6', '9', '6', '7', '8', '5', '5', '9', '3', '7', '7', '4', '6', '0', '7', '0', '7', '5', '4', '0', '8', '0', '0', '5', '0', '7', '7', '3', '2', '2', '1', '0', '5', '3', '7', '6', '2', '1', '6', '4', '1', '4', '6', '8', '3', '1', '4', '7'])) := by
  rfl

attribute [local simp] simplex03_lookup_max_bound

#check (900390 : Nat)
theorem simplex03_lookup_jensen_bound :
    rawSimplex03.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '5', '8', '0', '4', '0', '4', '0', '6', '3', '7', '1', '9', '8', '7', '0', '9', '8', '4', '7', '7', '4', '2', '1', '5', '8', '0', '6', '5', '9', '0', '7', '4', '3', '2', '2', '9', '4', '6', '4', '0', '8', '2', '2', '4', '7', '1', '5', '0', '0', '6', '9', '3', '2', '1', '9', '9', '2', '1', '8', '7', '5', '0', '/', '1', '6', '9', '4', '5', '0', '9', '4', '2', '1', '6', '0', '7', '7', '9', '3', '4', '3', '3', '9', '0', '7', '4', '5', '6', '6', '7', '9', '2', '9', '5', '3', '2', '1', '0', '3', '6', '0', '2', '0', '3', '0', '2', '7', '7', '0', '9', '3', '1', '2', '7', '7', '4', '5', '9', '9', '8', '5', '9', '2', '4', '5', '6', '8', '4', '5', '1', '3', '7', '1', '5', '2', '8', '7', '7', '6', '6', '6', '3', '3'])) := by
  rfl

attribute [local simp] simplex03_lookup_jensen_bound

#check (900391 : Nat)
theorem simplex03_lookup_max_floor_Q96 :
    rawSimplex03.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['2', '8', '5', '2', '8', '5', '5', '1', '3', '1', '1', '2'])) := by
  rfl

attribute [local simp] simplex03_lookup_max_floor_Q96

#check (900392 : Nat)
theorem simplex03_lookup_jensen_floor_Q96 :
    rawSimplex03.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['7', '3', '8', '9', '3', '0', '7', '3', '9', '4', '9', '2'])) := by
  rfl

attribute [local simp] simplex03_lookup_jensen_floor_Q96

#check (900393 : Nat)
theorem simplex03_decoded : decodeSimplex rawSimplex03 = .ok simplex03 := by
  unfold decodeSimplex simplex03
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex03_decoded

#check (900394 : Nat)
theorem simplex04_lookup_simplex_id :
    rawSimplex04.getObjVal? "simplex_id" = .ok (.number (String.ofList ['4'])) := by
  rfl

attribute [local simp] simplex04_lookup_simplex_id

#check (900395 : Nat)
theorem simplex04_lookup_vertex_ids :
    rawSimplex04.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['9']), .number (String.ofList ['8']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex04_lookup_vertex_ids

#check (900396 : Nat)
theorem simplex04_lookup_physical_volume :
    rawSimplex04.getObjVal? "physical_volume" = .ok (.str (String.ofList ['2', '3', '9', '5', '0', '8', '6', '6', '3', '0', '0', '3', '0', '1', '6', '3', '1', '6', '6', '0', '8', '5', '0', '1', '1', '2', '8', '1', '9', '3', '7', '2', '8', '9', '0', '7', '/', '4', '4', '3', '4', '4', '9', '8', '7', '0', '7', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex04_lookup_physical_volume

#check (900397 : Nat)
theorem simplex04_lookup_mean_gap :
    rawSimplex04.getObjVal? "mean_gap" = .ok (.str (String.ofList ['1', '1', '9', '9', '6', '4', '8', '9', '/', '1', '8', '3', '9', '1', '5', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex04_lookup_mean_gap

#check (900398 : Nat)
theorem simplex04_lookup_factor_maxima :
    rawSimplex04.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '8', '4', '3', '0', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '0', '7', '8', '1', '3', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '8', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex04_lookup_factor_maxima

#check (900399 : Nat)
theorem simplex04_lookup_gap_weighted_means :
    rawSimplex04.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['1', '2', '7', '5', '2', '1', '7', '0', '6', '7', '0', '1', '9', '0', '9', '2', '3', '3', '9', '/', '1', '5', '4', '4', '4', '3', '3', '9', '9', '2', '1', '0', '4', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '8', '8', '2', '7', '0', '7', '2', '9', '8', '9', '7', '1', '5', '7', '3', '7', '/', '1', '5', '4', '4', '4', '3', '3', '9', '9', '2', '1', '0', '4', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '5', '8', '3', '4', '4', '4', '7', '0', '2', '2', '0', '9', '0', '1', '6', '6', '7', '/', '2', '3', '1', '6', '6', '5', '0', '9', '8', '8', '1', '5', '6', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '9', '0', '7', '1', '8', '2', '3', '1', '2', '3', '5', '6', '2', '4', '0', '7', '/', '5', '1', '4', '8', '1', '1', '3', '3', '0', '7', '0', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '9', '8', '8', '1', '6', '0', '7', '3', '6', '6', '4', '8', '1', '4', '0', '1', '/', '5', '1', '4', '8', '1', '1', '3', '3', '0', '7', '0', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '0', '3', '0', '8', '1', '0', '7', '8', '2', '3', '2', '0', '2', '4', '9', '8', '7', '/', '3', '0', '8', '8', '8', '6', '7', '9', '8', '4', '2', '0', '9', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '4', '8', '3', '0', '9', '0', '1', '0', '7', '3', '3', '5', '7', '6', '0', '1', '/', '3', '0', '8', '8', '8', '6', '7', '9', '8', '4', '2', '0', '9', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '6', '7', '6', '4', '5', '3', '1', '2', '3', '5', '0', '5', '9', '7', '7', '/', '7', '7', '2', '2', '1', '6', '9', '9', '6', '0', '5', '2', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '7', '9', '3', '8', '9', '8', '0', '5', '2', '9', '7', '3', '9', '0', '5', '7', '/', '7', '7', '2', '2', '1', '6', '9', '9', '6', '0', '5', '2', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '0', '4', '9', '6', '4', '1', '4', '0', '6', '9', '7', '4', '9', '6', '2', '9', '/', '2', '3', '1', '6', '6', '5', '0', '9', '8', '8', '1', '5', '6', '7', '5', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex04_lookup_gap_weighted_means

#check (900400 : Nat)
theorem simplex04_lookup_max_bound :
    rawSimplex04.getObjVal? "max_bound" = .ok (.str (String.ofList ['7', '9', '3', '9', '7', '0', '5', '4', '7', '4', '3', '4', '9', '5', '5', '0', '9', '3', '3', '3', '5', '2', '0', '5', '3', '6', '3', '4', '9', '2', '6', '7', '4', '3', '5', '3', '2', '5', '5', '3', '6', '6', '6', '5', '0', '7', '5', '7', '1', '2', '0', '0', '0', '0', '0', '/', '4', '1', '2', '4', '2', '1', '3', '4', '8', '3', '8', '5', '6', '5', '6', '1', '0', '9', '9', '7', '7', '9', '9', '5', '8', '7', '2', '9', '3', '8', '0', '1', '9', '5', '8', '3', '9', '2', '5', '7', '8', '2', '1', '4', '5', '3', '1', '8', '8', '7', '8', '0', '7', '6', '8', '7', '4', '4', '1', '1', '8', '6', '3', '2', '4', '2', '0', '2', '9'])) := by
  rfl

attribute [local simp] simplex04_lookup_max_bound

#check (900401 : Nat)
theorem simplex04_lookup_jensen_bound :
    rawSimplex04.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['2', '5', '4', '3', '9', '4', '4', '6', '1', '4', '6', '7', '1', '2', '8', '3', '5', '8', '1', '1', '1', '9', '1', '6', '8', '5', '2', '3', '1', '0', '6', '2', '4', '6', '2', '5', '7', '4', '5', '7', '7', '3', '2', '2', '8', '3', '4', '8', '5', '2', '6', '2', '0', '1', '4', '6', '3', '9', '6', '1', '3', '5', '8', '1', '4', '3', '3', '0', '9', '9', '1', '6', '7', '8', '7', '7', '4', '0', '1', '8', '6', '3', '7', '9', '6', '3', '1', '9', '5', '4', '3', '2', '5', '0', '4', '4', '0', '7', '8', '1', '7', '6', '3', '5', '4', '0', '3', '9', '8', '8', '0', '9', '0', '6', '3', '6', '7', '5', '8', '6', '1', '8', '1', '8', '2', '1', '4', '1', '5', '5', '1', '5', '7', '8', '5', '1', '8', '2', '1', '6', '3', '7', '9', '6', '6', '3', '7', '4', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '0', '6', '3', '2', '6', '2', '2', '2', '5', '9', '3', '6', '6', '2', '0', '2', '0', '6', '2', '9', '9', '2', '6', '3', '1', '7', '7', '3', '2', '4', '0', '6', '6', '4', '9', '8', '9', '4', '6', '1', '2', '1', '7', '2', '1', '4', '8', '9', '1', '7', '8', '8', '9', '9', '9', '0', '1', '5', '4', '2', '3', '1', '5', '9', '1', '1', '1', '4', '2', '7', '3', '9', '4', '9', '4', '3', '8', '6', '0', '5', '2', '7', '6', '7', '0', '9', '4', '8', '7', '7', '5', '3', '6', '8', '2', '9', '1', '2', '7', '1', '4', '2', '2', '4', '0', '8', '9', '1', '0', '0', '8', '0', '2', '1', '8', '3', '7', '1', '6', '7', '8', '2', '1', '1', '2', '7', '0', '7', '3', '2', '5', '6', '6', '5', '9', '4', '1', '5', '2', '3', '3', '2', '5', '5', '5', '4', '5', '7', '8', '6', '1', '7', '1', '1', '3', '9', '3', '4', '4', '0', '5', '5', '6', '2', '4', '6', '4', '2', '2', '4', '6', '6', '9', '3'])) := by
  rfl

attribute [local simp] simplex04_lookup_jensen_bound

#check (900402 : Nat)
theorem simplex04_lookup_max_floor_Q96 :
    rawSimplex04.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['1', '5', '2', '5', '2', '5', '6', '3', '3', '8', '2', '0', '7', '1', '4', '8'])) := by
  rfl

attribute [local simp] simplex04_lookup_max_floor_Q96

#check (900403 : Nat)
theorem simplex04_lookup_jensen_floor_Q96 :
    rawSimplex04.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['3', '9', '8', '0', '6', '7', '5', '8', '6', '3', '9', '9', '1', '6', '2', '2'])) := by
  rfl

attribute [local simp] simplex04_lookup_jensen_floor_Q96

#check (900404 : Nat)
theorem simplex04_decoded : decodeSimplex rawSimplex04 = .ok simplex04 := by
  unfold decodeSimplex simplex04
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex04_decoded

#check (900405 : Nat)
theorem simplex05_lookup_simplex_id :
    rawSimplex05.getObjVal? "simplex_id" = .ok (.number (String.ofList ['5'])) := by
  rfl

attribute [local simp] simplex05_lookup_simplex_id

#check (900406 : Nat)
theorem simplex05_lookup_vertex_ids :
    rawSimplex05.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '1']), .number (String.ofList ['8']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex05_lookup_vertex_ids

#check (900407 : Nat)
theorem simplex05_lookup_physical_volume :
    rawSimplex05.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '0', '7', '2', '9', '1', '2', '9', '6', '4', '9', '4', '4', '1', '1', '9', '2', '5', '2', '3', '7', '2', '3', '0', '4', '3', '0', '8', '0', '3', '2', '5', '3', '/', '6', '1', '0', '6', '5', '2', '2', '8', '1', '0', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex05_lookup_physical_volume

#check (900408 : Nat)
theorem simplex05_lookup_mean_gap :
    rawSimplex05.getObjVal? "mean_gap" = .ok (.str (String.ofList ['9', '3', '7', '2', '1', '/', '3', '0', '1', '5', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex05_lookup_mean_gap

#check (900409 : Nat)
theorem simplex05_lookup_factor_maxima :
    rawSimplex05.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '8', '4', '3', '0', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '2', '1', '8', '8', '7', '/', '2', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '8', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex05_lookup_factor_maxima

#check (900410 : Nat)
theorem simplex05_lookup_gap_weighted_means :
    rawSimplex05.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['2', '7', '9', '3', '3', '6', '6', '3', '7', '/', '3', '3', '7', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '3', '0', '6', '5', '1', '3', '0', '9', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '1', '9', '4', '2', '2', '1', '0', '8', '7', '/', '2', '5', '3', '2', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '1', '6', '3', '4', '1', '5', '3', '/', '2', '3', '4', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '4', '6', '8', '7', '6', '9', '/', '1', '4', '0', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '1', '3', '8', '2', '4', '5', '0', '1', '/', '3', '3', '7', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '0', '5', '3', '8', '3', '1', '6', '9', '/', '1', '6', '8', '8', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '2', '0', '8', '2', '4', '0', '2', '7', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '6', '0', '7', '8', '2', '9', '2', '7', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '4', '1', '2', '9', '4', '3', '8', '1', '/', '5', '0', '6', '5', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex05_lookup_gap_weighted_means

#check (900411 : Nat)
theorem simplex05_lookup_max_bound :
    rawSimplex05.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '6', '8', '7', '0', '2', '4', '1', '6', '3', '4', '0', '9', '5', '6', '7', '2', '1', '4', '1', '8', '1', '1', '3', '4', '5', '9', '1', '9', '5', '7', '2', '6', '3', '0', '8', '9', '4', '8', '5', '7', '4', '2', '0', '8', '0', '0', '0', '0', '0', '/', '5', '6', '4', '7', '3', '8', '7', '9', '8', '9', '6', '3', '7', '9', '2', '5', '7', '4', '2', '3', '9', '6', '0', '9', '2', '4', '2', '8', '2', '7', '3', '1', '2', '6', '7', '9', '1', '3', '0', '7', '8', '2', '4', '8', '6', '3', '3', '7', '7', '7', '3', '5', '6', '9', '4', '0', '9', '3', '4', '1', '4', '3', '9', '5', '7', '6', '7'])) := by
  rfl

attribute [local simp] simplex05_lookup_max_bound

#check (900412 : Nat)
theorem simplex05_lookup_jensen_bound :
    rawSimplex05.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '0', '7', '1', '0', '3', '1', '6', '5', '9', '6', '1', '1', '3', '4', '8', '3', '3', '4', '8', '0', '5', '8', '6', '2', '8', '7', '3', '0', '5', '7', '6', '9', '2', '1', '3', '3', '9', '9', '7', '7', '0', '2', '7', '9', '8', '9', '6', '7', '1', '6', '8', '6', '7', '0', '6', '6', '8', '7', '0', '7', '5', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '8', '3', '9', '3', '0', '7', '2', '6', '5', '9', '9', '4', '2', '2', '5', '6', '4', '5', '8', '0', '4', '0', '9', '3', '2', '1', '7', '9', '8', '7', '4', '1', '3', '2', '0', '8', '3', '3', '5', '6', '5', '9', '5', '3', '9', '8', '0', '0', '6', '9', '0', '1', '7', '7', '4', '2', '9', '0', '8', '8', '6', '3', '4', '7', '3', '1', '6', '4', '1', '9', '2', '6', '8', '1', '9', '0', '1', '5', '9', '2', '6', '9', '1', '6', '5', '5', '3', '8', '1', '0', '7'])) := by
  rfl

attribute [local simp] simplex05_lookup_jensen_bound

#check (900413 : Nat)
theorem simplex05_lookup_max_floor_Q96 :
    rawSimplex05.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['2', '3', '6', '6', '7', '5', '4', '7', '6', '9', '2', '7'])) := by
  rfl

attribute [local simp] simplex05_lookup_max_floor_Q96

#check (900414 : Nat)
theorem simplex05_lookup_jensen_floor_Q96 :
    rawSimplex05.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['6', '1', '3', '1', '5', '1', '1', '4', '0', '8', '3', '8'])) := by
  rfl

attribute [local simp] simplex05_lookup_jensen_floor_Q96

#check (900415 : Nat)
theorem simplex05_decoded : decodeSimplex rawSimplex05 = .ok simplex05 := by
  unfold decodeSimplex simplex05
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex05_decoded

#check (900416 : Nat)
theorem simplex06_lookup_simplex_id :
    rawSimplex06.getObjVal? "simplex_id" = .ok (.number (String.ofList ['6'])) := by
  rfl

attribute [local simp] simplex06_lookup_simplex_id

#check (900417 : Nat)
theorem simplex06_lookup_vertex_ids :
    rawSimplex06.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['8']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex06_lookup_vertex_ids

#check (900418 : Nat)
theorem simplex06_lookup_physical_volume :
    rawSimplex06.getObjVal? "physical_volume" = .ok (.str (String.ofList ['4', '2', '9', '1', '5', '1', '4', '4', '8', '8', '8', '1', '9', '4', '1', '8', '7', '3', '8', '0', '6', '4', '3', '0', '5', '0', '6', '8', '2', '0', '5', '2', '3', '/', '2', '4', '4', '2', '6', '0', '9', '1', '2', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex06_lookup_physical_volume

#check (900419 : Nat)
theorem simplex06_lookup_mean_gap :
    rawSimplex06.getObjVal? "mean_gap" = .ok (.str (String.ofList ['9', '3', '7', '2', '1', '/', '3', '0', '1', '5', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex06_lookup_mean_gap

#check (900420 : Nat)
theorem simplex06_lookup_factor_maxima :
    rawSimplex06.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '8', '4', '3', '0', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '2', '1', '8', '8', '7', '/', '2', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '8', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '1', '8', '3', '/', '3', '7', '5', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex06_lookup_factor_maxima

#check (900421 : Nat)
theorem simplex06_lookup_gap_weighted_means :
    rawSimplex06.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['3', '4', '9', '1', '7', '1', '0', '0', '7', '3', '/', '4', '2', '2', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '3', '0', '6', '5', '5', '5', '3', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '0', '9', '7', '1', '0', '8', '4', '3', '3', '/', '1', '2', '6', '6', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '1', '6', '3', '4', '1', '5', '3', '/', '2', '3', '4', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '4', '6', '8', '7', '6', '9', '/', '1', '4', '0', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '4', '0', '1', '9', '7', '3', '0', '9', '/', '3', '3', '7', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '4', '7', '0', '3', '2', '6', '3', '/', '3', '3', '7', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '6', '0', '4', '1', '2', '7', '1', '7', '/', '4', '2', '2', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '3', '0', '3', '8', '9', '3', '5', '3', '/', '4', '2', '2', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '0', '3', '2', '3', '8', '0', '6', '3', '/', '1', '2', '6', '6', '3', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex06_lookup_gap_weighted_means

#check (900422 : Nat)
theorem simplex06_lookup_max_bound :
    rawSimplex06.getObjVal? "max_bound" = .ok (.str (String.ofList ['5', '2', '7', '1', '7', '8', '1', '7', '6', '1', '4', '3', '8', '7', '7', '3', '9', '8', '2', '6', '6', '0', '1', '9', '4', '9', '3', '0', '4', '8', '8', '2', '7', '7', '2', '1', '5', '8', '7', '0', '9', '7', '6', '0', '0', '0', '0', '0', '/', '1', '7', '6', '4', '8', '0', '4', '5', '6', '3', '3', '3', '2', '9', '9', '6', '1', '3', '5', '2', '3', '0', '8', '4', '0', '9', '3', '6', '1', '9', '2', '2', '3', '1', '7', '3', '9', '4', '2', '3', '8', '1', '0', '7', '9', '7', '8', '2', '7', '4', '3', '1', '7', '9', '9', '2', '8', '8', '2', '2', '9', '9', '4', '4', '7', '3'])) := by
  rfl

attribute [local simp] simplex06_lookup_max_bound

#check (900423 : Nat)
theorem simplex06_lookup_jensen_bound :
    rawSimplex06.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['8', '3', '6', '7', '1', '6', '7', '0', '0', '8', '5', '1', '9', '9', '6', '0', '9', '7', '6', '3', '7', '2', '4', '7', '0', '1', '5', '8', '8', '7', '7', '3', '9', '2', '3', '7', '1', '0', '1', '7', '4', '5', '4', '1', '7', '5', '7', '9', '1', '5', '8', '7', '4', '4', '8', '8', '9', '7', '6', '5', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '7', '9', '2', '8', '6', '9', '5', '0', '9', '4', '6', '2', '4', '3', '3', '9', '0', '1', '0', '5', '7', '5', '1', '0', '5', '9', '6', '9', '8', '7', '1', '4', '2', '1', '6', '1', '2', '1', '4', '4', '6', '5', '3', '0', '1', '1', '3', '4', '9', '8', '5', '2', '2', '6', '0', '7', '8', '5', '0', '2', '0', '9', '0', '7', '9', '3', '1', '3', '9', '7', '5', '3', '0', '6', '8', '8', '0', '3', '5', '4', '9', '6', '5', '8', '7', '6', '8', '3', '6', '9'])) := by
  rfl

attribute [local simp] simplex06_lookup_jensen_bound

#check (900424 : Nat)
theorem simplex06_lookup_max_floor_Q96 :
    rawSimplex06.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['2', '3', '6', '6', '6', '8', '4', '6', '2', '2', '2', '6'])) := by
  rfl

attribute [local simp] simplex06_lookup_max_floor_Q96

#check (900425 : Nat)
theorem simplex06_lookup_jensen_floor_Q96 :
    rawSimplex06.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['6', '1', '4', '2', '1', '5', '9', '5', '7', '0', '7', '5'])) := by
  rfl

attribute [local simp] simplex06_lookup_jensen_floor_Q96

#check (900426 : Nat)
theorem simplex06_decoded : decodeSimplex rawSimplex06 = .ok simplex06 := by
  unfold decodeSimplex simplex06
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex06_decoded

#check (900427 : Nat)
theorem simplex07_lookup_simplex_id :
    rawSimplex07.getObjVal? "simplex_id" = .ok (.number (String.ofList ['7'])) := by
  rfl

attribute [local simp] simplex07_lookup_simplex_id

#check (900428 : Nat)
theorem simplex07_lookup_vertex_ids :
    rawSimplex07.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex07_lookup_vertex_ids

#check (900429 : Nat)
theorem simplex07_lookup_physical_volume :
    rawSimplex07.getObjVal? "physical_volume" = .ok (.str (String.ofList ['2', '4', '0', '1', '4', '5', '4', '6', '3', '7', '6', '1', '6', '3', '8', '8', '5', '2', '8', '9', '8', '5', '6', '3', '6', '5', '6', '9', '8', '4', '7', '0', '8', '3', '1', '0', '7', '/', '1', '7', '4', '9', '9', '2', '8', '9', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex07_lookup_physical_volume

#check (900430 : Nat)
theorem simplex07_lookup_mean_gap :
    rawSimplex07.getObjVal? "mean_gap" = .ok (.str (String.ofList ['9', '3', '7', '2', '1', '/', '3', '0', '1', '5', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex07_lookup_mean_gap

#check (900431 : Nat)
theorem simplex07_lookup_factor_maxima :
    rawSimplex07.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '8', '4', '3', '0', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '2', '1', '8', '8', '7', '/', '2', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '1', '8', '5', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '1', '8', '3', '/', '3', '7', '5', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex07_lookup_factor_maxima

#check (900432 : Nat)
theorem simplex07_lookup_gap_weighted_means :
    rawSimplex07.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['6', '9', '8', '3', '4', '2', '4', '3', '6', '7', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '3', '0', '6', '5', '9', '7', '5', '1', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '3', '8', '8', '4', '2', '5', '2', '9', '/', '5', '0', '6', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '1', '6', '3', '4', '1', '5', '3', '/', '2', '3', '4', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '4', '6', '8', '7', '6', '9', '/', '1', '4', '0', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '4', '1', '7', '2', '0', '1', '0', '7', '/', '5', '6', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '5', '3', '8', '0', '9', '8', '0', '9', '/', '5', '6', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '5', '4', '9', '2', '7', '3', '3', '/', '2', '8', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '2', '1', '5', '4', '8', '9', '7', '/', '1', '6', '8', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '2', '0', '6', '4', '8', '0', '3', '4', '7', '/', '2', '5', '3', '2', '6', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex07_lookup_gap_weighted_means

#check (900433 : Nat)
theorem simplex07_lookup_max_bound :
    rawSimplex07.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '8', '4', '3', '7', '4', '6', '6', '5', '2', '9', '1', '4', '0', '3', '7', '1', '4', '0', '0', '7', '0', '9', '1', '4', '8', '2', '5', '9', '3', '3', '9', '3', '4', '3', '9', '4', '3', '3', '6', '4', '3', '6', '2', '2', '4', '0', '0', '0', '0', '0', '/', '7', '9', '0', '2', '0', '4', '8', '6', '7', '8', '6', '2', '4', '7', '7', '9', '5', '3', '1', '4', '1', '1', '5', '0', '9', '2', '7', '0', '7', '2', '5', '2', '0', '3', '8', '5', '5', '8', '0', '5', '7', '6', '9', '5', '6', '1', '5', '6', '2', '6', '4', '8', '6', '6', '5', '6', '9', '7', '1', '0', '8', '4', '6', '9'])) := by
  rfl

attribute [local simp] simplex07_lookup_max_bound

#check (900434 : Nat)
theorem simplex07_lookup_jensen_bound :
    rawSimplex07.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['5', '1', '9', '8', '4', '7', '2', '5', '2', '4', '9', '6', '9', '1', '8', '2', '9', '0', '5', '6', '5', '5', '1', '5', '1', '8', '8', '9', '1', '8', '6', '5', '0', '4', '0', '6', '0', '7', '4', '6', '9', '1', '8', '1', '7', '7', '8', '4', '0', '8', '8', '3', '2', '9', '6', '7', '6', '7', '7', '8', '9', '5', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '6', '0', '9', '0', '9', '1', '8', '1', '0', '4', '5', '8', '3', '6', '0', '8', '0', '6', '1', '4', '2', '2', '5', '7', '5', '6', '0', '9', '0', '7', '5', '5', '4', '8', '9', '6', '6', '3', '1', '3', '2', '3', '7', '9', '7', '6', '0', '0', '0', '1', '1', '4', '2', '5', '8', '0', '7', '8', '6', '7', '8', '0', '3', '9', '7', '3', '8', '0', '4', '2', '8', '9', '0', '5', '5', '0', '7', '5', '7', '4', '1', '9', '5', '2', '4', '2', '8', '9'])) := by
  rfl

attribute [local simp] simplex07_lookup_jensen_bound

#check (900435 : Nat)
theorem simplex07_lookup_max_floor_Q96 :
    rawSimplex07.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['1', '8', '4', '8', '5', '9', '2', '2', '4', '9', '8', '4', '7', '1', '1', '7'])) := by
  rfl

attribute [local simp] simplex07_lookup_max_floor_Q96

#check (900436 : Nat)
theorem simplex07_lookup_jensen_floor_Q96 :
    rawSimplex07.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['4', '7', '8', '4', '0', '7', '5', '1', '9', '7', '5', '0', '0', '6', '3', '1'])) := by
  rfl

attribute [local simp] simplex07_lookup_jensen_floor_Q96

#check (900437 : Nat)
theorem simplex07_decoded : decodeSimplex rawSimplex07 = .ok simplex07 := by
  unfold decodeSimplex simplex07
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex07_decoded

#check (900438 : Nat)
theorem simplices_mapped : rawSimplicesItems.toArray.mapM decodeSimplex = .ok simplices := by
  unfold rawSimplicesItems simplices
  simp

attribute [local simp] simplices_mapped

#check (900439 : Nat)
theorem physicalVolume_field : rationalField rawRoot "physical_volume" = .ok physicalVolume := by
  unfold rationalField physicalVolume
  simp [rawPhysicalVolume]

attribute [local simp] physicalVolume_field

#check (900440 : Nat)
theorem integralGap_field : rationalField rawRoot "integral_gap" = .ok integralGap := by
  unfold rationalField integralGap
  simp [rawIntegralGap]

attribute [local simp] integralGap_field

#check (900441 : Nat)
theorem rawRoot_decoded : decodeCell rawRoot = .ok cell00Payload := by
  unfold decodeCell cell00Payload
  simp [rawActive8, rawVertices, rawVertexValues, rawFaceLedger, rawSimplices]

attribute [local simp] rawRoot_decoded

#check (900442 : Nat)
end ImbalancedChen.P2Saving16Cell00FieldDecode
