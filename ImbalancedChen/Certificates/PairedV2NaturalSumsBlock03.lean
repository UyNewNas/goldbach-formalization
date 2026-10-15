import ImbalancedChen.Certificates.PairedV2FullCertificateData

/-! Exhaustive natural-number endpoint sums, generated from unchanged witnesses.
The source generator is untrusted. Acceptance requires P0's Lean/kernel gates.
A strip is the largest numerical reduction: at most 191 rows. No checker is
rerun here, no Q160 value is substituted, and no native evaluator is trusted. -/


namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0


def block03 : List (List Approximation) :=
  [approximations374, approximations375, approximations376, approximations377, approximations378, approximations379, approximations380, approximations381, approximations382, approximations383, approximations384, approximations385, approximations386, approximations387, approximations388, approximations389]

theorem strip374_sums :
    (approximations374.map Approximation.lower).sum = 166821721106364 ∧
      (approximations374.map Approximation.upper).sum = 166821832873931 := by
  decide +kernel

theorem strip375_sums :
    (approximations375.map Approximation.lower).sum = 170234634921781 ∧
      (approximations375.map Approximation.upper).sum = 170234748984953 := by
  decide +kernel

theorem strip376_sums :
    (approximations376.map Approximation.lower).sum = 173641785398250 ∧
      (approximations376.map Approximation.upper).sum = 173641901735457 := by
  decide +kernel

theorem strip377_sums :
    (approximations377.map Approximation.lower).sum = 177040090400235 ∧
      (approximations377.map Approximation.upper).sum = 177040208977974 := by
  decide +kernel

theorem strip378_sums :
    (approximations378.map Approximation.lower).sum = 180429545656784 ∧
      (approximations378.map Approximation.upper).sum = 180429666442588 := by
  decide +kernel

theorem strip379_sums :
    (approximations379.map Approximation.lower).sum = 183810146890835 ∧
      (approximations379.map Approximation.upper).sum = 183810269853253 := by
  decide +kernel

theorem strip380_sums :
    (approximations380.map Approximation.lower).sum = 187181889819386 ∧
      (approximations380.map Approximation.upper).sum = 187182014926486 := by
  decide +kernel

theorem strip381_sums :
    (approximations381.map Approximation.lower).sum = 190544335272022 ∧
      (approximations381.map Approximation.upper).sum = 190544462491814 := by
  decide +kernel

theorem strip382_sums :
    (approximations382.map Approximation.lower).sum = 193897024730482 ∧
      (approximations382.map Approximation.upper).sum = 193897154028755 := by
  decide +kernel

theorem strip383_sums :
    (approximations383.map Approximation.lower).sum = 197240843896052 ∧
      (approximations383.map Approximation.upper).sum = 197240975242903 := by
  decide +kernel

theorem strip384_sums :
    (approximations384.map Approximation.lower).sum = 200575788459400 ∧
      (approximations384.map Approximation.upper).sum = 200575921825988 := by
  decide +kernel

theorem strip385_sums :
    (approximations385.map Approximation.lower).sum = 203901854107705 ∧
      (approximations385.map Approximation.upper).sum = 203901989465119 := by
  decide +kernel

theorem strip386_sums :
    (approximations386.map Approximation.lower).sum = 207219036521480 ∧
      (approximations386.map Approximation.upper).sum = 207219173840705 := by
  decide +kernel

theorem strip387_sums :
    (approximations387.map Approximation.lower).sum = 210527331375213 ∧
      (approximations387.map Approximation.upper).sum = 210527470628877 := by
  decide +kernel

theorem strip388_sums :
    (approximations388.map Approximation.lower).sum = 213826734339300 ∧
      (approximations388.map Approximation.upper).sum = 213826875499905 := by
  decide +kernel

theorem strip389_sums :
    (approximations389.map Approximation.lower).sum = 217117241079048 ∧
      (approximations389.map Approximation.upper).sum = 217117384118930 := by
  decide +kernel

theorem block03_lower :
    (block03.map (fun xs => (xs.map Approximation.lower).sum)).sum = 3074010003974337 := by
  change (approximations374.map Approximation.lower).sum + ((approximations375.map Approximation.lower).sum + ((approximations376.map Approximation.lower).sum + ((approximations377.map Approximation.lower).sum + ((approximations378.map Approximation.lower).sum + ((approximations379.map Approximation.lower).sum + ((approximations380.map Approximation.lower).sum + ((approximations381.map Approximation.lower).sum + ((approximations382.map Approximation.lower).sum + ((approximations383.map Approximation.lower).sum + ((approximations384.map Approximation.lower).sum + ((approximations385.map Approximation.lower).sum + ((approximations386.map Approximation.lower).sum + ((approximations387.map Approximation.lower).sum + ((approximations388.map Approximation.lower).sum + ((approximations389.map Approximation.lower).sum + 0))))))))))))))) = 3074010003974337
  rw [strip374_sums.1, strip375_sums.1, strip376_sums.1, strip377_sums.1, strip378_sums.1, strip379_sums.1, strip380_sums.1, strip381_sums.1, strip382_sums.1, strip383_sums.1, strip384_sums.1, strip385_sums.1, strip386_sums.1, strip387_sums.1, strip388_sums.1, strip389_sums.1]
  decide +kernel

theorem block03_upper :
    (block03.map (fun xs => (xs.map Approximation.upper).sum)).sum = 3074012050937638 := by
  change (approximations374.map Approximation.upper).sum + ((approximations375.map Approximation.upper).sum + ((approximations376.map Approximation.upper).sum + ((approximations377.map Approximation.upper).sum + ((approximations378.map Approximation.upper).sum + ((approximations379.map Approximation.upper).sum + ((approximations380.map Approximation.upper).sum + ((approximations381.map Approximation.upper).sum + ((approximations382.map Approximation.upper).sum + ((approximations383.map Approximation.upper).sum + ((approximations384.map Approximation.upper).sum + ((approximations385.map Approximation.upper).sum + ((approximations386.map Approximation.upper).sum + ((approximations387.map Approximation.upper).sum + ((approximations388.map Approximation.upper).sum + ((approximations389.map Approximation.upper).sum + 0))))))))))))))) = 3074012050937638
  rw [strip374_sums.2, strip375_sums.2, strip376_sums.2, strip377_sums.2, strip378_sums.2, strip379_sums.2, strip380_sums.2, strip381_sums.2, strip382_sums.2, strip383_sums.2, strip384_sums.2, strip385_sums.2, strip386_sums.2, strip387_sums.2, strip388_sums.2, strip389_sums.2]
  decide +kernel


end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
