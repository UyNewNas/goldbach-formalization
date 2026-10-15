import ImbalancedChen.Certificates.PairedV2FullCertificateData

/-! Exhaustive natural-number endpoint sums, generated from unchanged witnesses.
The source generator is untrusted. Acceptance requires P0's Lean/kernel gates.
A strip is the largest numerical reduction: at most 191 rows. No checker is
rerun here, no Q160 value is substituted, and no native evaluator is trusted. -/


namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0


def block05 : List (List Approximation) :=
  [approximations406, approximations407, approximations408, approximations409, approximations410, approximations411, approximations412, approximations413, approximations414, approximations415, approximations416, approximations417, approximations418, approximations419, approximations420, approximations421]

theorem strip406_sums :
    (approximations406.map Approximation.lower).sum = 271659369011242 ∧
      (approximations406.map Approximation.upper).sum = 271659540171708 := by
  decide +kernel

theorem strip407_sums :
    (approximations407.map Approximation.lower).sum = 274786378297378 ∧
      (approximations407.map Approximation.upper).sum = 274786550913117 := by
  decide +kernel

theorem strip408_sums :
    (approximations408.map Approximation.lower).sum = 277903946672340 ∧
      (approximations408.map Approximation.upper).sum = 277904120722240 := by
  decide +kernel

theorem strip409_sums :
    (approximations409.map Approximation.lower).sum = 281011680590805 ∧
      (approximations409.map Approximation.upper).sum = 281011856052755 := by
  decide +kernel

theorem strip410_sums :
    (approximations410.map Approximation.lower).sum = 284110429028423 ∧
      (approximations410.map Approximation.upper).sum = 284110605883654 := by
  decide +kernel

theorem strip411_sums :
    (approximations411.map Approximation.lower).sum = 287200187581007 ∧
      (approximations411.map Approximation.upper).sum = 287200365810239 := by
  decide +kernel

theorem strip412_sums :
    (approximations412.map Approximation.lower).sum = 290280951840851 ∧
      (approximations412.map Approximation.upper).sum = 290281131426774 := by
  decide +kernel

theorem strip413_sums :
    (approximations413.map Approximation.lower).sum = 293352717400161 ∧
      (approximations413.map Approximation.upper).sum = 293352898325807 := by
  decide +kernel

theorem strip414_sums :
    (approximations414.map Approximation.lower).sum = 296415479852984 ∧
      (approximations414.map Approximation.upper).sum = 296415662099176 := by
  decide +kernel

theorem strip415_sums :
    (approximations415.map Approximation.lower).sum = 299469234789498 ∧
      (approximations415.map Approximation.upper).sum = 299469418339898 := by
  decide +kernel

theorem strip416_sums :
    (approximations416.map Approximation.lower).sum = 302513977801303 ∧
      (approximations416.map Approximation.upper).sum = 302514162639034 := by
  decide +kernel

theorem strip417_sums :
    (approximations417.map Approximation.lower).sum = 305549231714249 ∧
      (approximations417.map Approximation.upper).sum = 305549417821111 := by
  decide +kernel

theorem strip418_sums :
    (approximations418.map Approximation.lower).sum = 308574624488972 ∧
      (approximations418.map Approximation.upper).sum = 308574811845781 := by
  decide +kernel

theorem strip419_sums :
    (approximations419.map Approximation.lower).sum = 311590992996407 ∧
      (approximations419.map Approximation.upper).sum = 311591181588073 := by
  decide +kernel

theorem strip420_sums :
    (approximations420.map Approximation.lower).sum = 314598332829987 ∧
      (approximations420.map Approximation.upper).sum = 314598522639928 := by
  decide +kernel

theorem strip421_sums :
    (approximations421.map Approximation.lower).sum = 317596639582158 ∧
      (approximations421.map Approximation.upper).sum = 317596830594969 := by
  decide +kernel

theorem block05_lower :
    (block05.map (fun xs => (xs.map Approximation.lower).sum)).sum = 4716614174477765 := by
  change (approximations406.map Approximation.lower).sum + ((approximations407.map Approximation.lower).sum + ((approximations408.map Approximation.lower).sum + ((approximations409.map Approximation.lower).sum + ((approximations410.map Approximation.lower).sum + ((approximations411.map Approximation.lower).sum + ((approximations412.map Approximation.lower).sum + ((approximations413.map Approximation.lower).sum + ((approximations414.map Approximation.lower).sum + ((approximations415.map Approximation.lower).sum + ((approximations416.map Approximation.lower).sum + ((approximations417.map Approximation.lower).sum + ((approximations418.map Approximation.lower).sum + ((approximations419.map Approximation.lower).sum + ((approximations420.map Approximation.lower).sum + ((approximations421.map Approximation.lower).sum + 0))))))))))))))) = 4716614174477765
  rw [strip406_sums.1, strip407_sums.1, strip408_sums.1, strip409_sums.1, strip410_sums.1, strip411_sums.1, strip412_sums.1, strip413_sums.1, strip414_sums.1, strip415_sums.1, strip416_sums.1, strip417_sums.1, strip418_sums.1, strip419_sums.1, strip420_sums.1, strip421_sums.1]
  decide +kernel

theorem block05_upper :
    (block05.map (fun xs => (xs.map Approximation.upper).sum)).sum = 4716617076874264 := by
  change (approximations406.map Approximation.upper).sum + ((approximations407.map Approximation.upper).sum + ((approximations408.map Approximation.upper).sum + ((approximations409.map Approximation.upper).sum + ((approximations410.map Approximation.upper).sum + ((approximations411.map Approximation.upper).sum + ((approximations412.map Approximation.upper).sum + ((approximations413.map Approximation.upper).sum + ((approximations414.map Approximation.upper).sum + ((approximations415.map Approximation.upper).sum + ((approximations416.map Approximation.upper).sum + ((approximations417.map Approximation.upper).sum + ((approximations418.map Approximation.upper).sum + ((approximations419.map Approximation.upper).sum + ((approximations420.map Approximation.upper).sum + ((approximations421.map Approximation.upper).sum + 0))))))))))))))) = 4716617076874264
  rw [strip406_sums.2, strip407_sums.2, strip408_sums.2, strip409_sums.2, strip410_sums.2, strip411_sums.2, strip412_sums.2, strip413_sums.2, strip414_sums.2, strip415_sums.2, strip416_sums.2, strip417_sums.2, strip418_sums.2, strip419_sums.2, strip420_sums.2, strip421_sums.2]
  decide +kernel


end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
