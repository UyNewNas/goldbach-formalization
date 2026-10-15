import ImbalancedChen.Certificates.PairedV2FullCertificateData

/-! Exhaustive natural-number endpoint sums, generated from unchanged witnesses.
The source generator is untrusted. Acceptance requires P0's Lean/kernel gates.
A strip is the largest numerical reduction: at most 191 rows. No checker is
rerun here, no Q160 value is substituted, and no native evaluator is trusted. -/


namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0


def block04 : List (List Approximation) :=
  [approximations390, approximations391, approximations392, approximations393, approximations394, approximations395, approximations396, approximations397, approximations398, approximations399, approximations400, approximations401, approximations402, approximations403, approximations404, approximations405]

theorem strip390_sums :
    (approximations390.map Approximation.lower).sum = 220398402846965 ∧
      (approximations390.map Approximation.upper).sum = 220398547737929 := by
  decide +kernel

theorem strip391_sums :
    (approximations391.map Approximation.lower).sum = 223669782858730 ∧
      (approximations391.map Approximation.upper).sum = 223669929572077 := by
  decide +kernel

theorem strip392_sums :
    (approximations392.map Approximation.lower).sum = 226932254507356 ∧
      (approximations392.map Approximation.upper).sum = 226932403017399 := by
  decide +kernel

theorem strip393_sums :
    (approximations393.map Approximation.lower).sum = 230185813438398 ∧
      (approximations393.map Approximation.upper).sum = 230185963719887 := by
  decide +kernel

theorem strip394_sums :
    (approximations394.map Approximation.lower).sum = 233430455293790 ∧
      (approximations394.map Approximation.upper).sum = 233430607321226 := by
  decide +kernel

theorem strip395_sums :
    (approximations395.map Approximation.lower).sum = 236666175709964 ∧
      (approximations395.map Approximation.upper).sum = 236666329458932 := by
  decide +kernel

theorem strip396_sums :
    (approximations396.map Approximation.lower).sum = 239892970320033 ∧
      (approximations396.map Approximation.upper).sum = 239893125767193 := by
  decide +kernel

theorem strip397_sums :
    (approximations397.map Approximation.lower).sum = 243110834754645 ∧
      (approximations397.map Approximation.upper).sum = 243110991876417 := by
  decide +kernel

theorem strip398_sums :
    (approximations398.map Approximation.lower).sum = 246319764639458 ∧
      (approximations398.map Approximation.upper).sum = 246319923412657 := by
  decide +kernel

theorem strip399_sums :
    (approximations399.map Approximation.lower).sum = 249519301699674 ∧
      (approximations399.map Approximation.upper).sum = 249519462099175 := by
  decide +kernel

theorem strip400_sums :
    (approximations400.map Approximation.lower).sum = 252709030808433 ∧
      (approximations400.map Approximation.upper).sum = 252709192809468 := by
  decide +kernel

theorem strip401_sums :
    (approximations401.map Approximation.lower).sum = 255889813116988 ∧
      (approximations401.map Approximation.upper).sum = 255889976697555 := by
  decide +kernel

theorem strip402_sums :
    (approximations402.map Approximation.lower).sum = 259061644237976 ∧
      (approximations402.map Approximation.upper).sum = 259061809376445 := by
  decide +kernel

theorem strip403_sums :
    (approximations403.map Approximation.lower).sum = 262224519781971 ∧
      (approximations403.map Approximation.upper).sum = 262224686456355 := by
  decide +kernel

theorem strip404_sums :
    (approximations404.map Approximation.lower).sum = 265378435355501 ∧
      (approximations404.map Approximation.upper).sum = 265378603545645 := by
  decide +kernel

theorem strip405_sums :
    (approximations405.map Approximation.lower).sum = 268523386564131 ∧
      (approximations405.map Approximation.upper).sum = 268523556249521 := by
  decide +kernel

theorem block04_lower :
    (block04.map (fun xs => (xs.map Approximation.lower).sum)).sum = 3913912585934013 := by
  change (approximations390.map Approximation.lower).sum + ((approximations391.map Approximation.lower).sum + ((approximations392.map Approximation.lower).sum + ((approximations393.map Approximation.lower).sum + ((approximations394.map Approximation.lower).sum + ((approximations395.map Approximation.lower).sum + ((approximations396.map Approximation.lower).sum + ((approximations397.map Approximation.lower).sum + ((approximations398.map Approximation.lower).sum + ((approximations399.map Approximation.lower).sum + ((approximations400.map Approximation.lower).sum + ((approximations401.map Approximation.lower).sum + ((approximations402.map Approximation.lower).sum + ((approximations403.map Approximation.lower).sum + ((approximations404.map Approximation.lower).sum + ((approximations405.map Approximation.lower).sum + 0))))))))))))))) = 3913912585934013
  rw [strip390_sums.1, strip391_sums.1, strip392_sums.1, strip393_sums.1, strip394_sums.1, strip395_sums.1, strip396_sums.1, strip397_sums.1, strip398_sums.1, strip399_sums.1, strip400_sums.1, strip401_sums.1, strip402_sums.1, strip403_sums.1, strip404_sums.1, strip405_sums.1]
  decide +kernel

theorem block04_upper :
    (block04.map (fun xs => (xs.map Approximation.upper).sum)).sum = 3913915109117881 := by
  change (approximations390.map Approximation.upper).sum + ((approximations391.map Approximation.upper).sum + ((approximations392.map Approximation.upper).sum + ((approximations393.map Approximation.upper).sum + ((approximations394.map Approximation.upper).sum + ((approximations395.map Approximation.upper).sum + ((approximations396.map Approximation.upper).sum + ((approximations397.map Approximation.upper).sum + ((approximations398.map Approximation.upper).sum + ((approximations399.map Approximation.upper).sum + ((approximations400.map Approximation.upper).sum + ((approximations401.map Approximation.upper).sum + ((approximations402.map Approximation.upper).sum + ((approximations403.map Approximation.upper).sum + ((approximations404.map Approximation.upper).sum + ((approximations405.map Approximation.upper).sum + 0))))))))))))))) = 3913915109117881
  rw [strip390_sums.2, strip391_sums.2, strip392_sums.2, strip393_sums.2, strip394_sums.2, strip395_sums.2, strip396_sums.2, strip397_sums.2, strip398_sums.2, strip399_sums.2, strip400_sums.2, strip401_sums.2, strip402_sums.2, strip403_sums.2, strip404_sums.2, strip405_sums.2]
  decide +kernel


end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
