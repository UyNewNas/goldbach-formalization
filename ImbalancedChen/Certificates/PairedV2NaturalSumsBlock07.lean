import ImbalancedChen.Certificates.PairedV2FullCertificateData

/-! Exhaustive natural-number endpoint sums, generated from unchanged witnesses.
The source generator is untrusted. Acceptance requires P0's Lean/kernel gates.
A strip is the largest numerical reduction: at most 191 rows. No checker is
rerun here, no Q160 value is substituted, and no native evaluator is trusted. -/


namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0


def block07 : List (List Approximation) :=
  [approximations438, approximations439, approximations440, approximations441, approximations442, approximations443, approximations444, approximations445, approximations446, approximations447, approximations448, approximations449, approximations450, approximations451, approximations452, approximations453]

theorem strip438_sums :
    (approximations438.map Approximation.lower).sum = 370193782571981 ∧
      (approximations438.map Approximation.upper).sum = 370193993119049 := by
  decide +kernel

theorem strip439_sums :
    (approximations439.map Approximation.lower).sum = 373017929420503 ∧
      (approximations439.map Approximation.upper).sum = 373018140917727 := by
  decide +kernel

theorem strip440_sums :
    (approximations440.map Approximation.lower).sum = 375832953539088 ∧
      (approximations440.map Approximation.upper).sum = 375833165974758 := by
  decide +kernel

theorem strip441_sums :
    (approximations441.map Approximation.lower).sum = 378638850594283 ∧
      (approximations441.map Approximation.upper).sum = 378639063959069 := by
  decide +kernel

theorem strip442_sums :
    (approximations442.map Approximation.lower).sum = 381435616256505 ∧
      (approximations442.map Approximation.upper).sum = 381435830539054 := by
  decide +kernel

theorem strip443_sums :
    (approximations443.map Approximation.lower).sum = 384223246204658 ∧
      (approximations443.map Approximation.upper).sum = 384223461394905 := by
  decide +kernel

theorem strip444_sums :
    (approximations444.map Approximation.lower).sum = 387001235324532 ∧
      (approximations444.map Approximation.upper).sum = 387001451410975 := by
  decide +kernel

theorem strip445_sums :
    (approximations445.map Approximation.lower).sum = 389769275688005 ∧
      (approximations445.map Approximation.upper).sum = 389769492659435 := by
  decide +kernel

theorem strip446_sums :
    (approximations446.map Approximation.lower).sum = 392528168281263 ∧
      (approximations446.map Approximation.upper).sum = 392528386128214 := by
  decide +kernel

theorem strip447_sums :
    (approximations447.map Approximation.lower).sum = 395277908811493 ∧
      (approximations447.map Approximation.upper).sum = 395278127523529 := by
  decide +kernel

theorem strip448_sums :
    (approximations448.map Approximation.lower).sum = 398018492990135 ∧
      (approximations448.map Approximation.upper).sum = 398018712559253 := by
  decide +kernel

theorem strip449_sums :
    (approximations449.map Approximation.lower).sum = 400749916541163 ∧
      (approximations449.map Approximation.upper).sum = 400750136957257 := by
  decide +kernel

theorem strip450_sums :
    (approximations450.map Approximation.lower).sum = 403472175191050 ∧
      (approximations450.map Approximation.upper).sum = 403472396446471 := by
  decide +kernel

theorem strip451_sums :
    (approximations451.map Approximation.lower).sum = 406185264681776 ∧
      (approximations451.map Approximation.upper).sum = 406185486766736 := by
  decide +kernel

theorem strip452_sums :
    (approximations452.map Approximation.lower).sum = 411799027629727 ∧
      (approximations452.map Approximation.upper).sum = 411799251647529 := by
  decide +kernel

theorem strip453_sums :
    (approximations453.map Approximation.lower).sum = 414484924086775 ∧
      (approximations453.map Approximation.upper).sum = 414485148908472 := by
  decide +kernel

theorem block07_lower :
    (block07.map (fun xs => (xs.map Approximation.lower).sum)).sum = 6262628767812937 := by
  change (approximations438.map Approximation.lower).sum + ((approximations439.map Approximation.lower).sum + ((approximations440.map Approximation.lower).sum + ((approximations441.map Approximation.lower).sum + ((approximations442.map Approximation.lower).sum + ((approximations443.map Approximation.lower).sum + ((approximations444.map Approximation.lower).sum + ((approximations445.map Approximation.lower).sum + ((approximations446.map Approximation.lower).sum + ((approximations447.map Approximation.lower).sum + ((approximations448.map Approximation.lower).sum + ((approximations449.map Approximation.lower).sum + ((approximations450.map Approximation.lower).sum + ((approximations451.map Approximation.lower).sum + ((approximations452.map Approximation.lower).sum + ((approximations453.map Approximation.lower).sum + 0))))))))))))))) = 6262628767812937
  rw [strip438_sums.1, strip439_sums.1, strip440_sums.1, strip441_sums.1, strip442_sums.1, strip443_sums.1, strip444_sums.1, strip445_sums.1, strip446_sums.1, strip447_sums.1, strip448_sums.1, strip449_sums.1, strip450_sums.1, strip451_sums.1, strip452_sums.1, strip453_sums.1]
  decide +kernel

theorem block07_upper :
    (block07.map (fun xs => (xs.map Approximation.upper).sum)).sum = 6262632246912433 := by
  change (approximations438.map Approximation.upper).sum + ((approximations439.map Approximation.upper).sum + ((approximations440.map Approximation.upper).sum + ((approximations441.map Approximation.upper).sum + ((approximations442.map Approximation.upper).sum + ((approximations443.map Approximation.upper).sum + ((approximations444.map Approximation.upper).sum + ((approximations445.map Approximation.upper).sum + ((approximations446.map Approximation.upper).sum + ((approximations447.map Approximation.upper).sum + ((approximations448.map Approximation.upper).sum + ((approximations449.map Approximation.upper).sum + ((approximations450.map Approximation.upper).sum + ((approximations451.map Approximation.upper).sum + ((approximations452.map Approximation.upper).sum + ((approximations453.map Approximation.upper).sum + 0))))))))))))))) = 6262632246912433
  rw [strip438_sums.2, strip439_sums.2, strip440_sums.2, strip441_sums.2, strip442_sums.2, strip443_sums.2, strip444_sums.2, strip445_sums.2, strip446_sums.2, strip447_sums.2, strip448_sums.2, strip449_sums.2, strip450_sums.2, strip451_sums.2, strip452_sums.2, strip453_sums.2]
  decide +kernel


end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
