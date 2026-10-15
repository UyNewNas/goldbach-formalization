import ImbalancedChen.Certificates.PairedV2FullCertificateDataBlock06

/-! Exhaustive natural-number endpoint sums, generated from unchanged witnesses.
The source generator is untrusted. Acceptance requires P0's Lean/kernel gates.
A strip is the largest numerical reduction: at most 191 rows. No checker is
rerun here, no Q160 value is substituted, and no native evaluator is trusted. -/


namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0


def block06 : List (List Approximation) :=
  [approximations422, approximations423, approximations424, approximations425, approximations426, approximations427, approximations428, approximations429, approximations430, approximations431, approximations432, approximations433, approximations434, approximations435, approximations436, approximations437]

theorem strip422_sums :
    (approximations422.map Approximation.lower).sum = 320585908846315 ∧
      (approximations422.map Approximation.upper).sum = 320586101046866 := by
  decide +kernel

theorem strip423_sums :
    (approximations423.map Approximation.lower).sum = 323566136217956 ∧
      (approximations423.map Approximation.upper).sum = 323566329591382 := by
  decide +kernel

theorem strip424_sums :
    (approximations424.map Approximation.lower).sum = 329684185644668 ∧
      (approximations424.map Approximation.upper).sum = 329684381610942 := by
  decide +kernel

theorem strip425_sums :
    (approximations425.map Approximation.lower).sum = 332638222514166 ∧
      (approximations425.map Approximation.upper).sum = 332638419610201 := by
  decide +kernel

theorem strip426_sums :
    (approximations426.map Approximation.lower).sum = 335582713932133 ∧
      (approximations426.map Approximation.upper).sum = 335582912142471 := by
  decide +kernel

theorem strip427_sums :
    (approximations427.map Approximation.lower).sum = 338517309300051 ∧
      (approximations427.map Approximation.upper).sum = 338517508609288 := by
  decide +kernel

theorem strip428_sums :
    (approximations428.map Approximation.lower).sum = 341442833458996 ∧
      (approximations428.map Approximation.upper).sum = 341443033852868 := by
  decide +kernel

theorem strip429_sums :
    (approximations429.map Approximation.lower).sum = 344359282020822 ∧
      (approximations429.map Approximation.upper).sum = 344359483486261 := by
  decide +kernel

theorem strip430_sums :
    (approximations430.map Approximation.lower).sum = 347266650601347 ∧
      (approximations430.map Approximation.upper).sum = 347266853125517 := by
  decide +kernel

theorem strip431_sums :
    (approximations431.map Approximation.lower).sum = 350164934818674 ∧
      (approximations431.map Approximation.upper).sum = 350165138389999 := by
  decide +kernel

theorem strip432_sums :
    (approximations432.map Approximation.lower).sum = 353054130296392 ∧
      (approximations432.map Approximation.upper).sum = 353054334901509 := by
  decide +kernel

theorem strip433_sums :
    (approximations433.map Approximation.lower).sum = 355934232659805 ∧
      (approximations433.map Approximation.upper).sum = 355934438286580 := by
  decide +kernel

theorem strip434_sums :
    (approximations434.map Approximation.lower).sum = 358805237539207 ∧
      (approximations434.map Approximation.upper).sum = 358805444175727 := by
  decide +kernel

theorem strip435_sums :
    (approximations435.map Approximation.lower).sum = 361666649080463 ∧
      (approximations435.map Approximation.upper).sum = 361666856713385 := by
  decide +kernel

theorem strip436_sums :
    (approximations436.map Approximation.lower).sum = 364518138052983 ∧
      (approximations436.map Approximation.upper).sum = 364518346668110 := by
  decide +kernel

theorem strip437_sums :
    (approximations437.map Approximation.lower).sum = 367360517333841 ∧
      (approximations437.map Approximation.upper).sum = 367360726920989 := by
  decide +kernel

theorem block06_lower :
    (block06.map (fun xs => (xs.map Approximation.lower).sum)).sum = 5525147082317819 := by
  change (approximations422.map Approximation.lower).sum + ((approximations423.map Approximation.lower).sum + ((approximations424.map Approximation.lower).sum + ((approximations425.map Approximation.lower).sum + ((approximations426.map Approximation.lower).sum + ((approximations427.map Approximation.lower).sum + ((approximations428.map Approximation.lower).sum + ((approximations429.map Approximation.lower).sum + ((approximations430.map Approximation.lower).sum + ((approximations431.map Approximation.lower).sum + ((approximations432.map Approximation.lower).sum + ((approximations433.map Approximation.lower).sum + ((approximations434.map Approximation.lower).sum + ((approximations435.map Approximation.lower).sum + ((approximations436.map Approximation.lower).sum + ((approximations437.map Approximation.lower).sum + 0))))))))))))))) = 5525147082317819
  rw [strip422_sums.1, strip423_sums.1, strip424_sums.1, strip425_sums.1, strip426_sums.1, strip427_sums.1, strip428_sums.1, strip429_sums.1, strip430_sums.1, strip431_sums.1, strip432_sums.1, strip433_sums.1, strip434_sums.1, strip435_sums.1, strip436_sums.1, strip437_sums.1]
  decide +kernel

theorem block06_upper :
    (block06.map (fun xs => (xs.map Approximation.upper).sum)).sum = 5525150309132095 := by
  change (approximations422.map Approximation.upper).sum + ((approximations423.map Approximation.upper).sum + ((approximations424.map Approximation.upper).sum + ((approximations425.map Approximation.upper).sum + ((approximations426.map Approximation.upper).sum + ((approximations427.map Approximation.upper).sum + ((approximations428.map Approximation.upper).sum + ((approximations429.map Approximation.upper).sum + ((approximations430.map Approximation.upper).sum + ((approximations431.map Approximation.upper).sum + ((approximations432.map Approximation.upper).sum + ((approximations433.map Approximation.upper).sum + ((approximations434.map Approximation.upper).sum + ((approximations435.map Approximation.upper).sum + ((approximations436.map Approximation.upper).sum + ((approximations437.map Approximation.upper).sum + 0))))))))))))))) = 5525150309132095
  rw [strip422_sums.2, strip423_sums.2, strip424_sums.2, strip425_sums.2, strip426_sums.2, strip427_sums.2, strip428_sums.2, strip429_sums.2, strip430_sums.2, strip431_sums.2, strip432_sums.2, strip433_sums.2, strip434_sums.2, strip435_sums.2, strip436_sums.2, strip437_sums.2]
  decide +kernel



/-- Each length is checked separately over its original literal list. -/
theorem strip422_length :
    approximations422.length = 512 - firstU (⟨96, by decide⟩ : Fin 186) := by
  rfl

theorem strip423_length :
    approximations423.length = 512 - firstU (⟨97, by decide⟩ : Fin 186) := by
  rfl

theorem strip424_length :
    approximations424.length = 512 - firstU (⟨98, by decide⟩ : Fin 186) := by
  rfl

theorem strip425_length :
    approximations425.length = 512 - firstU (⟨99, by decide⟩ : Fin 186) := by
  rfl

theorem strip426_length :
    approximations426.length = 512 - firstU (⟨100, by decide⟩ : Fin 186) := by
  rfl

theorem strip427_length :
    approximations427.length = 512 - firstU (⟨101, by decide⟩ : Fin 186) := by
  rfl

theorem strip428_length :
    approximations428.length = 512 - firstU (⟨102, by decide⟩ : Fin 186) := by
  rfl

theorem strip429_length :
    approximations429.length = 512 - firstU (⟨103, by decide⟩ : Fin 186) := by
  rfl

theorem strip430_length :
    approximations430.length = 512 - firstU (⟨104, by decide⟩ : Fin 186) := by
  rfl

theorem strip431_length :
    approximations431.length = 512 - firstU (⟨105, by decide⟩ : Fin 186) := by
  rfl

theorem strip432_length :
    approximations432.length = 512 - firstU (⟨106, by decide⟩ : Fin 186) := by
  rfl

theorem strip433_length :
    approximations433.length = 512 - firstU (⟨107, by decide⟩ : Fin 186) := by
  rfl

theorem strip434_length :
    approximations434.length = 512 - firstU (⟨108, by decide⟩ : Fin 186) := by
  rfl

theorem strip435_length :
    approximations435.length = 512 - firstU (⟨109, by decide⟩ : Fin 186) := by
  rfl

theorem strip436_length :
    approximations436.length = 512 - firstU (⟨110, by decide⟩ : Fin 186) := by
  rfl

theorem strip437_length :
    approximations437.length = 512 - firstU (⟨111, by decide⟩ : Fin 186) := by
  rfl

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
