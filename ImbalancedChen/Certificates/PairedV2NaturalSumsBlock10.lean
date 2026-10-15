import ImbalancedChen.Certificates.PairedV2FullCertificateDataBlock10

/-! Exhaustive natural-number endpoint sums, generated from unchanged witnesses.
The source generator is untrusted. Acceptance requires P0's Lean/kernel gates.
A strip is the largest numerical reduction: at most 191 rows. No checker is
rerun here, no Q160 value is substituted, and no native evaluator is trusted. -/


namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0


def block10 : List (List Approximation) :=
  [approximations486, approximations487, approximations488, approximations489, approximations490, approximations491, approximations492, approximations493, approximations494, approximations495, approximations496, approximations497, approximations498, approximations499, approximations500, approximations501]

theorem strip486_sums :
    (approximations486.map Approximation.lower).sum = 500468477056828 ∧
      (approximations486.map Approximation.upper).sum = 500468725319977 := by
  decide +kernel

theorem strip487_sums :
    (approximations487.map Approximation.lower).sum = 502826411597686 ∧
      (approximations487.map Approximation.upper).sum = 502826660443591 := by
  decide +kernel

theorem strip488_sums :
    (approximations488.map Approximation.lower).sum = 505175017062625 ∧
      (approximations488.map Approximation.upper).sum = 505175266487173 := by
  decide +kernel

theorem strip489_sums :
    (approximations489.map Approximation.lower).sum = 510094635970573 ∧
      (approximations489.map Approximation.upper).sum = 510094886842721 := by
  decide +kernel

theorem strip490_sums :
    (approximations490.map Approximation.lower).sum = 512414643539482 ∧
      (approximations490.map Approximation.upper).sum = 512414894974057 := by
  decide +kernel

theorem strip491_sums :
    (approximations491.map Approximation.lower).sum = 514725304825685 ∧
      (approximations491.map Approximation.upper).sum = 514725556818852 := by
  decide +kernel

theorem strip492_sums :
    (approximations492.map Approximation.lower).sum = 517026616290492 ∧
      (approximations492.map Approximation.upper).sum = 517026868838454 := by
  decide +kernel

theorem strip493_sums :
    (approximations493.map Approximation.lower).sum = 519318574418729 ∧
      (approximations493.map Approximation.upper).sum = 519318827519309 := by
  decide +kernel

theorem strip494_sums :
    (approximations494.map Approximation.lower).sum = 521601175722282 ∧
      (approximations494.map Approximation.upper).sum = 521601429370307 := by
  decide +kernel

theorem strip495_sums :
    (approximations495.map Approximation.lower).sum = 523874416740614 ∧
      (approximations495.map Approximation.upper).sum = 523874670932487 := by
  decide +kernel

theorem strip496_sums :
    (approximations496.map Approximation.lower).sum = 526138294036543 ∧
      (approximations496.map Approximation.upper).sum = 526138548768747 := by
  decide +kernel

theorem strip497_sums :
    (approximations497.map Approximation.lower).sum = 528392804201371 ∧
      (approximations497.map Approximation.upper).sum = 528393059472005 := by
  decide +kernel

theorem strip498_sums :
    (approximations498.map Approximation.lower).sum = 530637387948291 ∧
      (approximations498.map Approximation.upper).sum = 530637643749157 := by
  decide +kernel

theorem strip499_sums :
    (approximations499.map Approximation.lower).sum = 532871864007039 ∧
      (approximations499.map Approximation.upper).sum = 532872120334143 := by
  decide +kernel

theorem strip500_sums :
    (approximations500.map Approximation.lower).sum = 535096963724488 ∧
      (approximations500.map Approximation.upper).sum = 535097220574549 := by
  decide +kernel

theorem strip501_sums :
    (approximations501.map Approximation.lower).sum = 537312683803695 ∧
      (approximations501.map Approximation.upper).sum = 537312941175055 := by
  decide +kernel

theorem block10_lower :
    (block10.map (fun xs => (xs.map Approximation.lower).sum)).sum = 8317975270946423 := by
  change (approximations486.map Approximation.lower).sum + ((approximations487.map Approximation.lower).sum + ((approximations488.map Approximation.lower).sum + ((approximations489.map Approximation.lower).sum + ((approximations490.map Approximation.lower).sum + ((approximations491.map Approximation.lower).sum + ((approximations492.map Approximation.lower).sum + ((approximations493.map Approximation.lower).sum + ((approximations494.map Approximation.lower).sum + ((approximations495.map Approximation.lower).sum + ((approximations496.map Approximation.lower).sum + ((approximations497.map Approximation.lower).sum + ((approximations498.map Approximation.lower).sum + ((approximations499.map Approximation.lower).sum + ((approximations500.map Approximation.lower).sum + ((approximations501.map Approximation.lower).sum + 0))))))))))))))) = 8317975270946423
  rw [strip486_sums.1, strip487_sums.1, strip488_sums.1, strip489_sums.1, strip490_sums.1, strip491_sums.1, strip492_sums.1, strip493_sums.1, strip494_sums.1, strip495_sums.1, strip496_sums.1, strip497_sums.1, strip498_sums.1, strip499_sums.1, strip500_sums.1, strip501_sums.1]
  decide +kernel

theorem block10_upper :
    (block10.map (fun xs => (xs.map Approximation.upper).sum)).sum = 8317979321620584 := by
  change (approximations486.map Approximation.upper).sum + ((approximations487.map Approximation.upper).sum + ((approximations488.map Approximation.upper).sum + ((approximations489.map Approximation.upper).sum + ((approximations490.map Approximation.upper).sum + ((approximations491.map Approximation.upper).sum + ((approximations492.map Approximation.upper).sum + ((approximations493.map Approximation.upper).sum + ((approximations494.map Approximation.upper).sum + ((approximations495.map Approximation.upper).sum + ((approximations496.map Approximation.upper).sum + ((approximations497.map Approximation.upper).sum + ((approximations498.map Approximation.upper).sum + ((approximations499.map Approximation.upper).sum + ((approximations500.map Approximation.upper).sum + ((approximations501.map Approximation.upper).sum + 0))))))))))))))) = 8317979321620584
  rw [strip486_sums.2, strip487_sums.2, strip488_sums.2, strip489_sums.2, strip490_sums.2, strip491_sums.2, strip492_sums.2, strip493_sums.2, strip494_sums.2, strip495_sums.2, strip496_sums.2, strip497_sums.2, strip498_sums.2, strip499_sums.2, strip500_sums.2, strip501_sums.2]
  decide +kernel



/-- Each length is checked separately over its original literal list. -/
theorem strip486_length :
    approximations486.length = 512 - firstU (⟨160, by decide⟩ : Fin 186) := by
  rfl

theorem strip487_length :
    approximations487.length = 512 - firstU (⟨161, by decide⟩ : Fin 186) := by
  rfl

theorem strip488_length :
    approximations488.length = 512 - firstU (⟨162, by decide⟩ : Fin 186) := by
  rfl

theorem strip489_length :
    approximations489.length = 512 - firstU (⟨163, by decide⟩ : Fin 186) := by
  rfl

theorem strip490_length :
    approximations490.length = 512 - firstU (⟨164, by decide⟩ : Fin 186) := by
  rfl

theorem strip491_length :
    approximations491.length = 512 - firstU (⟨165, by decide⟩ : Fin 186) := by
  rfl

theorem strip492_length :
    approximations492.length = 512 - firstU (⟨166, by decide⟩ : Fin 186) := by
  rfl

theorem strip493_length :
    approximations493.length = 512 - firstU (⟨167, by decide⟩ : Fin 186) := by
  rfl

theorem strip494_length :
    approximations494.length = 512 - firstU (⟨168, by decide⟩ : Fin 186) := by
  rfl

theorem strip495_length :
    approximations495.length = 512 - firstU (⟨169, by decide⟩ : Fin 186) := by
  rfl

theorem strip496_length :
    approximations496.length = 512 - firstU (⟨170, by decide⟩ : Fin 186) := by
  rfl

theorem strip497_length :
    approximations497.length = 512 - firstU (⟨171, by decide⟩ : Fin 186) := by
  rfl

theorem strip498_length :
    approximations498.length = 512 - firstU (⟨172, by decide⟩ : Fin 186) := by
  rfl

theorem strip499_length :
    approximations499.length = 512 - firstU (⟨173, by decide⟩ : Fin 186) := by
  rfl

theorem strip500_length :
    approximations500.length = 512 - firstU (⟨174, by decide⟩ : Fin 186) := by
  rfl

theorem strip501_length :
    approximations501.length = 512 - firstU (⟨175, by decide⟩ : Fin 186) := by
  rfl

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
