import ImbalancedChen.Certificates.PairedV2FullCertificateDataBlock08

/-! Exhaustive natural-number endpoint sums, generated from unchanged witnesses.
The source generator is untrusted. Acceptance requires P0's Lean/kernel gates.
A strip is the largest numerical reduction: at most 191 rows. No checker is
rerun here, no Q160 value is substituted, and no native evaluator is trusted. -/


namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0


def block08 : List (List Approximation) :=
  [approximations454, approximations455, approximations456, approximations457, approximations458, approximations459, approximations460, approximations461, approximations462, approximations463, approximations464, approximations465, approximations466, approximations467, approximations468, approximations469]

theorem strip454_sums :
    (approximations454.map Approximation.lower).sum = 417160838161233 ∧
      (approximations454.map Approximation.upper).sum = 417161063776280 := by
  decide +kernel

theorem strip455_sums :
    (approximations455.map Approximation.lower).sum = 419827559034695 ∧
      (approximations455.map Approximation.upper).sum = 419827785435264 := by
  decide +kernel

theorem strip456_sums :
    (approximations456.map Approximation.lower).sum = 422485082506097 ∧
      (approximations456.map Approximation.upper).sum = 422485309683272 := by
  decide +kernel

theorem strip457_sums :
    (approximations457.map Approximation.lower).sum = 425133404385070 ∧
      (approximations457.map Approximation.upper).sum = 425133632331276 := by
  decide +kernel

theorem strip458_sums :
    (approximations458.map Approximation.lower).sum = 427772520489686 ∧
      (approximations458.map Approximation.upper).sum = 427772749200031 := by
  decide +kernel

theorem strip459_sums :
    (approximations459.map Approximation.lower).sum = 430402426655568 ∧
      (approximations459.map Approximation.upper).sum = 430402656119020 := by
  decide +kernel

theorem strip460_sums :
    (approximations460.map Approximation.lower).sum = 433023118722440 ∧
      (approximations460.map Approximation.upper).sum = 433023348935645 := by
  decide +kernel

theorem strip461_sums :
    (approximations461.map Approximation.lower).sum = 435634592549501 ∧
      (approximations461.map Approximation.upper).sum = 435634823502944 := by
  decide +kernel

theorem strip462_sums :
    (approximations462.map Approximation.lower).sum = 438236324695185 ∧
      (approximations462.map Approximation.upper).sum = 438236556381612 := by
  decide +kernel

theorem strip463_sums :
    (approximations463.map Approximation.lower).sum = 440828049661643 ∧
      (approximations463.map Approximation.upper).sum = 440828282070564 := by
  decide +kernel

theorem strip464_sums :
    (approximations464.map Approximation.lower).sum = 443410544890123 ∧
      (approximations464.map Approximation.upper).sum = 443410778016229 := by
  decide +kernel

theorem strip465_sums :
    (approximations465.map Approximation.lower).sum = 445983806290147 ∧
      (approximations465.map Approximation.upper).sum = 445984040126960 := by
  decide +kernel

theorem strip466_sums :
    (approximations466.map Approximation.lower).sum = 448547829779648 ∧
      (approximations466.map Approximation.upper).sum = 448548064319530 := by
  decide +kernel

theorem strip467_sums :
    (approximations467.map Approximation.lower).sum = 451102611293118 ∧
      (approximations467.map Approximation.upper).sum = 451102846531125 := by
  decide +kernel

theorem strip468_sums :
    (approximations468.map Approximation.lower).sum = 453648146780630 ∧
      (approximations468.map Approximation.upper).sum = 453648382710658 := by
  decide +kernel

theorem strip469_sums :
    (approximations469.map Approximation.lower).sum = 458944039890768 ∧
      (approximations469.map Approximation.upper).sum = 458944277488921 := by
  decide +kernel

theorem block08_lower :
    (block08.map (fun xs => (xs.map Approximation.lower).sum)).sum = 6992140895785552 := by
  change (approximations454.map Approximation.lower).sum + ((approximations455.map Approximation.lower).sum + ((approximations456.map Approximation.lower).sum + ((approximations457.map Approximation.lower).sum + ((approximations458.map Approximation.lower).sum + ((approximations459.map Approximation.lower).sum + ((approximations460.map Approximation.lower).sum + ((approximations461.map Approximation.lower).sum + ((approximations462.map Approximation.lower).sum + ((approximations463.map Approximation.lower).sum + ((approximations464.map Approximation.lower).sum + ((approximations465.map Approximation.lower).sum + ((approximations466.map Approximation.lower).sum + ((approximations467.map Approximation.lower).sum + ((approximations468.map Approximation.lower).sum + ((approximations469.map Approximation.lower).sum + 0))))))))))))))) = 6992140895785552
  rw [strip454_sums.1, strip455_sums.1, strip456_sums.1, strip457_sums.1, strip458_sums.1, strip459_sums.1, strip460_sums.1, strip461_sums.1, strip462_sums.1, strip463_sums.1, strip464_sums.1, strip465_sums.1, strip466_sums.1, strip467_sums.1, strip468_sums.1, strip469_sums.1]

theorem block08_upper :
    (block08.map (fun xs => (xs.map Approximation.upper).sum)).sum = 6992144596629331 := by
  change (approximations454.map Approximation.upper).sum + ((approximations455.map Approximation.upper).sum + ((approximations456.map Approximation.upper).sum + ((approximations457.map Approximation.upper).sum + ((approximations458.map Approximation.upper).sum + ((approximations459.map Approximation.upper).sum + ((approximations460.map Approximation.upper).sum + ((approximations461.map Approximation.upper).sum + ((approximations462.map Approximation.upper).sum + ((approximations463.map Approximation.upper).sum + ((approximations464.map Approximation.upper).sum + ((approximations465.map Approximation.upper).sum + ((approximations466.map Approximation.upper).sum + ((approximations467.map Approximation.upper).sum + ((approximations468.map Approximation.upper).sum + ((approximations469.map Approximation.upper).sum + 0))))))))))))))) = 6992144596629331
  rw [strip454_sums.2, strip455_sums.2, strip456_sums.2, strip457_sums.2, strip458_sums.2, strip459_sums.2, strip460_sums.2, strip461_sums.2, strip462_sums.2, strip463_sums.2, strip464_sums.2, strip465_sums.2, strip466_sums.2, strip467_sums.2, strip468_sums.2, strip469_sums.2]



/-- Each length is checked separately over its original literal list. -/
theorem strip454_length :
    approximations454.length = 512 - firstU (⟨128, by decide⟩ : Fin 186) := by
  rfl

theorem strip455_length :
    approximations455.length = 512 - firstU (⟨129, by decide⟩ : Fin 186) := by
  rfl

theorem strip456_length :
    approximations456.length = 512 - firstU (⟨130, by decide⟩ : Fin 186) := by
  rfl

theorem strip457_length :
    approximations457.length = 512 - firstU (⟨131, by decide⟩ : Fin 186) := by
  rfl

theorem strip458_length :
    approximations458.length = 512 - firstU (⟨132, by decide⟩ : Fin 186) := by
  rfl

theorem strip459_length :
    approximations459.length = 512 - firstU (⟨133, by decide⟩ : Fin 186) := by
  rfl

theorem strip460_length :
    approximations460.length = 512 - firstU (⟨134, by decide⟩ : Fin 186) := by
  rfl

theorem strip461_length :
    approximations461.length = 512 - firstU (⟨135, by decide⟩ : Fin 186) := by
  rfl

theorem strip462_length :
    approximations462.length = 512 - firstU (⟨136, by decide⟩ : Fin 186) := by
  rfl

theorem strip463_length :
    approximations463.length = 512 - firstU (⟨137, by decide⟩ : Fin 186) := by
  rfl

theorem strip464_length :
    approximations464.length = 512 - firstU (⟨138, by decide⟩ : Fin 186) := by
  rfl

theorem strip465_length :
    approximations465.length = 512 - firstU (⟨139, by decide⟩ : Fin 186) := by
  rfl

theorem strip466_length :
    approximations466.length = 512 - firstU (⟨140, by decide⟩ : Fin 186) := by
  rfl

theorem strip467_length :
    approximations467.length = 512 - firstU (⟨141, by decide⟩ : Fin 186) := by
  rfl

theorem strip468_length :
    approximations468.length = 512 - firstU (⟨142, by decide⟩ : Fin 186) := by
  rfl

theorem strip469_length :
    approximations469.length = 512 - firstU (⟨143, by decide⟩ : Fin 186) := by
  rfl

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
