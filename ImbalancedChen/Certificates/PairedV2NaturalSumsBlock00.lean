import ImbalancedChen.Certificates.PairedV2FullCertificateDataBlock00

/-! Exhaustive natural-number endpoint sums, generated from unchanged witnesses.
The source generator is untrusted. Acceptance requires P0's Lean/kernel gates.
A strip is the largest numerical reduction: at most 191 rows. No checker is
rerun here, no Q160 value is substituted, and no native evaluator is trusted. -/


namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0


def block00 : List (List Approximation) :=
  [approximations326, approximations327, approximations328, approximations329, approximations330, approximations331, approximations332, approximations333, approximations334, approximations335, approximations336, approximations337, approximations338, approximations339, approximations340, approximations341]

theorem strip326_sums :
    (approximations326.map Approximation.lower).sum = 3398722871968 ∧
      (approximations326.map Approximation.upper).sum = 3398725146015 := by
  decide +kernel

theorem strip327_sums :
    (approximations327.map Approximation.lower).sum = 6797599230851 ∧
      (approximations327.map Approximation.upper).sum = 6797603778933 := by
  decide +kernel

theorem strip328_sums :
    (approximations328.map Approximation.lower).sum = 10196634611085 ∧
      (approximations328.map Approximation.upper).sum = 10196641433242 := by
  decide +kernel

theorem strip329_sums :
    (approximations329.map Approximation.lower).sum = 13595834555305 ∧
      (approximations329.map Approximation.upper).sum = 13595843651542 := by
  decide +kernel

theorem strip330_sums :
    (approximations330.map Approximation.lower).sum = 16995204614464 ∧
      (approximations330.map Approximation.upper).sum = 16995215984875 := by
  decide +kernel

theorem strip331_sums :
    (approximations331.map Approximation.lower).sum = 20394750347920 ∧
      (approximations331.map Approximation.upper).sum = 20394763992528 := by
  decide +kernel

theorem strip332_sums :
    (approximations332.map Approximation.lower).sum = 23794477323251 ∧
      (approximations332.map Approximation.upper).sum = 23794493242201 := by
  decide +kernel

theorem strip333_sums :
    (approximations333.map Approximation.lower).sum = 27194391116524 ∧
      (approximations333.map Approximation.upper).sum = 27194409309933 := by
  decide +kernel

theorem strip334_sums :
    (approximations334.map Approximation.lower).sum = 30594497312358 ∧
      (approximations334.map Approximation.upper).sum = 30594517780362 := by
  decide +kernel

theorem strip335_sums :
    (approximations335.map Approximation.lower).sum = 30571911321670 ∧
      (approximations335.map Approximation.upper).sum = 30571931741786 := by
  decide +kernel

theorem strip336_sums :
    (approximations336.map Approximation.lower).sum = 33969708831076 ∧
      (approximations336.map Approximation.upper).sum = 33969731520625 := by
  decide +kernel

theorem strip337_sums :
    (approximations337.map Approximation.lower).sum = 37367710495388 ∧
      (approximations337.map Approximation.upper).sum = 37367735454544 := by
  decide +kernel

theorem strip338_sums :
    (approximations338.map Approximation.lower).sum = 40765921920285 ∧
      (approximations338.map Approximation.upper).sum = 40765949149123 := by
  decide +kernel

theorem strip339_sums :
    (approximations339.map Approximation.lower).sum = 44164348719956 ∧
      (approximations339.map Approximation.upper).sum = 44164378218788 := by
  decide +kernel

theorem strip340_sums :
    (approximations340.map Approximation.lower).sum = 47562996517243 ∧
      (approximations340.map Approximation.upper).sum = 47563028286293 := by
  decide +kernel

theorem strip341_sums :
    (approximations341.map Approximation.lower).sum = 50961870944095 ∧
      (approximations341.map Approximation.upper).sum = 50961904983606 := by
  decide +kernel

theorem block00_lower :
    (block00.map (fun xs => (xs.map Approximation.lower).sum)).sum = 438326580733439 := by
  change (approximations326.map Approximation.lower).sum + ((approximations327.map Approximation.lower).sum + ((approximations328.map Approximation.lower).sum + ((approximations329.map Approximation.lower).sum + ((approximations330.map Approximation.lower).sum + ((approximations331.map Approximation.lower).sum + ((approximations332.map Approximation.lower).sum + ((approximations333.map Approximation.lower).sum + ((approximations334.map Approximation.lower).sum + ((approximations335.map Approximation.lower).sum + ((approximations336.map Approximation.lower).sum + ((approximations337.map Approximation.lower).sum + ((approximations338.map Approximation.lower).sum + ((approximations339.map Approximation.lower).sum + ((approximations340.map Approximation.lower).sum + ((approximations341.map Approximation.lower).sum + 0))))))))))))))) = 438326580733439
  rw [strip326_sums.1, strip327_sums.1, strip328_sums.1, strip329_sums.1, strip330_sums.1, strip331_sums.1, strip332_sums.1, strip333_sums.1, strip334_sums.1, strip335_sums.1, strip336_sums.1, strip337_sums.1, strip338_sums.1, strip339_sums.1, strip340_sums.1, strip341_sums.1]

theorem block00_upper :
    (block00.map (fun xs => (xs.map Approximation.upper).sum)).sum = 438326873674396 := by
  change (approximations326.map Approximation.upper).sum + ((approximations327.map Approximation.upper).sum + ((approximations328.map Approximation.upper).sum + ((approximations329.map Approximation.upper).sum + ((approximations330.map Approximation.upper).sum + ((approximations331.map Approximation.upper).sum + ((approximations332.map Approximation.upper).sum + ((approximations333.map Approximation.upper).sum + ((approximations334.map Approximation.upper).sum + ((approximations335.map Approximation.upper).sum + ((approximations336.map Approximation.upper).sum + ((approximations337.map Approximation.upper).sum + ((approximations338.map Approximation.upper).sum + ((approximations339.map Approximation.upper).sum + ((approximations340.map Approximation.upper).sum + ((approximations341.map Approximation.upper).sum + 0))))))))))))))) = 438326873674396
  rw [strip326_sums.2, strip327_sums.2, strip328_sums.2, strip329_sums.2, strip330_sums.2, strip331_sums.2, strip332_sums.2, strip333_sums.2, strip334_sums.2, strip335_sums.2, strip336_sums.2, strip337_sums.2, strip338_sums.2, strip339_sums.2, strip340_sums.2, strip341_sums.2]



/-- Each length is checked separately over its original literal list. -/
theorem strip326_length :
    approximations326.length = 512 - firstU (⟨0, by decide⟩ : Fin 186) := by
  rfl

theorem strip327_length :
    approximations327.length = 512 - firstU (⟨1, by decide⟩ : Fin 186) := by
  rfl

theorem strip328_length :
    approximations328.length = 512 - firstU (⟨2, by decide⟩ : Fin 186) := by
  rfl

theorem strip329_length :
    approximations329.length = 512 - firstU (⟨3, by decide⟩ : Fin 186) := by
  rfl

theorem strip330_length :
    approximations330.length = 512 - firstU (⟨4, by decide⟩ : Fin 186) := by
  rfl

theorem strip331_length :
    approximations331.length = 512 - firstU (⟨5, by decide⟩ : Fin 186) := by
  rfl

theorem strip332_length :
    approximations332.length = 512 - firstU (⟨6, by decide⟩ : Fin 186) := by
  rfl

theorem strip333_length :
    approximations333.length = 512 - firstU (⟨7, by decide⟩ : Fin 186) := by
  rfl

theorem strip334_length :
    approximations334.length = 512 - firstU (⟨8, by decide⟩ : Fin 186) := by
  rfl

theorem strip335_length :
    approximations335.length = 512 - firstU (⟨9, by decide⟩ : Fin 186) := by
  rfl

theorem strip336_length :
    approximations336.length = 512 - firstU (⟨10, by decide⟩ : Fin 186) := by
  rfl

theorem strip337_length :
    approximations337.length = 512 - firstU (⟨11, by decide⟩ : Fin 186) := by
  rfl

theorem strip338_length :
    approximations338.length = 512 - firstU (⟨12, by decide⟩ : Fin 186) := by
  rfl

theorem strip339_length :
    approximations339.length = 512 - firstU (⟨13, by decide⟩ : Fin 186) := by
  rfl

theorem strip340_length :
    approximations340.length = 512 - firstU (⟨14, by decide⟩ : Fin 186) := by
  rfl

theorem strip341_length :
    approximations341.length = 512 - firstU (⟨15, by decide⟩ : Fin 186) := by
  rfl

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
