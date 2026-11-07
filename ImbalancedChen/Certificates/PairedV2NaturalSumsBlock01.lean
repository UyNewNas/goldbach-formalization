import ImbalancedChen.Certificates.PairedV2FullCertificateDataBlock01

/-! Exhaustive natural-number endpoint sums, generated from unchanged witnesses.
The source generator is untrusted. Acceptance requires P0's Lean/kernel gates.
A strip is the largest numerical reduction: at most 191 rows. No checker is
rerun here, no Q160 value is substituted, and no native evaluator is trusted. -/


namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0


def block01 : List (List Approximation) :=
  [approximations342, approximations343, approximations344, approximations345, approximations346, approximations347, approximations348, approximations349, approximations350, approximations351, approximations352, approximations353, approximations354, approximations355, approximations356, approximations357]

theorem strip342_sums :
    (approximations342.map Approximation.lower).sum = 54360977640992 ∧
      (approximations342.map Approximation.upper).sum = 54361013951074 := by
  decide +kernel

theorem strip343_sums :
    (approximations343.map Approximation.lower).sum = 57760322257060 ∧
      (approximations343.map Approximation.upper).sum = 57760360838125 := by
  decide +kernel

theorem strip344_sums :
    (approximations344.map Approximation.lower).sum = 61159910450724 ∧
      (approximations344.map Approximation.upper).sum = 61159951303080 := by
  decide +kernel

theorem strip345_sums :
    (approximations345.map Approximation.lower).sum = 64559747888843 ∧
      (approximations345.map Approximation.upper).sum = 64559791012801 := by
  decide +kernel

theorem strip346_sums :
    (approximations346.map Approximation.lower).sum = 67959840247723 ∧
      (approximations346.map Approximation.upper).sum = 67959885643611 := by
  decide +kernel

theorem strip347_sums :
    (approximations347.map Approximation.lower).sum = 71360193212505 ∧
      (approximations347.map Approximation.upper).sum = 71360240880474 := by
  decide +kernel

theorem strip348_sums :
    (approximations348.map Approximation.lower).sum = 74760812477162 ∧
      (approximations348.map Approximation.upper).sum = 74760862417768 := by
  decide +kernel

theorem strip349_sums :
    (approximations349.map Approximation.lower).sum = 78161703745142 ∧
      (approximations349.map Approximation.upper).sum = 78161755958771 := by
  decide +kernel

theorem strip350_sums :
    (approximations350.map Approximation.lower).sum = 81562872728834 ∧
      (approximations350.map Approximation.upper).sum = 81562927215893 := by
  decide +kernel

theorem strip351_sums :
    (approximations351.map Approximation.lower).sum = 84964325150020 ∧
      (approximations351.map Approximation.upper).sum = 84964381910934 := by
  decide +kernel

theorem strip352_sums :
    (approximations352.map Approximation.lower).sum = 88366066739240 ∧
      (approximations352.map Approximation.upper).sum = 88366125774688 := by
  decide +kernel

theorem strip353_sums :
    (approximations353.map Approximation.lower).sum = 91768103237254 ∧
      (approximations353.map Approximation.upper).sum = 91768164547206 := by
  decide +kernel

theorem strip354_sums :
    (approximations354.map Approximation.lower).sum = 95170440393448 ∧
      (approximations354.map Approximation.upper).sum = 95170503978624 := by
  decide +kernel

theorem strip355_sums :
    (approximations355.map Approximation.lower).sum = 98573083966513 ∧
      (approximations355.map Approximation.upper).sum = 98573149827410 := by
  decide +kernel

theorem strip356_sums :
    (approximations356.map Approximation.lower).sum = 101976039725101 ∧
      (approximations356.map Approximation.upper).sum = 101976107862516 := by
  decide +kernel

theorem strip357_sums :
    (approximations357.map Approximation.lower).sum = 108863017670591 ∧
      (approximations357.map Approximation.upper).sum = 108863090531057 := by
  decide +kernel

theorem block01_lower :
    (block01.map (fun xs => (xs.map Approximation.lower).sum)).sum = 1281327457531152 := by
  change (approximations342.map Approximation.lower).sum + ((approximations343.map Approximation.lower).sum + ((approximations344.map Approximation.lower).sum + ((approximations345.map Approximation.lower).sum + ((approximations346.map Approximation.lower).sum + ((approximations347.map Approximation.lower).sum + ((approximations348.map Approximation.lower).sum + ((approximations349.map Approximation.lower).sum + ((approximations350.map Approximation.lower).sum + ((approximations351.map Approximation.lower).sum + ((approximations352.map Approximation.lower).sum + ((approximations353.map Approximation.lower).sum + ((approximations354.map Approximation.lower).sum + ((approximations355.map Approximation.lower).sum + ((approximations356.map Approximation.lower).sum + ((approximations357.map Approximation.lower).sum + 0))))))))))))))) = 1281327457531152
  rw [strip342_sums.1, strip343_sums.1, strip344_sums.1, strip345_sums.1, strip346_sums.1, strip347_sums.1, strip348_sums.1, strip349_sums.1, strip350_sums.1, strip351_sums.1, strip352_sums.1, strip353_sums.1, strip354_sums.1, strip355_sums.1, strip356_sums.1, strip357_sums.1]

theorem block01_upper :
    (block01.map (fun xs => (xs.map Approximation.upper).sum)).sum = 1281328313654032 := by
  change (approximations342.map Approximation.upper).sum + ((approximations343.map Approximation.upper).sum + ((approximations344.map Approximation.upper).sum + ((approximations345.map Approximation.upper).sum + ((approximations346.map Approximation.upper).sum + ((approximations347.map Approximation.upper).sum + ((approximations348.map Approximation.upper).sum + ((approximations349.map Approximation.upper).sum + ((approximations350.map Approximation.upper).sum + ((approximations351.map Approximation.upper).sum + ((approximations352.map Approximation.upper).sum + ((approximations353.map Approximation.upper).sum + ((approximations354.map Approximation.upper).sum + ((approximations355.map Approximation.upper).sum + ((approximations356.map Approximation.upper).sum + ((approximations357.map Approximation.upper).sum + 0))))))))))))))) = 1281328313654032
  rw [strip342_sums.2, strip343_sums.2, strip344_sums.2, strip345_sums.2, strip346_sums.2, strip347_sums.2, strip348_sums.2, strip349_sums.2, strip350_sums.2, strip351_sums.2, strip352_sums.2, strip353_sums.2, strip354_sums.2, strip355_sums.2, strip356_sums.2, strip357_sums.2]



/-- Each length is checked separately over its original literal list. -/
theorem strip342_length :
    approximations342.length = 512 - firstU (⟨16, by decide⟩ : Fin 186) := by
  rfl

theorem strip343_length :
    approximations343.length = 512 - firstU (⟨17, by decide⟩ : Fin 186) := by
  rfl

theorem strip344_length :
    approximations344.length = 512 - firstU (⟨18, by decide⟩ : Fin 186) := by
  rfl

theorem strip345_length :
    approximations345.length = 512 - firstU (⟨19, by decide⟩ : Fin 186) := by
  rfl

theorem strip346_length :
    approximations346.length = 512 - firstU (⟨20, by decide⟩ : Fin 186) := by
  rfl

theorem strip347_length :
    approximations347.length = 512 - firstU (⟨21, by decide⟩ : Fin 186) := by
  rfl

theorem strip348_length :
    approximations348.length = 512 - firstU (⟨22, by decide⟩ : Fin 186) := by
  rfl

theorem strip349_length :
    approximations349.length = 512 - firstU (⟨23, by decide⟩ : Fin 186) := by
  rfl

theorem strip350_length :
    approximations350.length = 512 - firstU (⟨24, by decide⟩ : Fin 186) := by
  rfl

theorem strip351_length :
    approximations351.length = 512 - firstU (⟨25, by decide⟩ : Fin 186) := by
  rfl

theorem strip352_length :
    approximations352.length = 512 - firstU (⟨26, by decide⟩ : Fin 186) := by
  rfl

theorem strip353_length :
    approximations353.length = 512 - firstU (⟨27, by decide⟩ : Fin 186) := by
  rfl

theorem strip354_length :
    approximations354.length = 512 - firstU (⟨28, by decide⟩ : Fin 186) := by
  rfl

theorem strip355_length :
    approximations355.length = 512 - firstU (⟨29, by decide⟩ : Fin 186) := by
  rfl

theorem strip356_length :
    approximations356.length = 512 - firstU (⟨30, by decide⟩ : Fin 186) := by
  rfl

theorem strip357_length :
    approximations357.length = 512 - firstU (⟨31, by decide⟩ : Fin 186) := by
  rfl

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
