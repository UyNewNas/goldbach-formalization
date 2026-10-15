import ImbalancedChen.Certificates.PairedV2FullCertificateDataBlock02

/-! Exhaustive natural-number endpoint sums, generated from unchanged witnesses.
The source generator is untrusted. Acceptance requires P0's Lean/kernel gates.
A strip is the largest numerical reduction: at most 191 rows. No checker is
rerun here, no Q160 value is substituted, and no native evaluator is trusted. -/


namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0


def block02 : List (List Approximation) :=
  [approximations358, approximations359, approximations360, approximations361, approximations362, approximations363, approximations364, approximations365, approximations366, approximations367, approximations368, approximations369, approximations370, approximations371, approximations372, approximations373]

theorem strip358_sums :
    (approximations358.map Approximation.lower).sum = 112269439714344 ∧
      (approximations358.map Approximation.upper).sum = 112269514857947 := by
  decide +kernel

theorem strip359_sums :
    (approximations359.map Approximation.lower).sum = 115676196661363 ∧
      (approximations359.map Approximation.upper).sum = 115676274088683 := by
  decide +kernel

theorem strip360_sums :
    (approximations360.map Approximation.lower).sum = 119083294332808 ∧
      (approximations360.map Approximation.upper).sum = 119083374044791 := by
  decide +kernel

theorem strip361_sums :
    (approximations361.map Approximation.lower).sum = 118995703863709 ∧
      (approximations361.map Approximation.upper).sum = 118995783390635 := by
  decide +kernel

theorem strip362_sums :
    (approximations362.map Approximation.lower).sum = 122400654407606 ∧
      (approximations362.map Approximation.upper).sum = 122400736214221 := by
  decide +kernel

theorem strip363_sums :
    (approximations363.map Approximation.lower).sum = 125805957784808 ∧
      (approximations363.map Approximation.upper).sum = 125806041871756 := by
  decide +kernel

theorem strip364_sums :
    (approximations364.map Approximation.lower).sum = 129211619841057 ∧
      (approximations364.map Approximation.upper).sum = 129211706209361 := by
  decide +kernel

theorem strip365_sums :
    (approximations365.map Approximation.lower).sum = 132617646432286 ∧
      (approximations365.map Approximation.upper).sum = 132617735081896 := by
  decide +kernel

theorem strip366_sums :
    (approximations366.map Approximation.lower).sum = 136024043423605 ∧
      (approximations366.map Approximation.upper).sum = 136024134355960 := by
  decide +kernel

theorem strip367_sums :
    (approximations367.map Approximation.lower).sum = 139430816691170 ∧
      (approximations367.map Approximation.upper).sum = 139430909906213 := by
  decide +kernel

theorem strip368_sums :
    (approximations368.map Approximation.lower).sum = 142837972119994 ∧
      (approximations368.map Approximation.upper).sum = 142838067619256 := by
  decide +kernel

theorem strip369_sums :
    (approximations369.map Approximation.lower).sum = 146245515606725 ∧
      (approximations369.map Approximation.upper).sum = 146245613390962 := by
  decide +kernel

theorem strip370_sums :
    (approximations370.map Approximation.lower).sum = 149653453056903 ∧
      (approximations370.map Approximation.upper).sum = 149653553126487 := by
  decide +kernel

theorem strip371_sums :
    (approximations371.map Approximation.lower).sum = 153061790387053 ∧
      (approximations371.map Approximation.upper).sum = 153061892742774 := by
  decide +kernel

theorem strip372_sums :
    (approximations372.map Approximation.lower).sum = 156470533523060 ∧
      (approximations372.map Approximation.upper).sum = 156470638165711 := by
  decide +kernel

theorem strip373_sums :
    (approximations373.map Approximation.lower).sum = 163409236529603 ∧
      (approximations373.map Approximation.upper).sum = 163409346002449 := by
  decide +kernel

theorem block02_lower :
    (block02.map (fun xs => (xs.map Approximation.lower).sum)).sum = 2163193874376094 := by
  change (approximations358.map Approximation.lower).sum + ((approximations359.map Approximation.lower).sum + ((approximations360.map Approximation.lower).sum + ((approximations361.map Approximation.lower).sum + ((approximations362.map Approximation.lower).sum + ((approximations363.map Approximation.lower).sum + ((approximations364.map Approximation.lower).sum + ((approximations365.map Approximation.lower).sum + ((approximations366.map Approximation.lower).sum + ((approximations367.map Approximation.lower).sum + ((approximations368.map Approximation.lower).sum + ((approximations369.map Approximation.lower).sum + ((approximations370.map Approximation.lower).sum + ((approximations371.map Approximation.lower).sum + ((approximations372.map Approximation.lower).sum + ((approximations373.map Approximation.lower).sum + 0))))))))))))))) = 2163193874376094
  rw [strip358_sums.1, strip359_sums.1, strip360_sums.1, strip361_sums.1, strip362_sums.1, strip363_sums.1, strip364_sums.1, strip365_sums.1, strip366_sums.1, strip367_sums.1, strip368_sums.1, strip369_sums.1, strip370_sums.1, strip371_sums.1, strip372_sums.1, strip373_sums.1]
  decide +kernel

theorem block02_upper :
    (block02.map (fun xs => (xs.map Approximation.upper).sum)).sum = 2163195321069102 := by
  change (approximations358.map Approximation.upper).sum + ((approximations359.map Approximation.upper).sum + ((approximations360.map Approximation.upper).sum + ((approximations361.map Approximation.upper).sum + ((approximations362.map Approximation.upper).sum + ((approximations363.map Approximation.upper).sum + ((approximations364.map Approximation.upper).sum + ((approximations365.map Approximation.upper).sum + ((approximations366.map Approximation.upper).sum + ((approximations367.map Approximation.upper).sum + ((approximations368.map Approximation.upper).sum + ((approximations369.map Approximation.upper).sum + ((approximations370.map Approximation.upper).sum + ((approximations371.map Approximation.upper).sum + ((approximations372.map Approximation.upper).sum + ((approximations373.map Approximation.upper).sum + 0))))))))))))))) = 2163195321069102
  rw [strip358_sums.2, strip359_sums.2, strip360_sums.2, strip361_sums.2, strip362_sums.2, strip363_sums.2, strip364_sums.2, strip365_sums.2, strip366_sums.2, strip367_sums.2, strip368_sums.2, strip369_sums.2, strip370_sums.2, strip371_sums.2, strip372_sums.2, strip373_sums.2]
  decide +kernel



/-- Each length is checked separately over its original literal list. -/
theorem strip358_length :
    approximations358.length = 512 - firstU (⟨32, by decide⟩ : Fin 186) := by
  rfl

theorem strip359_length :
    approximations359.length = 512 - firstU (⟨33, by decide⟩ : Fin 186) := by
  rfl

theorem strip360_length :
    approximations360.length = 512 - firstU (⟨34, by decide⟩ : Fin 186) := by
  rfl

theorem strip361_length :
    approximations361.length = 512 - firstU (⟨35, by decide⟩ : Fin 186) := by
  rfl

theorem strip362_length :
    approximations362.length = 512 - firstU (⟨36, by decide⟩ : Fin 186) := by
  rfl

theorem strip363_length :
    approximations363.length = 512 - firstU (⟨37, by decide⟩ : Fin 186) := by
  rfl

theorem strip364_length :
    approximations364.length = 512 - firstU (⟨38, by decide⟩ : Fin 186) := by
  rfl

theorem strip365_length :
    approximations365.length = 512 - firstU (⟨39, by decide⟩ : Fin 186) := by
  rfl

theorem strip366_length :
    approximations366.length = 512 - firstU (⟨40, by decide⟩ : Fin 186) := by
  rfl

theorem strip367_length :
    approximations367.length = 512 - firstU (⟨41, by decide⟩ : Fin 186) := by
  rfl

theorem strip368_length :
    approximations368.length = 512 - firstU (⟨42, by decide⟩ : Fin 186) := by
  rfl

theorem strip369_length :
    approximations369.length = 512 - firstU (⟨43, by decide⟩ : Fin 186) := by
  rfl

theorem strip370_length :
    approximations370.length = 512 - firstU (⟨44, by decide⟩ : Fin 186) := by
  rfl

theorem strip371_length :
    approximations371.length = 512 - firstU (⟨45, by decide⟩ : Fin 186) := by
  rfl

theorem strip372_length :
    approximations372.length = 512 - firstU (⟨46, by decide⟩ : Fin 186) := by
  rfl

theorem strip373_length :
    approximations373.length = 512 - firstU (⟨47, by decide⟩ : Fin 186) := by
  rfl

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
