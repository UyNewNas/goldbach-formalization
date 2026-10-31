import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query192_checked : logI (387062 / 386719 : ℚ) = (⟨1071780215041465690838, 1071780215041465690905⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query193_checked : logI (386719 / 386376 : ℚ) = (⟨1072731251232310259034, 1072731251232310259101⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query194_checked : logI (386376 / 386033 : ℚ) = (⟨1073683976712004275588, 1073683976712004275653⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query195_checked : logI (386033 / 385690 : ℚ) = (⟨1074638395985476797486, 1074638395985476797551⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query196_checked : logI (385690 / 385347 : ℚ) = (⟨1075594513573689224398, 1075594513573689224463⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query197_checked : logI (385347 / 385004 : ℚ) = (⟨1076552334013706682956, 1076552334013706683021⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query198_checked : logI (385004 / 384661 : ℚ) = (⟨1077511861858769792796, 1077511861858769792863⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query199_checked : logI (384661 / 384318 : ℚ) = (⟨1078473101678366816728, 1078473101678366816793⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query200_checked : logI (384318 / 383975 : ℚ) = (⟨1079436058058306197420, 1079436058058306197487⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query201_checked : logI (383975 / 383632 : ℚ) = (⟨1080400735600789483060, 1080400735600789483127⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query202_checked : logI (383632 / 383289 : ℚ) = (⟨1081367138924484644396, 1081367138924484644461⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query203_checked : logI (383289 / 382946 : ℚ) = (⟨1082335272664599785590, 1082335272664599785657⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query204_checked : logI (382946 / 382603 : ℚ) = (⟨1083305141472957251430, 1083305141472957251495⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query205_checked : logI (382603 / 382260 : ℚ) = (⟨1084276750018068133286, 1084276750018068133351⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query206_checked : logI (382260 / 381917 : ℚ) = (⟨1085250102985207176408, 1085250102985207176473⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query207_checked : logI (381917 / 381574 : ℚ) = (⟨1086225205076488091032, 1086225205076488091099⟩ : I80) := by
  decide +kernel

def block12 : List (ℚ × I80) :=
  [((387062 / 386719 : ℚ), (⟨1071780215041465690838, 1071780215041465690905⟩ : I80)),
   ((386719 / 386376 : ℚ), (⟨1072731251232310259034, 1072731251232310259101⟩ : I80)),
   ((386376 / 386033 : ℚ), (⟨1073683976712004275588, 1073683976712004275653⟩ : I80)),
   ((386033 / 385690 : ℚ), (⟨1074638395985476797486, 1074638395985476797551⟩ : I80)),
   ((385690 / 385347 : ℚ), (⟨1075594513573689224398, 1075594513573689224463⟩ : I80)),
   ((385347 / 385004 : ℚ), (⟨1076552334013706682956, 1076552334013706683021⟩ : I80)),
   ((385004 / 384661 : ℚ), (⟨1077511861858769792796, 1077511861858769792863⟩ : I80)),
   ((384661 / 384318 : ℚ), (⟨1078473101678366816728, 1078473101678366816793⟩ : I80)),
   ((384318 / 383975 : ℚ), (⟨1079436058058306197420, 1079436058058306197487⟩ : I80)),
   ((383975 / 383632 : ℚ), (⟨1080400735600789483060, 1080400735600789483127⟩ : I80)),
   ((383632 / 383289 : ℚ), (⟨1081367138924484644396, 1081367138924484644461⟩ : I80)),
   ((383289 / 382946 : ℚ), (⟨1082335272664599785590, 1082335272664599785657⟩ : I80)),
   ((382946 / 382603 : ℚ), (⟨1083305141472957251430, 1083305141472957251495⟩ : I80)),
   ((382603 / 382260 : ℚ), (⟨1084276750018068133286, 1084276750018068133351⟩ : I80)),
   ((382260 / 381917 : ℚ), (⟨1085250102985207176408, 1085250102985207176473⟩ : I80)),
   ((381917 / 381574 : ℚ), (⟨1086225205076488091032, 1086225205076488091099⟩ : I80))]

theorem block12_checked : ∀ p ∈ block12, p.2 = logI p.1 := by
  intro p hp
  simp only [block12, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query192_checked.symm
  · exact query193_checked.symm
  · exact query194_checked.symm
  · exact query195_checked.symm
  · exact query196_checked.symm
  · exact query197_checked.symm
  · exact query198_checked.symm
  · exact query199_checked.symm
  · exact query200_checked.symm
  · exact query201_checked.symm
  · exact query202_checked.symm
  · exact query203_checked.symm
  · exact query204_checked.symm
  · exact query205_checked.symm
  · exact query206_checked.symm
  · exact query207_checked.symm

end ImbalancedChen.P2HistoricalLogCache
