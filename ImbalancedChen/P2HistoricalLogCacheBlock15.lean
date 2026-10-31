import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query240_checked : logI (370598 / 370255 : ℚ) = (⟨1119416633948799931876, 1119416633948799931941⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query241_checked : logI (370255 / 369912 : ℚ) = (⟨1120454129433977481016, 1120454129433977481083⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query242_checked : logI (369912 / 369569 : ℚ) = (⟨1121493549842326320422, 1121493549842326320489⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query243_checked : logI (369569 / 369226 : ℚ) = (⟨1122534900535946929174, 1122534900535946929241⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query244_checked : logI (369226 / 368883 : ℚ) = (⟨1123578186896873981718, 1123578186896873981783⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query245_checked : logI (368883 / 368540 : ℚ) = (⟨1124623414327169068470, 1124623414327169068535⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query246_checked : logI (368540 / 368197 : ℚ) = (⟨1125670588249013934466, 1125670588249013934533⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query247_checked : logI (368197 / 367854 : ℚ) = (⟨1126719714104804239380, 1126719714104804239445⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query248_checked : logI (367854 / 367511 : ℚ) = (⟨1127770797357243842340, 1127770797357243842407⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query249_checked : logI (367511 / 367168 : ℚ) = (⟨1128823843489439614986, 1128823843489439615051⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query250_checked : logI (367168 / 366825 : ℚ) = (⟨1129878858004996786188, 1129878858004996786253⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query251_checked : logI (366825 / 366482 : ℚ) = (⟨1130935846428114821940, 1130935846428114822007⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query252_checked : logI (366482 / 366139 : ℚ) = (⟨1131994814303683843934, 1131994814303683844001⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query253_checked : logI (366139 / 365796 : ℚ) = (⟨1133055767197381590314, 1133055767197381590379⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query254_checked : logI (365796 / 365453 : ℚ) = (⟨1134118710695770922218, 1134118710695770922285⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query255_checked : logI (365453 / 365110 : ℚ) = (⟨1135183650406397879668, 1135183650406397879733⟩ : I80) := by
  decide +kernel

def block15 : List (ℚ × I80) :=
  [((370598 / 370255 : ℚ), (⟨1119416633948799931876, 1119416633948799931941⟩ : I80)),
   ((370255 / 369912 : ℚ), (⟨1120454129433977481016, 1120454129433977481083⟩ : I80)),
   ((369912 / 369569 : ℚ), (⟨1121493549842326320422, 1121493549842326320489⟩ : I80)),
   ((369569 / 369226 : ℚ), (⟨1122534900535946929174, 1122534900535946929241⟩ : I80)),
   ((369226 / 368883 : ℚ), (⟨1123578186896873981718, 1123578186896873981783⟩ : I80)),
   ((368883 / 368540 : ℚ), (⟨1124623414327169068470, 1124623414327169068535⟩ : I80)),
   ((368540 / 368197 : ℚ), (⟨1125670588249013934466, 1125670588249013934533⟩ : I80)),
   ((368197 / 367854 : ℚ), (⟨1126719714104804239380, 1126719714104804239445⟩ : I80)),
   ((367854 / 367511 : ℚ), (⟨1127770797357243842340, 1127770797357243842407⟩ : I80)),
   ((367511 / 367168 : ℚ), (⟨1128823843489439614986, 1128823843489439615051⟩ : I80)),
   ((367168 / 366825 : ℚ), (⟨1129878858004996786188, 1129878858004996786253⟩ : I80)),
   ((366825 / 366482 : ℚ), (⟨1130935846428114821940, 1130935846428114822007⟩ : I80)),
   ((366482 / 366139 : ℚ), (⟨1131994814303683843934, 1131994814303683844001⟩ : I80)),
   ((366139 / 365796 : ℚ), (⟨1133055767197381590314, 1133055767197381590379⟩ : I80)),
   ((365796 / 365453 : ℚ), (⟨1134118710695770922218, 1134118710695770922285⟩ : I80)),
   ((365453 / 365110 : ℚ), (⟨1135183650406397879668, 1135183650406397879733⟩ : I80))]

theorem block15_checked : ∀ p ∈ block15, p.2 = logI p.1 := by
  intro p hp
  simp only [block15, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query240_checked.symm
  · exact query241_checked.symm
  · exact query242_checked.symm
  · exact query243_checked.symm
  · exact query244_checked.symm
  · exact query245_checked.symm
  · exact query246_checked.symm
  · exact query247_checked.symm
  · exact query248_checked.symm
  · exact query249_checked.symm
  · exact query250_checked.symm
  · exact query251_checked.symm
  · exact query252_checked.symm
  · exact query253_checked.symm
  · exact query254_checked.symm
  · exact query255_checked.symm

end ImbalancedChen.P2HistoricalLogCache
