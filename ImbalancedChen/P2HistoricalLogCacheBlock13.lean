import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query208_checked : logI (381574 / 381231 : ℚ) = (⟨1087202061010939269870, 1087202061010939269935⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query209_checked : logI (381231 / 380888 : ℚ) = (⟨1088180675524579914506, 1088180675524579914571⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query210_checked : logI (380888 / 380545 : ℚ) = (⟨1089161053370496573330, 1089161053370496573395⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query211_checked : logI (380545 / 380202 : ℚ) = (⟨1090143199318920093558, 1090143199318920093625⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query212_checked : logI (380202 / 379859 : ℚ) = (⟨1091127118157302989982, 1091127118157302990049⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query213_checked : logI (379859 / 379516 : ℚ) = (⟨1092112814690397233078, 1092112814690397233143⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query214_checked : logI (379516 / 379173 : ℚ) = (⟨1093100293740332459120, 1093100293740332459185⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query215_checked : logI (379173 / 378830 : ℚ) = (⟨1094089560146694604996, 1094089560146694605063⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query216_checked : logI (378830 / 378487 : ℚ) = (⟨1095080618766604970384, 1095080618766604970449⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query217_checked : logI (378487 / 378144 : ℚ) = (⟨1096073474474799710018, 1096073474474799710083⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query218_checked : logI (378144 / 377801 : ℚ) = (⟨1097068132163709758810, 1097068132163709758877⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query219_checked : logI (377801 / 377458 : ℚ) = (⟨1098064596743541192496, 1098064596743541192563⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query220_checked : logI (377458 / 377115 : ℚ) = (⟨1099062873142356026670, 1099062873142356026737⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query221_checked : logI (377115 / 376772 : ℚ) = (⟨1100062966306153456938, 1100062966306153457005⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query222_checked : logI (376772 / 376429 : ℚ) = (⟨1101064881198951543026, 1101064881198951543091⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query223_checked : logI (376429 / 376086 : ℚ) = (⟨1102068622802869339670, 1102068622802869339737⟩ : I80) := by
  decide +kernel

def block13 : List (ℚ × I80) :=
  [((381574 / 381231 : ℚ), (⟨1087202061010939269870, 1087202061010939269935⟩ : I80)),
   ((381231 / 380888 : ℚ), (⟨1088180675524579914506, 1088180675524579914571⟩ : I80)),
   ((380888 / 380545 : ℚ), (⟨1089161053370496573330, 1089161053370496573395⟩ : I80)),
   ((380545 / 380202 : ℚ), (⟨1090143199318920093558, 1090143199318920093625⟩ : I80)),
   ((380202 / 379859 : ℚ), (⟨1091127118157302989982, 1091127118157302990049⟩ : I80)),
   ((379859 / 379516 : ℚ), (⟨1092112814690397233078, 1092112814690397233143⟩ : I80)),
   ((379516 / 379173 : ℚ), (⟨1093100293740332459120, 1093100293740332459185⟩ : I80)),
   ((379173 / 378830 : ℚ), (⟨1094089560146694604996, 1094089560146694605063⟩ : I80)),
   ((378830 / 378487 : ℚ), (⟨1095080618766604970384, 1095080618766604970449⟩ : I80)),
   ((378487 / 378144 : ℚ), (⟨1096073474474799710018, 1096073474474799710083⟩ : I80)),
   ((378144 / 377801 : ℚ), (⟨1097068132163709758810, 1097068132163709758877⟩ : I80)),
   ((377801 / 377458 : ℚ), (⟨1098064596743541192496, 1098064596743541192563⟩ : I80)),
   ((377458 / 377115 : ℚ), (⟨1099062873142356026670, 1099062873142356026737⟩ : I80)),
   ((377115 / 376772 : ℚ), (⟨1100062966306153456938, 1100062966306153457005⟩ : I80)),
   ((376772 / 376429 : ℚ), (⟨1101064881198951543026, 1101064881198951543091⟩ : I80)),
   ((376429 / 376086 : ℚ), (⟨1102068622802869339670, 1102068622802869339737⟩ : I80))]

theorem block13_checked : ∀ p ∈ block13, p.2 = logI p.1 := by
  intro p hp
  simp only [block13, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query208_checked.symm
  · exact query209_checked.symm
  · exact query210_checked.symm
  · exact query211_checked.symm
  · exact query212_checked.symm
  · exact query213_checked.symm
  · exact query214_checked.symm
  · exact query215_checked.symm
  · exact query216_checked.symm
  · exact query217_checked.symm
  · exact query218_checked.symm
  · exact query219_checked.symm
  · exact query220_checked.symm
  · exact query221_checked.symm
  · exact query222_checked.symm
  · exact query223_checked.symm

end ImbalancedChen.P2HistoricalLogCache
