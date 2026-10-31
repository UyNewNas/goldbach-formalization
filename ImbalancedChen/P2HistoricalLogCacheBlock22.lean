import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query352_checked : logI (332182 / 331839 : ℚ) = (⟨1248941202185929943154, 1248941202185929943221⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query353_checked : logI (331839 / 331496 : ℚ) = (⟨1250232817760776996004, 1250232817760776996069⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query354_checked : logI (331496 / 331153 : ℚ) = (⟨1251527107597628514596, 1251527107597628514661⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query355_checked : logI (331153 / 330810 : ℚ) = (⟨1252824080010594460254, 1252824080010594460319⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query356_checked : logI (330810 / 330467 : ℚ) = (⟨1254123743348284599894, 1254123743348284599959⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query357_checked : logI (330467 / 330124 : ℚ) = (⟨1255426105993987640164, 1255426105993987640231⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query358_checked : logI (330124 / 329781 : ℚ) = (⟨1256731176365851478876, 1256731176365851478941⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query359_checked : logI (329781 / 329438 : ℚ) = (⟨1258038962917064581898, 1258038962917064581963⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query360_checked : logI (329438 / 329095 : ℚ) = (⟨1259349474136038493688, 1259349474136038493755⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query361_checked : logI (329095 / 328752 : ℚ) = (⟨1260662718546591489776, 1260662718546591489841⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query362_checked : logI (328752 / 328409 : ℚ) = (⟨1261978704708133379486, 1261978704708133379551⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query363_checked : logI (328409 / 328066 : ℚ) = (⟨1263297441215851467380, 1263297441215851467447⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query364_checked : logI (328066 / 327723 : ℚ) = (⟨1264618936700897681842, 1264618936700897681907⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query365_checked : logI (327723 / 327380 : ℚ) = (⟨1265943199830576879404, 1265943199830576879469⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query366_checked : logI (327380 / 327037 : ℚ) = (⟨1267270239308536333432, 1267270239308536333499⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query367_checked : logI (327037 / 326694 : ℚ) = (⟨1268600063874956415842, 1268600063874956415909⟩ : I80) := by
  decide +kernel

def block22 : List (ℚ × I80) :=
  [((332182 / 331839 : ℚ), (⟨1248941202185929943154, 1248941202185929943221⟩ : I80)),
   ((331839 / 331496 : ℚ), (⟨1250232817760776996004, 1250232817760776996069⟩ : I80)),
   ((331496 / 331153 : ℚ), (⟨1251527107597628514596, 1251527107597628514661⟩ : I80)),
   ((331153 / 330810 : ℚ), (⟨1252824080010594460254, 1252824080010594460319⟩ : I80)),
   ((330810 / 330467 : ℚ), (⟨1254123743348284599894, 1254123743348284599959⟩ : I80)),
   ((330467 / 330124 : ℚ), (⟨1255426105993987640164, 1255426105993987640231⟩ : I80)),
   ((330124 / 329781 : ℚ), (⟨1256731176365851478876, 1256731176365851478941⟩ : I80)),
   ((329781 / 329438 : ℚ), (⟨1258038962917064581898, 1258038962917064581963⟩ : I80)),
   ((329438 / 329095 : ℚ), (⟨1259349474136038493688, 1259349474136038493755⟩ : I80)),
   ((329095 / 328752 : ℚ), (⟨1260662718546591489776, 1260662718546591489841⟩ : I80)),
   ((328752 / 328409 : ℚ), (⟨1261978704708133379486, 1261978704708133379551⟩ : I80)),
   ((328409 / 328066 : ℚ), (⟨1263297441215851467380, 1263297441215851467447⟩ : I80)),
   ((328066 / 327723 : ℚ), (⟨1264618936700897681842, 1264618936700897681907⟩ : I80)),
   ((327723 / 327380 : ℚ), (⟨1265943199830576879404, 1265943199830576879469⟩ : I80)),
   ((327380 / 327037 : ℚ), (⟨1267270239308536333432, 1267270239308536333499⟩ : I80)),
   ((327037 / 326694 : ℚ), (⟨1268600063874956415842, 1268600063874956415909⟩ : I80))]

theorem block22_checked : ∀ p ∈ block22, p.2 = logI p.1 := by
  intro p hp
  simp only [block22, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query352_checked.symm
  · exact query353_checked.symm
  · exact query354_checked.symm
  · exact query355_checked.symm
  · exact query356_checked.symm
  · exact query357_checked.symm
  · exact query358_checked.symm
  · exact query359_checked.symm
  · exact query360_checked.symm
  · exact query361_checked.symm
  · exact query362_checked.symm
  · exact query363_checked.symm
  · exact query364_checked.symm
  · exact query365_checked.symm
  · exact query366_checked.symm
  · exact query367_checked.symm

end ImbalancedChen.P2HistoricalLogCache
