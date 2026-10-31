import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query016_checked : logI (1922896 / 1922245 : ℚ) = (⟨409353371483001443120, 409353371483001443187⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query017_checked : logI (1922245 / 1921594 : ℚ) = (⟨409492029241523825182, 409492029241523825249⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query018_checked : logI (1921594 / 1920943 : ℚ) = (⟨409630780965260739306, 409630780965260739373⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query019_checked : logI (1920943 / 1920292 : ℚ) = (⟨409769626749761700686, 409769626749761700753⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query020_checked : logI (1920292 / 1919641 : ℚ) = (⟨409908566690705815824, 409908566690705815891⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query021_checked : logI (1919641 / 1918990 : ℚ) = (⟨410047600883902002280, 410047600883902002347⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query022_checked : logI (1918990 / 1918339 : ℚ) = (⟨410186729425289208930, 410186729425289208995⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query023_checked : logI (1918339 / 1917688 : ℚ) = (⟨410325952410936636598, 410325952410936636665⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query024_checked : logI (1917688 / 1917037 : ℚ) = (⟨410465269937043959214, 410465269937043959281⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query025_checked : logI (1917037 / 1916386 : ℚ) = (⟨410604682099941545364, 410604682099941545429⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query026_checked : logI (1916386 / 1915735 : ℚ) = (⟨410744188996090680326, 410744188996090680391⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query027_checked : logI (1915735 / 1915084 : ℚ) = (⟨410883790722083788534, 410883790722083788599⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query028_checked : logI (1915084 / 1914433 : ℚ) = (⟨411023487374644656516, 411023487374644656583⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query029_checked : logI (1914433 / 1913782 : ℚ) = (⟨411163279050628656286, 411163279050628656353⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query030_checked : logI (1913782 / 1913131 : ℚ) = (⟨411303165847022969176, 411303165847022969243⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query031_checked : logI (1913131 / 1912480 : ℚ) = (⟨411443147860946810130, 411443147860946810195⟩ : I80) := by
  decide +kernel

def block01 : List (ℚ × I80) :=
  [((1922896 / 1922245 : ℚ), (⟨409353371483001443120, 409353371483001443187⟩ : I80)),
   ((1922245 / 1921594 : ℚ), (⟨409492029241523825182, 409492029241523825249⟩ : I80)),
   ((1921594 / 1920943 : ℚ), (⟨409630780965260739306, 409630780965260739373⟩ : I80)),
   ((1920943 / 1920292 : ℚ), (⟨409769626749761700686, 409769626749761700753⟩ : I80)),
   ((1920292 / 1919641 : ℚ), (⟨409908566690705815824, 409908566690705815891⟩ : I80)),
   ((1919641 / 1918990 : ℚ), (⟨410047600883902002280, 410047600883902002347⟩ : I80)),
   ((1918990 / 1918339 : ℚ), (⟨410186729425289208930, 410186729425289208995⟩ : I80)),
   ((1918339 / 1917688 : ℚ), (⟨410325952410936636598, 410325952410936636665⟩ : I80)),
   ((1917688 / 1917037 : ℚ), (⟨410465269937043959214, 410465269937043959281⟩ : I80)),
   ((1917037 / 1916386 : ℚ), (⟨410604682099941545364, 410604682099941545429⟩ : I80)),
   ((1916386 / 1915735 : ℚ), (⟨410744188996090680326, 410744188996090680391⟩ : I80)),
   ((1915735 / 1915084 : ℚ), (⟨410883790722083788534, 410883790722083788599⟩ : I80)),
   ((1915084 / 1914433 : ℚ), (⟨411023487374644656516, 411023487374644656583⟩ : I80)),
   ((1914433 / 1913782 : ℚ), (⟨411163279050628656286, 411163279050628656353⟩ : I80)),
   ((1913782 / 1913131 : ℚ), (⟨411303165847022969176, 411303165847022969243⟩ : I80)),
   ((1913131 / 1912480 : ℚ), (⟨411443147860946810130, 411443147860946810195⟩ : I80))]

theorem block01_checked : ∀ p ∈ block01, p.2 = logI p.1 := by
  intro p hp
  simp only [block01, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query016_checked.symm
  · exact query017_checked.symm
  · exact query018_checked.symm
  · exact query019_checked.symm
  · exact query020_checked.symm
  · exact query021_checked.symm
  · exact query022_checked.symm
  · exact query023_checked.symm
  · exact query024_checked.symm
  · exact query025_checked.symm
  · exact query026_checked.symm
  · exact query027_checked.symm
  · exact query028_checked.symm
  · exact query029_checked.symm
  · exact query030_checked.symm
  · exact query031_checked.symm

end ImbalancedChen.P2HistoricalLogCache
