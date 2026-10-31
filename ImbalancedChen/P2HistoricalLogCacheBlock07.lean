import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query112_checked : logI (1860400 / 1859749 : ℚ) = (⟨423107094152706162942, 423107094152706163009⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query113_checked : logI (1859749 / 1859098 : ℚ) = (⟨423255227552074051420, 423255227552074051485⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query114_checked : logI (1859098 / 1858447 : ℚ) = (⟨423403464713301925112, 423403464713301925177⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query115_checked : logI (1858447 / 1857796 : ℚ) = (⟨423551805745449886292, 423551805745449886357⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query116_checked : logI (1857796 / 1857145 : ℚ) = (⟨423700250757730929314, 423700250757730929381⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query117_checked : logI (1857145 / 1856494 : ℚ) = (⟨423848799859511208636, 423848799859511208701⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query118_checked : logI (1856494 / 1855843 : ℚ) = (⟨423997453160310307386, 423997453160310307451⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query119_checked : logI (1855843 / 1855192 : ℚ) = (⟨424146210769801506520, 424146210769801506585⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query120_checked : logI (1855192 / 1854541 : ℚ) = (⟨424295072797812054538, 424295072797812054603⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query121_checked : logI (1854541 / 1853890 : ℚ) = (⟨424444039354323437772, 424444039354323437837⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query122_checked : logI (1853890 / 1853239 : ℚ) = (⟨424593110549471651228, 424593110549471651295⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query123_checked : logI (1853239 / 1852588 : ℚ) = (⟨424742286493547470024, 424742286493547470089⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query124_checked : logI (1852588 / 1851937 : ℚ) = (⟨424891567296996721370, 424891567296996721435⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query125_checked : logI (1851937 / 1851286 : ℚ) = (⟨425040953070420557156, 425040953070420557221⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query126_checked : logI (1851286 / 1850635 : ℚ) = (⟨425190443924575727084, 425190443924575727151⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query127_checked : logI (1850635 / 1849984 : ℚ) = (⟨425340039970374852404, 425340039970374852471⟩ : I80) := by
  decide +kernel

def block07 : List (ℚ × I80) :=
  [((1860400 / 1859749 : ℚ), (⟨423107094152706162942, 423107094152706163009⟩ : I80)),
   ((1859749 / 1859098 : ℚ), (⟨423255227552074051420, 423255227552074051485⟩ : I80)),
   ((1859098 / 1858447 : ℚ), (⟨423403464713301925112, 423403464713301925177⟩ : I80)),
   ((1858447 / 1857796 : ℚ), (⟨423551805745449886292, 423551805745449886357⟩ : I80)),
   ((1857796 / 1857145 : ℚ), (⟨423700250757730929314, 423700250757730929381⟩ : I80)),
   ((1857145 / 1856494 : ℚ), (⟨423848799859511208636, 423848799859511208701⟩ : I80)),
   ((1856494 / 1855843 : ℚ), (⟨423997453160310307386, 423997453160310307451⟩ : I80)),
   ((1855843 / 1855192 : ℚ), (⟨424146210769801506520, 424146210769801506585⟩ : I80)),
   ((1855192 / 1854541 : ℚ), (⟨424295072797812054538, 424295072797812054603⟩ : I80)),
   ((1854541 / 1853890 : ℚ), (⟨424444039354323437772, 424444039354323437837⟩ : I80)),
   ((1853890 / 1853239 : ℚ), (⟨424593110549471651228, 424593110549471651295⟩ : I80)),
   ((1853239 / 1852588 : ℚ), (⟨424742286493547470024, 424742286493547470089⟩ : I80)),
   ((1852588 / 1851937 : ℚ), (⟨424891567296996721370, 424891567296996721435⟩ : I80)),
   ((1851937 / 1851286 : ℚ), (⟨425040953070420557156, 425040953070420557221⟩ : I80)),
   ((1851286 / 1850635 : ℚ), (⟨425190443924575727084, 425190443924575727151⟩ : I80)),
   ((1850635 / 1849984 : ℚ), (⟨425340039970374852404, 425340039970374852471⟩ : I80))]

theorem block07_checked : ∀ p ∈ block07, p.2 = logI p.1 := by
  intro p hp
  simp only [block07, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query112_checked.symm
  · exact query113_checked.symm
  · exact query114_checked.symm
  · exact query115_checked.symm
  · exact query116_checked.symm
  · exact query117_checked.symm
  · exact query118_checked.symm
  · exact query119_checked.symm
  · exact query120_checked.symm
  · exact query121_checked.symm
  · exact query122_checked.symm
  · exact query123_checked.symm
  · exact query124_checked.symm
  · exact query125_checked.symm
  · exact query126_checked.symm
  · exact query127_checked.symm

end ImbalancedChen.P2HistoricalLogCache
