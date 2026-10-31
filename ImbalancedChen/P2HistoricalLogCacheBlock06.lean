import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query096_checked : logI (1870816 / 1870165 : ℚ) = (⟨420750982971219159302, 420750982971219159367⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query097_checked : logI (1870165 / 1869514 : ℚ) = (⟨420897470889271434042, 420897470889271434109⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query098_checked : logI (1869514 / 1868863 : ℚ) = (⟨421044060844798840792, 421044060844798840857⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query099_checked : logI (1868863 / 1868212 : ℚ) = (⟨421190752944451204340, 421190752944451204405⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query100_checked : logI (1868212 / 1867561 : ℚ) = (⟨421337547295027028832, 421337547295027028897⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query101_checked : logI (1867561 / 1866910 : ℚ) = (⟨421484444003473756952, 421484444003473757017⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query102_checked : logI (1866910 / 1866259 : ℚ) = (⟨421631443176888029634, 421631443176888029699⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query103_checked : logI (1866259 / 1865608 : ℚ) = (⟨421778544922515946340, 421778544922515946407⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query104_checked : logI (1865608 / 1864957 : ℚ) = (⟨421925749347753325870, 421925749347753325937⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query105_checked : logI (1864957 / 1864306 : ℚ) = (⟨422073056560145967712, 422073056560145967777⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query106_checked : logI (1864306 / 1863655 : ℚ) = (⟨422220466667389913960, 422220466667389914027⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query107_checked : logI (1863655 / 1863004 : ℚ) = (⟨422367979777331711758, 422367979777331711823⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query108_checked : logI (1863004 / 1862353 : ℚ) = (⟨422515595997968676308, 422515595997968676375⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query109_checked : logI (1862353 / 1861702 : ℚ) = (⟨422663315437449154438, 422663315437449154505⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query110_checked : logI (1861702 / 1861051 : ℚ) = (⟨422811138204072788692, 422811138204072788757⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query111_checked : logI (1861051 / 1860400 : ℚ) = (⟨422959064406290782012, 422959064406290782079⟩ : I80) := by
  decide +kernel

def block06 : List (ℚ × I80) :=
  [((1870816 / 1870165 : ℚ), (⟨420750982971219159302, 420750982971219159367⟩ : I80)),
   ((1870165 / 1869514 : ℚ), (⟨420897470889271434042, 420897470889271434109⟩ : I80)),
   ((1869514 / 1868863 : ℚ), (⟨421044060844798840792, 421044060844798840857⟩ : I80)),
   ((1868863 / 1868212 : ℚ), (⟨421190752944451204340, 421190752944451204405⟩ : I80)),
   ((1868212 / 1867561 : ℚ), (⟨421337547295027028832, 421337547295027028897⟩ : I80)),
   ((1867561 / 1866910 : ℚ), (⟨421484444003473756952, 421484444003473757017⟩ : I80)),
   ((1866910 / 1866259 : ℚ), (⟨421631443176888029634, 421631443176888029699⟩ : I80)),
   ((1866259 / 1865608 : ℚ), (⟨421778544922515946340, 421778544922515946407⟩ : I80)),
   ((1865608 / 1864957 : ℚ), (⟨421925749347753325870, 421925749347753325937⟩ : I80)),
   ((1864957 / 1864306 : ℚ), (⟨422073056560145967712, 422073056560145967777⟩ : I80)),
   ((1864306 / 1863655 : ℚ), (⟨422220466667389913960, 422220466667389914027⟩ : I80)),
   ((1863655 / 1863004 : ℚ), (⟨422367979777331711758, 422367979777331711823⟩ : I80)),
   ((1863004 / 1862353 : ℚ), (⟨422515595997968676308, 422515595997968676375⟩ : I80)),
   ((1862353 / 1861702 : ℚ), (⟨422663315437449154438, 422663315437449154505⟩ : I80)),
   ((1861702 / 1861051 : ℚ), (⟨422811138204072788692, 422811138204072788757⟩ : I80)),
   ((1861051 / 1860400 : ℚ), (⟨422959064406290782012, 422959064406290782079⟩ : I80))]

theorem block06_checked : ∀ p ∈ block06, p.2 = logI p.1 := by
  intro p hp
  simp only [block06, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query096_checked.symm
  · exact query097_checked.symm
  · exact query098_checked.symm
  · exact query099_checked.symm
  · exact query100_checked.symm
  · exact query101_checked.symm
  · exact query102_checked.symm
  · exact query103_checked.symm
  · exact query104_checked.symm
  · exact query105_checked.symm
  · exact query106_checked.symm
  · exact query107_checked.symm
  · exact query108_checked.symm
  · exact query109_checked.symm
  · exact query110_checked.symm
  · exact query111_checked.symm

end ImbalancedChen.P2HistoricalLogCache
