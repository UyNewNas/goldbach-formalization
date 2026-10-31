import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query304_checked : logI (348646 / 348303 : ℚ) = (⟨1189933810381434614998, 1189933810381434615063⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query305_checked : logI (348303 / 347960 : ℚ) = (⟨1191106204614539912616, 1191106204614539912683⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query306_checked : logI (347960 / 347617 : ℚ) = (⟨1192280911352628223580, 1192280911352628223647⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query307_checked : logI (347617 / 347274 : ℚ) = (⟨1193457937444452516056, 1193457937444452516121⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query308_checked : logI (347274 / 346931 : ℚ) = (⟨1194637289765836991882, 1194637289765836991949⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query309_checked : logI (346931 / 346588 : ℚ) = (⟨1195818975219810975318, 1195818975219810975383⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query310_checked : logI (346588 / 346245 : ℚ) = (⟨1197003000736743597150, 1197003000736743597215⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query311_checked : logI (346245 / 345902 : ℚ) = (⟨1198189373274479279790, 1198189373274479279857⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query312_checked : logI (345902 / 345559 : ℚ) = (⟨1199378099818474028810, 1199378099818474028877⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query313_checked : logI (345559 / 345216 : ℚ) = (⟨1200569187381932536618, 1200569187381932536683⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query314_checked : logI (345216 / 344873 : ℚ) = (⟨1201762643005946103830, 1201762643005946103897⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query315_checked : logI (344873 / 344530 : ℚ) = (⟨1202958473759631384148, 1202958473759631384213⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query316_checked : logI (344530 / 344187 : ℚ) = (⟨1204156686740269958374, 1204156686740269958439⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query317_checked : logI (344187 / 343844 : ℚ) = (⟨1205357289073448743418, 1205357289073448743483⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query318_checked : logI (343844 / 343501 : ℚ) = (⟨1206560287913201242110, 1206560287913201242177⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query319_checked : logI (343501 / 343158 : ℚ) = (⟨1207765690442149639696, 1207765690442149639761⟩ : I80) := by
  decide +kernel

def block19 : List (ℚ × I80) :=
  [((348646 / 348303 : ℚ), (⟨1189933810381434614998, 1189933810381434615063⟩ : I80)),
   ((348303 / 347960 : ℚ), (⟨1191106204614539912616, 1191106204614539912683⟩ : I80)),
   ((347960 / 347617 : ℚ), (⟨1192280911352628223580, 1192280911352628223647⟩ : I80)),
   ((347617 / 347274 : ℚ), (⟨1193457937444452516056, 1193457937444452516121⟩ : I80)),
   ((347274 / 346931 : ℚ), (⟨1194637289765836991882, 1194637289765836991949⟩ : I80)),
   ((346931 / 346588 : ℚ), (⟨1195818975219810975318, 1195818975219810975383⟩ : I80)),
   ((346588 / 346245 : ℚ), (⟨1197003000736743597150, 1197003000736743597215⟩ : I80)),
   ((346245 / 345902 : ℚ), (⟨1198189373274479279790, 1198189373274479279857⟩ : I80)),
   ((345902 / 345559 : ℚ), (⟨1199378099818474028810, 1199378099818474028877⟩ : I80)),
   ((345559 / 345216 : ℚ), (⟨1200569187381932536618, 1200569187381932536683⟩ : I80)),
   ((345216 / 344873 : ℚ), (⟨1201762643005946103830, 1201762643005946103897⟩ : I80)),
   ((344873 / 344530 : ℚ), (⟨1202958473759631384148, 1202958473759631384213⟩ : I80)),
   ((344530 / 344187 : ℚ), (⟨1204156686740269958374, 1204156686740269958439⟩ : I80)),
   ((344187 / 343844 : ℚ), (⟨1205357289073448743418, 1205357289073448743483⟩ : I80)),
   ((343844 / 343501 : ℚ), (⟨1206560287913201242110, 1206560287913201242177⟩ : I80)),
   ((343501 / 343158 : ℚ), (⟨1207765690442149639696, 1207765690442149639761⟩ : I80))]

theorem block19_checked : ∀ p ∈ block19, p.2 = logI p.1 := by
  intro p hp
  simp only [block19, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query304_checked.symm
  · exact query305_checked.symm
  · exact query306_checked.symm
  · exact query307_checked.symm
  · exact query308_checked.symm
  · exact query309_checked.symm
  · exact query310_checked.symm
  · exact query311_checked.symm
  · exact query312_checked.symm
  · exact query313_checked.symm
  · exact query314_checked.symm
  · exact query315_checked.symm
  · exact query316_checked.symm
  · exact query317_checked.symm
  · exact query318_checked.symm
  · exact query319_checked.symm

end ImbalancedChen.P2HistoricalLogCache
