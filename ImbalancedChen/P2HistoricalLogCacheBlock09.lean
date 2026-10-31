import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query144_checked : logI (1839568 / 1838917 : ℚ) = (⟨427899375305626101842, 427899375305626101907⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query145_checked : logI (1838917 / 1838266 : ℚ) = (⟨428050883946421769186, 428050883946421769251⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query146_checked : logI (1838266 / 1837615 : ℚ) = (⟨428202499916185104892, 428202499916185104957⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query147_checked : logI (1837615 / 1836964 : ℚ) = (⟨428354223329004543376, 428354223329004543441⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query148_checked : logI (1836964 / 1836313 : ℚ) = (⟨428506054299130274510, 428506054299130274577⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query149_checked : logI (1836313 / 1835662 : ℚ) = (⟨428657992940974530398, 428657992940974530465⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query150_checked : logI (1835662 / 1835011 : ℚ) = (⟨428810039369111872758, 428810039369111872825⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query151_checked : logI (1835011 / 1834360 : ℚ) = (⟨428962193698279480920, 428962193698279480985⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query152_checked : logI (1834360 / 1833709 : ℚ) = (⟨429114456043377440436, 429114456043377440503⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query153_checked : logI (1833709 / 1833058 : ℚ) = (⟨429266826519469032302, 429266826519469032369⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query154_checked : logI (1833058 / 1832407 : ℚ) = (⟨429419305241781022804, 429419305241781022871⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query155_checked : logI (1832407 / 1831756 : ℚ) = (⟨429571892325703953976, 429571892325703954043⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query156_checked : logI (1831756 / 1831105 : ℚ) = (⟨429724587886792434672, 429724587886792434739⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query157_checked : logI (1831105 / 1830454 : ℚ) = (⟨429877392040765432278, 429877392040765432343⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query158_checked : logI (1830454 / 1829803 : ℚ) = (⟨430030304903506565012, 430030304903506565079⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query159_checked : logI (1829803 / 1829152 : ℚ) = (⟨430183326591064394902, 430183326591064394969⟩ : I80) := by
  decide +kernel

def block09 : List (ℚ × I80) :=
  [((1839568 / 1838917 : ℚ), (⟨427899375305626101842, 427899375305626101907⟩ : I80)),
   ((1838917 / 1838266 : ℚ), (⟨428050883946421769186, 428050883946421769251⟩ : I80)),
   ((1838266 / 1837615 : ℚ), (⟨428202499916185104892, 428202499916185104957⟩ : I80)),
   ((1837615 / 1836964 : ℚ), (⟨428354223329004543376, 428354223329004543441⟩ : I80)),
   ((1836964 / 1836313 : ℚ), (⟨428506054299130274510, 428506054299130274577⟩ : I80)),
   ((1836313 / 1835662 : ℚ), (⟨428657992940974530398, 428657992940974530465⟩ : I80)),
   ((1835662 / 1835011 : ℚ), (⟨428810039369111872758, 428810039369111872825⟩ : I80)),
   ((1835011 / 1834360 : ℚ), (⟨428962193698279480920, 428962193698279480985⟩ : I80)),
   ((1834360 / 1833709 : ℚ), (⟨429114456043377440436, 429114456043377440503⟩ : I80)),
   ((1833709 / 1833058 : ℚ), (⟨429266826519469032302, 429266826519469032369⟩ : I80)),
   ((1833058 / 1832407 : ℚ), (⟨429419305241781022804, 429419305241781022871⟩ : I80)),
   ((1832407 / 1831756 : ℚ), (⟨429571892325703953976, 429571892325703954043⟩ : I80)),
   ((1831756 / 1831105 : ℚ), (⟨429724587886792434672, 429724587886792434739⟩ : I80)),
   ((1831105 / 1830454 : ℚ), (⟨429877392040765432278, 429877392040765432343⟩ : I80)),
   ((1830454 / 1829803 : ℚ), (⟨430030304903506565012, 430030304903506565079⟩ : I80)),
   ((1829803 / 1829152 : ℚ), (⟨430183326591064394902, 430183326591064394969⟩ : I80))]

theorem block09_checked : ∀ p ∈ block09, p.2 = logI p.1 := by
  intro p hp
  simp only [block09, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query144_checked.symm
  · exact query145_checked.symm
  · exact query146_checked.symm
  · exact query147_checked.symm
  · exact query148_checked.symm
  · exact query149_checked.symm
  · exact query150_checked.symm
  · exact query151_checked.symm
  · exact query152_checked.symm
  · exact query153_checked.symm
  · exact query154_checked.symm
  · exact query155_checked.symm
  · exact query156_checked.symm
  · exact query157_checked.symm
  · exact query158_checked.symm
  · exact query159_checked.symm

end ImbalancedChen.P2HistoricalLogCache
