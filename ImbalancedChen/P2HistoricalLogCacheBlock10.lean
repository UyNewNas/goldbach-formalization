import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query160_checked : logI (1829152 / 1828501 : ℚ) = (⟨430336457219652721332, 430336457219652721397⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query161_checked : logI (1828501 / 1827850 : ℚ) = (⟨430489696905650875252, 430489696905650875319⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query162_checked : logI (1827850 / 1827199 : ℚ) = (⟨430643045765604014002, 430643045765604014069⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query163_checked : logI (1827199 / 1826548 : ℚ) = (⟨430796503916223416776, 430796503916223416841⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query164_checked : logI (1826548 / 1825897 : ℚ) = (⟨430950071474386780698, 430950071474386780763⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query165_checked : logI (1825897 / 1825246 : ℚ) = (⟨431103748557138517572, 431103748557138517637⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query166_checked : logI (1825246 / 1824595 : ℚ) = (⟨431257535281690051214, 431257535281690051279⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query167_checked : logI (1824595 / 1823944 : ℚ) = (⟨431411431765420115456, 431411431765420115523⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query168_checked : logI (1823944 / 1823293 : ℚ) = (⟨431565438125875052798, 431565438125875052863⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query169_checked : logI (1823293 / 1822642 : ℚ) = (⟨431719554480769113644, 431719554480769113709⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query170_checked : logI (1822642 / 1821991 : ℚ) = (⟨431873780947984756256, 431873780947984756323⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query171_checked : logI (1821991 / 1821340 : ℚ) = (⟨432028117645572947296, 432028117645572947361⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query172_checked : logI (1821340 / 1820689 : ℚ) = (⟨432182564691753463010, 432182564691753463077⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query173_checked : logI (1820689 / 1820038 : ℚ) = (⟨432337122204915191118, 432337122204915191185⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query174_checked : logI (1820038 / 1819387 : ℚ) = (⟨432491790303616433272, 432491790303616433339⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query175_checked : logI (1819387 / 1818736 : ℚ) = (⟨432646569106585208232, 432646569106585208297⟩ : I80) := by
  decide +kernel

def block10 : List (ℚ × I80) :=
  [((1829152 / 1828501 : ℚ), (⟨430336457219652721332, 430336457219652721397⟩ : I80)),
   ((1828501 / 1827850 : ℚ), (⟨430489696905650875252, 430489696905650875319⟩ : I80)),
   ((1827850 / 1827199 : ℚ), (⟨430643045765604014002, 430643045765604014069⟩ : I80)),
   ((1827199 / 1826548 : ℚ), (⟨430796503916223416776, 430796503916223416841⟩ : I80)),
   ((1826548 / 1825897 : ℚ), (⟨430950071474386780698, 430950071474386780763⟩ : I80)),
   ((1825897 / 1825246 : ℚ), (⟨431103748557138517572, 431103748557138517637⟩ : I80)),
   ((1825246 / 1824595 : ℚ), (⟨431257535281690051214, 431257535281690051279⟩ : I80)),
   ((1824595 / 1823944 : ℚ), (⟨431411431765420115456, 431411431765420115523⟩ : I80)),
   ((1823944 / 1823293 : ℚ), (⟨431565438125875052798, 431565438125875052863⟩ : I80)),
   ((1823293 / 1822642 : ℚ), (⟨431719554480769113644, 431719554480769113709⟩ : I80)),
   ((1822642 / 1821991 : ℚ), (⟨431873780947984756256, 431873780947984756323⟩ : I80)),
   ((1821991 / 1821340 : ℚ), (⟨432028117645572947296, 432028117645572947361⟩ : I80)),
   ((1821340 / 1820689 : ℚ), (⟨432182564691753463010, 432182564691753463077⟩ : I80)),
   ((1820689 / 1820038 : ℚ), (⟨432337122204915191118, 432337122204915191185⟩ : I80)),
   ((1820038 / 1819387 : ℚ), (⟨432491790303616433272, 432491790303616433339⟩ : I80)),
   ((1819387 / 1818736 : ℚ), (⟨432646569106585208232, 432646569106585208297⟩ : I80))]

theorem block10_checked : ∀ p ∈ block10, p.2 = logI p.1 := by
  intro p hp
  simp only [block10, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query160_checked.symm
  · exact query161_checked.symm
  · exact query162_checked.symm
  · exact query163_checked.symm
  · exact query164_checked.symm
  · exact query165_checked.symm
  · exact query166_checked.symm
  · exact query167_checked.symm
  · exact query168_checked.symm
  · exact query169_checked.symm
  · exact query170_checked.symm
  · exact query171_checked.symm
  · exact query172_checked.symm
  · exact query173_checked.symm
  · exact query174_checked.symm
  · exact query175_checked.symm

end ImbalancedChen.P2HistoricalLogCache
