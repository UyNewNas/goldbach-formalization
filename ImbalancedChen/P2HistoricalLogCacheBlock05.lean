import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query080_checked : logI (1881232 / 1880581 : ℚ) = (⟨418420966925035731548, 418420966925035731613⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query081_checked : logI (1880581 / 1879930 : ℚ) = (⟨418565836627535959854, 418565836627535959921⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query082_checked : logI (1879930 / 1879279 : ℚ) = (⟨418710806681125106048, 418710806681125106115⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query083_checked : logI (1879279 / 1878628 : ℚ) = (⟨418855877190108936348, 418855877190108936413⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query084_checked : logI (1878628 / 1877977 : ℚ) = (⟨419001048258937822118, 419001048258937822183⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query085_checked : logI (1877977 / 1877326 : ℚ) = (⟨419146319992206990568, 419146319992206990635⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query086_checked : logI (1877326 / 1876675 : ℚ) = (⟨419291692494656775944, 419291692494656776011⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query087_checked : logI (1876675 / 1876024 : ℚ) = (⟨419437165871172871258, 419437165871172871325⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query088_checked : logI (1876024 / 1875373 : ℚ) = (⟨419582740226786580532, 419582740226786580597⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query089_checked : logI (1875373 / 1874722 : ℚ) = (⟨419728415666675071576, 419728415666675071641⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query090_checked : logI (1874722 / 1874071 : ℚ) = (⟨419874192296161629288, 419874192296161629355⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query091_checked : logI (1874071 / 1873420 : ℚ) = (⟨420020070220715909488, 420020070220715909553⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query092_checked : logI (1873420 / 1872769 : ℚ) = (⟨420166049545954193260, 420166049545954193327⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query093_checked : logI (1872769 / 1872118 : ℚ) = (⟨420312130377639641868, 420312130377639641935⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query094_checked : logI (1872118 / 1871467 : ℚ) = (⟨420458312821682552152, 420458312821682552217⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query095_checked : logI (1871467 / 1870816 : ℚ) = (⟨420604596984140612492, 420604596984140612559⟩ : I80) := by
  decide +kernel

def block05 : List (ℚ × I80) :=
  [((1881232 / 1880581 : ℚ), (⟨418420966925035731548, 418420966925035731613⟩ : I80)),
   ((1880581 / 1879930 : ℚ), (⟨418565836627535959854, 418565836627535959921⟩ : I80)),
   ((1879930 / 1879279 : ℚ), (⟨418710806681125106048, 418710806681125106115⟩ : I80)),
   ((1879279 / 1878628 : ℚ), (⟨418855877190108936348, 418855877190108936413⟩ : I80)),
   ((1878628 / 1877977 : ℚ), (⟨419001048258937822118, 419001048258937822183⟩ : I80)),
   ((1877977 / 1877326 : ℚ), (⟨419146319992206990568, 419146319992206990635⟩ : I80)),
   ((1877326 / 1876675 : ℚ), (⟨419291692494656775944, 419291692494656776011⟩ : I80)),
   ((1876675 / 1876024 : ℚ), (⟨419437165871172871258, 419437165871172871325⟩ : I80)),
   ((1876024 / 1875373 : ℚ), (⟨419582740226786580532, 419582740226786580597⟩ : I80)),
   ((1875373 / 1874722 : ℚ), (⟨419728415666675071576, 419728415666675071641⟩ : I80)),
   ((1874722 / 1874071 : ℚ), (⟨419874192296161629288, 419874192296161629355⟩ : I80)),
   ((1874071 / 1873420 : ℚ), (⟨420020070220715909488, 420020070220715909553⟩ : I80)),
   ((1873420 / 1872769 : ℚ), (⟨420166049545954193260, 420166049545954193327⟩ : I80)),
   ((1872769 / 1872118 : ℚ), (⟨420312130377639641868, 420312130377639641935⟩ : I80)),
   ((1872118 / 1871467 : ℚ), (⟨420458312821682552152, 420458312821682552217⟩ : I80)),
   ((1871467 / 1870816 : ℚ), (⟨420604596984140612492, 420604596984140612559⟩ : I80))]

theorem block05_checked : ∀ p ∈ block05, p.2 = logI p.1 := by
  intro p hp
  simp only [block05, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query080_checked.symm
  · exact query081_checked.symm
  · exact query082_checked.symm
  · exact query083_checked.symm
  · exact query084_checked.symm
  · exact query085_checked.symm
  · exact query086_checked.symm
  · exact query087_checked.symm
  · exact query088_checked.symm
  · exact query089_checked.symm
  · exact query090_checked.symm
  · exact query091_checked.symm
  · exact query092_checked.symm
  · exact query093_checked.symm
  · exact query094_checked.symm
  · exact query095_checked.symm

end ImbalancedChen.P2HistoricalLogCache
