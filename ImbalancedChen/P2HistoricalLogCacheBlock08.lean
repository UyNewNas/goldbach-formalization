import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query128_checked : logI (1849984 / 1849333 : ℚ) = (⟨425489741318886700196, 425489741318886700263⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query129_checked : logI (1849333 / 1848682 : ℚ) = (⟨425639548081336458268, 425639548081336458333⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query130_checked : logI (1848682 / 1848031 : ℚ) = (⟨425789460369106010604, 425789460369106010669⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query131_checked : logI (1848031 / 1847380 : ℚ) = (⟨425939478293734213414, 425939478293734213479⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query132_checked : logI (1847380 / 1846729 : ℚ) = (⟨426089601966917171754, 426089601966917171821⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query133_checked : logI (1846729 / 1846078 : ℚ) = (⟨426239831500508516752, 426239831500508516819⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query134_checked : logI (1846078 / 1845427 : ℚ) = (⟨426390167006519683388, 426390167006519683453⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query135_checked : logI (1845427 / 1844776 : ℚ) = (⟨426540608597120188892, 426540608597120188957⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query136_checked : logI (1844776 / 1844125 : ℚ) = (⟨426691156384637911714, 426691156384637911779⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query137_checked : logI (1844125 / 1843474 : ℚ) = (⟨426841810481559371102, 426841810481559371167⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query138_checked : logI (1843474 / 1842823 : ℚ) = (⟨426992571000530007250, 426992571000530007315⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query139_checked : logI (1842823 / 1842172 : ℚ) = (⟨427143438054354462054, 427143438054354462121⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query140_checked : logI (1842172 / 1841521 : ℚ) = (⟨427294411755996860470, 427294411755996860537⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query141_checked : logI (1841521 / 1840870 : ℚ) = (⟨427445492218581092446, 427445492218581092511⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query142_checked : logI (1840870 / 1840219 : ℚ) = (⟨427596679555391095474, 427596679555391095539⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query143_checked : logI (1840219 / 1839568 : ℚ) = (⟨427747973879871137734, 427747973879871137801⟩ : I80) := by
  decide +kernel

def block08 : List (ℚ × I80) :=
  [((1849984 / 1849333 : ℚ), (⟨425489741318886700196, 425489741318886700263⟩ : I80)),
   ((1849333 / 1848682 : ℚ), (⟨425639548081336458268, 425639548081336458333⟩ : I80)),
   ((1848682 / 1848031 : ℚ), (⟨425789460369106010604, 425789460369106010669⟩ : I80)),
   ((1848031 / 1847380 : ℚ), (⟨425939478293734213414, 425939478293734213479⟩ : I80)),
   ((1847380 / 1846729 : ℚ), (⟨426089601966917171754, 426089601966917171821⟩ : I80)),
   ((1846729 / 1846078 : ℚ), (⟨426239831500508516752, 426239831500508516819⟩ : I80)),
   ((1846078 / 1845427 : ℚ), (⟨426390167006519683388, 426390167006519683453⟩ : I80)),
   ((1845427 / 1844776 : ℚ), (⟨426540608597120188892, 426540608597120188957⟩ : I80)),
   ((1844776 / 1844125 : ℚ), (⟨426691156384637911714, 426691156384637911779⟩ : I80)),
   ((1844125 / 1843474 : ℚ), (⟨426841810481559371102, 426841810481559371167⟩ : I80)),
   ((1843474 / 1842823 : ℚ), (⟨426992571000530007250, 426992571000530007315⟩ : I80)),
   ((1842823 / 1842172 : ℚ), (⟨427143438054354462054, 427143438054354462121⟩ : I80)),
   ((1842172 / 1841521 : ℚ), (⟨427294411755996860470, 427294411755996860537⟩ : I80)),
   ((1841521 / 1840870 : ℚ), (⟨427445492218581092446, 427445492218581092511⟩ : I80)),
   ((1840870 / 1840219 : ℚ), (⟨427596679555391095474, 427596679555391095539⟩ : I80)),
   ((1840219 / 1839568 : ℚ), (⟨427747973879871137734, 427747973879871137801⟩ : I80))]

theorem block08_checked : ∀ p ∈ block08, p.2 = logI p.1 := by
  intro p hp
  simp only [block08, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query128_checked.symm
  · exact query129_checked.symm
  · exact query130_checked.symm
  · exact query131_checked.symm
  · exact query132_checked.symm
  · exact query133_checked.symm
  · exact query134_checked.symm
  · exact query135_checked.symm
  · exact query136_checked.symm
  · exact query137_checked.symm
  · exact query138_checked.symm
  · exact query139_checked.symm
  · exact query140_checked.symm
  · exact query141_checked.symm
  · exact query142_checked.symm
  · exact query143_checked.symm

end ImbalancedChen.P2HistoricalLogCache
