import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query176_checked : logI (1818736 / 1818085 : ℚ) = (⟨432801458732719555638, 432801458732719555705⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query177_checked : logI (1818085 / 1817434 : ℚ) = (⟨432956459301087840486, 432956459301087840553⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query178_checked : logI (1817434 / 1816783 : ℚ) = (⟨433111570930929058214, 433111570930929058279⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query179_checked : logI (1816783 / 1816132 : ℚ) = (⟨433266793741653140472, 433266793741653140539⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query180_checked : logI (1816132 / 1815481 : ℚ) = (⟨433422127852841261538, 433422127852841261603⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query181_checked : logI (1815481 / 1814830 : ℚ) = (⟨433577573384246145396, 433577573384246145463⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query182_checked : logI (1814830 / 1814179 : ℚ) = (⟨433733130455792373482, 433733130455792373549⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query183_checked : logI (1814179 / 1813528 : ℚ) = (⟨433888799187576693072, 433888799187576693139⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query184_checked : logI (1813528 / 1812877 : ℚ) = (⟨434044579699868326368, 434044579699868326435⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query185_checked : logI (1812877 / 1812226 : ℚ) = (⟨434200472113109280206, 434200472113109280273⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query186_checked : logI (389120 / 388777 : ℚ) = (⟨1066109222688470343954, 1066109222688470344021⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query187_checked : logI (388777 / 388434 : ℚ) = (⟨1067050216860816536576, 1067050216860816536641⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query188_checked : logI (388434 / 388091 : ℚ) = (⟨1067992873625167019024, 1067992873625167019089⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query189_checked : logI (388091 / 387748 : ℚ) = (⟨1068937197391734780516, 1068937197391734780583⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query190_checked : logI (387748 / 387405 : ℚ) = (⟨1069883192586344732540, 1069883192586344732607⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query191_checked : logI (387405 / 387062 : ℚ) = (⟨1070830863650502851780, 1070830863650502851845⟩ : I80) := by
  decide +kernel

def block11 : List (ℚ × I80) :=
  [((1818736 / 1818085 : ℚ), (⟨432801458732719555638, 432801458732719555705⟩ : I80)),
   ((1818085 / 1817434 : ℚ), (⟨432956459301087840486, 432956459301087840553⟩ : I80)),
   ((1817434 / 1816783 : ℚ), (⟨433111570930929058214, 433111570930929058279⟩ : I80)),
   ((1816783 / 1816132 : ℚ), (⟨433266793741653140472, 433266793741653140539⟩ : I80)),
   ((1816132 / 1815481 : ℚ), (⟨433422127852841261538, 433422127852841261603⟩ : I80)),
   ((1815481 / 1814830 : ℚ), (⟨433577573384246145396, 433577573384246145463⟩ : I80)),
   ((1814830 / 1814179 : ℚ), (⟨433733130455792373482, 433733130455792373549⟩ : I80)),
   ((1814179 / 1813528 : ℚ), (⟨433888799187576693072, 433888799187576693139⟩ : I80)),
   ((1813528 / 1812877 : ℚ), (⟨434044579699868326368, 434044579699868326435⟩ : I80)),
   ((1812877 / 1812226 : ℚ), (⟨434200472113109280206, 434200472113109280273⟩ : I80)),
   ((389120 / 388777 : ℚ), (⟨1066109222688470343954, 1066109222688470344021⟩ : I80)),
   ((388777 / 388434 : ℚ), (⟨1067050216860816536576, 1067050216860816536641⟩ : I80)),
   ((388434 / 388091 : ℚ), (⟨1067992873625167019024, 1067992873625167019089⟩ : I80)),
   ((388091 / 387748 : ℚ), (⟨1068937197391734780516, 1068937197391734780583⟩ : I80)),
   ((387748 / 387405 : ℚ), (⟨1069883192586344732540, 1069883192586344732607⟩ : I80)),
   ((387405 / 387062 : ℚ), (⟨1070830863650502851780, 1070830863650502851845⟩ : I80))]

theorem block11_checked : ∀ p ∈ block11, p.2 = logI p.1 := by
  intro p hp
  simp only [block11, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query176_checked.symm
  · exact query177_checked.symm
  · exact query178_checked.symm
  · exact query179_checked.symm
  · exact query180_checked.symm
  · exact query181_checked.symm
  · exact query182_checked.symm
  · exact query183_checked.symm
  · exact query184_checked.symm
  · exact query185_checked.symm
  · exact query186_checked.symm
  · exact query187_checked.symm
  · exact query188_checked.symm
  · exact query189_checked.symm
  · exact query190_checked.symm
  · exact query191_checked.symm

end ImbalancedChen.P2HistoricalLogCache
