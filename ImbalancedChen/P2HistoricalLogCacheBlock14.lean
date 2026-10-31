import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query224_checked : logI (376086 / 375743 : ℚ) = (⟨1103074196118209477168, 1103074196118209477233⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query225_checked : logI (375743 / 375400 : ℚ) = (⟨1104081606163541194396, 1104081606163541194463⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query226_checked : logI (375400 / 375057 : ℚ) = (⟨1105090857975783827276, 1105090857975783827341⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query227_checked : logI (375057 / 374714 : ℚ) = (⟨1106101956610290755556, 1106101956610290755621⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query228_checked : logI (374714 / 374371 : ℚ) = (⟨1107114907140933810842, 1107114907140933810909⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query229_checked : logI (374371 / 374028 : ℚ) = (⟨1108129714660188148866, 1108129714660188148931⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query230_checked : logI (374028 / 373685 : ℚ) = (⟨1109146384279217588946, 1109146384279217589013⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query231_checked : logI (373685 / 373342 : ℚ) = (⟨1110164921127960423670, 1110164921127960423737⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query232_checked : logI (373342 / 372999 : ℚ) = (⟨1111185330355215701796, 1111185330355215701863⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query233_checked : logI (372999 / 372656 : ℚ) = (⟨1112207617128729987434, 1112207617128729987499⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query234_checked : logI (372656 / 372313 : ℚ) = (⟨1113231786635284598590, 1113231786635284598657⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query235_checked : logI (372313 / 371970 : ℚ) = (⟨1114257844080783328142, 1114257844080783328207⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query236_checked : logI (371970 / 371627 : ℚ) = (⟨1115285794690340650376, 1115285794690340650443⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query237_checked : logI (371627 / 371284 : ℚ) = (⟨1116315643708370416220, 1116315643708370416287⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query238_checked : logI (371284 / 370941 : ℚ) = (⟨1117347396398675040352, 1117347396398675040417⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query239_checked : logI (370941 / 370598 : ℚ) = (⟨1118381058044535183300, 1118381058044535183365⟩ : I80) := by
  decide +kernel

def block14 : List (ℚ × I80) :=
  [((376086 / 375743 : ℚ), (⟨1103074196118209477168, 1103074196118209477233⟩ : I80)),
   ((375743 / 375400 : ℚ), (⟨1104081606163541194396, 1104081606163541194463⟩ : I80)),
   ((375400 / 375057 : ℚ), (⟨1105090857975783827276, 1105090857975783827341⟩ : I80)),
   ((375057 / 374714 : ℚ), (⟨1106101956610290755556, 1106101956610290755621⟩ : I80)),
   ((374714 / 374371 : ℚ), (⟨1107114907140933810842, 1107114907140933810909⟩ : I80)),
   ((374371 / 374028 : ℚ), (⟨1108129714660188148866, 1108129714660188148931⟩ : I80)),
   ((374028 / 373685 : ℚ), (⟨1109146384279217588946, 1109146384279217589013⟩ : I80)),
   ((373685 / 373342 : ℚ), (⟨1110164921127960423670, 1110164921127960423737⟩ : I80)),
   ((373342 / 372999 : ℚ), (⟨1111185330355215701796, 1111185330355215701863⟩ : I80)),
   ((372999 / 372656 : ℚ), (⟨1112207617128729987434, 1112207617128729987499⟩ : I80)),
   ((372656 / 372313 : ℚ), (⟨1113231786635284598590, 1113231786635284598657⟩ : I80)),
   ((372313 / 371970 : ℚ), (⟨1114257844080783328142, 1114257844080783328207⟩ : I80)),
   ((371970 / 371627 : ℚ), (⟨1115285794690340650376, 1115285794690340650443⟩ : I80)),
   ((371627 / 371284 : ℚ), (⟨1116315643708370416220, 1116315643708370416287⟩ : I80)),
   ((371284 / 370941 : ℚ), (⟨1117347396398675040352, 1117347396398675040417⟩ : I80)),
   ((370941 / 370598 : ℚ), (⟨1118381058044535183300, 1118381058044535183365⟩ : I80))]

theorem block14_checked : ∀ p ∈ block14, p.2 = logI p.1 := by
  intro p hp
  simp only [block14, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query224_checked.symm
  · exact query225_checked.symm
  · exact query226_checked.symm
  · exact query227_checked.symm
  · exact query228_checked.symm
  · exact query229_checked.symm
  · exact query230_checked.symm
  · exact query231_checked.symm
  · exact query232_checked.symm
  · exact query233_checked.symm
  · exact query234_checked.symm
  · exact query235_checked.symm
  · exact query236_checked.symm
  · exact query237_checked.symm
  · exact query238_checked.symm
  · exact query239_checked.symm

end ImbalancedChen.P2HistoricalLogCache
