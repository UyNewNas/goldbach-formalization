import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query048_checked : logI (1902064 / 1901413 : ℚ) = (⟨413837505132490692832, 413837505132490692899⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query049_checked : logI (1901413 / 1900762 : ℚ) = (⟨413979217821204694908, 413979217821204694973⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query050_checked : logI (1900762 / 1900111 : ℚ) = (⟨414121027598101394214, 414121027598101394279⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query051_checked : logI (1900111 / 1899460 : ℚ) = (⟨414262934562988494426, 414262934562988494491⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query052_checked : logI (1899460 / 1898809 : ℚ) = (⟨414404938815810550646, 414404938815810550713⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query053_checked : logI (1898809 / 1898158 : ℚ) = (⟨414547040456649204046, 414547040456649204113⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query054_checked : logI (1898158 / 1897507 : ℚ) = (⟨414689239585723416978, 414689239585723417043⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query055_checked : logI (1897507 / 1896856 : ℚ) = (⟨414831536303389708580, 414831536303389708645⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query056_checked : logI (1896856 / 1896205 : ℚ) = (⟨414973930710142390864, 414973930710142390931⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query057_checked : logI (1896205 / 1895554 : ℚ) = (⟨415116422906613805302, 415116422906613805367⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query058_checked : logI (1895554 / 1894903 : ℚ) = (⟨415259012993574559856, 415259012993574559921⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query059_checked : logI (1894903 / 1894252 : ℚ) = (⟨415401701071933766564, 415401701071933766631⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query060_checked : logI (1894252 / 1893601 : ℚ) = (⟨415544487242739279558, 415544487242739279625⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query061_checked : logI (1893601 / 1892950 : ℚ) = (⟨415687371607177933600, 415687371607177933667⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query062_checked : logI (1892950 / 1892299 : ℚ) = (⟨415830354266575783114, 415830354266575783179⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query063_checked : logI (1892299 / 1891648 : ℚ) = (⟨415973435322398341688, 415973435322398341755⟩ : I80) := by
  decide +kernel

def block03 : List (ℚ × I80) :=
  [((1902064 / 1901413 : ℚ), (⟨413837505132490692832, 413837505132490692899⟩ : I80)),
   ((1901413 / 1900762 : ℚ), (⟨413979217821204694908, 413979217821204694973⟩ : I80)),
   ((1900762 / 1900111 : ℚ), (⟨414121027598101394214, 414121027598101394279⟩ : I80)),
   ((1900111 / 1899460 : ℚ), (⟨414262934562988494426, 414262934562988494491⟩ : I80)),
   ((1899460 / 1898809 : ℚ), (⟨414404938815810550646, 414404938815810550713⟩ : I80)),
   ((1898809 / 1898158 : ℚ), (⟨414547040456649204046, 414547040456649204113⟩ : I80)),
   ((1898158 / 1897507 : ℚ), (⟨414689239585723416978, 414689239585723417043⟩ : I80)),
   ((1897507 / 1896856 : ℚ), (⟨414831536303389708580, 414831536303389708645⟩ : I80)),
   ((1896856 / 1896205 : ℚ), (⟨414973930710142390864, 414973930710142390931⟩ : I80)),
   ((1896205 / 1895554 : ℚ), (⟨415116422906613805302, 415116422906613805367⟩ : I80)),
   ((1895554 / 1894903 : ℚ), (⟨415259012993574559856, 415259012993574559921⟩ : I80)),
   ((1894903 / 1894252 : ℚ), (⟨415401701071933766564, 415401701071933766631⟩ : I80)),
   ((1894252 / 1893601 : ℚ), (⟨415544487242739279558, 415544487242739279625⟩ : I80)),
   ((1893601 / 1892950 : ℚ), (⟨415687371607177933600, 415687371607177933667⟩ : I80)),
   ((1892950 / 1892299 : ℚ), (⟨415830354266575783114, 415830354266575783179⟩ : I80)),
   ((1892299 / 1891648 : ℚ), (⟨415973435322398341688, 415973435322398341755⟩ : I80))]

theorem block03_checked : ∀ p ∈ block03, p.2 = logI p.1 := by
  intro p hp
  simp only [block03, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query048_checked.symm
  · exact query049_checked.symm
  · exact query050_checked.symm
  · exact query051_checked.symm
  · exact query052_checked.symm
  · exact query053_checked.symm
  · exact query054_checked.symm
  · exact query055_checked.symm
  · exact query056_checked.symm
  · exact query057_checked.symm
  · exact query058_checked.symm
  · exact query059_checked.symm
  · exact query060_checked.symm
  · exact query061_checked.symm
  · exact query062_checked.symm
  · exact query063_checked.symm

end ImbalancedChen.P2HistoricalLogCache
