import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query032_checked : logI (1912480 / 1911829 : ℚ) = (⟨411583225189651652476, 411583225189651652541⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query033_checked : logI (1911829 / 1911178 : ℚ) = (⟨411723397930521453130, 411723397930521453195⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query034_checked : logI (1911178 / 1910527 : ℚ) = (⟨411863666181072878274, 411863666181072878341⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query035_checked : logI (1910527 / 1909876 : ℚ) = (⟨412004030038955529500, 412004030038955529565⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query036_checked : logI (1909876 / 1909225 : ℚ) = (⟨412144489601952170402, 412144489601952170467⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query037_checked : logI (1909225 / 1908574 : ℚ) = (⟨412285044967978953644, 412285044967978953709⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query038_checked : logI (1908574 / 1907923 : ℚ) = (⟨412425696235085648492, 412425696235085648557⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query039_checked : logI (1907923 / 1907272 : ℚ) = (⟨412566443501455868800, 412566443501455868865⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query040_checked : logI (1907272 / 1906621 : ℚ) = (⟨412707286865407301484, 412707286865407301549⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query041_checked : logI (1906621 / 1905970 : ℚ) = (⟨412848226425391935438, 412848226425391935505⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query042_checked : logI (1905970 / 1905319 : ℚ) = (⟨412989262279996290942, 412989262279996291009⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query043_checked : logI (1905319 / 1904668 : ℚ) = (⟨413130394527941649530, 413130394527941649597⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query044_checked : logI (1904668 / 1904017 : ℚ) = (⟨413271623268084284330, 413271623268084284397⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query045_checked : logI (1904017 / 1903366 : ℚ) = (⟨413412948599415690880, 413412948599415690947⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query046_checked : logI (1903366 / 1902715 : ℚ) = (⟨413554370621062818408, 413554370621062818473⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query047_checked : logI (1902715 / 1902064 : ℚ) = (⟨413695889432288301596, 413695889432288301661⟩ : I80) := by
  decide +kernel

def block02 : List (ℚ × I80) :=
  [((1912480 / 1911829 : ℚ), (⟨411583225189651652476, 411583225189651652541⟩ : I80)),
   ((1911829 / 1911178 : ℚ), (⟨411723397930521453130, 411723397930521453195⟩ : I80)),
   ((1911178 / 1910527 : ℚ), (⟨411863666181072878274, 411863666181072878341⟩ : I80)),
   ((1910527 / 1909876 : ℚ), (⟨412004030038955529500, 412004030038955529565⟩ : I80)),
   ((1909876 / 1909225 : ℚ), (⟨412144489601952170402, 412144489601952170467⟩ : I80)),
   ((1909225 / 1908574 : ℚ), (⟨412285044967978953644, 412285044967978953709⟩ : I80)),
   ((1908574 / 1907923 : ℚ), (⟨412425696235085648492, 412425696235085648557⟩ : I80)),
   ((1907923 / 1907272 : ℚ), (⟨412566443501455868800, 412566443501455868865⟩ : I80)),
   ((1907272 / 1906621 : ℚ), (⟨412707286865407301484, 412707286865407301549⟩ : I80)),
   ((1906621 / 1905970 : ℚ), (⟨412848226425391935438, 412848226425391935505⟩ : I80)),
   ((1905970 / 1905319 : ℚ), (⟨412989262279996290942, 412989262279996291009⟩ : I80)),
   ((1905319 / 1904668 : ℚ), (⟨413130394527941649530, 413130394527941649597⟩ : I80)),
   ((1904668 / 1904017 : ℚ), (⟨413271623268084284330, 413271623268084284397⟩ : I80)),
   ((1904017 / 1903366 : ℚ), (⟨413412948599415690880, 413412948599415690947⟩ : I80)),
   ((1903366 / 1902715 : ℚ), (⟨413554370621062818408, 413554370621062818473⟩ : I80)),
   ((1902715 / 1902064 : ℚ), (⟨413695889432288301596, 413695889432288301661⟩ : I80))]

theorem block02_checked : ∀ p ∈ block02, p.2 = logI p.1 := by
  intro p hp
  simp only [block02, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query032_checked.symm
  · exact query033_checked.symm
  · exact query034_checked.symm
  · exact query035_checked.symm
  · exact query036_checked.symm
  · exact query037_checked.symm
  · exact query038_checked.symm
  · exact query039_checked.symm
  · exact query040_checked.symm
  · exact query041_checked.symm
  · exact query042_checked.symm
  · exact query043_checked.symm
  · exact query044_checked.symm
  · exact query045_checked.symm
  · exact query046_checked.symm
  · exact query047_checked.symm

end ImbalancedChen.P2HistoricalLogCache
