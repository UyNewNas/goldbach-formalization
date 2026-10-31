import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query320_checked : logI (343158 / 342815 : ℚ) = (⟨1208973503871647752952, 1208973503871647753019⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query321_checked : logI (342815 / 342472 : ℚ) = (⟨1210183735441924837872, 1210183735441924837937⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query322_checked : logI (342472 / 342129 : ℚ) = (⟨1211396392422230261980, 1211396392422230262045⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query323_checked : logI (342129 / 341786 : ℚ) = (⟨1212611482110979047324, 1212611482110979047391⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query324_checked : logI (341786 / 341443 : ℚ) = (⟨1213829011835898290250, 1213829011835898290317⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query325_checked : logI (341443 / 341100 : ℚ) = (⟨1215048988954174464174, 1215048988954174464241⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query326_checked : logI (341100 / 340757 : ℚ) = (⟨1216271420852601611514, 1216271420852601611579⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query327_checked : logI (340757 / 340414 : ℚ) = (⟨1217496314947730431096, 1217496314947730431161⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query328_checked : logI (340414 / 340071 : ℚ) = (⟨1218723678686018267326, 1218723678686018267391⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query329_checked : logI (340071 / 339728 : ℚ) = (⟨1219953519543980007508, 1219953519543980007575⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query330_checked : logI (339728 / 339385 : ℚ) = (⟨1221185845028339893734, 1221185845028339893801⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query331_checked : logI (339385 / 339042 : ℚ) = (⟨1222420662676184255804, 1222420662676184255871⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query332_checked : logI (339042 / 338699 : ℚ) = (⟨1223657980055115171716, 1223657980055115171781⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query333_checked : logI (338699 / 338356 : ℚ) = (⟨1224897804763405062292, 1224897804763405062357⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query334_checked : logI (338356 / 338013 : ℚ) = (⟨1226140144430152226612, 1226140144430152226677⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query335_checked : logI (338013 / 337670 : ℚ) = (⟨1227385006715437324862, 1227385006715437324927⟩ : I80) := by
  decide +kernel

def block20 : List (ℚ × I80) :=
  [((343158 / 342815 : ℚ), (⟨1208973503871647752952, 1208973503871647753019⟩ : I80)),
   ((342815 / 342472 : ℚ), (⟨1210183735441924837872, 1210183735441924837937⟩ : I80)),
   ((342472 / 342129 : ℚ), (⟨1211396392422230261980, 1211396392422230262045⟩ : I80)),
   ((342129 / 341786 : ℚ), (⟨1212611482110979047324, 1212611482110979047391⟩ : I80)),
   ((341786 / 341443 : ℚ), (⟨1213829011835898290250, 1213829011835898290317⟩ : I80)),
   ((341443 / 341100 : ℚ), (⟨1215048988954174464174, 1215048988954174464241⟩ : I80)),
   ((341100 / 340757 : ℚ), (⟨1216271420852601611514, 1216271420852601611579⟩ : I80)),
   ((340757 / 340414 : ℚ), (⟨1217496314947730431096, 1217496314947730431161⟩ : I80)),
   ((340414 / 340071 : ℚ), (⟨1218723678686018267326, 1218723678686018267391⟩ : I80)),
   ((340071 / 339728 : ℚ), (⟨1219953519543980007508, 1219953519543980007575⟩ : I80)),
   ((339728 / 339385 : ℚ), (⟨1221185845028339893734, 1221185845028339893801⟩ : I80)),
   ((339385 / 339042 : ℚ), (⟨1222420662676184255804, 1222420662676184255871⟩ : I80)),
   ((339042 / 338699 : ℚ), (⟨1223657980055115171716, 1223657980055115171781⟩ : I80)),
   ((338699 / 338356 : ℚ), (⟨1224897804763405062292, 1224897804763405062357⟩ : I80)),
   ((338356 / 338013 : ℚ), (⟨1226140144430152226612, 1226140144430152226677⟩ : I80)),
   ((338013 / 337670 : ℚ), (⟨1227385006715437324862, 1227385006715437324927⟩ : I80))]

theorem block20_checked : ∀ p ∈ block20, p.2 = logI p.1 := by
  intro p hp
  simp only [block20, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query320_checked.symm
  · exact query321_checked.symm
  · exact query322_checked.symm
  · exact query323_checked.symm
  · exact query324_checked.symm
  · exact query325_checked.symm
  · exact query326_checked.symm
  · exact query327_checked.symm
  · exact query328_checked.symm
  · exact query329_checked.symm
  · exact query330_checked.symm
  · exact query331_checked.symm
  · exact query332_checked.symm
  · exact query333_checked.symm
  · exact query334_checked.symm
  · exact query335_checked.symm

end ImbalancedChen.P2HistoricalLogCache
