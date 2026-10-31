import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query288_checked : logI (354134 / 353791 : ℚ) = (⟨1171484517641550515328, 1171484517641550515393⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query289_checked : logI (353791 / 353448 : ℚ) = (⟨1172620821642117430158, 1172620821642117430225⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query290_checked : logI (353448 / 353105 : ℚ) = (⟨1173759332143054209284, 1173759332143054209349⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query291_checked : logI (353105 / 352762 : ℚ) = (⟨1174900055577554625402, 1174900055577554625469⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query292_checked : logI (352762 / 352419 : ℚ) = (⟨1176042998403845301872, 1176042998403845301937⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query293_checked : logI (352419 / 352076 : ℚ) = (⟨1177188167105307591100, 1177188167105307591165⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query294_checked : logI (352076 / 351733 : ℚ) = (⟨1178335568190600165704, 1178335568190600165769⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query295_checked : logI (351733 / 351390 : ℚ) = (⟨1179485208193782327306, 1179485208193782327371⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query296_checked : logI (351390 / 351047 : ℚ) = (⟨1180637093674438037866, 1180637093674438037933⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query297_checked : logI (351047 / 350704 : ℚ) = (⟨1181791231217800678506, 1181791231217800678573⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query298_checked : logI (350704 / 350361 : ℚ) = (⟨1182947627434878540794, 1182947627434878540861⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query299_checked : logI (350361 / 350018 : ℚ) = (⟨1184106288962581055522, 1184106288962581055589⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query300_checked : logI (350018 / 349675 : ℚ) = (⟨1185267222463845764040, 1185267222463845764105⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query301_checked : logI (349675 / 349332 : ℚ) = (⟨1186430434627766037226, 1186430434627766037291⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query302_checked : logI (349332 / 348989 : ℚ) = (⟨1187595932169719547276, 1187595932169719547341⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query303_checked : logI (348989 / 348646 : ℚ) = (⟨1188763721831497497444, 1188763721831497497511⟩ : I80) := by
  decide +kernel

def block18 : List (ℚ × I80) :=
  [((354134 / 353791 : ℚ), (⟨1171484517641550515328, 1171484517641550515393⟩ : I80)),
   ((353791 / 353448 : ℚ), (⟨1172620821642117430158, 1172620821642117430225⟩ : I80)),
   ((353448 / 353105 : ℚ), (⟨1173759332143054209284, 1173759332143054209349⟩ : I80)),
   ((353105 / 352762 : ℚ), (⟨1174900055577554625402, 1174900055577554625469⟩ : I80)),
   ((352762 / 352419 : ℚ), (⟨1176042998403845301872, 1176042998403845301937⟩ : I80)),
   ((352419 / 352076 : ℚ), (⟨1177188167105307591100, 1177188167105307591165⟩ : I80)),
   ((352076 / 351733 : ℚ), (⟨1178335568190600165704, 1178335568190600165769⟩ : I80)),
   ((351733 / 351390 : ℚ), (⟨1179485208193782327306, 1179485208193782327371⟩ : I80)),
   ((351390 / 351047 : ℚ), (⟨1180637093674438037866, 1180637093674438037933⟩ : I80)),
   ((351047 / 350704 : ℚ), (⟨1181791231217800678506, 1181791231217800678573⟩ : I80)),
   ((350704 / 350361 : ℚ), (⟨1182947627434878540794, 1182947627434878540861⟩ : I80)),
   ((350361 / 350018 : ℚ), (⟨1184106288962581055522, 1184106288962581055589⟩ : I80)),
   ((350018 / 349675 : ℚ), (⟨1185267222463845764040, 1185267222463845764105⟩ : I80)),
   ((349675 / 349332 : ℚ), (⟨1186430434627766037226, 1186430434627766037291⟩ : I80)),
   ((349332 / 348989 : ℚ), (⟨1187595932169719547276, 1187595932169719547341⟩ : I80)),
   ((348989 / 348646 : ℚ), (⟨1188763721831497497444, 1188763721831497497511⟩ : I80))]

theorem block18_checked : ∀ p ∈ block18, p.2 = logI p.1 := by
  intro p hp
  simp only [block18, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query288_checked.symm
  · exact query289_checked.symm
  · exact query290_checked.symm
  · exact query291_checked.symm
  · exact query292_checked.symm
  · exact query293_checked.symm
  · exact query294_checked.symm
  · exact query295_checked.symm
  · exact query296_checked.symm
  · exact query297_checked.symm
  · exact query298_checked.symm
  · exact query299_checked.symm
  · exact query300_checked.symm
  · exact query301_checked.symm
  · exact query302_checked.symm
  · exact query303_checked.symm

end ImbalancedChen.P2HistoricalLogCache
