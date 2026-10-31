import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query272_checked : logI (359622 / 359279 : ℚ) = (⟨1153598583372255060658, 1153598583372255060723⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query273_checked : logI (359279 / 358936 : ℚ) = (⟨1154700438316058834334, 1154700438316058834401⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query274_checked : logI (358936 / 358593 : ℚ) = (⟨1155804400136836251204, 1155804400136836251269⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query275_checked : logI (358593 / 358250 : ℚ) = (⟨1156910474883267612928, 1156910474883267612993⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query276_checked : logI (358250 / 357907 : ℚ) = (⟨1158018668627209124044, 1158018668627209124111⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query277_checked : logI (357907 / 357564 : ℚ) = (⟨1159128987463803998354, 1159128987463803998421⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query278_checked : logI (357564 / 357221 : ℚ) = (⟨1160241437511594205050, 1160241437511594205115⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query279_checked : logI (357221 / 356878 : ℚ) = (⟨1161356024912632859000, 1161356024912632859067⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query280_checked : logI (356878 / 356535 : ℚ) = (⟨1162472755832597259420, 1162472755832597259487⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query281_checked : logI (356535 / 356192 : ℚ) = (⟨1163591636460902581352, 1163591636460902581419⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query282_checked : logI (356192 / 355849 : ℚ) = (⟨1164712673010816224352, 1164712673010816224419⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query283_checked : logI (355849 / 355506 : ℚ) = (⟨1165835871719572822816, 1165835871719572822883⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query284_checked : logI (355506 / 355163 : ℚ) = (⟨1166961238848489922414, 1166961238848489922479⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query285_checked : logI (355163 / 354820 : ℚ) = (⟨1168088780683084327122, 1168088780683084327189⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query286_checked : logI (354820 / 354477 : ℚ) = (⟨1169218503533189121436, 1169218503533189121503⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query287_checked : logI (354477 / 354134 : ℚ) = (⟨1170350413733071372290, 1170350413733071372355⟩ : I80) := by
  decide +kernel

def block17 : List (ℚ × I80) :=
  [((359622 / 359279 : ℚ), (⟨1153598583372255060658, 1153598583372255060723⟩ : I80)),
   ((359279 / 358936 : ℚ), (⟨1154700438316058834334, 1154700438316058834401⟩ : I80)),
   ((358936 / 358593 : ℚ), (⟨1155804400136836251204, 1155804400136836251269⟩ : I80)),
   ((358593 / 358250 : ℚ), (⟨1156910474883267612928, 1156910474883267612993⟩ : I80)),
   ((358250 / 357907 : ℚ), (⟨1158018668627209124044, 1158018668627209124111⟩ : I80)),
   ((357907 / 357564 : ℚ), (⟨1159128987463803998354, 1159128987463803998421⟩ : I80)),
   ((357564 / 357221 : ℚ), (⟨1160241437511594205050, 1160241437511594205115⟩ : I80)),
   ((357221 / 356878 : ℚ), (⟨1161356024912632859000, 1161356024912632859067⟩ : I80)),
   ((356878 / 356535 : ℚ), (⟨1162472755832597259420, 1162472755832597259487⟩ : I80)),
   ((356535 / 356192 : ℚ), (⟨1163591636460902581352, 1163591636460902581419⟩ : I80)),
   ((356192 / 355849 : ℚ), (⟨1164712673010816224352, 1164712673010816224419⟩ : I80)),
   ((355849 / 355506 : ℚ), (⟨1165835871719572822816, 1165835871719572822883⟩ : I80)),
   ((355506 / 355163 : ℚ), (⟨1166961238848489922414, 1166961238848489922479⟩ : I80)),
   ((355163 / 354820 : ℚ), (⟨1168088780683084327122, 1168088780683084327189⟩ : I80)),
   ((354820 / 354477 : ℚ), (⟨1169218503533189121436, 1169218503533189121503⟩ : I80)),
   ((354477 / 354134 : ℚ), (⟨1170350413733071372290, 1170350413733071372355⟩ : I80))]

theorem block17_checked : ∀ p ∈ block17, p.2 = logI p.1 := by
  intro p hp
  simp only [block17, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query272_checked.symm
  · exact query273_checked.symm
  · exact query274_checked.symm
  · exact query275_checked.symm
  · exact query276_checked.symm
  · exact query277_checked.symm
  · exact query278_checked.symm
  · exact query279_checked.symm
  · exact query280_checked.symm
  · exact query281_checked.symm
  · exact query282_checked.symm
  · exact query283_checked.symm
  · exact query284_checked.symm
  · exact query285_checked.symm
  · exact query286_checked.symm
  · exact query287_checked.symm

end ImbalancedChen.P2HistoricalLogCache
