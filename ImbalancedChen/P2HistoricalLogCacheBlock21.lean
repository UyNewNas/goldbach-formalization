import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query336_checked : logI (337670 / 337327 : ℚ) = (⟨1228632399310480815418, 1228632399310480815483⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query337_checked : logI (337327 / 336984 : ℚ) = (⟨1229882329937801352924, 1229882329937801352991⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query338_checked : logI (336984 / 336641 : ℚ) = (⟨1231134806351375154208, 1231134806351375154273⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query339_checked : logI (336641 / 336298 : ℚ) = (⟨1232389836336796338950, 1232389836336796339017⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query340_checked : logI (336298 / 335955 : ℚ) = (⟨1233647427711438252096, 1233647427711438252161⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query341_checked : logI (335955 / 335612 : ℚ) = (⟨1234907588324615774972, 1234907588324615775037⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query342_checked : logI (335612 / 335269 : ℚ) = (⟨1236170326057748632234, 1236170326057748632299⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query343_checked : logI (335269 / 334926 : ℚ) = (⟨1237435648824525701764, 1237435648824525701829⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query344_checked : logI (334926 / 334583 : ℚ) = (⟨1238703564571070334714, 1238703564571070334779⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query345_checked : logI (334583 / 334240 : ℚ) = (⟨1239974081276106692922, 1239974081276106692987⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query346_checked : logI (334240 / 333897 : ℚ) = (⟨1241247206951127111080, 1241247206951127111147⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query347_checked : logI (333897 / 333554 : ℚ) = (⟨1242522949640560490936, 1242522949640560491003⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query348_checked : logI (333554 / 333211 : ℚ) = (⟨1243801317421941735036, 1243801317421941735103⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query349_checked : logI (333211 / 332868 : ℚ) = (⟨1245082318406082227468, 1245082318406082227535⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query350_checked : logI (332868 / 332525 : ℚ) = (⟨1246365960737241369170, 1246365960737241369237⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query351_checked : logI (332525 / 332182 : ℚ) = (⟨1247652252593299175412, 1247652252593299175477⟩ : I80) := by
  decide +kernel

def block21 : List (ℚ × I80) :=
  [((337670 / 337327 : ℚ), (⟨1228632399310480815418, 1228632399310480815483⟩ : I80)),
   ((337327 / 336984 : ℚ), (⟨1229882329937801352924, 1229882329937801352991⟩ : I80)),
   ((336984 / 336641 : ℚ), (⟨1231134806351375154208, 1231134806351375154273⟩ : I80)),
   ((336641 / 336298 : ℚ), (⟨1232389836336796338950, 1232389836336796339017⟩ : I80)),
   ((336298 / 335955 : ℚ), (⟨1233647427711438252096, 1233647427711438252161⟩ : I80)),
   ((335955 / 335612 : ℚ), (⟨1234907588324615774972, 1234907588324615775037⟩ : I80)),
   ((335612 / 335269 : ℚ), (⟨1236170326057748632234, 1236170326057748632299⟩ : I80)),
   ((335269 / 334926 : ℚ), (⟨1237435648824525701764, 1237435648824525701829⟩ : I80)),
   ((334926 / 334583 : ℚ), (⟨1238703564571070334714, 1238703564571070334779⟩ : I80)),
   ((334583 / 334240 : ℚ), (⟨1239974081276106692922, 1239974081276106692987⟩ : I80)),
   ((334240 / 333897 : ℚ), (⟨1241247206951127111080, 1241247206951127111147⟩ : I80)),
   ((333897 / 333554 : ℚ), (⟨1242522949640560490936, 1242522949640560491003⟩ : I80)),
   ((333554 / 333211 : ℚ), (⟨1243801317421941735036, 1243801317421941735103⟩ : I80)),
   ((333211 / 332868 : ℚ), (⟨1245082318406082227468, 1245082318406082227535⟩ : I80)),
   ((332868 / 332525 : ℚ), (⟨1246365960737241369170, 1246365960737241369237⟩ : I80)),
   ((332525 / 332182 : ℚ), (⟨1247652252593299175412, 1247652252593299175477⟩ : I80))]

theorem block21_checked : ∀ p ∈ block21, p.2 = logI p.1 := by
  intro p hp
  simp only [block21, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query336_checked.symm
  · exact query337_checked.symm
  · exact query338_checked.symm
  · exact query339_checked.symm
  · exact query340_checked.symm
  · exact query341_checked.symm
  · exact query342_checked.symm
  · exact query343_checked.symm
  · exact query344_checked.symm
  · exact query345_checked.symm
  · exact query346_checked.symm
  · exact query347_checked.symm
  · exact query348_checked.symm
  · exact query349_checked.symm
  · exact query350_checked.symm
  · exact query351_checked.symm

end ImbalancedChen.P2HistoricalLogCache
