import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query368_checked : logI (326694 / 326351 : ℚ) = (⟨1269932682306742480672, 1269932682306742480737⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query369_checked : logI (326351 / 326008 : ℚ) = (⟨1271268103417717958290, 1271268103417717958357⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query370_checked : logI (326008 / 325665 : ℚ) = (⟨1272606336058818669244, 1272606336058818669311⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query371_checked : logI (325665 / 325322 : ℚ) = (⟨1273947389118288366650, 1273947389118288366717⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query372_checked : logI (325322 / 324979 : ℚ) = (⟨1275291271521875516284, 1275291271521875516349⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query373_checked : logI (324979 / 324636 : ℚ) = (⟨1276637992233031323456, 1276637992233031323523⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query374_checked : logI (324636 / 324293 : ℚ) = (⟨1277987560253109015946, 1277987560253109016013⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query375_checked : logI (324293 / 323950 : ℚ) = (⟨1279339984621564392262, 1279339984621564392329⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query376_checked : logI (323950 / 323607 : ℚ) = (⟨1280695274416157644632, 1280695274416157644699⟩ : I80) := by
  decide +kernel

def block23 : List (ℚ × I80) :=
  [((326694 / 326351 : ℚ), (⟨1269932682306742480672, 1269932682306742480737⟩ : I80)),
   ((326351 / 326008 : ℚ), (⟨1271268103417717958290, 1271268103417717958357⟩ : I80)),
   ((326008 / 325665 : ℚ), (⟨1272606336058818669244, 1272606336058818669311⟩ : I80)),
   ((325665 / 325322 : ℚ), (⟨1273947389118288366650, 1273947389118288366717⟩ : I80)),
   ((325322 / 324979 : ℚ), (⟨1275291271521875516284, 1275291271521875516349⟩ : I80)),
   ((324979 / 324636 : ℚ), (⟨1276637992233031323456, 1276637992233031323523⟩ : I80)),
   ((324636 / 324293 : ℚ), (⟨1277987560253109015946, 1277987560253109016013⟩ : I80)),
   ((324293 / 323950 : ℚ), (⟨1279339984621564392262, 1279339984621564392329⟩ : I80)),
   ((323950 / 323607 : ℚ), (⟨1280695274416157644632, 1280695274416157644699⟩ : I80))]

theorem block23_checked : ∀ p ∈ block23, p.2 = logI p.1 := by
  intro p hp
  simp only [block23, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query368_checked.symm
  · exact query369_checked.symm
  · exact query370_checked.symm
  · exact query371_checked.symm
  · exact query372_checked.symm
  · exact query373_checked.symm
  · exact query374_checked.symm
  · exact query375_checked.symm
  · exact query376_checked.symm

end ImbalancedChen.P2HistoricalLogCache
