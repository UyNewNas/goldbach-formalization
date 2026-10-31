import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query256_checked : logI (365110 / 364767 : ℚ) = (⟨1136250591957890290414, 1136250591957890290479⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query257_checked : logI (364767 / 364424 : ℚ) = (⟨1137319541000056935414, 1137319541000056935479⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query258_checked : logI (364424 / 364081 : ℚ) = (⟨1138390503203987274556, 1138390503203987274621⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query259_checked : logI (364081 / 363738 : ℚ) = (⟨1139463484262151736394, 1139463484262151736461⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query260_checked : logI (363738 / 363395 : ℚ) = (⟨1140538489888502575556, 1140538489888502575621⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query261_checked : logI (363395 / 363052 : ℚ) = (⟨1141615525818575301602, 1141615525818575301667⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query262_checked : logI (363052 / 362709 : ℚ) = (⟨1142694597809590683140, 1142694597809590683207⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query263_checked : logI (362709 / 362366 : ℚ) = (⟨1143775711640557330954, 1143775711640557331021⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query264_checked : logI (362366 / 362023 : ℚ) = (⟨1144858873112374864038, 1144858873112374864103⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query265_checked : logI (362023 / 361680 : ℚ) = (⟨1145944088047937662358, 1145944088047937662423⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query266_checked : logI (361680 / 361337 : ℚ) = (⟨1147031362292239210272, 1147031362292239210337⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query267_checked : logI (361337 / 360994 : ℚ) = (⟨1148120701712477034522, 1148120701712477034587⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query268_checked : logI (360994 / 360651 : ℚ) = (⟨1149212112198158240746, 1149212112198158240811⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query269_checked : logI (360651 / 360308 : ℚ) = (⟨1150305599661205652512, 1150305599661205652577⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query270_checked : logI (360308 / 359965 : ℚ) = (⟨1151401170036064556884, 1151401170036064556949⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query271_checked : logI (359965 / 359622 : ℚ) = (⟨1152498829279810060552, 1152498829279810060619⟩ : I80) := by
  decide +kernel

def block16 : List (ℚ × I80) :=
  [((365110 / 364767 : ℚ), (⟨1136250591957890290414, 1136250591957890290479⟩ : I80)),
   ((364767 / 364424 : ℚ), (⟨1137319541000056935414, 1137319541000056935479⟩ : I80)),
   ((364424 / 364081 : ℚ), (⟨1138390503203987274556, 1138390503203987274621⟩ : I80)),
   ((364081 / 363738 : ℚ), (⟨1139463484262151736394, 1139463484262151736461⟩ : I80)),
   ((363738 / 363395 : ℚ), (⟨1140538489888502575556, 1140538489888502575621⟩ : I80)),
   ((363395 / 363052 : ℚ), (⟨1141615525818575301602, 1141615525818575301667⟩ : I80)),
   ((363052 / 362709 : ℚ), (⟨1142694597809590683140, 1142694597809590683207⟩ : I80)),
   ((362709 / 362366 : ℚ), (⟨1143775711640557330954, 1143775711640557331021⟩ : I80)),
   ((362366 / 362023 : ℚ), (⟨1144858873112374864038, 1144858873112374864103⟩ : I80)),
   ((362023 / 361680 : ℚ), (⟨1145944088047937662358, 1145944088047937662423⟩ : I80)),
   ((361680 / 361337 : ℚ), (⟨1147031362292239210272, 1147031362292239210337⟩ : I80)),
   ((361337 / 360994 : ℚ), (⟨1148120701712477034522, 1148120701712477034587⟩ : I80)),
   ((360994 / 360651 : ℚ), (⟨1149212112198158240746, 1149212112198158240811⟩ : I80)),
   ((360651 / 360308 : ℚ), (⟨1150305599661205652512, 1150305599661205652577⟩ : I80)),
   ((360308 / 359965 : ℚ), (⟨1151401170036064556884, 1151401170036064556949⟩ : I80)),
   ((359965 / 359622 : ℚ), (⟨1152498829279810060552, 1152498829279810060619⟩ : I80))]

theorem block16_checked : ∀ p ∈ block16, p.2 = logI p.1 := by
  intro p hp
  simp only [block16, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query256_checked.symm
  · exact query257_checked.symm
  · exact query258_checked.symm
  · exact query259_checked.symm
  · exact query260_checked.symm
  · exact query261_checked.symm
  · exact query262_checked.symm
  · exact query263_checked.symm
  · exact query264_checked.symm
  · exact query265_checked.symm
  · exact query266_checked.symm
  · exact query267_checked.symm
  · exact query268_checked.symm
  · exact query269_checked.symm
  · exact query270_checked.symm
  · exact query271_checked.symm

end ImbalancedChen.P2HistoricalLogCache
