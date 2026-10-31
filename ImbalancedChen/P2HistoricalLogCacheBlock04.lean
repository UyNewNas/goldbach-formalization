import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query064_checked : logI (1891648 / 1890997 : ℚ) = (⟨416116614876250822104, 416116614876250822169⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query065_checked : logI (1890997 / 1890346 : ℚ) = (⟨416259893029878376824, 416259893029878376891⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query066_checked : logI (1890346 / 1889695 : ℚ) = (⟨416403269885166339020, 416403269885166339085⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query067_checked : logI (1889695 / 1889044 : ℚ) = (⟨416546745544140464052, 416546745544140464117⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query068_checked : logI (1889044 / 1888393 : ℚ) = (⟨416690320108967171488, 416690320108967171553⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query069_checked : logI (1888393 / 1887742 : ℚ) = (⟨416833993681953787598, 416833993681953787665⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query070_checked : logI (1887742 / 1887091 : ℚ) = (⟨416977766365548788362, 416977766365548788429⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query071_checked : logI (1887091 / 1886440 : ℚ) = (⟨417121638262342042984, 417121638262342043051⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query072_checked : logI (1886440 / 1885789 : ℚ) = (⟨417265609475065057886, 417265609475065057951⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query073_checked : logI (1885789 / 1885138 : ℚ) = (⟨417409680106591221242, 417409680106591221307⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query074_checked : logI (1885138 / 1884487 : ℚ) = (⟨417553850259936048002, 417553850259936048067⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query075_checked : logI (1884487 / 1883836 : ℚ) = (⟨417698120038257425416, 417698120038257425483⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query076_checked : logI (1883836 / 1883185 : ℚ) = (⟨417842489544855859082, 417842489544855859147⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query077_checked : logI (1883185 / 1882534 : ℚ) = (⟨417986958883174719494, 417986958883174719561⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query078_checked : logI (1882534 / 1881883 : ℚ) = (⟨418131528156800489108, 418131528156800489173⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query079_checked : logI (1881883 / 1881232 : ℚ) = (⟨418276197469463009918, 418276197469463009985⟩ : I80) := by
  decide +kernel

def block04 : List (ℚ × I80) :=
  [((1891648 / 1890997 : ℚ), (⟨416116614876250822104, 416116614876250822169⟩ : I80)),
   ((1890997 / 1890346 : ℚ), (⟨416259893029878376824, 416259893029878376891⟩ : I80)),
   ((1890346 / 1889695 : ℚ), (⟨416403269885166339020, 416403269885166339085⟩ : I80)),
   ((1889695 / 1889044 : ℚ), (⟨416546745544140464052, 416546745544140464117⟩ : I80)),
   ((1889044 / 1888393 : ℚ), (⟨416690320108967171488, 416690320108967171553⟩ : I80)),
   ((1888393 / 1887742 : ℚ), (⟨416833993681953787598, 416833993681953787665⟩ : I80)),
   ((1887742 / 1887091 : ℚ), (⟨416977766365548788362, 416977766365548788429⟩ : I80)),
   ((1887091 / 1886440 : ℚ), (⟨417121638262342042984, 417121638262342043051⟩ : I80)),
   ((1886440 / 1885789 : ℚ), (⟨417265609475065057886, 417265609475065057951⟩ : I80)),
   ((1885789 / 1885138 : ℚ), (⟨417409680106591221242, 417409680106591221307⟩ : I80)),
   ((1885138 / 1884487 : ℚ), (⟨417553850259936048002, 417553850259936048067⟩ : I80)),
   ((1884487 / 1883836 : ℚ), (⟨417698120038257425416, 417698120038257425483⟩ : I80)),
   ((1883836 / 1883185 : ℚ), (⟨417842489544855859082, 417842489544855859147⟩ : I80)),
   ((1883185 / 1882534 : ℚ), (⟨417986958883174719494, 417986958883174719561⟩ : I80)),
   ((1882534 / 1881883 : ℚ), (⟨418131528156800489108, 418131528156800489173⟩ : I80)),
   ((1881883 / 1881232 : ℚ), (⟨418276197469463009918, 418276197469463009985⟩ : I80))]

theorem block04_checked : ∀ p ∈ block04, p.2 = logI p.1 := by
  intro p hp
  simp only [block04, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query064_checked.symm
  · exact query065_checked.symm
  · exact query066_checked.symm
  · exact query067_checked.symm
  · exact query068_checked.symm
  · exact query069_checked.symm
  · exact query070_checked.symm
  · exact query071_checked.symm
  · exact query072_checked.symm
  · exact query073_checked.symm
  · exact query074_checked.symm
  · exact query075_checked.symm
  · exact query076_checked.symm
  · exact query077_checked.symm
  · exact query078_checked.symm
  · exact query079_checked.symm

end ImbalancedChen.P2HistoricalLogCache
