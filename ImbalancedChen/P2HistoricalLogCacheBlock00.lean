import ImbalancedChen.P2HistoricalLogCacheCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query000_checked : logI (1933312 / 1932661 : ℚ) = (⟨407147549146327847288, 407147549146327847353⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query001_checked : logI (1932661 / 1932010 : ℚ) = (⟨407284716351250257320, 407284716351250257385⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query002_checked : logI (1932010 / 1931359 : ℚ) = (⟨407421976010041753240, 407421976010041753305⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query003_checked : logI (1931359 / 1930708 : ℚ) = (⟨407559328216207918024, 407559328216207918089⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query004_checked : logI (1930708 / 1930057 : ℚ) = (⟨407696773063380469514, 407696773063380469581⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query005_checked : logI (1930057 / 1929406 : ℚ) = (⟨407834310645317473196, 407834310645317473261⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query006_checked : logI (1929406 / 1928755 : ℚ) = (⟨407971941055903555366, 407971941055903555431⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query007_checked : logI (1928755 / 1928104 : ℚ) = (⟨408109664389150116768, 408109664389150116835⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query008_checked : logI (1928104 / 1927453 : ℚ) = (⟨408247480739195546652, 408247480739195546719⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query009_checked : logI (1927453 / 1926802 : ℚ) = (⟨408385390200305437248, 408385390200305437315⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query010_checked : logI (1926802 / 1926151 : ℚ) = (⟨408523392866872798704, 408523392866872798771⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query011_checked : logI (1926151 / 1925500 : ℚ) = (⟨408661488833418274434, 408661488833418274501⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query012_checked : logI (1925500 / 1924849 : ℚ) = (⟨408799678194590356928, 408799678194590356995⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query013_checked : logI (1924849 / 1924198 : ℚ) = (⟨408937961045165603976, 408937961045165604043⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query014_checked : logI (1924198 / 1923547 : ℚ) = (⟨409076337480048855344, 409076337480048855409⟩ : I80) := by
  decide +kernel

/-- Exact original logI output, checked by the ordinary kernel. -/
theorem query015_checked : logI (1923547 / 1922896 : ℚ) = (⟨409214807594273449890, 409214807594273449957⟩ : I80) := by
  decide +kernel

def block00 : List (ℚ × I80) :=
  [((1933312 / 1932661 : ℚ), (⟨407147549146327847288, 407147549146327847353⟩ : I80)),
   ((1932661 / 1932010 : ℚ), (⟨407284716351250257320, 407284716351250257385⟩ : I80)),
   ((1932010 / 1931359 : ℚ), (⟨407421976010041753240, 407421976010041753305⟩ : I80)),
   ((1931359 / 1930708 : ℚ), (⟨407559328216207918024, 407559328216207918089⟩ : I80)),
   ((1930708 / 1930057 : ℚ), (⟨407696773063380469514, 407696773063380469581⟩ : I80)),
   ((1930057 / 1929406 : ℚ), (⟨407834310645317473196, 407834310645317473261⟩ : I80)),
   ((1929406 / 1928755 : ℚ), (⟨407971941055903555366, 407971941055903555431⟩ : I80)),
   ((1928755 / 1928104 : ℚ), (⟨408109664389150116768, 408109664389150116835⟩ : I80)),
   ((1928104 / 1927453 : ℚ), (⟨408247480739195546652, 408247480739195546719⟩ : I80)),
   ((1927453 / 1926802 : ℚ), (⟨408385390200305437248, 408385390200305437315⟩ : I80)),
   ((1926802 / 1926151 : ℚ), (⟨408523392866872798704, 408523392866872798771⟩ : I80)),
   ((1926151 / 1925500 : ℚ), (⟨408661488833418274434, 408661488833418274501⟩ : I80)),
   ((1925500 / 1924849 : ℚ), (⟨408799678194590356928, 408799678194590356995⟩ : I80)),
   ((1924849 / 1924198 : ℚ), (⟨408937961045165603976, 408937961045165604043⟩ : I80)),
   ((1924198 / 1923547 : ℚ), (⟨409076337480048855344, 409076337480048855409⟩ : I80)),
   ((1923547 / 1922896 : ℚ), (⟨409214807594273449890, 409214807594273449957⟩ : I80))]

theorem block00_checked : ∀ p ∈ block00, p.2 = logI p.1 := by
  intro p hp
  simp only [block00, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query000_checked.symm
  · exact query001_checked.symm
  · exact query002_checked.symm
  · exact query003_checked.symm
  · exact query004_checked.symm
  · exact query005_checked.symm
  · exact query006_checked.symm
  · exact query007_checked.symm
  · exact query008_checked.symm
  · exact query009_checked.symm
  · exact query010_checked.symm
  · exact query011_checked.symm
  · exact query012_checked.symm
  · exact query013_checked.symm
  · exact query014_checked.symm
  · exact query015_checked.symm

end ImbalancedChen.P2HistoricalLogCache
