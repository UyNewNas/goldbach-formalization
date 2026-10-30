import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip425_firstU : firstU (⟨99, by decide⟩ : Fin 186) = 411 := by
  rfl

theorem strip425_row_count : 512 - firstU (⟨99, by decide⟩ : Fin 186) = 101 := by
  rw [strip425_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
