import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip464_firstU : firstU (⟨138, by decide⟩ : Fin 186) = 371 := by
  rfl

theorem strip464_row_count : 512 - firstU (⟨138, by decide⟩ : Fin 186) = 141 := by
  rw [strip464_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
