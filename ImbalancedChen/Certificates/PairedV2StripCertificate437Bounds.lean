import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip437_firstU : firstU (⟨111, by decide⟩ : Fin 186) = 399 := by
  rfl

theorem strip437_row_count : 512 - firstU (⟨111, by decide⟩ : Fin 186) = 113 := by
  rw [strip437_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
