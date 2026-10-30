import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip505_firstU : firstU (⟨179, by decide⟩ : Fin 186) = 328 := by
  rfl

theorem strip505_row_count : 512 - firstU (⟨179, by decide⟩ : Fin 186) = 184 := by
  rw [strip505_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
