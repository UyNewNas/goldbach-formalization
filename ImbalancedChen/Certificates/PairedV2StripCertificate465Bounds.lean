import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip465_firstU : firstU (⟨139, by decide⟩ : Fin 186) = 370 := by
  rfl

theorem strip465_row_count : 512 - firstU (⟨139, by decide⟩ : Fin 186) = 142 := by
  rw [strip465_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
