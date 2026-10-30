import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip478_firstU : firstU (⟨152, by decide⟩ : Fin 186) = 356 := by
  rfl

theorem strip478_row_count : 512 - firstU (⟨152, by decide⟩ : Fin 186) = 156 := by
  rw [strip478_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
