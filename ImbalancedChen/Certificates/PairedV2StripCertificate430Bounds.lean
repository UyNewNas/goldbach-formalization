import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip430_firstU : firstU (⟨104, by decide⟩ : Fin 186) = 406 := by
  rfl

theorem strip430_row_count : 512 - firstU (⟨104, by decide⟩ : Fin 186) = 106 := by
  rw [strip430_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
