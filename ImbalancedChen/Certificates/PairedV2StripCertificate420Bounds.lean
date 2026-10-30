import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip420_firstU : firstU (⟨94, by decide⟩ : Fin 186) = 417 := by
  rfl

theorem strip420_row_count : 512 - firstU (⟨94, by decide⟩ : Fin 186) = 95 := by
  rw [strip420_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
