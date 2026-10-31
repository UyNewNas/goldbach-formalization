import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip509_firstU : firstU (⟨183, by decide⟩ : Fin 186) = 323 := by
  rfl

theorem strip509_row_count : 512 - firstU (⟨183, by decide⟩ : Fin 186) = 189 := by
  rw [strip509_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
