import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip441_firstU : firstU (⟨115, by decide⟩ : Fin 186) = 395 := by
  rfl

theorem strip441_row_count : 512 - firstU (⟨115, by decide⟩ : Fin 186) = 117 := by
  rw [strip441_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
