import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip477_firstU : firstU (⟨151, by decide⟩ : Fin 186) = 357 := by
  rfl

theorem strip477_row_count : 512 - firstU (⟨151, by decide⟩ : Fin 186) = 155 := by
  rw [strip477_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
