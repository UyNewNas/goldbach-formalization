import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip492_firstU : firstU (⟨166, by decide⟩ : Fin 186) = 341 := by
  rfl

theorem strip492_row_count : 512 - firstU (⟨166, by decide⟩ : Fin 186) = 171 := by
  rw [strip492_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
