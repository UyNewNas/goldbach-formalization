import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip502_firstU : firstU (⟨176, by decide⟩ : Fin 186) = 331 := by
  rfl

theorem strip502_row_count : 512 - firstU (⟨176, by decide⟩ : Fin 186) = 181 := by
  rw [strip502_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
