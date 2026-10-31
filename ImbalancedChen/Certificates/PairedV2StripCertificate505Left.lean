import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly
import ImbalancedChen.Certificates.PairedV2StripCertificate505LeftA
import ImbalancedChen.Certificates.PairedV2StripCertificate505LeftB

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip505_checked_left : ∀ j : Fin 92,
    (makeCertificate (⟨(⟨179, by decide⟩ : Fin 186), Fin.cast strip505_row_count.symm (Fin.castAdd 92 j)⟩ : Row) (approximation (⟨(⟨179, by decide⟩ : Fin 186), Fin.cast strip505_row_count.symm (Fin.castAdd 92 j)⟩ : Row))).check = true := by
  exact StripAssembly.forallFinAdd (a := 46) (b := 46)
    (fun j => (makeCertificate (⟨(⟨179, by decide⟩ : Fin 186), Fin.cast strip505_row_count.symm (Fin.castAdd 92 j)⟩ : Row) (approximation (⟨(⟨179, by decide⟩ : Fin 186), Fin.cast strip505_row_count.symm (Fin.castAdd 92 j)⟩ : Row))).check = true)
    strip505_checked_left_a strip505_checked_left_b

end ImbalancedChen.Certificates.PairedV2.FullMask
