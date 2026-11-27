import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip422_checked : ∀ j : Fin (512 - firstU (⟨96, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨96, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨96, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip423_checked : ∀ j : Fin (512 - firstU (⟨97, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨97, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨97, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip424_checked : ∀ j : Fin (512 - firstU (⟨98, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨98, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨98, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip425_checked : ∀ j : Fin (512 - firstU (⟨99, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨99, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨99, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip426_checked : ∀ j : Fin (512 - firstU (⟨100, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨100, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨100, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip427_checked : ∀ j : Fin (512 - firstU (⟨101, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨101, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨101, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip428_checked : ∀ j : Fin (512 - firstU (⟨102, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨102, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨102, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip429_checked : ∀ j : Fin (512 - firstU (⟨103, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨103, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨103, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip430_checked : ∀ j : Fin (512 - firstU (⟨104, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨104, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨104, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip431_checked : ∀ j : Fin (512 - firstU (⟨105, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨105, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨105, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip432_checked : ∀ j : Fin (512 - firstU (⟨106, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨106, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨106, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip433_checked : ∀ j : Fin (512 - firstU (⟨107, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨107, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨107, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip434_checked : ∀ j : Fin (512 - firstU (⟨108, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨108, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨108, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip435_checked : ∀ j : Fin (512 - firstU (⟨109, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨109, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨109, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip436_checked : ∀ j : Fin (512 - firstU (⟨110, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨110, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨110, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip437_checked : ∀ j : Fin (512 - firstU (⟨111, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨111, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨111, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock06_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock06 k) := by
  fin_cases k
  · exact strip422_checked
  · exact strip423_checked
  · exact strip424_checked
  · exact strip425_checked
  · exact strip426_checked
  · exact strip427_checked
  · exact strip428_checked
  · exact strip429_checked
  · exact strip430_checked
  · exact strip431_checked
  · exact strip432_checked
  · exact strip433_checked
  · exact strip434_checked
  · exact strip435_checked
  · exact strip436_checked
  · exact strip437_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
