import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip502_checked : ∀ j : Fin (512 - firstU (⟨176, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨176, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨176, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip503_checked : ∀ j : Fin (512 - firstU (⟨177, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨177, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨177, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip504_checked : ∀ j : Fin (512 - firstU (⟨178, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨178, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨178, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip505_checked : ∀ j : Fin (512 - firstU (⟨179, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨179, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨179, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip506_checked : ∀ j : Fin (512 - firstU (⟨180, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨180, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨180, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip507_checked : ∀ j : Fin (512 - firstU (⟨181, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨181, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨181, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip508_checked : ∀ j : Fin (512 - firstU (⟨182, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨182, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨182, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip509_checked : ∀ j : Fin (512 - firstU (⟨183, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨183, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨183, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip510_checked : ∀ j : Fin (512 - firstU (⟨184, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨184, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨184, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip511_checked : ∀ j : Fin (512 - firstU (⟨185, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨185, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨185, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock11_checked (k : Fin 10) :
    StripAssembly.StripChecked (StripAssembly.indexBlock11 k) := by
  fin_cases k
  · exact strip502_checked
  · exact strip503_checked
  · exact strip504_checked
  · exact strip505_checked
  · exact strip506_checked
  · exact strip507_checked
  · exact strip508_checked
  · exact strip509_checked
  · exact strip510_checked
  · exact strip511_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
