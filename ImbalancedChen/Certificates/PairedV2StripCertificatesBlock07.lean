import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip438_checked : ∀ j : Fin (512 - firstU (⟨112, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨112, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨112, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip439_checked : ∀ j : Fin (512 - firstU (⟨113, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨113, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨113, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip440_checked : ∀ j : Fin (512 - firstU (⟨114, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨114, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨114, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip441_checked : ∀ j : Fin (512 - firstU (⟨115, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨115, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨115, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip442_checked : ∀ j : Fin (512 - firstU (⟨116, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨116, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨116, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip443_checked : ∀ j : Fin (512 - firstU (⟨117, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨117, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨117, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip444_checked : ∀ j : Fin (512 - firstU (⟨118, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨118, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨118, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip445_checked : ∀ j : Fin (512 - firstU (⟨119, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨119, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨119, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip446_checked : ∀ j : Fin (512 - firstU (⟨120, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨120, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨120, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip447_checked : ∀ j : Fin (512 - firstU (⟨121, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨121, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨121, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip448_checked : ∀ j : Fin (512 - firstU (⟨122, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨122, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨122, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip449_checked : ∀ j : Fin (512 - firstU (⟨123, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨123, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨123, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip450_checked : ∀ j : Fin (512 - firstU (⟨124, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨124, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨124, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip451_checked : ∀ j : Fin (512 - firstU (⟨125, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨125, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨125, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip452_checked : ∀ j : Fin (512 - firstU (⟨126, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨126, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨126, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip453_checked : ∀ j : Fin (512 - firstU (⟨127, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨127, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨127, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock07_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock07 k) := by
  fin_cases k
  · exact strip438_checked
  · exact strip439_checked
  · exact strip440_checked
  · exact strip441_checked
  · exact strip442_checked
  · exact strip443_checked
  · exact strip444_checked
  · exact strip445_checked
  · exact strip446_checked
  · exact strip447_checked
  · exact strip448_checked
  · exact strip449_checked
  · exact strip450_checked
  · exact strip451_checked
  · exact strip452_checked
  · exact strip453_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
