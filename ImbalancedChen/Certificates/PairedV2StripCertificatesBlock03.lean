import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip374_checked : ∀ j : Fin (512 - firstU (⟨48, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨48, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨48, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip375_checked : ∀ j : Fin (512 - firstU (⟨49, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨49, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨49, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip376_checked : ∀ j : Fin (512 - firstU (⟨50, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨50, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨50, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip377_checked : ∀ j : Fin (512 - firstU (⟨51, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨51, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨51, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip378_checked : ∀ j : Fin (512 - firstU (⟨52, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨52, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨52, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip379_checked : ∀ j : Fin (512 - firstU (⟨53, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨53, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨53, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip380_checked : ∀ j : Fin (512 - firstU (⟨54, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨54, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨54, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip381_checked : ∀ j : Fin (512 - firstU (⟨55, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨55, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨55, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip382_checked : ∀ j : Fin (512 - firstU (⟨56, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨56, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨56, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip383_checked : ∀ j : Fin (512 - firstU (⟨57, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨57, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨57, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip384_checked : ∀ j : Fin (512 - firstU (⟨58, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨58, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨58, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip385_checked : ∀ j : Fin (512 - firstU (⟨59, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨59, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨59, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip386_checked : ∀ j : Fin (512 - firstU (⟨60, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨60, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨60, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip387_checked : ∀ j : Fin (512 - firstU (⟨61, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨61, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨61, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip388_checked : ∀ j : Fin (512 - firstU (⟨62, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨62, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨62, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip389_checked : ∀ j : Fin (512 - firstU (⟨63, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨63, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨63, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock03_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock03 k) := by
  fin_cases k
  · exact strip374_checked
  · exact strip375_checked
  · exact strip376_checked
  · exact strip377_checked
  · exact strip378_checked
  · exact strip379_checked
  · exact strip380_checked
  · exact strip381_checked
  · exact strip382_checked
  · exact strip383_checked
  · exact strip384_checked
  · exact strip385_checked
  · exact strip386_checked
  · exact strip387_checked
  · exact strip388_checked
  · exact strip389_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
