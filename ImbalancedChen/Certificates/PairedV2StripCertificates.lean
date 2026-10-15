import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore
import ImbalancedChen.Certificates.PairedV2StripCertificatesBlock00
import ImbalancedChen.Certificates.PairedV2StripCertificatesBlock01
import ImbalancedChen.Certificates.PairedV2StripCertificatesBlock02
import ImbalancedChen.Certificates.PairedV2StripCertificatesBlock03
import ImbalancedChen.Certificates.PairedV2StripCertificatesBlock04
import ImbalancedChen.Certificates.PairedV2StripCertificatesBlock05
import ImbalancedChen.Certificates.PairedV2StripCertificatesBlock06
import ImbalancedChen.Certificates.PairedV2StripCertificatesBlock07
import ImbalancedChen.Certificates.PairedV2StripCertificatesBlock08
import ImbalancedChen.Certificates.PairedV2StripCertificatesBlock09
import ImbalancedChen.Certificates.PairedV2StripCertificatesBlock10
import ImbalancedChen.Certificates.PairedV2StripCertificatesBlock11

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Two-branch proof composition for original strip blocks 01–02. -/
theorem checkedBlocks01_02 : ∀ k : Fin 32, StripAssembly.StripChecked ((Fin.castAdd 90 (Fin.castAdd 48 (Fin.natAdd 16 k)))) := by
  exact StripAssembly.joinChecked (m := 16) (n := 16)
    (fun k : Fin 32 => (Fin.castAdd 90 (Fin.castAdd 48 (Fin.natAdd 16 k))))
    stripBlock01_checked stripBlock02_checked

/-- Two-branch proof composition for original strip blocks 00–02. -/
theorem checkedBlocks00_02 : ∀ k : Fin 48, StripAssembly.StripChecked ((Fin.castAdd 90 (Fin.castAdd 48 k))) := by
  exact StripAssembly.joinChecked (m := 16) (n := 32)
    (fun k : Fin 48 => (Fin.castAdd 90 (Fin.castAdd 48 k)))
    stripBlock00_checked checkedBlocks01_02

/-- Two-branch proof composition for original strip blocks 04–05. -/
theorem checkedBlocks04_05 : ∀ k : Fin 32, StripAssembly.StripChecked ((Fin.castAdd 90 (Fin.natAdd 48 (Fin.natAdd 16 k)))) := by
  exact StripAssembly.joinChecked (m := 16) (n := 16)
    (fun k : Fin 32 => (Fin.castAdd 90 (Fin.natAdd 48 (Fin.natAdd 16 k))))
    stripBlock04_checked stripBlock05_checked

/-- Two-branch proof composition for original strip blocks 03–05. -/
theorem checkedBlocks03_05 : ∀ k : Fin 48, StripAssembly.StripChecked ((Fin.castAdd 90 (Fin.natAdd 48 k))) := by
  exact StripAssembly.joinChecked (m := 16) (n := 32)
    (fun k : Fin 48 => (Fin.castAdd 90 (Fin.natAdd 48 k)))
    stripBlock03_checked checkedBlocks04_05

/-- Two-branch proof composition for original strip blocks 00–05. -/
theorem checkedBlocks00_05 : ∀ k : Fin 96, StripAssembly.StripChecked ((Fin.castAdd 90 k)) := by
  exact StripAssembly.joinChecked (m := 48) (n := 48)
    (fun k : Fin 96 => (Fin.castAdd 90 k))
    checkedBlocks00_02 checkedBlocks03_05

/-- Two-branch proof composition for original strip blocks 07–08. -/
theorem checkedBlocks07_08 : ∀ k : Fin 32, StripAssembly.StripChecked ((Fin.natAdd 96 (Fin.castAdd 42 (Fin.natAdd 16 k)))) := by
  exact StripAssembly.joinChecked (m := 16) (n := 16)
    (fun k : Fin 32 => (Fin.natAdd 96 (Fin.castAdd 42 (Fin.natAdd 16 k))))
    stripBlock07_checked stripBlock08_checked

/-- Two-branch proof composition for original strip blocks 06–08. -/
theorem checkedBlocks06_08 : ∀ k : Fin 48, StripAssembly.StripChecked ((Fin.natAdd 96 (Fin.castAdd 42 k))) := by
  exact StripAssembly.joinChecked (m := 16) (n := 32)
    (fun k : Fin 48 => (Fin.natAdd 96 (Fin.castAdd 42 k)))
    stripBlock06_checked checkedBlocks07_08

/-- Two-branch proof composition for original strip blocks 10–11. -/
theorem checkedBlocks10_11 : ∀ k : Fin 26, StripAssembly.StripChecked ((Fin.natAdd 96 (Fin.natAdd 48 (Fin.natAdd 16 k)))) := by
  exact StripAssembly.joinChecked (m := 16) (n := 10)
    (fun k : Fin 26 => (Fin.natAdd 96 (Fin.natAdd 48 (Fin.natAdd 16 k))))
    stripBlock10_checked stripBlock11_checked

/-- Two-branch proof composition for original strip blocks 09–11. -/
theorem checkedBlocks09_11 : ∀ k : Fin 42, StripAssembly.StripChecked ((Fin.natAdd 96 (Fin.natAdd 48 k))) := by
  exact StripAssembly.joinChecked (m := 16) (n := 26)
    (fun k : Fin 42 => (Fin.natAdd 96 (Fin.natAdd 48 k)))
    stripBlock09_checked checkedBlocks10_11

/-- Two-branch proof composition for original strip blocks 06–11. -/
theorem checkedBlocks06_11 : ∀ k : Fin 90, StripAssembly.StripChecked ((Fin.natAdd 96 k)) := by
  exact StripAssembly.joinChecked (m := 48) (n := 42)
    (fun k : Fin 90 => (Fin.natAdd 96 k))
    checkedBlocks06_08 checkedBlocks09_11

/-- Two-branch proof composition for original strip blocks 00–11. -/
theorem allStrips_checked : ∀ k : Fin 186, StripAssembly.StripChecked (k) := by
  exact StripAssembly.joinChecked (m := 96) (n := 90)
    (fun k : Fin 186 => k)
    checkedBlocks00_05 checkedBlocks06_11

theorem strip_certificates_checked (i : Fin 186) (j : Fin (512 - firstU i)) :
    (makeCertificate ⟨i,j⟩ (approximation ⟨i,j⟩)).check = true := by
  exact allStrips_checked i j

end ImbalancedChen.Certificates.PairedV2.FullMask
