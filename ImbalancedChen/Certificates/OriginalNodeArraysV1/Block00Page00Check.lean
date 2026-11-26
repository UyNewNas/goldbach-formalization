import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Window

/- SOURCEONLY uncompiled64-row kernel-check candidate, NOT an observed PASS.
No native oracle and no raised reduction budget. Tail remains universally
quantified; all actually used block slots are fixed by window00. -/

namespace ImbalancedChen.OriginalU2StoredNodeBlockPilotSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly

theorem block00_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 32769 64 = true := by
  have hread (i : Nat) (hi : i ≤ 32832) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 32769 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 32769+k ≤ 32832 := by omega
  have hprev : 32769+k-1 ≤ 32832 := by omega
  have h0 : ¬ 32769+k ≤ 32768 := by omega
  have h4 : 32769+k ≤ 65536 := by omega
  have h3 : 32769+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (32769+k) hi, hread (32769+k-1) hprev]
  exact hs

end ImbalancedChen.OriginalU2StoredNodeBlockPilotSourceOnly
