import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Window
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check

/- Full original Block00: 64 pages of 64 original updates.
Every page uses kernel reduction and retains the same universally quantified tail.
Page00 is imported from the accepted module; shared generated equations keep their owner. -/

namespace ImbalancedChen.OriginalU2StoredNodeBlock00FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly

theorem block00_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 32769 64 = true :=
  ImbalancedChen.OriginalU2StoredNodeBlockPilotSourceOnly.block00_page00_checked tail

theorem block00_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 32833 64 = true := by
  have hread (i : Nat) (hi : i ≤ 32896) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 32833 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 32833+k ≤ 32896 := by omega
  have hprev : 32833+k-1 ≤ 32896 := by omega
  have h0 : ¬ 32833+k ≤ 32768 := by omega
  have h4 : 32833+k ≤ 65536 := by omega
  have h3 : 32833+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (32833+k) hi, hread (32833+k-1) hprev]
  exact hs

theorem block00_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 32897 64 = true := by
  have hread (i : Nat) (hi : i ≤ 32960) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 32897 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 32897+k ≤ 32960 := by omega
  have hprev : 32897+k-1 ≤ 32960 := by omega
  have h0 : ¬ 32897+k ≤ 32768 := by omega
  have h4 : 32897+k ≤ 65536 := by omega
  have h3 : 32897+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (32897+k) hi, hread (32897+k-1) hprev]
  exact hs

theorem block00_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 32961 64 = true := by
  have hread (i : Nat) (hi : i ≤ 33024) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 32961 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 32961+k ≤ 33024 := by omega
  have hprev : 32961+k-1 ≤ 33024 := by omega
  have h0 : ¬ 32961+k ≤ 32768 := by omega
  have h4 : 32961+k ≤ 65536 := by omega
  have h3 : 32961+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (32961+k) hi, hread (32961+k-1) hprev]
  exact hs

theorem block00_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 33025 64 = true := by
  have hread (i : Nat) (hi : i ≤ 33088) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 33025 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 33025+k ≤ 33088 := by omega
  have hprev : 33025+k-1 ≤ 33088 := by omega
  have h0 : ¬ 33025+k ≤ 32768 := by omega
  have h4 : 33025+k ≤ 65536 := by omega
  have h3 : 33025+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (33025+k) hi, hread (33025+k-1) hprev]
  exact hs

theorem block00_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 33089 64 = true := by
  have hread (i : Nat) (hi : i ≤ 33152) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 33089 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 33089+k ≤ 33152 := by omega
  have hprev : 33089+k-1 ≤ 33152 := by omega
  have h0 : ¬ 33089+k ≤ 32768 := by omega
  have h4 : 33089+k ≤ 65536 := by omega
  have h3 : 33089+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (33089+k) hi, hread (33089+k-1) hprev]
  exact hs

theorem block00_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 33153 64 = true := by
  have hread (i : Nat) (hi : i ≤ 33216) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 33153 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 33153+k ≤ 33216 := by omega
  have hprev : 33153+k-1 ≤ 33216 := by omega
  have h0 : ¬ 33153+k ≤ 32768 := by omega
  have h4 : 33153+k ≤ 65536 := by omega
  have h3 : 33153+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (33153+k) hi, hread (33153+k-1) hprev]
  exact hs

theorem block00_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 33217 64 = true := by
  have hread (i : Nat) (hi : i ≤ 33280) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 33217 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 33217+k ≤ 33280 := by omega
  have hprev : 33217+k-1 ≤ 33280 := by omega
  have h0 : ¬ 33217+k ≤ 32768 := by omega
  have h4 : 33217+k ≤ 65536 := by omega
  have h3 : 33217+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (33217+k) hi, hread (33217+k-1) hprev]
  exact hs

theorem block00_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 33281 64 = true := by
  have hread (i : Nat) (hi : i ≤ 33344) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 33281 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 33281+k ≤ 33344 := by omega
  have hprev : 33281+k-1 ≤ 33344 := by omega
  have h0 : ¬ 33281+k ≤ 32768 := by omega
  have h4 : 33281+k ≤ 65536 := by omega
  have h3 : 33281+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (33281+k) hi, hread (33281+k-1) hprev]
  exact hs

theorem block00_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 33345 64 = true := by
  have hread (i : Nat) (hi : i ≤ 33408) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 33345 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 33345+k ≤ 33408 := by omega
  have hprev : 33345+k-1 ≤ 33408 := by omega
  have h0 : ¬ 33345+k ≤ 32768 := by omega
  have h4 : 33345+k ≤ 65536 := by omega
  have h3 : 33345+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (33345+k) hi, hread (33345+k-1) hprev]
  exact hs

theorem block00_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 33409 64 = true := by
  have hread (i : Nat) (hi : i ≤ 33472) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 33409 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 33409+k ≤ 33472 := by omega
  have hprev : 33409+k-1 ≤ 33472 := by omega
  have h0 : ¬ 33409+k ≤ 32768 := by omega
  have h4 : 33409+k ≤ 65536 := by omega
  have h3 : 33409+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (33409+k) hi, hread (33409+k-1) hprev]
  exact hs

theorem block00_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 33473 64 = true := by
  have hread (i : Nat) (hi : i ≤ 33536) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 33473 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 33473+k ≤ 33536 := by omega
  have hprev : 33473+k-1 ≤ 33536 := by omega
  have h0 : ¬ 33473+k ≤ 32768 := by omega
  have h4 : 33473+k ≤ 65536 := by omega
  have h3 : 33473+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (33473+k) hi, hread (33473+k-1) hprev]
  exact hs

theorem block00_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 33537 64 = true := by
  have hread (i : Nat) (hi : i ≤ 33600) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 33537 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 33537+k ≤ 33600 := by omega
  have hprev : 33537+k-1 ≤ 33600 := by omega
  have h0 : ¬ 33537+k ≤ 32768 := by omega
  have h4 : 33537+k ≤ 65536 := by omega
  have h3 : 33537+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (33537+k) hi, hread (33537+k-1) hprev]
  exact hs

theorem block00_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 33601 64 = true := by
  have hread (i : Nat) (hi : i ≤ 33664) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 33601 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 33601+k ≤ 33664 := by omega
  have hprev : 33601+k-1 ≤ 33664 := by omega
  have h0 : ¬ 33601+k ≤ 32768 := by omega
  have h4 : 33601+k ≤ 65536 := by omega
  have h3 : 33601+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (33601+k) hi, hread (33601+k-1) hprev]
  exact hs

theorem block00_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 33665 64 = true := by
  have hread (i : Nat) (hi : i ≤ 33728) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 33665 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 33665+k ≤ 33728 := by omega
  have hprev : 33665+k-1 ≤ 33728 := by omega
  have h0 : ¬ 33665+k ≤ 32768 := by omega
  have h4 : 33665+k ≤ 65536 := by omega
  have h3 : 33665+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (33665+k) hi, hread (33665+k-1) hprev]
  exact hs

theorem block00_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 33729 64 = true := by
  have hread (i : Nat) (hi : i ≤ 33792) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 33729 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 33729+k ≤ 33792 := by omega
  have hprev : 33729+k-1 ≤ 33792 := by omega
  have h0 : ¬ 33729+k ≤ 32768 := by omega
  have h4 : 33729+k ≤ 65536 := by omega
  have h3 : 33729+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (33729+k) hi, hread (33729+k-1) hprev]
  exact hs

theorem block00_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 33793 64 = true := by
  have hread (i : Nat) (hi : i ≤ 33856) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 33793 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 33793+k ≤ 33856 := by omega
  have hprev : 33793+k-1 ≤ 33856 := by omega
  have h0 : ¬ 33793+k ≤ 32768 := by omega
  have h4 : 33793+k ≤ 65536 := by omega
  have h3 : 33793+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (33793+k) hi, hread (33793+k-1) hprev]
  exact hs

theorem block00_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 33857 64 = true := by
  have hread (i : Nat) (hi : i ≤ 33920) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 33857 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 33857+k ≤ 33920 := by omega
  have hprev : 33857+k-1 ≤ 33920 := by omega
  have h0 : ¬ 33857+k ≤ 32768 := by omega
  have h4 : 33857+k ≤ 65536 := by omega
  have h3 : 33857+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (33857+k) hi, hread (33857+k-1) hprev]
  exact hs

theorem block00_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 33921 64 = true := by
  have hread (i : Nat) (hi : i ≤ 33984) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 33921 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 33921+k ≤ 33984 := by omega
  have hprev : 33921+k-1 ≤ 33984 := by omega
  have h0 : ¬ 33921+k ≤ 32768 := by omega
  have h4 : 33921+k ≤ 65536 := by omega
  have h3 : 33921+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (33921+k) hi, hread (33921+k-1) hprev]
  exact hs

theorem block00_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 33985 64 = true := by
  have hread (i : Nat) (hi : i ≤ 34048) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 33985 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 33985+k ≤ 34048 := by omega
  have hprev : 33985+k-1 ≤ 34048 := by omega
  have h0 : ¬ 33985+k ≤ 32768 := by omega
  have h4 : 33985+k ≤ 65536 := by omega
  have h3 : 33985+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (33985+k) hi, hread (33985+k-1) hprev]
  exact hs

theorem block00_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 34049 64 = true := by
  have hread (i : Nat) (hi : i ≤ 34112) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 34049 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 34049+k ≤ 34112 := by omega
  have hprev : 34049+k-1 ≤ 34112 := by omega
  have h0 : ¬ 34049+k ≤ 32768 := by omega
  have h4 : 34049+k ≤ 65536 := by omega
  have h3 : 34049+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (34049+k) hi, hread (34049+k-1) hprev]
  exact hs

theorem block00_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 34113 64 = true := by
  have hread (i : Nat) (hi : i ≤ 34176) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 34113 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 34113+k ≤ 34176 := by omega
  have hprev : 34113+k-1 ≤ 34176 := by omega
  have h0 : ¬ 34113+k ≤ 32768 := by omega
  have h4 : 34113+k ≤ 65536 := by omega
  have h3 : 34113+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (34113+k) hi, hread (34113+k-1) hprev]
  exact hs

theorem block00_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 34177 64 = true := by
  have hread (i : Nat) (hi : i ≤ 34240) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 34177 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 34177+k ≤ 34240 := by omega
  have hprev : 34177+k-1 ≤ 34240 := by omega
  have h0 : ¬ 34177+k ≤ 32768 := by omega
  have h4 : 34177+k ≤ 65536 := by omega
  have h3 : 34177+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (34177+k) hi, hread (34177+k-1) hprev]
  exact hs

theorem block00_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 34241 64 = true := by
  have hread (i : Nat) (hi : i ≤ 34304) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 34241 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 34241+k ≤ 34304 := by omega
  have hprev : 34241+k-1 ≤ 34304 := by omega
  have h0 : ¬ 34241+k ≤ 32768 := by omega
  have h4 : 34241+k ≤ 65536 := by omega
  have h3 : 34241+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (34241+k) hi, hread (34241+k-1) hprev]
  exact hs

theorem block00_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 34305 64 = true := by
  have hread (i : Nat) (hi : i ≤ 34368) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 34305 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 34305+k ≤ 34368 := by omega
  have hprev : 34305+k-1 ≤ 34368 := by omega
  have h0 : ¬ 34305+k ≤ 32768 := by omega
  have h4 : 34305+k ≤ 65536 := by omega
  have h3 : 34305+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (34305+k) hi, hread (34305+k-1) hprev]
  exact hs

theorem block00_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 34369 64 = true := by
  have hread (i : Nat) (hi : i ≤ 34432) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 34369 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 34369+k ≤ 34432 := by omega
  have hprev : 34369+k-1 ≤ 34432 := by omega
  have h0 : ¬ 34369+k ≤ 32768 := by omega
  have h4 : 34369+k ≤ 65536 := by omega
  have h3 : 34369+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (34369+k) hi, hread (34369+k-1) hprev]
  exact hs

theorem block00_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 34433 64 = true := by
  have hread (i : Nat) (hi : i ≤ 34496) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 34433 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 34433+k ≤ 34496 := by omega
  have hprev : 34433+k-1 ≤ 34496 := by omega
  have h0 : ¬ 34433+k ≤ 32768 := by omega
  have h4 : 34433+k ≤ 65536 := by omega
  have h3 : 34433+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (34433+k) hi, hread (34433+k-1) hprev]
  exact hs

theorem block00_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 34497 64 = true := by
  have hread (i : Nat) (hi : i ≤ 34560) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 34497 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 34497+k ≤ 34560 := by omega
  have hprev : 34497+k-1 ≤ 34560 := by omega
  have h0 : ¬ 34497+k ≤ 32768 := by omega
  have h4 : 34497+k ≤ 65536 := by omega
  have h3 : 34497+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (34497+k) hi, hread (34497+k-1) hprev]
  exact hs

theorem block00_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 34561 64 = true := by
  have hread (i : Nat) (hi : i ≤ 34624) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 34561 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 34561+k ≤ 34624 := by omega
  have hprev : 34561+k-1 ≤ 34624 := by omega
  have h0 : ¬ 34561+k ≤ 32768 := by omega
  have h4 : 34561+k ≤ 65536 := by omega
  have h3 : 34561+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (34561+k) hi, hread (34561+k-1) hprev]
  exact hs

theorem block00_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 34625 64 = true := by
  have hread (i : Nat) (hi : i ≤ 34688) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 34625 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 34625+k ≤ 34688 := by omega
  have hprev : 34625+k-1 ≤ 34688 := by omega
  have h0 : ¬ 34625+k ≤ 32768 := by omega
  have h4 : 34625+k ≤ 65536 := by omega
  have h3 : 34625+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (34625+k) hi, hread (34625+k-1) hprev]
  exact hs

theorem block00_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 34689 64 = true := by
  have hread (i : Nat) (hi : i ≤ 34752) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 34689 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 34689+k ≤ 34752 := by omega
  have hprev : 34689+k-1 ≤ 34752 := by omega
  have h0 : ¬ 34689+k ≤ 32768 := by omega
  have h4 : 34689+k ≤ 65536 := by omega
  have h3 : 34689+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (34689+k) hi, hread (34689+k-1) hprev]
  exact hs

theorem block00_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 34753 64 = true := by
  have hread (i : Nat) (hi : i ≤ 34816) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 34753 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 34753+k ≤ 34816 := by omega
  have hprev : 34753+k-1 ≤ 34816 := by omega
  have h0 : ¬ 34753+k ≤ 32768 := by omega
  have h4 : 34753+k ≤ 65536 := by omega
  have h3 : 34753+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (34753+k) hi, hread (34753+k-1) hprev]
  exact hs

theorem block00_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 34817 64 = true := by
  have hread (i : Nat) (hi : i ≤ 34880) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 34817 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 34817+k ≤ 34880 := by omega
  have hprev : 34817+k-1 ≤ 34880 := by omega
  have h0 : ¬ 34817+k ≤ 32768 := by omega
  have h4 : 34817+k ≤ 65536 := by omega
  have h3 : 34817+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (34817+k) hi, hread (34817+k-1) hprev]
  exact hs

theorem block00_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 34881 64 = true := by
  have hread (i : Nat) (hi : i ≤ 34944) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 34881 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 34881+k ≤ 34944 := by omega
  have hprev : 34881+k-1 ≤ 34944 := by omega
  have h0 : ¬ 34881+k ≤ 32768 := by omega
  have h4 : 34881+k ≤ 65536 := by omega
  have h3 : 34881+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (34881+k) hi, hread (34881+k-1) hprev]
  exact hs

theorem block00_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 34945 64 = true := by
  have hread (i : Nat) (hi : i ≤ 35008) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 34945 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 34945+k ≤ 35008 := by omega
  have hprev : 34945+k-1 ≤ 35008 := by omega
  have h0 : ¬ 34945+k ≤ 32768 := by omega
  have h4 : 34945+k ≤ 65536 := by omega
  have h3 : 34945+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (34945+k) hi, hread (34945+k-1) hprev]
  exact hs

theorem block00_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 35009 64 = true := by
  have hread (i : Nat) (hi : i ≤ 35072) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 35009 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 35009+k ≤ 35072 := by omega
  have hprev : 35009+k-1 ≤ 35072 := by omega
  have h0 : ¬ 35009+k ≤ 32768 := by omega
  have h4 : 35009+k ≤ 65536 := by omega
  have h3 : 35009+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (35009+k) hi, hread (35009+k-1) hprev]
  exact hs

theorem block00_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 35073 64 = true := by
  have hread (i : Nat) (hi : i ≤ 35136) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 35073 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 35073+k ≤ 35136 := by omega
  have hprev : 35073+k-1 ≤ 35136 := by omega
  have h0 : ¬ 35073+k ≤ 32768 := by omega
  have h4 : 35073+k ≤ 65536 := by omega
  have h3 : 35073+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (35073+k) hi, hread (35073+k-1) hprev]
  exact hs

theorem block00_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 35137 64 = true := by
  have hread (i : Nat) (hi : i ≤ 35200) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 35137 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 35137+k ≤ 35200 := by omega
  have hprev : 35137+k-1 ≤ 35200 := by omega
  have h0 : ¬ 35137+k ≤ 32768 := by omega
  have h4 : 35137+k ≤ 65536 := by omega
  have h3 : 35137+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (35137+k) hi, hread (35137+k-1) hprev]
  exact hs

theorem block00_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 35201 64 = true := by
  have hread (i : Nat) (hi : i ≤ 35264) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 35201 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 35201+k ≤ 35264 := by omega
  have hprev : 35201+k-1 ≤ 35264 := by omega
  have h0 : ¬ 35201+k ≤ 32768 := by omega
  have h4 : 35201+k ≤ 65536 := by omega
  have h3 : 35201+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (35201+k) hi, hread (35201+k-1) hprev]
  exact hs

theorem block00_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 35265 64 = true := by
  have hread (i : Nat) (hi : i ≤ 35328) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 35265 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 35265+k ≤ 35328 := by omega
  have hprev : 35265+k-1 ≤ 35328 := by omega
  have h0 : ¬ 35265+k ≤ 32768 := by omega
  have h4 : 35265+k ≤ 65536 := by omega
  have h3 : 35265+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (35265+k) hi, hread (35265+k-1) hprev]
  exact hs

theorem block00_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 35329 64 = true := by
  have hread (i : Nat) (hi : i ≤ 35392) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 35329 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 35329+k ≤ 35392 := by omega
  have hprev : 35329+k-1 ≤ 35392 := by omega
  have h0 : ¬ 35329+k ≤ 32768 := by omega
  have h4 : 35329+k ≤ 65536 := by omega
  have h3 : 35329+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (35329+k) hi, hread (35329+k-1) hprev]
  exact hs

theorem block00_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 35393 64 = true := by
  have hread (i : Nat) (hi : i ≤ 35456) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 35393 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 35393+k ≤ 35456 := by omega
  have hprev : 35393+k-1 ≤ 35456 := by omega
  have h0 : ¬ 35393+k ≤ 32768 := by omega
  have h4 : 35393+k ≤ 65536 := by omega
  have h3 : 35393+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (35393+k) hi, hread (35393+k-1) hprev]
  exact hs

theorem block00_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 35457 64 = true := by
  have hread (i : Nat) (hi : i ≤ 35520) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 35457 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 35457+k ≤ 35520 := by omega
  have hprev : 35457+k-1 ≤ 35520 := by omega
  have h0 : ¬ 35457+k ≤ 32768 := by omega
  have h4 : 35457+k ≤ 65536 := by omega
  have h3 : 35457+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (35457+k) hi, hread (35457+k-1) hprev]
  exact hs

theorem block00_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 35521 64 = true := by
  have hread (i : Nat) (hi : i ≤ 35584) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 35521 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 35521+k ≤ 35584 := by omega
  have hprev : 35521+k-1 ≤ 35584 := by omega
  have h0 : ¬ 35521+k ≤ 32768 := by omega
  have h4 : 35521+k ≤ 65536 := by omega
  have h3 : 35521+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (35521+k) hi, hread (35521+k-1) hprev]
  exact hs

theorem block00_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 35585 64 = true := by
  have hread (i : Nat) (hi : i ≤ 35648) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 35585 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 35585+k ≤ 35648 := by omega
  have hprev : 35585+k-1 ≤ 35648 := by omega
  have h0 : ¬ 35585+k ≤ 32768 := by omega
  have h4 : 35585+k ≤ 65536 := by omega
  have h3 : 35585+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (35585+k) hi, hread (35585+k-1) hprev]
  exact hs

theorem block00_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 35649 64 = true := by
  have hread (i : Nat) (hi : i ≤ 35712) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 35649 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 35649+k ≤ 35712 := by omega
  have hprev : 35649+k-1 ≤ 35712 := by omega
  have h0 : ¬ 35649+k ≤ 32768 := by omega
  have h4 : 35649+k ≤ 65536 := by omega
  have h3 : 35649+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (35649+k) hi, hread (35649+k-1) hprev]
  exact hs

theorem block00_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 35713 64 = true := by
  have hread (i : Nat) (hi : i ≤ 35776) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 35713 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 35713+k ≤ 35776 := by omega
  have hprev : 35713+k-1 ≤ 35776 := by omega
  have h0 : ¬ 35713+k ≤ 32768 := by omega
  have h4 : 35713+k ≤ 65536 := by omega
  have h3 : 35713+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (35713+k) hi, hread (35713+k-1) hprev]
  exact hs

theorem block00_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 35777 64 = true := by
  have hread (i : Nat) (hi : i ≤ 35840) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 35777 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 35777+k ≤ 35840 := by omega
  have hprev : 35777+k-1 ≤ 35840 := by omega
  have h0 : ¬ 35777+k ≤ 32768 := by omega
  have h4 : 35777+k ≤ 65536 := by omega
  have h3 : 35777+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (35777+k) hi, hread (35777+k-1) hprev]
  exact hs

theorem block00_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 35841 64 = true := by
  have hread (i : Nat) (hi : i ≤ 35904) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 35841 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 35841+k ≤ 35904 := by omega
  have hprev : 35841+k-1 ≤ 35904 := by omega
  have h0 : ¬ 35841+k ≤ 32768 := by omega
  have h4 : 35841+k ≤ 65536 := by omega
  have h3 : 35841+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (35841+k) hi, hread (35841+k-1) hprev]
  exact hs

theorem block00_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 35905 64 = true := by
  have hread (i : Nat) (hi : i ≤ 35968) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 35905 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 35905+k ≤ 35968 := by omega
  have hprev : 35905+k-1 ≤ 35968 := by omega
  have h0 : ¬ 35905+k ≤ 32768 := by omega
  have h4 : 35905+k ≤ 65536 := by omega
  have h3 : 35905+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (35905+k) hi, hread (35905+k-1) hprev]
  exact hs

theorem block00_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 35969 64 = true := by
  have hread (i : Nat) (hi : i ≤ 36032) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 35969 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 35969+k ≤ 36032 := by omega
  have hprev : 35969+k-1 ≤ 36032 := by omega
  have h0 : ¬ 35969+k ≤ 32768 := by omega
  have h4 : 35969+k ≤ 65536 := by omega
  have h3 : 35969+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (35969+k) hi, hread (35969+k-1) hprev]
  exact hs

theorem block00_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 36033 64 = true := by
  have hread (i : Nat) (hi : i ≤ 36096) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 36033 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 36033+k ≤ 36096 := by omega
  have hprev : 36033+k-1 ≤ 36096 := by omega
  have h0 : ¬ 36033+k ≤ 32768 := by omega
  have h4 : 36033+k ≤ 65536 := by omega
  have h3 : 36033+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (36033+k) hi, hread (36033+k-1) hprev]
  exact hs

theorem block00_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 36097 64 = true := by
  have hread (i : Nat) (hi : i ≤ 36160) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 36097 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 36097+k ≤ 36160 := by omega
  have hprev : 36097+k-1 ≤ 36160 := by omega
  have h0 : ¬ 36097+k ≤ 32768 := by omega
  have h4 : 36097+k ≤ 65536 := by omega
  have h3 : 36097+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (36097+k) hi, hread (36097+k-1) hprev]
  exact hs

theorem block00_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 36161 64 = true := by
  have hread (i : Nat) (hi : i ≤ 36224) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 36161 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 36161+k ≤ 36224 := by omega
  have hprev : 36161+k-1 ≤ 36224 := by omega
  have h0 : ¬ 36161+k ≤ 32768 := by omega
  have h4 : 36161+k ≤ 65536 := by omega
  have h3 : 36161+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (36161+k) hi, hread (36161+k-1) hprev]
  exact hs

theorem block00_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 36225 64 = true := by
  have hread (i : Nat) (hi : i ≤ 36288) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 36225 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 36225+k ≤ 36288 := by omega
  have hprev : 36225+k-1 ≤ 36288 := by omega
  have h0 : ¬ 36225+k ≤ 32768 := by omega
  have h4 : 36225+k ≤ 65536 := by omega
  have h3 : 36225+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (36225+k) hi, hread (36225+k-1) hprev]
  exact hs

theorem block00_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 36289 64 = true := by
  have hread (i : Nat) (hi : i ≤ 36352) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 36289 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 36289+k ≤ 36352 := by omega
  have hprev : 36289+k-1 ≤ 36352 := by omega
  have h0 : ¬ 36289+k ≤ 32768 := by omega
  have h4 : 36289+k ≤ 65536 := by omega
  have h3 : 36289+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (36289+k) hi, hread (36289+k-1) hprev]
  exact hs

theorem block00_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 36353 64 = true := by
  have hread (i : Nat) (hi : i ≤ 36416) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 36353 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 36353+k ≤ 36416 := by omega
  have hprev : 36353+k-1 ≤ 36416 := by omega
  have h0 : ¬ 36353+k ≤ 32768 := by omega
  have h4 : 36353+k ≤ 65536 := by omega
  have h3 : 36353+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (36353+k) hi, hread (36353+k-1) hprev]
  exact hs

theorem block00_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 36417 64 = true := by
  have hread (i : Nat) (hi : i ≤ 36480) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 36417 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 36417+k ≤ 36480 := by omega
  have hprev : 36417+k-1 ≤ 36480 := by omega
  have h0 : ¬ 36417+k ≤ 32768 := by omega
  have h4 : 36417+k ≤ 65536 := by omega
  have h3 : 36417+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (36417+k) hi, hread (36417+k-1) hprev]
  exact hs

theorem block00_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 36481 64 = true := by
  have hread (i : Nat) (hi : i ≤ 36544) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 36481 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 36481+k ≤ 36544 := by omega
  have hprev : 36481+k-1 ≤ 36544 := by omega
  have h0 : ¬ 36481+k ≤ 32768 := by omega
  have h4 : 36481+k ≤ 65536 := by omega
  have h3 : 36481+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (36481+k) hi, hread (36481+k-1) hprev]
  exact hs

theorem block00_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 36545 64 = true := by
  have hread (i : Nat) (hi : i ≤ 36608) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 36545 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 36545+k ≤ 36608 := by omega
  have hprev : 36545+k-1 ≤ 36608 := by omega
  have h0 : ¬ 36545+k ≤ 32768 := by omega
  have h4 : 36545+k ≤ 65536 := by omega
  have h3 : 36545+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (36545+k) hi, hread (36545+k-1) hprev]
  exact hs

theorem block00_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 36609 64 = true := by
  have hread (i : Nat) (hi : i ≤ 36672) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 36609 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 36609+k ≤ 36672 := by omega
  have hprev : 36609+k-1 ≤ 36672 := by omega
  have h0 : ¬ 36609+k ≤ 32768 := by omega
  have h4 : 36609+k ≤ 65536 := by omega
  have h3 : 36609+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (36609+k) hi, hread (36609+k-1) hprev]
  exact hs

theorem block00_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 36673 64 = true := by
  have hread (i : Nat) (hi : i ≤ 36736) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 36673 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 36673+k ≤ 36736 := by omega
  have hprev : 36673+k-1 ≤ 36736 := by omega
  have h0 : ¬ 36673+k ≤ 32768 := by omega
  have h4 : 36673+k ≤ 65536 := by omega
  have h3 : 36673+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (36673+k) hi, hread (36673+k-1) hprev]
  exact hs

theorem block00_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 36737 64 = true := by
  have hread (i : Nat) (hi : i ≤ 36800) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 36737 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 36737+k ≤ 36800 := by omega
  have hprev : 36737+k-1 ≤ 36800 := by omega
  have h0 : ¬ 36737+k ≤ 32768 := by omega
  have h4 : 36737+k ≤ 65536 := by omega
  have h3 : 36737+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (36737+k) hi, hread (36737+k-1) hprev]
  exact hs

theorem block00_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 36801 64 = true := by
  have hread (i : Nat) (hi : i ≤ 36864) :
      assembledRead (window00 tail) i =
        assembledRead (fun _ : Nat => block00) i := by
    by_cases hp : i ≤ 32768
    · simp only [assembledRead, assembledRawRead, if_pos hp]
    · have hmax : i ≤ 196608 := by omega
      have hzero : (i-32769)/4096=0 := by omega
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
        hzero, window00, ite_true]
  have hclosed :
      readCheckBlock (assembledRead (fun _ : Nat => block00)) 36801 64 = true := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64 := List.mem_range.mp hk
  have hi : 36801+k ≤ 36864 := by omega
  have hprev : 36801+k-1 ≤ 36864 := by omega
  have h0 : ¬ 36801+k ≤ 32768 := by omega
  have h4 : 36801+k ≤ 65536 := by omega
  have h3 : 36801+k ≤ 49152 := by omega
  have hs := readCheckBlock_step hclosed hk'
  simp only [readCheckStep, ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.checkedUpdate,
    if_neg h0, if_pos h4, if_pos h3] at hs ⊢
  rw [hread (36801+k) hi, hread (36801+k-1) hprev]
  exact hs

/-- Generic exact assembly of any finite run of 64-row page checks.
This proves the conjunction of supplied page checks without evaluating rows. -/
theorem readCheckBlock_of_64_page_count
    (read : Nat → ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly.OriginalNode) (lo pages : Nat)
    (hpages : ∀ p : Nat, p < pages →
      readCheckBlock read (lo + 64*p) 64 = true) :
    readCheckBlock read lo (64*pages) = true := by
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64*pages := List.mem_range.mp hk
  let p := k/64
  let r := k%64
  have hp : p < pages := by dsimp [p]; omega
  have hr : r < 64 := by dsimp [r]; omega
  have he : 64*p+r=k := by dsimp [p,r]; omega
  have hs : readCheckStep read (lo + 64*p + r) = true :=
    readCheckBlock_step (hpages p hp) hr
  have hindex : lo + 64*p + r = lo+k := by omega
  simpa only [hindex] using hs

/-- All 4096 original Block00 updates, rows 32769 through 36864. -/
theorem block00_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (window00 tail)) 32769 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (window00 tail)) (32769 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block00_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (window00 tail)) 32769 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock00FullSourceOnly
