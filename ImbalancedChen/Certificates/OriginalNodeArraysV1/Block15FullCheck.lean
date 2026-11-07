-- SOURCEONLY generated candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission.
-- Page starts: 32769 + 4096*15 + 64*p; the full block ends at 98304.
-- raw Llo: E:\timot\Documents\FilesForGPT\Myath\goldbach-proof-continuation\.lake\proof-continuation\drafts\20261024d-original-node-arrays-ARTIFACT-ONLY\block-15.Llo.dec; bytes=143360; SHA256=95ed5409e588a7c058b0aea37044f2c710967df5ff75b08ca5e4177df105c26f
-- raw Lhi: E:\timot\Documents\FilesForGPT\Myath\goldbach-proof-continuation\.lake\proof-continuation\drafts\20261024d-original-node-arrays-ARTIFACT-ONLY\block-15.Lhi.dec; bytes=143360; SHA256=157ec9839b0f1e004d455cf7ab0ead8207eaac52ffd9d26066afa77d2d4a75e5
-- raw Hlo: E:\timot\Documents\FilesForGPT\Myath\goldbach-proof-continuation\.lake\proof-continuation\drafts\20261024d-original-node-arrays-ARTIFACT-ONLY\block-15.Hlo.dec; bytes=143360; SHA256=1c47587d4d2a98545e6cb7d004bce44d88b181d4d6eb3c6810a82cdbcbe9bdae
-- raw Hhi: E:\timot\Documents\FilesForGPT\Myath\goldbach-proof-continuation\.lake\proof-continuation\drafts\20261024d-original-node-arrays-ARTIFACT-ONLY\block-15.Hhi.dec; bytes=143360; SHA256=d846e2967e671a67bda3fa75854e8f08e4b29529c0b210444fde53bbb9ef6b33
-- Frozen manifest SHA256: c9528798da192706cedbfca63222dfc9b635577e566de1f8129705789916189d
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block10Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block11Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block14Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block15Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock15FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block15_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 94209 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 0 (by omega) (by decide +kernel))

theorem block15_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 94273 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 1 (by omega) (by decide +kernel))

theorem block15_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 94337 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 2 (by omega) (by decide +kernel))

theorem block15_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 94401 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 3 (by omega) (by decide +kernel))

theorem block15_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 94465 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 4 (by omega) (by decide +kernel))

theorem block15_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 94529 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 5 (by omega) (by decide +kernel))

theorem block15_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 94593 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 6 (by omega) (by decide +kernel))

theorem block15_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 94657 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 7 (by omega) (by decide +kernel))

theorem block15_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 94721 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 8 (by omega) (by decide +kernel))

theorem block15_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 94785 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 9 (by omega) (by decide +kernel))

theorem block15_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 94849 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 10 (by omega) (by decide +kernel))

theorem block15_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 94913 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 11 (by omega) (by decide +kernel))

theorem block15_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 94977 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 12 (by omega) (by decide +kernel))

theorem block15_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 95041 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 13 (by omega) (by decide +kernel))

theorem block15_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 95105 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 14 (by omega) (by decide +kernel))

theorem block15_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 95169 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 15 (by omega) (by decide +kernel))

theorem block15_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 95233 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 16 (by omega) (by decide +kernel))

theorem block15_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 95297 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 17 (by omega) (by decide +kernel))

theorem block15_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 95361 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 18 (by omega) (by decide +kernel))

theorem block15_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 95425 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 19 (by omega) (by decide +kernel))

theorem block15_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 95489 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 20 (by omega) (by decide +kernel))

theorem block15_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 95553 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 21 (by omega) (by decide +kernel))

theorem block15_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 95617 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 22 (by omega) (by decide +kernel))

theorem block15_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 95681 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 23 (by omega) (by decide +kernel))

theorem block15_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 95745 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 24 (by omega) (by decide +kernel))

theorem block15_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 95809 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 25 (by omega) (by decide +kernel))

theorem block15_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 95873 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 26 (by omega) (by decide +kernel))

theorem block15_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 95937 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 27 (by omega) (by decide +kernel))

theorem block15_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 96001 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 28 (by omega) (by decide +kernel))

theorem block15_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 96065 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 29 (by omega) (by decide +kernel))

theorem block15_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 96129 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 30 (by omega) (by decide +kernel))

theorem block15_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 96193 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 31 (by omega) (by decide +kernel))

theorem block15_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 96257 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 32 (by omega) (by decide +kernel))

theorem block15_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 96321 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 33 (by omega) (by decide +kernel))

theorem block15_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 96385 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 34 (by omega) (by decide +kernel))

theorem block15_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 96449 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 35 (by omega) (by decide +kernel))

theorem block15_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 96513 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 36 (by omega) (by decide +kernel))

theorem block15_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 96577 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 37 (by omega) (by decide +kernel))

theorem block15_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 96641 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 38 (by omega) (by decide +kernel))

theorem block15_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 96705 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 39 (by omega) (by decide +kernel))

theorem block15_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 96769 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 40 (by omega) (by decide +kernel))

theorem block15_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 96833 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 41 (by omega) (by decide +kernel))

theorem block15_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 96897 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 42 (by omega) (by decide +kernel))

theorem block15_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 96961 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 43 (by omega) (by decide +kernel))

theorem block15_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 97025 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 44 (by omega) (by decide +kernel))

theorem block15_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 97089 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 45 (by omega) (by decide +kernel))

theorem block15_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 97153 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 46 (by omega) (by decide +kernel))

theorem block15_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 97217 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 47 (by omega) (by decide +kernel))

theorem block15_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 97281 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 48 (by omega) (by decide +kernel))

theorem block15_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 97345 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 49 (by omega) (by decide +kernel))

theorem block15_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 97409 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 50 (by omega) (by decide +kernel))

theorem block15_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 97473 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 51 (by omega) (by decide +kernel))

theorem block15_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 97537 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 52 (by omega) (by decide +kernel))

theorem block15_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 97601 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 53 (by omega) (by decide +kernel))

theorem block15_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 97665 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 54 (by omega) (by decide +kernel))

theorem block15_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 97729 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 55 (by omega) (by decide +kernel))

theorem block15_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 97793 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 56 (by omega) (by decide +kernel))

theorem block15_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 97857 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 57 (by omega) (by decide +kernel))

theorem block15_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 97921 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 58 (by omega) (by decide +kernel))

theorem block15_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 97985 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 59 (by omega) (by decide +kernel))

theorem block15_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 98049 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 60 (by omega) (by decide +kernel))

theorem block15_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 98113 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 61 (by omega) (by decide +kernel))

theorem block15_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 98177 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 62 (by omega) (by decide +kernel))

theorem block15_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 98241 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 15 (by omega) (by omega) block10 block11 block14 block15 tail 63 (by omega) (by decide +kernel))

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

theorem block15_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 94209 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) (94209 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block15_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 15 block10 block11 block14 block15 tail)) 94209 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock15FullSourceOnly
