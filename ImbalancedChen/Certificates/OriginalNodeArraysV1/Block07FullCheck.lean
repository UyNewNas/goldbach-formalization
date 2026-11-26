-- SOURCEONLY generated candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- Block07 pages: indices 61441..65536 in 64-row pages; original step 1.
-- raw Llo: E:\timot\Documents\FilesForGPT\Myath\goldbach-proof-continuation\.lake\proof-continuation\drafts\20261024d-original-node-arrays-ARTIFACT-ONLY\block-07.Llo.dec bytes=143360 sha256=bd775489f8e8b5679026a265234863713caec4703b9067cc845be0b4491643e4
-- raw Lhi: E:\timot\Documents\FilesForGPT\Myath\goldbach-proof-continuation\.lake\proof-continuation\drafts\20261024d-original-node-arrays-ARTIFACT-ONLY\block-07.Lhi.dec bytes=143360 sha256=eb3a925ad9641569a45f4812d621cf31f86774e3714d2bdb92b7bfd22f1b1ae0
-- raw Hlo: E:\timot\Documents\FilesForGPT\Myath\goldbach-proof-continuation\.lake\proof-continuation\drafts\20261024d-original-node-arrays-ARTIFACT-ONLY\block-07.Hlo.dec bytes=143360 sha256=c3e159408dc2784c17f37da611a30bd0d0096f009dd21a2801f05d82e58a05ab
-- raw Hhi: E:\timot\Documents\FilesForGPT\Myath\goldbach-proof-continuation\.lake\proof-continuation\drafts\20261024d-original-node-arrays-ARTIFACT-ONLY\block-07.Hhi.dec bytes=143360 sha256=afdf18d2cfa08af02bc61ca6545d21f3ca731ad597a573fcd4d17193bb0d10fb
-- Block00Data.lean SHA256 078a7959c4aa7d162efbd66bd83d025ae10d5599b7c9490ac8df165f4774904c
-- Block01Data.lean SHA256 707ed0026d02a286da0675e31f2c3470b548b34bcf63da5ad9da4e09205dff78
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block02Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block03Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block06Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block07Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock07FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block07_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 61441 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 0 (by omega) (by decide +kernel))

theorem block07_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 61505 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 1 (by omega) (by decide +kernel))

theorem block07_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 61569 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 2 (by omega) (by decide +kernel))

theorem block07_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 61633 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 3 (by omega) (by decide +kernel))

theorem block07_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 61697 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 4 (by omega) (by decide +kernel))

theorem block07_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 61761 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 5 (by omega) (by decide +kernel))

theorem block07_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 61825 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 6 (by omega) (by decide +kernel))

theorem block07_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 61889 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 7 (by omega) (by decide +kernel))

theorem block07_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 61953 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 8 (by omega) (by decide +kernel))

theorem block07_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 62017 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 9 (by omega) (by decide +kernel))

theorem block07_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 62081 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 10 (by omega) (by decide +kernel))

theorem block07_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 62145 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 11 (by omega) (by decide +kernel))

theorem block07_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 62209 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 12 (by omega) (by decide +kernel))

theorem block07_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 62273 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 13 (by omega) (by decide +kernel))

theorem block07_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 62337 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 14 (by omega) (by decide +kernel))

theorem block07_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 62401 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 15 (by omega) (by decide +kernel))

theorem block07_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 62465 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 16 (by omega) (by decide +kernel))

theorem block07_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 62529 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 17 (by omega) (by decide +kernel))

theorem block07_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 62593 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 18 (by omega) (by decide +kernel))

theorem block07_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 62657 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 19 (by omega) (by decide +kernel))

theorem block07_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 62721 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 20 (by omega) (by decide +kernel))

theorem block07_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 62785 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 21 (by omega) (by decide +kernel))

theorem block07_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 62849 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 22 (by omega) (by decide +kernel))

theorem block07_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 62913 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 23 (by omega) (by decide +kernel))

theorem block07_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 62977 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 24 (by omega) (by decide +kernel))

theorem block07_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 63041 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 25 (by omega) (by decide +kernel))

theorem block07_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 63105 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 26 (by omega) (by decide +kernel))

theorem block07_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 63169 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 27 (by omega) (by decide +kernel))

theorem block07_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 63233 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 28 (by omega) (by decide +kernel))

theorem block07_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 63297 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 29 (by omega) (by decide +kernel))

theorem block07_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 63361 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 30 (by omega) (by decide +kernel))

theorem block07_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 63425 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 31 (by omega) (by decide +kernel))

theorem block07_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 63489 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 32 (by omega) (by decide +kernel))

theorem block07_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 63553 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 33 (by omega) (by decide +kernel))

theorem block07_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 63617 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 34 (by omega) (by decide +kernel))

theorem block07_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 63681 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 35 (by omega) (by decide +kernel))

theorem block07_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 63745 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 36 (by omega) (by decide +kernel))

theorem block07_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 63809 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 37 (by omega) (by decide +kernel))

theorem block07_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 63873 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 38 (by omega) (by decide +kernel))

theorem block07_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 63937 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 39 (by omega) (by decide +kernel))

theorem block07_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 64001 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 40 (by omega) (by decide +kernel))

theorem block07_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 64065 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 41 (by omega) (by decide +kernel))

theorem block07_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 64129 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 42 (by omega) (by decide +kernel))

theorem block07_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 64193 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 43 (by omega) (by decide +kernel))

theorem block07_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 64257 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 44 (by omega) (by decide +kernel))

theorem block07_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 64321 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 45 (by omega) (by decide +kernel))

theorem block07_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 64385 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 46 (by omega) (by decide +kernel))

theorem block07_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 64449 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 47 (by omega) (by decide +kernel))

theorem block07_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 64513 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 48 (by omega) (by decide +kernel))

theorem block07_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 64577 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 49 (by omega) (by decide +kernel))

theorem block07_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 64641 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 50 (by omega) (by decide +kernel))

theorem block07_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 64705 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 51 (by omega) (by decide +kernel))

theorem block07_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 64769 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 52 (by omega) (by decide +kernel))

theorem block07_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 64833 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 53 (by omega) (by decide +kernel))

theorem block07_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 64897 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 54 (by omega) (by decide +kernel))

theorem block07_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 64961 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 55 (by omega) (by decide +kernel))

theorem block07_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 65025 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 56 (by omega) (by decide +kernel))

theorem block07_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 65089 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 57 (by omega) (by decide +kernel))

theorem block07_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 65153 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 58 (by omega) (by decide +kernel))

theorem block07_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 65217 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 59 (by omega) (by decide +kernel))

theorem block07_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 65281 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 60 (by omega) (by decide +kernel))

theorem block07_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 65345 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 61 (by omega) (by decide +kernel))

theorem block07_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 65409 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 62 (by omega) (by decide +kernel))

theorem block07_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 65473 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 7 (by omega) (by omega)
      block02 block03 block06 block07 tail 63 (by omega) (by decide +kernel))

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

theorem block07_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 61441 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) (61441 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block07_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 7 block02 block03 block06 block07 tail)) 61441 64 hpages

/-- Same-table specialization for the concrete four slots. The slot facts bind
    the imported immutable blocks to entries of one shared block table; the
    window equality then preserves current, previous, delayed and boundary reads. -/
theorem block07_all_pages_checked_same_table (blocks : Nat → Block)
    (hboundary : blocks 2 = block02)
    (hdelayed : blocks 3 = block03)
    (hprev : blocks 6 = block06)
    (hcurrent : blocks 7 = block07) :
    readCheckBlock (assembledRead blocks) 61441 4096 = true := by
  have hslots : windowBlocks 7 block02 block03 block06 block07 blocks = blocks := by
    rw [← hboundary, ← hdelayed, ← hprev, ← hcurrent]
    exact windowBlocks_eq_original 7 blocks
  rw [← hslots]
  exact block07_all_pages_checked blocks

end ImbalancedChen.OriginalU2StoredNodeBlock07FullSourceOnly
