-- SOURCEONLY complete Block18 candidate. UNCOMPILED / NOT PASS.
-- ROOT owns source installation, kernel compilation, and acceptance.
-- Original updates: 106497..110592. Pages: 106497+64*p, p=0..63.
-- Delayed slots are blocks 13,14; previous/current slots are blocks 17,18.
-- Raw block field Llo: block-18.Llo.dec SHA256 e40b08e15c15f164d64b6678fdab2eadee337987281523beee3290edb6362070
-- Raw block field Lhi: block-18.Lhi.dec SHA256 961466b71cd4253e720410818f2608d7b200c5a3819807478a512d9b356cfa02
-- Raw block field Hlo: block-18.Hlo.dec SHA256 566141ccdaaaab15d178d5cd3c2790a758c9d2f844976e15eb0fa9bfc24c1bd7
-- Raw block field Hhi: block-18.Hhi.dec SHA256 4361ab74582bdbfa98901a829420d45e5cb59de6c1a9328d215452ffa6a5bea2
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block13Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block14Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block17Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block18Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock18FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block18_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 106497 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 0 (by omega) (by decide +kernel))

theorem block18_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 106561 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 1 (by omega) (by decide +kernel))

theorem block18_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 106625 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 2 (by omega) (by decide +kernel))

theorem block18_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 106689 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 3 (by omega) (by decide +kernel))

theorem block18_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 106753 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 4 (by omega) (by decide +kernel))

theorem block18_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 106817 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 5 (by omega) (by decide +kernel))

theorem block18_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 106881 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 6 (by omega) (by decide +kernel))

theorem block18_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 106945 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 7 (by omega) (by decide +kernel))

theorem block18_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 107009 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 8 (by omega) (by decide +kernel))

theorem block18_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 107073 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 9 (by omega) (by decide +kernel))

theorem block18_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 107137 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 10 (by omega) (by decide +kernel))

theorem block18_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 107201 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 11 (by omega) (by decide +kernel))

theorem block18_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 107265 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 12 (by omega) (by decide +kernel))

theorem block18_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 107329 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 13 (by omega) (by decide +kernel))

theorem block18_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 107393 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 14 (by omega) (by decide +kernel))

theorem block18_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 107457 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 15 (by omega) (by decide +kernel))

theorem block18_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 107521 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 16 (by omega) (by decide +kernel))

theorem block18_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 107585 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 17 (by omega) (by decide +kernel))

theorem block18_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 107649 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 18 (by omega) (by decide +kernel))

theorem block18_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 107713 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 19 (by omega) (by decide +kernel))

theorem block18_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 107777 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 20 (by omega) (by decide +kernel))

theorem block18_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 107841 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 21 (by omega) (by decide +kernel))

theorem block18_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 107905 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 22 (by omega) (by decide +kernel))

theorem block18_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 107969 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 23 (by omega) (by decide +kernel))

theorem block18_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 108033 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 24 (by omega) (by decide +kernel))

theorem block18_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 108097 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 25 (by omega) (by decide +kernel))

theorem block18_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 108161 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 26 (by omega) (by decide +kernel))

theorem block18_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 108225 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 27 (by omega) (by decide +kernel))

theorem block18_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 108289 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 28 (by omega) (by decide +kernel))

theorem block18_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 108353 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 29 (by omega) (by decide +kernel))

theorem block18_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 108417 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 30 (by omega) (by decide +kernel))

theorem block18_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 108481 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 31 (by omega) (by decide +kernel))

theorem block18_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 108545 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 32 (by omega) (by decide +kernel))

theorem block18_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 108609 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 33 (by omega) (by decide +kernel))

theorem block18_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 108673 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 34 (by omega) (by decide +kernel))

theorem block18_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 108737 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 35 (by omega) (by decide +kernel))

theorem block18_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 108801 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 36 (by omega) (by decide +kernel))

theorem block18_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 108865 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 37 (by omega) (by decide +kernel))

theorem block18_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 108929 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 38 (by omega) (by decide +kernel))

theorem block18_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 108993 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 39 (by omega) (by decide +kernel))

theorem block18_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 109057 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 40 (by omega) (by decide +kernel))

theorem block18_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 109121 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 41 (by omega) (by decide +kernel))

theorem block18_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 109185 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 42 (by omega) (by decide +kernel))

theorem block18_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 109249 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 43 (by omega) (by decide +kernel))

theorem block18_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 109313 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 44 (by omega) (by decide +kernel))

theorem block18_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 109377 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 45 (by omega) (by decide +kernel))

theorem block18_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 109441 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 46 (by omega) (by decide +kernel))

theorem block18_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 109505 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 47 (by omega) (by decide +kernel))

theorem block18_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 109569 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 48 (by omega) (by decide +kernel))

theorem block18_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 109633 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 49 (by omega) (by decide +kernel))

theorem block18_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 109697 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 50 (by omega) (by decide +kernel))

theorem block18_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 109761 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 51 (by omega) (by decide +kernel))

theorem block18_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 109825 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 52 (by omega) (by decide +kernel))

theorem block18_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 109889 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 53 (by omega) (by decide +kernel))

theorem block18_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 109953 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 54 (by omega) (by decide +kernel))

theorem block18_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 110017 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 55 (by omega) (by decide +kernel))

theorem block18_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 110081 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 56 (by omega) (by decide +kernel))

theorem block18_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 110145 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 57 (by omega) (by decide +kernel))

theorem block18_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 110209 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 58 (by omega) (by decide +kernel))

theorem block18_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 110273 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 59 (by omega) (by decide +kernel))

theorem block18_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 110337 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 60 (by omega) (by decide +kernel))

theorem block18_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 110401 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 61 (by omega) (by decide +kernel))

theorem block18_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 110465 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 62 (by omega) (by decide +kernel))

theorem block18_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 110529 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 18 (by omega) (by omega)
      block13 block14 block17 block18 tail 63 (by omega) (by decide +kernel))

/-- Exact 64-page assembly helper copied from the actual Block00FullCheck supplier. -/
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

theorem block18_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 106497 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) (106497 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block18_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 18 block13 block14 block17 block18 tail)) 106497 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock18FullSourceOnly
