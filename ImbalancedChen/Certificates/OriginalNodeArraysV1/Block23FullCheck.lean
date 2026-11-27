-- SOURCEONLY generated candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns dependency installation, strict checking, stock replay, and any admission.
-- Block 23 rows 126977..131072; page starts 32769 + 4096*23 + 64*p (p=0..63).
-- Block18/19/22/23Data modules are required future suppliers; exact exports are in CP.json.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block18Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block19Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block22Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block23Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock23FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block23_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 126977 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 0 (by omega) (by decide +kernel))

theorem block23_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 127041 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 1 (by omega) (by decide +kernel))

theorem block23_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 127105 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 2 (by omega) (by decide +kernel))

theorem block23_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 127169 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 3 (by omega) (by decide +kernel))

theorem block23_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 127233 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 4 (by omega) (by decide +kernel))

theorem block23_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 127297 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 5 (by omega) (by decide +kernel))

theorem block23_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 127361 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 6 (by omega) (by decide +kernel))

theorem block23_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 127425 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 7 (by omega) (by decide +kernel))

theorem block23_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 127489 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 8 (by omega) (by decide +kernel))

theorem block23_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 127553 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 9 (by omega) (by decide +kernel))

theorem block23_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 127617 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 10 (by omega) (by decide +kernel))

theorem block23_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 127681 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 11 (by omega) (by decide +kernel))

theorem block23_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 127745 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 12 (by omega) (by decide +kernel))

theorem block23_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 127809 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 13 (by omega) (by decide +kernel))

theorem block23_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 127873 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 14 (by omega) (by decide +kernel))

theorem block23_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 127937 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 15 (by omega) (by decide +kernel))

theorem block23_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 128001 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 16 (by omega) (by decide +kernel))

theorem block23_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 128065 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 17 (by omega) (by decide +kernel))

theorem block23_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 128129 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 18 (by omega) (by decide +kernel))

theorem block23_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 128193 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 19 (by omega) (by decide +kernel))

theorem block23_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 128257 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 20 (by omega) (by decide +kernel))

theorem block23_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 128321 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 21 (by omega) (by decide +kernel))

theorem block23_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 128385 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 22 (by omega) (by decide +kernel))

theorem block23_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 128449 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 23 (by omega) (by decide +kernel))

theorem block23_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 128513 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 24 (by omega) (by decide +kernel))

theorem block23_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 128577 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 25 (by omega) (by decide +kernel))

theorem block23_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 128641 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 26 (by omega) (by decide +kernel))

theorem block23_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 128705 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 27 (by omega) (by decide +kernel))

theorem block23_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 128769 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 28 (by omega) (by decide +kernel))

theorem block23_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 128833 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 29 (by omega) (by decide +kernel))

theorem block23_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 128897 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 30 (by omega) (by decide +kernel))

theorem block23_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 128961 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 31 (by omega) (by decide +kernel))

theorem block23_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 129025 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 32 (by omega) (by decide +kernel))

theorem block23_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 129089 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 33 (by omega) (by decide +kernel))

theorem block23_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 129153 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 34 (by omega) (by decide +kernel))

theorem block23_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 129217 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 35 (by omega) (by decide +kernel))

theorem block23_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 129281 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 36 (by omega) (by decide +kernel))

theorem block23_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 129345 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 37 (by omega) (by decide +kernel))

theorem block23_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 129409 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 38 (by omega) (by decide +kernel))

theorem block23_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 129473 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 39 (by omega) (by decide +kernel))

theorem block23_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 129537 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 40 (by omega) (by decide +kernel))

theorem block23_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 129601 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 41 (by omega) (by decide +kernel))

theorem block23_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 129665 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 42 (by omega) (by decide +kernel))

theorem block23_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 129729 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 43 (by omega) (by decide +kernel))

theorem block23_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 129793 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 44 (by omega) (by decide +kernel))

theorem block23_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 129857 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 45 (by omega) (by decide +kernel))

theorem block23_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 129921 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 46 (by omega) (by decide +kernel))

theorem block23_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 129985 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 47 (by omega) (by decide +kernel))

theorem block23_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 130049 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 48 (by omega) (by decide +kernel))

theorem block23_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 130113 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 49 (by omega) (by decide +kernel))

theorem block23_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 130177 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 50 (by omega) (by decide +kernel))

theorem block23_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 130241 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 51 (by omega) (by decide +kernel))

theorem block23_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 130305 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 52 (by omega) (by decide +kernel))

theorem block23_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 130369 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 53 (by omega) (by decide +kernel))

theorem block23_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 130433 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 54 (by omega) (by decide +kernel))

theorem block23_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 130497 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 55 (by omega) (by decide +kernel))

theorem block23_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 130561 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 56 (by omega) (by decide +kernel))

theorem block23_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 130625 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 57 (by omega) (by decide +kernel))

theorem block23_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 130689 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 58 (by omega) (by decide +kernel))

theorem block23_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 130753 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 59 (by omega) (by decide +kernel))

theorem block23_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 130817 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 60 (by omega) (by decide +kernel))

theorem block23_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 130881 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 61 (by omega) (by decide +kernel))

theorem block23_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 130945 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 62 (by omega) (by decide +kernel))

theorem block23_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 131009 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 23 (by omega) (by omega) block18 block19 block22 block23 tail 63 (by omega) (by decide +kernel))

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

theorem block23_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 126977 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) (126977 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block23_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 23 block18 block19 block22 block23 tail)) 126977 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock23FullSourceOnly
