-- SOURCEONLY generated candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission.
-- Page starts: 77825 + 64*p; full block ends at 81920.
-- Raw byte correspondence and source dependency hashes are recorded in the accompanying CP.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block06Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block07Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block10Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block11Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock11FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block11_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 77825 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 0 (by omega) (by decide +kernel))

theorem block11_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 77889 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 1 (by omega) (by decide +kernel))

theorem block11_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 77953 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 2 (by omega) (by decide +kernel))

theorem block11_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 78017 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 3 (by omega) (by decide +kernel))

theorem block11_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 78081 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 4 (by omega) (by decide +kernel))

theorem block11_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 78145 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 5 (by omega) (by decide +kernel))

theorem block11_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 78209 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 6 (by omega) (by decide +kernel))

theorem block11_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 78273 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 7 (by omega) (by decide +kernel))

theorem block11_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 78337 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 8 (by omega) (by decide +kernel))

theorem block11_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 78401 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 9 (by omega) (by decide +kernel))

theorem block11_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 78465 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 10 (by omega) (by decide +kernel))

theorem block11_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 78529 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 11 (by omega) (by decide +kernel))

theorem block11_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 78593 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 12 (by omega) (by decide +kernel))

theorem block11_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 78657 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 13 (by omega) (by decide +kernel))

theorem block11_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 78721 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 14 (by omega) (by decide +kernel))

theorem block11_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 78785 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 15 (by omega) (by decide +kernel))

theorem block11_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 78849 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 16 (by omega) (by decide +kernel))

theorem block11_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 78913 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 17 (by omega) (by decide +kernel))

theorem block11_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 78977 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 18 (by omega) (by decide +kernel))

theorem block11_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 79041 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 19 (by omega) (by decide +kernel))

theorem block11_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 79105 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 20 (by omega) (by decide +kernel))

theorem block11_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 79169 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 21 (by omega) (by decide +kernel))

theorem block11_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 79233 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 22 (by omega) (by decide +kernel))

theorem block11_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 79297 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 23 (by omega) (by decide +kernel))

theorem block11_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 79361 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 24 (by omega) (by decide +kernel))

theorem block11_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 79425 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 25 (by omega) (by decide +kernel))

theorem block11_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 79489 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 26 (by omega) (by decide +kernel))

theorem block11_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 79553 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 27 (by omega) (by decide +kernel))

theorem block11_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 79617 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 28 (by omega) (by decide +kernel))

theorem block11_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 79681 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 29 (by omega) (by decide +kernel))

theorem block11_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 79745 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 30 (by omega) (by decide +kernel))

theorem block11_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 79809 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 31 (by omega) (by decide +kernel))

theorem block11_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 79873 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 32 (by omega) (by decide +kernel))

theorem block11_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 79937 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 33 (by omega) (by decide +kernel))

theorem block11_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 80001 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 34 (by omega) (by decide +kernel))

theorem block11_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 80065 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 35 (by omega) (by decide +kernel))

theorem block11_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 80129 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 36 (by omega) (by decide +kernel))

theorem block11_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 80193 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 37 (by omega) (by decide +kernel))

theorem block11_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 80257 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 38 (by omega) (by decide +kernel))

theorem block11_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 80321 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 39 (by omega) (by decide +kernel))

theorem block11_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 80385 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 40 (by omega) (by decide +kernel))

theorem block11_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 80449 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 41 (by omega) (by decide +kernel))

theorem block11_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 80513 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 42 (by omega) (by decide +kernel))

theorem block11_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 80577 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 43 (by omega) (by decide +kernel))

theorem block11_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 80641 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 44 (by omega) (by decide +kernel))

theorem block11_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 80705 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 45 (by omega) (by decide +kernel))

theorem block11_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 80769 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 46 (by omega) (by decide +kernel))

theorem block11_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 80833 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 47 (by omega) (by decide +kernel))

theorem block11_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 80897 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 48 (by omega) (by decide +kernel))

theorem block11_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 80961 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 49 (by omega) (by decide +kernel))

theorem block11_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 81025 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 50 (by omega) (by decide +kernel))

theorem block11_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 81089 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 51 (by omega) (by decide +kernel))

theorem block11_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 81153 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 52 (by omega) (by decide +kernel))

theorem block11_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 81217 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 53 (by omega) (by decide +kernel))

theorem block11_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 81281 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 54 (by omega) (by decide +kernel))

theorem block11_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 81345 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 55 (by omega) (by decide +kernel))

theorem block11_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 81409 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 56 (by omega) (by decide +kernel))

theorem block11_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 81473 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 57 (by omega) (by decide +kernel))

theorem block11_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 81537 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 58 (by omega) (by decide +kernel))

theorem block11_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 81601 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 59 (by omega) (by decide +kernel))

theorem block11_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 81665 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 60 (by omega) (by decide +kernel))

theorem block11_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 81729 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 61 (by omega) (by decide +kernel))

theorem block11_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 81793 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 62 (by omega) (by decide +kernel))

theorem block11_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 81857 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 11 (by omega) (by omega) block06 block07 block10 block11 tail 63 (by omega) (by decide +kernel))

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

theorem block11_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 77825 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) (77825 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block11_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 11 block06 block07 block10 block11 tail)) 77825 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock11FullSourceOnly
