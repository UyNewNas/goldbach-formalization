-- SOURCEONLY generated candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission.
-- Page starts: 32769 + 4096*34 + 64*p; the full block ends at 176128.
-- Block34Data.lean.txt SHA256 c189b9a9c3d66c8ba6284e02e8f3f98d43ebb582080d912f06f0526903427700
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block29Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block30Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block33Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block34Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

-- Serialize the independent kernel checks to stay within the compiler memory budget.
set_option Elab.async false

namespace ImbalancedChen.OriginalU2StoredNodeBlock34FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block34_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 172033 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 0 (by omega) (by decide +kernel))

theorem block34_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 172097 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 1 (by omega) (by decide +kernel))

theorem block34_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 172161 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 2 (by omega) (by decide +kernel))

theorem block34_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 172225 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 3 (by omega) (by decide +kernel))

theorem block34_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 172289 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 4 (by omega) (by decide +kernel))

theorem block34_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 172353 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 5 (by omega) (by decide +kernel))

theorem block34_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 172417 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 6 (by omega) (by decide +kernel))

theorem block34_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 172481 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 7 (by omega) (by decide +kernel))

theorem block34_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 172545 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 8 (by omega) (by decide +kernel))

theorem block34_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 172609 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 9 (by omega) (by decide +kernel))

theorem block34_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 172673 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 10 (by omega) (by decide +kernel))

theorem block34_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 172737 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 11 (by omega) (by decide +kernel))

theorem block34_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 172801 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 12 (by omega) (by decide +kernel))

theorem block34_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 172865 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 13 (by omega) (by decide +kernel))

theorem block34_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 172929 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 14 (by omega) (by decide +kernel))

theorem block34_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 172993 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 15 (by omega) (by decide +kernel))

theorem block34_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 173057 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 16 (by omega) (by decide +kernel))

theorem block34_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 173121 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 17 (by omega) (by decide +kernel))

theorem block34_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 173185 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 18 (by omega) (by decide +kernel))

theorem block34_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 173249 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 19 (by omega) (by decide +kernel))

theorem block34_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 173313 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 20 (by omega) (by decide +kernel))

theorem block34_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 173377 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 21 (by omega) (by decide +kernel))

theorem block34_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 173441 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 22 (by omega) (by decide +kernel))

theorem block34_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 173505 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 23 (by omega) (by decide +kernel))

theorem block34_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 173569 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 24 (by omega) (by decide +kernel))

theorem block34_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 173633 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 25 (by omega) (by decide +kernel))

theorem block34_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 173697 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 26 (by omega) (by decide +kernel))

theorem block34_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 173761 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 27 (by omega) (by decide +kernel))

theorem block34_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 173825 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 28 (by omega) (by decide +kernel))

theorem block34_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 173889 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 29 (by omega) (by decide +kernel))

theorem block34_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 173953 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 30 (by omega) (by decide +kernel))

theorem block34_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 174017 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 31 (by omega) (by decide +kernel))

theorem block34_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 174081 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 32 (by omega) (by decide +kernel))

theorem block34_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 174145 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 33 (by omega) (by decide +kernel))

theorem block34_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 174209 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 34 (by omega) (by decide +kernel))

theorem block34_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 174273 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 35 (by omega) (by decide +kernel))

theorem block34_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 174337 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 36 (by omega) (by decide +kernel))

theorem block34_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 174401 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 37 (by omega) (by decide +kernel))

theorem block34_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 174465 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 38 (by omega) (by decide +kernel))

theorem block34_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 174529 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 39 (by omega) (by decide +kernel))

theorem block34_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 174593 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 40 (by omega) (by decide +kernel))

theorem block34_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 174657 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 41 (by omega) (by decide +kernel))

theorem block34_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 174721 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 42 (by omega) (by decide +kernel))

theorem block34_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 174785 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 43 (by omega) (by decide +kernel))

theorem block34_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 174849 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 44 (by omega) (by decide +kernel))

theorem block34_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 174913 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 45 (by omega) (by decide +kernel))

theorem block34_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 174977 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 46 (by omega) (by decide +kernel))

theorem block34_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 175041 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 47 (by omega) (by decide +kernel))

theorem block34_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 175105 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 48 (by omega) (by decide +kernel))

theorem block34_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 175169 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 49 (by omega) (by decide +kernel))

theorem block34_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 175233 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 50 (by omega) (by decide +kernel))

theorem block34_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 175297 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 51 (by omega) (by decide +kernel))

theorem block34_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 175361 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 52 (by omega) (by decide +kernel))

theorem block34_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 175425 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 53 (by omega) (by decide +kernel))

theorem block34_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 175489 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 54 (by omega) (by decide +kernel))

theorem block34_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 175553 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 55 (by omega) (by decide +kernel))

theorem block34_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 175617 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 56 (by omega) (by decide +kernel))

theorem block34_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 175681 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 57 (by omega) (by decide +kernel))

theorem block34_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 175745 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 58 (by omega) (by decide +kernel))

theorem block34_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 175809 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 59 (by omega) (by decide +kernel))

theorem block34_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 175873 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 60 (by omega) (by decide +kernel))

theorem block34_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 175937 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 61 (by omega) (by decide +kernel))

theorem block34_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 176001 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 62 (by omega) (by decide +kernel))

theorem block34_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 176065 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 34 (by omega) (by omega) block29 block30 block33 block34 tail 63 (by omega) (by decide +kernel))

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

theorem block34_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 172033 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) (172033 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block34_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 34 block29 block30 block33 block34 tail)) 172033 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock34FullSourceOnly
