-- SOURCEONLY complete candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission.
-- Page starts: 32769 + 4096*29 + 64*p; full block ends at 155648.
-- Frozen raw inputs are byte-bound in the accompanying CP record.
-- Raw Llo: bytes=147456 sha256=d02274de1d4c6c8a5add0faa193f56cbef38078a2b2594eb7ef9b00fd5e0cd1e
-- Raw Lhi: bytes=147456 sha256=2b22483b7f121e63f1b32acc662be172828e5ec08fafadc9bd5c2e44f1d919d8
-- Raw Hlo: bytes=147456 sha256=44509da98777003fdb7329d854816bd302095b5bb2b6661be7744c2b4b4890af
-- Raw Hhi: bytes=147456 sha256=223abccf047cb64e43ba16e3eedc4e818e39526d11132f35ed49809f4a55f3ce
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block24Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block25Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block28Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block29Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

-- Serialize the independent kernel checks to stay within the compiler memory budget.
set_option Elab.async false

namespace ImbalancedChen.OriginalU2StoredNodeBlock29FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block29_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 151553 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 0 (by omega) (by decide +kernel))

theorem block29_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 151617 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 1 (by omega) (by decide +kernel))

theorem block29_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 151681 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 2 (by omega) (by decide +kernel))

theorem block29_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 151745 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 3 (by omega) (by decide +kernel))

theorem block29_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 151809 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 4 (by omega) (by decide +kernel))

theorem block29_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 151873 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 5 (by omega) (by decide +kernel))

theorem block29_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 151937 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 6 (by omega) (by decide +kernel))

theorem block29_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 152001 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 7 (by omega) (by decide +kernel))

theorem block29_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 152065 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 8 (by omega) (by decide +kernel))

theorem block29_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 152129 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 9 (by omega) (by decide +kernel))

theorem block29_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 152193 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 10 (by omega) (by decide +kernel))

theorem block29_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 152257 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 11 (by omega) (by decide +kernel))

theorem block29_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 152321 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 12 (by omega) (by decide +kernel))

theorem block29_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 152385 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 13 (by omega) (by decide +kernel))

theorem block29_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 152449 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 14 (by omega) (by decide +kernel))

theorem block29_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 152513 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 15 (by omega) (by decide +kernel))

theorem block29_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 152577 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 16 (by omega) (by decide +kernel))

theorem block29_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 152641 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 17 (by omega) (by decide +kernel))

theorem block29_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 152705 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 18 (by omega) (by decide +kernel))

theorem block29_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 152769 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 19 (by omega) (by decide +kernel))

theorem block29_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 152833 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 20 (by omega) (by decide +kernel))

theorem block29_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 152897 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 21 (by omega) (by decide +kernel))

theorem block29_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 152961 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 22 (by omega) (by decide +kernel))

theorem block29_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 153025 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 23 (by omega) (by decide +kernel))

theorem block29_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 153089 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 24 (by omega) (by decide +kernel))

theorem block29_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 153153 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 25 (by omega) (by decide +kernel))

theorem block29_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 153217 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 26 (by omega) (by decide +kernel))

theorem block29_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 153281 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 27 (by omega) (by decide +kernel))

theorem block29_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 153345 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 28 (by omega) (by decide +kernel))

theorem block29_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 153409 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 29 (by omega) (by decide +kernel))

theorem block29_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 153473 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 30 (by omega) (by decide +kernel))

theorem block29_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 153537 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 31 (by omega) (by decide +kernel))

theorem block29_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 153601 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 32 (by omega) (by decide +kernel))

theorem block29_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 153665 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 33 (by omega) (by decide +kernel))

theorem block29_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 153729 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 34 (by omega) (by decide +kernel))

theorem block29_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 153793 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 35 (by omega) (by decide +kernel))

theorem block29_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 153857 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 36 (by omega) (by decide +kernel))

theorem block29_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 153921 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 37 (by omega) (by decide +kernel))

theorem block29_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 153985 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 38 (by omega) (by decide +kernel))

theorem block29_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 154049 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 39 (by omega) (by decide +kernel))

theorem block29_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 154113 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 40 (by omega) (by decide +kernel))

theorem block29_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 154177 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 41 (by omega) (by decide +kernel))

theorem block29_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 154241 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 42 (by omega) (by decide +kernel))

theorem block29_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 154305 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 43 (by omega) (by decide +kernel))

theorem block29_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 154369 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 44 (by omega) (by decide +kernel))

theorem block29_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 154433 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 45 (by omega) (by decide +kernel))

theorem block29_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 154497 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 46 (by omega) (by decide +kernel))

theorem block29_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 154561 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 47 (by omega) (by decide +kernel))

theorem block29_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 154625 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 48 (by omega) (by decide +kernel))

theorem block29_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 154689 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 49 (by omega) (by decide +kernel))

theorem block29_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 154753 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 50 (by omega) (by decide +kernel))

theorem block29_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 154817 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 51 (by omega) (by decide +kernel))

theorem block29_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 154881 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 52 (by omega) (by decide +kernel))

theorem block29_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 154945 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 53 (by omega) (by decide +kernel))

theorem block29_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 155009 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 54 (by omega) (by decide +kernel))

theorem block29_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 155073 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 55 (by omega) (by decide +kernel))

theorem block29_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 155137 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 56 (by omega) (by decide +kernel))

theorem block29_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 155201 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 57 (by omega) (by decide +kernel))

theorem block29_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 155265 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 58 (by omega) (by decide +kernel))

theorem block29_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 155329 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 59 (by omega) (by decide +kernel))

theorem block29_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 155393 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 60 (by omega) (by decide +kernel))

theorem block29_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 155457 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 61 (by omega) (by decide +kernel))

theorem block29_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 155521 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 62 (by omega) (by decide +kernel))

theorem block29_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 155585 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 29 (by omega) (by omega) block24 block25 block28 block29 tail 63 (by omega) (by decide +kernel))

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

theorem block29_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 151553 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) (151553 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block29_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 29 block24 block25 block28 block29 tail)) 151553 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock29FullSourceOnly
