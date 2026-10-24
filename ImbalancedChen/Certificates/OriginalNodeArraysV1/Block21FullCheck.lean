-- SOURCEONLY generated candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission.
-- Raw Block21 starts at 118785, ends at 122880; page p starts at 118785+64*p.
-- DataCore.lean SHA256 ec88f692be60266026428c7a00e5a45a0b0e99da5937181c42be2505e1a2c92d
-- CheckerCore.lean SHA256 2eddf3387a91fb0d4195433a20189d5a8d98709e45cd5be4f5880b7b7ef47a81
-- Block00Page00Check.lean SHA256 b9c307a4b121b595b1e6f19c0cc88120a61480bf758f312973c07aedd7bda250
-- DelayedPageTransfer.lean SHA256 2ef2d7dc49f65b2c051c61f9f46534128b35270e5e708fd44f8268e670f14bc0
-- Block00FullCheck.lean SHA256 31b37cf2d75d1c836cae9d497a735a3947c542875ab4f5559c248de71d71e663
-- Additional data module contract: Block16Data, Block17Data, Block20Data and Block21Data
-- each import DataCore, open the data namespace, and export def blockNN : NodeTree 12.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block16Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block17Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block20Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block21Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

-- Serialize the independent kernel checks to stay within the compiler memory budget.
set_option Elab.async false

namespace ImbalancedChen.OriginalU2StoredNodeBlock21FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block21_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 118785 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 0 (by omega) (by decide +kernel))
theorem block21_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 118849 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 1 (by omega) (by decide +kernel))
theorem block21_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 118913 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 2 (by omega) (by decide +kernel))
theorem block21_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 118977 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 3 (by omega) (by decide +kernel))
theorem block21_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 119041 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 4 (by omega) (by decide +kernel))
theorem block21_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 119105 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 5 (by omega) (by decide +kernel))
theorem block21_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 119169 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 6 (by omega) (by decide +kernel))
theorem block21_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 119233 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 7 (by omega) (by decide +kernel))
theorem block21_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 119297 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 8 (by omega) (by decide +kernel))
theorem block21_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 119361 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 9 (by omega) (by decide +kernel))
theorem block21_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 119425 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 10 (by omega) (by decide +kernel))
theorem block21_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 119489 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 11 (by omega) (by decide +kernel))
theorem block21_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 119553 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 12 (by omega) (by decide +kernel))
theorem block21_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 119617 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 13 (by omega) (by decide +kernel))
theorem block21_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 119681 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 14 (by omega) (by decide +kernel))
theorem block21_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 119745 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 15 (by omega) (by decide +kernel))
theorem block21_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 119809 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 16 (by omega) (by decide +kernel))
theorem block21_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 119873 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 17 (by omega) (by decide +kernel))
theorem block21_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 119937 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 18 (by omega) (by decide +kernel))
theorem block21_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 120001 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 19 (by omega) (by decide +kernel))
theorem block21_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 120065 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 20 (by omega) (by decide +kernel))
theorem block21_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 120129 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 21 (by omega) (by decide +kernel))
theorem block21_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 120193 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 22 (by omega) (by decide +kernel))
theorem block21_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 120257 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 23 (by omega) (by decide +kernel))
theorem block21_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 120321 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 24 (by omega) (by decide +kernel))
theorem block21_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 120385 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 25 (by omega) (by decide +kernel))
theorem block21_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 120449 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 26 (by omega) (by decide +kernel))
theorem block21_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 120513 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 27 (by omega) (by decide +kernel))
theorem block21_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 120577 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 28 (by omega) (by decide +kernel))
theorem block21_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 120641 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 29 (by omega) (by decide +kernel))
theorem block21_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 120705 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 30 (by omega) (by decide +kernel))
theorem block21_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 120769 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 31 (by omega) (by decide +kernel))
theorem block21_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 120833 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 32 (by omega) (by decide +kernel))
theorem block21_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 120897 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 33 (by omega) (by decide +kernel))
theorem block21_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 120961 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 34 (by omega) (by decide +kernel))
theorem block21_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 121025 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 35 (by omega) (by decide +kernel))
theorem block21_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 121089 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 36 (by omega) (by decide +kernel))
theorem block21_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 121153 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 37 (by omega) (by decide +kernel))
theorem block21_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 121217 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 38 (by omega) (by decide +kernel))
theorem block21_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 121281 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 39 (by omega) (by decide +kernel))
theorem block21_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 121345 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 40 (by omega) (by decide +kernel))
theorem block21_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 121409 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 41 (by omega) (by decide +kernel))
theorem block21_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 121473 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 42 (by omega) (by decide +kernel))
theorem block21_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 121537 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 43 (by omega) (by decide +kernel))
theorem block21_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 121601 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 44 (by omega) (by decide +kernel))
theorem block21_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 121665 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 45 (by omega) (by decide +kernel))
theorem block21_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 121729 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 46 (by omega) (by decide +kernel))
theorem block21_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 121793 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 47 (by omega) (by decide +kernel))
theorem block21_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 121857 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 48 (by omega) (by decide +kernel))
theorem block21_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 121921 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 49 (by omega) (by decide +kernel))
theorem block21_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 121985 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 50 (by omega) (by decide +kernel))
theorem block21_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 122049 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 51 (by omega) (by decide +kernel))
theorem block21_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 122113 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 52 (by omega) (by decide +kernel))
theorem block21_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 122177 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 53 (by omega) (by decide +kernel))
theorem block21_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 122241 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 54 (by omega) (by decide +kernel))
theorem block21_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 122305 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 55 (by omega) (by decide +kernel))
theorem block21_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 122369 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 56 (by omega) (by decide +kernel))
theorem block21_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 122433 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 57 (by omega) (by decide +kernel))
theorem block21_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 122497 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 58 (by omega) (by decide +kernel))
theorem block21_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 122561 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 59 (by omega) (by decide +kernel))
theorem block21_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 122625 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 60 (by omega) (by decide +kernel))
theorem block21_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 122689 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 61 (by omega) (by decide +kernel))
theorem block21_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 122753 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 62 (by omega) (by decide +kernel))
theorem block21_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 122817 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 21 (by omega) (by omega) block16 block17 block20 block21 tail 63 (by omega) (by decide +kernel))

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

theorem block21_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 118785 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) (118785 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block21_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 21 block16 block17 block20 block21 tail)) 118785 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock21FullSourceOnly
