-- SOURCEONLY / UNCOMPILED / NOT PASS. Candidate full original Block35 check.
-- Rows 176129..180224; 64 consecutive 64-row page checks, assembled exactly.
-- The page proofs retain delayed reads through the actual blocks30,31,34,35.
-- Neighbour modules Block30Data, Block31Data, Block34Data are expected imports;
-- install each under its pinned canonical module name before ROOT queue compilation.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block30Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block31Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block34Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block35Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

-- Serialize the independent kernel checks to stay within the compiler memory budget.
set_option Elab.async false

namespace ImbalancedChen.OriginalU2StoredNodeBlock35FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block35_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 176129 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 0 (by omega)
      (by decide +kernel))

theorem block35_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 176193 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 1 (by omega)
      (by decide +kernel))

theorem block35_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 176257 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 2 (by omega)
      (by decide +kernel))

theorem block35_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 176321 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 3 (by omega)
      (by decide +kernel))

theorem block35_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 176385 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 4 (by omega)
      (by decide +kernel))

theorem block35_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 176449 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 5 (by omega)
      (by decide +kernel))

theorem block35_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 176513 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 6 (by omega)
      (by decide +kernel))

theorem block35_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 176577 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 7 (by omega)
      (by decide +kernel))

theorem block35_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 176641 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 8 (by omega)
      (by decide +kernel))

theorem block35_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 176705 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 9 (by omega)
      (by decide +kernel))

theorem block35_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 176769 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 10 (by omega)
      (by decide +kernel))

theorem block35_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 176833 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 11 (by omega)
      (by decide +kernel))

theorem block35_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 176897 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 12 (by omega)
      (by decide +kernel))

theorem block35_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 176961 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 13 (by omega)
      (by decide +kernel))

theorem block35_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 177025 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 14 (by omega)
      (by decide +kernel))

theorem block35_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 177089 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 15 (by omega)
      (by decide +kernel))

theorem block35_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 177153 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 16 (by omega)
      (by decide +kernel))

theorem block35_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 177217 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 17 (by omega)
      (by decide +kernel))

theorem block35_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 177281 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 18 (by omega)
      (by decide +kernel))

theorem block35_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 177345 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 19 (by omega)
      (by decide +kernel))

theorem block35_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 177409 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 20 (by omega)
      (by decide +kernel))

theorem block35_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 177473 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 21 (by omega)
      (by decide +kernel))

theorem block35_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 177537 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 22 (by omega)
      (by decide +kernel))

theorem block35_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 177601 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 23 (by omega)
      (by decide +kernel))

theorem block35_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 177665 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 24 (by omega)
      (by decide +kernel))

theorem block35_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 177729 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 25 (by omega)
      (by decide +kernel))

theorem block35_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 177793 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 26 (by omega)
      (by decide +kernel))

theorem block35_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 177857 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 27 (by omega)
      (by decide +kernel))

theorem block35_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 177921 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 28 (by omega)
      (by decide +kernel))

theorem block35_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 177985 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 29 (by omega)
      (by decide +kernel))

theorem block35_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 178049 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 30 (by omega)
      (by decide +kernel))

theorem block35_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 178113 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 31 (by omega)
      (by decide +kernel))

theorem block35_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 178177 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 32 (by omega)
      (by decide +kernel))

theorem block35_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 178241 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 33 (by omega)
      (by decide +kernel))

theorem block35_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 178305 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 34 (by omega)
      (by decide +kernel))

theorem block35_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 178369 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 35 (by omega)
      (by decide +kernel))

theorem block35_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 178433 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 36 (by omega)
      (by decide +kernel))

theorem block35_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 178497 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 37 (by omega)
      (by decide +kernel))

theorem block35_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 178561 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 38 (by omega)
      (by decide +kernel))

theorem block35_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 178625 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 39 (by omega)
      (by decide +kernel))

theorem block35_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 178689 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 40 (by omega)
      (by decide +kernel))

theorem block35_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 178753 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 41 (by omega)
      (by decide +kernel))

theorem block35_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 178817 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 42 (by omega)
      (by decide +kernel))

theorem block35_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 178881 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 43 (by omega)
      (by decide +kernel))

theorem block35_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 178945 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 44 (by omega)
      (by decide +kernel))

theorem block35_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 179009 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 45 (by omega)
      (by decide +kernel))

theorem block35_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 179073 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 46 (by omega)
      (by decide +kernel))

theorem block35_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 179137 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 47 (by omega)
      (by decide +kernel))

theorem block35_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 179201 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 48 (by omega)
      (by decide +kernel))

theorem block35_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 179265 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 49 (by omega)
      (by decide +kernel))

theorem block35_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 179329 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 50 (by omega)
      (by decide +kernel))

theorem block35_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 179393 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 51 (by omega)
      (by decide +kernel))

theorem block35_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 179457 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 52 (by omega)
      (by decide +kernel))

theorem block35_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 179521 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 53 (by omega)
      (by decide +kernel))

theorem block35_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 179585 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 54 (by omega)
      (by decide +kernel))

theorem block35_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 179649 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 55 (by omega)
      (by decide +kernel))

theorem block35_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 179713 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 56 (by omega)
      (by decide +kernel))

theorem block35_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 179777 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 57 (by omega)
      (by decide +kernel))

theorem block35_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 179841 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 58 (by omega)
      (by decide +kernel))

theorem block35_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 179905 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 59 (by omega)
      (by decide +kernel))

theorem block35_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 179969 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 60 (by omega)
      (by decide +kernel))

theorem block35_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 180033 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 61 (by omega)
      (by decide +kernel))

theorem block35_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 180097 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 62 (by omega)
      (by decide +kernel))

theorem block35_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 180161 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 35 (by omega) (by omega)
      block30 block31 block34 block35 tail 63 (by omega)
      (by decide +kernel))

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

theorem block35_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 176129 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) (176129 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block35_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 35 block30 block31 block34 block35 tail)) 176129 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock35FullSourceOnly
