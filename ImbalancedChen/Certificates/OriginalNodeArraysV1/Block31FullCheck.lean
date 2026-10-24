-- SOURCEONLY generated candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission asserted by ROOT.
-- Page starts: 159745+64*p; rows 159745..163840.
-- Raw Llo: block-31.Llo.dec SHA256 148f00e4321517764e7e50aa74af137792b13fa9e1669904ab12285817d15080
-- Raw Lhi: block-31.Lhi.dec SHA256 4f13ce0ac135bfbd60015d2aa9a16fd499379d76e3f7dbda299e5a0f0da9dafd
-- Raw Hlo: block-31.Hlo.dec SHA256 934bb53b8034fc6be2a0df9a11014fdef836516d892d4fe4a6a58f276840c807
-- Raw Hhi: block-31.Hhi.dec SHA256 51a35675dbbb2b3cb2cb10f3fc0ca3c6b4eceae8d1f1ba4ab8690110f58a467c
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block26Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block27Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block30Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block31Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

-- Serialize the independent kernel checks to stay within the compiler memory budget.
set_option Elab.async false

namespace ImbalancedChen.OriginalU2StoredNodeBlock31FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block31_page00_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 159745 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (159745) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*0) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 0 (by omega) hclosed')

theorem block31_page01_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 159809 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (159809) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*1) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 1 (by omega) hclosed')

theorem block31_page02_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 159873 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (159873) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*2) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 2 (by omega) hclosed')

theorem block31_page03_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 159937 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (159937) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*3) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 3 (by omega) hclosed')

theorem block31_page04_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 160001 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (160001) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*4) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 4 (by omega) hclosed')

theorem block31_page05_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 160065 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (160065) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*5) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 5 (by omega) hclosed')

theorem block31_page06_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 160129 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (160129) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*6) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 6 (by omega) hclosed')

theorem block31_page07_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 160193 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (160193) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*7) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 7 (by omega) hclosed')

theorem block31_page08_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 160257 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (160257) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*8) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 8 (by omega) hclosed')

theorem block31_page09_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 160321 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (160321) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*9) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 9 (by omega) hclosed')

theorem block31_page10_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 160385 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (160385) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*10) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 10 (by omega) hclosed')

theorem block31_page11_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 160449 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (160449) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*11) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 11 (by omega) hclosed')

theorem block31_page12_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 160513 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (160513) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*12) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 12 (by omega) hclosed')

theorem block31_page13_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 160577 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (160577) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*13) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 13 (by omega) hclosed')

theorem block31_page14_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 160641 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (160641) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*14) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 14 (by omega) hclosed')

theorem block31_page15_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 160705 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (160705) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*15) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 15 (by omega) hclosed')

theorem block31_page16_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 160769 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (160769) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*16) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 16 (by omega) hclosed')

theorem block31_page17_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 160833 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (160833) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*17) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 17 (by omega) hclosed')

theorem block31_page18_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 160897 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (160897) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*18) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 18 (by omega) hclosed')

theorem block31_page19_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 160961 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (160961) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*19) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 19 (by omega) hclosed')

theorem block31_page20_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 161025 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (161025) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*20) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 20 (by omega) hclosed')

theorem block31_page21_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 161089 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (161089) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*21) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 21 (by omega) hclosed')

theorem block31_page22_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 161153 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (161153) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*22) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 22 (by omega) hclosed')

theorem block31_page23_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 161217 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (161217) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*23) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 23 (by omega) hclosed')

theorem block31_page24_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 161281 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (161281) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*24) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 24 (by omega) hclosed')

theorem block31_page25_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 161345 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (161345) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*25) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 25 (by omega) hclosed')

theorem block31_page26_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 161409 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (161409) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*26) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 26 (by omega) hclosed')

theorem block31_page27_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 161473 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (161473) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*27) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 27 (by omega) hclosed')

theorem block31_page28_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 161537 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (161537) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*28) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 28 (by omega) hclosed')

theorem block31_page29_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 161601 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (161601) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*29) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 29 (by omega) hclosed')

theorem block31_page30_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 161665 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (161665) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*30) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 30 (by omega) hclosed')

theorem block31_page31_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 161729 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (161729) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*31) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 31 (by omega) hclosed')

theorem block31_page32_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 161793 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (161793) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*32) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 32 (by omega) hclosed')

theorem block31_page33_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 161857 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (161857) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*33) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 33 (by omega) hclosed')

theorem block31_page34_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 161921 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (161921) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*34) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 34 (by omega) hclosed')

theorem block31_page35_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 161985 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (161985) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*35) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 35 (by omega) hclosed')

theorem block31_page36_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 162049 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (162049) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*36) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 36 (by omega) hclosed')

theorem block31_page37_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 162113 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (162113) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*37) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 37 (by omega) hclosed')

theorem block31_page38_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 162177 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (162177) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*38) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 38 (by omega) hclosed')

theorem block31_page39_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 162241 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (162241) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*39) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 39 (by omega) hclosed')

theorem block31_page40_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 162305 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (162305) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*40) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 40 (by omega) hclosed')

theorem block31_page41_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 162369 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (162369) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*41) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 41 (by omega) hclosed')

theorem block31_page42_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 162433 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (162433) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*42) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 42 (by omega) hclosed')

theorem block31_page43_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 162497 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (162497) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*43) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 43 (by omega) hclosed')

theorem block31_page44_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 162561 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (162561) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*44) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 44 (by omega) hclosed')

theorem block31_page45_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 162625 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (162625) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*45) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 45 (by omega) hclosed')

theorem block31_page46_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 162689 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (162689) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*46) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 46 (by omega) hclosed')

theorem block31_page47_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 162753 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (162753) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*47) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 47 (by omega) hclosed')

theorem block31_page48_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 162817 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (162817) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*48) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 48 (by omega) hclosed')

theorem block31_page49_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 162881 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (162881) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*49) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 49 (by omega) hclosed')

theorem block31_page50_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 162945 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (162945) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*50) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 50 (by omega) hclosed')

theorem block31_page51_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 163009 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (163009) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*51) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 51 (by omega) hclosed')

theorem block31_page52_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 163073 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (163073) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*52) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 52 (by omega) hclosed')

theorem block31_page53_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 163137 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (163137) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*53) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 53 (by omega) hclosed')

theorem block31_page54_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 163201 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (163201) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*54) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 54 (by omega) hclosed')

theorem block31_page55_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 163265 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (163265) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*55) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 55 (by omega) hclosed')

theorem block31_page56_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 163329 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (163329) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*56) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 56 (by omega) hclosed')

theorem block31_page57_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 163393 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (163393) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*57) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 57 (by omega) hclosed')

theorem block31_page58_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 163457 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (163457) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*58) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 58 (by omega) hclosed')

theorem block31_page59_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 163521 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (163521) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*59) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 59 (by omega) hclosed')

theorem block31_page60_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 163585 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (163585) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*60) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 60 (by omega) hclosed')

theorem block31_page61_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 163649 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (163649) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*61) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 61 (by omega) hclosed')

theorem block31_page62_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 163713 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (163713) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*62) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 62 (by omega) hclosed')

theorem block31_page63_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 163777 64 = true := by
  have hclosed : readCheckBlock (assembledRead (referenceBlocks 31 block26 block27 block30 block31)) (163777) 64 = true := by
    decide +kernel
  have hclosed' : readCheckBlock (assembledRead (referenceBlocks 31 (blocks (31-5)) (blocks (31-4)) (blocks (31-1)) (blocks 31))) (32769+4096*31+64*63) 64 = true := by
    simpa [h26, h27, h30, h31] using hclosed
  simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
    (assembled_page_transfer_blocks04to39 blocks 31 (by omega) (by omega) 63 (by omega) hclosed')

theorem block31_all_pages_checked (blocks : Nat → Block)
    (h26 : blocks 26 = block26) (h27 : blocks 27 = block27)
    (h30 : blocks 30 = block30) (h31 : blocks 31 = block31) :
    readCheckBlock (assembledRead blocks) 159745 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead blocks) (159745 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · exact block31_page00_checked blocks h26 h27 h30 h31
    · exact block31_page01_checked blocks h26 h27 h30 h31
    · exact block31_page02_checked blocks h26 h27 h30 h31
    · exact block31_page03_checked blocks h26 h27 h30 h31
    · exact block31_page04_checked blocks h26 h27 h30 h31
    · exact block31_page05_checked blocks h26 h27 h30 h31
    · exact block31_page06_checked blocks h26 h27 h30 h31
    · exact block31_page07_checked blocks h26 h27 h30 h31
    · exact block31_page08_checked blocks h26 h27 h30 h31
    · exact block31_page09_checked blocks h26 h27 h30 h31
    · exact block31_page10_checked blocks h26 h27 h30 h31
    · exact block31_page11_checked blocks h26 h27 h30 h31
    · exact block31_page12_checked blocks h26 h27 h30 h31
    · exact block31_page13_checked blocks h26 h27 h30 h31
    · exact block31_page14_checked blocks h26 h27 h30 h31
    · exact block31_page15_checked blocks h26 h27 h30 h31
    · exact block31_page16_checked blocks h26 h27 h30 h31
    · exact block31_page17_checked blocks h26 h27 h30 h31
    · exact block31_page18_checked blocks h26 h27 h30 h31
    · exact block31_page19_checked blocks h26 h27 h30 h31
    · exact block31_page20_checked blocks h26 h27 h30 h31
    · exact block31_page21_checked blocks h26 h27 h30 h31
    · exact block31_page22_checked blocks h26 h27 h30 h31
    · exact block31_page23_checked blocks h26 h27 h30 h31
    · exact block31_page24_checked blocks h26 h27 h30 h31
    · exact block31_page25_checked blocks h26 h27 h30 h31
    · exact block31_page26_checked blocks h26 h27 h30 h31
    · exact block31_page27_checked blocks h26 h27 h30 h31
    · exact block31_page28_checked blocks h26 h27 h30 h31
    · exact block31_page29_checked blocks h26 h27 h30 h31
    · exact block31_page30_checked blocks h26 h27 h30 h31
    · exact block31_page31_checked blocks h26 h27 h30 h31
    · exact block31_page32_checked blocks h26 h27 h30 h31
    · exact block31_page33_checked blocks h26 h27 h30 h31
    · exact block31_page34_checked blocks h26 h27 h30 h31
    · exact block31_page35_checked blocks h26 h27 h30 h31
    · exact block31_page36_checked blocks h26 h27 h30 h31
    · exact block31_page37_checked blocks h26 h27 h30 h31
    · exact block31_page38_checked blocks h26 h27 h30 h31
    · exact block31_page39_checked blocks h26 h27 h30 h31
    · exact block31_page40_checked blocks h26 h27 h30 h31
    · exact block31_page41_checked blocks h26 h27 h30 h31
    · exact block31_page42_checked blocks h26 h27 h30 h31
    · exact block31_page43_checked blocks h26 h27 h30 h31
    · exact block31_page44_checked blocks h26 h27 h30 h31
    · exact block31_page45_checked blocks h26 h27 h30 h31
    · exact block31_page46_checked blocks h26 h27 h30 h31
    · exact block31_page47_checked blocks h26 h27 h30 h31
    · exact block31_page48_checked blocks h26 h27 h30 h31
    · exact block31_page49_checked blocks h26 h27 h30 h31
    · exact block31_page50_checked blocks h26 h27 h30 h31
    · exact block31_page51_checked blocks h26 h27 h30 h31
    · exact block31_page52_checked blocks h26 h27 h30 h31
    · exact block31_page53_checked blocks h26 h27 h30 h31
    · exact block31_page54_checked blocks h26 h27 h30 h31
    · exact block31_page55_checked blocks h26 h27 h30 h31
    · exact block31_page56_checked blocks h26 h27 h30 h31
    · exact block31_page57_checked blocks h26 h27 h30 h31
    · exact block31_page58_checked blocks h26 h27 h30 h31
    · exact block31_page59_checked blocks h26 h27 h30 h31
    · exact block31_page60_checked blocks h26 h27 h30 h31
    · exact block31_page61_checked blocks h26 h27 h30 h31
    · exact block31_page62_checked blocks h26 h27 h30 h31
    · exact block31_page63_checked blocks h26 h27 h30 h31
  exact readCheckBlock_of_64_pages
    (assembledRead blocks) 159745 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock31FullSourceOnly
