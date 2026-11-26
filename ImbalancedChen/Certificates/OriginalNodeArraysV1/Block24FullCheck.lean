-- SOURCEONLY generated candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission.
-- Page starts: 131073 + 64*p; block range 131073..135168.
-- Actual same-table specialization retains predecessor block23, delayed block20, and boundary block19.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block19Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block20Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block23Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block24Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock24FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block24_page00_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 131073 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*0) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      0 (by omega) hclosed)

theorem block24_page01_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 131137 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*1) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      1 (by omega) hclosed)

theorem block24_page02_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 131201 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*2) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      2 (by omega) hclosed)

theorem block24_page03_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 131265 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*3) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      3 (by omega) hclosed)

theorem block24_page04_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 131329 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*4) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      4 (by omega) hclosed)

theorem block24_page05_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 131393 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*5) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      5 (by omega) hclosed)

theorem block24_page06_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 131457 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*6) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      6 (by omega) hclosed)

theorem block24_page07_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 131521 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*7) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      7 (by omega) hclosed)

theorem block24_page08_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 131585 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*8) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      8 (by omega) hclosed)

theorem block24_page09_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 131649 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*9) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      9 (by omega) hclosed)

theorem block24_page10_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 131713 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*10) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      10 (by omega) hclosed)

theorem block24_page11_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 131777 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*11) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      11 (by omega) hclosed)

theorem block24_page12_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 131841 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*12) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      12 (by omega) hclosed)

theorem block24_page13_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 131905 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*13) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      13 (by omega) hclosed)

theorem block24_page14_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 131969 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*14) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      14 (by omega) hclosed)

theorem block24_page15_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 132033 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*15) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      15 (by omega) hclosed)

theorem block24_page16_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 132097 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*16) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      16 (by omega) hclosed)

theorem block24_page17_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 132161 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*17) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      17 (by omega) hclosed)

theorem block24_page18_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 132225 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*18) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      18 (by omega) hclosed)

theorem block24_page19_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 132289 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*19) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      19 (by omega) hclosed)

theorem block24_page20_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 132353 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*20) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      20 (by omega) hclosed)

theorem block24_page21_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 132417 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*21) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      21 (by omega) hclosed)

theorem block24_page22_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 132481 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*22) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      22 (by omega) hclosed)

theorem block24_page23_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 132545 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*23) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      23 (by omega) hclosed)

theorem block24_page24_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 132609 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*24) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      24 (by omega) hclosed)

theorem block24_page25_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 132673 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*25) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      25 (by omega) hclosed)

theorem block24_page26_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 132737 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*26) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      26 (by omega) hclosed)

theorem block24_page27_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 132801 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*27) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      27 (by omega) hclosed)

theorem block24_page28_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 132865 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*28) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      28 (by omega) hclosed)

theorem block24_page29_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 132929 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*29) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      29 (by omega) hclosed)

theorem block24_page30_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 132993 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*30) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      30 (by omega) hclosed)

theorem block24_page31_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 133057 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*31) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      31 (by omega) hclosed)

theorem block24_page32_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 133121 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*32) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      32 (by omega) hclosed)

theorem block24_page33_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 133185 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*33) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      33 (by omega) hclosed)

theorem block24_page34_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 133249 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*34) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      34 (by omega) hclosed)

theorem block24_page35_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 133313 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*35) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      35 (by omega) hclosed)

theorem block24_page36_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 133377 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*36) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      36 (by omega) hclosed)

theorem block24_page37_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 133441 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*37) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      37 (by omega) hclosed)

theorem block24_page38_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 133505 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*38) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      38 (by omega) hclosed)

theorem block24_page39_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 133569 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*39) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      39 (by omega) hclosed)

theorem block24_page40_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 133633 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*40) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      40 (by omega) hclosed)

theorem block24_page41_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 133697 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*41) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      41 (by omega) hclosed)

theorem block24_page42_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 133761 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*42) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      42 (by omega) hclosed)

theorem block24_page43_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 133825 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*43) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      43 (by omega) hclosed)

theorem block24_page44_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 133889 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*44) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      44 (by omega) hclosed)

theorem block24_page45_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 133953 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*45) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      45 (by omega) hclosed)

theorem block24_page46_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 134017 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*46) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      46 (by omega) hclosed)

theorem block24_page47_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 134081 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*47) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      47 (by omega) hclosed)

theorem block24_page48_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 134145 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*48) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      48 (by omega) hclosed)

theorem block24_page49_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 134209 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*49) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      49 (by omega) hclosed)

theorem block24_page50_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 134273 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*50) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      50 (by omega) hclosed)

theorem block24_page51_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 134337 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*51) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      51 (by omega) hclosed)

theorem block24_page52_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 134401 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*52) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      52 (by omega) hclosed)

theorem block24_page53_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 134465 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*53) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      53 (by omega) hclosed)

theorem block24_page54_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 134529 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*54) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      54 (by omega) hclosed)

theorem block24_page55_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 134593 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*55) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      55 (by omega) hclosed)

theorem block24_page56_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 134657 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*56) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      56 (by omega) hclosed)

theorem block24_page57_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 134721 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*57) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      57 (by omega) hclosed)

theorem block24_page58_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 134785 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*58) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      58 (by omega) hclosed)

theorem block24_page59_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 134849 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*59) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      59 (by omega) hclosed)

theorem block24_page60_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 134913 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*60) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      60 (by omega) hclosed)

theorem block24_page61_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 134977 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*61) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      61 (by omega) hclosed)

theorem block24_page62_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 135041 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*62) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      62 (by omega) hclosed)

theorem block24_page63_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 135105 64 = true := by
  have h19slot : blocks (24-5) = block19 := by simpa using h19
  have h20slot : blocks (24-4) = block20 := by simpa using h20
  have h23slot : blocks (24-1) = block23 := by simpa using h23
  have hclosed : readCheckBlock
      (assembledRead (referenceBlocks 24 (blocks (24-5)) (blocks (24-4))
        (blocks (24-1)) (blocks 24))) (32769+4096*24+64*63) 64 = true := by
    rw [h19slot, h20slot, h23slot, h24]
    decide +kernel
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (assembled_page_transfer_blocks04to39 blocks 24 (by omega) (by omega)
      63 (by omega) hclosed)

theorem block24_all_pages_checked (blocks : Nat → Block)
    (h19 : blocks 19 = block19) (h20 : blocks 20 = block20)
    (h23 : blocks 23 = block23) (h24 : blocks 24 = block24) :
    readCheckBlock (assembledRead blocks) 131073 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead blocks) (131073 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page00_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page01_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page02_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page03_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page04_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page05_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page06_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page07_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page08_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page09_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page10_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page11_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page12_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page13_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page14_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page15_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page16_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page17_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page18_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page19_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page20_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page21_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page22_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page23_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page24_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page25_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page26_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page27_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page28_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page29_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page30_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page31_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page32_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page33_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page34_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page35_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page36_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page37_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page38_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page39_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page40_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page41_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page42_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page43_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page44_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page45_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page46_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page47_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page48_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page49_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page50_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page51_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page52_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page53_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page54_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page55_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page56_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page57_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page58_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page59_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page60_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page61_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page62_checked blocks h19 h20 h23 h24
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block24_page63_checked blocks h19 h20 h23 h24
  exact readCheckBlock_of_64_pages (assembledRead blocks) 131073 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock24FullSourceOnly
