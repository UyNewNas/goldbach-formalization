# T03 early-three installation supplement

Independent static review of the two notation changes for the published 12-source packet at `2798513f25c982c151b878ce36c08d28af12bc6c`. The selected install operation passes this source review. Remote parser and kernel acceptance remain pending.

The pinned Lean core blob `a45b3110afdf9a53be21f7051742b2f364d8dd49` declares the infix `<+` with `scoped` inside namespace `List` at line 1110 of `src/Init/Data/List/Basic.lean`. This is the notation for `List.Sublist`. I matched both unified-diff headers and all context against the frozen author files, applied each hunk to bytes in memory, and checked size, SHA-256 and Git blob of each result. The single insertion of the five ASCII bytes ` List` on the file-wide scope line enables exactly the three identified uses in the reviewed source.

| Install module | Scope line | Uses | Published SHA-256 | Selected stage SHA-256 |
|---|---:|---|---|---|
| P4AOriginalEarlyTupleCarriers | 6 | 43 | `0a84e536f8a2308eaa1db6b98631e97d8cdbbc90248eb118e0f5eaf7222d17fc` | `c46fca0070b9d762ea60031c667914df59d34dc07b54cedb1aa02e2334637be7` |
| P4AOriginalEarlyTupleComparison | 5 | 74, 103 | `0ae717c64d9bfe7c077a698428cfc70d43de0537fa9705e409d715cadfb2c7ec` | `e43fb92eda561fbde152b720c48266f78349b39deceaf23a654286607a79578c` |

The imports, declarations, proofs and early-defect terminal retain the original bytes past the scope change. The terminal SHA-256 is `141d73f387f81246ecd2770c7a9322249a50919cc052cae770e96dd805720027`. Its mathematical scope remains the one in the prior independent review `6dfaa58ce5126d829870574e3c4adf8601509bbf0ea332029924dfa8dc4a8cc5`. The source of the staging output is the verified frozen preimage plus this exact patch. No compiled output or new mathematical result is part of this supplement.
