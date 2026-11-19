# Durable P1.4 recovery — strict upper quotient makes proper AP tail empty

Continue from LIVE HEAD on branch chatgpt/p1-full87-upper-room-proper-multiple-20261120-0410.
Previous verified continuation HEAD: 913928e25afa5c4db680d60598ba71bbb9243cd7.
New candidate source commit (corrected): 333b8a004c7dd355dc8b6caeadbf026b61638644.
SOURCE: docs/source-only/20261120-upper-room-proper-multiple/P4AOriginalFull87UpperRoomNoProperMultiple.lean
SOURCE GitHub blob: bafa9f08d8681fd962427a911daebe62e6c9b591, 246 lines.
The initial source commit 8f25959 had an incorrect open-namespace for originalFullQOutsideShellRoom; the correction was committed as 333b8a004c7dd355dc8b6caeadbf026b61638644. The initial commit must not be cited as the latest candidate.

Key new mathematical deduction: actualPrimitiveRosserRoom is filtered from the two-sided fullUpperQuotientRoom with a>=floor(N/(2b))+1, hence 2ab>N. For every true receiver r=N-P<=N, r cannot be a proper multiple of ab (would imply 2ab<=r). Thus its previously identified non-shell AP tail and signed proper-divisor convolution vanish on the actual upper room, *without PP or smoothness*. The actual stopped ledger becomes physical-lower_once = frozen mean + frozen full-q AP. This fixes the earlier overbroad obstruction; it does NOT apply to unrestricted q or lower-half fibres.

Next concrete action: compile/typecheck this exact source under pinned Lean v4.33.0-rc1, mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1 and native 09b97db5764ade1246bfb77206baa1b124760958, once the fixed dependencies are actually available. Before any new proof, inspect the local source and repair real elaboration errors, especially the Nat.div strict-endpoint lemma, the exact imported symbol origins and List.sum-of-zero reductions. Then aggregate genuine original physical rho_N(q), identify the same smooth labelled-prime PP mean, and pay same H_N budget. Preserve original dynamic parent and ordered events, strict endpoints, lower once, c and K. Do not trigger CI or modify master.

Present evidence: 206,354 finite original upper interval arithmetic checks, 0 discrepancies; lean/lake/elan command checks all 127, 4 GiB limit. Status SOURCE_ONLY / UNEVALUATED / UNCOMPILED, no kernel replay, no axiom audit, no independent review. Full provenance in REPORT, external boundaries in INPUT_BOUNDARY, machine fields in REGISTRY.
