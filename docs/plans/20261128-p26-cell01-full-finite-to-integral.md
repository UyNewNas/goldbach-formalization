# Complete the original Cell01 chain

Accepted base: `e4205213a17d2c9690c463b8c75235b436ce6745`, with the
1,341-object context pinned by
`d20aa91e469b0ad05e1d80297965b2d7838fe35e7af59471f7c63804880702b9`.
The original 144 rows, 40 vertices, degree six, Q80/Q96 and saved maximum
remain fixed. The overall P2.6 goal remains active.

1. Finish the missing exact finite owners in isolated batches. Keep the
   historical ordinals 98–106 unchanged. Only unused `simp` arguments are
   removed from the other candidate scripts; all numerical data and theorem
   statements are unchanged. Each owner needs normal, stock-kernel and full
   owned checks and post-batch input readback.
2. `prepare_finite_join.py` restores the completed objects without normal
   recompilation. `qualify_finite_join.py` uses official trust-zero replay
   against the exact accepted base, then audits every serialized occurrence.
   Each standalone owner has 292 occurrences: 288 new row-specific entries
   and four generated arithmetic equation theorems already in the base.
   For 143 owners, expect 41,184 unique new canonical entries and 572 shared
   proof bodies. Each shared body is separately kernel checked. A passed
   kernel checkpoint is preserved before the final audit.
3. `verify_after_finite.py floors` checks all nine original 16-row floor
   blocks, their full 144-row aggregation and all row-arithmetic certificates.
4. Its `physical` phase attaches every saved floor to the actual simplex and
   completes all 123 hierarchy nodes and original 144-leaf coverage.
5. Its `packing` phase proves the original saved sum below the union integral.
6. Its `source` phase proves all 97 original gates at all 40 original vertices,
   removes proved null walls and establishes the exact source-cell-1 bound
   `282451447802500037895 / 2^96`. The audit also checks the exact, premise-free
   endpoint type. The host's 3,880 rational sign checks are advisory only.

All four phases inherit and reconstruct the precise accepted parent catalog,
pin their control code and audit, and perform complete canonical/shared
inventory checks. External readbacks use the same plan and published helper
as the accepted base. Their acceptance records are written only after the
actual checks succeed; source candidates and queued jobs carry no acceptance.

Current job IDs, frozen file hashes and completed receipts are checkpointed
in `/workspace/p26-cell01-next-20261128/CONTINUATION.json`. Do not alter active
or queued control/source inputs, reset the working tree, run `lake update`,
or repeat a passed normal/kernel step. After any failure, inspect the actual
job and receipts before choosing a narrowly scoped repair or continuation.
