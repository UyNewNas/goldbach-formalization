# Cell05 all-row gap conditions

## Goal and scope

Continue P2.6 from work-branch head `5177b7b9e0617006888e7733416912440e72d41a` and the accepted Cell05 Shape checkpoint. Add one new owner, `ImbalancedChen.P2OriginalSaving19Cell05AllRowGaps`, proving for each of the 56 actual Cell05 rows that the sum of its nine original vertex gaps is positive and its stored `meanGap` is that sum divided by nine. These are conditions 3 and 5 of `RowNumericsPure.RowDataChecksFor`. Preserve bounded accessors and equalities to the original array selections, with no fallback assumptions.

The manuscript is frozen at `UyNewNas/chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a`, `paper/release-20261106/en/argument.tex` (eighth-rank saving density) and `numerical-appendix.tex` (simplex moments and Saving19). The diagnostic rational computations are authoring aids only, never proof inputs.

## Constraints

- Author code locally in the existing isolated partial checkout. Publish only explicit paths onto the current remote work branch by an expected-head lease; no wholesale push, main merge, CI run, or board completion.
- Root alone operates P2. Do not cancel unrelated queued jobs. P1/P3 mapping and original evidence-transfer boundaries remain unchanged.
- Reuse 126 accepted Shape-closure modules and two canonical pure modules. The latter are `P2OriginalSaving19RowNumericsPure` and `P2OriginalLogMomentQ96ArithmeticPure`; their overlap with Shape uses exactly the same ArchiveSchema and SourceJson objects. The new project closure is expected to have 129 modules including the new owner.
- Preserve all old source/object identities and raw receipts. No old normal, kernel, or owned command is replayed in its old context. Existing supplier evidence is reused according to its actual contract; do not invent a requirement for a separate full-owned audit of every old supplier.
- Authenticate current runtime using the retained recovery-v2 certificate and read-only validation. Do not rewrite the original runtime guard or historical command flags/counts.
- New normal and owned commands explicitly use `--trust=0 -DwarningAsError=true`; kernel uses the stock pinned `leanchecker`. Audit every target declaration by declaring module, including private/generated declarations, with full types and transitive axioms. Allow only `propext`, `Classical.choice`, and `Quot.sound`; reject axioms, unsafe/partial declarations, omitted declarations, and truncated types.
- No `sorry`, `admit`, `native_decide`, new axiom, substituted data, weakened statement, or fabricated receipt. Preserve actual failures and launch witnesses; no automatic replay of a launched command with missing receipts.
- This checkpoint adds at most 56 rows times two conditions. It adds zero complete ten-condition rows, zero original moment-floor rows, and zero ownership/integration/global-endpoint conclusions. `P2_6_complete=false`.

## Tasks and ownership

1. **Lean source.** `/root/shape_completion_runner` implements the one owner, following the reviewed all-56 design and actual typed leaves, with seven eight-row private proof blocks where useful. Root and an independent reviewer check the exact statement, original-data selections, imports, and proof boundary before deployment.
2. **Supplier preparation.** Root extracts exactly the two pure modules, their original normal/kernel receipts and logs, and their immutable provenance documents from the preserved Cell00 transfer archive. Verify original archive and per-file hashes; do not recompile old suppliers. Record the original paths and the new transport paths separately.
3. **One-owner executor.** `/root/remaining9_source_review` implements an isolated executor under `tools/p26/cell05-all-row-gaps-20261127/`, with a fresh `/workspace/p26-cell05-all-row-gaps-20261127-v1` stage. Reuse frozen read-only Shape/recovery validation without mutating old constants or evidence. Bind all new source/config/audit/helper bytes; retain raw command/result/log/receipt and durable per-mode launch witnesses. Add targeted tests for actual tamper/no-replay risks. `/root/p26_remote_audit` independently reviews.
4. **Compile and preserve.** After source and executor review, root deploys exact bytes, validates the 128 suppliers and target dedup, then runs only the three new checks at the allowed P2 resource envelope. Any source fix gets a new attempt and preserved failure evidence, with successful earlier checks reused only when their exact inputs remain unchanged.
5. **Readback and publication.** Recover the complete new evidence archive, independently validate all three chains and complete declaration inventory, and publish the accepted source plus accurate evidence/status on the existing work branch. Update the ledger with actual results, not preparation status.

## Other continuation gates

Cell01 AllRowArithmetic does not import the original-floor family, but its Row001Finite dependency itself requires the original P3 same-host verification or an already valid full portable attestation. The available historical v1 summary does not satisfy the frozen v2 portable contract. Preserve the precise BLOCKED assessment; do not move or reconstruct restricted evidence. Cell05 uses an independent available dependency chain.
