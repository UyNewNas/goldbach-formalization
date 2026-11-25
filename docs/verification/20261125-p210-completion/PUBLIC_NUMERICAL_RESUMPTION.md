# P2.10: resume the original numerical certificates

> Latest acceptance: [completed P2.10 final record](./PUBLIC_P210_FINAL_ACCEPTANCE.md).
> The text below is the historical resumption checkpoint. The linked final record contains the accepted Winner9 terminal, seed-supplier connection, and completion boundary.

This change preserves the numerical Lean sources from
`8bb6eac5aae11d217fb29324e1db7685954d30ac`. It changes transport, resource
allocation, and resumability. It does not claim that P2.10 or the full
1 + 1.7482 manuscript has been completely verified.

## Existing work that must be reused

The accepted historical prefix remains pages 0000–0127, containing 2048 rows.
None of those numerical proofs is scheduled for recompilation or replay.
The exact 93-module public bootstrap from run `45589950483` is also reused;
its original source, object, recursive record, and seal hashes remain fixed.

The same run attempted all 562 remaining pages with a 6144 MiB Lean limit.
Five pages compiled successfully. All 36 block jobs failed their compilation
gate, so none of those jobs reached the audit or export gate. The recovery
inventory recorded 557 failed pages, including 374 with explicit memory
exceptions, and 36 blocked Check modules. These failures did not establish
that any numerical proposition was false.

| Page | Original rows | Reuse boundary |
|---|---|---|
| 0265 | 4240–4255 | Strict compilation; original 6144 MiB command |
| 0281 | 4496–4511 | Strict compilation; original 6144 MiB command |
| 0360 | 5760–5775 | Strict compilation; original 6144 MiB command |
| 0551 | 8816–8831 | Strict compilation; original 6144 MiB command |
| 0689 | 11024–11025 | Strict compilation; original 6144 MiB command |

The complete recovery inventory was checked against all 36 original ZIPs,
their tar inventories, original compile records, source commit, object
facets, and logs. Its SHA-256 is
`c7ad1f81be123c1cbf96212b6fb97c7b038a5685c69edfb349812f3b18241107`.
The checked-in resume plan binds all 36 inputs, including blocks whose
successful-module list is empty.

## Controlled Page0224 result

[Run 45603936379](https://github.com/UyNewNas/goldbach-formalization/actions/runs/45603936379)
compiled the unchanged Page0224 source with one worker, one Lean thread,
and an 11264 MiB limit. It passed the original strict compiler, stock
leanchecker, complete owned-declaration audit, and original exporter.
Its source and producer commit are recorded in
`PAGE0224_PUBLIC_ACCEPTANCE.json`.

The original compile took 102.804 seconds and peaked at 6,738,524 KiB RSS.
Stock replay took 98.313 seconds; the owned-declaration audit took 4.238
seconds. The export binds exactly ordinals 3584–3599, 16 rows, and 34 owned
declarations. The permitted transitive axioms remain only `propext`,
`Classical.choice`, and `Quot.sound`.

This adds one accepted page outside the old prefix: 2064 accepted rows in
total, with the continuous accepted prefix still 2048 rows. The next run
must reuse both its compilation and its accepted receipt. Its original
11264 MiB command must not be rewritten as a 6144 MiB command.

## Resumption protocol

`p210_resume_plan.json` binds the public bootstrap and 37 recovery inputs:
the 36 completed original block jobs and the accepted Page0224 diagnostic.
The workflow starts only after the source runs have completed. It refuses
unplanned preserved work for the same block.

Each of the 36 block jobs restores the unchanged 93-module dependency
closure. It then processes its pages individually. An already compiled
page is reused. A missing page is compiled with the original compiler
driver, one worker, one Lean thread, and an 11264 MiB limit. The resulting
object, facets, original record, and logs are uploaded before any audit.

The original auditor handles a missing audit. A fully accepted receipt is
validated through the original relocatable exporter and reused. If only
stock replay previously succeeded, its exact snapshot, original command,
and original log must match before the auditor can reuse that replay.
The workflow preserves partial audit progress even when the next gate fails.

The Check module is scheduled only when all of its page predecessors are
already valid. A failed page cannot cause the Check driver to silently
compile that page again. Final block export requires every original gate,
the exact page intervals, the complete owned inventory, and the original
axiom boundary. A slot's `continue-on-error` does not confer acceptance:
the final block delivery fails if any slot is incomplete. The collector
requires every matrix job to succeed.

The receiver validates the source/object/dependency bindings and original
receipts before installation. It compares each reused compilation record
with its original public registry, allowing only the live object locator
to change. It preserves commands, source/object hashes, dependency
signatures, and receipt bytes. The bootstrap's original run and commit are
separate from the new collection producer; the old seal is never rewritten.
New compilations, reused compilations, reused accepted audits, and reused
stock replays for new audits are counted separately and independently
recomputed by the receiver.

## Review and remaining integration boundary

The original C/A/E files were not modified. Static Python, YAML, and shell
checks passed. Ten offline controller regressions cover reuse, missing
predecessors, accepted receipts, partial replay, and unplanned artifacts.
Two actual public archives exercised both 6144 and 11264 MiB compilation
histories. Five positive receiver checks and fourteen rejection cases
covered altered ZIPs, tars, commands, producers, and receipts. These are
orchestration checks; they do not count as Lean compilation or replay.

At this source commit, six remaining-page compilations are reusable, one
of those pages is fully accepted, and 592 numerical targets still need a
new compilation: 556 pages and 36 Check modules. The next public run must
establish their actual outcomes. Final integration with the existing
2048-row prefix, the preparation modules, and the final three theorem
modules remains a separate acceptance step. No green P2.10 status follows
from this source-only resumption change.
