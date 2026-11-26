# Original owned-audit reuse after the LogPoint/source promotion

This is a read-only review of the original scripts at
`909214bbfb5ca9caa74fcc1b6f95b469bf43e125`. The source promotion is
`6e616f4e0372555f7a78bcdba3e198d0e277eec8`; its two Lean source edits do not alter
these scripts or the original template. No runner, exporter, template, scope,
resource limit or qualification rule is changed by this note.

## What is actually reusable

The original machinery supports reuse of historical valid receipts. Project
Git HEAD itself is not its content-reuse key. The wrapper's explicit project
source pin remains mandatory: this observation does not authorize omitting it.
The scripts' own Git HEAD checks concern the locked Mathlib checkout.

| Check | Exact original behavior |
|---|---|
| Per-target input snapshot | Every project module in that target's import closure: source relative path and SHA, object absolute path and SHA; toolchain; Lean/checker/template/driver SHA; qualified external snapshot when needed. |
| Runner full-audit reuse | Only `latest.json`, accepted=true, entire input_snapshot exactly equal to the current before snapshot, and every artifact hash still valid. |
| Runner replay-only reuse | Same project/toolchain/Lean/checker/native binding, successful unchanged-input replay, exact command and log hash. The replay binding excludes audit driver and template. |
| Exporter historical selection | Scans all attempt-*/receipt.json and latest.json, newest first, and tries each accepted candidate under the original validator. A newer failed latest receipt does not hide an older still-valid accepted receipt. |
| Exporter project comparison | Exact current project-module set, source relative path/SHA and object SHA. It reconstructs current absolute object paths rather than requiring the old object absolute path to match. |
| Compile dependency binding | Every closure module needs a valid compile record; source/object hashes, direct dependency object hashes and recursive dependency signatures must match. The accepted target closure signature must still be the current one. |
| Audit evidence | Exact allowed driver bytes, unchanged template, exact audit command and target substitution, successful replay/audit, immutable stage logs, full declaration inventory/types and artifact hashes are revalidated. |

Sources: [runner snapshot/replay context](https://github.com/UyNewNas/goldbach-formalization/blob/909214bbfb5ca9caa74fcc1b6f95b469bf43e125/verification/part2/run_winner9_private_audit.py#L65-L87),
[compile bindings](https://github.com/UyNewNas/goldbach-formalization/blob/909214bbfb5ca9caa74fcc1b6f95b469bf43e125/verification/part2/run_winner9_private_audit.py#L90-L119),
[runner reuse](https://github.com/UyNewNas/goldbach-formalization/blob/909214bbfb5ca9caa74fcc1b6f95b469bf43e125/verification/part2/run_winner9_private_audit.py#L210-L247),
[exporter validator](https://github.com/UyNewNas/goldbach-formalization/blob/909214bbfb5ca9caa74fcc1b6f95b469bf43e125/verification/part2/export_winner9_private_evidence.py#L138-L207),
[historical selection](https://github.com/UyNewNas/goldbach-formalization/blob/909214bbfb5ca9caa74fcc1b6f95b469bf43e125/verification/part2/export_winner9_private_evidence.py#L263-L319).

## Determining the affected targets

For each previously accepted receipt, inspect its exact
`input_snapshot.project` map. If that map contains either changed source module,
the source-SHA comparison necessarily fails after promotion, even if the target's
own source and object bytes did not change:

- `ImbalancedChen.P2HistoricLogPointInterpreter` now has source SHA
  `07798022d2370d12091d123a8f55ab106ee08a02b5dd104ce84d30aed3882552`.
- `ImbalancedChen.P2OriginalCompactArchivedTotalCandidate` now has source SHA
  `03e45537c9309e79c46fd924383d850935cb2b82a5de7ac4205731f4df048fcd`.

A receipt whose project map excludes both changes is a reuse candidate, not an
automatic success: the remaining object/tool/native/artifact/compile bindings
still have to pass the original validator. No actual new-pin selected count
can be established while P2 still has the old checkout/registry or while the
new 321-module batch has not completed its postchecks.

At pin909, 50 symbolic targets were attempted: 49 original audits passed and
LogPoint failed; 271 symbolic targets were not yet attempted. The isolated
126-declaration natrec02 diagnostic does not replace LogPoint's canonical
module receipt. Therefore the new pending list is not simply the old 271:
it also includes the old failure and any formerly accepted receipt invalidated
by the dependency change, after original historical selection.

## Next batches under the unchanged scope

1. Wait for the original fast-forward plus 321-module compiler task
   `6a0e0788dce1478985474f7aa68bb4d6` at source6e616 to finish with its normal
   qualification and source/registry/native/object postchecks. Preserve the old
   pin909 receipts. Do not recreate environments, migrate caches or rerun
   qualification merely because project HEAD changed.
2. Invoke the unchanged exporter in a fresh output directory using the explicit,
   frozen **complete 324-module list**, with ordered fingerprint
   `c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f`.
   Do not use its default directory scan or substitute a 321-only selector.
   Uncompiled A/B/W may remain unselected at this partial stage; exporter exit0
   is not full-scope acceptance.
3. Keep every selected valid historical receipt. Form pending work as
   `exporter.unselected` intersected with the fixed symbolic321 list, ordered
   by the existing topological sequence. This puts LogPoint before targets
   whose proofs import it. Do not send already-selected targets back through
   the runner solely because latest.json is not the selected historical receipt.
4. Audit only that pending list in bounded batches using the original runner,
   qualified native snapshot and `--memory-mb 11264`, with one audit worker.
   Use new, nonexisting summary basenames (for example
   `p24-owned-symbolic-002-r01.json` if still unused), retaining normal postchecks
   even when one module fails. Do not carry the old registry SHA forward as the
   expected new one: bind the actual completed compiler batch's registry and
   verify it remains unchanged during each audit batch.
5. A/B/W must first pass their respective original compiler gates in that order.
   Then audit their canonical modules, including all generated owned declarations.
   The final exporter still receives the same complete324 list and must leave
   zero unselected modules and no duplicate declarations.

The original CLI accepts explicit module arguments; the exporter requires a
new output directory, and the runner requires a distinct summary basename.
There is no added timeout/thread flag or weakened-template mode in this plan.
See [runner options](https://github.com/UyNewNas/goldbach-formalization/blob/909214bbfb5ca9caa74fcc1b6f95b469bf43e125/verification/part2/run_winner9_private_audit.py#L171-L203)
and [exporter options](https://github.com/UyNewNas/goldbach-formalization/blob/909214bbfb5ca9caa74fcc1b6f95b469bf43e125/verification/part2/export_winner9_private_evidence.py#L229-L255).

No remote task was submitted or executed for this review. No new canonical,
finite A/B/W, full324-audit or whole-P2 completion credit is claimed.
