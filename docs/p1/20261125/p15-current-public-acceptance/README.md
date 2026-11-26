# Bounded public summaries of retained P1 acceptance

This directory contains a read-only acceptance collector for four fixed groups.
It reuses the complete published Batch13 `audit_valid` path used by
`p15-singleton-proper-power/evidence-initial-four/collect_public_acceptance.py`.
The implementation task does not run the collector against P1, compile Lean,
replay a kernel, inspect a new compiler job, or publish an acceptance result.

## Fixed identities

| Group | Fixed source commit | Permitted requested scope | Published project graph |
| --- | --- | --- | ---: |
| `atlas10` | `418ad4b9a5f2d992871062258a2eefd7fdf4b9ee` | The complete ten-owner Atlas integration list | 68 |
| `p3-20` | `418ad4b9a5f2d992871062258a2eefd7fdf4b9ee` | All twenty owners, or an explicit nonempty subset of that fixed list | 77 |
| `pure2` | `ef450be0a89b6a3f88b3bca19d06e04e7967fa18` | Both owners, or an explicit nonempty subset of Core/Mellin | 168 |
| `mellin-current` | `21789da92213323d645122cfcc7dff9c10dc82d6` | The complete one-owner Mellin group; no `--targets` override | 168 |

The exact target lists, driver hashes, source-manifest hashes, evidence roots,
and parent-observed job identities are literals in the script. There is no
arbitrary source commit, project path, output path, or target option. `--targets`
is permitted only for `pure2` and `p3-20`; unknown, duplicate, or empty subsets
hold. Omitting it requests the complete fixed group, so the collector never
silently drops an unsuccessful requested owner.

The fixed jobs are Atlas
`job_5f42ad18fde84377987c244daf0b5bfc`, P3
`job_41c06d666c6642889cc27d82ee281eb7`, and pure owners
`job_0c98f60f3fbe4aaa8d3e23fcf53dbcb8`. The repaired Mellin job is
`job_8d58f7741c56448980ca0984ae5c0239`. These job IDs identify the tasks observed
by the parent. The retained local result, source commit, scope, serialized
command, and per-owner evidence are independently checked; the script does not
query the cloud service or turn a configured job ID into an acceptance claim.

The original collector is fixed at commit
`bbcf75642ec19ebd976820c89011e83351856756`, SHA-256
`cd70c392b10cc1a57b7759c4fa16b49be5cc6780a43e814be666f0ee52dec123`.
Both selected drivers load the same unchanged Batch13 API at
`4cea0407c1258eaddd7d4952cffa4aea67310422`, SHA-256
`95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea`,
with helper commit `220c14630ffd266f824bdbf0977147ecb740c0dd`.
The collector changes no driver, API, guard, serializer, runtime, or old receipt.
The driver is loaded from its fixed Git commit and compared with the retained
`executed-driver.py`. Its module file identity points to that retained file, as
in the original job. No current working-tree driver path is required or changed;
the P1 checkout may intentionally retain its earlier dirty state.

## Complete checks and restricted output

For every requested owner, the collector invokes the original `audit_valid`
with that owner's retained normal receipt, frozen audit plan, original source
commit, committed source graph, and pinned helpers. That path revalidates:

- The original one-owner normal command, real Built scope, source/output
  fingerprints, dependency objects, runtime, and normal log.
- The exact named `leanchecker --verbose` command, its exit status, command
  receipt, log hash, and frozen runtime/template identity.
- The complete environment-owned inventory, including private entries during
  verification, equality with the recorded owned exports, exact owned/public
  counts, and the original axiom restrictions.
- The retained audit's stock readiness commands and their exact scopes.

The allowed axiom union remains `Classical.choice`, `Quot.sound`, and `propext`.
No new axiom declaration is allowed. No fallback accepts a normal receipt alone,
a sampled theorem, a public-only subset, or a shortened owned inventory.

The public JSON contains owner/module identities, source hashes, receipt/log
hashes and byte counts, owned/public counts, axiom unions, validated command
exit codes and scopes, and context-preservation statements. It emits no
declaration names or types from the owned inventory, no private declaration
details, raw logs, or raw exception text. The original run result and serialized
worker command are bound separately. All retained evidence fingerprints and
the selected live context are checked again before output.

Atlas/P3 use their original complete live 68/77-source preflight. Selected target
artifacts and all preserved dependencies must remain unchanged during
collection. Their acceptance class is current P1 integration of existing proof
sources; their historical acceptance identities remain intact. Pure owners have
a separate new phase2 mathematical-owner acceptance class. The collector itself
develops no new mathematical proof and always records `whole_P1_5_complete=false`.

## Core can retain its original acceptance after a Mellin repair

For `pure2`, the full published 168-source graph is verified from the fixed
`ef450…` Git commit. The current installed graph is checked only for the
explicitly requested owners and their actual dependencies, using the original
`context` and `audit_valid` APIs. Core and Mellin each have only literal
`import Mathlib`; requesting Core therefore checks a live project closure of
one source. The summary distinguishes the published graph count 168 from that
selected live closure count. It does not assert that all current168 sources
still equal the earlier commit.

This permits the already accepted Core at its original `ef450…` identity to be
revalidated after an unrelated Mellin source repair. It does not rebind Core's
normal receipt or audit to a new commit. The current parent observation reports
Core accepted and Mellin failed in that original run. A Core-only request may
therefore succeed after full audit revalidation, while a request including
Mellin must hold. The output preserves the original overall run failure,
including worker exit 1 and the reported failed owner, instead of describing
the original two-owner run as successful. Any later Mellin source identity needs
an explicit new whitelist binding; it cannot be supplied through a CLI override.

## Repaired Mellin has its own fixed acceptance identity

`mellin-current` binds only `ImbalancedChen.PrimeProductsMellinExactMeanInsertion`
at `21789da92213323d645122cfcc7dff9c10dc82d6`. Its driver remains SHA-256
`8f18e7d7b00db15ca071e28f6bffdae263fc098df4ccb0156d17fdaa64374fe5`; its
published 168-source manifest is SHA-256
`c1dfff16bd8a758d47f14f5dfbed1ca3c836f657b525ed2afbefbf2605e182ad`.
The group requires the original successful `runs/attempt-00000` to have exactly
this single target, worker exit 0, no failures, and full-group success. It then
revalidates the complete original normal, named-kernel and full-owned evidence
through the unchanged `audit_valid` API. The published Git graph has 168 sources;
the required current live project closure is the one Mellin source, whose only
literal import is `Mathlib`.

This addition leaves all three earlier group bindings unchanged. Core remains
bound to `pure2` at `ef450…`; it is absent from the new group's requested scope
and receives no new source or acceptance identity. The existing
`ATLAS10_PUBLIC_ACCEPTANCE.json`, `CORE_PUBLIC_ACCEPTANCE.json` and
`BRUN_PUBLIC_ACCEPTANCE.json` are retained without modification. Publishing this
collector update requires collecting only `mellin-current`; it does not rerun
the earlier collections or any Lean compilation.

## Partial P3 integration remains a partial original run

The parent observation reports that `Part3BrunWeights` completed its full owner
acceptance at `418ad…`, while the next target, `Part3CompletedReciprocalWeil`,
stopped at external-import stock readiness exit 3 without being compiled.
An explicit BrunWeights-only request is therefore permitted. It must still pass
the complete original `audit_valid`; the collector preserves the original
whole-group failure, worker exit, failed owner, and all reported not-accepted
owners. A request containing CompletedReciprocalWeil or another unaccepted
owner holds. It never describes the twenty-owner integration as complete.

P3 retains its full live77-source preflight and protected dependency checks even
for this requested subset. The selected owner's artifacts are also compared
before and after collection. No dependency is compiled to make a receipt valid.

## Invocation after review and publication

After publishing this addition, run only the new group from the published P1 checkout:

```bash
python3 -B docs/p1/20261125/p15-current-public-acceptance/collect_public_acceptance.py --group mellin-current
```

Only the fixed `runs/attempt-00000` and corresponding owner evidence are read.
An incomplete group, unsuccessful requested owner, unknown or ambiguous audit,
stale context, or missing evidence emits `PUBLIC_ACCEPTANCE_HOLD` and exits 2.
No accepted counts are emitted in that case. Successful collection creates one
exclusive public JSON under
`/workspace/p1-complete-proof/20261125-p15-current-public-acceptance-v1/`, named
by group, original source commit, and explicit subset. An existing byte-identical
summary is reused; a differing file holds. Nothing in the project, cache,
original normal/kernel evidence, or Git metadata is written.

The script prints `PUBLIC_ACCEPTANCE_SUMMARY` followed by that bounded public
JSON. Counts are obtained only from successful full retained-audit validation;
this directory does not prefill acceptance counts for queued or failed owners.
