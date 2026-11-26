# AllK first normal-compile repair and original PerGroup@O acceptance

This packet continues `4c1fa038318acbc2070bd9ef7ec626452b38466d`. It changes only four proof lines in `ImbalancedChen/Part3AllKLambdaChartCorrection.lean`; all declarations, statements, hypotheses and literal imports are unchanged.

## Actual original O result

P1 service access was restored on 2026-11-26. The retained task `job_cda017c5183c4b5ba80a8a2182f446ba`, source commit `dc1e74ee5c15471d6dd22e4e2c609d5e79b0169d`, ended with exit 1. It fully accepted `P5PerGroupIntegerHBAtlasPushforward`, then failed normal compilation of `Part3AllKLambdaChartCorrection`; the other twelve selected targets did not start. This failed group remains failed.

PerGroup's original normal, named-kernel and full environment-owned type/axiom receipts were revalidated by the unchanged original O APIs. The actual counts are 68 owned and 58 public, audit `370ebae525106ac7bd2e`, original closure 69. The bounded public record is `docs/p1/20261125/p15-current-public-acceptance/PERGROUP_O_PUBLIC_ACCEPTANCE.json`. It preserves O as the acceptance source commit and records all six receipt fingerprints; it does not rerun or rebind the accepted owner.

## Exact cause and repair

The four errors came from two concrete API interactions:

1. After `push_neg`, `hbad` has type `¬ Nat.Prime n ∧ (IsPrimePow n → Nat.Prime n)`. The original proof applied it as a negated disjunction. The two lines now use its conjunction projections.
2. Default `simpa` rewrote `List.getD` to `Option.getD` before the explicit indexed-list equality could match. The two lines now use `simpa only` with the original `List.getD_eq_getElem` and `hget` arguments.

`REPAIR_CANDIDATE.json` records the complete pre/post file bindings and two exact reversible byte splices. Independent static review checked these against the four real compiler errors and found no remaining blocking source-review findings.

## Actual whole-module probe

`probe_allk_repair.py` was authored locally and sent unchanged to the P1 compiler. Task `job_7ace088559f843d180cb12d7e4bd45a1` succeeded: exit 0, 55.055 seconds, sampled peak memory 7,185,842,176 bytes. It called the original serializer and guard for one `lake --no-build env lean` check of the entire repaired module, requesting no output objects.

The probe first revalidated the original PerGroup acceptance without compiling it. All 21 watched project sources, their 441 artifact slots, original O evidence, runtime configuration and Git state were preserved. The remaining output contains deprecation/style warnings, with no error or forbidden proof placeholder. `ACTUAL_ALLK_PROBE_RESULT.json` records the exact 1,327-byte log and its SHA-256.

**The repaired AllK file has passed this whole-module typecheck probe. It has not yet received normal/kernel/full-owned acceptance.** Its old failed setup remains preserved in place; the independently bound updater must archive that exact setup and install only the repaired source before a reanchored entrypoint runs formal acceptance. The existing entrypoint's old source anchor is not silently changed by this packet.

P1.5 remains open. The historical rough-comparison files from the preceding commit keep their source-only status. No closed-node PR scope is enlarged.
