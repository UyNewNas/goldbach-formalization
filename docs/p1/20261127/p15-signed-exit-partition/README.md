# Partition source publication with a real no-output probe

Status: **source publication; formal normal/kernel acceptance pending**.
Parent commit: `9cd26da0496210ab44d1e5cfa2edcfad4b332275`. No P1.5 closure or new formal credit is claimed.

The only canonical source update in this packet is `ImbalancedChen/P1SignedExitPartition.lean`:
15982 B / `cb4d4bb096d7de762cb23925af58624736bcfd753251f348b352acc67bdd2ad9` to 15972 B / `19f59a09107d934a8230d58a11afd256dd6134d7e2bba958a4144331f191249c`. It joins the rejected-state record
literal onto one line. All nonwhitespace bytes are identical. The other
three original medium-chain modules are unchanged; their exact parent
source pins are recorded in `PARENT_SOURCE_PINS.json`.

## Actual original probe evidence

| Attempt | Original task | Source | Inner / outer / lane exit |
|---|---|---|---|
| Failed v1 | `job_26dda8849e2f4038b3a5eb22f333d49b` | `cb4d4bb096d7de762cb23925af58624736bcfd753251f348b352acc67bdd2ad9` | 1 / 1 / 1 |
| Passed v2 | `job_ffea0245489740cc997473431e9840f8` | `19f59a09107d934a8230d58a11afd256dd6134d7e2bba958a4144331f191249c` | 0 / 0 / 0 |

Both lanes have `VALIDATION_LANE_FINISHED`. The successful result is
6493 B / `da7944fa8d721f973a3272744037eeadc1aeaad404872668254b493ad891254c`; its exact driver is
19700 B / `b83d3c1579a76b8f30fd0e125a6da3feed703af5370cb10f46f5e71f8abf422c` and its raw Lean log is
412 B / `5a65142e861066f000f78d984070741baacd14000261ca1818b7d3c60039e425`. Its `previous_failure` binds the original
v1 task, source, result and log. Each attempt retains all 17 exported raw
files, including the 14 gate files and three original started records.
No raw JSON, driver, source or log is rewritten.

The four original before/after protection files have identical bytes:
1357417 B / `abb9805ca3d17bff7fcd4ee5fe9f8c07c84f5f427c9f36658642d45fb7c1de2a`. Direct-import queries built no
modules. Each direct Lean call used the original guard with
`lake --no-build env lean` and no output-object flag. Inner success alone
was not treated as outer success. `TASK_IDENTITIES.json` preserves the
actual task identities and command timings; `PARTITION_RAW_EXPORT_MANIFEST.json`
records the exact subset of the original export. This packet contains no
GroupLog probe results.

## Bound adapter and unchanged old acceptance identities

The reviewed unbound runner is preserved under `reviewed-unbound/`, with
its original README, local boundary tests, raw test output and report.
Its SHA256 is `451a2578e94dd9b3432a7d316fab376cf15fe8e38789c554d86258f51d37897e`. The published `run_partition.py` differs
only in the literal value of `INPUTS`; its SHA256 is `208fca4558eca8021837b3a2ca992eb6c071a4c9c33893f98a9f93a183582c57`.
`INPUTS.json` is the data-only form of that literal. No validator or other
runner code changed during binding. The existing local 19/19 test report
applies to the original reviewed code; those tests were not rerun here.

Dictionary acceptance remains at `040d46058821746c69c5183b3f6c22792287c4ba`;
Variation acceptance remains at `f7e9219f4860a819758d52752c5a9309dd14a8c7`.
The frozen helper reads the original Dictionary receipts and exact
40-source / 840-artifact Partition dependency subset, while protecting
the full D288 metadata before and after the new operation. It does not
reaccept or recompile the Dictionary, Variation or their existing owners.
The new formal graph is those 40 old dependencies plus Partition.

After independent review and publication, root may use the new full
publication commit with the bound adapter. `--check` remains readonly and
does not run Lean. `--run` uses the original serializer/guard and original
`g.run_owner` for Partition only, then original normal/complete-owned/kernel
acceptance readers. Existing or partial target owners are retained and
rejected rather than rebuilt. This publication itself is not that formal
acceptance. See `reviewed-unbound/README.md` for the unchanged lifecycle and
partial-attempt handling details.

Only local data verification and packet assembly took place in this step;
no Git mutation, cloud task, Lean command or old acceptance replay was run.
