# Local assembly of the two new P1.5 owner evidence packets

This directory prepares an evidence publication under
`docs/p1/20261127/p15-partition-group-log-acceptance`. Its fixed source parent is
`ce08ba304bafb7732c8fd9f27553822f87cfb7d0`.

The assembler does not run a compiler, a kernel checker, a published adapter,
Git, a cloud task, or a new acceptance validator. Acceptance remains owned by the
original frozen adapters, the original `g.run_owner` normal/kernel/full-owned
audit mechanism, and the later independent original `--check` receipts. The
assembler checks the transport and consistency of those already-produced
records, then preserves their exact bytes for publication.

## Completion gate

Both owner entries must supply real pinned files before assembly can write a
publication directory. An entry contains:

| Input | Required original evidence |
| --- | --- |
| `formal_provider` | Full provider task metadata for the actual successful formal task |
| `formal_stdout` | Complete original formal task output, including the stage fingerprint and the final original check result |
| `readonly_provider` | Full provider metadata for a distinct, later successful readonly/export task |
| `export_stdout` | Complete compressed export JSON printed by the exact original export script |
| `raw_root` | Local directory containing all four decoded original operation, owner, readonly and stage groups |

Each file pin has exactly `local`, `bytes`, and `sha256`. `local` is an absolute
regular-file path. No task status, count, or SHA may be supplied from a prediction.

The compressed envelope is the complete export member list. The assembler checks
its compressed byte count, decoded SHA256 and byte count, expected group set,
every base64 member, exact original remote path, and every decoded local file.
Every original exported member is copied, including started markers, commands,
logs, context records, plan bindings, ownership/type/axiom exports, source
backups, the executed adapter, and preservation snapshots.

For each owner, the retained records must show all of the following:

- The actual formal and independent readonly provider tasks have both finished
  successfully, with complete output. The readonly task is distinct and begins
  after formal completion. Both submitted command bodies equal the preserved
  transport scripts byte for byte.
- The original readonly result says `REVALIDATED`. `FRESH`, missing, partial,
  queued, or failed outcomes do not satisfy this gate. The readonly command is
  the exact published adapter's `--check` at its original source acceptance
  commit. Its stdout and stderr SHA256 bindings are retained.
- Original operation PASS, worker PASS, install receipt, source backup,
  before/after snapshots, normal command, outer command and finished lane all
  agree with the original module/source/adapter identity. Only that new target
  appears in the actual normal build; the direct readiness command builds none.
- The worker's original normal receipt, audit plan and audit result fingerprints
  resolve to the exported raw files. The original audit is complete and includes
  private/generated declarations. Counts and axiom names are read from the real
  `OWNED_EXPORTS.json`, then compared with the original worker, audit, readonly,
  and export-envelope summaries. No owned/public count is hardcoded.

These checks bind published records to their actual raw transport. They do not
rerun, reimplement, replace, or grant a new mathematical acceptance. In
particular, the dependency objects remain under their original acceptance
identities; the assembler performs no dependency replay or compilation.

## Immutable identities

| Owner | Source acceptance commit | Source SHA256 | Adapter SHA256 |
| --- | --- | --- | --- |
| `ImbalancedChen.P1SignedExitPartition` | `7296a9659fbf34773ec03f437860c14073b3a638` | `19f59a09107d934a8230d58a11afd256dd6134d7e2bba958a4144331f191249c` | `208fca4558eca8021837b3a2ca992eb6c071a4c9c33893f98a9f93a183582c57` |
| `ImbalancedChen.P5OriginalGroupLogAbelVariation` | `ce08ba304bafb7732c8fd9f27553822f87cfb7d0` | `dc2870dd9a94a2f6f1dfe3e8872e8c4ba3c541cb58ec3595fd406f1910db7f73` | `9f618457ddd5dd25b251b153cf5f278bbf37ffead78247a034146efa95c49057` |

The actual formal task identities are respectively
`job_5fbfb818f8f24d439f519edc1d22176b` and
`job_67db0441349a4ad58ecacd1480001ceb`. Partition's independent readonly task is
`job_d2a04ab9365246faa0b39e61f510694b`. GroupLog's later readonly task is
`job_9d92c26f45804a4a954b05bf94ad82f5`; its actual completion and output must still
be supplied in the original provider metadata and exact export.

The original Partition provider event
`job_9db0b07f37bf40caa314b1c6637647d7` is separately retained as
`resource_unavailable`, with `started_at=null` and zero output bytes. It did not
run a normal command. It is not counted as a failed formal attempt and does not
cause the successful normal to be repeated.

## Support and next-step preservation

`SUPPORT_BINDINGS.json` pins frozen local copies of the source-publication Git
verification, independent source/adapter/INPUTS reviews, exact stage/export
scripts, original pre-execution provider event, and the reusable next
PolicyComparison UNBOUND preparation and its review. The original locations are
recorded in `frozen-support/metadata/SUPPORT_ORIGINS.json`.

The next PolicyComparison template in this packet must still have
`PARTITION_BINDING=None`. Its readiness record must have no parent acceptance
binding and no prefilled ownership count. It is an archived reusable preparation;
a separately queued or later bound probe is outside this two-owner acceptance
claim. No PolicyComparison formal credit is assigned by this packet.

The large failed-probe raw packages already belong to the two published source
commits. This packet references those immutable source packages instead of
copying the failed probe packages again. Small independent reviews and exact
transport records are included for traceability.

## Local use

Before both exports are available, print the requirements without touching a
project checkout or calling an adapter:

```bash
python3 -B /workspace/scratch/b70e634c1342/p15-next-dual-owner-acceptance/assemble_acceptance.py --requirements
```

`INPUTS_TEMPLATE.json` intentionally contains null owner entries. Running it must
refuse before loading support, processing an export, or writing a publication:

```bash
python3 -B /workspace/scratch/b70e634c1342/p15-next-dual-owner-acceptance/assemble_acceptance.py --bindings /workspace/scratch/b70e634c1342/p15-next-dual-owner-acceptance/INPUTS_TEMPLATE.json
```

After root has supplied both complete original exports and actual provider
metadata, create a separate `INPUT_BINDINGS.json` with the exact local pins.
Run the same command with that input file. The default output is this directory's
fresh `publication/` child. Existing publications and `FILE_INDEX.json` are never
overwritten. All checks for both owners happen before publication writes.

The output `FILE_INDEX.json` is a top-level array of
`{local,path,bytes,sha256}` suitable for root's separate Git API publication.
Only new documentation/evidence paths are indexed; no canonical source is
modified. `ACCEPTANCE_SUMMARY.json` is generated only when the complete original
evidence for both owners has passed the transport/completion gates.

## Scope of the final report

The original fixed registry stays **18 accepted out of 21 registered**. Partition
and GroupLog are listed as two separate new owners, with counts derived from
their own real audit records. The original Dictionary and Variation acceptance
identities are retained inside the raw dependency records.

The restored ShiftedTau source
`d006abee2c8dd632d9fd9712b29030dbff0a70f6c95ade6ffec92955a37444c2`
and the reviewed medium first-disagreement bridge
`edb45d7c44440fdb68937fc0931c95c7a7ab0532ec26b1f20002b8669c8700a2`
remain **source-only**, with no new formal credit. The bridge's scope is the
actual coefficient difference, unchanged complete divisor, rough-mask change,
and original common-tree first disagreement. It supplies no whole-atom or
medium estimate. **The complete P1.5 task remains OPEN.**
