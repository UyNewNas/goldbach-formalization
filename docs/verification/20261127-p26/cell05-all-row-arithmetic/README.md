# Cell05 all-row arithmetic continuation

This checkpoint resumes the existing P2.6 work without repeating accepted
proof commands. The manuscript remains the frozen 2026-11-06 version.

## Inputs already accepted

`P2OriginalSaving19Cell05AllRowGaps` has one accepted owner and three checks
(strict normal compilation, stock kernel replay, complete declaring-module
audit). Its original run is `8c52634c0b3e4a2fa00d1dc337cbca5e`; its read-only
verification/export run is `6405a08f25e1497cbd5969f6d31a9c1d`. The exact
1,465,240-byte archive is retained in the sibling `cell05-all-row-gaps/accepted`
directory. It proves clauses 3 and 5 for all 56 original decoded rows.

## New source prepared for verification

The unchanged, previously reviewed
`ImbalancedChen/P2OriginalSaving19Cell05AllRowArithmetic.lean` supplies the
remaining eight clauses. Its source SHA-256 is
`8a271737e570b277b2f30a39ec193fe72480f8e685de5860e648b8477918c931`.
Both public statements quantify over `Fin 56` and use each original row's
ordered vertex IDs. `fastDet_eq` transports the computational determinant
to `Matrix.det`; positive stored volume gives nondegeneracy.

The new configuration is bound to the actual accepted Gaps RUN, object,
SUCCESS, complete archive and read-only report. The deployment package
contains exact copies of that reviewed workflow, this source and the
original FastDet supplier capsule. It does not modify earlier runtimes,
guards, source files, receipts or command flags.

Expected new acceptance: one owner, three checks, 130 reused project
suppliers, 131 project modules including the new owner. All private and
generated declarations must be audited; the 15 explicit source prints are
not an assumed complete declaration count.

At this source checkpoint Arithmetic has **not yet been compiled**.
Its three new checks and their independent evidence readback are the next
steps. Any failure will be retained separately.

## Scope boundary

Acceptance of this owner would establish all ten `RowDataChecksFor`
conditions for the 56 original decoded Cell05 geometry rows. The Q96
statement concerns the geometry Jensen record's old floor. It does not
supply the separate original moment record's new floor or its ten Q80
factor bounds.

The global archive transport, original moment-floor chain, simplex
ownership, integration, and complete 28,918-row Saving19 endpoint remain
open. `P2_6_complete=false`. No board completion, PR aggregation or merge
is claimed by this checkpoint.
