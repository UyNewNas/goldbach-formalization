# Coordination contract

The single live coordination root is `/workspace/shared/chen-coordination`. Read `p0/automation/control.json` and `ownership.json` before editing. All workers start from checkpoint `1337e2db4712fb4a9f86add073f771f84b66d0c8`, while separately comparing legacy part suppliers; no reset or downgrade is authorized.

P1–P5 submit `REQUESTED` JSON into their allocated `requests/` directory. Include exact source/data hashes, complete relevant dependency fingerprint, toolchain, stages, strategy, current type and unpaid assumptions. They do not start Lean, Lake, checker, audit or CI. P0 accepts requests before READY_FOR_P0.

P0 alone invokes `with-heavy-lock.sh` for any local proof-environment process. Its flock descriptor is inherited for the entire command and child-process lifetime; all workspaces on this host share the absolute lock. CI is dispatched only by P0 and has a separately tracked remote run identity. A running flag without a live process and terminal receipt is LOST_TERMINAL_EVIDENCE. Never retry unchanged failure just because a new hour began.

Publish status/source with `[skip ci]` until P0 selects verification. A skip is not a PASS. Exact prior receipts may cover unchanged inputs; archive/hash checks are not mathematical verification.
