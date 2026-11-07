# Append-only E0 batch: original rows [4,64)

This archive accepts 60 new actual E0 integrals and their exact append to the
previous four rows. The cumulative object is the actual finite sum of rows
[0,64), not a geometric union or a full-mask arithmetic gain.

Read [ROUND3_HANDOFF.md](../../../../docs/part2/ROUND3_HANDOFF.md),
[receipt.json](receipt.json), [generated-report.json](generated-report.json)
and [append-ledger.json](append-ledger.json).

The successful local batch contains three strict official frontend executions,
three stock selected-module kernel replays, and a final all-production-module
audit. The audit covers 709 declarations in twelve modules, including private
and compiler-generated declarations. Its 309 old records are exactly unchanged;
400 records belong to the three new modules. Only propext, Classical.choice and
Quot.sound occur as transitive axioms.

All successful execution receipts and raw logs are in [gates/](gates/).
Unsuccessful or excluded attempts remain in [attempts/](attempts/), with the
scheduling exclusion explained separately in [scheduling-rejections.json](scheduling-rejections.json).
The original receipts are never rewritten to change their outcomes.

The unchanged nine-module historical receiver passed before any mutation; its
record and the complete parent source identity manifest are retained here.
The new [verify_acceptance.py](verify_acceptance.py) checks that historical scope,
the new scope, all source and object bindings, exact data decoding and complete
compiler types. It does not invoke Lean or prove an integral. It rejects the
two excluded scheduling attempts and checks the accepted execution intervals.

[build_receipt.py](build_receipt.py) only assembles completed external execution
evidence. To reproduce mathematical validation, use the fixed project toolchain
and `verification/part2/check.sh`, or a new source-bound execution of the
[archived official frontend runner](../runtime/README.md).

Source CRLF bytes and LF seven-field streams are distinct identities. The
default Prefix4 generated sources and report remain byte-for-byte unchanged.
Certificate names 0004 through 0063 retain original source ordinals; no row is
skipped or renumbered. The old four-row integral is added exactly once.
