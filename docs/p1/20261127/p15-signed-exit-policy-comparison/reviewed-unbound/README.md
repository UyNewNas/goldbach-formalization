# PolicyComparison formal adapter: review before binding

Status: **UNBOUND; no formal execution**. `run_policy.py` has `INPUTS = None`.
The real original-source no-output probe has completed, and its seventeen raw
files are available. `ACTUAL_PROBE_INPUTS.json` records their actual hashes;
it is not installed into the adapter until independent review is complete.

The complete mathematical source is frozen at 17805 bytes / SHA-256
`c60992855b519d9767e66f31c9007dd18f2292e326e28539fc2a39d1d831b57f`.
All proof bodies, statements, definitions, comments and namespace bytes must
match the original `040d46058821746c69c5183b3f6c22792287c4ba` source exactly.
`POLICY_ORIGINAL_INTERFACE.json` in the parent directory inventories complete
original headers, including their internal `let ... :=` terms; no header
truncation or proof repair is permitted by this adapter.

## Reuse and execution scope

- Publication parent: `19f493948737f6f5f7bc5e858d5266b41f976b22`.
- Partition keeps its original accepted commit
  `7296a9659fbf34773ec03f437860c14073b3a638`; the new publication does not
  rebind it. Dictionary remains `040d4605...`, Variation `f7e9219f...`.
- The original bound probe helper, 12998 bytes / `1b0915e3...`, is reused
  unchanged. Its `load` uses the published Partition `load/check` API.
- The forty original project inputs plus accepted Partition give 41 actual
  project dependencies. Adding only PolicyComparison gives 42 source nodes.
- One call to the original `g.run_owner` is permitted, for PolicyComparison.
  The direct preflight is guarded `lake --no-build build +Partition:olean`.
  Existing objects, configuration, runtime and old acceptance evidence are
  checked through the original parent APIs and protected before and after.
- Canonical Partition and GroupLog sources must equal the new publication's
  parent. The Policy mathematical source itself is unchanged.

## Real probe gate

The adapter requires every one of the seventeen original files, exact hashes
and exact publication-byte equality. It verifies the original source and
driver, direct/inner/outer command provenance, all three started receipts,
zero dependency builds, completed outer lane, unchanged runtime guard,
byte-identical preservation and Git snapshots, and the same original parent
acceptance. Unreviewed additional or partial probe histories block execution.
The no-output probe confers no formal owner credit.

Before a formal run, an existing or partial Policy owner blocks execution.
After a run, normal and complete-owned/kernel evidence is read through the
original APIs, including private and generated declarations and standard
axioms. Owned/public counts are read from actual resulting exports and are
not prefilled. A separate readonly check verifies complete outer dispatch.

## Local checks and review boundary

Five local checks passed against the actual probe raw data: UNBOUND refusal
before operative helpers, whole-source immutability, complete raw inventory,
the same source/parent/zero-credit contract, and inner/outer/lane completion
with no dependency builds. These are Python adapter checks, not Lean or kernel
verification. The report is `LOCAL_CHECKS.json`; all mathematical acceptance
counts remain null until actual formal execution.

Next: review this unbound adapter, replace only its `INPUTS` assignment with
the already verified actual raw-file bindings, then publish on the stated
parent and let root schedule the one new owner. This agent performed no
cloud, Git, Lean or kernel command for this draft.
