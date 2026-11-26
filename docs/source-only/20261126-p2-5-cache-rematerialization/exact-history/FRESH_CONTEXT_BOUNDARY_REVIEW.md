# Independent boundary review: Cell00 attempt008 fresh context

Reviewer: `p25_finite_review`, 2026-11-26.

Status: **design boundary passed; implementation and execution pending**.
This is a static review of the proposed narrow continuation, not an accepted
attempt008 receipt. No cloud scan, Lean execution, old test rerun, production
edit, historical receipt edit, or old runner edit was performed for this review.

## Reviewed files and exact identities

Repository root: `/workspace/library-files/p25-proof-work`.

| Repository-relative file | SHA256 |
| --- | --- |
| `docs/verification/20261126-p2-5-resumed/run_cell00_four_consumers_v7.py` | `4d0b9e19a564f99416fc5f57ccb41f0570df2b3af53d5a61277f31b3ee063197` |
| `docs/source-only/20261126-p2-5-cache-rematerialization/restore_p3_cache.py` | `d6d895b80f07c9bd499501cce3e275a271ccd8ddfc166826942953afa960d542` |
| `docs/source-only/20261126-p2-5-cache-rematerialization/RECOVERY_SELECTION.json` | `cd0b812eaf659d675406c594f7eae66b4ea550bdd30f874b1a2876ebdef04cbf` |
| `docs/source-only/20261126-p2-5-cache-rematerialization/exact-history/EXTERNAL_SNAPSHOT_BLOCKERS.json` | `7ad7bdadcf10290d053af16fdd89393e8778a71e5dee08e4fa857dd3a49e4580` |
| `docs/source-only/20261126-p2-5-cache-rematerialization/exact-history/OWNED_AND_SNAPSHOT_RECOVERY.md` | `f232db0b376d77a531d8562251bb1f72a663c18d89df441bbdc09b635f5b5a3b` |
| `docs/superpowers/specs/2026-11-26-p2-5-fresh-context-design.md` | `64b70f23eec895b41ac5c89fa47d606306e80fcd3bb2fdc4244d5b0179eea986` |
| `docs/superpowers/plans/2026-11-26-p2-5-fresh-context-plan.md` | `ebc08983feb81e8d4e860aeee5cb401d29532f03851bed8ab043e081080d1054` |

The design and plan were checked against the boundaries below. Their final
versions explicitly cover the 544-name Payload inventory, 296 scoped private
bindings, exact dependency-object closure, unobserved historical files, and
truthful normal-rematerialization accounting. No substantive design omission
remains in those reviewed versions. The future v8 implementation needs its own
independent diff review; this document does not approve unreviewed code.

## Exact archival exception set

Only absence of the following five envelope files is an allowed historical
archive gap. **Each expected byte count is exactly 4,302,154.** A present file
with a wrong size or SHA is a conflict, not an allowed absence. A sixth missing
non-object historical input is outside this continuation. If an original
envelope becomes available, validate its exact bytes and preserve it.

| Exact historical path | Expected full SHA256 |
| --- | --- |
| `/workspace/p25-q96-20261125/.lake/diagnostic/p25-cell00-five-consumers-attempt004/COMPLETE_EXTERNAL_BEFORE.json` | `ed4b8328aacf4606ebb2eae0b5d680c54efa73a3a4564a07cc036f3f4fed224a` |
| `/workspace/p25-q96-20261125/.lake/diagnostic/p25-cell00-five-consumers-attempt005/COMPLETE_EXTERNAL_BEFORE.json` | `079497803ca132cadcab9cf4d8310b0fefcee0be1be07ea4f1a942169c7d0dd7` |
| `/workspace/p25-q96-20261125/.lake/diagnostic/p25-cell00-field-decode-attempt004/COMPLETE_EXTERNAL_BEFORE.json` | `733ef9fe3577992676b93cae03b9473389a01f79b30314029560303b71e8cd44` |
| `/workspace/p25-q96-20261125/.lake/diagnostic/p25-cell00-field-decode-attempt005/COMPLETE_EXTERNAL_BEFORE.json` | `3d354f35e94ff09ed63773692cb791dab3f22d659a8d40d03b8fe3ca534f91ca` |
| `/workspace/p25-q96-20261125/.lake/diagnostic/p25-cell00-field-decode-attempt006/COMPLETE_EXTERNAL_BEFORE.json` | `7335b49d0723555b677fbaf00e0216142fdb1fb3e2516440a7cd8db73cf21a42` |

The bounded reconstruction audit identifies ten unavailable clock values:
`started_utc` and `finished_utc` for each envelope. Overall run/stage times do
not determine those separately sampled values. Equality of the deterministic
content or expected length does not establish the old full-file SHA. No
synthetic timestamp, masked JSON, or current snapshot may fill an old path.

The unchanged v7 full-history preflight and unchanged recovery normal mode
remain blocked by these missing bytes. The unchanged recovery `--restore`
may truthfully restore available exact bytes and report `PARTIAL_RESTORE_ONLY`.
The new protocol must record the five gaps separately; it must not catch
arbitrary missing-file errors or pretend that an absent artifact was read.
Unread envelopes must not enter the new observed `frozen_inputs` map.

## Retained proof and identity gates

1. **Source and input identity.** Retain the exact 45-module graph, selected
   source hashes, imports/public names, original statements/data, accepted
   OriginalParse transport override and its three private helpers. Preserve
   all 14 raw witness size/SHA bindings and the before/after input checks,
   including OriginalInput's original elaborator reads.
2. **Runtime and actual resolution.** Retain Lean and leanchecker binary
   hashes, `LEAN_SYSROOT`, Mathlib commit
   `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, toolchain/manifest pins, and
   the exact nine ordered providers: Lean `lib/lean`, Mathlib build,
   plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq,
   batteries. Validate the exact names/paths/sizes/SHA of all 5,312 resolved
   objects and 10,624 companions. Reject shadow providers, extra/missing
   companions, wrong equal-count sets, and project fallback outside the
   isolated library. The already observed 15,940 path-hash matches alone
   are insufficient: recovery `runtime_check` does not perform all these
   actual provider/companion resolution checks.
3. **Historical accepted owners.** Retain `strict_commands`, `modern_owner`,
   `legacy_owner`, `verify_reuse_validation`, `verify_container_objects`,
   and their source/object/companion/command/log checks. Owner source origin,
   accepted status, all three successful stages, audit source, complete
   declarations/inventory and actual dependency closure must agree. Keep
   the exact 544 Payload names and 296 private scoped-simp bindings. Preserve
   original publications and failed aggregates, including the accepted
   Decoded owner under the still-unsuccessful consumer005 aggregate.
4. **Owned audit and new gates.** Retain `read_audit`, `audited_imports`,
   private-scope and Parse-helper predicates. Serialized, environment and
   declaration inventories must coincide with no duplicate/missing names;
   actual project closure and external imports must match. Reject axiom,
   partial and unsafe declarations; retain the original allowed-axiom set
   `{propext, Classical.choice, Quot.sound}`. Every new consumer still needs
   normal Lean, stock `leanchecker --verbose` independent replay and the
   complete owned audit, including private/generated declarations.
5. **Stage context and resources.** Retain the exact strict flags
   `-t0 -j1 -M11264 -DwarningAsError=true -DmaxRecDepth=1000000 -DmaxHeartbeats=80000000`,
   600-second stages, 320-MiB startup/256-MiB per-stage reserves, hardlink
   no-overwrite/symlink safeguards, and actual command/log/exit/timeout
   records. Check publication/clean tracked state, all actual frozen inputs,
   provider and companion resolutions after every stage and at finalization.

These predicates remain the old v7 acceptance contract. Only the availability
and physical reading of the five listed old envelopes can move to an explicit
historical-gap ledger. Their old expected descriptors and all other history
checks remain intact. This is not permission to bypass another owner or
external-context validation.

## Minimal attempt008 sequence

Use a new publication-bound driver/selection and the previously nonexistent
`/workspace/p25-q96-20261125/.lake/diagnostic/p25-cell00-four-consumers-attempt008`.
Keep the old runners, selections and receipts byte-identical. Current execution
HEAD/publication is separate from each historical owner's publication.

First capture a real current context. The preserved upstream arithmetic
snapshot is member `COMPLETE_EXTERNAL_BEFORE.json` (4,949,062 bytes, SHA256
`b94ab99b39a831a616d626c55c4b89c0a921d15c95319de19063d375bc982728`)
of `docs/verification/20261126-p2-5-continuation/cell00_remaining_arithmetic_accepted.tar.gz`
(archive SHA256 `1e856f4e3c593d9201649dd3f8f7bd8f7cb88ae48ab536f641f16297290bdbf4`).
Bind those actual bytes and compare each freshly resolved external record with
that complete inventory and every relevant old receipt's frozen hash map.
Record real new clock values, a new snapshot path/SHA, and true current
before/after context checks; do not assert recovery of an old envelope.

Reuse the 31 available exact objects without recompiling or repeating their
accepted replay/audit. Traverse the complete 41-object dependency DAG first,
then filter to the currently unresolved subset of the unchanged ten-module
whitelist. Preserve dependency checks through already available intermediates.
Compile only that missing subset from the original source, into fresh outputs.
After each normal stage, require the full current context and witness checks,
exact original output SHA, and the original empty project companion set before
admission or freezing. Any restoration of an old object alias may install only
those exact original bytes and must be recorded; it cannot rewrite evidence.

**Stop on the first different output SHA.** A fresh replay/owned pass for that
one new object would not automatically license reusing old downstream owners:
their recorded dependency-object maps would differ. No automatic new-object
or widened dependent-closure route belongs to this minimum plan.

Once all 41 dependencies are exact, run the four consumers in order:
OriginalParse, OriginalFloors, OriginalArithmetic, OriginalSourceFacts. Keep
their 17 public source declarations and complete actual owned inventories.
Record every new dependency normal stage in a separate rematerialization phase.
A zero dependency-normal counter may describe the later consumer phase only;
the aggregate must not hide the preceding rematerializations.

## Acceptance boundary

The new receipt can establish exact accepted-object reuse under a newly
observed current context and the actual new consumer results. It cannot claim
that old v7 passed, the five original envelopes were recovered, or no new
normal stage ran. Restoration/context capture grants no formal credit. Full
consumer acceptance still leaves the other13 cells, all14 aggregation and
geometric/analytic endpoints separate; `Q96_proved` and `P2_5_proved` remain
false. All execution claims must come from the actual new attempt's records.
