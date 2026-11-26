# P2.5 fresh context after exact cache recovery

## Decision and scope

This is the root assistant's implementation choice within the user's existing
P2.5 continuation request. It records an environment-recovery refinement, not
a claim that the user approved these new documents. It changes no Lean proof,
manuscript obligation, historical receipt, v7 runner, or recovery runner.

The bounded local audit recovered four owned JSON files exactly. Five old
`COMPLETE_EXTERNAL_BEFORE.json` envelopes remain unavailable: consumer004/005
and field004/005/006. Their snapshot-specific clock values were not retained
in the inspected receipts/capsules. Preserve their original paths, sizes,
SHA256 values and missing status; never synthesize old timestamps or claim
that the unchanged v7 preflight passed. The evidence is
`docs/source-only/20261126-p2-5-cache-rematerialization/exact-history/EXTERNAL_SNAPSHOT_BLOCKERS.json`.

## Approaches considered

Restoring exact existing bytes is the first step and remains useful, but the
old v7 route still requires the five absent envelopes. Recompiling/replaying
all accepted work would duplicate available evidence and is outside this
recovery scope. The chosen refinement restores every available exact byte,
then creates one independently dated current-context receipt for attempt008.
Only actually missing accepted objects may be normally rematerialized; four
unfinished consumers retain their full original acceptance gates.

## Historical and current records

Run the published `restore_p3_cache.py --restore` with the reviewed supplemental
payload mappings. A truthful `PARTIAL_RESTORE_ONLY` result is expected while
the envelopes are absent. Do not use or change its blocked `--normal-rebuild`
route. The new driver consumes the exact original receipts and reconstructed
owned metadata. It allows archive incompleteness only for the five exact
path/size/SHA tuples in the audit; any other missing non-object input or any
changed historical input stops execution. The ten approved missing objects
remain pending until exact normal rematerialization; their source and historical
acceptance records must already be intact. If an original envelope becomes available,
validate and preserve it instead of applying the exception.

Keep accepted owners under their original publications and aggregate status,
including Decoded under the unsuccessful consumer005 aggregate. Require the
same source, object, original commands, complete stage logs, owned declarations,
inventory, dependency closure, and existing supplemental context validations.
The new receipt lists the five archive gaps separately from its freshly
observed current context; it never substitutes a new snapshot into an old path
or rewrites an old owner dictionary. Unread missing snapshots must not appear
as verified entries in the new `frozen_inputs` map.

## Current context invariants

The fresh root is
`/workspace/p25-q96-20261125/.lake/diagnostic/p25-cell00-four-consumers-attempt008`.
It must not exist. Bind the new runner/selection and every selected source to
the exact publication, retaining original owner publication pins separately.

Preserve the nine provider roots in their original order: Lean's `lib/lean`,
mathlib's build, then `plausible`, `LeanSearchClient`, `importGraph`,
`proofwidgets`, `aesop`, `Qq`, and `batteries` builds. Resolve each of the
5,312 expected external modules to exactly one regular object across these
providers; retain the exact 10,624 `.private`/`.server` companion set. Require
the same module names, paths, sizes and SHA256 values as the preserved upstream
snapshot and every relevant old `frozen_inputs` map, not just equal counts.
Reject provider shadowing and project modules outside the isolated project
library. Keep all 15,940 runtime pins, Lean 4.33.0-rc1, and mathlib commit
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

Capture real start/end times and the complete current resolved inventory into
new files. Freeze runtime, sources, metadata, all available historical bytes,
the 14 original witness files, and all accepted project objects. Revalidate
the frozen files and provider/companion resolution after every normal,
independent-kernel and owned-audit stage, plus final postflight. Add each
successful newly materialized object to that frozen set before using it.

## Work and stopping rules

Reuse the 31 available accepted objects without normal recompilation or
duplicate replay/audit. Topologically traverse the full 41-object dependency
graph, then select only the currently unresolved subset of the ten modules in
the unchanged recovery selection. Preserve exact
source/import/owner pins and strict flags:
`-t0 -j1 -M11264 -DwarningAsError=true -DmaxRecDepth=1000000 -DmaxHeartbeats=80000000`.
Each normal stage has a 600-second limit. Require its `.olean` SHA256 to equal
the original expected SHA and its expected project companion set to remain
empty before admitting it as a dependency. A mismatch stops the attempt;
do not relabel old acceptance or automatically enlarge the replay closure.

Then run OriginalParse, OriginalFloors, OriginalArithmetic and
OriginalSourceFacts in the established dependency order. Each must pass normal
Lean compilation, stock `leanchecker --verbose` independent kernel checking,
and the complete owned audit, including private/generated declarations,
serialized/environment/declaration inventory equality, exact project/external
closure, and the three approved private Parse helpers. Permit only
`propext`, `Classical.choice`, and `Quot.sound`; reject axiom declarations,
partial/unsafe declarations and missing or duplicate inventory records.
Preserve the existing `strict_commands`, `modern_owner`, `legacy_owner`,
`verify_reuse_validation` and `verify_container_objects` checks, including
the 296 private scoped-simp bindings and the exact 544-name Payload inventory.

Retain hardlink reuse, no overwrite/symlink escape or deletion, the 320-MiB
startup and 256-MiB per-stage reserves, and actual command/log/exit/timeout
records. New dependency normal stages are reported in a separate
rematerialization phase. The consumer phase may retain its truthful zero
dependency-compilation counter; the aggregate must report every new normal
stage and must not claim that no normal rematerialization ran. No new
formal credit is granted by restoration or context capture. `Q96_proved` and
`P2_5_proved` remain false; any consumer credit requires all original gates.

## Acceptance and handoff

An independent review must map every old v7/recovery check to a retained check
or the five explicitly listed archival-envelope exceptions. Publish the new
driver, selection, review and exact-source mappings before cloud execution.
The root assistant handles implementation, publication and execution. This
document and its plan do not represent an executed or accepted attempt008.
