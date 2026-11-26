# Attempt008 retained gates and bounded archive exception

Status: **selection prepared; v8 implementation and execution require their
own review**. This is the required comparison map for the new driver, not a
claim that unwritten or unreviewed code already preserves every check.

`FRESH_CONTEXT_SELECTION.json` is 10,740 bytes, SHA256
`1be717f81e2886e5291bdff7f129dbff8d75453656d6afa88c54cfd8168f01ca`.
It pins the unchanged v7 runner `4d0b9e19…`, recovery runner `d6d895b8…`,
recovery selection `cd0b812e…`, blocker audit `7ad7bda…`, and independently
reviewed design/plan/boundary files. Full hashes are in its `inputs` map.

## Exact input and deployment bindings

All `inputs` and `source_selection_inputs` paths are repository-relative.
The historical exception target paths and `prior_partial_restore.path` are
absolute P3 paths. The prior restore is bound to SHA256
`cf26553c585e5a5e4e2527095935af092d402381c47fc6595d9e5a08093cac17`;
its byte count was not supplied when preparing this selection and is not
invented. The driver must read that actual receipt and verify its status,
empty normal-stage list, exact runtime result, and unresolved requirement set.

The original consumer005 RESULT and the five exception-source RESULT files
are exact raw JSON restored by the existing bootstrap, not necessarily direct
Git tree entries. Their SHA/size remains mandatory. Their original published
capsule derivation is pinned by
`docs/source-only/20261126-p2-5-cache-rematerialization/RECEIPT_BOOTSTRAP_SELECTION.json`
(`845ebbb50bc889d05d6ecb81e41b44eb2e95ffafa187dc7c82bae4181170cf31`).
Do not replace this derivation with a blind `git show` requirement on the raw
RESULT paths. The new runner/selection and selected tracked code, metadata,
reports and source capsules must match their exact publication blobs.

The manifest references the existing 41-object graph, 722 historical paths,
14 witnesses, runtime configuration and original owner evidence rather than
copying them. Its source graph reference covers all 45 historical modules;
the approved Parse transport override is applied exactly as in v7. The old
package metadata list is retained, including its original repeated records.

## Check map

| Original check/source | Required attempt008 behavior | Permitted adaptation |
| --- | --- | --- |
| Publication checks; original source/receipt selections; exact override records | Bind v8 and its selection to the new publication; retain original owner publication/source/hash and every package/source import pin. | New runner/output/selection paths and a new publication identity only. Raw original RESULT uses its existing capsule derivation above. |
| Historical RESULT/owner status checks; failed Parse, consumer004 and field attempts | Keep every original dictionary, accepted/pending/failed owner, failed aggregate, command and full log identity. | A new receipt may cite these records; it cannot relabel or mutate them. |
| `strict_commands`, `modern_owner`, `legacy_owner` | Revalidate exact original normal/replay/audit commands, success status, logs, object/companion hashes, complete owned declarations and inventories. | No proof-gate exception. |
| `verify_reuse_validation`, `verify_container_objects` | Retain original supplemental complete-context checks and actual project-closure object identity for reused imports. | Available objects use exact hardlinks; newly rematerialized exact bytes become available only after SHA validation. |
| `read_audit`, `audited_imports`, `require_external` | Require the full serialized/environment/declaration name equality, uniqueness, exact project/external imports and safe declaration/axiom policy. | Bind new current-context descriptor only for new observations. |
| FieldSimp private scoped-simp audit; Payload expected names; Parse helper checks | Preserve all 296 private scoped-simp bindings, exact 544 Payload names and all three approved private Parse helper records. | None. These are not reduced to public-name spot checks. |
| Original complete external snapshot and each old `frozen_inputs` map | Retain all 15,940 runtime hash pins and the original upstream external record identities. Independently resolve all 5,312 external names across nine ordered providers; check exactly 10,624 companions and uniqueness. | Capture actual current start/end times in a new snapshot. Runtime hash counts alone do not replace resolution checks. |
| Physical reads/binds of five missing old envelope files | Validate each expected path/size/SHA tuple against its exact original RESULT; record absence separately. A present wrong file is a conflict. Validate a matching present file normally. | Only these five absent envelopes may remain archival gaps. No broad missing-file exception, fake timestamp, replacement old path, or verified-frozen entry for unread bytes. |
| Recovery final inventory/whitelist and exact historical `.olean` requirements | Retain all 41 source/object/import pins and completed P3 inventory; determine actual availability after restore. Traverse the entire 41-object DAG, then select the unresolved approved subset. | Normally rebuild at most the ten named modules in an explicit new phase; never recompile the 31 available objects. |
| Normal source/flags/timeout/object acceptance | Use exact sources, original strict flags, 600-second bound and exact prerequisites. Require the original output SHA and empty project companion set before admission or filling absent old object aliases. | New normal command paths and logs are reported as new work. Mismatch stops; no automatic larger replay closure. |
| v7 four-consumer loop | OriginalParse, OriginalFloors, OriginalArithmetic, OriginalSourceFacts each require normal, stock independent-kernel replay and complete owned audit in dependency order. | Attempt008 output paths; no omitted or reused fresh gate. |
| `context_check`, witness/postflight/space/link gates | Rehash all observed frozen inputs, verify provider/companion resolution after every stage and at finalization, retain 14 witness pins, no overwrite/symlink escape/deletion, 320-MiB startup and 256-MiB stage reserve. | Pending approved objects are explicitly pending until exact reconstruction; freeze each before admitting it. Unread envelopes remain separate. |
| Final assertions and reporting | Four accepted consumers require all original proof conditions. Preserve old accepted owners unchanged and report archive gaps, current context and new normal stages separately. Keep `Q96_proved` and `P2_5_proved` false. | Consumer-phase dependency normal count may stay zero; the aggregate must expose actual rematerialization stages. Never claim original v7 passed or the missing envelopes were recovered. |

Only the eighth row permits omission of physical historical bytes. It does
not relax source, object, owner, command, declaration, external membership or
current-environment identity. New current observations have their own receipt
and cannot serve as a fabricated historical envelope.

## Ten-module review order

The selection's `normal_order` is computed by traversing every object in the
complete graph (ascending root names, original import order) and then filtering
to the approved set. Dependencies through already available intermediate
objects are therefore retained. Execution filters again to actual missing
objects; finding an exact existing object removes work rather than adding it.

1. `ImbalancedChen.P2OriginalSaving16DecoderChars`
2. `ImbalancedChen.P2OriginalSaving16DecoderCompose`
3. `ImbalancedChen.P2OriginalSaving16OriginalInput`
4. `ImbalancedChen.P2OriginalSaving16FiniteCore`
5. `ImbalancedChen.P2Saving16CanonicalCell00Binding`
6. `ImbalancedChen.P2Saving16Cell00TypedPayload`
7. `ImbalancedChen.P2Saving16Cell00StoredFloors`
8. `ImbalancedChen.P2Saving16Cell00ScalarDecode`
9. `ImbalancedChen.P2Saving16Cell00PayloadBinding`
10. `ImbalancedChen.P2Saving16Cell00OriginalJson`

## Preparation verification and limits

Local preparation verified all nine `inputs` byte counts/hashes, all five
exception-source receipts and their original target descriptors, all five
v7 source-selection/override inputs, and every original package metadata
record. The pinned upstream archive members were checked, and all 15,936
external object/companion records agreed with the 15,940-entry historical
runtime subset. The complete graph contains 41 objects and no cycle; the
derived order contains exactly the ten approved modules. Four consumers and
14 original witness bindings remain referenced unchanged.

The prior partial restore is a runtime input pinned from the root's actual
P3 result; this preparation did not independently fetch it. No remote scan,
Lean run, old-test rerun, object regeneration, commit, or new proof-credit
claim was made while writing these two files. The final independent review
must inspect the actual v8 code and targeted new boundary tests against this
map before publication/execution.
