# P2.5: concrete next-cell continuation after attempt008

## Result and evidence boundary

The next ready proof source is the existing Cell01 canonical character binding,
not a new parser or a new all-cell endpoint. Reuse the two unchanged sources
published at `52098e403ac4b28c72ec5958fd738ae93d785ac5`:

| Repository-relative source | SHA256 |
| --- | --- |
| `docs/source-only/20261125-p2-5-canonical-char-loader/ImbalancedChen/P2Saving16CanonicalCharLoader.lean` | `a61bf5fe0b370019f7b3115684dae4ba98ca947604adbd03d01d543528b134a1` |
| `docs/source-only/20261125-p2-5-canonical-char-loader/ImbalancedChen/P2Saving16CanonicalCell01Binding.lean` | `a18d3ae821babe0d06642aaece7abd73b368bf6196095810f669a5756d40f802` |

Their exact target is `String.ofList chars01 = originalText (1 : Fin 14)`.
The loader reduces the already imported canonical String literal and quotes its
characters. It reads no witness file, does no JSON parsing, and creates no typed
decoder. `goal.refl (check := false)` still requires ordinary kernel checking
and independent replay. Neither new module has a located acceptance receipt.

The existing local `cell01-canonical/run_canonical_cell01_v2.py` is complete
dormant preparation, SHA `9dfa73a333775b72d3f03e9902fe927d793b88e76b639eb17c0319bcb1f0b99e`.
It is currently untracked and expects successful v6 attempt006, so it cannot be
activated by replacing a result hash alone. Preserve it; prepare a separately
reviewed v3 adapter after the actual attempt008 result is accepted.

This review reuses `NEXT_CELL_REUSE.json` and `MANUSCRIPT_REUSE_AUDIT.json`.
The relevant Git path changes from their prior review checkpoint `b667409e…`
to inspected HEAD `929fd05e4c8e57243e1517f6396975b0f03bbef9` contain no new
Cell01-or-later concrete parser/decoder/arithmetic source or replacement total
proof. This is a bounded incremental result, not a global absence claim.
`EXISTING_IMPLEMENTATIONS.json` records exact source blobs/commits and all input
sizes/hashes. No remote inventory, old test, generator or Lean run was repeated.

## 1. Exact v2-to-v3 adaptation, conditional on actual v8 success

Proposed new files are `cell01-canonical/run_canonical_cell01_v3.py`,
`RUNNER_MANIFEST_V3.json`, a delta against the pinned v2 bytes, and targeted
adapter tests. No Cell01 Lean source needs changing for this step.

| Existing entry/check | Required concrete adaptation |
| --- | --- |
| `CELL00_PUBLICATION`, `PREVIOUS_COMMIT`, `CELL00_RESULT`, `CELL00_RESULT_SHA256`, `CELL00_RUNNER_SHA256`, readiness flag | Pin the actual published v8 commit, `p25-cell00-four-consumers-attempt008/RESULT.json`, actual receipt hash and exact executed v8 runner hash. Keep readiness false until its full artifacts have been reviewed. Never fill a predicted receipt hash. |
| v2 `CELL00_DRIVER` and main's `import_exact` | Separate executed-runner provenance from static receipt validators. Bind v8 as the executed source, but retain the exact v6 helper source/`validate_failed_consumer`, `validate_failed_parse`, `validate_parse_helpers` if those functions are reused unchanged. Importing those helpers does not require claiming v6 execution succeeded. |
| `ready_manifest` and manifest provenance | Pin the actual v8 source/selection, new Cell01 v3 runner, observed result and reviewed artifact hashes. Preserve source manifest `fed4f00b…`, the two source hashes, OriginalInput's b80 provenance and canonical00's original failed-aggregate history. |
| `validate_workflow_receipts` schema/counters | Require actual `p25-cell00-four-consumers-fresh-context-strict-v8`, successful four-owner status, all 12 passed stages, all 41 exact dependencies and the original accepted Decoded dictionary. Replace the aggregate zero-normal assumption with exact `normal_rematerialization_stages`/receipt verification against the original ten-module whitelist and object hashes. Require `consumer_phase_dependency_modules_compiled`, accepted replay/audit reruns and Decoded reruns to be empty. |
| New historical/context provenance | Freeze actual rematerialization receipt, `fresh_context_before`, `fresh_context_after`, v8 selection and exact archive-gap tuples. Preserve `old_v7_preflight_passed = false`, `old_recovery_complete = false`, `old_snapshots_synthesized = false`. Do not require unavailable old envelopes or count them as read. |
| `qualify_external_context` / `recheck_external_context` | The inspected v8 candidate still writes an actual `complete_external_before` with the existing reuse-v1 schema and upstream `b94ab99b…` snapshot. Reuse these predicates on that new attempt008 descriptor; also verify the fresh before/after context descriptors and their exact common entries. Nine ordered providers, unique resolution, 5,312 modules, 10,624 companions and all runtime pins remain mandatory. Final published v8 receipt is authoritative if implementation changes. |
| `validate_dependencies`: global `RECORDS` access | `.lake/p2-private/records.json` is absent from the 722 recovery requirements and must not be presumed restored. The exact original outer receipt `cb11eb09…` contains the complete `compile_records[OriginalInput]`, equal to its `records_after_audit[OriginalInput]` (locally checked). Consume that unchanged original dictionary instead; preserve all cache-schema, command, closure-signature, dependency, toolchain, source/object, replay/audit and artifact checks. Do not manufacture or overwrite a global records file. |
| Historical fourteen-file snapshot equality | v2 compares full historical/current snapshots including device/inode/mtime/ctime. Preserve the old receipt's internal before/after read-window equalities, compare current files to the same 14 path/size/SHA pins, and record/check current physical identities throughout the new run. Do not substitute new inode metadata into historical evidence. If all old metadata still matches, retain that stronger observed equality too. |
| Publication advance and freeze sets | Keep exact publication source bindings, actual old-owner provenance, source/import closure and frozen artifacts. Include new context/rematerialization evidence; remove only the requirement to read the unneeded global cache index. No failed or pending owner becomes accepted. |

OriginalInput remains source SHA `792a5adf…`, object SHA `72488821…`,
93,650,960 bytes, owned receipt `8cca39ad…`, closure `81c89a9f…`, original
publication `448e03d6ce02fd7d3b8d008defcd5ffffc4fc426`. Successful v8 must first
have reconstructed that missing object to precisely this old SHA. Cell01 never
normally recompiles it. The complete original input/read-window provenance
remains supplied by outer receipt `cb11eb092d12e3e1f08eb9dccad4ecbe53311f456babe6c0ccabe72b93c3fa65`.

## 2. Smallest execution and acceptance scope

1. Review the actual successful v8 result and complete owner/context artifacts.
   Validate the adapter's changed schema/counter/context/cache-index predicates
   with targeted fixtures; do not rerun settled old suites or accepted gates.
2. Publish the exact v3 adapter/manifest and unchanged two-source package.
   Its existing positional invocation can remain
   `python -B /workspace/p25-cell01-canonical-v3-20261126.py <cell01-publication>`;
   this is a planned filename, not an already available command.
3. Use fresh `.lake/diagnostic/p25-cell01-canonical-attempt001` only if absent.
   Stage accepted OriginalInput; run loader normal, independent kernel replay,
   complete owned audit. Admit the actual accepted loader object into the
   binding stage; run binding normal, replay and complete owned audit.
4. Require unchanged source/input/context snapshots around all six gates.
   Audit all generated/private elaborator declarations; predict no owned count.
   Acceptance proves only the exact character equality, with project closure
   `{OriginalInput, CanonicalCharLoader, CanonicalCell01Binding}`. Cell00 is a
   workflow prerequisite, not a logical import. Parse/decode, finite arithmetic,
   Q96 and P2.5 remain false.

The complete frozen provider inventory still has 5,312 modules; a canonical
owner's actually imported external subset is checked as in v2 and is not
artificially required to contain all 5,312. Its actual project closure must
equal the precise two-module or three-module stage graph.

Retain v2's 180-second stage limit and strict flags
`-t0 -j1 -M11264 -DwarningAsError=true -DmaxRecDepth=50000 -DmaxHeartbeats=40000000`;
the binding source keeps local `maxRecDepth 1000000`. Its existing disk policy
reserves 1 GiB initially and 256 MiB per gate, and stages two exact OriginalInput
copies totaling 187,301,920 bytes. Check this explicitly after v8; do not infer
capacity from its success. If it is the sole blocker, a separately recorded
reuse of v7's already-reviewed exact hardlink helper avoids the duplicate
allocation while retaining all content/postflight checks. No cleanup or silent
resource-policy change belongs in the pin-only adaptation.

## 3. Next unimplemented concrete source: Cell01 parser, then typed decoder

No accepted or concrete Cell01 Parse/Floors/Arithmetic/SourceFacts package was
found in the reused inventory or subsequent relevant Git additions. Reuse the
existing general structures, not Cell00's data-specific conclusions.

**Exact input.** Cell01 is canonical index/source ID 1; witness size 344,873
bytes and SHA `d7215c408203fd149155ec34af91c0d3af45a49d4dc64e23b508917d176a5c2f`.
Use the already verified original artifact when available locally; this task
did not transfer or regenerate it. Its concrete token inventory, exact fuel,
tail and distinct scalar counts are not yet measured and must not be copied
from Cell00.

**Parser source.** Adapt the existing `cell00-segmented/generate_direct.py`
(commit `4b7aaff36b55a7c7098fb6abf0e8f51a47efa948`) using its unchanged donor
`Node/Field/RawPlanner/quote_char/quote_list/lean_node` implementations. Replace
only the explicit input pin/index, namespace, candidate AST, measured fuel and
trailing characters. Preserve the original reader, every field/order/value and
whitespace. The next new theorem is
`SourceJson.value fuel01 chars01 = .ok (rootValue01, tail01)` plus the real
fuel bound and whitespace tail, followed by existing
`SourceJson.parse_of_value_of_ofList_eq`. Kernel-check quotation equality; the
host planner supplies no correctness credit. Never reuse Cell00's fuel 371,
53,303-character endpoint or assumed CRLF without inspecting Cell01.

**Typed payload/decode.** Adapt `cell00-decoded/generate_typed_payload.py`
(commit `55ef1e4be9d8295ab5ced1335f1210f52a7031b2`), keeping all 17 root fields,
ten simplex fields, original rational spellings, ordering, raw face ledger and
active8 data. Recompute its Cell00-specific assertions (eight rows, 211 distinct
rationals/428 occurrences and 16 distinct integers) from the exact new input.
Reuse accepted generic DecoderChars/DecoderCompose/FuelBridge objects and the
existing symbolic field/simplex composition pattern. The concrete closed scalar,
field and simplex facts are new; generic helpers and Cell00 certificates are not.
Do not duplicate the previously failed monolithic closed record proof.

**Arithmetic and transports.** After new `decodeCell rootValue01 = .ok payload01`,
reuse the existing thin Parse/Floors/Arithmetic/SourceFacts construction at index
1. Prove actual determinant, gap, ten weighted means, Jensen and individual
Q96 floor facts for each Cell01 row before the arithmetic transport. Existing
stored `jensenFloor` fields alone do not establish the geometric floor sum.
The Cell00 examples are unchanged complete templates; their theorems cannot
certify the other cells by renaming. Add finite geometry/pulling only through
the already prepared generic/source-bound owners and actual new cell data.

## 4. Certificate scale, without claiming runtime feasibility

Counts below are copied from the existing independent host report, not new
numerics or Lean acceptance. Each row needs one 8-by-8 determinant calculation,
ten means, one separate Q96 floor and all 11 `simplexValid` conjuncts. Source
membership additionally needs the actual unique vertices against all 96 rows;
vertex/facet/face-ledger sizes must come from that cell's original data.

| Canonical index | Source ID | Original bytes | Simplices / separate floors | Conjunct instances at 11 per row |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 1 | 344,873 | 81 | 891 |
| 2 | 2 | 1,587,277 | 596 | 6,556 |
| 3 | 3 | 125,188 | 21 | 231 |
| 4 | 4 | 1,336,943 | 456 | 5,016 |
| 5 | 5 | 3,906,248 | 1,697 | 18,667 |
| 6 | 6 | 465,744 | 144 | 1,584 |
| 7 | 8 | 3,487,549 | 1,295 | 14,245 |
| 8 | 9 | 28,398,290 | 12,089 | 132,979 |
| 9 | 10 | 9,585,502 | 4,393 | 48,323 |
| 10 | 11 | 8,070,370 | 3,719 | 40,909 |
| 11 | 12 | 16,140,239 | 6,713 | 73,843 |
| 12 | 13 | 16,354,400 | 7,175 | 78,925 |
| 13 | 14 | 3,652,259 | 1,354 | 14,894 |

The remaining 13 cells contain 39,733 rows. Cell01 has 810 means, 81 floors
and 729 vertex-index occurrences; these are obligation counts, not independent
theorem counts. Literal one-row-per-owner reuse would entail 81 simplex-decode
owners and 81 arithmetic owners, hence 486 normal/replay/audit stages plus
field/scalar/aggregate/transport owners. This is a planning scale, not a required
partition or a runtime prediction. Use measured Cell01 results to choose bounded
batches; do not generate all 13 cells in advance or repeat accepted base owners.

## 5. Existing total/integral route and manuscript classification

The frozen manuscript is `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`. The locally
rechecked `eq:current-eighth-saving`, `sv:eighth-range`/`sv:eighth-density`
require the original density
`4*(M-R6)/((R6-S8)*(M-S8)*product(t_i))`, ancestor/square tests and disjoint
same-stage interiors. `num:upper-table` gives `1543640141/10^14` for G16.
The earlier precise certificate audit supplies the 14 IDs excluding old ID 7,
39,741 simplices, Jacobian 1, `abs(det)/8!`, and separate floors summing to
`1222997719565324892497827/2^96`. Do not insert a Chen quarter/order factorial
or add the separately booked old cell 7.

| Existing source and exact path commit | Available declaration; actual boundary |
| --- | --- |
| `P2OriginalSaving16FiniteArchive.lean`, `4b7aaff36b55a7c7098fb6abf0e8f51a47efa948` | `original_parse_success`, `original_simplex_operations`, `original_q96_aggregate`, `original_counts` already written; closed all-cell reductions remain unaccepted. |
| `P2OriginalSaving16OriginalArchive.lean` / `P2OriginalSaving16JensenFloor.lean`, `9838fca5e517bcf4d90e1dc18f1668984bd4768a` | Original 96-row/facet checks, `original_q96_aggregate_real`, actual simplex Jensen/Q96 interface; retain their real dependencies. |
| `P2OriginalSaving16SimplexBinding.lean`, `3b6582873ef894360be668dc4f0f1f4f05a68c83` | `original_row_q96` and `historical_endpoint_le_sum_simplex_integrals` already fill the same original geometry; no new total-sum theorem needed. |
| `P2OriginalSaving16PullingOwnership.lean` / `P2OriginalSaving16OwnedIntegral.lean`, same `3b658287…` | Original face/pulling checks feed separating-wall/null-overlap proofs and `historical_endpoint_le_source_integral`; the positive inner-union route needs no exhaustive whole-cell triangulation. |
| Existing `P2OriginalSaving16DisplayBound.lean` source-only package, `58b652df0144a0726818775e61d188c23ae40072` | Two completed source proofs compare the Q96 rational and transport the integral endpoint to the manuscript display. This is not accepted until its dependencies and gates pass. |

Canonical equality, parser/decoder composition and rational certificates are
Lean expression/resource/finite-verification work, not an identified substantive
proof gap. The sum/integral/display deductions have existing explicit Lean source;
do not write them again or treat their unaccepted declarations as usable proof.
The same-policy quantitative PP supplier is a separate still-open formal input
in the previous reviewed set; Cell01 or all-cell certificate acceptance does not
supply it. No manuscript contradiction was established by this bounded audit.

## Handoff

The next concrete deliverable is a reviewed v3 Cell01 adapter, kept dormant
until bound to an actual successful v8 result, followed by six new canonical
checks. Once the exact Cell01 input is available, its parser/typed candidate
package may be prepared offline in parallel; execution follows the qualified
canonical equality and observed resource limits. This plan changes no repository
source, v8 driver, selection or cloud state.
