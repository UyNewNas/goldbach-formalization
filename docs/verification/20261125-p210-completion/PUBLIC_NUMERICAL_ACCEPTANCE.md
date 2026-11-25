# P2.10 Winner9 public numerical acceptance record

> Subsequent final acceptance: [P2.10 terminal and seed-supplier completion](./PUBLIC_P210_FINAL_ACCEPTANCE.md).
> The numerical record below preserves its earlier checkpoint, including the then-pending final integration status.

**The public numerical certificate queue is accepted: all 37 proof-workflow jobs succeeded, and the unchanged original importer independently validated all 36 blocks and installed 598 modules. Full P2.10 integration remains pending.**

The record below distinguishes the original proof producer, the later transport-only producer, and the completed receiver validation. The GitHub transport job verified the original full collection ZIP. The receiver verified the smaller tail, combined its original files with the already held exact bootstrap, and successfully invoked the unchanged original importer once. Receiver validation completed at `2026-11-25T17:17:28.554Z`.

**Full P2.10 integration status: `terminal_integrated = false`.**

## Original proof producer and full collection

| Field | Value |
|---|---|
| Repository | `UyNewNas/goldbach-formalization` |
| Proof source commit | `94c7c507ab747cf4e05a4f19d8d4507cedfede38` |
| Workflow run | [45611402948](https://github.com/UyNewNas/goldbach-formalization/actions/runs/45611402948) |
| Final run attempt | `1` |
| Final run conclusion | `success` |
| All 36 numerical blocks and collect | **37/37 jobs succeeded: 36 numerical matrix jobs plus collect** |
| Collect job ID | `139335475949` |
| Collect job completed, UTC | `2026-11-25T16:07:48Z` |
| Workflow run updated, UTC | `2026-11-25T16:07:49Z` |
| Complete collection artifact ID | [15041690180](https://api.github.com/repos/UyNewNas/goldbach-formalization/actions/artifacts/15041690180) |
| Complete collection artifact name | `p210-collection-45611402948-1` |
| Collection ZIP bytes reported by GitHub | `635602594` |
| Collection ZIP SHA-256 reported by GitHub | `1965d3a92c336a4b1931835275e2602d14bef41bfd7cebcaeea3fa098ca597df` |
| Index SHA-256 reported by the public collector | `687c35f8ef018ad85e7cc68581dcadd98cd0acd22bd22f031dfd95966abfc70e` |
| Independent receiver acceptance | **`PUBLIC_COLLECTION_IMPORTED_EXACT`; completed `2026-11-25T17:17:28.554Z`** |

The original complete artifact is `p210-collection-45611402948-1`. A diagnostics, compiled-slot, progress-slot, or individual block artifact does not establish complete-batch acceptance. The successful transport job verified the full ZIP's metadata, size, digest, and exact 38 original members: `index.json`, `bootstrap.tar.gz`, and `block-08.zip` through `block-43.zip`.

The receiver downloaded and verified the smaller tail artifact below. It validated the preserved original index and block bytes, the exact reused bootstrap, and the original importer gates. Verification of the full ZIP container was performed by the public GitHub transport job; the receiver did not download or reconstruct that container.

The proof source remains the commit above after the report is published. A later documentation or workflow-trigger commit must not be substituted for the original proof producer.

## Public transport-only producer and tail artifact

| Field | Value |
|---|---|
| Transport source commit | `87c87492ab1e403ef2376188d2a6bfdb9f4520d1` |
| Transport workflow run | [45654126721](https://github.com/UyNewNas/goldbach-formalization/actions/runs/45654126721) |
| Transport run attempt | `1` |
| Transport CI conclusion | `success` |
| Tail artifact ID | [15041064001](https://api.github.com/repos/UyNewNas/goldbach-formalization/actions/artifacts/15041064001) |
| Tail artifact name | `p210-public-transport-45654126721-1` |
| Tail ZIP bytes | `221637364` |
| Tail ZIP SHA-256 | `7831443fff334f7fa675f443ac27dc4419335ef414012c789ed4fe5cee50352c` |
| Original files delivered | **37: the original index and 36 original block ZIPs** |
| Additional transport metadata | `tail.json` |
| Original bootstrap in this tail | **Omitted; its exact bytes are reused at the receiver** |
| Proof compilation / stock replay / new proof credit | **0 / 0 / 0** |

The transport job downloaded and verified the original 635602594-byte collection ZIP on GitHub, including a streaming check of the omitted bootstrap. It delivered the index and 36 block ZIPs byte for byte, with a manifest recording their source and transport provenance. The transport run neither recompiled nor replayed a numerical proof and is not a replacement proof producer.

The tail ZIP contains 37 unchanged original files plus `tail.json`. The receiver verified this distinct tail ZIP against its public size and digest, validated its manifest and original file bindings, and added the already held bootstrap to form the original importer's exact 38-file input. `tail.json` is transport evidence and is not an additional importer input.

## Completed receiver validation

**Status: `PUBLIC_COLLECTION_IMPORTED_EXACT`.** The original importer returned exit code **0** after validating all 36 numerical blocks. It installed **598 modules / 562 pages / 8978 rows**, preserving the original accepted receipts and the old 93 bootstrap records. The resulting collection contains **691 cached modules**.

| Validated result | Value |
|---|---|
| Completed, UTC | `2026-11-25T17:17:28.554Z` |
| Original index SHA-256 | `687c35f8ef018ad85e7cc68581dcadd98cd0acd22bd22f031dfd95966abfc70e` |
| Verified tail artifact | `15041064001`, `221637364` bytes |
| Verified tail ZIP SHA-256 | `7831443fff334f7fa675f443ac27dc4419335ef414012c789ed4fe5cee50352c` |
| Verified tail-manifest SHA-256 | `3829ac29f68b12ceef9edeaca6dc6cb46378c9f35a6ecbfe3f887d12dde8359e` |
| Original proof producer and transport producer | Confirmed separately against their fixed commits and runs above |
| Exact bootstrap reuse | Confirmed; all **93** prior dependency records remained unchanged |
| Original importer | **1 invocation; exit code 0** |
| Validated numerical blocks | **36**, blocks `08` through `43` |
| Installed / resulting cached modules | **598 / 691** |
| Actual origin counts: new C / reused C / reused accepted A / reused stock replay for new A | **592 / 6 / 1 / 0** |
| New accepted audits | **597** |
| Receiver version probe / proof compilation / stock replay | **1 / 0 / 0** |

The version probe is the original importer's required `Lean --version` invocation. The receiver performed no proof compilation or stock replay and ran no final integration module. Its successful validation preserves the original producer provenance; it adds no new proof credit.

The [machine-readable public summary](./PUBLIC_NUMERICAL_ACCEPTANCE.json) contains the corresponding minimal receiver result. Private environment receipts, cache records, filesystem paths, job identifiers, host details, and signed download URLs are not published here.

## Numerical queue and reuse accounting

The queue covers **562 numerical pages, 8978 rows, and 598 modules**:

- Numerical pages `0128` through `0689`: 562 modules.
- Numerical checks `08` through `43`: 36 modules.
- Original row ordinals `2048` through `11025`: 8978 rows.

| Gate | Prior completed work reused | New work in this batch | Total modules covered |
|---|---:|---:|---:|
| C: original strict compilation | **6** | **592** | **598** |
| A: accepted audit | **1 accepted A** | **597 new accepted audits** | **598** |

The six reused C results and the one reused accepted A belong to the 598-module queue. Their original producer records and receipts remain the provenance of that work. They are not counted as new compilation or new accepted audit work in this run.

**E covers 598 exported modules, confirmed by the successful original-importer validation.** This is a module-coverage count, not a count of exporter process invocations. `NumericalPage0224` reuses its prior accepted A, while the current run still executes E to export its evidence again. Thus 597 new accepted audits must not be described as only 597 E exports. Exporting, repackaging, or collecting evidence creates no additional proof credit.

The receiver confirmed the actual public index counts: `new_strict_compilations_in_run = 592`, `reused_strict_compilations = 6`, `reused_accepted_audits = 1`, and `reused_stock_replays_for_new_audits = 0`. The last value concerns reuse of stock replay for a new audit; it is separate from reuse of a fully accepted audit and adds nothing to the 598-module total.

The page/row totals describe coverage relative to the historical prefix. They do not mean that all 562 pages were recompiled in this run.

## Historical prefix, recorded separately

The existing prefix comprises **128 pages and 2048 rows**, pages `0000` through `0127` and row ordinals `0` through `2047`. It is outside the 598-module queue above and receives no new compile or replay credit from this batch.

The public prefix reference binds 135 historical accepted targets: those 128 pages plus `NumericalCheck00` through `NumericalCheck06`. `NumericalCheck07` is not silently included in that historical accepted set; its remaining preparation gates are tracked separately.

The numerical coverage relation is:

`2048 historical rows + 8978 accepted queue rows = 11026 rows`.

This coverage relation does not itself establish the final integral/seed theorem.

## Preserved verification boundary

The batch retains the original strict C, stock-kernel/owned-declaration A, and evidence-export E acceptance logic. Original source/object/dependency bindings, original receipt bytes, and the original producer identity of reused work remain part of the acceptance boundary.

The resumed producer is the `94c7c507...` source and run `45611402948`. Its original public bootstrap remains artifact **15013442313**, from run **45589950483**, attempt **1**, source **8bb6eac5aae11d217fb29324e1db7685954d30ac**. The bootstrap must not be relabelled as newly produced by the resumed run.

Published source pins:

- Resume plan SHA-256: `46e739a5a5ddfa3ad6b0dd4697f1bf95bb9cbb21ef84ce1c7f32e2cb33162978`.
- Original collection importer SHA-256: `b90f11e049080eff0ccc2d09e63f2d78ce88825791b5c4efdf6a92dc78be188c`.

This public record cites fixed source and public GitHub evidence, with a minimal summary of the completed receiver validation. It does not publish private environment records, filesystem layouts, host identifiers, credentials, or signed transport URLs.

## Remaining P2.10 integration obligations

**`terminal_integrated = false` remains explicit after acceptance of the numerical collection.** The remaining gates are:

| Remaining scope | Still required |
|---|---|
| Preparation modules: strict compilation | **3 C** |
| All six preparation modules: audit/evidence | **6 A/E** |
| Final integration modules | **3 modules, each requiring C/A/E** |

The final three modules are:

1. `ImbalancedChen.P2Winner9CompleteNumericalChecks`
2. `ImbalancedChen.P2Winner9CompleteSeedTerminal`
3. `ImbalancedChen.P4AOriginalFull87SeedRefinements`

Their pending status must not be replaced by a successful numerical queue or collection status. This report makes no final P2.10 terminal, integral, or seed-API acceptance claim.

## Public evidence references

- [Fixed proof source](https://github.com/UyNewNas/goldbach-formalization/tree/94c7c507ab747cf4e05a4f19d8d4507cedfede38)
- [Resumed numerical run](https://github.com/UyNewNas/goldbach-formalization/actions/runs/45611402948)
- [Published resume plan](https://github.com/UyNewNas/goldbach-formalization/blob/94c7c507ab747cf4e05a4f19d8d4507cedfede38/verification/part2/p210_resume_plan.json)
- [Original collection importer](https://github.com/UyNewNas/goldbach-formalization/blob/94c7c507ab747cf4e05a4f19d8d4507cedfede38/verification/part2/import_winner9_ci_artifacts.py)
- [Original numerical workflow](https://github.com/UyNewNas/goldbach-formalization/blob/94c7c507ab747cf4e05a4f19d8d4507cedfede38/.github/workflows/p210-winner9.yml)
- [Transport-only source](https://github.com/UyNewNas/goldbach-formalization/blob/87c87492ab1e403ef2376188d2a6bfdb9f4520d1/verification/part2/transport_winner9_collection.py)
- [Successful transport-only run](https://github.com/UyNewNas/goldbach-formalization/actions/runs/45654126721)
- [Original public bootstrap producer](https://github.com/UyNewNas/goldbach-formalization/actions/runs/45589950483)
- [Historical prefix reference](https://github.com/UyNewNas/goldbach-formalization/blob/94c7c507ab747cf4e05a4f19d8d4507cedfede38/docs/verification/20261125-p210-completion/PREFIX_REFERENCE.json)

## Completed trigger change and later report publication

Transport commit `87c87492ab1e403ef2376188d2a6bfdb9f4520d1` already removed these two push-trigger lines from the completed numerical workflow, retaining `workflow_dispatch`:

```diff
 on:
-  push:
-    branches: [codex-p210-complete-20261125]
   workflow_dispatch:
```

This removes the batch's automatic response to later pushes on the completion branch while retaining its existing manual entry. The original proof jobs and acceptance gates are preserved. The dispatch-only trigger remains in place; publishing this record requires no second removal or numerical rerun. Explicit manual reruns and the separate `pull_request` triggers in the general Lean and variable-envelope workflows remain distinct publication considerations.

The containing Git commit identifies this report's publication version; it is separate from the fixed original proof source commit above.
