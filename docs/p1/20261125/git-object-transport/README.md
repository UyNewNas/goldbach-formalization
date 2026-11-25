# Published Git object transport after Batch15 fetch failures

The three initial Batch15 tasks stopped at `git fetch`, before retrieving or running the proof caller. The replacement operation made the exact already-published Git objects available to the cloud repository. It did not change authentication settings, the working tree, HEAD or refs, and it did not run Lean or an audit.

## Failed retrieval tasks

| Group | Task | Actual status | Elapsed seconds |
|---|---|---|---:|
| Wire five | `job_a3a42ff2b1dd40b583401edafa88f480` | failed, exit 1 | 0.49955034255981445 |
| Ordinary five | `job_f9d7db2673074fbfb706060f1beb1d4a` | failed, exit 1 | 0.4879930019378662 |
| Interiors four | `job_aa7cdaaddbb7477286d7108d3eaf5003` | failed, exit 1 | 0.5161991119384766 |

The supplied final summary classifies each failure as `BOOTSTRAP_GIT_FETCH_AUTH_FAILURE_BEFORE_DRIVER`: credentials were unavailable for the fetch. All three records have `driver_check_started`, `normal_started`, `audit_started` and `acceptance_claimed` set to false. Each complete, untruncated output is 833 bytes with SHA256 `6635c89af5d21ca5ddb0269c348ed2a0c8df14fcea48e933a2a6cdcf872523b1`. This report preserves the supplied diagnosis and output digest; it does not invent or quote an unavailable raw authentication error. [Evidence: `RECEIPTS.json`, `fetch_failures` and `fetch_failure_boundary`.]

The failure records show unchanged HEAD and porcelain-status digest. They do not contain a refs snapshot; the stronger HEAD/status/refs comparison below belongs to the import receipt.

## Exact published objects and import receipt

The transport manifest bounds the operation to base commit `65d14498902b16b2b89798ed7a82f3e031dce1dc` and published target commit `95b96cb5fe1a26322b7ecbdc66f15c2775035138`, target tree `384d4efd612176430b5719db3b07b97ce1203272`.

| Binding | Exact value |
|---|---|
| Import task | `job_05a1bc4d7dd04723a96d88f19b4fe4e2` |
| Recorded receipt status | `PUBLISHED_GIT_OBJECTS_VERIFIED` |
| Pack size | 203792 bytes, four parts of 60000, 60000, 60000 and 23792 bytes |
| Pack SHA256 | `1825ed8e0e71932efb175e534a6814fe2205249ca2d797804981b02b4370c24a` |
| Pack Git SHA1 | `d42bf9ee200113887d3349d724796d9ad36779bc` |
| Original import receipt SHA256 | `297fe894fe1c57ed66a086d078bed9f4f966a6c3810f820ec1715c6d48bd9e9d` |
| Caller SHA256 | `364bc26c294293afc06a05513de1f7a7114743dfe8d1969788cf26f22f951278` |
| Source manifest SHA256 | `13034d8b171c6e3a51faeff1ac337f386085cf947028f5998648d69ee415cf49` |

The recorded importer verifies all four parts, the assembled pack, the Git trailer, the target tree, the caller, the source manifest and the 14 exact module-source hashes. It invokes `git index-pack --stdin --strict` only if the target commit is absent. The receipt does not distinguish an actual import from the already-present branch. The submitted task record says `queued`; completion here is supported by the actual verification receipt, not by an invented final platform status. [Evidence: `RECEIPTS.json`, `transport_manifest` and `import_execution`.]

Before and after import, the recorded repository state is identical:

- HEAD: `10b89181754c78c0e77616677295ee2105de0bb6`.
- Porcelain SHA256: `477507c474369d6cca90fc3c3d1f36e859a70226c5c89e71e2147bf82e8e7789`.
- Refs SHA256: `841edd54ba32edfcc67a9cad8d7dd2ee4293851be2aa5542a61a69a7b620bdc3`.

This preserves the existing dirty worktree; it is not a claim that the worktree was clean. The recorded command contains no authentication changes, checkout/reset/ref updates or Lean/audit invocation. The receipt explicitly records `worktree_refs_or_Lean_sources_modified = false` and `normal_kernel_or_audit_repeated = false`.

## Evidence and scope

`RECEIPTS.json` records the exact paths, sizes and SHA256 values of the five supplied scratch evidence files, the three failure summaries, the compact transport manifest, and the parsed import receipt with the original receipt-byte digest. It retains all 14 published source hashes. No raw pack, base64 payload or executable command is embedded in this directory.

This local documentation review cross-checks those five records and the recorded command control flow. It performs no new cloud call, pack import, compilation or audit. Raw pack data was not re-read during this review. No unpublished Batch16 object is included. Git-object availability supplies no normal/kernel/full-owned acceptance claim, and the receipt explicitly leaves `whole_P1_complete = false`.
