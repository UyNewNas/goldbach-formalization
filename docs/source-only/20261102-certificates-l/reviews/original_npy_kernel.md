# Independent source review: L/original_npy_kernel

**SOURCE_REVIEW_PASS**, strictly for source construction and proof-body wiring. Reviewer `/root/h_review_upper`, retained assignment `gpt-6-astra / xhigh`; runtime model metadata was not queried. The author supplies a concrete independent-byte construction and a closed full-parse proof candidate. All three decisive guards and the elaborator application remain **UNEVALUATED**. Full original authentication, elaboration, kernel acceptance and resource feasibility remain **OPEN**. Preserve `source_construction_complete=true`, `local_step_complete=false`, `task_complete=false`, `compiled=false`, `kernel_verified=false`, `formal_credit=0`, `ready_to_install=false`.

## Frozen packet and independent input

| Artifact | Exact raw SHA256 |
| --- | --- |
| `P1HistoricalFifthOriginalByteLiteral.lean` | `500830a7da65ba0b0288cc33b3c956575ac1c9ea98b4f690bb957e1d499717e2` |
| `P1HistoricalFifthOriginalNpyKernel.lean` | `c7f6baf013b4e73ac1bc8e33a2fb6fbb3fa905f9098ec0a328be0477a35c77fd` |
| `REGISTRY.json` | `438d47b3787e9718a22a4fe2294d72318d46a4006da0a3414333454503a08478` |
| `REPORT.md` | `71f5ce46a341747c875c7ae47c1c8ddad48649b7d40f397754ead9e7b3ecc746` |
| Original and retained `cells.npy`, each 23410768 bytes | `d6c59992f3f89d7ff30ad5b02e3f95f0d15205ed3446961862c0f126298f17b7` |
| J association source | `2f5fe968467a54a187ba04690b1abf1eca9adb99eb4ac412fdf91aab230384ea` |
| Actual 143-block hub | `4590eb2a2bbca87b2ae373401cfa408172e93fd87c51623ef9eed114130fc274` |
| E original-data authority registry | `cc96a607f6acd48880ded6b56d815373d1b24104794614d69175711d3f0fe827` |
| F key partition | `a70ff1b0160d74840feff040241a822be20f793053c53785d541a44802e33e94` |
| F base geometry | `9a71bdc1dec78b45e5d437f22bfb88fe2557c29e84d4ae5e8ffff32719878885` |

The two new files contain 323 lines and 24 public theorem bodies: five in the literal module, nineteen in the consumer, including three closed historical guards. These are source counts, not verified-theorem counts. The companion JSON records every exact source/import/reference/API pin, all 143 block pins, and both binary paths. Independently checked 183 metadata pins and four direct-import pins: no mismatch. Each block's path, module, hash, interval and installation target also matches E's authority manifest. No block data decision was executed.

The original fixture is the existing `docs/source-only/20261028-paper-first/cohort04/upper/pure-data/d6c59992f3f89d7ff30ad5b02e3f95f0d15205ed3446961862c0f126298f17b7/cells.npy`; the retained copy is `docs/source-only/20261102-certificates-l/original_npy_kernel/provenance/original-fifth/cells.npy`. This review performed only whole-file hashing and bytecount inspection. The author's first-128-byte hash is reported predecessor metadata; it was not recomputed here. No header or payload bytes were parsed in this review.

## Source findings

The original manuscript, exporter and existing parser agree on ten signed64 fields `[n,l1,l2,l3,l4,l5,mask,vertex_gap_sum,A,B]`. Original `c=49044063/25000000` and `K=8452171/1250000` are preserved. The new literal reader takes only a file path; it does not read typed rows, invoke a decoder or checker, or construct a proof. Its output is a transparent constructor tree with natural literals, including the normal `OfNat` frontend applications used by the pinned `mkNatLit` API. Filesystem IO is an external data boundary, with no proof authority.

The reversed-index Horner loop packs each successive slice in little-endian base 256. Retaining the slice count preserves high zero bytes. Ascending slices and adjacent left/right tree pairing preserve order, including an unmatched final subtree. The expansion prepends the left subtree before the right. Generic structural proofs give exact represented length and byte bounds; `block_roundtrip` uses the existing arbitrary-byte inverse `encodeNatLE_unsignedLE`. This algebraic inverse does not assert correctness of filesystem IO or execute the elaborator. The indexing and order were inspected mathematically from source only.

The pinned Lean APIs support the intended path resolution: `getFileName` comes from the consuming elaboration context; `FilePath.withFileName` joins the argument beneath that file's parent. The current source-relative fixture exists. Installation must retain `ImbalancedChen/provenance/original-fifth/cells.npy` alongside the main module and install the exact source-only dependencies. Copying only the two new Lean files is insufficient. Compiler/API acceptance is still untested.

The closed `original_literal_length` guard checks represented length independently of the reader's early IO size diagnostic. `original_header` checks the exact authentic 128-byte header. The existing `decodeFrame` checks NPY1.0 magic/version, header length118, `<i8`, C order False, shape `(292633,10)`, padding/newline, and exact payload length. Its row parser consumes complete 80-byte rows and ten signed64 words, with no partial or trailing payload accepted.

The decisive `original_complete_ordered_columns` has an actual closed `by decide` body. `SameColumns` quantifies over every `Fin 10` column using integer equality, and `wireOfColumns_wireColumns` gives exact row equality, including lower-key functions and opaque fields. `OrderedColumns` compares pairs sequentially and accepts only simultaneous list termination; `ParseColumns` rejects parser failure. Ordinary proof bodies convert this predicate to the exact full target:

```lean
decodeFrame originalBytes = some Data.P1HistoricalFifthSavedTableData.rows.toList
```

There is no header, success, association, desired result or checker-flag hypothesis in this declaration. The target uses the genuine 143-block append hub in original order, with its existing 292633-row shape source. No sort, deduplication, mask filter, zero-row deletion or aggregate replacement occurs. This supplies a substantive full-target source candidate beyond J's conditional criterion; it does not establish that the unexecuted guard is true or feasible.

J's actual parser-to-window implication supplies `128+80*i.val+8*column.val`, signed64 fields, exact eight-byte reconstruction, arbitrary block splits and zero-based mask slots. `encodeFrame typedRows = originalBytes` is a consequence of parsing, not the construction of the supposedly original input. F's existing `actual_typed_keys_nodup` and `archiveRow_baseGeometry` are transported after exact parse equality. Their finite proofs remain inherited, unevaluated and unverified. The parsed-output premises in those transport corollaries do not become a hidden assumption of the full original parse theorem.

No mandatory source correction, new axiom, `sorry`/`admit`, `unsafe`, `native_decide`, altered source family or assumed analytic endpoint was found in the new files.

## Remaining obligations and precise pass boundary

The packet supplies the independent-byte object mechanism, generic byte representation arguments, closed exact header/length/full-parse proof bodies, and their J/F consumers. It eliminates the need for a future author to supply these source bodies or assume `OriginalFieldAssociation originalBytes`. **No historical data obligation has been discharged by execution or kernel checking.**

The three guards are `original_literal_length`, `original_header`, and `original_complete_ordered_columns`; all remain UNEVALUATED. The include-bytes term has not been generated, elaborated or inspected as an actual output. Kernel reduction over 23410768 bytes and 292633 ordered ten-field comparisons may fail or exhaust resources; large recursion limits and unlimited heartbeats provide no feasibility guarantee. Exact dependency installation and the inherited typed range/key/base guards remain unresolved verification work.

If the kernel accepts the eventual term, it proves statements about that transparent literal. It does not prove a filesystem SHA256 or the external file-to-literal provenance. Current matching raw hashes and static IO inspection document that separate boundary. No authenticity claim is made solely from the hash equality, source criterion, or anticipated guard success.

Original physical/current-parent/history/owner licences, analytic integrals, signed compiler debts, both reserves, currentK/all22/hdensity and the main Goldbach1+1.748 target remain OPEN. Base geometry and exact parsing do not supply those estimates.

Only these two review files were written. Author sources, J/K reviews, production and earlier batches were untouched. No Lean/lake/compiler/build/CI, elaborator application, `decide`, finite replay, payload parsing, literal generation, Git operation, quota call or subagent was used.
