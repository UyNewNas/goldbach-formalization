# P3.4 exact original source recovery

The completed recovery scopes returned **zero exact matches** for the three requested source identities. This result applies to the verified archive regions, original bundle entries, and decoder selections in the [coverage manifest](coverage-manifest.json). The proof acceptance has its own verification record.

| Requested source | Bytes | SHA-256 |
|---|---:|---|
| `Part3OriginalMediumPhysicalE3Block.lean` | 6,566 | `1ed9fec9d526f866fff9a29f9d8d0fa96d63def2a8b1e4e7a42ad759a8989982` |
| `Part3OriginalMediumDoubleLambdaColorWindows.lean` | 7,882 | `e034925f0c0fe6b3fbc1e74966848dadd66591910e7a074403151dbbb3e66f7a` |
| `Part3ActualFrickeNonzeroFourier.lean` | 8,079 | `926ee1b5e78c1a714fcb91405b6c85cc0c8d09dd32ad61c9135c2f15359a27fc` |

## Completed coverage

- **Rescue TARs.** Verified EOF and header unions of 14,287 for priority and 8,775 for receipts. Priority's last pass closed 32 exact positions in 19 members. The two exact digest strings under `targets/missing` are DoubleLambda and Fricke metadata. Receipts ordinal 7,161 closed as a 120-record `PACKEDCHARS_FLAG` audit log after correcting the provisional PACK-prefix classification.
- **Block 24 and P2.9.** Block 24 covers the selected TAR and ZIP suffix, with 312 TAR headers and 315 payload receipts. The P2.9 follow-up closed two previously capped JSON members under the verified shared inner TAR identity. Their reconciliations retain the original ZIP prefix exclusion and the earlier scope of the other 126 P2.9 members.
- **Bootstrap and tail.** Five paths reduced to three outer identities. All 39 stored ZIP members reconciled to one standalone bootstrap identity, 36 prior block ZIPs, or two checked rescue JSON members. The bootstrap pass finished all 96 new selectors, with 208 transport-only parent members. Three prior exclusions retain original-target-only scope. The 96 compiled binary occurrences remain outside source decoding and produced no requested or related compiled-owner alert.
- **Twelve prior bundles.** The eleven complete local receipts cover 200 original pack-entry observations. The checkpoint covers 39 original entries. The same twelve size and SHA-256 identities close the corresponding duplicates inside the receipts TAR.
- **Five P2.1 manifests.** The exact selected decode completed ordinals 1, 3, 4, 13,847 and 13,859. It examined 360,982 JSON nodes, passed the other 13,854 headers as transport, and found zero exact sources, related metadata or boundaries. The 4,349,603,840-byte TAR reached verified EOF with SHA-256 `782ed338be356af00590c74dc94b64b91f199f147544c1306b930127762195c8`. The failed first adapter attempt stopped before payload processing because its metadata comparison treated equivalent tuples and lists differently. The retry used the pinned canonical comparison. The 32 MiB JSON-document and 4 GiB nested-expansion caps were unchanged. The outer transport had its own exact byte limit.
- **Two P2.1 control texts.** Ordinals 306 and 13,854 contributed 2,436 bytes of inert metadata. The context names five P2 roots and the known snapshot. The Python text documents Lake sidecar hash binding and supplies no checkpoint JSON schema. Neither text disclosed a target pointer.
- **One P2.1 checkpoint document.** The exact 67,075,207-byte JSON at ordinal 13,846 reached verified TAR EOF and completed 950,288 JSON nodes, with 609 catalog exclusions under their original scopes. It yielded zero exact targets, related strings, decoder boundaries or nested decoded bytes. The recorded document contains 731 source-and-data entries, 730 modules, 63,605 file entries, 9,441 actual-import sources and 526 guarded package compilations. The larger JSON allowance applied only to this SHA-256-pinned document. The generic 32 MiB document cap and the 768 MiB and eight-million-node guards were preserved.
- **Canonical advertised commit.** The independent check authenticated all 134 added file bodies in `8c745b0ae79dfc56415da20b2bfd6b8925270442` and found zero target bodies or related source mentions. Its 377-row selection catalog was checked as metadata. The result applies to the fixed commit delta and does not authenticate the captured bundle pack. See the [canonical inspection report](canonical8c/REPORT.md).

## Remaining evidence boundaries

- **Receipts ordinal 8,417.** The exact 60,000-byte transport, SHA-256 `a875a48de2881e09d1bde698c004a1bd8fb02630e50122e37ff36b1d4edeac3e`, has a v2 bundle header and a pack checksum mismatch. Its object coverage remains open. The retained bytes establish the mismatch without distinguishing truncation from corruption.
- **P2.1 remaining scope.** The fingerprint pass recorded 13,544 new identities and zero direct whole-member matches. The eight exact selected checks leave **13,536 other new identities unread**. The native snapshot keeps its earlier limited coverage and verified digest.

The manifest records scope separately for each target and retains the identity of every sealed source ZIP. It also records where an inherited decoder or historical single-target exclusion limits coverage.

## Evidence packages

| Package | Contents | SHA-256 |
|---|---|---|
| [Rescue evidence](recovery-rescue-evidence.zip) | First pass, scoped reconciliations, TAR resume and exact-field receipts, inventories, selectors, scanners | `405f18a0b06191c3cf36b144f89cd66976a61d6b9cfdf844c9bc6f3a59a00e60` |
| [Archive-probe evidence](recovery-archive-probe-evidence.zip) | Large alias identities, bootstrap and P2.1 fingerprint inventories, bootstrap selected-decoder evidence, reproducibility inputs | `6c2d90de04d2b0629715a86307b2a049691239714f3480117c6fc7cdc7bb966f` |
| [Local-bundle evidence](recovery-local-bundle-evidence.zip) | Prior original-entry receipts, checkpoint closure, exact audit-log and pack integrity evidence, scanners | `1b73ceb8a4bb12b1649b79be9b88759df89bff27c56f680035d2e046be9daa86` |
| [P2.1 follow-up evidence](recovery-p21-followup-evidence.zip) | Five manifest checks, two inert controls, exact checkpoint, and retained pre-payload adapter attempt | `138e0ff46b551d80dddef889f81c165911ba72a376c17241f975e7a15c4eca0d` |

Each package includes an `ARTIFACTS.json` entry manifest. The public result projections preserve the raw-body lengths, digests and input selectors, and omit inline Git transport bodies and header strings. The original sealed receipts remain intact in staging.

The manifest also binds the selected P2.1 runs, earlier adapter attempt, and separate canonical commit receipt. The earlier P2.1 controls plan remains a historical artifact and is superseded by the exact checkpoint receipt. The separate P2.1 follow-up package preserves the new receipts alongside the three unchanged original packages.
