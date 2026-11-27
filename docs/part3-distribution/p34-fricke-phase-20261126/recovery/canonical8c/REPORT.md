# Canonical commit source-recovery delta

## Outcome

The complete 134-file addition delta of commit `8c745b0ae79dfc56415da20b2bfd6b8925270442` was inspected read-only. None of the three requested source bodies was recovered, and the inspected bodies and catalogs contained no direct target-interface declaration, import, or actionable target-recovery pointer.

This report materializes the previously completed GitHub inspection from retained results. Materialization performs no further source reads or scans.

## Fixed scope and identities

- Repository: `UyNewNas/goldbach-formalization`.
- Commit: `8c745b0ae79dfc56415da20b2bfd6b8925270442`.
- Parent: `9b16c5f0580a60a574e2611fb4b81778dd407244`.
- Tree: `adfbe283250c742e2ae284609a66e3c146b82d2e`.
- Commit message: `restore(p3.6): resume exact classical six-interface source closure [skip ci]`.
- Canonical evidence: [fixed GitHub commit](https://github.com/UyNewNas/goldbach-formalization/commit/8c745b0ae79dfc56415da20b2bfd6b8925270442).

| Inspected region | Files | Bytes |
| --- | ---: | ---: |
| Restored canonical Lean sources | 126 | 1,286,365 |
| Archived P2 raw-density Lean source | 1 | 4,179 |
| Restoration and provenance documents | 7 | 298,734 |
| Complete commit delta | 134 | 1,589,278 |

All 134 complete file bodies matched their Git blob SHA1 identities. The inspection authenticated 97 bodies reconstructed from complete added-file patches, 30 directly fetched Lean bodies, and seven directly fetched documents. The 126 canonical restored sources also matched the byte lengths and SHA256 values in the restoration catalog. The archived P2 source matched its separate recovery record. No patch reconstruction remained partial.

The selection catalog's 377 rows were inspected as metadata; this does not assert inspection of the 251 inherited source bodies.

## Target checks

| Authentic target | Bytes | SHA256 |
| --- | ---: | --- |
| `Part3OriginalMediumPhysicalE3Block.lean` | 6,566 | `1ed9fec9d526f866fff9a29f9d8d0fa96d63def2a8b1e4e7a42ad759a8989982` |
| `Part3OriginalMediumDoubleLambdaColorWindows.lean` | 7,882 | `e034925f0c0fe6b3fbc1e74966848dadd66591910e7a074403151dbbb3e66f7a` |
| `Part3ActualFrickeNonzeroFourier.lean` | 8,079 | `926ee1b5e78c1a714fcb91405b6c85cc0c8d09dd32ad61c9135c2f15359a27fc` |

The complete delta contained no target SHA256 match or target name/hash reference. Source bodies contained no `Fricke`, `DoubleLambda`, `PhysicalE3`, `E3Block`, `ColorWindow`, `MediumPhase`, or `MediumPhysical` mention. Five JSON documents were structurally inspected: 4,606 nodes and 3,427 strings, maximum string length 151 UTF-8 bytes, with no source-sized strings or encoded-payload fields/signatures.

The 13 added `Part3*` sources, totaling 140,628 bytes, concern attachment/complement support, proper-power chart counts, lambda-over-log corrections, and rough-slot character lifting. Each matched its Git blob and restoration-catalog SHA256. This inspection supplied no Lean compilation or formal acceptance credit.

## Source-catalog evidence

- [SOURCE_RESTORATION.json](https://github.com/UyNewNas/goldbach-formalization/blob/8c745b0ae79dfc56415da20b2bfd6b8925270442/docs/part3-distribution/continuation-20261126-p36/classical-six/SOURCE_RESTORATION.json): 33,708 bytes; Git blob `0c136841d20b0b933ca457f9c6974ef4e6e10774`; SHA256 `0149846715f2d7fcde4f6087e005164fd71bb90bb04531de5ce35a7775fa0873`.
- [SOURCE_SELECTION.json](https://github.com/UyNewNas/goldbach-formalization/blob/8c745b0ae79dfc56415da20b2bfd6b8925270442/docs/part3-distribution/continuation-20261126-p36/classical-six/SOURCE_SELECTION.json): 257,484 bytes; Git blob `ebee5b1d3b751d786224b345cf8e3a7c0eb9809b`; SHA256 `b7a3323839091dbd58fc0cd1de6aa2573f0a32b7da7644742df2facb764b2a45`.
- [Classical-six README](https://github.com/UyNewNas/goldbach-formalization/blob/8c745b0ae79dfc56415da20b2bfd6b8925270442/docs/part3-distribution/continuation-20261126-p36/classical-six/README.md) records the fixed P3.6 six-interface restoration scope and its formal-acceptance boundary.

The fixed donor is `e0cf45ba533922d9c06db118d7c169e083e33c5a`. These catalogs provide no new target-specific source pointer. The additional archived source is the unrelated P2 raw-density reserve, 4,179 bytes, SHA256 `2beab36383f2ea6ec68aee505978fcae27ca48960284e420109bca8af440fdd5`; its donor history was not traversed.

## Coverage boundary and retained receipt

Record the outcome as **canonical advertised commit delta fully inspected; no three-target recovery**. Preserve the `a875a48de2881e09d1bde698c004a1bd8fb02630e50122e37ff36b1d4edeac3e` bundle's integrity failure separately. Canonical commit inspection authenticates the added-file delta and does not authenticate or decode the original captured pack's entries. No global repository/history absence claim follows.

`final-receipt.json` is the exact retained, newline-free JSON serialization: **34,637 UTF-8 bytes**, SHA256 **`1753d20fcf5a00a711aebc01de698537c7c55c21eaf630d0dcaeb58001108254`**. It includes all 134 file identities, JSON traversal counts, exact scope, and boundaries. `verification.json` records the materialized receipt and report hashes.

No GitHub or worktree writes, pack decoding, compilation, or recovered-code execution occurred. The materialization writes only this staging directory.
