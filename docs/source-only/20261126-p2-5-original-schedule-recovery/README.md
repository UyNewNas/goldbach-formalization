# Original schedule: recovery of existing source providers

**Source recovery only. No production install, proof change, Lean execution,
cloud task, or acceptance credit.** Seven existing source-only files are copied
byte-for-byte from the recorded checkpoint. The earlier lightweight extraction
package and its historical selection reports remain unchanged.

## Provenance

Repository: `UyNewNas/goldbach-formalization`.

Checkpoint: `9b1b19b44e756777738a8b37ef677429c60eb5e3`.

Tree: `b8853b75b3cb5e616708a6f0d4968480d9e47a3a`.

The checkpoint was already named by the existing fourteen-family
`SCHEDULE_SOURCE_MAP.json`. Its two direct caller sources,
`P2Saving16ActualUpperCornerCap` and
`P2Saving16NegativeCoefficientComparison`, have exactly the same bytes as the
versions in the frozen lightweight graph. The named `All96ClosedBox` source
also matches the previously recorded commit, path, blob, byte count, and SHA.

`SOURCE_PROVENANCE.json` is the per-source manifest. Each row records the
original commit/tree/path/blob, SHA-256, byte count, source status markers,
direct imports, caller that required it, selected recovery path, and source
declaration list. The original comments label every recovered file
`SOURCE_ONLY / UNCOMPILED / UNEVALUATED`. This package supplies no new acceptance
evidence for any owner.

| Recovered owner | Required by | Original directory under `docs/source-only/` |
| --- | --- | --- |
| `P2Saving16ActionGatesClosedBox` | `P2Saving16ActualUpperCornerCap` | `20261120-p2-saving16-action-gates` |
| `P2Saving16OriginalPhysicalEightSource` | `P2Saving16NegativeCoefficientComparison` | `20261120-p2-saving16-original-physical-eight` |
| `P2Saving16All96ClosedBox` | `P2Saving16ActionGatesClosedBox` | `20261120-p2-saving16-all96-closed-box` |
| `P2Saving16ThreeCapRows` | `P2Saving16All96ClosedBox` | `20261120-p2-saving16-three-cap-rows` |
| `P2Saving16FourHistoryRows` | `P2Saving16ThreeCapRows` | `20261120-p2-saving16-four-history-rows` |
| `P2Saving16SevenOrderRowsCarrier` | `P2Saving16FourHistoryRows` | `20261120-p2-saving16-seven-order-rows` |
| `P2Saving16FourthRowSignedProduct` | `P2Saving16SevenOrderRowsCarrier` | `20261120-p2-saving16-fourth-row` |

Each original filename is its owner name followed by `.lean`. The final
`FourthRowSignedProduct` imports `ThirdRowFourthParent` and
`ActualCompilerDifference`, both already supplied by the frozen selection.
The other imports of `OriginalPhysicalEightSource` are also already supplied.
The recursive search stopped there; no module or proof was reimplemented.

## Combined selection view

`COMBINED_SELECTION.json` pins the frozen lightweight
`DEPENDENCY_REDUCTION.json` and adds exactly these seven providers. It replaces
no existing provider or version. The base has 1,510 defined provider records;
the combined view has 1,517.

| Existing root | Project module nodes | Missing providers | Import cycles |
| --- | ---: | ---: | ---: |
| `P4AOriginalR17PaidIntegral` | 1,487 | 0 | 0 |
| `P2Saving16R17StrictFourteenCorners` | 1,517 | 0 | 0 |

The former all14 report counted 1,512 nodes, including the two unresolved
owner names. Resolving those two names exposes five additional nodes; all
seven needed source files are now present in this recovery package. The
ordinary root's graph is unchanged.

These counts describe the exact declared import graph. Only the seven added
files are materialized here. The historical base sources, their already
recorded transforms, the seven existing negative finite postimages, and the
two existing IntegralDefinitions deduplication hunks still need their proper
selection before a complete installation. No production source was installed
by this recovery.

The recovered owners retain every formula, hypothesis, full carrier, original
policy, sign-selected beta test, and same-Q identity. The existing actual
distribution-error estimate obligation is unchanged: the same compiled Q/rho
and common beta/k/N0 schedule still need the quantitative error bound described
by the frozen lightweight package. Recovery is not a proof of that estimate or
of an all14 integral, finite cell, Q96, or P2.5 endpoint.

## Verification and reuse

`verify_recovery.py` reads only the exact recorded Git objects and the pinned
existing selection files. It checks Git blob identities, SHA-256 and byte
counts, namespaces/status markers, direct caller edges, the two selected
caller identities, and both import closures. It verifies all files in the
frozen lightweight package before and after the operation. Its `--write` mode
writes only this package and refuses to replace different existing bytes.

To check the frozen recovery without installing sources or invoking Lean:

```sh
python3 docs/source-only/20261126-p2-5-original-schedule-recovery/verify_recovery.py
```

Future acceptance must compile each selected recovered owner, replay its
kernel object, and audit its complete serialized/environment owned inventory,
including generated and private declarations. Source declaration lists here
are provenance metadata, not an owned-inventory substitute. All acceptance and
finite-credit flags remain false.
