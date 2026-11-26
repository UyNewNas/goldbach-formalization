# Existing two-long Brun support: exact shared-source extraction

**SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.**

`Part3TwoLongBrunSupport.lean` owns the six existing generic declarations in
the unchanged namespace
`ImbalancedChen.Part3.TwoLongActualLowerBrunMoment`:

- `brunSupport`
- `brunSupport_bounds`
- `brunSupport_card`
- `brunPairCoefficient`
- `brunPairCoefficient_norm`
- `brunPair_mass`

The source is
`docs/source-only/20261102-resume-30j/twolong_e4/Part3TwoLongActualLowerBrunMoment.lean`,
11,742 bytes, SHA256
`552838390dcd59daa76aa26e7fe64b689484fb5cc3f709748870d7dbca0154df`,
Git blob `b39382fb050fcd7996f3abc14503f1b23d4d86dc`.
The source was read at snapshot
`f3084a33ca08daf305ddd7c6eb660a038794614a`; its last touching commit is
`39f5123cfe7f12c2e278797decabddecab324a5e`.

The shared module copies the single original byte interval `[5685, 9321)`:
3,636 bytes containing all six declarations, their complete proof bodies,
both declaration documentation blocks, and their original whitespace.
The support, real power bound, coefficient signs, Boolean cases, arbitrary
complex weight, and theorem premises remain exactly the original text.

## Imports and ownership

Only two direct imports are needed for these declarations:

| Import | Used existing API |
| --- | --- |
| `ImbalancedChen.P5OriginalOneLongLiteralBrunDictionary` | `divisorSupport`, `upperCoefficient`, `gapCoefficient`, `coefficient_bounds`, `chartDivisor_positive`; also supplies the imported `TwoLongDivisorAxisClosure.chartDivisor` and Mathlib context |
| `ImbalancedChen.Part3RoughSlotCharacterLift` | `smallPrimes`, `smallPrimes_prime`, `mem_smallPrimes` |

The literal dictionary's source is still archived under
`docs/source-only/20261102-go-takeover/dependencies/`; this extraction does not
install it or claim its dependencies have been compiled. The import-owner
paths and exact source fingerprints are recorded in `EXTRACTION_BINDING.json`.

The shared module can be referenced as
`import ImbalancedChen.Part3TwoLongBrunSupport` after a separately reviewed
source adoption. The lower-rho definitions and P2 receiver remain owned by
the original provider.

## Complementary provider postimage

`postimages/Part3TwoLongActualLowerBrunMoment.lean` is the original provider
with exactly two edits, expressed in original byte coordinates:

1. At byte 219, insert
   `import ImbalancedChen.Part3TwoLongBrunSupport` followed by LF.
2. Delete the copied byte interval `[5685, 9321)`.

Every other original byte is unchanged, including the provider's module
documentation, namespace, remaining declarations, lower-rho definitions,
and proof bodies. The archival provider itself has not been edited.

For future installation, select the shared owner together with this
complementary provider postimage. The untouched archived provider remains
provenance; compiling its original declarations alongside the shared owner
would create duplicate owners.

## Verification performed

Local byte comparisons verified the contiguous copy, all six individual
documentation/declaration slices, the exact two-edit provider reconstruction,
the six remaining provider declaration names, and the unchanged archival
source. The new shared source contains no `sorry`, `admit`, `axiom`, `unsafe`,
or `native_decide` token. The binding records both output SHA256/Git-blob
identities and all original/shared byte ranges.

No Lean elaboration, kernel validation, cloud task, canonical source edit,
driver edit, new mathematical proof body, or commit was performed.
