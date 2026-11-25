# Scoped reciprocal core extraction — source evidence

## Scope and status

Date: 2026-11-25. Checkout HEAD before this edit: `63fcd8691951b552078d928bb840c5eef46d0221`.

This is a physical extraction of the existing generic reciprocal/division/clamp declarations. The original declaration text, theorem statements, proof bodies, namespace and order are preserved. No mathematical premise or conclusion is changed. The final endpoint source is unchanged. Lean compilation, kernel replay, declaration ownership inspection and native input qualification are pending; this document grants none of those forms of acceptance.

The previous project edge `P2HistoricQ80DefectLookup -> P2GuardedReciprocalRounding -> CurrentChenUpsilon8HarmonicMean` brought the U8 application and its unrelated Liu–Pan branch into the P2.4 endpoint closure. Q80 consumes the generic arithmetic declarations. It now imports their core module directly.

## Exact edits

1. New `ImbalancedChen/P2GuardedReciprocalRoundingCore.lean` imports only `ImbalancedChen.P2DirectedLogRounding`. The contiguous original block beginning with the namespace command and ending after `Enclosure.clampLower_contains` was moved here without altering any byte of that block; a matching namespace end and a module header were added.
2. `ImbalancedChen/P2GuardedReciprocalRounding.lean` imports the new core and still imports `ImbalancedChen.CurrentChenUpsilon8HarmonicMean`. All six U8 declarations and the ending namespace command remain byte-identical. Existing users of this wrapper retain access to both generic and U8 declarations through its imports.
3. Only the first import of `ImbalancedChen/P2HistoricQ80DefectLookup.lean` changes to the core. Every byte after its first line, including all production defect-lookup repairs, is unchanged.

## File identity

| Path | Before SHA-256 | After SHA-256 |
|---|---|---|
| `ImbalancedChen/P2GuardedReciprocalRounding.lean` | `37621e9308c8d4559a7725ceac018c3a67fc18a4ef048dbab31bdca0682aa1d0` | `eee6ea2c97e259e65dcbb10c49771304e682597411624b3d9e8945021132b073` |
| `ImbalancedChen/P2GuardedReciprocalRoundingCore.lean` | `(new file)` | `d926d9ac112b42518264492cf8bfe591d8de6be9a36210a3621615fbef341c07` |
| `ImbalancedChen/P2HistoricQ80DefectLookup.lean` | `a0a598b9129cecd045de5832a68ecbb2a833313905fac44a8001ded52e5bdd6e` | `992a456dcb131b00fd07d3520d9a77b0c9d23abd4d7b3130b880800c2af9c1f1` |
| `ImbalancedChen/P2OriginalCompactWholeFunctionalEndpoint.lean` | `606cb2277c031d440cc379aedd4029a8f386f9925d93ccfcb77cf37557d80185` | `606cb2277c031d440cc379aedd4029a8f386f9925d93ccfcb77cf37557d80185` |

## Block identity

| Block | Bytes | SHA-256 before and after |
|---|---:|---|
| Namespace start through `Enclosure.clampLower_contains`, including original trailing blank line | 7708 | `d1146d89ef477279652dc77543d1595e008ffbb5d6a3c16961e11554b8e7d3e7` |
| Original U8 doc comment through final namespace end | 2655 | `276a63676e400e933a044aeb9f9c1f5d83e0b1d759978de3ca0a60964fe10eca` |
| Q80 file after its first import line | 29719 | `7e7f9706864c450b6a646d1af520849c6c64378dfffeb0d088092f26de60402f` |

The three equality checks use exact byte comparisons, not whitespace normalization. The original wrapper is recoverable by replacing its first import with the old directed-log import and reinserting the unchanged generic block. The endpoint file byte comparison also passed.

## Declaration ownership

All names below retain the namespace prefix `ImbalancedChen.Certificates.P2DirectedLogRounding.`. Their source owner moves from `ImbalancedChen.P2GuardedReciprocalRounding` to `ImbalancedChen.P2GuardedReciprocalRoundingCore`. There are 25 named declarations plus the original anonymous `Decidable a.ReciprocalValid` instance. The instance command is moved byte-identically in the same namespace and declaration order; its elaborated generated name and object ownership remain for compiler inspection. No aliases, duplicate proof copies or new instances were introduced.

| Kind | Name under the unchanged namespace |
|---|---|
| def | `Enclosure.ReciprocalValid` |
| def | `Enclosure.reciprocalCheck` |
| def | `Enclosure.reciprocalBounds` |
| def | `Enclosure.checkedReciprocal` |
| theorem | `Enclosure.reciprocalCheck_false_of_crosses_zero` |
| theorem | `Enclosure.checkedReciprocal_none_of_crosses_zero` |
| theorem | `Enclosure.reciprocal_endpoint_ne_zero` |
| theorem | `Enclosure.reciprocal_width_denominator_pos` |
| theorem | `Enclosure.reciprocalBounds_contains` |
| theorem | `Enclosure.checkedReciprocal_sound` |
| theorem | `Enclosure.reciprocal_width` |
| def | `Enclosure.reciprocalQ80` |
| theorem | `Enclosure.reciprocalQ80_contains` |
| theorem | `Enclosure.reciprocalQ80_errors` |
| theorem | `Enclosure.reciprocalQ80_width` |
| def | `Enclosure.divisionBounds` |
| def | `Enclosure.checkedDivision` |
| theorem | `Enclosure.checkedDivision_none_of_crosses_zero` |
| theorem | `Enclosure.divisionBounds_contains` |
| theorem | `Enclosure.checkedDivision_sound` |
| def | `Enclosure.divisionQ80` |
| theorem | `Enclosure.divisionQ80_contains` |
| theorem | `Enclosure.divisionQ80_errors` |
| def | `Enclosure.clampLower` |
| theorem | `Enclosure.clampLower_contains` |

The wrapper retains exactly these six U8 declarations: `u8GapBox`, `u8DenominatorBox`, `u8KernelQ80`, `u8DenominatorBox_guard`, `u8KernelQ80_contains`, `u8OriginalGapKernelQ80_contains`.

Moving the source owner requires rebuilding the new module and dependent project objects. Historical object receipts for the old wrapper are not relabeled as acceptance of the new core.

## Closure and verification boundary

The closure agent independently recomputed the actual post-edit graph and recorded it in `scoped_reciprocal_core_census.json`, SHA-256 `d81aef9644faf9d91f821a2162cdf7ef65de9eb9881ddbdefa748523726597ed`.

| Source graph quantity | Before | After |
|---|---:|---:|
| Project modules | 339 | 322, including the new core |
| Direct native entries | 26 | 22 |
| Native source closure | 826 | 515 |

The project count is reduced by 17 net, and the native closure excludes the 311 modules from the unrelated branch. No native module is missing from the fixed-pin historical source census. All 515 remaining native source SHA-256 values match the earlier actual P1 checkpoint source/object probe recorded in `p1_whole_native_census.json`, SHA-256 `945ca3bd3863d62a512e7f2a519adb4b5e7d33134dec52d1787780eb25e5d01e`, task `job_eaf35f2bd90e494696f79222be761976`.

These are source-scope and source/own-object matching results. The earlier probe did not qualify actual import-object maps or a fresh leaf. `Architect.Command`, checkpoint row 54, retains `PACKAGE_PARTIAL_OR_UNBOUND_OUTPUTS_QUARANTINED`. The census explicitly records `compile_credit: false`, `kernel_credit: false`, `cache_acceptance: false` and `STATIC_SCOPE_REDUCED_NATIVE_INPUT_QUALIFICATION_PENDING`.

An independent read-only reviewer compared the extraction against Git commit `63fcd8691951b552078d928bb840c5eef46d0221`. The reviewer confirmed all block/file hashes, exact reconstruction of the original wrapper, unchanged Q80 remainder and endpoint, balanced namespaces and unique moved declaration ownership. The core's directed-log dependency already imports `Mathlib.Tactic` via `RationalLogCertificate`; no obvious missing tactic import was found. Generated instance names and actual elaboration remain pending compiler inspection.

Completed local checks: exact generic-block equality; exact retained U8 suffix equality; Q80 first-line-only difference; unchanged endpoint bytes; unique source ownership of the moved declarations; `git diff --check`. No Lean/Lake command, compile job, kernel replay or CI dispatch was run for this extraction.
