# P2 lossless certificate-data split

State: **WAITING_FOR_P0**. Request: **REQUESTED**. Verification: **SOURCE_ONLY**.
Input commit: `d41a7bc48b7066cd95c2a9e143a13e494d44b284`.

## Subsequent diagnostic-driven proof repairs

P0 run `38673067254`, source `dbf27664c27e22f97dda5c2e74fc7555d46ab92d`,
strictly compiled and replayed the corrected generic Rows source. Its unchanged
source SHA-256 is
`56eebe1e99f8dd6d79da3c49d0bcfb39fcc28f4c2468fdff8446a5876314cfbf`.
DataBlock11 also compiled. These are limited stage receipts, not whole-P2
acceptance. The run then failed only on Block11's two trailing `decide +kernel`
steps, which reported `No goals to be solved` after the preceding rewrites.

The current candidate removes that exact redundant ending in all twelve block
totals and the two final totals, 26 lines altogether. It retains all 186 strip
decision proofs, every declaration type, all numerals and data, the rewrites,
all length proofs and the already-passed Rows file. The current split producer
incorporates both this control-flow repair and the earlier two-line Rows shape
repair, so regeneration no longer needs an external Rows overlay. Its `--check`
verifies the actual corrected source hashes. Corrected blocks and final assembly
remain SOURCE_ONLY until P0 runs their gates; no success is inferred for them.

## Concrete failure addressed

Run `38669650232`, source `8733e7d6035ecf3897d8771ce77b139a7fcf6d08`,
failed twice while compiling the common `PairedV2FullCertificateData` dependency
at `-t0 -j2 -M4096`. Both failures were `lean::memory_exception` at `interpreter`,
exit `-6`; neither new target theorem was reached. The exact artifact is
`11944095568`, SHA-256
`e3351bc45373b2ee504c0f228a6baefae49c3bc828633c4d00cae725fe780171`.
The receipt and log identities are recorded in `data-split-prior-failure.json`.
This is a changed-source retry proposal, not an unchanged rerun or a resource
increase. No execution or proof acceptance is claimed by this source work.

## Lossless carrier change

- All 186 `approximations326` through `approximations511` declarations retain
  their exact original names, types, definition bodies and whitespace bytes.
- Twelve data modules carry consecutive groups of at most 16 strips. The
  largest data leaf has 2,757 rows; the longest individual strip is 191 rows.
- The old `PairedV2FullCertificateData` compatibility entry imports the twelve
  leaves and keeps its original `approximations` selector and `approximation`
  definition byte-for-byte. Its source is now 4,978 bytes.
- Every existing sum block imports only its corresponding data leaf. Its old
  block definitions, declaration types and strip proofs are byte-identical;
  only the redundant trailing tactic of each block total is removed.
- `PairedV2FullMask`, `PairedV2FullMaskData`, `PairedV2FullChecker`,
  `PairedV2StripCertificates`, raw JSON, root imports, pins and constants are
  unchanged. Historical full-row checker receipts are retained; they have not
  been rerun or promoted to acceptance of the changed module graph.

`data-split-source-manifest.json` gives the complete 186-declaration mapping,
old/new line spans, identical declaration SHA-256 values, tuple-stream hashes,
pair/E0/E1 counts and every generated-source hash. Static coverage is exactly
17,572 unique canonical pairs, with E0 = 6,091 and E1 = 11,481. The old input
reconstructs exactly to SHA-256
`a059e969139810aa89516661609b540968efbf6b1e2c2ab975a8262ce8462309`.
No numerical witness was regenerated from a different certificate.

## Kernel proof candidate, not merely Python equality

The light `PairedV2NaturalSumRows` module retains the existing
`sum_getD_eq_map` theorem type and actual list/getD objects, with only the
two-line cons-domain shape repair. It imports `FullChecker` instead of the
full certificate data. Its closure excludes FullCertificateData and the twelve
large data leaves; existing small mask/geometry data dependencies remain.

Each numerical block now also proposes a separate `stripN_length` theorem:
the original literal list length equals `512 - firstU` at its original Fin 186
ordinal, proved by `rfl`. Each fact reduces just one list spine. A new
`PairedV2NaturalSumRowAssembly` combines all 186 facts using the actual
dependent `Fin.cases` eliminator, ending in `fun i : Fin 0 => Fin.elim0 i`.
It does not run a monolithic `decide` over all 17,572 rows.

The exact full theorem type is retained:

```lean
approximation_lengths : ∀ i : Fin 186,
  (approximations i).length = 512 - firstU i
```

The existing `strip_sum_eq_map` and `sum_rows_eq_list` statements/proofs move
verbatim into that assembly. Their names remain unchanged. The final
`PairedV2NaturalSums` import is redirected to it; `approximations_partition`
remains unchanged, while its two total proofs lose only the redundant trailing
tactic. This is a source candidate for
the actual kernel bridge. P0 must check it; source or Python equality alone
does not establish the bridge.

The final unchanged finite goals remain:

```lean
lower_numerator_sum :
  (∑ r : Row, (approximation r).lower) = 55858378943374979
upper_numerator_sum :
  (∑ r : Row, (approximation r).upper) = 55858409959907296
```

The common denominator stays `100000000000000000000`. These are the
K/80-normalized adopted-fibre witnesses, not a bound on complete K. No actual
integral, Buchstab, full eighteen-term budget, hLower or hUpper obligation is
discharged by this increment.

## Reproduction and source-only checks

```text
python3 verification/parts/p2/split_paired_v2_certificate_data.py --check
```

Without `--check`, this deterministic static producer regenerates the 28
selected Lean sources and two reports from the frozen Git input. It uses only
Python and `git show`, never Lean or any checker. It verifies protected bytes,
declaration and tuple identity, once-only E0/E1 provenance coverage, preservation
of strip proofs and the exact total-proof repair, source dependency hashes, and that each sum block
reaches exactly one data leaf. Its reported project closure has 37 modules plus
10 external Mathlib import-frontier modules. External recursive object binding
is deliberately unpaid; pinned package revisions are recorded.

The older `generate_paired_v2_natural_sums.py` still targets the monolithic
layout and is not the current split generator. Its Rows and total-proof templates
receive the same minimal corrections so it cannot regenerate these known
tactic bugs. Do not run that older producer over this split candidate. Its two
original manifests and `data-split-static-review.json` remain historical records
of the earlier frozen candidates; the current split manifests and latest P0
request identify the corrected sources and the exact 26-line removal map.

The dependent eliminator design was checked against Lean `v4.33.0-rc1`:

- [Fin.cases](https://raw.githubusercontent.com/leanprover/lean4/v4.33.0-rc1/src/Init/Data/Fin/Lemmas.lean)
  has motive `Fin (n+1) → Sort _`, a zero case and a dependent successor case.
- [Fin.elim0](https://raw.githubusercontent.com/leanprover/lean4/v4.33.0-rc1/src/Init/Data/Fin/Basic.lean)
  has type `Fin 0 → α`; the explicit terminal lambda is needed for the dependent
  motive. The frozen goldbach `MixedEtaGeometry.lean` uses this same pattern.

These are API/source checks. They do not supply compilation, same-object replay,
complete declaration/type export or transitive-axiom/import-object acceptance.

## P0 acceptance order and stop conditions

1. Compile the light `PairedV2NaturalSumRows`, then `PairedV2NaturalSumsBlock11`
   (longest strip) and `PairedV2NaturalSumsBlock10` (largest data leaf), under the
   existing single-heavy-slot `-j2 -M4096` policy. Stop on an actual diagnostic.
2. If those pass, compile every remaining block 00–09, the compatibility data
   selector, `PairedV2NaturalSumRowAssembly`, and `PairedV2NaturalSums`. No strip
   or budget may be skipped; passing the pilot is not global completion.
3. Bind the exact moved defining-module declarations and all imported objects,
   obtain required strict/type/inventory/axiom/replay gates, and let P0 record
   acceptance. Existing compatible compiled prerequisites may be reused only
   under P0's exact fingerprint/object rules.

The 186-deep elaboration, old row/list tactics and aggregate import memory
remain genuine untested risks. Preserve the first exact failure and stop for
diagnosis rather than changing limits, pins, constants, witnesses or trust.
This round ends at the frozen REQUESTED handoff; no new analytic layer is added.
