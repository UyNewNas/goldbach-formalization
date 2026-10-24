# Compilation-scope inventory

Exact source commit: `368736567624353986efd3b6d6c5ccef97e8b535`.
Read-only, no Lean/lake/build/checker invocation. All source/import/hash data read from Git blobs at that SHA, not mutable worktree content. Nested block comments and line comments removed before import extraction. No AGENTS.md or repository .agents skills were found.

## Counts and scopes

- 1,646 tracked `.lean` files total.
- 1,339 inside `ImbalancedChen/`, plus `ImbalancedChen.lean`: 1,340 library modules.
- 306 other Lean files: verification programs and historical/archive/third-party source copies, not additional production library modules.
- Root has 277 direct imports; its local transitive closure contains 292 modules including root.
- `UncompiledContinuation` has 586 direct imports; closure contains 1,210 including itself.
- Their overlap is 254; union 1,248. Therefore 92 library modules are outside both.
- Batch4 source manifest contains exactly 711 unique paths. Every path exists and every SHA-256 matches the exact committed blob. Its closure contains 1,218 modules.
- No missing local ImbalancedChen imports were found, even when inspecting all 1,646 Lean files. The production local import graph is acyclic. This does not check installed third-party dependencies or Lean elaboration.

## Submitted sources missed by the continuation entrypoint

Eight of the 711 manifest modules are outside both root and continuation closures:

1. `ImbalancedChen.P2AdoptedRowsActualEnclosure`
2. `ImbalancedChen.Part5OriginalOmegaGridCore`
3. `ImbalancedChen.Part5SavedParent394700Buchstab`
4. `ImbalancedChen.Part5SavedParent394700BuchstabAll32Segmented`
5. `ImbalancedChen.UncompiledContinuationV2`
6. `ImbalancedChen.UncompiledContinuationV3`
7. `ImbalancedChen.UncompiledContinuationV4`
8. `ImbalancedChen.UncompiledContinuationV5`

The first is byte-identical to `ImbalancedChen.Certificates.P2AdoptedRowsActualEnclosure`. Compile these module paths independently: importing every source into one new umbrella risks duplicate declarations and changes import-environment semantics.

## ROOT266 is not the repository root import closure

The 266-module census is preserved at:
`docs/evidence/owned-frontiers/20261024-after260-next6-v1/p/026-e8c0e21cd551fef4610e1f2214fa1c68f83f35cdf64d4dff525fa8f31e62b544.raw`.

Its 266 keys are historical owned-module accounting, not root import coverage. Only 28 occur in root closure. 201 occur in continuation closure. 65 occur outside BOTH. Their dependency closure contains 381 local modules. The census itself retains candidate/pending acceptance labels; this inventory does not independently promote its proof status.

All 711 submitted modules plus all 266 census modules plus repository root reach 1,321 library modules, leaving 19 legacy library modules outside. Thus even checking all submitted sources and historical accepted accounting is not equivalent to checking all repository library sources.

## Recommended exact build coverage

For narrow latest submitted checkpoint: explicitly build all 711 manifest module targets, or continuation plus the eight uncovered submitted module targets. Preserve separate existing root regression/audit gates. Combined root + submitted coverage is 1,256 library modules.

For user's broad “all submitted content” with robust repository regression coverage: explicitly name all 1,340 tracked production library modules as independent Lake targets. This avoids silently dropping legacy modules and does not make conflicting historical definitions coexist in one new import environment. A smaller equivalent import coverage set is root + continuation + the 92 modules outside their union. Build coverage must be recorded per actual target and failures must not be silently excluded.

Do not replace the existing root or merge every file into one aggregate. Do not treat archive-copy elaboration as production proof acceptance. Historical `.raw` payloads and source snapshots are immutable evidence, not live modules to rewrite. Continue existing verification/audit programs according to their runner scripts and pinned runtime requirements.

## Archive and duplicate classification

The 306 nonlibrary files break down as:
- 141 in `verification/proof-continuation/2026-10-15`: 140 historical audit sources, one tool.
- 120 in `verification/parts/p0`: 69 round3, 40 round4, 9 top-level audit programs, one queue template, one round5 historical producer audit.
- 5 in `docs/evidence/external-native-pnt`: external Lean/tool/source-context snapshots.
- 40 elsewhere under verification, including current audit tools and historical compilation attempts.

There are 50 exact-byte duplicate groups among all Lean files. One group has two production module paths (the P2 enclosure pair above); most other duplicates are production modules repeated in ledger snapshots or audit snapshots. Full groups, every external path, every module's imports/hash/size, and complete closure lists are in the JSON.

## Reproducible inventory CLI

Run `python3 verification/full_source_inventory.py --output inventory.json` to
record every tracked file's disposition, current SHA-256, size, and existence.
Lean records additionally include parsed imports, production module identity,
root/continuation reachability, batch711 membership, and census266 membership.
Untracked files are intentionally not described as submitted content.

Use `--revision 368736567624353986efd3b6d6c5ccef97e8b535` to read the original
checkpoint directly from Git, independent of later worktree repairs. Without
`--revision`, the report reads current tracked worktree bytes, including edits.
`--targets` prints all production module targets, one per line, for independent
build scheduling. It never runs Lean, creates an umbrella, or alters sources.

`changed_batch_hashes` records original/current hashes explicitly. Changes are
expected during repairs and do not fail inventory generation. Missing submitted
paths or missing local imports return a nonzero exit status. Neither an inventory
pass nor a matching hash is evidence of elaboration, kernel checking, or proof
acceptance. The manifest and historical census remain provenance, not new proof
claims. JSON records every tracked non-Lean file as well as all 306 external Lean
files; historical failure probes and archived snapshots are not automatically
compiled. Current verification programs must use their documented runners.

Run stdlib tests with:
`python3 -m unittest discover -s verification -p test_full_source_inventory.py -v`.

This is a provisional source scope document, not a compilation success receipt.
The initial inventory was read-only and did not invoke a compiler.
