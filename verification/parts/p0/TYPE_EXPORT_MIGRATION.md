# Type export after the finite-core migration

This is an audit-baseline revision, not a production proof change or an
unconditional-main-theorem claim. Existing full-build, bundled kernel replay,
root/transitive axiom audit, required export gates, runtime guard, dependency
pins, and conditional final bridge remain required and unchanged.

## Evidence and provenance

- Failed run: <https://github.com/UyNewNas/goldbach-formalization/actions/runs/41600572528>.
  Its PR head was `f5acf7426c7e3ee55afee0670366f9c92718058e`, while checkout
  was merge commit `3bd9869ad80e94eb1d0d91f6af76f31db9c1209f`. Both have tree
  `d90bd9b66cc998056399ec41386dbe3327333c59`.
- Migration: <https://github.com/UyNewNas/goldbach-formalization/commit/81b63cafb6ee00590cad194975cc140f465d68b5>.
  Declarations moved from the old supplier modules into
  `ImbalancedChen.FinitePrimeGeometryCore` without renaming their public names.
- Historical Round 3 baseline: successful run
  <https://github.com/UyNewNas/goldbach-formalization/actions/runs/38349841383>,
  job `115139480848`, checkout `59d338b93b2347021237eb51293bb934a316909d`.
  All 198 `P0_ROUND3_DECL` records were recovered from its decoded job log.
  The JSON baseline records every exact name, kind, old/current defining module,
  and SHA256 of the original UTF-8 complete `pp.all` type string, without
  normalization. Its own file hash is pinned by the exporter.
- The failed run emitted 159 Round 3 declarations. Each has the same name,
  kind, complete type, and readable type as the historical run. The 39 remaining
  historical names include the moved structure's generated declarations.

File SHA256 is byte identity, not theorem-semantic identity. Moving a declaration
can change file hashes and module ownership without changing its public name.
The source migration alone is not evidence of successful Lean elaboration or
kernel replay under the new exporter.

## Round 3 revision v2

The complete serialized census now covers the old eight modules plus the finite
core. It requires exact equality of serialized constant names, defining-module
environment names, and exported names, including private/generated declarations.
IR/codegen-only names without ConstantInfo remain separate.

All 198 historical names are still required, with their original kinds and
complete type hashes. Exactly 39 have an explicit ownership migration to the
core. The core's other declarations are also exported and safety-checked; the
new total is therefore not guessed or reduced to 159. The nine production source
files, baseline manifest, and existing toolchain/dependency pins are frozen.

Unsafe, partial, axiom, unknown-kind, forbidden-transitive-axiom, duplicate,
missing, truncated-type, and malformed census cases fail closed. The final
bridge is separate and must still display both `hLower` and `hUpper`.

## Round 6 revision v3

The complete census covers the original four modules plus the finite core.
All 46 historical public names remain required. These three now have the core
as their defining module:

- `ImbalancedChen.HistoricalPrefixCapData.level3_on_fifth_cell`
- `ImbalancedChen.HistoricalPrefixCapData.level3_tuple_on_fifth_cell`
- `ImbalancedChen.historicalUpperFive_cube_tests_iff_log`

The reviewed current HistoricalUpperFiveCellGeometry hash replaces its
pre-migration hash, and the core hash is added. The other three historical
production source hashes and all original toolchain/dependency pins are unchanged.

## Validation and limits

Run the lightweight regression suite with:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover \
  -s verification/parts/p0 -p 'test_type_export_migration.py' -v
```

The parser tests use synthetic fixtures and explicitly test rejection of missing
historical/generated declarations, changed ownership/type, duplicate records,
unsafe/partial/axiom dependencies, truncation, removed bridge hypotheses, changed
frozen sources, and a changed baseline manifest. They do not establish successful
production exports. The historical type hashes are deliberately strict under the
pinned toolchain; a mismatch must be investigated rather than normalized away.

Before acceptance, run the existing complete workflow on the final exact commit.
Retain the new receipts and serialized inventories, confirm all 198 historical
Round 3 types and all 46 Round 6 public names, and inspect any first Lean
diagnostic. Do not mark an unavailable, skipped, or unrun proof gate as passed.
