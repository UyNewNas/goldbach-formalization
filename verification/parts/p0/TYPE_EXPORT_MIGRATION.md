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

## Round 3 revision v3: serialized occurrences and defining owners

Run <https://github.com/UyNewNas/goldbach-formalization/actions/runs/41748160724>
passed its full build, kernel replay, root axiom audit, Round 4 export, and Round 6
export, but the previous Round 3 exporter stopped at the exact-set assertion for
`ImbalancedChen.Certificates.PairedV2Prefix4`. Its imported ownership census was
229. This is diagnostic evidence, not a newly fixed expected count. The old
exporter did not print that module's differing names before failing; this
revision prints both partitions and their concrete differences before asserting.

The pinned Lean 4.33.0-rc1 importer explicitly permits an equivalent generated
theorem to be realized and serialized in several modules, retaining the first
module as its defining owner. See
[the pinned importer and its theorem-identity checks](https://github.com/leanprover/lean4/blob/v4.33.0-rc1/src/Lean/Environment.lean#L2248-L2347).
Consequently, per-module serialized occurrences and unique defining-module
ownership are distinct inventories. Treating them as always identical rejects
valid imported theorem copies.

The census still covers the old eight modules plus the finite core. For each:

- Serialized names must exactly match its `ConstantInfo` entries, with no
  duplicate names within a module. Every occurrence produces a separate record
  keyed by `(serialized_module, name)`; no shared occurrence is silently dropped.
- Its owned serialized partition must exactly equal the defining-module
  environment inventory and exported census. IR/codegen-only names without
  `ConstantInfo` remain separate. Shared names do not inflate the owned count.
- Every raw occurrence must be safe, non-partial, non-axiomatic, and have exactly
  the environment's type expression, universe parameters, and declaration kind.
- A shared occurrence must be a theorem with an earlier defining module and an
  actual theorem entry in that owner's serialized constants. Its type, universe
  parameters, and theorem `all` field must agree with the owner and environment.
  Lean permits different proof values for these equivalent theorem statements;
  this check does not pretend their proof bytes must be equal.
- Each exact serialized type and proof/value is inspected for direct constant
  dependencies, including inductive constructors where relevant. Every dependency
  must exist in the kernel environment, and its transitive axioms are checked
  against the unchanged `propext`, `Classical.choice`, `Quot.sound` allowlist.
  Direct theorem self-reference is rejected. This avoids checking only the shared
  theorem name through the first owner's cached axiom entry. Existing complete
  owned-declaration and final-bridge transitive-axiom checks remain in place.

All 198 historical names are still required, with their original kinds and
complete type hashes. Exactly 39 have an explicit ownership migration to the
core. The core's other declarations are also exported and safety-checked; the
new total is not guessed or reduced. The nine production source files, baseline
manifest, and existing toolchain/dependency pins are frozen.

Unsafe, partial, axiom, unknown-kind, forbidden-transitive-axiom, duplicate,
missing-occurrence, malformed-partition, truncated-type, and malformed census
cases fail closed. The final bridge is separate and must still display both
`hLower` and `hUpper`. These inventory checks supplement, not replace, the
existing successful full build and independent kernel/root audit gates.

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
frozen sources, and a changed baseline manifest. Round 3 also accepts valid shared
theorem occurrences and rejects missing/extra occurrence records, malformed
owned/shared partitions, wrong owners, shared non-theorems, failed identity flags,
missing dependencies, direct theorem self-reference, and forbidden raw axioms.
These synthetic tests do not establish successful production exports. The historical type hashes are deliberately strict under the
pinned toolchain; a mismatch must be investigated rather than normalized away.

Before acceptance, run the existing complete workflow on the final exact commit.
Retain the new receipts and serialized inventories, confirm all 198 historical
Round 3 types and all 46 Round 6 public names, and inspect any first Lean
diagnostic. Do not mark an unavailable, skipped, or unrun proof gate as passed.
