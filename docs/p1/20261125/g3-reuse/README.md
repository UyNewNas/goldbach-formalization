# P1 G3 exact-data provenance and reuse inventory

Recorded 2026-11-25. This packet records existing sources and metadata. It does not download or extract fixtures, change Lean sources, run Lean/Lake, restore objects, or submit a cloud job. Root owns the next inspection of existing cloud data before any download.

## Authoritative data already exists

`ImbalancedChen/P4AOriginalNewFifthArchiveData.lean` reads 94 original pairs: `C0000`–`C0046` and `F0000`–`F0046`, each with `cells.npy` and `floors.npy`. The companion [G3_REUSE_INVENTORY.json](G3_REUSE_INVENTORY.json) contains all 188 exact destination paths, byte sizes, SHA256 hashes, outer NPZ member paths/hashes/sizes, and inner member names. It also records source/configuration provenance and the historical installer inputs.

All 188 path/size/SHA256 triples agree across these three existing records:

- `docs/source-only/20261110-yellow-closure-10t/t05_all22_actual_density/G3_FIXTURES.json`, SHA256 `f79c794c614af8b4aec78ca4601f9b6e6d58f3e47d72b72eac98f94003cca184`.
- `docs/source-only/20261112-resume/t01/density-validation-plan/DATA_INPUT_DELTA.json`, SHA256 `496ed045b62d8cf57afc8db834dc3bb73482d23022660c031e960d4778b7391c` (`old_data_inputs`).
- `docs/source-only/20261110-yellow-closure-10t/t06_actual_mixed_fourier/full87_remote_v3/EXACT_INSTALL_MANIFEST.json`, SHA256 `21ee9d56c5891d6929e4ce1be045a21e6adbda0c372af7bc9a84575b113ff3c9` (`data_inputs`).

| Bank | Blocks | Files | Rows | Uncompressed bytes |
| --- | ---: | ---: | ---: | ---: |
| C, coarse, grid 400 | 47 | 94 | 43,236 | 10,388,672 |
| F, refinement, grid 800 | 47 | 94 | 1,720,184 | 412,856,192 |
| Total | 94 | 188 | 1,763,420 | 423,244,864 |

There are 73 nonempty blocks. The largest is F0020: 133,348 rows and 32,003,776 raw bytes across its pair. Each NPY has a 128-byte header; cells consume 80 bytes/row and floors 160 bytes/row. These are existing source-manifest counts, not a newly executed numerical verification.

The exact original asset is [chen-numerical-evidence-20261010.zip](https://github.com/UyNewNas/chen-imbalanced-semiprimes/releases/download/v2026.10.10/chen-numerical-evidence-20261010.zip), asset ID `626620833`, **323,605,374 bytes**, SHA256 **`8f1bdf63e1aa972256b2422f824f3d177617b31bf41b6a2b8cf29b0562647ad1`**. The live GitHub release API independently reports the same size and digest. This audit did not download or rehash its payload.

For index `kkkk`, the outer member is respectively:

```text
chen-numerical-evidence-20261010-renewal-v2/goldbach-research/fifth-prefix-new-coverage-blocks/block-kkkk.npz
chen-numerical-evidence-20261010-renewal-v2/goldbach-research/fifth-prefix-new-coverage-refinement-blocks/block-kkkk.npz
```

The two original inner members, `cells.npy` and `floors.npy`, are copied byte-for-byte to `ImbalancedChen/g3-fixtures/Ckkkk-{cells,floors}.npy` or the corresponding F paths. No regenerated array or recomputed floor is needed.

## Historical staging archive and local availability

T05's `G3_REPORT.md` and registry identify `G3_INPUTS.zip`: **32,285,020 bytes**, SHA256 **`5903eadd154aa06797a22a2b01399c6255b25d67d688a283630c56ef33f0c328`**. Its reported repository-relative path is `docs/source-only/20261110-yellow-closure-10t/t05_all22_actual_density/G3_INPUTS.zip`; the historical Windows staging path ends in that same directory. The archive would supply sibling `g3-fixtures/` beside the data module.

No physical G3 archive or fixtures were found by the local `/workspace` and `/tmp` inventory. The GitHub T05 directory at source commit `6848b4a69fd6f25806989dac7d305d27a6cd204e` contains the reports/manifests/Lean sources but does not list `G3_INPUTS.zip`. These observations make no claim about the current cloud workspace, which this agent did not inspect.

**Inspect existing cloud candidates before any download.** `docs/p1/20261124/README.md` reports that the original 357 verified numeric inputs are available under `/workspace/p1-stage-20261124` and the required sibling data directories, with `/workspace/p1-mcp-20261124` as the prepared cloud checkout. First check `/workspace/p1-stage-20261124/ImbalancedChen/g3-fixtures/`, then `/workspace/p1-mcp-20261124/ImbalancedChen/g3-fixtures/`, and the current `/workspace/blue-member-build/ImbalancedChen/g3-fixtures/`. Their current existence and hashes remain unverified by this agent. This packet schedules no cloud inspection or compiler call.

## Reuse and acceptance status

Seven local copies of `P4AOriginalNewFifthArchiveData.lean`, including the current canonical file, T05 copies, `stage-r6b`, and `stage-r6b-verify`, are byte-identical: **13,833 bytes**, SHA256 **`5fc51f4622c04ff0d2ce69d87e19d7b0a1cb20ccd48295309e24aab6a4879df4`**, Git blob `571a538486465065b9569b8c40c3914e67610d9d`. No local split data module was found.

The historical `full87_remote_v3/RUNTIME_SETUP_IMPORT_ACCEPTANCE_MAP.json` explicitly records this module as `fresh_or_unmatched_source_build`, with `accepted_object = null` and `actual_setup_import_read_receipt = null`. Its overall status is `STATIC_EXPECTED_INPUTS_ONLY_ACTUAL_RUNTIME_RECEIPTS_PENDING`, `compiled = false`, `kernel_verified = false`, and `accepted_objects = []`. The later `docs/p1/20261124/batch5-source-alignment/NEXT_FRONTIER_GROUPS.json` also records `prior_reuse = null` and excludes the module from ordinary batches because of the external archive elaborators. Source equality is established; a current successful data-module object was not established by this lookup.

Preserve the current reader selection when reusing data:

| Reader | Bytes | SHA256 |
| --- | ---: | --- |
| Current `ImbalancedChen/P4AOriginalNewFifthArchiveReader.lean` | 6,324 | `59d3c878507d07dff88790ed2c9fc626768fd7155dc3250c01763273e2f0d5b6` |
| Historical T05 `P4AOriginalNewFifthArchiveReader.lean` | 6,198 | `c449ef380e318797bcd9789e282b705bbdb847d4215d40cd04b2f404cafac540` |

The historical full87 installer selects the old reader. Reusing its exact data map does not justify overwriting the current reader or its separately obtained acceptance evidence.

## Existing installer: exact invocation and inputs

The existing script is `docs/source-only/20261110-yellow-closure-10t/t06_actual_mixed_fourier/full87_remote_v3/stage_project_full87_v3.py`, SHA256 `d4cba9534ab40e8d0a8b4a4b441cdc0b6b092ed503b3e4f180526ea945d61e76`. Its published invocation appears in sibling `EXECUTION_ORDER.md`. With the variables bound to the existing plan directory, immutable checkout, **new** project destination, and verified original asset, the exact CLI is:

```sh
python "$P1_G3_PLAN/stage_project_full87_v3.py" \
  --repo "$P1_G3_CHECKOUT" --dest "$P1_G3_NEW_PROJECT" \
  --release-asset "$P1_G3_ORIGINAL_RELEASE_ZIP" \
  --manifest-sha256 21ee9d56c5891d6929e4ce1be045a21e6adbda0c372af7bc9a84575b113ff3c9 \
  --purpose source_validation
```

This is a historical full87 source installer, not a G3-only extraction command. It is fixed to `P4AOriginalR17PaidIntegral`, materializes 1,625 mathematical sources and 335 data inputs, and requires 94 exact original NPZ receipts. It was **not invoked** in this audit.

The existing script requires a real authorized GitHub Actions context (`GITHUB_ACTIONS=true`), `SOURCE_COMMIT` equal to checkout HEAD, `GITHUB_RUN_ID`, and `GITHUB_RUN_ATTEMPT`; it does not fetch missing Git objects. All source-origin commits are listed in the companion inventory. Inherited T01 inputs come from `cdc81d65ea82bd35ccc2ea19f916f65d84b7a3a1`, under `docs/source-only/20261110-yellow-closure-10t/t01_remote_fifth_kernel`; their manifest SHA256 is `0aa3a96b57923c18febbc9da35d2cca88d2fec323df75dfd0ea5408a43f41963`.

Its fixed configuration is Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, and native goldbach `09b97db5764ade1246bfb77206baa1b124760958`. The existing `release_nested_member` implementation checks the whole release size/hash, unique ZIP member names, every outer NPZ size/hash, and every inner member size/hash. It writes original bytes and `FULL87_PROVENANCE.json`, without compiling or restoring objects. Existing current-cloud data can instead be checked against the 188 records in this packet; inspecting that data is the pending root-owned step.

## Mathematical identity retained

The original saved G3 floors use four lower and five upper odd logarithm terms. The independent replay uses six/seven terms, so its improved bound cannot replace equality with the original saved floors. The source reports the G3 contribution as `1648717268323516459667 / 2^80`. This inventory retains the manuscript's original finite data and introduces no new mathematical claim or proof credit.
