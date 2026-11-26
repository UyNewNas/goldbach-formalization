# Current P1 correction stage: explicit selection and original receipt reuse

This directory prepares an independent entrypoint for the 21 previously identified P1.5 owners. It does not alter any earlier driver, `P3_REUSE.json`, runtime configuration, guard, serializer, Lean source, or accepted receipt. No cloud job or Lean command was run while preparing this directory.

The complete source inventory is anchored at `6067deae48cbdc0095ac12acc47e24a6ef29cb69`. Publication of this directory will give the entrypoint its own source commit. Every one of the 360 published project sources must still have the anchor's exact bytes, Git blob and literal imports. The live project is checked only on the explicitly selected import closure; the script does not claim that all 360 sources or objects are installed in P1.

## First selection

The smallest useful initial selection is:

1. `ImbalancedChen.P1OriginalSingletonSupportData`, using the original Pointwise provider accepted in the initial four-owner run.
2. `ImbalancedChen.P5OriginalPrimeChartHBWitnesses`, using `P5ActualLabelledPrimeSmoothCharts` accepted in Atlas10.
3. `ImbalancedChen.P1OriginalSingletonCutoffData`, using the preceding witness provider.

These three roots have a closure of **130 project modules**. The only correction-stage targets in that closure are exactly these three. Compilation order is computed from the fixed import graph. Neither P3's unaccepted proper-power chain nor Core nor Mellin is required by this selection.

The explicit whitelist contains 21 targets: the previous 18 candidates plus `P5OriginalPrimeEndpointLogPayment`, `P5OriginalSharpPrimeSynthesis` and `P5PrimeDivisorMeanCorrection`. The published `SOURCE_MANIFEST.json` records every target, its canonical source commit and exact source hash, applicable extraction/review manifests, its direct imports, and the complete candidate topological layers.

`P1OriginalSingletonRemainingTypeIGeometry` is not in this whitelist. Adding it requires a separate explicit revision. A missing `--targets`, an empty list, duplicate names, accepted supplier names, and names outside the 21-owner whitelist are rejected. The entrypoint never silently adds a dependency to the requested compilation or installation list.

## Exact inventory boundary

| Class | Count | Required evidence |
| --- | ---: | --- |
| Explicit correction candidates | 21 | Fresh artifacts, or their own complete retained acceptance at this entrypoint's exact commit |
| Accepted supplier owners | 17 | Their original normal, named kernel and complete owned-inventory receipts, validated by the unchanged API |
| Fixed dependencies with retained context witnesses | 295 | Actual `.olean` and `.trace` fingerprints read from an original normal receipt whose hash is fixed by the published public acceptance summary |
| Additional fixed dependencies with object observations | 8 | Existing P1 object observations, including the two retained trim providers |
| P3 dependencies without acceptance in this revision | 19 | Any selected closure reaching one of them holds; this entrypoint does not compile them |
| Full published project source graph | 360 | Exact source bytes and literal import graph from the fixed Git anchor |

The 303 fixed dependencies are the 295 retained-context entries plus the eight observed entries. A source hash is never used as an object hash. For a retained-context entry, the script reads the original `NORMAL_PASS.json`, checks its published hash, original source commit, complete source map, complete `.olean`/`.trace` key set, and runtime/configuration binding, then obtains the object's recorded fingerprint from that receipt. It checks only the relevant live dependency against this fingerprint. Reading such a dependency record does not claim a new standalone normal/kernel acceptance for that dependency.

The eight observation records are extracted from already saved P1 observations. Their input file hashes and row indices are retained in `FIXED_DEPENDENCY_OBSERVATIONS.json`. They cover:

- `Part3CleanBetaLargeGCDMajorant`
- `Part3CommonSmoothCutoff`
- `Part3ComplexCRTConsumer`
- `Part3ComplexDispersion`
- `Part3FactorFiberDivisor`
- `Part3PolynomialResidueDivisorBound`
- `P5OriginalPrimeEndpointDivisors`
- `P5zElevenErrorTransport`

The last two already have source, `.olean`, `.trace` and `.ilean` artifacts in the saved observation. They are preserved dependencies, never installation or compilation targets. The three newly added trim candidates were previously observed with absent sources and artifacts; this fact does not replace the fresh live checks before any new action. For other new candidates, no absence is inferred from a missing inventory row.

Of the 21 candidates, only `P1OriginalSingletonProperPower`, `P1OriginalHistoricalProperPower` and `P1OriginalSingletonAtlasProperPower` reach the unaccepted P3 chain. The other 18 have a union of 157 project modules. This classification concerns project imports. Every selected owner still has to pass the guarded stock readiness command for **all its literal imports**, including external imports.

## Supplier identities remain separate

| Supplier group | Original source commit | Original job | Published graph size |
| --- | --- | --- | ---: |
| Initial four providers | `d20acdf13882e17d97833064f5e7c54f3192b03c` | `job_1ed0e0c8d4ee466f8444aff044abe510` | 316 |
| Atlas10 | `418ad4b9a5f2d992871062258a2eefd7fdf4b9ee` | `job_5f42ad18fde84377987c244daf0b5bfc` | 68 |
| Core | `ef450be0a89b6a3f88b3bca19d06e04e7967fa18` | `job_0c98f60f3fbe4aaa8d3e23fcf53dbcb8` | 168 |
| Mellin | `21789da92213323d645122cfcc7dff9c10dc82d6` | `job_8d58f7741c56448980ca0984ae5c0239` | 168 |
| BrunWeights | `418ad4b9a5f2d992871062258a2eefd7fdf4b9ee` | `job_41c06d666c6642889cc27d82ee281eb7` | 77 |

Only supplier owners in the selected live closure receive a full read-only `audit_valid` validation. The validator is the unchanged Batch13 API at `4cea0407c1258eaddd7d4952cffa4aea67310422`, SHA-256 `95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea`. It checks the original normal build, named kernel command, full environment-owned inventory and all owned axioms. It does not invoke Lean or the kernel while reading those receipts.

Each old graph is verified from its own published commit. The selected supplier's current closure must equal its original closure and source hashes. The retained `executed-driver.py` must equal the old published driver; no equality to a mutable or absent checkout driver is required. Original compile `CONTEXT_BEFORE/AFTER` and `GIT_BEFORE/AFTER` remain equal, and every retained evidence file read by this entrypoint is fingerprinted and preserved through the new run.

Core and Mellin keep distinct acceptance identities. Core's old published graph contains the first Mellin repair, but Core's own live closure is one module. The later unrelated Mellin change does not invalidate or rebind Core's receipt. Mellin is bound to the successful second-epoch terminal observation and its exact original `RESULT.json` and normal-log hash, then checked through the same complete original audit API. The terminal observation must also contain exactly one successful `audit-lane-0` END record, with exit zero and empty Built/Failed lists. Its published log hash must match the retained `runs/attempt-00000/ImbalancedChen.PrimeProductsMellinExactMeanInsertion/audit-lane-0.log`; that log joins the before/after retained-input fingerprints without being exported. Mellin's original source commit is never replaced with the new correction-stage commit.

The original Core group failed on Mellin, and the original P3-20 group failed after BrunWeights. Those group failures remain recorded. The entrypoint uses only the individually accepted Core and BrunWeights owners and does not turn their original group results into full-group successes.

## Two separate steps

`install_sources.py` is an additive source operation. `run_selected.py` performs selected normal/kernel/full-owned acceptance. The latter contains no source installer or cache importer.

### Additive source installation

The installer validates the complete published 360-source manifest. In the selected live closure, every existing source must exactly match its published bytes. A missing source is allowed only when its module was explicitly selected. Such a module must have no existing artifact. All active sources are checked before the first write; each addition uses `O_CREAT | O_EXCL`. There is no overwrite, deletion, backup restoration, trace repair, cache transfer, or runtime/configuration edit.

The installer records all observed cache artifacts for the selected closure and all 21 whitelist targets. It requires those artifacts to remain unchanged, preserves all existing and unselected target sources, and verifies the selected source graph after writing. It uses the existing lane-0 serializer and verifies the original dirty Git state before and after. `--check` makes no writes and opens no validation lane.

After publication, invoke the retained published installer with the final full source commit and the exact first-three selection:

```sh
python3 -B <retained-published-installer.py> \
  --source-commit <published-source-commit> \
  --targets \
    ImbalancedChen.P1OriginalSingletonSupportData \
    ImbalancedChen.P5OriginalPrimeChartHBWitnesses \
    ImbalancedChen.P1OriginalSingletonCutoffData \
  --check
```

Use the same arguments with `--install` for the separately authorized additive step. The executed installer bytes must equal `git show <published-source-commit>:docs/p1/20261126/p15-current-corrections/install_sources.py`. The cloud checkout need not contain this new path.

### Selected acceptance

The analogous command for the retained published driver is:

```sh
python3 -B <retained-published-driver.py> \
  --source-commit <published-source-commit> \
  --targets \
    ImbalancedChen.P1OriginalSingletonSupportData \
    ImbalancedChen.P5OriginalPrimeChartHBWitnesses \
    ImbalancedChen.P1OriginalSingletonCutoffData \
  --check
```

`--check` reads source, runtime, cache and original receipts; it does not perform stock readiness or acceptance commands. `--run` uses the same explicit selection inside the unchanged lane-0 serializer.

Before each new owner, the driver executes the guarded literal direct-import command `lake --no-build build +<import>:olean ...`. Exit zero and empty Built/Failed lists are required. The unchanged `run_owner` then calls the unchanged `normal_one` and `audit`: only that one owner may be built, followed by its named kernel and full owned-type/axiom audit. Successful accepted suppliers are never passed to `run_owner`.

An already complete selected owner at this exact new entrypoint/commit is read and reused without another normal/kernel run. A nonselected candidate needed as a dependency must already have its own complete acceptance at this same entrypoint/commit. Unknown existing target artifacts, partial audit evidence, or retained computation under a different commit cause a hold for inspection. No artifact is deleted to make an owner appear fresh.

Every stage preserves sources, runtime, configuration, the four protected original roots, fixed dependency artifacts, original retained evidence and other target artifacts. A final guarded stock check of the selected owners must also return zero with empty Built/Failed lists. All source reads and new evidence retain `whole_P1_5_complete = false`.

New execution evidence is confined to `/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/<published-source-commit>/`. Original evidence stays in its original directory and retains its original source-commit fields.

## Local verification and limits

Run `python -B docs/p1/20261126/p15-current-corrections/verify_static.py` locally to reproduce the source and static checks. It verifies the exact 360-source Git binding, all 21 per-source origin bindings, 17 original supplier source closures, 295 normal-context recipes, eight real object-observation records, and equality of 14 borrowed function ASTs with the published integration driver. It also exercises isolated Python positive/negative fixtures for selection, literal-import stock gates, old Core identity, and additive-only source planning.

The check does not call a driver or installer entrypoint, the live acceptance API, Lean, Lake, a kernel, or any cloud service. `STATIC_VERIFICATION.json` records the actual local result and input hashes. This is preparation evidence, not a new Lean acceptance and not a claim that the 21 candidates have succeeded in P1.
