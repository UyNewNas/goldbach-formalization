# P4A.5 same-ρ hdensity installation continuation r15

Parent `9b3a3eeebf8b65f417cab7a35d26f5587fd85efb`. All **105** original witness files previously identified for five actual source loaders have been recovered from the author's published v2026.10.10 numerical-evidence release, checked against the recorded individual SHA-256 and byte length, and actually installed in a new isolated working tree at the exact source-relative or working-directory-relative paths. A separate audit reopened every installed file and reported `105 match`, 632,957,612 bytes. The previous 188 G3 member files were separately installed and verified in the same working tree. This is byte identity and placement evidence, **not** a finite-certificate evaluation, Lean compilation, or a complete-data-closure claim.

The candidate `P4AOriginalFiniteAll22FineDensity.lean` remains unchanged, SHA-256 `1942060c36cde2fb609dce8d370d29fa10701c5e6ed75159416e1c51cb8df7e5`. No Lean theorem, proof body, mathematical assumption, analytic input, resource option, manuscript version or constants were changed. SOURCE_ONLY=true; COMPILED=false / UNCOMPILED; KERNEL_REPLAYED=false; TRANSITIVE_AXIOMS=NOT_CHECKED; FINITE_BODIES=UNEVALUATED; NEW_INDEPENDENT_PROOF_REVIEW=false.

## Original witness provenance and exact placement

The r14 `RUNTIME_WITNESS_AUDIT.json` binds five actually reached source-loader hashes to the independently recorded T06 v3 source-only install manifest and 105 exact data member names, lengths and SHA-256 hashes. The G6 witness also matches this P4A.5 chain's own `G6_RELEASE_INPUT_REUSE.json`. The recovered data are original release members, not substituted numbers, recalculated endpoints or a new proof. Matching these five source hashes and their data records does not establish full T06/P4A.5 variant compatibility.

- `P2OriginalSaving15RadialArchive`: one radial file, 77,770,486 bytes.
- `P2OriginalSaving17DescendingArchive`: 15 files, 140,255,702 bytes.
- `P2OriginalSaving18UnequalArchive`: 30 files, 177,946,884 bytes.
- `P2OriginalSaving20FirstFailureIntegral`: 58 files, 236,787,809 bytes.
- `P4AOriginalThirdFallbackArchive`: one G6 witness, 196,731 bytes; SHA-256 `0401062c690c7993fd34722dca97d3c504f3e72f83d87659f597d135490d50a5`.

The isolated cwd is `/workspace/scratch/cb6959cc4223/p4a5-r15-work/lean`. The first four loaders use the **cwd-relative** `../goldbach-research/`, which here is the task-specific sibling `/workspace/scratch/cb6959cc4223/p4a5-r15-work/goldbach-research/`; G6 is source-relative `lean/ImbalancedChen/G6_ORIGINAL_WITNESS.json`. Other working directories need appropriate placement or a separately justified adaptation. This work does not modify any Lean loader or external shared `goldbach-research` directory. `WITNESS_STAGE_RECEIPT.json` and `INSTALLED_WITNESS_AUDIT.json` provide per-file paths, hashes and exact verification status.

Only the ZIP central directory and selected byte ranges were downloaded. The release metadata reports whole-archive SHA `8f1bdf63e1aa972256b2422f824f3d177617b31bf41b6a2b8cf29b0562647ad1`, but the whole archive was **not** downloaded or hashed. For each recovered member the staging script checks central-directory metadata, local header name/method, decompressed size, CRC and registered SHA-256; it validates every requested member before writing, then rechecks while writing. `audit_runtime_witnesses.py` independently reopens and hashes the files at the paths the five loaders actually use. No JSON proof payload was evaluated.

## Reproduction from the registered release

The preceding r9/r14 packets document rebuilding the sparse partial ZIP central index and the 188 G3 members and assembling the exact reachable Lean sources. `stage_release_witnesses.py` expects the central index from r9 (not a full ZIP) and these exact original byte ranges, fetched sequentially from `https://github.com/UyNewNas/chen-imbalanced-semiprimes/releases/download/v2026.10.10/chen-numerical-evidence-20261010.zip`:

| Range file | Inclusive byte range | Observed SHA-256 of fragment |
|---|---:|---|
| `r15-firstfail.range` | `2925544-67447288` | `dcf5d49d79c2bcb98580c23fbd80f3b5698133f9e3c6ea7112553e1bd7c93143` |
| `r15-descending.range` | `99788252-133159180` | `01157aeb6913e84d88321770c591d2479ad7d281d47d66151b5661a135fd9b4b` |
| `r15-radial.range` | `134934435-151869660` | `507e9191a6eb61a3b4e389b3082bb98885867b9e5b9cd027ecab813032b8a006` |
| `r15-unequal.range` | `171917503-217058034` | `e835fffe0aec8b125c52c96f23a2538ed8751c5ee5f174e77fd58bb921f89858` |
| `r15-g6.range` | `323064482-323164481` | `165b0b0e20f546eb7bc065572c6d97c44505bfa6d4e6d6c649aeb1f0a0bd19f4` |

Example per range: `curl -fsSL --max-time 55 -r 323064482-323164481 "$url" -o "$scratch/r15-g6.range"`. Run the stage verifier with `--stage "$scratch/work/lean" --range-dir "$scratch" --index "$scratch/paper-zip-index.sparse" --groups firstfail descending radial unequal g6`. Use the r14 auditor on the same stage root as cwd assumption. The staging verifier authenticates individual members against prior manifest SHA/size, not a claimed whole sparse-file hash. Large raw inputs and fragments are ephemeral and are not committed to Git.

## Claim and remaining boundaries

The unchanged source-reviewed candidate targets `∀ δ>0, ∀ᶠ N, Even N → physicalDensitySum (Q δ N) (ρ δ N) ≤ (currentK+δ)*(singularSeries N/Real.log N)`. Its historical source review records a single Fine invocation at `densityReserve/2`, one β/k and common N₀, δ-independent Q/ρ, inherited HighAtoms, strict support, compiler expense and real finite count, and the actual correction retained with nonnegativity applied to the same F/N/cap/w/z and w≤z. Compiler expense is not paid again. This is inherited **source-only** scope, not a newly verified theorem. The finite count retains the complete signed distribution error, `ceil(z)` and `T+1`; full PP payment, remaining assembly inputs and hUpper are not supplied, and no signed PP premise was added as a density hypothesis.

The previous literal import inventory still has 70 unresolved project imports and 157 external names; this count is not a closure result. The gamma producer/consumer source conflict (`6917658f…` original versus `fb0e5a57…` v3 repair) and conditional selections remain unresolved. Existing source-level resource options recorded in r13 were not executed or increased; do not run them contrary to the user's no-expansion rule. These 105 files complete only the five inventoried loaders and do not establish that every other potential data dependency is installed.

The manuscript revision `9731290e8f53cffda44129906cde6a965eaa869b` again has `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, consistent with the registered chain. Fixed declarations remain Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`; these are not locally installed-version receipts. External inputs, precise statements, normalizations, conditions, call sites and verification statuses remain in the predecessor registries; no new analytical input was introduced.

## Verification and next action

- Python 3.12.14. The r14 source merger re-created the 664-source tree with receipt SHA `6eda93a3dcfad09f56d8cdf6051bc444e7afc9621ab5fecadded2cb03bb17092`; r9's G3 verifier installed 188 members with receipt SHA `ca484f66ba9efdc89fbf7b1692cac17ccee9ff3825a546870faa9799c2d3fb5f`. Both exited 0.
- `python3 docs/source-only/20261120-p4a5-hdensity-install-r15/stage_release_witnesses.py --stage /workspace/scratch/cb6959cc4223/p4a5-r15-work/lean --range-dir /workspace/scratch/cb6959cc4223 --index /workspace/scratch/cb6959cc4223/paper-zip-index.sparse --groups firstfail descending radial unequal g6 > docs/source-only/20261120-p4a5-hdensity-install-r15/WITNESS_STAGE_RECEIPT.json` exited 0. A rerun with the final script exited 0 and produced an identical receipt. All 105 individual members were verified prior to installation and each new output rehashed during write.
- The r14 `audit_runtime_witnesses.py` was run independently on the new stage, exit 0: `{'match': 105}`, total 632,957,612 bytes; its separate receipt is `INSTALLED_WITNESS_AUDIT.json`. Its repeat output compared byte-identical. This is file identity, not numerical certificate replay.
- A deliberately all-zero, length-correct G6 fragment was rejected by the final staging script with exit 1 and a local-header assertion. The previously staged G6 file's SHA before/after was identical (`cmp` exit 0); this tests fail-closed behavior for that input. `python3 -m py_compile` for the staging script exited 0.
- From the isolated working directory, `lake env lean ImbalancedChen/P4AOriginalFiniteAll22FineDensity.lean` exited 127: `/bin/bash: lake: command not found`. Lean/Lake/Elan and pinned package closure remain unavailable. No Lean elaboration, kernel replay, transitive axiom check, finite certificate evaluation, resource expansion, CI or user machine was used.
- Next: confirm and install any additional raw inputs from other reached or newly reached modules, resolve the 70 visible missing imports, gamma conflict and conditional choices, and reconcile source resource options without expanding permitted resources. In a permitted existing pinned environment compile the precise target and dependencies, inspect transitive axioms and replay finite bodies. Separately prove signed-error payment and other assembly hypotheses; full PP/hUpper are still open.

Changed-file SHA-256 (excluding this report):

- `INSTALLED_WITNESS_AUDIT.json`: `dcdc69d4251752747f43bb797e13b53955e40bd2509fa118d2868e965091a8ef`
- `WITNESS_STAGE_RECEIPT.json`: `c7f31bdef38f444746ad92359bc2f66460050a1d2d409550437341ed4a5353d5`
- `stage_release_witnesses.py`: `796871e5f3da13aa82da7a2657746644994bde0fe895192a39a2588ff78ac909`
