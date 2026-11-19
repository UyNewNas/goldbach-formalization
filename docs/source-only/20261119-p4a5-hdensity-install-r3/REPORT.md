# P4A.5 hdensity installation continuation r3

Parent `c98d1fe0797a32e3409de801d4413916be39ee65`; candidate `P4AOriginalFiniteAll22FineDensity.lean` SHA-256 `1942060c36cde2fb609dce8d370d29fa10701c5e6ed75159416e1c51cb8df7e5`. SOURCE_ONLY; COMPILED=false; KERNEL_REPLAYED=false; TRANSITIVE_AXIOMS=NOT_CHECKED; finite proof bodies UNEVALUATED. No new proof body, mathematical assumptions or external inputs. The independent review referenced in the old packet is a historical source-only review; no new independent review or green promotion was performed.

## New installation evidence

`bind_fallback.py` verifies the linked SHA-256 chain: the hdensity final registry binds the fine predecessor registry; that registry binds `T01_FINE_COFINAL_ALLOWLIST.json`; its high-author record binds `HIGH_PP_REGISTRY.json`; that record binds `COEFFICIENT_REGISTRY.json`. This is scoped to source provenance and does not certify other transitive modules.

For each of the 12 high helpers reached by the Fine allowlist, the actual source bytes, byte count, SHA-256 and literal `import` lines were compared with both Fine's allowlist and the high-author record. All matched. For all 32 sources in the linked finite-coefficient registry, the actual archived source bytes, byte count and SHA-256 matched; their literal imports are recorded individually in `FALLBACK_EVIDENCE.json`. All 32 are now reachable in the static import walk. Of the prior staged choices, 25 previously marked provisional now have exact source-byte bindings to this linked coefficient registry. This does not independently prove theorems or verify transitive compatibility.

Three archived, registry-matched modules were newly staged: `P4AOriginalFiniteFallbackSecondWalls`, `P4AOriginalFiniteFallbackSignedSectors`, and their newly reached `P4AOriginalFiniteFallbackSecondEndpoint`. A fixed-point pass follows only actual imports within this 32-source registry. The original source files and mathematical statements were not edited, and no copy was installed into the checkout's production module directory.

The reproducible partial stage contains 123 files; the literal-import walk visits 524 project module paths, with 35 unresolved project modules and 131 external names. There are 57 explicitly provisional/conditional staged selections, including the v3 gamma candidate described in r2. Counts are diagnostic only: they do not prove parsing, data-file coverage, package presence, correct `.olean` identity, the entire transitive closure or version compatibility. `IMPORT_AUDIT.json` lists the exact frontier and `FALLBACK_EVIDENCE.json` lists source identity and imports.

## Exact theorem and boundaries

The unchanged source candidate intends `∀ δ>0, eventually N, Even N → physicalDensitySum (Q δ N) (ρ δ N) ≤ (currentK+δ)*(singularSeries N / Real.log N)`. Its Fine/cofinal predecessor is called once at `densityReserve/2`; the delta-constant Q and ρ inherit the same β/k and unified N₀. The candidate retains the correction and uses the established sign theorem on the same F, w, z, N and cap=N; compiler expense is inherited rather than charged again. This is a source-level interface assessment, not a newly elaborated theorem. The finite count still retains the complete signed `realPhysicalDistributionError`, `ceil(z)` and `T+1`. Full PP payment, hmajor, hcoprime, hdistribution and hUpper remain outside this result.

The linked manuscript registry identifies revisions `9731290e8f53cffda44129906cde6a965eaa869b` and `ba6ec11d800eccc54406490631895e174de85766` with the same paper tree. The requested 9731290 manuscript was re-read at lines 465–480 and returned blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, matching the documented pin. No versions or parameters were mixed. No new external input was introduced; existing external inputs and their statuses remain in prior registries.

## Verification and remaining work

- `python3 docs/source-only/20261119-p4a5-hdensity-install-r3/bind_fallback.py`: exit 0; 12 high entries and 32 coefficient entries checked, 25 prior provisional entries bound, three missing reachable modules staged in the manifest.
- `python3 docs/source-only/20261119-p4a5-hdensity-install-r3/stage_and_audit.py /workspace/scratch/cb6959cc4223/stage-r3-final > docs/source-only/20261119-p4a5-hdensity-install-r3/IMPORT_AUDIT.json`: exit 0. It checks exact listed hashes and existing scope overlays before the literal import walk. This is not Lean verification.
- The baseline declares `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. They are declarations only; locally `lean`, `lake`, `elan`, `.lake/packages` and `.lake/build` are absent. `lake env lean /workspace/scratch/cb6959cc4223/stage-r3-final/ImbalancedChen/P4AOriginalFiniteAll22FineDensity.lean` returned 127, `lake: command not found`. No kernel, axiom, data or finite certificate replay was run. No CI, resource expansion or user-machine access was performed.
- Next: bind and install the 35 missing imports and verify the 57 provisional selections against the correct source-chain registries; resolve v3 gamma and radial variants without conflation, check data inputs and package identities, and then typecheck the exact candidate and its real import closure in the existing permitted pinned environment. Record every exit code, logs and transitive axioms.

Changed-file SHA-256 (excluding this report):

- `FALLBACK_EVIDENCE.json` `8e37cd77a42d2a07ea2c5ca2d73a9093eb7c5977ba8599e956e7c21b1a75b3d8`
- `IMPORT_AUDIT.json` `4a991daa0c2ea8e4876e089d2fa2d379122b4e6db0e4ee3bf1b33f8c0b7585d3`
- `INSTALL_MANIFEST.json` `948d819832e2c5c67ecbd9e0441b942e1d1c1e81043fa6fc1e0076565f70dbf9`
- `bind_fallback.py` `9a9e94c62f97277fadd3c1ef918b77975ce39b3cb677d26e56db68754fc20070`
- `stage_and_audit.py` `4712cdf8de1acaf35e8ec422e35958736b046088bdaceb39e2c115ca7029dd1a`
