# P4A.5 hdensity installation continuation r6

Parent `f0a0cbbe181c58c61d8e13cb30d9ae358095993f`; unchanged candidate `P4AOriginalFiniteAll22FineDensity.lean` SHA-256 `1942060c36cde2fb609dce8d370d29fa10701c5e6ed75159416e1c51cb8df7e5`. SOURCE_ONLY; COMPILED=false; KERNEL_REPLAYED=false; TRANSITIVE_AXIOMS=NOT_CHECKED; finite proof bodies UNEVALUATED. No mathematical theorem, proof body or external input was added. Previous independent review is a historical source-only review; no new independent review or green promotion was performed.

## Installation progress

The actual import traversal reaches the original T03 saved87 upper-chain sources. All 16 author-selected source files in `t03_saved87_actual_gain/FINAL_REGISTRY.json` were compared with the archived bytes, sizes, SHA-256 values and actual literal imports. The restricted traversal reached 15: 12 newly needed sources were staged and three already-staged provisional choices were matched to that registry. One registry source was not reached and was not installed solely because it was listed. See `SAVED87_EVIDENCE.json` for the exact files and edges.

The same T03 final registry lists earlier source inputs used at review. Of its 19 Lean source inputs, 18 match the currently archived bytes. The actual import walk reaches all 18; 17 were newly staged and one existing provisional selection was bound to its recorded hash. This is source installation work, not a repetition of the P4A.4 endpoint proofs, evaluation of their finite certificates, or proof of any outside analytic input. No production module was overwritten. See `REVIEWED_INPUT_EVIDENCE.json`.

The remaining reviewed-input source `P4AOriginalNewFifthArchiveReader` differs: T03 recorded `0eae7ab3d79c3a0f57d42870a1c8016f9e5b22aa50a8c0fa5e7d2fe24527b844`, while the current archive is `c449ef380e318797bcd9789e282b705bbdb847d4215d40cd04b2f404cafac540`. The historical T09 review explicitly describes a later proof-body repair, states definitions/types remain the same, and directs the final T05 hash for that joint manifest. Neither byte identity nor this old review establishes a kernel receipt. The Reader was not staged in this step; its actual P4A.5 compatibility and the optimized radial variant remain separate obligations.

The isolated partial stage now contains 169 files; the literal-import walker visits 630 project modules, with 55 unresolved project imports, 153 external module names and 46 provisional or conditional choices. Previously there were 35 missing modules: newly traversed imports exposed further dependencies. These counts do not measure proof completion or guarantee Lean parsing, data coverage, package identity, `.olean` compatibility, transitive closure or kernel acceptance. The two audit JSONs record the intermediate and final literal import frontiers.

## Exact density and boundaries

The unchanged candidate intends `∀ δ>0, ∀ᶠ N, Even N → physicalDensitySum (Q δ N) (ρ δ N) ≤ (currentK+δ)*(singularSeries N / Real.log N)`. The old source calls Fine/cofinal once at `densityReserve/2`; its Q and ρ ignore δ and share β/k and N₀. The actual correction stays in the upper; the sign theorem uses the same F, w, z, N and cap=N, while compiler expense is not charged twice. This is the existing source-level claim, not a newly compiled theorem. The actual finite count still retains full signed `realPhysicalDistributionError`, `ceil(z)` and `T+1`. Full PP payment, hmajor, hcoprime, hdistribution and hUpper remain outside the result.

The linked registry records manuscript revisions `9731290e8f53cffda44129906cde6a965eaa869b` and `ba6ec11d800eccc54406490631895e174de85766` with the same paper tree. A fresh read of the requested 9731290 manuscript lines 465–480 returned blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. No manuscript pin or parameters changed. External analytic assumptions remain at their inherited sources and verification statuses; no external theorem was implemented.

## Verification and next step

- `python3 docs/source-only/20261119-p4a5-hdensity-install-r6/bind_saved87.py`: exit 0; 16 source files matched, three staged provisional selections bound, 12 reachable sources added, zero conflicting selections in this restricted walk.
- Intermediate `stage_and_audit.py /workspace/scratch/cb6959cc4223/stage-r6` produced `IMPORT_AUDIT.json`. Then `python3 docs/source-only/20261119-p4a5-hdensity-install-r6/bind_t03_inputs.py` exited 0: 18 matching Lean sources, one historical version difference, one prior provisional selection bound, 17 reachable sources added, zero other conflicts. Final `stage_and_audit.py /workspace/scratch/cb6959cc4223/stage-r6b` produced `IMPORT_AUDIT_FINAL.json` and exited 0. Run in this order because the second binder updates the manifest. These are static checks, not Lean elaboration.
- Baseline declarations: Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. They are declarations only. `lake env lean /workspace/scratch/cb6959cc4223/stage-r6b/ImbalancedChen/P4AOriginalFiniteAll22FineDensity.lean` returned 127: `lake: command not found`. Lean/Lake/Elan and `.lake/packages`/`.lake/build` are absent. No actual elaboration, kernel replay, transitive-axiom check or finite certificate execution occurred; no CI or resource expansion was requested.
- Next: resolve the 55 currently visible missing imports and 46 provisional choices from the correct chain; inspect data-file sources and the final-reader/radial variants; verify exact package and toolchain availability before typechecking. Build and check the exact candidate and its actual closure in an existing permitted environment, then capture declarations, transitive axioms and finite replay logs. Static identity checks are not kernel acceptance.

Changed-file SHA-256 (excluding this report):

- `IMPORT_AUDIT.json`: `12ddd905c2e177985799772e68e4983b874248dfd2c6bcb31914281a2aa28793`
- `IMPORT_AUDIT_FINAL.json`: `9babe62fa1c96b8bf4a391f8e4571697890eb624c15bda00027bff4f5eb37ffd`
- `INSTALL_MANIFEST.json`: `a4d6f125595aabd2abd73adaec0e69b19cfa062f1cd393eade616eb78d1ef9bb`
- `REVIEWED_INPUT_EVIDENCE.json`: `14f275d5bdd76f3c95cf1982e9b5981a4fcd3bb5518ff4775ea29bd2375f79b2`
- `SAVED87_EVIDENCE.json`: `d760089cf9789e99e7510efb72a121338a5602fb2d6386bdd8d6e5b9430c1ab4`
- `bind_saved87.py`: `4656577677cb545e783c3ae9c17c9719a58cebcff9a6163e70b2a60c03ddb3cf`
- `bind_t03_inputs.py`: `32aadc2bbd0db58b22ade909dda5b094114c922c57824affa6c0b393552d2d34`
- `stage_and_audit.py`: `4712cdf8de1acaf35e8ec422e35958736b046088bdaceb39e2c115ca7029dd1a`
