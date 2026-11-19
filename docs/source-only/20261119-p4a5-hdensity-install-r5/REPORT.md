# P4A.5 hdensity installation continuation r5

Parent `3399e9f51bc54ab46ea9270052c12e7e58768470`; unchanged candidate `P4AOriginalFiniteAll22FineDensity.lean` SHA-256 `1942060c36cde2fb609dce8d370d29fa10701c5e6ed75159416e1c51cb8df7e5`. SOURCE_ONLY; COMPILED=false; KERNEL_REPLAYED=false; TRANSITIVE_AXIOMS=NOT_CHECKED; finite proof bodies UNEVALUATED. No mathematical proof body or theorem statement was changed. The existing independent review is the historical source-only review; there is no new independent review or green promotion.

## This round: recover a missing actual dependency

The bank registry linked by the candidate's Fine/high registry chain identifies its remote reused dependency `P4AOriginalFull87HistoryCore` at `be2efd01c561080672e6c0ad0ba21638837afe4c:docs/source-only/20261103-full87-common-history/P4AOriginalFull87HistoryCore.lean`. This module was an actual missing import of `P4AFallbackCompactEndpointCover` in r4 and is opened by the candidate. It was recovered from that exact Git tree, with byte count 7227, 164 lines, SHA-256 `cad88ca9f018acf3ae3e78c203403f15b0e4f8089bc1d7dc1394dfc15b575c77` and Git blob `458a67483f57fba768d06acc431a27a386bf9975`, all matching the bank registry. Its actual imports are `P4AOriginalFull87SourceDictionary` and `Mathlib.MeasureTheory.Integral.DominatedConvergence`.

The dictionary is also absent from the baseline tree; its source and two direct source inputs were recovered from the same fixed Git tree, matching the `20261102-resume-30r/full87_source_history/REGISTRY.json` SHA-256 bindings. The dictionary's remaining two direct imports already exist in the checkout and match the registry bytes. The recovered remaining-eighth source then exposes three registered direct source inputs; the recovered H3 semantics source exposes the H3 literal input. These four were likewise retrieved from the same pinned Git tree and checked against their original source registries. In total eight exact Git source files were added to this packet and the isolated stage. No existing source or mathematical claim was altered, no root production file overwritten, and no formal proof completion follows from this installation work. `HISTORY_EVIDENCE.json` records the origins, hashes, actual imports and chain checks.

The updated static stage has 140 files, with 597 project modules visited, 35 unresolved project imports, 151 external module names, and 50 provisional or conditional selections. The missing count does not measure proof progress and can increase as the import walk reaches additional sources. This line-based walk does not certify all Lean parsing, data files, installed packages, `.olean` identities, source compatibility or transitive closure. The v3 gamma and radial variants remain separately recorded as unresolved choices.

## Exact theorem and scope

The unchanged candidate intends `∀ δ>0, ∀ᶠ N, Even N → physicalDensitySum (Q δ N) (ρ δ N) ≤ (currentK+δ)*(singularSeries N / Real.log N)`. Its source calls the Fine/cofinal predecessor once at `densityReserve/2`, and delta-constant Q and ρ use the same β/k and common N₀. The actual correction remains in the inherited upper; the nonnegativity call uses the same F, w, z, N and cap=N, and compiler expense is not paid again. This is an existing, source-reviewed claim, not a newly elaborated result. The finite count retains the complete signed `realPhysicalDistributionError`, `ceil(z)` and `T+1`; full PP payment and full hUpper remain open, as do the other assembly inputs.

The chain registry records manuscript revisions `9731290e8f53cffda44129906cde6a965eaa869b` and `ba6ec11d800eccc54406490631895e174de85766` with the same paper tree. A fresh read of the requested 9731290 manuscript lines 465–480 returned blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. No manuscript pin or parameters were changed. No new external mathematical input was introduced; prior external input declarations and their statuses remain governed by existing registries.

## Checks and next step

- `git show be2efd01c561080672e6c0ad0ba21638837afe4c:<registered-path>` and local byte comparisons: eight recovered files matched the named Git tree, including the registered SHA-256 and blob for HistoryCore. The direct import list was checked against the source registry.
- `python3 docs/source-only/20261119-p4a5-hdensity-install-r5/bind_history.py`: exit 0; verifies the registry chain, HistoryCore SHA/blob/length, source dictionary identity and direct imports, and the selected subsequent source hashes.
- `python3 docs/source-only/20261119-p4a5-hdensity-install-r5/stage_and_audit.py /workspace/scratch/cb6959cc4223/stage-r5-final2 > docs/source-only/20261119-p4a5-hdensity-install-r5/IMPORT_AUDIT.json`: exit 0; this is static source/path/hash checking only.
- Baseline declarations: Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. They are declarations, not locally installed version receipts. `lake env lean /workspace/scratch/cb6959cc4223/stage-r5-final2/ImbalancedChen/P4AOriginalFiniteAll22FineDensity.lean` returned 127, `lake: command not found`. Lean/Lake/Elan and `.lake/packages`/`.lake/build` were absent. No real elaboration, kernel replay, transitive-axiom check or finite certificate execution occurred; no CI or resource increase was requested.
- Next: resolve the remaining 35 imported modules and 50 provisional selections, including exact v3 gamma/radial versions, and verify data and pinned packages. In an existing permitted environment with the actual pinned toolchain, install and typecheck the exact candidate closure and then inspect the generated type and transitive axioms. Record exit status and logs.

Changed-file SHA-256 (excluding this report):

- `HISTORY_EVIDENCE.json`: `5468653419e859c7fe4aa4a1e53956fa4255d1f897d05957be40afa649398a38`
- `IMPORT_AUDIT.json`: `bc936b67abf3b7b9b35897e2b99fe265eef7abb29673425d87b185d1c1c9d9eb`
- `INSTALL_MANIFEST.json`: `812ed2a2998d91eb87f1a808ba750ef731dfb3240a2f1ad15119471f0ac8b339`
- `bind_history.py`: `b180e492f05a3772b6900b076032b42e55b6726095d2b58ee7f79f6d1c92df7e`
- `stage_and_audit.py`: `4712cdf8de1acaf35e8ec422e35958736b046088bdaceb39e2c115ca7029dd1a`
- `pinned/P4AOriginalFull87HistoryCore.lean`: `cad88ca9f018acf3ae3e78c203403f15b0e4f8089bc1d7dc1394dfc15b575c77`
- `pinned/P4AOriginalFull87SourceDictionary.lean`: `dbfadaa879e08c2c3ecb270f699b84f3f9ac7b0b044ba96be8046da4a73c501c`
- `pinned/P4AOriginalRemainingEighthSources.lean`: `cd0eeb7e27f7596c30da8576a065e94ae45d3aeb6c7e5dcde637709d9aced564`
- `pinned/P4AOriginalFirstFailureH3SourceSemantics.lean`: `744b58311fb693e0751d7c7d18bf8f60c01111b3f6e5026244cc36da0c208664`
- `pinned/P4AOriginalAscendingFourteenAffineSource.lean`: `e5e7c88c94e3debd43ad523ecdcafcf3878852414f473037328761b0d73e5aaa`
- `pinned/P4AOriginalSeed7Unequal15Literal.lean`: `13cffcaf2b85775e9bd819401ae95b7b04708cb99ca7a6e11ba97bf721226b63`
- `pinned/P4AOriginalFirstFailureH5H7Literal.lean`: `c075ee740cadd6a6d2b4cd67fcd52825cad1a686da7db4380a527708dd57f852`
- `pinned/P4AOriginalFirstFailureH3Literal.lean`: `2154c6be4be885c15ec779f232616e3506add090d6370f758bb4c6b1ecc91f9f`
