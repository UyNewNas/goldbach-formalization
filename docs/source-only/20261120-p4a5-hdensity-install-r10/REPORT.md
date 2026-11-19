# P4A.5 same-ρ hdensity installation continuation r10

Parent `2de9b04a73959081ea84303a0f96bfbe005fad35`. The exact historical candidate `P4AOriginalFiniteAll22FineDensity.lean`, SHA-256 `1942060c36cde2fb609dce8d370d29fa10701c5e6ed75159416e1c51cb8df7e5`, and its theorem are unchanged. Two previously unresolved *actual literal imports* were installed as conditional source selections in a fresh isolated stage. Their bytes, lengths and direct imports match the same-chain G3 registry, but their compatibility with the complete target has not been established by Lean. No new mathematical theorem or proof body was added.

SOURCE_ONLY=true; COMPILED=false / UNCOMPILED; KERNEL_REPLAYED=false; TRANSITIVE_AXIOMS=NOT_CHECKED; FINITE_BODIES=UNEVALUATED; NEW_INDEPENDENT_PROOF_REVIEW=false. The historical independent review is source-only and is not a compilation or kernel receipt. No premise was newly proved or eliminated in this round.

## Frontier and exact provenance

G3 registry `docs/source-only/20261110-yellow-closure-10t/t05_all22_actual_density/G3_REGISTRY.json`, SHA-256 `c0da5890b26433b464fd52cb278e8987b41b70873666bd23edd9bcdbdf63886d`, explicitly records both source paths, install paths, byte lengths, SHA-256 values and ordered direct imports. The actual previous stage's importing module and hash are recorded in `G3_FRONTIER_EVIDENCE.json`; both importers were from the prior isolated stage, not checkout root:

- `P4AOriginalEarlyFifthOwner` imports `P4AOriginalNewFifthMean`: `9e4af05f4e0ab547e622a31a3209a2dd91f2bec990b082f4ee82d7a18c97c890`, 8,916 bytes; direct imports `P4AOriginalNewFifthOwners`, `P5OriginalArchiveCommonRawMean`.
- `P4AOriginalEarlyHistoricalFloors` imports `P4AOriginalNewFifthPhysical`: `39e7fc854c590a34bf20cfeb02ba608aff70772359a72c3ea30804c4adab431e`, 15,749 bytes; direct imports `P4AOriginalNewFifthIntegral`, `P4AOriginalFull87ActualSavedEndpoint`, `P4AOriginalFull87JointPhysicalBudget`.

`bind_g3_frontier.py` verifies these registry/source pairs and appends them to the inherited hash-checked install manifest; it checks that each appeared in the previous unresolved set and records all direct importers. `stage_and_audit.py` installs those exact bytes and audits the literal import graph. The resulting stage has 181 staged files, 642 visited project modules and 60 missing project modules, versus 179, 640 and 59 respectively before this round; 154 external import names remain. The two prior missing names disappear, but their imports expose three new missing names: `P4AOriginalNewFifthOwners`, `P4AOriginalNewFifthIntegral`, `P4AOriginalFull87JointPhysicalBudget`. This is not a closed import graph. The two new selections are conditional in addition to the 56 prior provisional/conditional selections recorded in r8. Source presence, source hash matching and literal import resolution do not establish namespace correctness, elaboration, compatible variants, package identity, .olean compatibility or kernel acceptance.

The stage was also populated with the 188 registered G3 members using r9's verifier from the same range-reconstructed sparse archive. The stdout receipt is byte-identical to r9 `G3_ORIGINAL_MEMBERS_RECEIPT.json` (SHA-256 `ca484f66ba9efdc89fbf7b1692cac17ccee9ff3825a546870faa9799c2d3fb5f`); the verifier hashes all selected NPZ and NPY members. The outer release archive's full SHA and the old G3_INPUTS.zip SHA remain unverified, and data checks do not evaluate finite certificates. Source/data staging and reproduction limitations are as in r9.

## Claim and boundaries

The unchanged candidate is source-reviewed to target `∀ δ > 0, ∀ᶠ N, Even N → physicalDensitySum (Q δ N) (ρ δ N) ≤ (currentK + δ) * (singularSeries N / Real.log N)` on the same Q/ρ as its inherited Fine witnesses. The predecessor is invoked once at `densityReserve/2`, with β/k chosen before the common N₀ and constant Q/ρ in δ. HighAtoms, strict support, compiler expense and finite counting stay on those witnesses; the correction is retained and its existing nonnegativity theorem uses the same F, N, cap, w, z and w ≤ z, without a second compiler payment. These are inherited source-review statements, not claims of new compilation or an accepted theorem. The real finite count retains the complete signed distribution error, `ceil(z)` and `T+1`; complete PP payment and hUpper remain open. No P4B.4 signed PP hypothesis was introduced.

The manuscript pin `9731290e8f53cffda44129906cde6a965eaa869b` again yields `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, consistent with the inherited pin; lines 465–480 explicitly refer to the same ρ and strict support parameter. External analytic inputs, precise statements, source/version, normalizations and statuses remain as in prior registries; no new external input or proof is introduced. Declared pins remain Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`; these are not receipts of installed tools. c/K are unchanged.

## Commands, outcomes and next steps

- `python3 docs/source-only/20261120-p4a5-hdensity-install-r10/bind_g3_frontier.py > docs/source-only/20261120-p4a5-hdensity-install-r10/G3_FRONTIER_EVIDENCE.json`: exit 0; registry byte/hash/import identity and previous literal importers verified. Python 3.12.14.
- `python3 docs/source-only/20261120-p4a5-hdensity-install-r10/stage_and_audit.py /workspace/scratch/cb6959cc4223/stage-r10 > docs/source-only/20261120-p4a5-hdensity-install-r10/IMPORT_AUDIT.json`: exit 0; source-only literal audit. The fresh stage retained the selected List/namespace overlays from r8.
- `python3 docs/source-only/20261120-p4a5-hdensity-install-r9/stage_original_npz.py --outer-zip /workspace/scratch/cb6959cc4223/paper-zip-index.sparse --stage /workspace/scratch/cb6959cc4223/stage-r10 > /workspace/scratch/cb6959cc4223/r10-fixtures-receipt.json`: exit 0; 188 files present, receipt hash matches r9. Stage contents are ephemeral and large fixture files are not committed.
- `lake env lean /workspace/scratch/cb6959cc4223/stage-r10/ImbalancedChen/P4AOriginalFiniteAll22FineDensity.lean`: exit 127, `/bin/bash: lake: command not found`. Lean/Lake/Elan are unavailable on PATH; the pinned toolchain and package closure are not installed. No Lean elaboration, finite evaluation, kernel replay, transitive axiom check, resource expansion, CI or user machine was used.
- Next, individually bind the three newly exposed imports to their recorded exact sources and continue the real import closure, respecting distinct source variants and their conditions. In an existing permitted environment containing the pinned Lean and packages, compile the exact source closure, inspect generated declarations and transitive axioms and replay finite bodies; independently finish signed error/PP payment and the remaining assembly inputs. Do not equate source staging with same-ρ density kernel acceptance.

Changed-file SHA-256 (excluding this report):

- `bind_g3_frontier.py`: `9e08ec22c38aa9da8e85c4c0eb6a11cc3f3eef7abef6a8adc8c73eb10d6bfe75`
- `stage_and_audit.py`: `4712cdf8de1acaf35e8ec422e35958736b046088bdaceb39e2c115ca7029dd1a`
- `INSTALL_MANIFEST.json`: `7b97377ec585ef1b041677c846f4386f38c7604d2e6700dc1f101998aa61cdcb`
- `IMPORT_AUDIT.json`: `98d24784df8a95a56c66b40c5b53cf8930bb80d8fd173f091caad51bcb16fe91`
- `G3_FRONTIER_EVIDENCE.json`: `e4623adf5383ea5ef94aeefa7e742d6e9cbd60275cbf11f364bcb75920b44928`
