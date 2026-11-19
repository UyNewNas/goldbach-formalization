# P4A.5 same-ρ hdensity installation continuation r16

Parent `0c650d2735effe90dd2887cec0472661c3020d6e`. On the actual r13 literal import frontier, 47 missing project modules were found with (i) at least one actual importer whose exact source SHA and import edge match the separate T06 v3 source-only manifest, and (ii) a local source matching that manifest's exact SHA-256, Git blob, byte length and literal imports. They were staged unchanged as **conditional selections**, not accepted objects. The new reached `P2OriginalSaving19Archive` loader also has 26 original witness files; all 26 were recovered from the author's release, hash/size/CRC-checked, placed at its actual cwd-relative paths, and independently reread and hashed. This is installation evidence, not proof evaluation.

The historical candidate `P4AOriginalFiniteAll22FineDensity.lean` remains SHA-256 `1942060c36cde2fb609dce8d370d29fa10701c5e6ed75159416e1c51cb8df7e5`; no Lean statement, proof body, mathematical premise, external analytical input, pin or parameter was changed. SOURCE_ONLY=true; COMPILED=false / UNCOMPILED; KERNEL_REPLAYED=false; TRANSITIVE_AXIOMS=NOT_CHECKED; FINITE_BODIES=UNEVALUATED; NEW_INDEPENDENT_PROOF_REVIEW=false. Earlier independent source review is not a kernel receipt.

## Exact source selection and dependency frontier

`FRONTIER_EVIDENCE.json` lists each selected module, source path, exact SHA/blob/length, observed imports, T06 source origin and selection, and *all* actual r13 importers with a flag identifying which parent hash and edge match T06. `bind_exact_frontier.py` only stages a source if it was actually missing in r13, has at least one such exact parent edge and a unique local exact byte match, and its direct imports and blob also match the T06 registry. The registry SHA is `21ee9d56c5891d6929e4ce1be045a21e6adbda0c372af7bc9a84575b113ff3c9`; its own status is source-only, `compiled=false`, `kernel_verified=false`, and it belongs to a different full87 target. Exact equality is evidence for byte selection only: it is **not** Lean compatibility, transitive closure, or authorization to substitute other T06 variants.

Of the 70 r13 missing modules: 47 meet the condition above; nine have no T06 file record, 12 lack an exact local source for that record, and two lack an exact matched T06 parent edge. These categories describe the r13 frontier only. Rewalking after the 47 selections resolves those 47 names but discovers 64 new ones; the current literal audit has 250 staged files, 715 visited project modules, 87 missing project imports and 163 external names (previously 203, 664, 70 and 157). `IMPORT_AUDIT.json` records their exact names and importers. The restricted G3/T05 registered-edge audit remains 35 match / zero missing / one mismatch; gamma original `6917658f…` versus conditional v3 repair `fb0e5a57…` is still not resolved.

`RESOURCE_DIRECTIVES.json` is a line-leading textual inventory on the current reached sources, with exact source hashes: 21 files and 731 matches, including 218 `maxHeartbeats 0` text lines. Comments are not lexed and other forms may be missed. This scan is not Lean parsing or an execution/resource measurement; no listed option was executed or increased. Existing resource restrictions must be respected before compilation.

## Saving19 original witnesses

The newly reached `P2OriginalSaving19Archive` source is SHA-256 `b8821bbc996d6fdbc19fd359b1be9dd4be181064f7fe1b2f36b8b5a27996a9b6`, matching its T06 source record. Its two actual literal loaders name original geometry and moment JSONs for indices 00–12. `audit_saving19_inputs.py` derives those names from the exact loader source and matches them to the 26 T06 per-file source records: `SAVING19_BEFORE.json` records 26 missing; `SAVING19_INSTALLED_AUDIT.json` independently reopens all files and records **26 match**, 80,189,086 bytes. These records use the isolated cwd `/workspace/scratch/cb6959cc4223/p4a5-r16-work/lean`, with original loader files in its task-specific sibling `../goldbach-research/`.

The registered release is `https://github.com/UyNewNas/chen-imbalanced-semiprimes/releases/download/v2026.10.10/chen-numerical-evidence-20261010.zip`. The required original ZIP range is inclusive `151858969-171885060`; the downloaded 20,026,092-byte fragment has SHA-256 `6f6d1fc88d164ebdc152e072e31f5efee13700184ba94f1bcec4536e08d8622f`. `stage_saving19.py` checks the prior source/data audit, central directory, each original local header, decompressed size, CRC and recorded per-member SHA before writes, then rechecks while writing; `SAVING19_STAGE_RECEIPT.json` records all 26 identities. The full ZIP was neither downloaded nor hashed. The same isolated workspace also reinstalled the prior 105 witnesses and 188 G3 NPY members; the five-loader independent r14 audit again reports 105 match. This does not assert that newly reached modules have no other unrecognized file inputs or that the stored data prove their claims. No Lean numerical certificate or finite proof body was executed. All raw data/ranges are ephemeral, not committed to Git.

## Exact density scope and boundaries

The inherited candidate targets `∀ δ>0, ∀ᶠ N, Even N → physicalDensitySum (Q δ N) (ρ δ N) ≤ (currentK+δ)*(singularSeries N/Real.log N)`. Historical source review records a single Fine invocation at `densityReserve/2`, same β/k and common N₀, δ-independent Q/ρ, inherited HighAtoms/support/compiler/finite counting, the actual correction retained with nonnegativity at the same F/N/cap/w/z and w≤z, and no second compiler payment. This is prior source scope, not a new compiled theorem. Real finite counting retains the complete signed distribution error, `ceil(z)` and `T+1`; complete PP, remaining assembly inputs and hUpper are not supplied. No P4B.4 signed PP hypothesis was inserted into density.

Manuscript revision `9731290e8f53cffda44129906cde6a965eaa869b` has `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, consistent with the recorded chain. The declared pins remain Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`; these are not installed-version receipts. The inherited c/K, external inputs, precise statements, normalizations, applicability and statuses remain unchanged in the predecessor registries.

## Checks and next action

- Python 3.12.14. `bind_exact_frontier.py > FRONTIER_EVIDENCE.json` exited 0; a repeat compared byte-identical. `stage_and_audit.py /workspace/scratch/cb6959cc4223/stage-r16 > IMPORT_AUDIT.json`, the G3/T05 registered-edge audit and the textual resource audit each exited 0. None executes Lean.
- `assemble_reachable_sources.py --stage /workspace/scratch/cb6959cc4223/stage-r16 --destination /workspace/scratch/cb6959cc4223/p4a5-r16-work/lean` exited 0: 715 reached source files (250 from stage, 465 from checkout) and three fixed project config files were hash-checked before and after copying. `SOURCE_MERGE_RECEIPT.json` does not certify full source/data/package closure. Reinstalling prior r9 G3 and r15 five-loader data exited 0 with receipts identical to earlier rounds; the prior independent audit again reported 105 match.
- `stage_saving19.py --stage /workspace/scratch/cb6959cc4223/p4a5-r16-work/lean --range-dir /workspace/scratch/cb6959cc4223 --index /workspace/scratch/cb6959cc4223/paper-zip-index.sparse --groups saving19` exited 0; a repeat produced identical receipt. `audit_saving19_inputs.py` independently reported 26 match; repeated output matched byte-for-byte. Python scripts passed `py_compile`. These are input identity checks, not a numerical replay.
- From the merged isolated cwd, `lake env lean ImbalancedChen/P4AOriginalFiniteAll22FineDensity.lean` exited 127: `/bin/bash: lake: command not found`. Lean/Lake/Elan and the pinned package closure are unavailable. No Lean elaboration, resource increase, transitive-axiom check, finite certificate evaluation, CI or user-machine access occurred.
- Next: individually verify remaining actual source variants and the 87 visible missing imports, discover and stage other actual data readers, resolve gamma and resource options within the no-expansion boundary, and typecheck the exact closure/candidate only in an existing permitted pinned environment. Then check transitive axioms and replay finite bodies. Separately complete signed error payment and the other assembly hypotheses; full PP/hUpper remain open.

Changed-file SHA-256 (excluding this report):

- `FRONTIER_EVIDENCE.json`: `103d9437926624f29be435884c774c61c89b0c365fb94edabaed9b8a8a062398`
- `IMPORT_AUDIT.json`: `7114b4ab2c0284950265f98902afc1e213fd80c081f73fc59d4e1949bc5cfed3`
- `INSTALL_MANIFEST.json`: `f46949762fdbce956241b56b979070c3abc20a7f89987f07891a021e4752276d`
- `REGISTERED_EDGE_AUDIT.json`: `3717e9eaaa8d7f2abbd451e96ac07c2a7093c6c9e4d33b526590a2db129d3319`
- `RESOURCE_DIRECTIVES.json`: `9af2b08ce9f6ed1bc04f9cb4885de96a024d44a2ed7489e9b1e52c11f48ed392`
- `SAVING19_BEFORE.json`: `20eaa930b2d105c2c26f41563849045c6befbf619936b4c49546d1da48a1a69c`
- `SAVING19_INSTALLED_AUDIT.json`: `13ae753b200ff99b721b6322157cc9c6d430919ea95184379edce0ea7f0c180f`
- `SAVING19_STAGE_RECEIPT.json`: `84a51e9720cc3e69fb8de7fdcc4089d47beedf8fef592b18b268e3a1d5c3205a`
- `SOURCE_MERGE_RECEIPT.json`: `9a05cb27c94d9ef0acc554a84f288bb8a54a8f60822307567ab5e8aca9ce6d89`
- `assemble_reachable_sources.py`: `4cd52ed5c7380abeb78749bcb67fb61b0c55592cf1e25c37dda754d96d21c7d9`
- `audit_registered_edges.py`: `a384f87d2e8dc232d4dcb855dc780c3f9da41f0f16328353e082e8027a908b5c`
- `audit_resource_directives.py`: `ad673d6fb64f36481483ab2fae7f5810f050d4a88f014bb3b4452084f0e7e761`
- `audit_saving19_inputs.py`: `7673df7efe319f855c51c336eea34e82f81d96985f7782c647a63ff96cde4daf`
- `bind_exact_frontier.py`: `2434d086b06b40e9207fc278f1b1dca2aef2f122463326ef8f8f9b7d6386738b`
- `stage_and_audit.py`: `4712cdf8de1acaf35e8ec422e35958736b046088bdaceb39e2c115ca7029dd1a`
- `stage_saving19.py`: `f5a3cef78e4bdb1d17e94301423aad637a261393f97ef111726f25a3b134cbcb`
