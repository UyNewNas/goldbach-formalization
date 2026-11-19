# P4A.5 same-ρ hdensity installation continuation r14

Parent `59a13ec90afdef851f9434ba319b11b2e288aaf9`. The 664 project sources reached by r13's literal import audit were merged into one new external directory: 202 came from its exact selected stage and 462 from the checkout. Every input was hash-checked against the r13 audit before copying, and every output was rehashed; the three declared project configuration files were also copied and hash-checked. The directory retains the exact selected bytes, including the unresolved gamma selection. The r9 verifier separately installed all 188 hash-checked G3 members there. This is a **partial source/data stage**, not an installed or compiled dependency closure. The historical candidate remains SHA-256 `1942060c36cde2fb609dce8d370d29fa10701c5e6ed75159416e1c51cb8df7e5`; no Lean declaration, proof body, premise, or analytic input was changed.

SOURCE_ONLY=true; COMPILED=false / UNCOMPILED; KERNEL_REPLAYED=false; TRANSITIVE_AXIOMS=NOT_CHECKED; FINITE_BODIES=UNEVALUATED; NEW_INDEPENDENT_PROOF_REVIEW=false. The earlier independent source review is not a kernel receipt.

## Runtime data frontier

The new `RUNTIME_WITNESS_AUDIT.json` follows five actual Lean source loaders, checks each selected source SHA against both the r13 reached source and the T06 v3 exact install manifest (a separate source-only manifest), derives the exact names from those source literals/index ranges, and matches each to the manifest's recorded consuming module, path, byte count and SHA. The G6 entry is additionally checked against this chain's own `G6_RELEASE_INPUT_REUSE.json`. These five selected source bytes match the T06 v3 source records; this is not a claim that all T06 variants or proof objects are compatible with P4A.5. With the merged directory as working directory, all **105** enumerated witness files are absent, with **632,957,612** total bytes recorded by the manifest:

- `P2OriginalSaving15RadialArchive`: one radial JSON at `../goldbach-research/` (77,770,486 bytes).
- `P2OriginalSaving17DescendingArchive`: 15 descending-cell JSONs at `../goldbach-research/` (140,255,702 bytes).
- `P2OriginalSaving18UnequalArchive`: 30 geometry/moment JSONs at `../goldbach-research/` (177,946,884 bytes).
- `P2OriginalSaving20FirstFailureIntegral`: 58 geometry/moment JSONs at `../goldbach-research/` (236,787,809 bytes).
- `P4AOriginalThirdFallbackArchive`: `ImbalancedChen/G6_ORIGINAL_WITNESS.json` next to its actual source (196,731 bytes; registered SHA `0401062c690c7993fd34722dca97d3c504f3e72f83d87659f597d135490d50a5`).

The four relative paths are relative to the compiler's working directory; the G6 loader uses the Lean source file's own directory. The precise checked condition is the merged stage root as cwd. These 105 missing files are in addition to the 188 G3 members, not a substitute for them. This is a focused audit of five loaders, not a comprehensive proof that there are no other file reads, nor an evaluation of any witness.

The original G6 release member is recorded at v2026.10.10, `chen-numerical-evidence-20261010-renewal-v2/goldbach-research/third-prefix-fallback-pair-20261009.witness.json`. A `curl -fsSL --max-time 45 -r 323064482-323164481` request to the registered release URL was started, but network approval was cancelled before a decision and no file/exit code was returned. The witness was not installed; no asset, member hash or numerical result is claimed from that attempt. The full release archive SHA is metadata only.

## Scope and unresolved boundaries

The unchanged historical candidate targets `∀ δ>0, ∀ᶠ N, Even N → physicalDensitySum (Q δ N) (ρ δ N) ≤ (currentK+δ)*(singularSeries N/Real.log N)`. Its prior source review records one Fine invocation at `densityReserve/2`, same β/k, δ-independent Q/ρ, the inherited common N₀, the actual correction and same F/N/cap/w/z/w≤z nonnegativity theorem, and compiler expense paid once. These are inherited source statements, not newly compiled claims. The real finite count retains the complete signed distribution error, `ceil(z)` and `T+1`; full PP, remaining assembly inputs and hUpper remain open. No P4B.4 signed PP hypothesis was added to density.

The r13 literal graph still has 70 unresolved project imports and 157 external names. The existing G3 registered edge conflict between original gamma SHA `6917658f287ac043bfebca18c7775efc145db71796a2ee71ae03e0e16c2e625a` and conditionally staged v3 repair SHA `fb0e5a57a1123f2ef778c36f1ee29820a0db138d8cc0d862e244eec5d2b33130` is unchanged and unvalidated. Some existing sources contain local/global resource options, as inventoried in r13; no such options were executed, changed or authorized beyond the user's limits here. Stage source/data copying does not resolve any of these issues.

The manuscript revision `9731290e8f53cffda44129906cde6a965eaa869b` has `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, consistent with the recorded chain. The stage's copied configuration declares Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`; these declarations are not installed-version receipts. No manuscript pin, c/K constant, external-input scope or status changed; exact assumptions and sources are inherited from prior registries.

## Checks and next action

- Python 3.12.14. `python3 docs/source-only/20261120-p4a5-hdensity-install-r14/assemble_reachable_sources.py --stage /workspace/scratch/cb6959cc4223/stage-r13 --destination /workspace/scratch/cb6959cc4223/stage-r14-merged > docs/source-only/20261120-p4a5-hdensity-install-r14/SOURCE_MERGE_RECEIPT.json` exited 0. It checks the exact r13 import-audit hash and all 664 observed source hashes, stages 664 files plus three exact configuration files, and checks each copied hash. It does not install packages, .olean files, other witnesses or the unvisited graph.
- The r9 `stage_original_npz.py` ran against the existing sparse release fragment and new merged stage, exit 0; stdout SHA `ca484f66ba9efdc89fbf7b1692cac17ccee9ff3825a546870faa9799c2d3fb5f` matches r9's receipt for 188 members. The sparse fragment is not the complete release archive and no finite certificate was evaluated.
- `python3 docs/source-only/20261120-p4a5-hdensity-install-r14/audit_runtime_witnesses.py /workspace/scratch/cb6959cc4223/stage-r14-merged > docs/source-only/20261120-p4a5-hdensity-install-r14/RUNTIME_WITNESS_AUDIT.json` exited 0; rerun output compared byte-identical. The first attempt exited 1 because its regex accidentally crossed a newline in an elaborator declaration; inspection identified the extra match, and restricting it to a single line fixed the inventory. This Python issue was not a Lean diagnostic. `py_compile` of both scripts exited 0.
- From the merged directory, `lake env lean ImbalancedChen/P4AOriginalFiniteAll22FineDensity.lean` exited 127: `/bin/bash: lake: command not found`. Lean/Lake/Elan are unavailable on PATH and `.lake/packages`/`.lake/build` are absent. The existing shell `ulimit` reported stack 8,192 KiB, open files 16,384, CPU time/virtual memory unlimited; no limit was changed. No Lean elaboration, finite-body evaluation, axiom inspection, CI or user-machine access occurred.
- Next: obtain and verify the exact 105 recorded raw witnesses at the correct source/cwd locations, plus any other actual loader inputs discovered by a complete audit; do not regenerate their numerical proofs. Resolve the 70 visible missing imports, gamma choice and all conditional variants, and reconcile existing source-level resource options with the no-expansion restriction. In a permitted existing pinned environment typecheck the exact actual closure and candidate, check transitive axioms and replay finite bodies. Separately finish signed error payment and assembly inputs. This packet does not provide full PP/hUpper.

Changed-file SHA-256 (excluding this report):

- `RUNTIME_WITNESS_AUDIT.json`: `4f8a4b81fdfa7ccdfd98add8429c57dac45750d9789e576471708003db42b369`
- `SOURCE_MERGE_RECEIPT.json`: `6eda93a3dcfad09f56d8cdf6051bc444e7afc9621ab5fecadded2cb03bb17092`
- `assemble_reachable_sources.py`: `170b092f66336585ef89943b451a2865a9a18f3ab33072ee2b756117dc5fb850`
- `audit_runtime_witnesses.py`: `09edf336716463fdec1cd823b7f2ff5762fdee6d2a26ffb672a23d149512870a`
