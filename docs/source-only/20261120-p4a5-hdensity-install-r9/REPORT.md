# P4A.5 same-ρ hdensity installation continuation r9

Parent: `8b4d8255630a1767e9f1477d8b98315f13914e29`. This packet adds no Lean declaration and does not change the previously reviewed candidate `P4AOriginalFiniteAll22FineDensity.lean` (SHA-256 `1942060c36cde2fb609dce8d370d29fa10701c5e6ed75159416e1c51cb8df7e5`). It makes a previously missing input available in the isolated source stage: all 94 original NPZ blocks and their 188 unchanged NPY members match the hashes and sizes registered by `G3_FIXTURES.json`; the members have actually been written beside the selected Lean data module and independently reread and hashed. This is input identity and placement evidence, not evaluation of finite certificates.

SOURCE_ONLY=true; COMPILED=false (UNCOMPILED); KERNEL_REPLAYED=false; TRANSITIVE_AXIOMS=NOT_CHECKED; FINITE_BODIES=UNEVALUATED; NEW_INDEPENDENT_PROOF_REVIEW=false. The historical independent source review remains historical, not a Lean receipt. No theorem, proof body, external analytic input, pin, or parameter changed.

## Provenance and reproducibility

The manuscript repository at revision `9731290e8f53cffda44129906cde6a965eaa869b` has `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, matching the pin recorded in the inherited saved87 chain; see r8 for the second manuscript revision and source scope. The pinned manuscript repository's README points to the author's [v2026.10.10 numerical evidence release](https://github.com/UyNewNas/chen-imbalanced-semiprimes/releases/tag/v2026.10.10). Its `chen-numerical-evidence-20261010.zip` asset is reported by release metadata as 323,605,374 bytes, SHA-256 `8f1bdf63e1aa972256b2422f824f3d177617b31bf41b6a2b8cf29b0562647ad1`. **The full release archive was neither downloaded nor hashed.** Only its central directory and the range containing the 94 required NPZ files were retrieved. The old, separately recorded `G3_INPUTS.zip` (32,285,020 bytes, SHA-256 `5903eadd154aa06797a22a2b01399c6255b25d67d688a283630c56ef33f0c328`) was not located or reconstructed and its archive hash was not verified.

The registry-bound `G3_FIXTURES.json` SHA-256 is `f79c794c614af8b4aec78ca4601f9b6e6d58f3e47d72b72eac98f94003cca184`; the selected staged Data module SHA-256 is `5fc51f4622c04ff0d2ce69d87e19d7b0a1cb20ccd48295309e24aab6a4879df4`. The receipt lists each source NPZ and its manifest hash; the existing r8 `G3_EVIDENCE.json` lists all member names, hashes and lengths. Individual NPZ hashes and all individual members' hashes were checked before writing. The member total is 423,244,864 bytes. The final Reader selection remains conditional, exactly as in r8; distinct old and final Reader variants were not conflated.

Reproduction in a permitted environment, from repository root, with an isolated stage such as `$stage` and scratch directory `$scratch` (the two downloaded fragments are not a complete ZIP and must not be represented as one):

```sh
python3 docs/source-only/20261119-p4a5-hdensity-install-r8/stage_and_audit.py "$stage" > "$scratch/import-audit.json"
url=https://github.com/UyNewNas/chen-imbalanced-semiprimes/releases/download/v2026.10.10/chen-numerical-evidence-20261010.zip
curl -fsSL --max-time 25 -r 323421542-323605373 "$url" -o "$scratch/central"
curl -fsSL --max-time 60 -r 222771322-252706000 "$url" -o "$scratch/blocks"
python3 - "$scratch" <<'PY'
import pathlib, sys
p = pathlib.Path(sys.argv[1])
central, blocks = (p/'central').read_bytes(), (p/'blocks').read_bytes()
assert len(central) == 183832 and len(blocks) == 29934679
with (p/'partial.zip').open('wb') as f:
    f.truncate(323605374)
    f.seek(323421542); f.write(central)
    f.seek(222771322); f.write(blocks)
PY
python3 docs/source-only/20261120-p4a5-hdensity-install-r9/stage_original_npz.py --outer-zip "$scratch/partial.zip" --stage "$stage" > "$scratch/receipt.json"
```

Observed fragment SHA-256: central `9e2c69c770f7760fc41a060829116c8abdffdd4e36a198e99baba24ef458f900`, blocks `767a0012c6c4b147e28521973291893a120d2050cb9101da8e560b36020e721d`. The verifier depends on exact per-NPZ and per-member hashes, not on trust in this partial archive's whole-file hash. Each ZIP member is read through Python's CRC checking as well. The full release asset hash is metadata only. No large data are committed to Git; stage bytes are ephemeral.

## Exact claim and boundary

The unchanged source candidate is intended to supply, for every δ > 0 and sufficiently large even N, `physicalDensitySum (Q δ N) (ρ δ N) ≤ (currentK + δ) * (singularSeries N / Real.log N)`. Its historical source review records one Fine/cofinal invocation with `η = densityReserve/2`, shared β/k and N₀, Q/ρ independent of δ, inherited HighAtoms, strict support, compiler cost and finite counting. The same F, w, z, N, cap and w ≤ z feed the correction nonnegativity theorem; actual correction is retained and u_c is not paid twice. This describes the existing candidate, not a newly proved or compiled claim. Real finite counting still contains the complete signed `realPhysicalDistributionError`, `ceil(z)` and `T+1`. Full PP, hUpper and remaining assembly obligations are not supplied here; no signed PP hypothesis was introduced as a density premise.

External analytic inputs, exact normalizations and original sources retain the statuses of the prior reports and registries; this packet neither proves nor changes them. Fixed declared versions remain Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. These are manifest declarations, not installed-version receipts. The c/K values remain those recorded in the predecessor chain.

## Verification and next step

- Python 3.12.14; `stage_and_audit.py /workspace/scratch/cb6959cc4223/stage-r9` exited 0. The inherited literal-import audit remains 179 staged sources, 59 unresolved project imports and 56 provisional/conditional selections; this is not Lean elaboration.
- `stage_original_npz.py --outer-zip /workspace/scratch/cb6959cc4223/r8-incorrect-fixture.zip --stage /workspace/scratch/cb6959cc4223/stage-r9` exited 1, `missing or duplicate original block`; no fixture directory was created.
- `stage_original_npz.py --outer-zip /workspace/scratch/cb6959cc4223/paper-zip-index.sparse --stage /workspace/scratch/cb6959cc4223/stage-r9` exited 0. `G3_ORIGINAL_MEMBERS_RECEIPT.json` is its stdout. A separate Python pass reopened all staged files and verified SHA-256 and byte size against the fixture manifest: `188 members, 423244864 bytes; all SHA-256 match`, exit 0. These checks do not evaluate certificate contents.
- `lake env lean /workspace/scratch/cb6959cc4223/stage-r9/ImbalancedChen/P4AOriginalFiniteAll22FineDensity.lean` exited 127, `/bin/bash: lake: command not found`. The environment does not contain the pinned Lean/Lake/Elan or installed `.lake` closure. No resource limits were increased and no CI or user machine was used.
- Next, preserve and reproduce the staged inputs, resolve the 59 missing imports and confirm the 56 conditional selections and other fixture dependencies, then typecheck this exact candidate and its actual dependency closure with the declared pinned packages in the permitted environment. Only after successful elaboration check transitive axioms and replay finite bodies, and separately complete the signed error payment and assembly inputs. Do not treat this data receipt as kernel acceptance or complete PP/hUpper.

Changed-file SHA-256 (excluding this self-referential report):

- `stage_original_npz.py`: `b4419a7fcce0a5b5a95b834bff1ead744d946963bb5689c4664ed37d84dc4a24`
- `G3_ORIGINAL_MEMBERS_RECEIPT.json`: `ca484f66ba9efdc89fbf7b1692cac17ccee9ff3825a546870faa9799c2d3fb5f`
