# saving19: original polynomial supporting-face arithmetic

Parent `213ac8d35c70d5efc6150fa98a4e75c695d6e4d1`; original source baseline `6848b4a69fd6f25806989dac7d305d27a6cd204e`. This commit's identity is supplied by Git. This packet adds finite-data verification and a handoff, not a Lean theorem and not a discharged formal premise. The preceding `PHYSICAL_OWNERSHIP_HANDOFF.md`, `ORIGINAL_ROWS_REPLAY_HANDOFF.md` and downstream history handoffs remain in force.

## Exact source and target

Reread in full `docs/source-only/20261102-resume-30m/saving19_owned_integral/P2OriginalSaving19PullingOwnership.lean`, blob `49a15fb31f001c8ac627b2b333d283b4f69e4277`, SHA-256 `87fd625fc864128a001ba49deab415fd82eb944ee3c23bda036762c199f94dde`, and `P2OriginalSaving19OwnedIntegral.lean` (prior registered blob `d3b32ef07f879568849305683dfd8e3e8fd73439`). The existing closed `original_polynomial_faces` candidate requires, for every actual row, its affine plane polynomial to equal `-X^vertexId` at all nine own vertices and, for each off-simplex original vertex, the leading coefficient of `heightPolynomial v - planePolynomial r v` to be strictly positive. `original_within_cell_null_overlap` and `original_endpoint_le_selectedSaving` use this source chain. Their Lean proof bodies have NOT been evaluated, and neither their elaboration nor their semantic conclusions are established by this script.

The manuscript `9731290e8f53cffda44129906cde6a965eaa869b:paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, SHA-256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`, matches the chain's recorded pin. Lines 365–374, 435–449, 1354–1365 were reread: retained causal ancestors, new-minus-current-parent and legal inner subset; Q96 remains a replacement bound, not a second payment. No original constant, ordering, sign, boundary or occurrence was changed.

## Arithmetic checked and derivation

`check_polynomial_faces.py`, SHA-256 `be6bbe9ba8290412adc5bcdaecdf326770fd7849212688e328d3a97b201f1ca3`, blob `551484c97625bc7607e3eb76eb89a3aa4db9c4d4`, reads the exact manifest (SHA-256 `fccf400489947123dd088d7f6087b76dc7b777259a0348d9c31601f75565684f`), exact Lean source hash above, and 13 geometry files after each original manifest size and digest comparison. The exact recovered release and all 26 files were authenticated as documented in `ORIGINAL_ROWS_REPLAY_HANDOFF.md`.

For one row let H have rows `(1,t_k)`, in the original vertex-ID order, and let lambda = `(1,t) H^-1`. A fixed nonzero integer scale per coordinate clears the vertex denominators without changing lambda. The code computes an integer numerator inverse and denominator, normalizes the denominator positive, and checks all 81 entries of `H * inverse = denominator * I` for every row. Hence at the nine own vertices the nine barycentric coefficients form the identity. For an off vertex v, the exact residual specified by the source is `sum_k lambda_k X^(id_k) - X^v`; since all nine ids and v are distinct, scanning these exponents in descending order gives its actual leading coefficient. The script rejects zero or negative leading coefficients. No sample approximation or floating point is used.

Result, Python exit 0: all 28,918 original rows; 260,262 own-vertex identities; 3,119,744 off-vertex strict leading-coefficient checks. `POLYNOMIAL_FACES.log`, SHA-256 `72ed9f3a721eeb41e5086296239f524df89810e79d3977a58d606b89a6ac4a1f`, blob `c13c97cd9e0c889abc9e031c0a4a449eb026231f`, records each cell. A separate spot check formed actual SymPy `Poly` residuals via a rational matrix inverse on the first three rows of cell 0, giving 57 off-vertex positive leading coefficients and matching all their own-vertex identities; this is not independent review of the complete result. Initial development used an incorrect `DomainMatrix.from_list` argument count and failed with TypeError before checking data; the corrected invocation was used for the complete successful run.

## Reproduction and boundary

In the existing environment, single process, Python 3.12.14 and SymPy 1.14.0; shell `ulimit -v` unlimited; no resource enlargement. From `/workspace/scratch/8c9d3a651a4e`:

```sh
python3 -u /tmp/p2_saving19/check_polynomial_faces.py \
  --manifest /tmp/full87.json \
  --source goldbach/docs/source-only/20261102-resume-30m/saving19_owned_integral/P2OriginalSaving19PullingOwnership.lean \
  --witness-dir goldbach-research
```

The full command (wrapped in `bash -o pipefail` with `tee`) exited 0; `python3 -m py_compile /tmp/p2_saving19/check_polynomial_faces.py` exited 0. `lean --version` and `lake --version` returned 127; the local `lake env lean docs/source-only/20261102-resume-30m/saving19_owned_integral/P2OriginalSaving19PullingOwnership.lean` likewise returned 127, `lake: command not found`. No Lean elaboration or kernel checking took place; no toolchain was installed, no pins changed, no CI was launched. Declared pins remain Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`; installed revisions were not verified.

SOURCE_ONLY=yes; COMPILED=no (UNCOMPILED); KERNEL_REPLAYED=no; TRANSITIVE_AXIOM_CHECK=NOT RUN; INDEPENDENT_REVIEW=NOT RUN; finite Lean bodies=UNEVALUATED. This arithmetic does not check the continuous null-overlap theorem, prime-history realization, the actual sixth-parent chronology, occurrence weights or the complete T03 consumer. The existing outside inputs remain inherited from the prior registries, with no new external theorem or proof project introduced.

Next: use an already available authorized matching environment to stage the exact registered import closure and source bytes, and compile/replay the actual bridge and consumer with full logs and a transitive axiom report. Trace the same frozen ancestor, actual licensed sixth parent and ordered prime occurrences in the separate reciprocal-prime and unit-weight dictionaries; do not equate them merely because this finite geometry passed. A missing compiler is not a new mathematical obligation; only a concrete failing same-parameter consumer would justify identifying and repairing a new one.
