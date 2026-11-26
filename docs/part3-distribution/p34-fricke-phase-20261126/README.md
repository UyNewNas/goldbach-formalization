# P3.4 original cusp-one and literal Fricke phase acceptance

## Accepted scope

The original cusp-one / literal Fricke Fourier phase chain is accepted at source
[`e84cfd0ee77bb6be687c1f511d666eb478a17737`](https://github.com/UyNewNas/goldbach-formalization/commit/e84cfd0ee77bb6be687c1f511d666eb478a17737),
tree `068c9cb77a4ced2f736faa9a1fd724ac43f77e6e`.
P3 task `301f744322e04ab3930207ce04fb2fe1` completed in **238.635 seconds**:
**61/61 stages, 10 strict compiles, 10 bundled kernel replays, 234 inventoried declarations**.
The independent fresh worktree started with zero project objects, ended with ten,
and retained the exact clean source and tree throughout.

This is first acceptance of four existing source owners in their actual ten-module
closure. Six providers were already accepted. All 101 reused declaration records,
including full elaborated types and transitive axiom lists, and all six provider
source/object hashes equal their earlier packet receipt.

**Full P3.4 and historical D20 remain incomplete.** The accepted coefficients are
genuine fixed-height circle Fourier coefficients of the literal Fricke trace.
DI/Whittaker spectral coefficient identification, ABL dilation, the missing original
medium-source interfaces and the remaining continuous spectral normalization are
outside this acceptance.

## Manuscript theorem retained

The frozen 1106 manuscript is
[`paper/release-20261106/en/analytic-appendix.tex`](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/8ca3f6a7f6bbaf6f67c96e80a5065eca9838e703/paper/release-20261106/en/analytic-appendix.tex),
commit `8ca3f6a7f6bbaf6f67c96e80a5065eca9838e703`, SHA-256
`e2d46ac61f2ae2add02a9c432bc4defec3fd3449230e586d5445a44da01d1548`.
The selected chart and phase are at lines 951–962; the later analytic interfaces
at lines 964–1024 are not supplied by this result.

The two manuscript-facing endpoints in
`ImbalancedChen.Part3.ActualFrickeCuspPhase20261025a` are
`sigmaOne_fourierCoeff_fricke_phase` and `integrable_sigmaOne_and_phase`.
For every positive natural level, positive height, signed integer frequency and
genuinely Gamma0-invariant function, the first proves

```lean
_root_.fourierCoeff (sigmaOneSection N hN F hF y hy) n =
  Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / (N : ℂ)) *
    frickeFourierCoeff N hN F hF y hy n
```

The chart is the original `normalizedScaling N hN cuspOneMatrix`. Its matrix
identity uses the actual integral translation, literal determinant-one Fricke
matrix, and real shift `1 / N`. Both square-root scaling factors are retained.
The frequency is `n : ℤ`, so zero and negative frequencies are included. The
integrable endpoint retains its explicit `Integrable (frickeSection ...)
AddCircle.haarAddCircle` premise and uses the same normalized Haar measure in the
conclusion. No Fricke eigenfunction condition or desired spectral identity is
assumed.

## Existing proof reuse and repairs

The original owners and exact five-prefix terminal API repair are recorded in
`NEXT_ENDPOINT_AUDIT.md` and `SOURCE_INTAKE.json`. The historical source-only
registry and repair file are preserved. Subsequent changes repair the actual
pinned-compiler diagnostics in proof bodies: explicit SL/matrix coercions and
entries, scoped action names, scalar cast expressions, and strict tactic lint.
Original mathematical statements, definition bodies, hypotheses and imports are
preserved; the terminal namespace repair is separately identified in the intake.
No new outside-manuscript foundation was introduced.

| First-accepted existing owner | Original explicit declarations | Complete compiler inventory |
| --- | ---: | ---: |
| `Part3FrickeNormalizer` | 22 | 40 |
| `Part3Gamma0GeneralCuspWidth` | 16 | 29 |
| `Part3Gamma0GeneralCuspUnitPeriod` | 19 | 46 |
| `Part3ActualFrickeCuspPhase` | 15 | 18 |
| Total | 72 | 133 |

The 72 explicit declarations include the existing private theorem. They comprise
54 theorems and 18 definitions. The 61 additional compiler records are generated
theorems. These are coverage counts, not 133 new mathematical proofs.

## Verification and trust boundary

Lean is pinned to `4.33.0-rc1`, compiler commit
`62eed1db4d67327ec8120be05f1a1b0847d74561`; Mathlib is pinned to
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. All eleven dependency pin and cleanliness
checks passed. The unchanged shared verifier checks Lean-resolved import paths,
strict warnings-as-errors, three import-scope regressions, bundled `leanchecker`
replay, source/object bindings and clean checkout provenance.

The audit includes every private and generated declaration selected by its actual
defining module, and cross-checks that inventory against the serialized module
constant list. All 234 records have full untruncated types. There is no new axiom
or unsafe declaration; the complete transitive axiom union is exactly
`propext`, `Classical.choice`, and `Quot.sound`. The source guard rejects `sorry`,
`admit`, new `axiom`, `unsafe`, `native_decide`, and kernel-bypass markers.

The new gate freshly compiles and replays these ten project modules. Locked
external dependency caches are reused; this does not claim a fresh rebuild or
replay of the entire Mathlib dependency closure. Earlier focused probes reuse
authenticated provider objects only for diagnosis and carry no acceptance claim.
Their full logs, failed runs and local source lineage are retained separately.

## Accounting with previous accepted scopes

Together with the four earlier accepted scopes, the inventory union is
**28 distinct modules and 494 distinct declarations**, including 351 theorem
constants. The previous 272 repeated records and the new 101 overlap records
compare exactly. This is a union of five separately accepted runs, **not a fresh
joint 28-module run**. The six reused providers receive no new-proof credit.
See `accepted-union-accounting.json` for source receipts and exact added names.

## Evidence and reproduction

- `clean-cloud-verification.zip`: original 76-entry receipt, 138,095 bytes,
  SHA-256 `f79a382a6e38841fcd363e032c112b734d5b548168777541e72e5b7283363008`.
- `clean-cloud-report.json`: full gate report, SHA-256
  `ee0f48254a402e1ce4a7de2aaca17edd0d720fec4d747c8d0e3478d545334674`.
- `declarations.json.gz` and `theorem-types.txt.gz`: lossless copies of all 234
  records and 194 complete theorem types; raw hashes are in the manifest.
- `worktree-provenance.json`, `source-publication-mapping.json` and
  `diagnostic-and-source-history.zip`: exact source trees, preserved local Git
  bundles, all failed/focused receipts and the final fresh runner.
- `task-1-report.md` and `proof-evidence-manifest.json`: detailed checks and file
  identities. Independent review records are recorded alongside this evidence.

With the original pinned Lean/Lake and locked packages available, run from the
exact accepted clean source with no initial project `.olean` files:

```sh
python3 -B verification/verify_p34_fricke_phase.py \
  --expected-head e84cfd0ee77bb6be687c1f511d666eb478a17737 \
  --output-dir .lake/p34-fricke-phase-acceptance
```

`--source-only` verifies source provenance only and does not accept proofs.
The final evidence commit adds records to this immutable accepted source; it does
not change the nineteen source/configuration bindings used by the gate.
