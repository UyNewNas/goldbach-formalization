# saving19: degree-six universal moment coefficient audit

Parent `1da322b0f95583511cd92ef9eccbadca220d84f2`; original source baseline `6848b4a69fd6f25806989dac7d305d27a6cd204e`. The containing Git commit supplies its own identity. This packet adds an exact-arithmetic audit and handoff; no new Lean theorem, proof assumption or arithmetic input is introduced. It does not claim P2.6 completion.

## Source and actual consumer

Read the complete `docs/source-only/20261102-resume-30m/saving19_higher_moments/P2OriginalSaving19HigherMoments.lean`, blob `623ba5ec94460c2265875e0119d2b31b5f200ef8`, SHA-256 `59ccbb110e9aceac63a5bb7030b49e0f1103993bc6b2f6fb2b49a80391b2d41e`, and `.../saving19_original28918/P2OriginalSaving19Original28918FloorBinding.lean`, blob `c663f7e5baa908f85f2cfde8b8fe219bfc4515d4`, SHA-256 `c4f5765cf575b3faacafe0e765c358373e975a960ab8a7c87d742660510e51b1`.

The former defines `duplicateH` on nine arbitrary nodes with node i duplicated, `integratedPower` with the source's barycentric factorial coefficient, and the closed UNEVALUATED candidates `integratedPower_newton_guard` and `duplicateH_author_guard`, for `i : Fin 9` and `k ≤ 6`. `integerNewtonNumerator_divisible` depends on the universal identity. The source candidate `physical_power_moment` uses the separate K simplex integral and Jacobian chain; the audit below does not execute or establish those analytic ingredients. `higherPowerMoments_of_encoding` feeds this into `AlgebraicMomentRow.toMomentRow`. In the latter file `fullMomentRow` is formed from the same original row's physical vertices; `saved_Q96_binding` rewrites its original saved floor to the max of old and refined floor, and `saved_row_floor_le_actual_simplex_integral` invokes the existing soundness candidate. None of these Lean proof bodies were elaborated or kernel replayed here.

The manuscript pin remains commit `9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, SHA-256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`, matching the chain registry. Paragraphs 365–374, 435–449, 1327–1340, 1354–1360 were reread: actual causal ancestor, factor-four density, replacement rather than a second same-domain gain, and legality of an inner subset.

## Exact coefficient verification

New `check_universal_moment_polynomials.py`, SHA-256 `f79ddb88bbddbdffba10713dce7de1abc5e7e39bda2498d46079b6fb87b622df`, Git blob `27403dea6b268c3d0ed3261ff7c71ff1a2e37dd6`, first checks the exact higher-moment source bytes. It enumerates all exponent vectors `e ∈ ℕ^9` with sum k for each k=0,…,6 and each of the nine duplicate nodes i. Thus the variables remain formal; this is not a test only at archived numerical vertices.

One calculation implements the source's duplicated-node Newton recurrence `H_k=(1/k) Σ_{j=1}^k (Σ_r y_r^j+y_i^j) H_{k-j}` over exact rational polynomial coefficients. A separate geometric-series/in-place coefficient recurrence multiplies the nine original node factors followed by the duplicate i. Every coefficient agrees, and every divided Newton coefficient is integral. Independently, for each exponent vector, the script compares the source's multinomial times bumped barycentric coefficient

`k! * ∏_r (e_r + [r=i])! / (∏_r e_r! * (k+9)!)`

with the Newton coefficient divided by `9! * C(9+k,k)`. This is a coefficient identity **assuming the source's stated barycentric coefficient**; the script does not prove the Lebesgue integral or the simplex measure theorem from which that coefficient is derived.

Full run: 63 node/degree combinations, 45,045 monomials, 90,090 coefficient equalities, all pass; log `UNIVERSAL_MOMENT_POLYNOMIALS.log` SHA-256 `3209ab84c9a83caa7e740b99249aee49e72b2d34bce27d03d9198bbb753ad942`, blob `4db29adae3c34fd0d652f000c21b7d6f66e85a89`. It is a Python exact-arithmetic verification of two universal coefficient formulae, not Lean compilation, a proof of any real integral, an audit of the 28,918-row `by decide`, or independent review.

## Reproduction and status

Python 3.12.14, standard library only, one process, existing environment and `ulimit -v` unlimited; no resources were increased:

```sh
python3 -u /tmp/p2_saving19/check_universal_moment_polynomials.py \
  --source goldbach/docs/source-only/20261102-resume-30m/saving19_higher_moments/P2OriginalSaving19HigherMoments.lean
```

The full command, run through `bash -o pipefail` and `tee`, exited 0; `python3 -m py_compile` exited 0. Fresh `lean --version`, `lake --version` and `lake env lean docs/source-only/20261102-resume-30m/saving19_higher_moments/P2OriginalSaving19HigherMoments.lean` each returned 127, command not found. No compiler or import closure was installed, no CI/Actions started, and no pins changed. Declared pins remain Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`; no installed-version evidence. Prior exact per-row replay, original geometry and common-history trace are in sibling handoffs and are not promoted to kernel verification by this audit.

SOURCE_ONLY=yes; COMPILED=no (UNCOMPILED); KERNEL_REPLAYED=no; TRANSITIVE_AXIOM_CHECK=NOT RUN; INDEPENDENT_REVIEW=NOT RUN; finite Lean proof bodies=UNEVALUATED. Existing analytic/external input normalization and verification status remain those of the prior registries and `ACTUAL_OCCURRENCE_TRACE_HANDOFF.md`; this audit neither adds nor proves an external number-theory input.

Next: use the task's existing authorized matching Lean environment and exact effective import map to elaborate the higher-moment module, actual 28,918-row guard, owned integral, and matching T03 consumer, retaining logs and separately checking axioms and independent review. The relation between the separately staged fourteen→thirteen held policy and the finite T03 policy remains a scoped consumer question; do not conflate their signs, weights or parents. A missing compiler is not a new mathematical obligation.
