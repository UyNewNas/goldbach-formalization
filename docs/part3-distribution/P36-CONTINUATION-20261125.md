# P3.6: actual original U5 physical support

## Status and pins

This continuation is based on
`ef1479c272bdd6b24800fa10409d793f0a2fe95c`. The original source checkpoint is
`a2e708f909e98f471d74abb79dee199d786de023` on
`work/p3-6-original-u5-20261125`.

**Source implementation is not a compilation certificate. P3.6 remains
open.** The new modules require strict compilation, kernel replay and the
complete defining-module/transitive-axiom audit before acceptance. No
existing board counts or whole-leaf status have been changed.

The manuscript is the frozen 2026-11-06 release at
`UyNewNas/chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`,
under `paper/release-20261106/en/`. The relevant targets are
`argument.tex` (`eq:current-PP`), `coefficient-appendix.tex`
(`coef:prime-product-insertion`), and `sieve-appendix.tex`
(`sv:finite-feedback`).

## New supplier

`ImbalancedChen.P3OriginalU5PhysicalModulusCap` uses the literal receiver
`selectedPolicy R bank buffer false N t` and the original U5 selector.
The root seed remains the original physical level minus **two** buffers;
the finite continuation plan also receives `2 * buffer`.

The existing accepted-run induction bounds the complete external pair
times the accepted rough word by `N^(153/256)`. It applies at every rough
rank, including the empty rough word. The original U5 triangle supplies
the initial reserve; the finite plan's checked fresh caps supply its
ceiling. Neither the final modulus bound nor an arbitrary-policy support
bound is an assumption.

For the same nonzero native rho, the existing small/rough factorization
provides the same active pair `(s,r)`. The small factor satisfies
`s < N^(attachmentNu * epsilon)`, with `attachmentNu = 34/125`. Under the
explicit allocation `attachmentNu * epsilon <= buffer`, the complete
physical modulus `t.1 * t.2 * s * r` is strictly less than
`N^(153/256 + buffer)`. For `0 <= buffer <= 1/1000`,

```
153/256 + 1/1000 = 19157/32000
599/1000 - 19157/32000 = 11/32000 > 0.
```

The final corollary uses the pre-existing pooled integer rho and original
fibre uniqueness. It does not construct a replacement coefficient, remove
negative occurrences, or discard the external pair from the modulus.

The six new declarations are:

- `physical_cap_margin`
- `buffered_cap_lt_theta`
- `selected_U5_accepted_word_le_topCap`
- `native_U5_physical_modulus_lt_buffered`
- `native_U5_physical_modulus_lt_theta`
- `selected_integerRho_nonzero_modulus_lt_theta`

## Reuse and dependency extraction

Existing source suppliers were located before writing the new connection.
Their mathematical proofs are reused. Small interface declarations are
moved into separately importable files, retaining their original namespaces
and declaration bodies. The original broader modules import these files
and retain their remaining declarations. The single intended visibility
change is that the existing `accepted_run_sum_le` becomes public.

Exact source pins, hashes, original-file reconstruction checks and the
selected dependency manifest are kept in
`continuation-20261125-p36/`. Dependency recovery is not counted as new
mathematical work. Previously accepted baseline source variants are not
silently overwritten by later archival versions.

The initial two-core extraction and all six new theorem statements received
an independent read-only review. The review found no Critical or Important
mathematical correctness issue in those statements. It checked the actual
nonzero coefficient, active small factor, original outer pair, complete
product, all rough ranks and pooled integer fibre identity. This review is
not Lean acceptance. Later import-only extractions have separate byte
preservation records and still require compilation.

## Exact boundary of the result

The support theorem is useful for P3.6 but does not prove a signed
prime-product error estimate. In particular:

1. `R` and `bank` remain parameters. The cap does not prove that the bank
   covers every adopted manuscript branch, every full or selected
   complement square, every chi margin, or every ordinary descendant.
2. A modulus bound does not supply positive marked mass, filtered
   complement payment, or a common-Q finite feedback licence for the
   complete actual query family.
3. No retained-medium/no-medium arithmetic estimate, actual normalized
   trace estimate, or uniform signed cancellation is established here.
4. Existing accepted proper-power removal is reused; it does not supply
   the missing von Mangoldt distribution estimate.

The existing yellow-leaf ledger identifies these remaining targets:

| Node | Remaining supplier |
| --- | --- |
| `P3.6.child-28` | Original causal common-Q coverage, filtered complement payment, quantitative harmonic mass, required sparse positive-mass families |
| `P3.6.child-30` | High-rank/enhanced and other actual coefficient classes beyond the accepted level range, then complete same-rho PP assembly |

The upstream `P3.5` analytic inputs described in
`CONTINUATION-20261124.md` also remain explicit. No new axiom or formalization
of an external analytic theorem is introduced to replace them. These are
missing formal suppliers, not evidence that the manuscript theorem is false.

## Reproducible verification entry point

`verification/p36/compile_p36_local.py` resolves the selected import closure
against the pinned toolchain and package revisions, reuses valid dependency
objects, and writes all new objects and logs to its own build directory.
It does not download dependencies or alter shared package checkouts.

The default action is preflight. `--build --strict-owned --verify-owned`
enables actual serial compilation, independent `leanchecker` replay and the
existing P3 declaration/axiom audit. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted as transitive axioms. Every reported outcome must
refer to the exact source and object hashes in the corresponding fresh run;
old baseline receipts are not counted as new acceptance.
