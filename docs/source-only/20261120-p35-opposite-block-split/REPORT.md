# P3.5: the original opposite-sign two-chart block

## Baseline and files

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734`, parent
`37477ed5e4e69a0052d0b23926cafd05b4cc5a33`; the commit containing this
report is the new SHA. Packet path:
`docs/source-only/20261120-p35-opposite-block-split/`.
`Part3OriginalOppositeBlockSplit.lean` SHA-256:
`1fc3753f59ac6359836a06bce62fecdaff06e6d088630dad10b651d95d835d36`.

## Precise proposed deduction

For the original marked `fullBlockMode`, with actual nonzero residue,
positive N and the original composite sign `traceNegative = true`, the
candidate `opposite_block_split` identifies the entire original block
with `E+R+C`: E is the sum of the two physical charts' existing strict
exceptional modes; R is the sum of their native cusp complements; C is
the sum of their original continuous modes. It uses the existing exact
one-chart split twice and the actual original block spectrum identity.
Every chart keeps its own `fixedZ`, level set, test scale, raw n row,
Fourier coefficient and scalar. No identification of the two chart
phases is made and no further hypothesis about their relative size is
introduced. The block has one fixed Poisson sign constrained by the
composite-sign condition; it is not a simultaneous statement about
both Poisson signs.

`opposite_block_sq_le_parts` then supplies the explicit inequality
`|fullBlockMode|^2 <= 3*(|E|^2+|R|^2+|C|^2)`, by the triangle
inequality and the three pairwise nonnegative squared differences. It
introduces no J, sieve, oldform, gap or target 7/32 assumption. This is
an exact manuscript-specific algebraic reduction to three separately
named contributions, not their analytic estimate and not (24). The
continuous term remains the actual chart integrals rather than a
single Eisenstein-vector norm. The n coefficient remains level-dependent.

## Read sources and input boundary

The full parent `Part3OriginalOppositeChartSplit.lean`, blob
`bf2ebc9973de8f5df094e0b5d2ba19a3edc9fc7e`, was read, as were its
previous strict-row split blob `2037814843ce0e8b8857f9809ad074aff5934a8b`
and level-index bridge blob `a9a767f433c3b48a6cd9e057c3f35512d4ffb2a1`.
The complete original `Part3OriginalPrescribedChartSpectrum.lean`, blob
`fc79ad8d2de109d661b52ba0e9bb83c3c8315e5a`, was reread: its
`full_block_opposite_spectrum` and `oppositeBlockSpectrum` use exactly
the two actual physical charts. The signed exceptional mode source,
blob `628b660ed173c0e1180b3eccb26b992017cdbbd3`, retains the earlier
one-chart, one-phase estimate, but the present block split does not
assert that estimate for a sum of chart phases. The complete existing
post-removal pair, blob `a038900816ae4e167afb9f46ace2e142440d386c`, was
read to check that its fixed-level n sieve is not a cross-level average.

The manuscript body at
`UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`
was checked again: blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, as
registered. The actual (24) passage in distribution module blob
`19f9672bc9b6d455045213c5e23e10433a9569d2` was reread. No new external
input is introduced; the prior Pascadi v3, ABL v1, regular sieve and
spectral-gap registrations and missing-supplier statuses remain
unchanged. No initial AvgJ is extended to the full physical weight.

## Verification and next step

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axiom check: not performed. Independent review: not performed.
`UNEVALUATED`: yes, including parent candidates and finite proof bodies.
The import closure is not staged. `command -v lean` and `command -v
lake` each exited 1 without output; no compiler was invoked, so there is
no compiler exit code or log. Repository files pin Lean
`leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` and native
`09b97db5764ade1246bfb77206baa1b124760958`; installed versions cannot be
verified. Stack 8192 KiB, virtual memory unlimited, unchanged. A source
`rg -n '\b(sorry|admit|axiom|unsafe|native_decide)\b'` returned exit 1
with no matches; this is neither compilation nor a transitive axiom
audit. `sha256sum` exited 0 with the hash above. No CI was started.
Root, docs and docs/source-only `AGENTS.md` lookups returned 404.

Next stage and elaborate the exact import chain; kernel-replay and audit
it. Supply estimates for R and C, including regular and continuous
contributions; connect the actual same-sign trace including holomorphic
terms. Pay oldform removal and the level-dependent n-row cost, and
supply missing full-range J and the spectral gap. Keep both zero lanes,
actual cutoff tails, 14eta/28eta weights, 128C enlargement, N threshold
order and reserve payment intact. Neither the present block split nor
the factor 3 alone establishes any of those remaining obligations.
