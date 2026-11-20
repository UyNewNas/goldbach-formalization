# P3.5: exact original n-mass assembly across two physical charts

## Baseline and packet

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734`, parent
`ecda7539b6e8419cc49fb09fd803bd6b52565f2b`. The containing commit is the
new SHA. Packet directory `docs/source-only/20261120-p35-two-chart-raw-mass/`.
`Part3OriginalTwoChartRawMass.lean` SHA-256:
`ee26d57fb755e67b4ce7ab85b88865528d6d58c0b6532b7e9d54d45a691def84`.

## Precise candidate result

The original raw n coefficients genuinely vary with the level. For the
actual D, r and primary/sign/y-dyadic key k, define the joint-output mass

    B_actual^2 = sum_{zy in outputCarrier D k} |blockBeta D r k zy|^2.

`two_chart_row_mass_eq_actual` proposes the exact equality between
this mass and the two existing `rowMass` sums over the lower and upper
physical charts. It first uses the previous value-preserving level
equivalence, then the original disjoint chart filter at 2*S^2, and the
actual `sum_output_eq_rows` quotient-coordinate change. The original
joint-output multiplicity is inside `blockBeta`; no output is repeated,
no coprimality or phase assumption is added, and empty charts are valid.

Writing G=|a|*nu, L=`rowLength k`, Z0=S^2, and A0=
`2*sieveConstant*(1+G*L/Z0)`, the raw fixed-level sieve expenses obey

    rawChartN(false) + rawChartN(true) <= A0 * B_actual^2.

The reason is Z0<=Z1=2*S^2 and each row mass is nonnegative. There is no
additional factor 2 from the chart partition. This does not remove the
large raw factor `1+G*L/Z0`, and is not an oldform removal or a
cross-level spectral large sieve.

The candidate also proves nonnegativity of the two actual full native
m-side `rawChartJ` sums and forms their original squared outside weights
`W_u=M^2*Z_u*B_u^2*rawChartJ_u`. The two J sums retain separate
W-thresholds and separate phases, with one phase chosen across the
levels of each graph. The distinct two raw costs are then bounded by

    max(W_false,W_true) * A0 * B_actual^2.

`opposite_block_with_original_raw_mass` substitutes this result into the
existing original opposite `fullBlockMode` inequality, choosing B0, B1,
omega0 and omega1 before r and the Poisson sign. The actual Fourier
coefficient, previous factors 2 and 3, regular cuspidal complement and
continuous part remain. This is a usable manuscript-specific cost
assembly candidate, not a proof of (24), full-range AvgJ or 7/32.

## Source and input boundary

The immediate prior cutoff packet and its parent are recorded in the
branch history. `Part3OriginalExceptionalChartIndex.lean`, blob
`a9a767f433c3b48a6cd9e057c3f35512d4ffb2a1`, supplies the value-preserving
chart equivalence; `Part3OriginalOppositeBlockExceptionalBound.lean`,
blob `779f7d38325d249390e8c812c1918a93db063c1d`, supplies the actual
two-chart raw inequality and original J/raw n weights. The exact
`rowMass` and fixed-level post-removal comparison were read in full in
`Part3OriginalExceptionalPostRemovalPair.lean`, blob
`a038900816ae4e167afb9f46ace2e142440d386c`. The present source does not
identify the raw n row with that post-removal row.

The complete `Part3OriginalPrimaryPacketRows.lean`, blob
`4281ec328d4c3a0f4cb9ca21c2f0923604e6e47a`, defines `outputCarrier`,
`nCarrier`, `decode` and `sum_output_eq_rows`. The complete two-chart
source blob `62d248aa63bd5d66db39f681732ead8291d8c7ae` defines the
literal endpoint filters. The original fixed-level sieve cost is not
promoted to a level-averaged spectral theorem. `pascadiJ` stays an
unevaluated full m-side energy; the initial estimate is not extrapolated.

Paper body at
`UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`
was checked as blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`;
distribution module blob `19f9672bc9b6d455045213c5e23e10433a9569d2` and
its (24) paragraph were reread. No new external theorem is introduced.
Pascadi v3, ABL v1, regular sieve and gap registrations and unresolved
formal suppliers retain the prior status.

## Verification and open obligations

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axiom check: not performed. Independent review: not performed.
`UNEVALUATED`: yes, including all imported candidate proof bodies. The
exact import closure is unstaged. `command -v lean` and `command -v
lake` each returned exit 1 with no output. No compiler ran, so no
compiler exit code or log exists. Configured Lean is
`leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native
`09b97db5764ade1246bfb77206baa1b124760958`; installed versions cannot be
checked. Stack 8192 KiB; virtual memory unlimited, unchanged.
`sha256sum` exited 0 with the source hash above. The source scan
`rg -n '\b(sorry|admit|axiom|unsafe|native_decide)\b'` exited 1 without
matches; it is not a compilation or axiom audit. No CI was started.
Applicable root/docs AGENTS checks were previously recorded absent.

Next elaborate the exact import closure, in particular the real/complex
finite-sum conversion and dependent chart equivalence, replay and
audit. Combine the actual output masses across the original disjoint
primary keys only through the already stated beta-energy identity;
control the two m J weights and test budgets, replace or pay raw-n and
oldform costs, and estimate regular/holomorphic and continuous terms.
Handle the full frequency range, both zero lanes, actual tail, 14eta and
28eta weights, 128C enlargement, threshold order and reserves.
