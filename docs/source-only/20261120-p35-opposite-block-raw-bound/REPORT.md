# P3.5: raw exceptional Cauchy bound on the original two-chart block

## Baseline and deliverable

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734`, parent
`258148aca9ccf6d321587aaf38a2e67c70a5096a`; the containing commit is the
new SHA. Packet directory:
`docs/source-only/20261120-p35-opposite-block-raw-bound/`.
`Part3OriginalOppositeBlockExceptionalBound.lean` SHA-256:
`b75895a754e34be82aad5c67f617b6c972322dfa4fe4e1f3592d7c0fbd139d90`.

## Exact candidate and removed gap

The preceding packet split the actual opposite `fullBlockMode` into
exceptional E, cuspidal complement R and continuous C but did not
connect E to a spectral-energy estimate. This packet proposes that
connection without assuming the desired (24) or 7/32 bound:

* `one_chart_mode_raw_bound` lifts the existing raw two-sided Cauchy
  estimate to the literal `signedExceptionalMode`, including the actual
  Fourier coefficient and the physical `M sqrt Z` scalar. Its phase is
  selected once for the entire occupied original chart before both the
  mark `r` and the Poisson sign; the m sequence is level-independent on
  that chart and the actual n row remains level-dependent.
* `rawChartJ` is explicitly the original `W = threshold V Z` weighted
  pair of Pascadi-J energies on `(Z/2,Z]` and `(Z,2Z]`, divided by 4
  for the existing native normalization. It is an expression in the
  conclusion, not an assumed full-X bound. `rawChartN` explicitly keeps
  the currently available raw sieve expense
  `2*sieveConstant*(1+|a|*nu*rowLength/Z)` times the actual marked row
  mass. No ABL removal or saving is silently inserted.
* `two_chart_exceptional_raw_bound` combines exactly the two actual
  chart contributions. It chooses separate test budgets and phases for
  the two different test scales; within either chart its single phase
  covers all levels, multiplicities, marks and both signs. It keeps the
  two costs separate and pays factor 2 by the squared triangle bound.
* `opposite_block_with_exceptional_raw_bound` combines that estimate
  with the preceding actual opposite-block squared split. Its conclusion
  retains the unestimated squared R and C contributions, with the
  original block split's factor 3. Thus it is a partial original-block
  inequality, not full (24).

The candidate quantifiers select B0, omega0, B1 and omega1 before r and
negativeM. The chart budget can depend on the actual Fourier mark and
test scale, and no uniformity in those parameters is asserted. The
exceptional range is exactly the strict finite native set in the parent
chain; the same proof does not assert a regular or holomorphic bound.
The only sign restriction used for the full block is the original
`traceNegative = true`; the exceptional estimate itself is available for
both boolean signs through the already written signed-source candidate.

## Sources and boundary

Parent `Part3OriginalOppositeBlockSplit.lean`, blob
`27dc3d2b114c4c9f791e02196a09bb8a379bfc42`, was reread in full. The
actual one-chart raw Cauchy source is
`Part3OriginalSignedExceptionalChart.lean`, blob
`292f96931d23fb22545681824276ee576f468c51`. The actual scalar and
previous two-sign proof are in `Part3OriginalSignedExceptionalMode.lean`,
blob `628b660ed173c0e1180b3eccb26b992017cdbbd3`; this packet exposes its
single-mode estimate for both actual chart test scales and connects it
to the original block. The post-removal pair blob
`a038900816ae4e167afb9f46ace2e142440d386c` was read to distinguish the
reduced n row from the raw n row; this packet uses the latter.

The paper pin was checked again: manuscript body at
`UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`
has blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`; the distribution
module containing the original (24) is blob
`19f9672bc9b6d455045213c5e23e10433a9569d2`. No manuscript revision or
parameter was changed. The prior registration of Pascadi v3, ABL v1,
regular input and the spectral gap remains in force and remains
unfulfilled where previously recorded; no new external estimate is
introduced. In particular, no fixed-level statement is relabelled as an
average and initial AvgJ is not extended to full W.

## Verification and remaining work

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axiom check: not performed. Independent review: not performed.
`UNEVALUATED`: yes, including all parent candidate bodies. No exact
import closure is staged. `command -v lean` and `command -v lake` each
returned exit 1, without output. No compiler was invoked, so no compiler
exit code or log exists. Repository configuration pins Lean
`leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native
`09b97db5764ade1246bfb77206baa1b124760958`; installed versions could not
be verified. Stack 8192 KiB, virtual memory unlimited, unchanged.
`sha256sum` exited 0 with the source hash above. `rg -n
'\b(sorry|admit|axiom|unsafe|native_decide)\b'` exited 1 without
matches; neither static result is a compilation or axiom audit. No CI
was started. Applicable AGENTS lookups at repository root and docs were
previously checked absent.

Stage and elaborate this exact chain and kernel-audit it. Prove an actual
replacement or affordable bound for the large raw n cost, including the
separate oldform removal; control the chart test budgets and missing
full-physical-weight J. Bound the actual cusp complement and continuous
terms, and connect the same-sign/holomorphic branch. Preserve both zero
lanes, the actual cutoff tail, 14eta/28eta weights, 128C extension, N
threshold order and reserve payment; none is closed by this packet.
