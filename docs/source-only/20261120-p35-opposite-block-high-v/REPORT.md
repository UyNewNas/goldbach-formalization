# P3.5: explicit no-extra-transport subcase on the actual opposite block

## Baseline and packet

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734`, parent
`d179a4ae19f9e6c6c5878173d4f6f766d0fa6256`. The containing commit is
the new SHA. Files live under
`docs/source-only/20261120-p35-opposite-block-high-v/`.
Lean source SHA-256:
`cc653a1230c5d8461501ac663e77ca0d8b7920b0209dafef88bc5b494d2beb97`.

## Exact restriction and proposed reduction

Let the actual physical scales be Z0=S^2 and Z1=2S^2, V=2^j and
m=V-1/2. On the explicitly restricted subcase `Z1 <= V`, the candidate
`opposite_block_highV_initial_price` supplies the previous opposite
block inequality with the prior explicit 3/4 transport multiplier
removed **at W** on both physical charts and both level intervals.
More precisely, for Z=Z0 or Z1, W=max(V,Z^2/V)=V and Z>=1, so

    W <= Z/2 + m,       W <= Z + m,
    max(1,W/(Q+m))^(3/4) = 1,   Q = Z/2 or Z.

The proof includes `fixedZ_one_le` for both literal physical charts,
including empty charts, and preserves the endpoint correction. Thus the
transported price is exactly the existing baseline price
`C*((1+Q)*(1+m))^epsilon*(Q+m)*m` at each of the four relevant intervals.
The argument derives the lower-chart hypothesis from `Z0 <= Z1`, rather
than requiring two unrelated physical restrictions. The equality
`transportedChartCost_eq_initial` is then substituted into the actual
previous `fullBlockMode` inequality; it keeps the original Fourier
coefficient, M^2 Z, both chart budgets, raw level-dependent n expenses,
cuspidal complement, continuous term, and factors 2 and 3.

This removes the **additional** multiplier arising from transporting
the baseline `Q+m` to W. The prior baseline price itself is inherited
from `full_J_with_transport`; no assertion is made that W lies in the
smaller initial-AvgJ interval or that its baseline price was obtained
without any earlier loss. The proof does not establish that an occupied
chart under the actual global frequency cutoff can satisfy `Z1 <= V`;
that intersection must be checked before using the subcase in the full
physical summation. No statement about its complement `V < Z1` follows.
The raw n factor, test-profile budget, other spectrum, oldforms, gap,
and all-cost 7/32 remain unpaid. No changed input or target-equivalent
assumption is introduced.

## Source and boundary

Parent `Part3OriginalOppositeBlockTransport.lean`, blob
`093d86c6c21994a9b7cee7e847d60db719478985`, and its full report were
read; its initial transport candidate is `Part3OriginalAllChartLossyPair`
blob `01f0a4bbdf3deddb96a4533b007cb4beadc8cab6`. Exact definitions of
`threshold`, `fixedZ`, and `classicalMScale` were reread in blobs
`dc31cc0fac0fe6d9fa049f66dc48ffcb9ae55d41`,
`62d248aa63bd5d66db39f681732ead8291d8c7ae`, and
`00ea3113f35c8063519d8889ed3744b13d24d48d` respectively. The existing
`AVGJ_APPLICABILITY.md`, blob `e4a4e3e8b5798d9f4616a297b9e1082d4130e36c`,
was read to retain the distinction between the initial range and full
physical W, and to keep n-row dependence on the level.

Paper body pin
`UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`
was rechecked as blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`,
matching the chain; original (24) is in distribution blob
`19f9672bc9b6d455045213c5e23e10433a9569d2`. No new external input is
added. Prior Pascadi v3, ABL v1, regular sieve and spectral-gap
registrations and unsupplied ranges are unchanged.

## Validation and next obligations

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axioms: not checked. Independent review: not performed. `UNEVALUATED`:
yes, including predecessor proof bodies. No exact import closure is
staged. `command -v lean` and `command -v lake` each exited 1 without
output; no compiler ran, so no compiler exit code or log exists.
Configuration verified: Lean `leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native
`09b97db5764ade1246bfb77206baa1b124760958`; installed versions cannot be
verified. Stack 8192 KiB and virtual memory unlimited, unchanged.
`sha256sum` exited 0 with the hash above. `rg -n
'\b(sorry|admit|axiom|unsafe|native_decide)\b'` exited 1 without
matches; this is not compilation or a transitive-axiom audit. No CI ran.
The root/docs AGENTS lookups were previously recorded absent.

Next elaborate and replay the exact chain; check the high-V subcase's
intersection with the actual truncated occupied families and handle
`V < 2S^2`. Control raw n and oldforms and both chart test budgets,
provide sharp full physical J, estimate the regular and continuous
pieces, and connect the other sign and holomorphic part. The two zero
lanes, actual cutoff tail, 14eta/28eta weights, 128C enlargement,
original N threshold order and reserve payment remain open.
