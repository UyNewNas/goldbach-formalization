# P3.5: exceptional cosine denominator on the actual reduced pair

## Baseline and files

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734` was read at
`8899183bd10c958a90c5cb45e33d531b645d0b48`. The containing commit is the
new SHA. This packet adds only `Part3OriginalExceptionalCosinePair.lean`
and this report in `docs/source-only/20261120-p35-cosine-pair/`.
Candidate source SHA-256:
`2a1dad62e9adcbfb69d268bcb7be068d0b737c2bf60af66cca51ab63e2e7d84e`.

## Exact proposed deduction

For each actual strict exceptional slot write
`tau=2*sqrt(1/4-lambda)` and use the original common positive Poisson
interval and its original infinity-cusp `originalMFunctional`. The
existing source-only `high_positive_zero` states that **each positive
infinity coefficient** vanishes when `tau>3/4`. Therefore every term of
the actual clipped m functional vanishes in such a slot, regardless of
the separate, genuinely level-dependent n row. This applies even for
an empty m block and does not assert that the eigenvalue itself is absent.

For the remaining slots `0<=tau<=3/4`, elementary monotonicity gives

    cos(pi*tau/2) >= cos(3*pi/8) > 0,
    1/cos(pi*tau/2) <= Kcos := 1/cos(3*pi/8).

The separate existing `complementary_range` supplies positivity of the
actual cosine for every strict exceptional slot. The proposed
`cosine_pair_le` combines these facts on the **same actual finite slot
set** and unchanged m/n factors F,G:

    sum_slots (F*G)/cos(pi*tau/2) <= Kcos * sum_slots F*G.

Here F includes the original threshold weight and clipped common m
functional, and G the original reduced, level-dependent n functional and
its weight. No condition `tau<=7/32`, unbounded-Q/M J bound, full J input
or spectral-gap hypothesis is introduced. `cosine_pair_with_transport`
then composes the inequality with the preceding `all_chart_pair_with_transport`,
paying `Kcos^2` in its squared bound; the inherited 3/4 moving-scale
transport fee remains explicit and unchanged.

This pays the cosine denominator **only for this specific post-removal
exceptional bilinear pair**, conditional on eventual validation of the
already source-only high-positive-zero and pair suppliers. It is not a
uniform bound on the denominator of each exceptional form independently,
not a proof of a spectral gap, and not a bound for the n row alone. The
full trace transform must still be connected to this exact denominator
and pair; the raw discrete oldclass and continuous reductions, sharp
full J, tau<=7/32 transport elsewhere, both zero lanes, truncated tail,
14eta/28eta and 128C expenses and complete reserve remain unresolved.
No equality between the raw and reduced bilinear trace is asserted.

## Exact sources and external input boundary

* `docs/source-only/20261115-resume/s09/actualpositive6/Part3OriginalPositiveMarkOrder.lean`,
  blob `a7b55fd75d003112c65aa9cb2283259a4843ef5a`, theorem
  `high_positive_zero`; and
  `Part3OriginalFullPositiveLevelSwitch.lean`, blob
  `9ecc9cdc0ebf448515ad2da47c939f0a011351f8`. These are source-only
  candidates; the latter already records the corresponding high-order
  zero for positive native rhoK, but its full-row helper is private.
* `docs/source-only/20261112-resume/t04/positive-test-next/Part3ActualPositiveNativeDiagonal.lean`,
  blob `087daa59457776f5c18e69d73862394fb635c082`, defines the native
  complementary height and `complementary_range` with a positive cosine.
  `docs/source-only/20261102-resume-30s/S/s20_normalized_kuznetsov/Part3OriginalNativeCuspFunctionals.lean`,
  blob `88c3220e130f426f55f2f742d73b9572fb0faa8c`, gives the literal
  `originalMFunctional` and clipped common block.
* `docs/source-only/20261119-p35-all-chart-lossy/Part3OriginalAllChartLossyPair.lean`,
  blob `01f0a4bbdf3deddb96a4533b007cb4beadc8cab6`, gives the inherited
  reduced pair and explicit transport cost. All are uncompiled here.
* Pinned mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`,
  `Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean`, blob
  `86ee5817a80feccb86eb9e6fae7b0730007c54c4`, was read: its
  `Real.cos_pos_of_mem_Ioo` and `Real.cos_le_cos_of_nonneg_of_le_pi`
  have the signatures used in the proposed scalar proof.
* Original manuscript pin remains `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`,
  main body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, distribution
  module blob `19f9672bc9b6d455045213c5e23e10433a9569d2`, §7 (24) and
  §10(v)–(vii). The external normalization is `R(n)=sqrt(|n|)rho_ABL(n)`;
  the native `rhoK=2R`, `tau=2*theta`, and the corresponding squared
  `rhoK` energy has factor four. These are not changed here.
* Pascadi, arXiv:2404.04239v3 (15 January 2026), Theorem J,
  (3.34)–(3.35), was read at https://arxiv.org/html/2404.04239v3#S3.SS4:
  for `Q,M>=1/2`, one phase independent of level, and
  `X << max(M,Q^2/M)`, it bounds the full level-averaged strict exceptional
  infinity energy by `(QM)^epsilon*(Q+M)*M` in its rho convention.
  Its full-range native Lean provider remains missing; the present lemma
  neither proves nor assumes it as a new axiom. ABL v1 Lemmas 3.1/3.2,
  regular spectrum, numerical gap and actual continuous normalization
  remain separate external/source obligations as in the prior report.

## Verification and next work

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axioms: not checked. Independent review: not performed. `UNEVALUATED`:
yes, including the upstream high-positive-zero and all-chart pair source.
The existing environment has no Lean/Lake executables and no staged
exact import closure; no compiler ran and there is no compiler exit code
or log. Configured pins are Lean `leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` and native
`09b97db5764ade1246bfb77206baa1b124760958`. Stack limit 8192 KiB and
virtual-memory limit unlimited; no resource was increased.

`sha256sum` gave the candidate hash above; the `rg -n
'\b(sorry|admit|axiom|unsafe|native_decide)\b'` scan returned exit 1
(no matches). These are source inspection, not compilation. No CI, Codex
or user machine was invoked. Next stage exact frozen imports, elaborate
this candidate and its dependencies, replay the kernel and check
transitive axioms. Then connect this denominator to the actual normalized
trace while retaining its transform/oldform weights, and independently
supply or register the precise sharp J and 7/32 inputs for the full range.
