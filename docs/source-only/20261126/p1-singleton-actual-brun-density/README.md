# Actual singleton Brun density payment

Status: **source only, not elaborated, no Lean or kernel acceptance**.

The new owner is `P1OriginalSingletonActualBrunDensity.lean`, 8336 bytes,
SHA256 `a4323f4ec8be32fd12d219e2ad2dff838ea5a3684cc899a2fa5fb6da21d91d39`.
It imports only the existing `P1OriginalSingletonFixedScaleTransport` owner.
The old Brun, factorial, harmonic and logarithmic absorption sources are
unchanged. This task does not close their inherited source/import boundary.

## Uniform actual-cutoff helper

`eventually_uniform_actual_cutoff_gap_budget` fixes a nonnegative constant C,
natural logarithmic orders B and A, and eta > 0. After one natural-scale
threshold, it applies to every real cutoff 1 <= Z <= n and proves

    C * n * gapDensity Z (halfOrder n) * (log n)^B
      <= eta * n / (log n)^A.

Here n is cast to the reals wherever required. The helper also returns
`1 <= log n`.

The actual finite prime alphabet is `chartPrimes Z`. The existing real-chart
harmonic theorem bounds its reciprocal sum by `2*loglog n`, uniformly in Z.
The new proof compares its natural power with the same power of the fixed
envelope `Hbar n = 2*L2 n`, using the identical factorial denominator. The
original `gap_is_superlog Hbar` and `eventually_gap_budget` then supply the
entire factorial and logarithmic estimate. The prime alphabet is never
replaced by `chartPrimes (roughZ n)`.

## Actual singleton specialization

`eventually_actual_singleton_twoLong_density_payment` fixes cutoffOrder,
logOrder, accuracy, C, eta and the existing kappa/zeta/trim parameters before
the physical-N threshold. The original profile order, chart, HB row, tuple
and two selected positions follow that threshold.

Its hypotheses are the existing geometry conditions: j in range3, distinct
positions i and k, the tuple in the original rectangle, one actual scalar
profile value nonzero, and every short position below the original medium
cutoff. It keeps

    X0 = shortScale bs
    M  = shortScale of the original short positions
    U  = lower (bs i)
    V  = lower (bs k)
    Z  = beforeHBCutoff cutoffOrder [cj].

The existing scale transport at eps=1 gives `1 <= Z` and
`Z^(2*halfOrder X0+1) <= X0`. Its original odd exponent is at least1, so
`Z <= X0`. Since X0 is the cast of the original natural block-endpoint
product, the uniform helper uses exactly the same `halfOrder X0` and
factorial order. No rounding of X0 or change of Brun order occurs.

The existing rectangle trim inequality `(N^(1-kap0))/64 < X0` lifts the
natural-scale threshold to a uniform physical-N threshold. The terminal
conclusion retains the old equality `X0 = M*U*V` and proves

    C * (M*U*V) * gapDensity Z (halfOrder X0) * (log X0)^logOrder
      <= eta * X0 / (log X0)^accuracy.

This is the density summand from manuscript equation `coef:two-rough-error`.
It does not assert a finite discrepancy bound or complete rough restoration.
It neither changes Q/rho nor assumes aggregate or whole-rectangle activity.

## Source bindings and verification boundary

`SOURCE_REVIEW.json` records exact bytes/SHA256/Git blob identities for the
eight source suppliers, declaration locations, and the fixed 1106 manuscript
at commit `a988cba584d803ae2856a0de50efb582f4f3dd6a`, lines797-821.

Only the new scratch owner and these notes were written. No canonical source,
old proof, compiler artifact, driver, guard or configuration was changed.
No Lean command, cloud task or existing test suite was run. Independent review
of the new glue is recorded separately from any future elaboration result.

Independent narrow review by `p15_resume_source_paths` found no concrete
mathematical or obvious Lean API blocker in the two new declarations. It
confirmed the same-order factorial comparison, actual-Z prime bound, natural
scale cast and physical threshold, and the final MUV rewrite. The review did
not run Lean or re-audit the old Brun/Rates proofs; source-only status remains.
