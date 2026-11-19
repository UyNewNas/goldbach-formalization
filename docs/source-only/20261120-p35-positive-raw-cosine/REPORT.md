# P3.5: raw same-sign strict-exceptional slot

## Baseline and packet

Baseline branch `chatgpt/p3-5-bounded-chart-20261119-1734`, parent
`1e21762354c70364df39bdb9748f7ea587c7e483`; the new SHA is the commit
containing this report. Files added under
`docs/source-only/20261120-p35-positive-raw-cosine/`:
`Part3OriginalPositiveRawCosine.lean` and this `REPORT.md`. The Lean
file SHA-256 is `3fd04dbab592a01879a469163c795acde45e97056565240c803e048e36af1cfd`.

## Exact candidate and deduction

For each positive integer level `z`, each actual strictly exceptional
native basis index `i` (`0 < lambda_i < 1/4`), the original clipped
common Poisson m functional `M_i`, and the actual level-dependent n
functional `N_i`, the proposed theorem states

    |nativeWeight(z, spectralTest(ell,Y),i) * conjugate(M_i)*N_i|
      <= Kcos * |exceptionalWeight(spectralTest(ell,Y),a_i)| * |M_i| * |N_i|,
    a_i = sqrt(1/4-lambda_i),  Kcos = 1/cos(3*pi/8).

It holds for arbitrary `Y : R`, `ell`, level and original row
parameters, and makes no 7/32 hypothesis.  In the actual positive trace
the row belongs to the permitted chart, `Y>0`, and the signs satisfy
the hypotheses of that trace; these restrictions are unnecessary for
this pointwise algebraic statement.  The m interval, its phase, the n
coefficient, and actual level/basis index are unchanged. The n sequence
is not made independent of level. This bound has **no extra factor 8**:
the exact positive exceptional integral is the existing
`exceptionalWeight` and `nativeWeight` is precisely that integral
divided by `cos(pi*a_i)`.  One may specialize to any original Row using
its positivity proof; identifying the `dMark` expression is definitional.

Proof idea: the already source-only `original_m_zero_high` proves
`M_i=0` for `tau_i=2*a_i>3/4`. For `tau_i<=3/4`, the existing
`cosine_inverse_le_cost` bounds the reciprocal cosine by `Kcos`.
Unfold the strict-exceptional branch of `nativeWeight`, take norms,
and multiply by the nonnegative norms of both original rows. Thus the
pointwise exceptional **raw** trace has no denominator obligation
remaining, conditional on all cited candidates checking. Unlike the
previous node's post-removal estimate, it retains the original complex
transform and n functional and makes no oldform-removal identification.
It does not bound the transform numerator, sum over the trace, return
oldforms, or give a spectral gap.

## Source and boundary

* `Part3OriginalExceptionalCosinePair.lean`, blob
  `b3a6d528b4ab2296968f9a94486296a1589c4d66`: high m-row vanishing,
  cosine positivity and bounded inverse. It and its dependencies are
  source-only, including `high_positive_zero` in
  `Part3OriginalPositiveMarkOrder.lean`, blob
  `a7b55fd75d003112c65aa9cb2283259a4843ef5a`.
* `Part3ActualPositiveNativeDiagonal.lean`, blob
  `087daa59457776f5c18e69d73862394fb635c082`: exact native weight and
  complementary height. `Part3ActualPrescribedPositiveJ.lean`, blob
  `ac43ee9822d8df17a60e16d904006b3617d066e4`: actual integral definition
  of exceptionalWeight, including its normalization.
* `Part3OriginalMarkedPacketLimits.lean`, blob
  `b70b3e02d9924fbe44f9841f25693b403f381380`: `dMark = star(M)*N`.
  `Part3OriginalPrescribedPositiveTrace.lean`, blob
  `18715c3a04c31b972749878339b042b88704f5cf`: positive trace's actual
  `nativeWeight * dMark`. The opposite trace instead uses
  `8*kTransform` and is **not** covered by this statement.
* Manuscript repository pin `9731290e8f53cffda44129906cde6a965eaa869b`,
  body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` agrees with the
  chain; original section 7 (24), section 10(v)–(vii), and the input
  inventory remain as recorded in the parent report. No new external
  theorem is asserted. The parent records Pascadi arXiv:2404.04239v3,
  Theorem J, (3.34)–(3.35), its actual initial X range and rhoK=2R
  normalization; this pointwise lemma neither extends that range nor
  supplies a full-range averaged bound. ABL v1 Lemmas 3.1/3.2 and the
  numerical gap, regular and continuous inputs remain separately open.

## Verification and remaining work

`SOURCE_ONLY`: yes; `COMPILED`: no; `KERNEL_REPLAYED`: no; transitive
axioms check: not performed; independent review: not performed;
`UNEVALUATED`: yes, including all imported candidates. This environment
has no `lean` or `lake` on PATH and no staged exact import closure:
`command -v lean` and `command -v lake` returned no path; no compiler
was invoked, so no compiler exit code or log exists. Requested pins are
Lean `leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native
`09b97db5764ade1246bfb77206baa1b124760958`; the actual installed versions
cannot be checked here. Stack 8192 KiB, virtual memory unlimited; no
limits changed. `sha256sum` returned the above hash; `rg -n
'\b(sorry|admit|axiom|unsafe|native_decide)\b'` returned exit 1 (no
matches). Neither is a compiler check. No CI was launched.

Next: elaborate this candidate with the frozen import closure, kernel
replay and audit transitive axioms; explicitly specialize to Row and
sum its strict-exceptional slots, with exact transform numerator weights
and original sign conditions. Then connect oldform subtraction and its
cost to the original full pair; independently handle regular,
holomorphic and continuous pieces, opposite-sign K transform, the
spectral gap and full-range J. Both zero lanes, actual truncated tail,
14eta versus 28eta, 128C expansion and original N-threshold/reserve
order remain unproved here.
