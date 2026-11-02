# K/u8_upper: actual U8 scalar and signed midpoint enclosure

Status: a substantive analytic enclosure step is written; the exact selected endpoint, original h8, and P5.6 remain **OPEN**. All files are static source candidates: `compiled=false`, `kernel_verified=false`, `formal_credit=0`. No compiler, build, CI, finite certificate execution, numerical replay, Git, quota call, or subagent was used. Only K/u8_upper was written.

The delivery proves a full-domain rational midpoint enclosure of the true original `currentChenUpsilon8HarmonicIntegral`. Neither an integral bound nor a second-derivative bound is assumed. The decisive rational comparison to the saved upper endpoint is deliberately unasserted.

## Original manuscript and producer

Manuscript lines 562–590 define U8 by `N^(417/5000) <= p1 < N^(1/3) <= p2 < sqrt(N/p1)`, with quotient sifted at p2. Lines 691–996 retain the actual common density, the positive-product use, and the negative U8 quarter in the unchanged root. The production harmonic integral has domain

`417/5000 <= x < 1/3`, `1/3 <= y < (1-x)/2`,

with density `1/(x*y*(1-x-y))`. The existing `P2NegativeDomainCover.eighthHarmonicIntegral_eq_nested` already proves genuine Fubini on that exact domain; this delivery reuses it.

The original source `../goldbach-research/certify_sharp_switch_midpoint.py` has SHA `4b1830eb0168470f2007581777f6755a8a2dd14dfa67bd14b2f6fa0b6f103476`, matching the selected JSON's producer binding. Its U8 scalar is `log(2-3t)/(t*(1-t))`, on `[417/5000,1/3]`. It uses 1024 cells, midpoint values, signed second-derivative intervals, and the exact factor `delta^3/24`. Its original Q80 backend `certify_conservative_chen.py` has SHA `67b9429667e18786058e0fe58676fbe09d556868468f1281166cac2b55f8604e`, also matching that binding. These sources and the accompanying proof were read; neither producer was run.

The selected JSON stores U8 upper `4904703865205402441361491 / 1208925819614629174706176` at `K0=67619/10000`. The integral endpoint remains exactly `savedU8/K0`. Original `currentK=8452171/1250000`, `currentC=49044063/25000000`, `fixedProductDensityCoefficient=currentK+1/100000000`, and the stored `U8Envelope` are unchanged.

## New analytic proof bodies

`P5OriginalU8ScalarProducer.lean` proves the exact scalar dictionary by applying the already proved general moving-slice logarithmic primitive with **d=1/3**. The generic primitive happens to live in the U9 integration module; no U9 domain, endpoints, integral, or source is substituted. The result is

`J8 = integral_[417/5000,1/3) log(2-3t)/(t*(1-t)) dt`.

On the full closed interval, t, 1-t, and 2-3t are positive. The file derives both real derivatives of the archived scalar. With `L=log(2-3t)` and `R=1/t+1/(1-t)`, its exact second derivative is

`(-9/(2-3t)^2)*R + 2*(-3/(2-3t))*(-1/t^2+1/(1-t)^2) + L*(2/t^3+2/(1-t)^3)`.

This is precisely `main_second(t,8)` in the source. The factored `producerValue=L*R` equals the original quotient throughout the original interval. Its second derivative is continuous there. No derivative of a numerical interpolant is used.

The uniform mesh reuses `P2U8UniformRationalCover.node`. New identities bind it to the archive's exact Fraction arithmetic `left+j*step` and `r=l+step`. Adjacent interval integration proves the complete original integral equals the sum of all cell integrals, including the literal 1024-cell partition. The closed endpoint t=1/3 and the original weak y=1/3 wall are treated by the genuine integral identities, without deleting a source slice.

`P5OriginalU8MidpointEnclosure.lean` supplies the missing analytic curvature enclosure. For every cell `[l,r]` in the original interval it encloses `1/t`, `1/(1-t)`, and `1/(2-3t)` using the existing proved reciprocal operation, with its positivity guard derived from the original endpoints. Existing `logLower`/`logUpper` enclose `log(2-3t)` by the exact query `q=3-3t`; the lower log uses r and the upper log uses l. The exact original second-derivative expression is propagated through the proved signed four-corner interval multiplication and addition. The theorem `secondBounds_contains` has only original endpoint and membership hypotheses, not an analytic-bound premise.

The shared `P5OriginalSignedMidpoint` module, owned by K/u7_sharp, supplies the signed Peano identity. Its two half-cell kernels are nonnegative and have total mass `delta^3/24`. This delivery proves all of its U8 hypotheses: the two derivatives, full-cell continuity, and genuine second-derivative enclosure. It also encloses the true midpoint value. Thus `panel_enclosure` bounds the actual full cell integral on both sides, retaining the sign of each second-derivative endpoint.

Summation produces `original_integral_midpoint_enclosure`: for every logarithm truncation n and every positive mesh size m,

`rationalLower n m <= J8 <= rationalUpper n m`.

The symbolic specialization `original_1024_midpoint_enclosure` uses n=32 and m=1024. These rational expressions are not evaluated. The theorem has no finite endpoint-check premise.

`P5OriginalU8MidpointEndpointPort.lean` is only a downstream consumer. It identifies the unchanged stored rational endpoint and defines `upperEndpointCheck n m`. Conditional soundness transfers a successful comparison to the J upper-only envelope. There is **no theorem asserting that any endpoint check is true**, and no unconditional h8 theorem is exported. This small consumer is not the substantive progress claimed above.

## Exact scope and remaining blockers

The enclosure evaluates the archived **real mathematical expression and partition** with exact rational interval/Taylor operations. It is not asserted to equal the historical Q80 output. The archived backend rounds after operations and uses its own fixed-point log routine; the new exact-rational backend does not reproduce that execution. Source hashes authenticate which original producer was inspected; they do not certify its output.

The following remain open:

1. Prove an exact rational comparison `rationalUpper n m <= savedU8/K0` for an explicitly chosen n,m, or finish literal Q80 producer soundness and saved-output authentication. No claim is made that n=32,m=1024 passes the new comparison. No finite decision term was executed.
2. The common full-policy integral limit, certificate, strict gap below the original fixed density coefficient, cap, licensing, and active-modulus scope. The new analytic enclosure supplies none of those arithmetic/density hypotheses.
3. The same-rho signed PP estimate on the original `strictTriples N`. J's independently source-reviewed diagonal payment is reused through its unchanged upper-only slot; no strict-source PP estimate is inferred from integral quadrature.
4. Same-instance assembly with the other seven original grouped suppliers, independent source review of these candidates and the shared K midpoint dependency, draft installation, and later user-owned compilation.

The new local work removes the scalar/producer dictionary, full original cell partition, true second-derivative identity/continuity, full-cell rational curvature enclosure, and signed midpoint integration obligations. It does not remove the selected endpoint comparison or any broad original supplier debt. No manuscript gap is established.

## Static provenance

Read the task row and README, J/h8 source/REGISTRY/REPORT and its current independent `SOURCE_REVIEW_PASS` scope, original manuscript ranges, original producer/backend/proof/selected JSON, and the relevant production Fubini, primitive, directed reciprocal/log, and mesh sources. The I/medium_d0 registry format was used. REGISTRY records exact raw hashes, draft import resolutions, declaration names, manuscript positions, eliminated obligations, and remaining ports. Its dependency inventory covers direct imports and inspected supporting files, not the complete transitive DAG.

Static text inspection found no placeholder proof, new axiom, or asserted decisive data guard. Mathlib source is absent at the manifest's local `.lake/packages/mathlib` path; existing repository uses were used to check API shape, and no Mathlib source hash or elaboration success is claimed. Raw hashes and manual mathematics are provenance and source review, not kernel verification.
