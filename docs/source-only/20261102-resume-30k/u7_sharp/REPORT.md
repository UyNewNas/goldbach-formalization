# K / u7_sharp — original midpoint analytic error and complete sum

Status: **substantive analytic step written; original sharp U7 endpoints OPEN; uncompiled; kernel_verified=false; formal_credit=0**. Only this assigned directory was written. No compiler, build, CI, finite mathematical decision, numerical producer, certificate replay, Git operation, quota call or subagent was used.

The delivery proves the original midpoint second-derivative formulas and the signed quadrature identity, then binds the complete two original 1024-cell sums to the genuine U7 integral. It does not assert the stored numerical endpoints or accept a finite check as passed. The directed-arithmetic adapter has explicit remaining point and derivative-box inputs and is not counted as an actual numerical supplier.

## Original source and predecessor

The K task row and README, current manuscript lines 562–630 and 691–996, J/h7 source/REGISTRY/REPORT and independent review were read. The frozen J dictionary identifies the true original integral at K=1 as P+C, where

    P = integral_[59/250,1/3] log((1-2t)/t)/(t(1-t)) dt,
    C = integral_[2,132/59] (log(u-1)/u) log((191/59)/(u+1)) du.

The actual original producer `../goldbach-research/certify_sharp_switch_midpoint.py` uses these same two kernels, 1024 equal rational cells, their explicit second derivatives and a signed error term. Its step expression is

    (value(midpoint) + second(cell) * I(step*step/24)) * I(step).

The exact Python source, its frozen Q80 backend `certify_conservative_chen.py`, the proof note, the archived midpoint output, and the independent 64-panel Simpson producer/output were read. Their recorded success fields are provenance, not proof. No producer was executed. The archived K0=67619/10000 scales both terms. The manuscript current c=49044063/25000000 and K=8452171/1250000 are unchanged. The root's factor two on U7 and subsequent Chen quarter are external to this primitive cost.

J/h7 has a narrow refreshed SOURCE_REVIEW_PASS. The inherited production blocker in `P5U7ComponentLeadingIntegrals.lean:104` is untouched: its `ContinuousOn.congr` equality is reversed. The standalone generic midpoint module imports no U7 source, so that inherited defect does not enter the generic theorem. It does enter the actual U7 dictionary import chain. No claim of a verified import DAG is made.

## New proof bodies

`P5OriginalSignedMidpoint.lean` is the standalone shared module requested by the parent for U7/U8/U9. It imports explicit derivative product/power APIs, interval FTC, and tactics. Its principal exact equality is

    integral_[l,r] f = (r-l) f((l+r)/2) + E,
    E = integral_[l,m] (x-l)^2 f''(x)/2
          + integral_[m,r] (x-r)^2 f''(x)/2,
    m=(l+r)/2.

The proof differentiates `(x-v)f(x)-(x-v)^2 f'(x)/2`, separately with v=l and v=r, and applies FTC. The midpoint f' terms cancel exactly. Actual integrability is proved from continuity, and the degenerate l=r case is included. Both weights are nonnegative. Their exact total mass is `(r-l)^3/24`, proved using a cubic primitive. Therefore a signed interval `[L,U]` for f'' gives precisely the producer's bounds `step*(f(mid)+[L,U]*step^2/24)`. Negative curvature is retained; no absolute-value inflation or coarse estimate is substituted.

`P5U7OriginalMidpointDerivatives.lean` proves the literal `main_second(t,7)` and `correction_second(u)` formulas. The prime factorization uses `r=1/t+1/(1-t)`, with its actual first and second derivatives. The logarithmic first and second derivatives agree exactly with the source's `log_terms(t,7)`. For the correction, A=log(u-1)/u and B=log((191/59)/(u+1)); both first/second derivatives and the product formula A''B+2A'B'+AB'' are proved. The functions are regular on neighborhoods of the complete closed original domains. No derivative value, range, monotonicity or quadrature estimate is a hypothesis of these actual derivative theorems.

`P5U7OriginalMidpointSum.lean` fixes 1024 in the rational mesh and proves its step formula, endpoint identities, monotonicity and closed-cell coverage. It then uses adjacent-interval integration to identify the full exact sum of midpoint samples plus signed error integrals with each genuine scalar integral. The final theorems identify the genuine Omega integral with both complete original sums and multiply the entire pair by archive K0. The correction is added once with its original sign; the J coarse correction enclosure is not imported or used. There is no pointwise bound, finite-sum identity, saved endpoint or original-integral equality taken as a new hypothesis.

`P5OriginalDirectedMidpoint.lean` reuses the existing `P2DirectedLogRounding.Enclosure` operations. It places Q80 rounding at the original rational constructor and multiplication positions, with exact addition. The shared signed midpoint bound proves soundness of that operation layout. This is only an adapter: its actual midpoint-value and whole-cell second-derivative enclosures must still be established. It does not identify a Python output numerator with a typed Lean computation or silently discharge the source/log/finite checks. This conditional adapter is not counted as removal of an original numerical supplier.

## Exact progress and remaining blockers

The packet removes the analytic obligations that the original second-derivative expressions really differentiate the actual two source kernels, that the signed midpoint remainder has the exact original 1/24 factor, and that the original 1024-cell sums reconstruct both entire scalar integrals. Those are substantive unconditional internal steps. No premise of `p5z_original_h7_of_actual_full_policy_source_supplied` is yet removed.

The original upper endpoint remains

    J7 <= (1672464594622060236183097 / 2^80) / (67619/10000).

The original independent lower Simpson endpoint remains

    (7183180737282426411788973366247539 / 2^112) / (67619/10000) <= J7.

For the upper endpoint, still needed are the actual Q80 midpoint samples and full closed-cell second-derivative enclosures for both kernels, soundness/authentication of the precise original log backend's per-operation outputs, and the complete original aggregate-to-saved-numerator binding. This packet does not substitute a new direct Taylor log sum for the original backend. Its exact error integrals are not numerical evaluations. For the lower endpoint, the independent 64-panel Simpson fourth-derivative/error and directed-output binding remain unproved. The midpoint lower numerator is not substituted for that sharper independent lower slope.

Full-policy reciprocal-totient density/integral/certificate and strict gap, the actual same-e licence/cap/active support, and the signed rank-three plus rank-four PP error at the original attached coefficient and threshold order remain unchanged and OPEN. No classical external result is introduced as an assumption. No manuscript contradiction or missing original-data claim is made.

## Installation and verification

Install the shared signed module independently. Install J's scalar dictionary before the U7 derivative module, and the signed/derivative modules before the sum module. The optional directed adapter needs the signed module and installed `P2DirectedLogRounding`. All actual draft and installation paths, raw source/import hashes, declaration names and manuscript bindings are recorded in REGISTRY.

The manifest pins Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` and Lean `v4.33.0-rc1`. The local Mathlib source directory is absent. Pinned upstream FTC, interval integral operations, and derivative import definitions were inspected directly. In particular FTC intentionally excludes the derivative product API; explicit `Deriv.Mul` and `Deriv.Pow` imports were added to the standalone shared module. Verification is static source/mathematical inspection, forbidden-token search and raw hashing only. Independent review, installation, elaboration and kernel verification remain outstanding.
